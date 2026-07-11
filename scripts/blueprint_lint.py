#!/usr/bin/env python3
"""Blueprint lint (see docs/blueprints/brun-guide.md preamble).

Checks, in order:
  Phase 1 — brun-guide.md N-cards (unchanged, byte-identical output):
    1. sorry sweep      — no `sorry` anywhere under Salt/
    2. card grammar     — every card in brun-guide.md parses; status token present
    3. open-card sanity — cards marked open/blocked cite no Lean declarations
    4. existence+axioms — every declaration cited by a proved/partial card exists
                          and depends on at most [propext, Classical.choice,
                          Quot.sound]  (mechanizes CLAUDE.md iron rule 3)
  Phase 2 — largesieve.md node-catalog table audit:
    every ✅ row's backticked project declarations resolve in Salt/.
  Phase 3 — repo-wide headliner axiom audit:
    the flagship theorem of each landed track (HEADLINERS below) is
    axiom-clean, in a single lake compile.

What this can NOT check: that a card's prose Statement matches the Lean
statement's meaning. Green output means "not mechanically stale", never
"the docs are true". Statement fidelity is covered by the card-immutability
policy (guide preamble), not by this script.

OUT OF SCOPE (deliberately): the explicit12-design.md card grammar. Those
~40 cards are heterogeneous prose (Card C1 / W5-5 / NC-3 / NB-1 shapes) and
need a separate parser — a distinct design task, not folded in here.

Usage: python3 scripts/blueprint_lint.py   (from the repo root)
Exit code 0 = all checks pass; nonzero on any FAIL.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GUIDE = os.path.join(ROOT, "docs", "blueprints", "brun-guide.md")
LARGESIEVE = os.path.join(ROOT, "docs", "blueprints", "largesieve.md")
SCRATCH = os.path.join(ROOT, "LintScratch.lean")
HEADLINER_SCRATCH = os.path.join(ROOT, "LintScratchHeadliners.lean")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Repo-wide axiom headliners: the flagship declaration of each landed track.
# Phase 3 asserts each is axiom-clean ([propext, Classical.choice, Quot.sound]).
# MANUAL UPKEEP: this list is hand-curated. When a track/rung closes, add its
# headline theorem here; when one is renamed, update it here (a rename makes the
# name unknown -> the phase FAILs, which is the intended tripwire).
HEADLINERS = [
    "Salt.Twelve.gaps_le_twelve",
    "Salt.LS.analytic_LS",
    "Salt.LS.arithmetic_LS",
    "Salt.LS.char_LS",
    "Salt.LS.bdh",
    "Salt.LS.vaughan",
    "Salt.N6.N6_2",
]

PROVED_TOKENS = ("✅", "\U0001f7e1")  # ✅ proved, 🟡 partial
OPEN_TOKENS = ("\U0001f534", "⛔")  # 🔴 open, ⛔ tier-blocked

CARD_RE = re.compile(r"^#### (N\d+\.\d+)\b(.*)$")
NAME_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")
# Lean names cited in a card's **Lean.** field. Multi-line field: consume
# until the next **Field.** or the next card.
FIELD_RE = re.compile(r"^\*\*(\w[\w ]*)\.\*\*")

errors: list[str] = []
warnings: list[str] = []


def fail(msg: str) -> None:
    errors.append(msg)


SORRY_RE = re.compile(r"(?<!`)\bsorry\b(?!`|-)")  # prose: `sorry`, "sorry-free"


def check_sorry() -> None:
    out = subprocess.run(
        ["grep", "-rn", "sorry", os.path.join(ROOT, "Salt")],
        capture_output=True, text=True,
    )
    for h in out.stdout.splitlines():
        if not h.strip():
            continue
        _, _, text = h.split(":", 2)
        if SORRY_RE.search(text):
            fail(f"sorry sweep: {h}")


def parse_cards() -> list[dict]:
    if not os.path.exists(GUIDE):
        fail(f"guide not found: {GUIDE}")
        return []
    cards: list[dict] = []
    card: dict | None = None
    field: str | None = None
    with open(GUIDE, encoding="utf-8") as f:
        for line in f:
            m = CARD_RE.match(line)
            if m:
                card = {"node": m.group(1), "header": m.group(2).strip(), "fields": {}}
                cards.append(card)
                field = None
                continue
            if card is None:
                continue
            if line.startswith("#"):  # left the catalog card
                card, field = None, None
                continue
            fm = FIELD_RE.match(line)
            if fm:
                field = fm.group(1)
                card["fields"][field] = line[fm.end():]
            elif field is not None:
                card["fields"][field] += line
    return cards


def card_status(card: dict) -> str:
    # The header is the sole status source: Status-field prose may legitimately
    # reference other nodes' tokens ("dep N3.1 ✅").
    for tok in PROVED_TOKENS + OPEN_TOKENS:
        if tok in card["header"]:
            return tok
    return ""


def collect() -> tuple[list[dict], dict[str, list[str]]]:
    cards = parse_cards()
    audit: dict[str, list[str]] = {}
    for card in cards:
        node = card["node"]
        status = card_status(card)
        if not status:
            fail(f"{node}: no status token (expected one of ✅ 🟡 🔴 ⛔)")
            continue
        lean_field = card["fields"].get("Lean", "")
        names = NAME_RE.findall(lean_field)
        if status in OPEN_TOKENS:
            if names:
                fail(f"{node}: marked open/blocked but cites Lean names: {names}")
        else:
            if not names:
                fail(f"{node}: marked proved/partial but cites no Lean names")
            for n in names:
                audit.setdefault(n, []).append(node)
    return cards, audit


def scan_axioms(
    names: list[str], scratch_path: str
) -> tuple[int, str, dict[str, set[str]]]:
    """Compile one scratch (`import Salt` + a `#print axioms` per name) with a
    single `lake env lean` call and parse the reported axiom sets.

    Returns (returncode, combined-output, {name: axiom-set}). Names Lean could
    not resolve are simply absent from the dict; a nonzero returncode means the
    compile itself failed (unknown constant, build error, ...). This is the one
    slow step, so callers batch all their names into a single invocation.
    """
    with open(scratch_path, "w", encoding="utf-8") as f:
        f.write("import Salt\n\n")
        for n in names:
            f.write(f"#print axioms {n}\n")
    lake = os.path.expanduser("~/.elan/bin/lake")
    if not os.path.exists(lake):
        lake = "lake"
    try:
        out = subprocess.run(
            [lake, "env", "lean", scratch_path],
            capture_output=True, text=True, cwd=ROOT, timeout=600,
        )
    finally:
        os.unlink(scratch_path)
    reported: dict[str, set[str]] = {}
    for line in out.stdout.splitlines():
        m = re.match(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
        if m:
            reported[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        else:
            m2 = re.match(r"'([^']+)' does not depend on any axioms", line)
            if m2:
                reported[m2.group(1)] = set()
    return out.returncode, out.stdout + out.stderr, reported


def check_axioms(audit: dict[str, list[str]]) -> None:
    if not audit:
        return
    names = sorted(audit)
    rc, output, reported = scan_axioms(names, SCRATCH)
    if rc != 0:
        # Unknown constants and other elaboration errors land here.
        fail("existence/axioms: lean failed:\n" + output)
        return
    for n in names:
        if n not in reported:
            fail(f"existence/axioms: no #print axioms output for {n} (cited by {audit[n]})")
            continue
        extra = reported[n] - ALLOWED_AXIOMS
        if extra:
            fail(f"axioms: {n} uses non-standard axioms {sorted(extra)} (cited by {audit[n]})")


# --- Phase 2: largesieve.md node-catalog table audit ------------------------
# largesieve.md carries its nodes as markdown tables (`| Lx.y | stmt | class |
# status |`), not brun-style N-cards, so it needs its own parser. For every ✅
# row we pull the backticked *project* declarations out of the statement cell
# and confirm they still resolve in Salt/. Mathlib names cited as inputs and
# prose fragments are filtered out heuristically (see ls_candidate); only names
# the project could actually own are checked.

# Grabs the declared name from a Lean declaration line under Salt/.
DECL_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)"
)
LS_ROW_RE = re.compile(r"^\|\s*(L\d+\.\d+[a-z]?)\s*\|(.*)$")
BACKTICK_RE = re.compile(r"`([^`]+)`")
LS_IDENT_RE = re.compile(r"^(?:Salt\.)?[A-Za-z_][A-Za-z0-9_.']*$")


def project_decls() -> set[str]:
    """Every declaration name defined under Salt/ (full and leaf form)."""
    names: set[str] = set()
    for dp, _dirs, files in os.walk(os.path.join(ROOT, "Salt")):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            with open(os.path.join(dp, fn), encoding="utf-8") as f:
                for line in f:
                    m = DECL_LINE_RE.match(line)
                    if m:
                        full = m.group(1)
                        names.add(full)
                        names.add(full.rsplit(".", 1)[-1])
    return names


def ls_candidate(tok: str) -> bool:
    """Does a backticked token look like a Lean declaration worth checking?

    Heuristic (see brun-guide/largesieve docs): no spaces, length > 2, not a
    filename, and either `Salt.`-prefixed or lowercase-initial (uppercase-
    initial dotted tokens are mathlib namespaces — Nat., Real., DirichletChar…).
    """
    if " " in tok or len(tok) <= 2:
        return False
    if tok.endswith(".lean") or tok.endswith(".md"):
        return False
    if not LS_IDENT_RE.match(tok):
        return False
    return tok.startswith("Salt.") or tok[0].islower()


def check_largesieve(decls: set[str]) -> int:
    """Audit largesieve.md's ✅ rows. Prints its own phase block, returns #FAILs.

    resolved   — a backticked candidate that resolves as a Salt/ declaration.
    missing    — a `Salt.`-prefixed candidate that does NOT resolve = FAIL
                 (an unambiguous, now-broken claim on a project declaration).
    A ✅ row with zero resolvable project declarations = WARN, not FAIL: some
    rows legitimately cite only prose, file paths, or mathlib inputs.
    Non-`Salt.` candidates that fail to resolve are treated as mathlib inputs
    and skipped — the project cannot own them, so they are not our tripwire.
    """
    if not os.path.exists(LARGESIEVE):
        print("largesieve: SKIP (docs/blueprints/largesieve.md not found)")
        return 0
    rows = 0
    resolved_total = 0
    warn_nodes: list[str] = []
    fail_nodes: list[tuple[str, list[str]]] = []
    in_catalog = False
    with open(LARGESIEVE, encoding="utf-8") as f:
        for line in f:
            if line.startswith("## "):
                in_catalog = line.startswith("## Node catalog")
            if not in_catalog:
                continue
            m = LS_ROW_RE.match(line)
            if not m:
                continue
            node = m.group(1)
            cells = m.group(2).split("|")
            while cells and not cells[-1].strip():
                cells.pop()  # drop the trailing empty from the closing `|`
            if len(cells) < 2:
                continue
            status = cells[-1]
            if "✅" not in status:  # ✅
                continue
            rows += 1
            # Reconstruct the statement cell(s): everything but class + status.
            # `|.join` restores any `|` that lived inside a backticked formula.
            statement = "|".join(cells[:-2])
            resolved: list[str] = []
            missing: list[str] = []
            for tok in BACKTICK_RE.findall(statement):
                if not ls_candidate(tok):
                    continue
                leaf = tok.rsplit(".", 1)[-1]
                if tok in decls or leaf in decls:
                    resolved.append(tok)
                elif tok.startswith("Salt."):
                    missing.append(tok)
                # else: mathlib input / prose token -> skip silently
            resolved_total += len(resolved)
            if missing:
                fail_nodes.append((node, missing))
            elif not resolved:
                warn_nodes.append(node)
    print(f"largesieve: {rows} ✅ rows, {resolved_total} project declarations "
          f"resolved, {len(warn_nodes)} description-only")
    for node in warn_nodes:
        print(f"WARN  largesieve {node}: ✅ row cites no resolvable project "
              f"declaration (names given in prose/paths, not backticked)")
    for node, missing in fail_nodes:
        print(f"ERROR largesieve {node}: Salt-namespaced declaration(s) do not "
              f"resolve in Salt/: {missing}")
    print("largesieve: " + ("FAIL" if fail_nodes else "OK"))
    return len(fail_nodes)


# --- Phase 3: repo-wide headliner axiom audit -------------------------------
def check_headliners() -> int:
    """Axiom-audit the HEADLINERS in a single lake compile. Returns #FAILs."""
    print(f"headliners: {len(HEADLINERS)} declarations, single lake compile")
    rc, output, reported = scan_axioms(HEADLINERS, HEADLINER_SCRATCH)
    fails: list[str] = []
    if rc != 0:
        # A renamed/removed headliner (unknown constant) or a broken build.
        print("ERROR headliners: lean failed:\n" + output)
        print("headliners: FAIL")
        return 1
    for n in HEADLINERS:
        if n not in reported:
            fails.append(f"headliners: no #print axioms output for {n} "
                         f"(unknown constant?)")
            continue
        extra = reported[n] - ALLOWED_AXIOMS
        if extra:
            fails.append(f"headliners: {n} uses non-standard axioms "
                         f"{sorted(extra)}")
    for msg in fails:
        print(f"ERROR {msg}")
    print("headliners: " + ("FAIL" if fails
                            else f"OK ({len(HEADLINERS)} axiom-clean)"))
    return len(fails)


def main() -> int:
    # --- Phase 1: brun-guide N-cards (output byte-identical to prior versions) ---
    check_sorry()
    cards, audit = collect()
    check_axioms(audit)
    n_proved = sum(1 for c in cards if card_status(c) in PROVED_TOKENS)
    print(f"cards: {len(cards)} parsed, {n_proved} proved/partial, "
          f"{len(audit)} declarations audited")
    for w in warnings:
        print(f"WARN  {w}")
    for e in errors:
        print(f"ERROR {e}")
    # --- Phase 2 + Phase 3 ---
    ls_fails = check_largesieve(project_decls())
    hl_fails = check_headliners()
    total = len(errors) + ls_fails + hl_fails
    print("lint: " + ("OK" if total == 0 else f"{total} failures"))
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
