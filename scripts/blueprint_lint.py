#!/usr/bin/env python3
"""Blueprint lint, phase 1 (see docs/blueprints/brun-guide.md preamble).

Checks, in order:
  1. sorry sweep      — no `sorry` anywhere under Salt/
  2. card grammar     — every card in brun-guide.md parses; status token present
  3. open-card sanity — cards marked open/blocked cite no Lean declarations
  4. existence+axioms — every declaration cited by a proved/partial card exists
                        and depends on at most [propext, Classical.choice,
                        Quot.sound]  (mechanizes CLAUDE.md iron rule 3)

What this can NOT check: that a card's prose Statement matches the Lean
statement's meaning. Green output means "not mechanically stale", never
"the docs are true". Statement fidelity is covered by the card-immutability
policy (guide preamble), not by this script.

Usage: python3 scripts/blueprint_lint.py   (from the repo root)
Exit code 0 = all checks pass.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GUIDE = os.path.join(ROOT, "docs", "blueprints", "brun-guide.md")
SCRATCH = os.path.join(ROOT, "LintScratch.lean")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

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


SORRY_RE = re.compile(r"(?<!`)\bsorry\b(?!`)")  # prose mentions are `sorry`


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


def check_axioms(audit: dict[str, list[str]]) -> None:
    if not audit:
        return
    names = sorted(audit)
    with open(SCRATCH, "w", encoding="utf-8") as f:
        f.write("import Salt\n\n")
        for n in names:
            f.write(f"#print axioms {n}\n")
    lake = os.path.expanduser("~/.elan/bin/lake")
    if not os.path.exists(lake):
        lake = "lake"
    try:
        out = subprocess.run(
            [lake, "env", "lean", SCRATCH],
            capture_output=True, text=True, cwd=ROOT, timeout=600,
        )
    finally:
        os.unlink(SCRATCH)
    if out.returncode != 0:
        # Unknown constants and other elaboration errors land here.
        fail("existence/axioms: lean failed:\n" + out.stdout + out.stderr)
        return
    reported: dict[str, set[str]] = {}
    for line in out.stdout.splitlines():
        m = re.match(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
        if m:
            reported[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        else:
            m2 = re.match(r"'([^']+)' does not depend on any axioms", line)
            if m2:
                reported[m2.group(1)] = set()
    for n in names:
        if n not in reported:
            fail(f"existence/axioms: no #print axioms output for {n} (cited by {audit[n]})")
            continue
        extra = reported[n] - ALLOWED_AXIOMS
        if extra:
            fail(f"axioms: {n} uses non-standard axioms {sorted(extra)} (cited by {audit[n]})")


def main() -> int:
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
    print("lint: " + ("FAIL" if errors else "OK"))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
