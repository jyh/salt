#!/usr/bin/env python3
"""THE HEADLINE THEOREMS PAGE, BY MACHINE (objective O47).

Writes docs/HEADLINE-THEOREMS.md: one page, one entry per landed headline theorem, each with
its Lean statement, Lean name, the commit and date it entered the public history, and the
axiom receipt that covers it.

Only ONE thing on the page is chosen by hand: the list HEADLINES below (which theorems are
headline-tier). Everything else is read from the repository:

  statement    copied from the source, from the `theorem` keyword to the `:=` that ends the
               signature. When the statement is a single named Prop (e.g. `BrunStatement`),
               that definition is copied too, so the reader sees what the name means.
  file:line    found by searching the file for the declaration.
  plain line   copied from the theorem's row in docs/RESULTS.md (that file's own lint,
               scripts/results_lint.py, checks the row).
  sha, date    the first commit whose diff adds `theorem <name>` to the file (git pickaxe),
               and that commit's author date.
  ledger       the `#audit_axioms` line naming the theorem, which fails `lake build` if the
               theorem depends on any axiom other than propext, Classical.choice, Quot.sound.
  receipt      scripts/headline_receipt.json, written by `--receipt` as a TRIPLE:
               (1) THE BUILD LINE: a `../saltbuild.sh` BUILD of every module that DEFINES a
                   headline theorem, `saltbuild EXIT=0` with no tagged error, read from that
                   run's log AND from the fleet's machine-written audit record (args, HEAD,
                   EXIT, time), which must name every defining module and come BEFORE the
                   audit run, at the same HEAD;
               (2) THE AUDIT LOG of the scratch file that `--audit-file` writes: EXIT=0, no
                   tagged error, one `#print axioms` line per theorem;
               (3) AN IMPORTED CONTROL in that log: `#print axioms Lean.reduceBool`, a core
                   constant read from its olean's table, must print `Lean.trustCompiler`.
               Why the triple: `#print axioms` on an IMPORTED name reads a table written into
               its olean at build time (`exportedAxiomsExt`), so a scratch run that builds
               nothing can print "does not depend on any axioms" for a theorem whose upstream
               has since gained a `sorry` (h2c, measured 2026-11-23). Only (1) makes the table
               current; a planted `sorry` in the scratch itself tests the printer, not that path.

The lint (`--check`) fails when the page is stale, when a theorem's statement has changed
since the receipt was taken (the receipt stores a digest of each statement), when a theorem
has no `#audit_axioms` line, or when the receipt is missing a theorem or shows any axiom
outside the three. So a statement cannot change, and a theorem cannot be added, without a
new receipt.

What this can NOT check: that a statement means what the plain line says (a reader checks
that), that the build record describes the build log handed in (the receipt records both logs'
sha256, the audit records, and the commit; anyone can re-run it), or that an uncommitted edit
was not made between the build and the audit (the record's `dirty` count is copied, not judged).

Usage (from anywhere):
  python3 scripts/headline_theorems.py               write docs/HEADLINE-THEOREMS.md
  python3 scripts/headline_theorems.py --check       exit 1 if the page or the receipt is stale
  python3 scripts/headline_theorems.py --audit-file F    write the scratch audit file F
  python3 scripts/headline_theorems.py --build-targets   print the defining modules (term 1's args)
  python3 scripts/headline_theorems.py --receipt BUILDLOG AUDITLOG   check the triple, write the receipt
  python3 scripts/headline_theorems.py --self-test   run the parser fixtures and mutants
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAGE = os.path.join("docs", "HEADLINE-THEOREMS.md")
RESULTS = os.path.join("docs", "RESULTS.md")
RECEIPT = os.path.join("scripts", "headline_receipt.json")
COMMAND = "python3 scripts/headline_theorems.py"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONTROL = "Lean.reduceBool"
CONTROL_AXIOM = "Lean.trustCompiler"

# ---------------------------------------------------------------- the one hand-chosen list
# (section, fully qualified Lean name, source file). Each must have a row in docs/RESULTS.md.
HEADLINES = [
    ("Sieves and almost-primes", "Salt.N6.N6_2", "Salt/Brun/N6.lean"),
    ("Sieves and almost-primes", "Salt.BrunLower.twin_almost_prime", "Salt/BrunLower/TwinInstance.lean"),
    ("Sieves and almost-primes", "Salt.Chen.chen_headline", "Salt/Chen/ChenTheorem.lean"),
    ("Sieves and almost-primes", "Salt.Goldbach.chen_goldbach", "Salt/Goldbach/ChenGoldbach.lean"),
    ("Primes in progressions and bounded gaps", "Salt.SW.siegelWalfisz_holds", "Salt/SW/Gate.lean"),
    ("Primes in progressions and bounded gaps", "Salt.SW.bounded_gaps_unconditional", "Salt/SW/Gate.lean"),
    ("Primes in progressions and bounded gaps", "Salt.MaynardK.gaps_le_600", "Salt/MaynardK/Gaps600.lean"),
    ("Primes in progressions and bounded gaps", "SaltC1.MaynardK.gaps_le_270", "SaltC1/MaynardK/Gaps270.lean"),
    ("Primes in progressions and bounded gaps", "Salt.ThreePrimes.three_primes", "Salt/ThreePrimes/Assembly.lean"),
    ("Zeros and exponential sums", "Salt.Vk.zeta_zero_free_region_pow", "Salt/Vk/GrowthPow.lean"),
    ("Zeros and exponential sums", "Salt.Vmvt.vmvt", "Salt/Vmvt/Summit2.lean"),
    ("Zeros and exponential sums", "Salt.Weil.norm_kloosterman_le_two_sqrt", "Salt/Weil/Descent.lean"),
    ("Multiplicative functions and the parity barrier", "Salt.MR.lambda_nonpret", "Salt/MR/NonPretClose.lean"),
    ("Multiplicative functions and the parity barrier", "Salt.TwinBar.M₂_squeeze", "Salt/TwinBar/Witness.lean"),
    ("Multiplicative functions and the parity barrier", "Salt.TwinBar.parity_wall_unconditional", "Salt/TwinBar/WallUnconditional.lean"),
    ("Outside number theory", "Keller.jacobian_conjecture_counterexample", "Salt/Keller/Counterexample.lean"),
]

DECL_KW = r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"


# ---------------------------------------------------------------- source reading
def read(path: str) -> str:
    with open(os.path.join(REPO, path), encoding="utf-8") as f:
        return f.read()


def short(name: str) -> str:
    return name.split(".")[-1]


def find_decl(text: str, name: str, kinds: str = "theorem|lemma") -> int | None:
    """0-based line index of the declaration of `short(name)` in `text`, or None.
    Several matches (a doc block quoting the signature, say) resolve to the LAST code line,
    i.e. the one not inside a comment; ties are refused by the caller's check."""
    pat = re.compile(r"^" + DECL_KW + r"(?:" + kinds + r")\s+" + re.escape(short(name))
                     + r"(?=[\s:({\[]|$)")
    hits = []
    in_block = 0
    for i, line in enumerate(text.split("\n")):
        opened = line.count("/-")
        closed = line.count("-/")
        if in_block == 0 and pat.match(line):
            hits.append(i)
        in_block = max(0, in_block + opened - closed)
    return hits[-1] if hits else None


def signature(text: str, start: int) -> str:
    """The declaration from line `start` up to (not including) the `:=` or `where` that ends
    its signature at bracket depth 0. Comments inside are kept verbatim."""
    lines = text.split("\n")
    src = "\n".join(lines[start:])
    depth = 0
    i = 0
    while i < len(src):
        c = src[i]
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
            continue
        if src.startswith("/-", i):
            j = src.find("-/", i)
            i = len(src) if j < 0 else j + 2
            continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and src.startswith(":=", i):
            return src[:i].rstrip()
        elif depth == 0 and re.match(r"\swhere\b", src[i:i + 7]):
            return src[:i].rstrip()
        i += 1
    raise ValueError("no end of signature found")


def conclusion_ident(sig: str) -> str | None:
    """If the statement's type is one bare identifier (`theorem t : Foo`), return it."""
    m = re.search(r"\)?\s:\s*([A-Z][A-Za-z0-9_.'₀-₉]*)((?:\s+[a-z][A-Za-z0-9_']*)*)\s*$", sig)
    return m.group(1) if m else None


def find_def(ident: str) -> tuple[str, int, str] | None:
    """Locate `def|abbrev <ident>` in Salt*/ and return (path, line, text up to its body end)."""
    r = subprocess.run(["git", "-C", REPO, "grep", "-n", "-E",
                        r"^" + r"(noncomputable )?(def|abbrev) " + re.escape(short(ident)) + r"( |$|:)",
                        "--", "Salt*"], capture_output=True, text=True)
    hits = [h for h in r.stdout.splitlines() if h]
    if len(hits) != 1:
        return None
    path, line, _ = hits[0].split(":", 2)
    text = read(path)
    lines = text.split("\n")
    i = int(line) - 1
    out = [lines[i]]
    j = i + 1
    while j < len(lines) and lines[j].startswith((" ", "\t")) and lines[j].strip():
        out.append(lines[j])
        j += 1
    return path, i + 1, "\n".join(out).rstrip()


def ledger_line(name: str) -> str | None:
    """`path:line` of an `#audit_axioms` block (header or continuation line) naming `name`."""
    bl = read(os.path.join("scripts", "blueprint_lint.py")).split("\n")
    for k, x in enumerate(bl):
        if x.strip() == f'"{name}",':
            return f"scripts/blueprint_lint.py:{k + 1} (HEADLINERS)"
    r = subprocess.run(["git", "-C", REPO, "grep", "-n", "-F", name, "--", "Salt*"],
                       capture_output=True, text=True)
    for hit in r.stdout.splitlines():
        path, line, body = hit.split(":", 2)
        toks = body.split()
        if name not in toks:
            continue
        if body.startswith("#audit_axioms"):
            return f"{path}:{line}"
        # a continuation line: walk up to its block's header
        lines = read(path).split("\n")
        k = int(line) - 1
        while k > 0 and lines[k].startswith((" ", "\t")) and lines[k].strip():
            k -= 1
        if lines[k].startswith("#audit_axioms"):
            return f"{path}:{line}"
    return None


def first_commit(path: str, name: str) -> tuple[str, str] | None:
    """(short sha, author date) of the first commit adding `theorem <short>` to `path`."""
    r = subprocess.run(["git", "-C", REPO, "log", "--reverse", "--format=%h %as",
                        "-S", "theorem " + short(name), "--", path],
                       capture_output=True, text=True)
    rows = [x for x in r.stdout.splitlines() if x.strip()]
    if not rows:
        return None
    sha, date = rows[0].split()
    return sha, date


def results_rows() -> dict[str, str]:
    """Lean name -> plain one-line statement, from docs/RESULTS.md."""
    out = {}
    for line in read(RESULTS).split("\n"):
        if not line.startswith("| `"):
            continue
        cells = split_row(line)
        m = re.match(r"`([^`]+)`", cells[0])
        if m:
            plain = cells[1].replace("\\|", "|")
            # a sentence that points at the RESULTS table's own layout means nothing here
            plain = " ".join(x for x in re.split(r"(?<=\.) ", plain) if "this table" not in x)
            out.setdefault(m.group(1), plain)
    return out


def split_row(line: str) -> list[str]:
    body = line.strip().strip("|")
    cells, cur, i = [], [], 0
    while i < len(body):
        if body[i] == "\\" and body[i + 1:i + 2] == "|":
            cur.append("\\|")
            i += 2
            continue
        if body[i] == "|":
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(body[i])
        i += 1
    cells.append("".join(cur).strip())
    return cells


def digest(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()[:16]


# ---------------------------------------------------------------- one entry per theorem
def collect() -> tuple[list[dict], list[str]]:
    rows = results_rows()
    entries, problems = [], []
    for section, name, path in HEADLINES:
        e = {"section": section, "name": name, "path": path}
        try:
            text = read(path)
        except OSError:
            problems.append(f"{name}: file {path} missing")
            continue
        i = find_decl(text, name)
        if i is None:
            problems.append(f"{name}: no `theorem {short(name)}` in {path}")
            continue
        e["line"] = i + 1
        e["statement"] = signature(text, i)
        ident = conclusion_ident(e["statement"])
        e["unfold"] = find_def(ident) if ident else None
        if ident and e["unfold"] is None:
            problems.append(f"{name}: its statement is the name `{ident}`, whose definition was not found once")
        e["digest"] = digest(e["statement"] + "\n" + (e["unfold"][2] if e["unfold"] else ""))
        fc = first_commit(path, name)
        if fc is None:
            problems.append(f"{name}: no commit adds `theorem {short(name)}` to {path} (shallow clone?)")
            e["sha"], e["date"] = "?", "?"
        else:
            e["sha"], e["date"] = fc
        e["ledger"] = ledger_line(name)
        if e["ledger"] is None:
            problems.append(f"{name}: no #audit_axioms line names it")
        e["plain"] = rows.get(name)
        if e["plain"] is None:
            problems.append(f"{name}: no row in {RESULTS}")
        entries.append(e)
    return entries, problems


# ---------------------------------------------------------------- the receipt
def module_of(path: str) -> str:
    return path[:-len(".lean")].replace("/", ".")


def build_targets() -> list[str]:
    """Term (1)'s args: every module that DEFINES a headline theorem."""
    return sorted({module_of(p) for _, _, p in HEADLINES})


def audit_file() -> str:
    mods = build_targets()
    out = ["-- Generated by `" + COMMAND + " --audit-file`. A scratch file: never commit it.",
           "-- FIRST build the defining modules: `../saltbuild.sh $(" + COMMAND + " --build-targets)`;",
           "-- THEN audit this file: `../saltbuild.sh <this file>`; pass both logs to `--receipt`."]
    out += [f"import {m}" for m in mods]
    out += [""]
    out += [f"#print axioms {n}" for _, n, _ in HEADLINES]
    out += ["-- The IMPORTED control: a core constant, read from its olean's table; it must print",
            f"-- `{CONTROL_AXIOM}`, so the imported path is shown able to report an axiom.",
            f"#print axioms {CONTROL}", ""]
    return "\n".join(out)


AUDIT_REC = re.compile(r"^(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) \| (build|audit) \| ([^|]+?) \| args=([^|]*?) \|"
                       r"(?: sha256=\S+)? ?HEAD=(\S+) \| .*?\| EXIT=(\d+) \|(.*)$")


def fleet_audit_path() -> str | None:
    """Where `../saltbuild.sh` writes its machine record: $SALTBUILD_AUDITLOG, else the default
    the wrapper itself names (read from the wrapper, so no path is written here)."""
    if os.environ.get("SALTBUILD_AUDITLOG"):
        return os.environ["SALTBUILD_AUDITLOG"]
    try:
        w = open(os.path.join(os.path.dirname(REPO), "saltbuild.sh"), encoding="utf-8").read()
    except OSError:
        return None
    m = re.search(r'SALTBUILD_AUDITLOG-([^}"]+)\}', w)
    return m.group(1) if m else None


def fleet_records(text: str, cwd: str) -> list[dict]:
    """The fleet audit log's machine-written lines for runs in `cwd`, oldest first."""
    out = []
    for line in text.splitlines():
        m = AUDIT_REC.match(line)
        if m and os.path.realpath(m.group(3).strip()) == os.path.realpath(cwd):
            out.append({"when": m.group(1), "kind": m.group(2), "args": m.group(4).split(),
                        "head": m.group(5), "exit": m.group(6)})
    return out


def pick_records(recs: list[dict], scratch: str) -> tuple[dict | None, dict | None]:
    """The LAST audit run of `scratch`, and the last build before it whose args cover every
    defining module."""
    audits = [r for r in recs if r["kind"] == "audit" and os.path.basename(scratch) in
              [os.path.basename(a) for a in r["args"]]]
    if not audits:
        return None, None
    a = audits[-1]
    need = set(build_targets())
    builds = [r for r in recs if r["kind"] == "build" and r["when"] <= a["when"] and need <= set(r["args"])]
    return (builds[-1] if builds else None), a


TAGGED = re.compile(r":[0-9]+:[0-9]+: error(\([^)]*\))?:|^error: .*:[0-9]+:[0-9]+:", re.M)
AX_LINE = re.compile(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def parse_log(log: str) -> dict:
    """The receipt pair from ONE saltbuild log: the EXIT line, the tagged-error count, and
    one axioms line per declaration (a line may wrap; it is flattened first)."""
    flat = " ".join(log.split())
    exits = re.findall(r"saltbuild EXIT=(\d+)", log)
    axioms = {}
    for m in AX_LINE.finditer(flat):
        nm = m.group(1)
        axs = [a.strip() for a in m.group(3).split(",")] if m.group(3) is not None else []
        axioms[nm] = sorted(a for a in axs if a)
    return {"exit": exits[-1] if exits else None,
            "tagged_errors": len(TAGGED.findall(log)),
            "plain_error_lines": sum(1 for x in log.splitlines() if "error" in x),
            "axioms": axioms}


def receipt_problems(entries: list[dict], rc: dict | None) -> list[str]:
    if rc is None:
        return [f"no receipt at {RECEIPT}: run the audit (see the page's Receipt section)"]
    p = []
    if rc.get("exit") != "0":
        p.append(f"receipt EXIT={rc.get('exit')}, not 0")
    if rc.get("tagged_errors") != 0:
        p.append(f"receipt carries {rc.get('tagged_errors')} tagged error(s)")
    if CONTROL_AXIOM not in rc.get("axioms", {}).get(CONTROL, []):
        p.append(f"receipt's IMPORTED control {CONTROL} does not show {CONTROL_AXIOM} "
                 "(the imported path is not proven able to report an axiom)")
    b = rc.get("build")
    if not b:
        p.append("receipt has no BUILD LINE (term 1): an audit that built nothing reads tables that may be stale "
                 "(it can print 'does not depend on any axioms' over an upstream sorry)")
    else:
        if b.get("exit") != "0" or b.get("tagged_errors") != 0:
            p.append(f"build line EXIT={b.get('exit')} tagged={b.get('tagged_errors')}, not 0/0")
        rec, arec = b.get("record") or {}, rc.get("audit_record") or {}
        missing = sorted(set(build_targets()) - set(rec.get("args", [])))
        if missing:
            p.append(f"build record does not name the defining module(s) {missing}")
        if rec.get("exit") != "0":
            p.append(f"build record EXIT={rec.get('exit')}, not 0")
        if not arec or arec.get("exit") != "0":
            p.append("no audit record with EXIT=0 for the scratch")
        elif not (rec.get("when", "") <= arec.get("when", "")):
            p.append("the build record is not BEFORE the audit record")
        elif rec.get("head") != arec.get("head"):
            p.append(f"build HEAD {rec.get('head')} != audit HEAD {arec.get('head')}")
    for e in entries:
        got = rc.get("axioms", {}).get(e["name"])
        if got is None:
            p.append(f"{e['name']}: no axioms line in the receipt")
        elif not set(got) <= ALLOWED:
            p.append(f"{e['name']}: receipt shows axioms {got}")
        if rc.get("digests", {}).get(e["name"]) != e.get("digest"):
            p.append(f"{e['name']}: statement changed since the receipt (digest "
                     f"{rc.get('digests', {}).get(e['name'])} -> {e.get('digest')}); re-run the audit")
    return p


def logp_scratch(argv: list[str]) -> str:
    """The scratch file the audit ran on (`--scratch F`, default HeadlineAudit.lean)."""
    return argv[argv.index("--scratch") + 1] if "--scratch" in argv else "HeadlineAudit.lean"


def load_receipt() -> dict | None:
    try:
        with open(os.path.join(REPO, RECEIPT), encoding="utf-8") as f:
            return json.load(f)
    except OSError:
        return None


# ---------------------------------------------------------------- the page
def render(entries: list[dict], rc: dict | None) -> str:
    L = ["# Headline results", "",
         f"<!-- GENERATED by `{COMMAND}`. Do not edit by hand; edit HEADLINES in the script. -->", "",
         "The landed top-level results of this repository, one theorem each. Each statement below is "
         "copied from the Lean source by the generator; the Lean statement is the authority, and the "
         "one-line summary beside it is a paraphrase from [RESULTS.md](RESULTS.md), which holds every "
         "registered result (this page is the short list).", "",
         "**What \"axiom-audited\" means here.** Each theorem is checked two ways. (1) Its "
         "ledger (named in its entry) fails CI if the theorem depends on any axiom other than "
         "`propext`, `Classical.choice`, `Quot.sound`: an `#audit_axioms` line fails `lake build`, "
         "and a `scripts/blueprint_lint.py` HEADLINERS entry fails the blueprint lint. (2) The receipt at the foot of "
         "this page, in three parts: a build of every module that defines one of these theorems, "
         "exiting 0 with no errors (an audit that builds nothing reads axiom tables written into each "
         "compiled file at its last build, which can be stale); then an audit log, exiting 0 with no "
         "errors, in which `#print axioms` names only those three for every theorem; and in that log "
         "an imported control, `Lean.reduceBool`, printing `Lean.trustCompiler`. The check is `" + COMMAND + " --check`, which also fails if any statement "
         "has changed since the receipt was taken.", "",
         "**Commit and date** are the first commit in this repository's public history that adds "
         "the declaration to its file, and that commit's author date.", ""]
    section = None
    for e in entries:
        if e["section"] != section:
            section = e["section"]
            L += [f"## {section}", ""]
        L += [f"### `{e['name']}`", "",
              f"{e.get('plain') or '(no RESULTS.md row)'}", "",
              f"`{e['path']}:{e.get('line')}` · commit `{e.get('sha')}` · {e.get('date')} · "
              f"ledger `{e.get('ledger')}`", "",
              "```lean", e.get("statement", ""), "```", ""]
        if e.get("unfold"):
            upath, uline, utext = e["unfold"]
            L += [f"where (`{upath}:{uline}`):", "", "```lean", utext, "```", ""]
    L += ["## Receipt", ""]
    if rc is None:
        L += ["No receipt yet.", ""]
    else:
        b = rc.get("build") or {}
        L += [f"Built at commit `{rc['built_at']}` on {rc['date']}; audit log sha256 `{rc['log_sha256']}`"
              f", build log sha256 `{b.get('log_sha256')}`.", "",
              f"- build line (the {len(build_targets())} defining modules, rebuilt before the audit): "
              f"`saltbuild EXIT={b.get('exit')}` · tagged errors {b.get('tagged_errors')}",
              f"- audit log: `saltbuild EXIT={rc['exit']}` · tagged errors {rc['tagged_errors']}",
              f"- {sum(1 for e in entries if e['name'] in rc['axioms'])} of {len(entries)} theorems "
              f"print only `{', '.join(sorted(ALLOWED))}` (or a subset)",
              f"- imported control `{CONTROL}`: `{', '.join(rc['axioms'].get(CONTROL, []))}`", "",
              "To re-take it: `" + COMMAND + " --audit-file HeadlineAudit.lean`, then "
              "`../saltbuild.sh $(" + COMMAND + " --build-targets) > build.log 2>&1`, then "
              "`../saltbuild.sh HeadlineAudit.lean > audit.log 2>&1`, then `" + COMMAND +
              " --receipt build.log audit.log` and regenerate this page.", ""]
    return "\n".join(L).rstrip() + "\n"


# ---------------------------------------------------------------- self-test
def self_test() -> int:
    fails = 0

    def check(label, cond):
        nonlocal fails
        print(("PASS  " if cond else "FAIL  ") + label)
        fails += 0 if cond else 1

    src = "/-- doc\ntheorem foo : x := y -/\ntheorem foo (a : Nat)\n    (h : a = (1 : Nat)) : a + 0 = a := by\n  simp\n"
    i = find_decl(src, "X.foo")
    check("find_decl skips a signature quoted inside a comment", i == 2)
    check("signature stops at the depth-0 :=", signature(src, i).endswith(": a + 0 = a"))
    check("signature keeps the := inside parentheses", "(1 : Nat)" in signature(src, i))
    check("conclusion_ident reads a bare named Prop", conclusion_ident("theorem t : Foo.Bar") == "Foo.Bar")
    check("conclusion_ident refuses a compound type", conclusion_ident("theorem t : a = b") is None)
    check("conclusion_ident reads a named Prop applied to binders",
          conclusion_ident("theorem v (k r : ℕ) (hk : 2 ≤ k) : VmvtBound k r") == "VmvtBound")
    log = ("x.lean:3:0: error(lean.unknownIdentifier): unknown\nerror: y.lean:1:2: bad\n"
           "'A.b' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
           "'C' does not depend on any axioms\n'D' depends on axioms: [sorryAx]\nsaltbuild EXIT=1\n")
    r = parse_log(log)
    check("parse_log counts BOTH error orders", r["tagged_errors"] == 2)
    check("parse_log reads a wrapped axioms line", r["axioms"].get("A.b") == ["Classical.choice", "Quot.sound", "propext"])
    check("parse_log reads the no-axioms form", r["axioms"].get("C") == [])
    check("parse_log reads the EXIT line", r["exit"] == "1")
    ent = [{"name": "A.b", "digest": "d1"}]
    cwd = "/r/salt"
    tg = build_targets()
    flog = (f"2026-11-23 05:00:00 | build | {cwd} | args={' '.join(tg)} | HEAD=abc | cap=lakefile | EXIT=0 | start=x\n"
            f"2026-11-23 05:01:00 | audit | {cwd} | args=HeadlineAudit.lean | sha256=ff HEAD=abc | cap=24000 | EXIT=0 | start=y\n"
            f"2026-11-23 05:02:00 | audit | /elsewhere | args=HeadlineAudit.lean | sha256=ff HEAD=zzz | cap=24000 | EXIT=0 | start=y\n")
    brec, arec = pick_records(fleet_records(flog, cwd), "HeadlineAudit.lean")
    check("fleet record: the build covering every defining module is found", brec is not None and brec["head"] == "abc")
    check("fleet record: another tree's audit run is not taken", arec is not None and arec["head"] == "abc")
    late = flog.replace("05:00:00 | build", "05:09:00 | build")
    check("fleet record: a build AFTER the audit is not taken", pick_records(fleet_records(late, cwd), "HeadlineAudit.lean")[0] is None)
    part = flog.replace(f"args={' '.join(tg)}", f"args={' '.join(tg[1:])}")
    check("fleet record: a build missing one defining module is not taken",
          pick_records(fleet_records(part, cwd), "HeadlineAudit.lean")[0] is None)
    good = {"exit": "0", "tagged_errors": 0, "axioms": {"A.b": ["propext"], CONTROL: [CONTROL_AXIOM]},
            "digests": {"A.b": "d1"}, "build": {"exit": "0", "tagged_errors": 0, "record": brec},
            "audit_record": arec}
    check("a sound receipt passes", receipt_problems(ent, good) == [])
    old_form = {"exit": "0", "tagged_errors": 0, "digests": {"A.b": "d1"},
                "axioms": {"A.b": ["propext"], "Salt.HeadlineAudit.sorry_control": ["sorryAx"]}}
    check("RED: the OLD receipt form (no build line, in-file sorry control) is refused",
          receipt_problems(ent, old_form) != [])
    for label, mut in [
        ("mutant: EXIT=1", {**good, "exit": "1"}),
        ("mutant: a tagged error", {**good, "tagged_errors": 1}),
        ("mutant: imported control without its axiom", {**good, "axioms": {"A.b": ["propext"], CONTROL: []}}),
        ("mutant: only an in-file sorry control", {**good, "axioms": {"A.b": ["propext"], "X.sorry_control": ["sorryAx"]}}),
        ("mutant: a fourth axiom", {**good, "axioms": {"A.b": ["sorryAx"], CONTROL: [CONTROL_AXIOM]}}),
        ("mutant: theorem missing from receipt", {**good, "axioms": {CONTROL: [CONTROL_AXIOM]}}),
        ("mutant: statement changed since receipt", {**good, "digests": {"A.b": "d2"}}),
        ("mutant: STALE-CLEAN shape, no build line", {k: v for k, v in good.items() if k != "build"}),
        ("mutant: build log EXIT=1", {**good, "build": {**good["build"], "exit": "1"}}),
        ("mutant: build record names too few modules", {**good, "build": {**good["build"], "record": {**brec, "args": tg[1:]}}}),
        ("mutant: build record after the audit", {**good, "build": {**good["build"], "record": {**brec, "when": "2026-11-23 06:00:00"}}}),
        ("mutant: build at another HEAD", {**good, "build": {**good["build"], "record": {**brec, "head": "def"}}}),
        ("mutant: no audit record", {**good, "audit_record": None}),
    ]:
        check(label + " is refused", receipt_problems(ent, mut) != [])
    check("no receipt is refused", receipt_problems(ent, None) != [])
    print(f"self-test: {'OK' if fails == 0 else f'{fails} FAILED'}")
    return 1 if fails else 0


# ---------------------------------------------------------------- main
def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    if "--audit-file" in argv:
        out = argv[argv.index("--audit-file") + 1]
        with open(out, "w", encoding="utf-8") as f:
            f.write(audit_file())
        print(f"wrote {out} ({len(HEADLINES)} theorems + 1 control)")
        return 0
    entries, problems = collect()
    if "--build-targets" in argv:
        print(" ".join(build_targets()))
        return 0
    if "--receipt" in argv:
        i = argv.index("--receipt")
        if len(argv) < i + 3:
            print("usage: --receipt BUILDLOG AUDITLOG (the build of --build-targets, then the scratch audit)")
            return 2
        blogp, logp = argv[i + 1], argv[i + 2]
        braw = open(blogp, "rb").read()
        raw = open(logp, "rb").read()
        rc = parse_log(raw.decode("utf-8", "replace"))
        bl = parse_log(braw.decode("utf-8", "replace"))
        fpath = fleet_audit_path()
        try:
            ftext = open(fpath, encoding="utf-8", errors="replace").read() if fpath else ""
        except OSError:
            ftext = ""
        brec, arec = pick_records(fleet_records(ftext, os.getcwd()), logp_scratch(argv))
        rc["build"] = {"exit": bl["exit"], "tagged_errors": bl["tagged_errors"],
                       "log_sha256": hashlib.sha256(braw).hexdigest()[:16], "record": brec}
        rc["audit_record"] = arec
        head = subprocess.run(["git", "-C", REPO, "rev-parse", "--short=10", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
        date = subprocess.run(["date", "+%Y-%m-%d"], capture_output=True, text=True).stdout.strip()
        rc.update({"built_at": head, "date": date, "log_sha256": hashlib.sha256(raw).hexdigest()[:16],
                   "digests": {e["name"]: e["digest"] for e in entries}})
        rc["axioms"] = {k: v for k, v in rc["axioms"].items()
                        if k in {e["name"] for e in entries} | {CONTROL}}
        with open(os.path.join(REPO, RECEIPT), "w", encoding="utf-8") as f:
            json.dump(rc, f, indent=1, sort_keys=True, ensure_ascii=False)
            f.write("\n")
        rp = receipt_problems(entries, rc)
        print(f"wrote {RECEIPT}: EXIT={rc['exit']} tagged={rc['tagged_errors']} "
              f"axioms lines={len(rc['axioms'])}; problems={len(rp)}")
        for x in rp:
            print("  " + x)
        return 1 if rp else 0
    rc = load_receipt()
    problems += receipt_problems(entries, rc)
    page = render(entries, rc)
    if "--check" in argv:
        try:
            cur = read(PAGE)
        except OSError:
            cur = None
        if cur != page:
            problems.append(f"{PAGE} is stale: run `{COMMAND}`")
        for x in problems:
            print("FAIL  " + x)
        print(f"headline_theorems --check: {len(entries)} theorems, {len(problems)} problem(s)")
        return 1 if problems else 0
    with open(os.path.join(REPO, PAGE), "w", encoding="utf-8") as f:
        f.write(page)
    for x in problems:
        print("WARN  " + x)
    print(f"wrote {PAGE}: {len(entries)} theorems, {len(problems)} problem(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
