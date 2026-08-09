#!/usr/bin/env python3
"""docstring_coverage.py — the SMOKE ALARM for the docstring-vs-file axis.

WHAT IT IS, AND WHAT IT IS NOT
------------------------------
It is NOT a test that a module docstring is CORRECT — no program can check that, which is
exactly why this axis produced 2 hits on its first sweep (2026-08-08 night) after the
name-vs-statement sweep over the same files found neither.

It IS a smoke alarm for the one mechanical shadow that class casts: a public theorem whose
name is never mentioned anywhere in the module docstring.  A header that says "it delivers
THE TWO sums" while the file holds eight rows will light this up, because six of the eight
are unmentioned.

WHY IT EXISTS AT ALL
--------------------
The night's rung hierarchy (kit -> bank -> gate -> BUILD) sorts laws by where they live.  The
name read and the docstring read have no rung-4 form: the kernel does not read names or prose.
This script is the largest mechanizable fragment of the docstring half — it moves the *cheap*
part into an executable that a successor inherits, and leaves the judgement where judgement has
to stay.

⚠️ THE DOMINANT FLAG CLASS IS "DESCRIBES BUT DOES NOT NAME" — measured, not guessed
  This matcher is EXACT on identifiers, so a header that says "the sawtooth Fourier expansion"
  while the row is `sawtooth_fourier_expansion` FLAGS.  Sampled 2026-08-08: `Sawtooth.lean` and
  `NewtonBridge.lean` both describe their rows in prose and never name them.
  ⇒ THREE CLASSES, and only the first is a FALSE CLAIM:
     (1) the header asserts something untrue of the file  ("it delivers THE TWO sums" / "that
         is the WHOLE content of row 10").  A DEFECT.  Two found, both fixed.
     (2) the header DESCRIBES a row but does not NAME it.  Not false — but a reader cannot
         grep from header to row.  A usability gap; the dominant class here.
     (3) a helper the header deliberately omits.  Not a defect at all.
  ⚠️ A raw flag count mixes all three.  Do not report flags as defects; sample first.

⚠️ WHAT A FLAG DOES AND DOES NOT MEAN — read before quoting a count
  A flag says: this header ENUMERATES rows and these ones are absent from it.  It does NOT
  say the absence is a defect: a helper row a header deliberately omits looks identical to a
  row the header never grew to include.  THE TOOL NARROWS; A HUMAN JUDGES.
  Measured 2026-08-08 on Salt/Weil: 21 of 29 files flagged — and a three-file sample showed
  all three DO enumerate (7/11, 7/8, 2/3 mentioned), so those flags are partial-enumeration
  gaps rather than a descriptive-docstring style difference.  ⚠️ Do NOT quote "21 defective
  docstrings"; quote "21 files where a human should look."

⚠️ ITS OWN LIMITS, STATED SO NOBODY READS SILENCE AS SUCCESS
  * a docstring that MENTIONS a row and lies about it passes here.  That is the residue.
  * `private` declarations are skipped by design — a header need not list them.
  * a module with NO docstring is REPORTED, not silently passed.
  * zero public theorems is REPORTED, never treated as clean.

Usage:  python3 scripts/docstring_coverage.py Salt/Weil/GcdDivisorSum.lean [more.lean ...]
        python3 scripts/docstring_coverage.py --all        (every .lean under Salt/)
Exit:   0 = every public theorem is mentioned in its module docstring
        1 = at least one unmentioned (or a module with no docstring / no theorems)
        2 = usage error
"""
import re
import sys
from pathlib import Path

DOCSTRING = re.compile(r"/-!(.*?)-/", re.S)
# public theorem/lemma at column 0; `private` and `protected` are excluded deliberately
DECL = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'’.]*)", re.M)


def audit(path: Path):
    """Return (unmentioned, total, note). `note` is non-empty when the file itself is odd."""
    src = path.read_text(encoding="utf-8")
    blocks = DOCSTRING.findall(src)
    if not blocks:
        return [], 0, "NO MODULE DOCSTRING"
    prose = "\n".join(blocks)
    names = DECL.findall(src)
    if not names:
        return [], 0, "NO PUBLIC THEOREMS"
    unmentioned = [n for n in names if n not in prose]
    return unmentioned, len(names), ""


def main(argv):
    if len(argv) < 2:
        print(__doc__.strip().splitlines()[-4])
        return 2
    if argv[1] == "--all":
        targets = sorted(Path("Salt").rglob("*.lean"))
    else:
        targets = [Path(a) for a in argv[1:]]
    if not targets:
        print("REFUSE: no files matched — an empty population is not a pass.")
        return 2

    bad = 0
    for p in targets:
        if not p.is_file():
            print(f"⛔ {p}: not a file")
            bad += 1
            continue
        unmentioned, total, note = audit(p)
        if note:
            print(f"⚠️  {p}: {note}")
            bad += 1
        elif unmentioned:
            # label GATED on the value: this line cannot print when the list is empty
            print(f"⛔ {p}: {len(unmentioned)}/{total} public theorems unmentioned in the "
                  f"module docstring")
            for n in unmentioned:
                print(f"      {n}")
            bad += 1
        else:
            print(f"✅ {p}: all {total} public theorems mentioned")
    print(f"--- population: {len(targets)} file(s); {bad} flagged ---")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
