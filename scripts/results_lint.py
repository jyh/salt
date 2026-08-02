#!/usr/bin/env python3
"""Results lint (see docs/RESULTS.md — THE LAW OF THIS DOCUMENT).

The trophy room's mechanical teeth. Every row of docs/RESULTS.md claims that a
named Lean declaration exists at a named file, landed on a named date in a named
commit. This script checks the three claims a text file can check without the
kernel:

  1. file exists      — the `File:line` column resolves to a real file under the
                        repo root.
  2. decl exists      — that file actually declares the row's Lean name
                        (regex over theorem/lemma/def/abbrev/structure/instance).
  3. date well-formed — the `Date landed` column is an ISO `YYYY-MM-DD`, and the
                        `Commit` column is a hex sha (7-40 chars).

What this can NOT check: that the row's plain-English statement matches the Lean
statement's meaning, that the date is the RIGHT date, or that the declaration is
sorry-free. Green output means "not mechanically stale", never "the registry is
true". Axiom-cleanliness is certified by the `#audit_axioms` ledgers cited in the
Axioms column and by scripts/blueprint_lint.py — deliberately NOT re-run here,
because this script must stay cheap enough to run on every commit.

Usage: python3 scripts/results_lint.py   (from anywhere)
Exit code 0 = all rows pass; nonzero on any violation.
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "docs", "RESULTS.md")

# A row is a markdown table line with at least the six declared columns.
COLUMNS = ("Theorem", "Plain statement", "File:line", "Date landed", "Commit", "Axioms")

# Column 1: the Lean name, first backticked token in the cell. Namespaces
# allowed; primes allowed (`thm_a2'`); Unicode subscripts allowed (`M₂_squeeze`).
NAME_RE = re.compile(r"`([^`]+)`")
# Column 3: `Salt/Foo/Bar.lean:123`, with or without backticks.
LOC_RE = re.compile(r"([A-Za-z0-9_./\-]+\.lean):(\d+)")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{7,40}$")
# A separator row: |---|---|...
SEP_RE = re.compile(r"^\|[\s:\-|]+\|$")

DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "instance",
    "inductive",
    "class",
)


def decl_regex(short_name: str) -> re.Pattern[str]:
    """Match a top-level declaration of `short_name` in a Lean source."""
    kw = "|".join(DECL_KEYWORDS)
    mods = r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+)*"
    # Lean identifiers continue with letters, digits, _, ', !, ?, and subscripts.
    tail = r"(?![A-Za-z0-9_'\u2080-\u2089\u00b2\u00b3\u00b9])"
    return re.compile(
        rf"^{mods}(?:{kw})\s+{re.escape(short_name)}{tail}",
        re.MULTILINE,
    )


def split_row(line: str) -> list[str]:
    """Split a markdown table row into cells, honouring `\\|` escapes."""
    body = line.strip()
    if body.startswith("|"):
        body = body[1:]
    if body.endswith("|"):
        body = body[:-1]
    cells, cur, i = [], [], 0
    while i < len(body):
        ch = body[i]
        if ch == "\\" and i + 1 < len(body) and body[i + 1] == "|":
            cur.append("|")
            i += 2
            continue
        if ch == "|":
            cells.append("".join(cur).strip())
            cur = []
            i += 1
            continue
        cur.append(ch)
        i += 1
    cells.append("".join(cur).strip())
    return cells


def main() -> int:
    if not os.path.isfile(RESULTS):
        print(f"FAIL  docs/RESULTS.md missing at {RESULTS}")
        return 1

    with open(RESULTS, encoding="utf-8") as fh:
        lines = fh.read().split("\n")

    violations: list[str] = []
    checked = 0
    section = "(preamble)"
    seen_names: dict[str, int] = {}
    source_cache: dict[str, str] = {}

    for lineno, raw in enumerate(lines, start=1):
        if raw.startswith("## "):
            section = raw[3:].strip()
            continue
        if not raw.startswith("|"):
            continue
        if SEP_RE.match(raw.strip()):
            continue

        cells = split_row(raw)
        if len(cells) < len(COLUMNS):
            violations.append(
                f"RESULTS.md:{lineno}  row has {len(cells)} cells, need "
                f"{len(COLUMNS)} ({', '.join(COLUMNS)})"
            )
            continue
        # The header row of each table repeats the column names verbatim.
        if cells[0].startswith("Theorem") and cells[2].startswith("File"):
            continue

        name_cell, _stmt, loc_cell, date_cell, commit_cell, _axioms = cells[:6]

        name_match = NAME_RE.search(name_cell)
        if not name_match:
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  no backticked Lean name in "
                f"column 1: {name_cell!r}"
            )
            continue
        full_name = name_match.group(1).strip()
        short_name = full_name.split(".")[-1]
        checked += 1

        if full_name in seen_names:
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}` already has a "
                f"row at line {seen_names[full_name]} (one row per result)"
            )
        else:
            seen_names[full_name] = lineno

        # (a) the file exists
        loc_match = LOC_RE.search(loc_cell)
        if not loc_match:
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}`: column 3 is not "
                f"a `path.lean:line` location: {loc_cell!r}"
            )
            continue
        relpath, _decl_line = loc_match.group(1), loc_match.group(2)
        abspath = os.path.join(ROOT, relpath)
        if not os.path.isfile(abspath):
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}`: file not found: "
                f"{relpath}"
            )
            continue

        # (b) the file declares that name
        if abspath not in source_cache:
            with open(abspath, encoding="utf-8") as fh:
                source_cache[abspath] = fh.read()
        if not decl_regex(short_name).search(source_cache[abspath]):
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}`: no declaration "
                f"of `{short_name}` in {relpath}"
            )

        # (c) the row has a date (and a commit that looks like one)
        if not DATE_RE.match(date_cell):
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}`: date "
                f"{date_cell!r} is not ISO YYYY-MM-DD"
            )
        commit = commit_cell.strip().strip("`")
        if not COMMIT_RE.match(commit):
            violations.append(
                f"RESULTS.md:{lineno}  [{section}]  `{full_name}`: commit "
                f"{commit_cell!r} is not a 7-40 char hex sha"
            )

    if violations:
        print(f"results_lint: {len(violations)} violation(s) over {checked} row(s)\n")
        for v in violations:
            print(f"  FAIL  {v}")
        return 1

    print(f"results_lint: OK — {checked} rows, all verified "
          f"(file exists, declaration exists, date + commit well-formed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
