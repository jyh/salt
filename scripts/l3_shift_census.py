#!/usr/bin/env python3
"""L3-FORK CENSUS — the shift-h dependence surface, re-derived mechanically.

WHY THIS SCRIPT EXISTS.  The shift-2 / shift-h campaign was priced off a hand
census ("84 syntactic sites, 85 structural sites, 13 files"), and two independent
refuter passes ordered that number re-derived by a committed script with published
counts before any arm-3 Lean is written (the idiom law: derived expectations ·
declared coverage · published receipts).  W-F1 lands the fork's definition layer;
this script lands its census receipt.

WHAT IT DOES, in one sentence: it extracts every `liouville (…)` argument and
every `windowVal H _ (…)` offset in the corpus STRUCTURALLY (balanced-paren
parsing, not a fixed-string grep), applies a PRINTED inclusion criterion to decide
whether the shift h enters that offset, and reports the resulting counts against
the four expected numbers-of-record — reporting any drift rather than reconciling
it.

Run:  python3 scripts/l3_shift_census.py         (from the repo root, or anywhere)

Exit status is always 0: this is an instrument, not a gate.  Read the DRIFT
section; it is the verdict.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

# ---------------------------------------------------------------------------
# 0 · scope
# ---------------------------------------------------------------------------

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SALT = os.path.join(REPO, "Salt")

# The file W-F1 itself adds.  It is NOT excluded from anything silently — every
# total below is printed twice when it matters, once salt-wide and once for the
# pre-fork baseline, with the exclusion named in the output.
FORK_FILE = "Salt/Entropy/Chowla/ShiftFork.lean"
HUB_FILE = "Salt/Entropy/All.lean"
W_F1_TOUCHED = (FORK_FILE, HUB_FILE)

CHOWLA_DIR = "Salt/Entropy/Chowla/"

# The two fixed strings the hand census used.  Kept as NAMED SUB-ROWS of the
# structured scan so the old number and the new one can be compared at the byte.
FIXED_I = "liouville (n + 1)"
FIXED_II = "(j + (p : ℕ))"

# The numbers of record, from the hand census (spine reader facts 12/17/26) as
# re-measured by the 08/15 extraction pass at tree 8548842.
EXPECTED = {
    ("i", "salt-wide"): (84, 12),
    ("i", "chowla-dir"): (79, 10),
    ("ii", "chowla-dir"): (85, 13),
    ("ii", "salt-wide"): (87, 14),
}

# The `bigXi*` consumer surface, measured the same pass by `grep -rn -F "bigXi"`
# — a count of matching LINES, not of occurrences.  Both are printed below.
EXPECTED_BIGXI_LINES = 387
EXPECTED_BIGXI_FILES = 35

# ---------------------------------------------------------------------------
# 1 · the inclusion criterion, stated before it is applied
# ---------------------------------------------------------------------------

CRITERION = """\
INCLUSION CRITERION — "does h enter this offset?"

  The landed spine is Tao 1509.05422 at shift h = 1.  De-specializing to shift h
  changes exactly two textual things:

    shape (i)   the CARRIED SCALAR    λ(n)·λ(n+1)          ->  λ(n)·λ(n+h)
    shape (ii)  the F-BRIDGE PAIRING  x₁(j)·x₂(j+p)        ->  x₁(j)·x₂(j+p·h)

  An extracted offset is therefore counted h-CARRYING iff it is the SECOND FACTOR
  of a landed correlation pair — mechanically:

    write the offset as a multiset of top-level `+`-atoms; the offset is
    h-carrying iff removing ONE atom from the shift set

        SHIFT = { 1 , p , (p : ℕ) , 2 }

    yields the atom multiset of another `liouville`/`windowVal` offset occurring
    IN THE SAME FILE (its pair's first factor).

  This is deliberately a *structural* test, not a fixed-string grep: it survives
  `+`-reassociation (`n + j + p + 1` is recognised as `n + j + 1` plus `p`), and it
  rejects an offset whose `+1` has no partner — which is exactly the window's
  1-offset indexing (`liouvilleWindow` gives the window λ(n+1),…,λ(n+H), and that
  `+1` would be identical at any shift h).

  The criterion is FALLIBLE and every row is printed with its matched partner so a
  reader can audit the call.  Rows where a shift-generic offset is already
  parametric (`liouville (n + a)`, `corr_shift_le`'s two free offsets) are counted
  OUT: no edit is needed there, the offset is general already.
"""

SHIFT_ATOMS = {"1", "p", "(p : ℕ)", "2"}

# ---------------------------------------------------------------------------
# 2 · structural extraction
# ---------------------------------------------------------------------------


def git_changed():
    """Paths under Salt/ that differ from git HEAD (modified or untracked)."""
    try:
        out = subprocess.run(["git", "-C", REPO, "status", "--porcelain", "--", "Salt"],
                             capture_output=True, text=True, check=True).stdout
    except Exception:
        return set()
    return {line[3:].strip().strip('"') for line in out.splitlines() if line.strip()}


def git_show_head(rel):
    """The file's bytes at HEAD, or None if it does not exist there."""
    try:
        r = subprocess.run(["git", "-C", REPO, "show", f"HEAD:{rel}"],
                           capture_output=True, text=True)
    except Exception:
        return None
    return r.stdout if r.returncode == 0 else None


def lean_files():
    out = []
    for dirpath, _dirnames, filenames in os.walk(SALT):
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                out.append(os.path.relpath(p, REPO))
    out.sort()
    return out


def match_paren(s: str, i: int) -> int:
    """s[i] == '('; return the index just past the matching ')' (or -1)."""
    depth = 0
    while i < len(s):
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return -1


TOKEN_LIOUVILLE = re.compile(r"(?<![A-Za-z0-9_'])liouville(?![A-Za-z0-9_'])")
TOKEN_WINDOWVAL = re.compile(r"(?<![A-Za-z0-9_'])windowVal(?![A-Za-z0-9_'])")


def read_arg(text: str, i: int):
    """Read one Lean argument starting at text[i] (skipping spaces/newlines).

    Returns (arg_string, end_index) or (None, i)."""
    n = len(text)
    while i < n and text[i] in " \n":
        i += 1
    if i >= n:
        return None, i
    if text[i] == "(":
        j = match_paren(text, i)
        if j < 0:
            return None, i
        return text[i:j], j
    j = i
    while j < n and (text[j].isalnum() or text[j] in "_'.ℕℝℂ"):
        j += 1
    if j == i:
        return None, i
    return text[i:j], j


def extract_liouville(text: str):
    """-> list of (arg_string, arg_start, arg_end).

    The recorded span is the ARGUMENT's own span, not the whole application: the
    decoy control below asks whether a decoy string is itself counted as an
    h-carrying OFFSET, and a span that swallowed the function head would answer
    a different (and useless) question."""
    out = []
    for m in TOKEN_LIOUVILLE.finditer(text):
        arg, end = read_arg(text, m.end())
        if arg is None:
            continue
        out.append((arg, end - len(arg), end))
    return out


def extract_windowval(text: str):
    """`windowVal H x OFFSET` -> list of (offset_string, offset_start, offset_end)."""
    out = []
    for m in TOKEN_WINDOWVAL.finditer(text):
        i = m.end()
        args = []
        ok = True
        for _ in range(3):
            a, i = read_arg(text, i)
            if a is None:
                ok = False
                break
            args.append(a)
        if ok:
            out.append((args[2], i - len(args[2]), i))
    return out


def atoms(expr: str):
    """Top-level `+`-atoms of an offset expression, outer parens stripped."""
    e = expr.strip()
    while e.startswith("(") and match_paren(e, 0) == len(e):
        e = e[1:-1].strip()
    parts, depth, cur = [], 0, ""
    for ch in e:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "+" and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    parts.append(cur.strip())
    return tuple(sorted(p for p in parts if p))


def classify(forms_in_file, key):
    """Return (True, partner_form) if `key` is h-carrying in this file, else (False, None).

    `forms_in_file` maps atom-tuple -> a representative source form."""
    for s in SHIFT_ATOMS:
        k = list(key)
        if s in k:
            k.remove(s)
            partner = tuple(sorted(k))
            if partner in forms_in_file and partner != key:
                return True, (forms_in_file[partner], s)
    return False, None


# ---------------------------------------------------------------------------
# 3 · the scan
# ---------------------------------------------------------------------------


def scan(extractor):
    """-> (rows, hitspans)

    rows: form -> dict(count, files Counter, hcarrying bool, partner, shift)
    hitspans: relpath -> list of (start, end) for h-CARRYING occurrences."""
    per_file_occ = {}
    texts = {}
    for rel in lean_files():
        with open(os.path.join(REPO, rel), encoding="utf-8") as fh:
            t = fh.read()
        texts[rel] = t
        occ = extractor(t)
        if occ:
            per_file_occ[rel] = occ

    rows = {}
    hitspans = defaultdict(list)
    for rel, occ in per_file_occ.items():
        forms_in_file = {}
        for arg, _s, _e in occ:
            forms_in_file.setdefault(atoms(arg), arg)
        for arg, s, e in occ:
            key = atoms(arg)
            hc, info = classify(forms_in_file, key)
            r = rows.setdefault(
                arg,
                {"count": 0, "files": Counter(), "hc": hc, "partner": None, "shift": None},
            )
            r["count"] += 1
            r["files"][rel] += 1
            if hc:
                r["hc"] = True
                r["partner"], r["shift"] = info
                hitspans[rel].append((s, e))
    return rows, hitspans


def totals(rows, pred_file):
    n = 0
    fs = set()
    for form, r in rows.items():
        if not r["hc"]:
            continue
        for rel, c in r["files"].items():
            if pred_file(rel):
                n += c
                fs.add(rel)
    return n, len(fs)


def fixed_string_counts(fixed, pred_file):
    n = 0
    fs = set()
    for rel in lean_files():
        if not pred_file(rel):
            continue
        with open(os.path.join(REPO, rel), encoding="utf-8") as fh:
            c = fh.read().count(fixed)
        if c:
            n += c
            fs.add(rel)
    return n, len(fs)


SCOPES = {
    "salt-wide": lambda rel: True,
    "chowla-dir": lambda rel: rel.startswith(CHOWLA_DIR),
    "baseline (salt-wide minus the W-F1 fork file)": lambda rel: rel != FORK_FILE,
}


def head(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def print_rows(rows, limit=None):
    order = sorted(rows.items(), key=lambda kv: (-kv[1]["count"], kv[0]))
    if limit:
        order = order[:limit]
    print(f"  {'n':>4}  {'h?':<4} {'offset':<34} {'partner (+shift)'}")
    print(f"  {'-'*4}  {'-'*4} {'-'*34} {'-'*30}")
    for form, r in order:
        mark = "IN " if r["hc"] else "out"
        part = ""
        if r["hc"]:
            part = f"{r['partner']}  + {r['shift']}"
        print(f"  {r['count']:>4}  {mark:<4} {form:<34} {part}")


def print_files(rows, pred_file, label):
    per = Counter()
    for form, r in rows.items():
        if not r["hc"]:
            continue
        for rel, c in r["files"].items():
            if pred_file(rel):
                per[rel] += c
    print(f"  per-file h-carrying counts [{label}]:")
    for rel, c in sorted(per.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {c:>4}  {rel}")
    print(f"    ---- {sum(per.values())} occurrences across {len(per)} files")
    return per


# ---------------------------------------------------------------------------
# 4 · main
# ---------------------------------------------------------------------------


def main():
    try:
        sha = subprocess.run(
            ["git", "-C", REPO, "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, check=True).stdout.strip()
        dirty = subprocess.run(
            ["git", "-C", REPO, "status", "--porcelain", "Salt"],
            capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        sha, dirty = "unknown", ""

    files = lean_files()
    head("L3-FORK CENSUS — the shift-h dependence surface")
    print(f"  repo      : {REPO}")
    print(f"  HEAD      : {sha}{'  (Salt/ has uncommitted changes)' if dirty else ''}")
    print(f"  scanned   : {len(files)} .lean files under Salt/")
    print(f"  fork file : {FORK_FILE} "
          f"{'PRESENT' if FORK_FILE in files else 'ABSENT'} — the file W-F1 adds")
    print()
    print(CRITERION)

    # ---- shape (i) ---------------------------------------------------------
    head("SHAPE (i) — THE CARRIED SCALAR:  structured `liouville (…)` extraction")
    rows_i, spans_i = scan(extract_liouville)
    tot_occ = sum(r["count"] for r in rows_i.values())
    print(f"  {len(rows_i)} distinct argument forms, {tot_occ} occurrences, "
          f"read by balanced-paren parse (NOT a fixed-string grep).")
    print()
    print_rows(rows_i)
    print()
    print_files(rows_i, SCOPES["salt-wide"], "salt-wide")
    print()
    print("  NOTE on the fork's own row: `liouville (n + h)` (ShiftFork.lean, W-F1's")
    print("  `logChowlaFails`) reads OUT above, because `h` is not in the SHIFT set —")
    print("  the criterion asks whether h WOULD HAVE TO ENTER an h=1 offset, and that")
    print("  offset is already general.  It is the census's own fixed point, not a miss.")
    print()
    print(f"  NAMED SUB-ROW — the hand census's fixed string  `{FIXED_I}`:")
    for label, pred in SCOPES.items():
        n, f = fixed_string_counts(FIXED_I, pred)
        print(f"    {n:>4} occurrences / {f:>2} files   [{label}]")
    print()
    print("  NAIVE-GREP CONTRAST (what the criterion buys):")
    naive, naive_f = fixed_string_counts("(n + 1)", SCOPES["salt-wide"])
    print(f"    {naive:>4} occurrences / {naive_f:>2} files   "
          f"[salt-wide, the bare string `(n + 1)`]")
    print("    — i.e. a bare `(n + 1)` grep over-counts by "
          f"{naive - fixed_string_counts(FIXED_I, SCOPES['salt-wide'])[0]}; "
          "the structured scan never sees those.")

    # ---- shape (ii) --------------------------------------------------------
    head("SHAPE (ii) — THE F-BRIDGE PAIRING:  structured `windowVal H _ (…)` extraction")
    rows_ii, spans_ii = scan(extract_windowval)
    tot_occ2 = sum(r["count"] for r in rows_ii.values())
    print(f"  {len(rows_ii)} distinct third-argument (offset) forms, {tot_occ2} "
          f"`windowVal` applications parsed.")
    print()
    print_rows(rows_ii)
    print()
    print_files(rows_ii, SCOPES["salt-wide"], "salt-wide")
    print()
    print(f"  NAMED SUB-ROW — the hand census's fixed string  `{FIXED_II}`:")
    for label, pred in SCOPES.items():
        n, f = fixed_string_counts(FIXED_II, pred)
        print(f"    {n:>4} occurrences / {f:>2} files   [{label}]")
    wv = rows_ii.get(FIXED_II)
    if wv:
        print(f"    of which {wv['count']} sit in `windowVal`'s third-argument position; "
              f"the remainder occur in other contexts.")

    # ---- the four expected numbers ----------------------------------------
    head("THE FOUR NUMBERS OF RECORD — expected vs measured, WITH SCOPES")
    drift = []
    measured = {
        ("i", "salt-wide"): fixed_string_counts(FIXED_I, SCOPES["salt-wide"]),
        ("i", "chowla-dir"): fixed_string_counts(FIXED_I, SCOPES["chowla-dir"]),
        ("ii", "chowla-dir"): fixed_string_counts(FIXED_II, SCOPES["chowla-dir"]),
        ("ii", "salt-wide"): fixed_string_counts(FIXED_II, SCOPES["salt-wide"]),
    }
    print(f"  {'shape':<7} {'scope':<12} {'expected':<14} {'measured':<14} verdict")
    print(f"  {'-'*7} {'-'*12} {'-'*14} {'-'*14} {'-'*20}")
    for key in [("i", "salt-wide"), ("i", "chowla-dir"),
                ("ii", "chowla-dir"), ("ii", "salt-wide")]:
        en, ef = EXPECTED[key]
        mn, mf = measured[key]
        ok = (en, ef) == (mn, mf)
        if not ok:
            drift.append(f"shape ({key[0]}) [{key[1]}]: expected {en}/{ef}, measured {mn}/{mf}")
        print(f"  {'('+key[0]+')':<7} {key[1]:<12} {str(en)+' / '+str(ef)+' files':<14} "
              f"{str(mn)+' / '+str(mf)+' files':<14} {'REPRODUCES' if ok else 'DRIFT'}")
    print()
    print("  Scope note: the hand census's `85 / 13 files` is Salt/Entropy/Chowla/ ONLY;")
    print("  salt-wide the same pattern is 87 / 14, the extra 2 being Salt/MR/S16Uniform.lean.")
    print("  Both are printed above so no consumer has to guess which one it inherited.")

    # ---- the structured totals beside them ---------------------------------
    head("THE STRUCTURED TOTALS (the criterion's own answer, beside the fixed strings)")
    for shape, rows in (("i", rows_i), ("ii", rows_ii)):
        for label, pred in SCOPES.items():
            n, f = totals(rows, pred)
            print(f"  shape ({shape})  h-carrying: {n:>4} occurrences / {f:>2} files   [{label}]")
    print()
    print("  These are NOT the same objects as the two fixed strings and are not")
    print("  expected to agree with them: the structured scan counts every h-carrying")
    print("  offset of its shape, the fixed strings count one spelling each.  The")
    print("  DilationStability.lean rows are the clearest gap — see the per-file table.")
    ds = "Salt/Entropy/Chowla/DilationStability.lean"
    n_ds = sum(c for r in rows_i.values() if r["hc"] for rel, c in r["files"].items() if rel == ds)
    print(f"  DilationStability.lean, shape (i) h-carrying: {n_ds} occurrences "
          f"(hand estimate carried into the design block: ~9).")
    if n_ds != 9:
        drift.append(f"DilationStability.lean shape-(i) h-carrying: block said ~9, measured {n_ds}")

    # ---- decoys ------------------------------------------------------------
    head("DECOYS — the NEGATIVE CONTROL")
    print("  Each decoy is a `+1`/`n+1` that a naive grep would sweep in and that is NOT")
    print("  a Chowla shift.  For each: its raw corpus count, and how many of its")
    print("  occurrences fall inside a span the structured scan classified h-CARRYING.")
    print("  Every in-hit-set count MUST be 0; a nonzero one is a bug in the criterion.")
    print()
    decoys = [
        ("liouvilleWindow", "the window's own 1-offset indexing (Windows.lean:18,:26-28) — "
                            "identical at any shift h"),
        ("Real.log (5 * Tann + 1)", "MR numeral arithmetic, no Liouville anywhere"),
        ("doorLadder", "MR's `doorLadder … (n + 1)` — a ladder index, not a shift"),
        ("Finset.range (n + 1)", "a Nat successor as a range bound"),
    ]
    allspans = defaultdict(list)
    for d in (spans_i, spans_ii):
        for rel, sp in d.items():
            allspans[rel].extend(sp)
    for pat, why in decoys:
        raw = 0
        inside = 0
        for rel in files:
            with open(os.path.join(REPO, rel), encoding="utf-8") as fh:
                t = fh.read()
            start = 0
            while True:
                k = t.find(pat, start)
                if k < 0:
                    break
                raw += 1
                for (a, b) in allspans.get(rel, []):
                    if a <= k < b:
                        inside += 1
                        break
                start = k + 1
        print(f"  {raw:>5} occurrences  |  IN HIT SET: {inside}  |  `{pat}`")
        print(f"         {why}")
        if inside:
            drift.append(f"decoy `{pat}` landed inside the hit set {inside} time(s)")
    print()
    print("  (Fact 25's other MR `n + 1` families — S13CapFloor, M4Rows*, V7A — are")
    print("   `Finset.range (n+1)` / `doorLadder … (n+1)` / numeral arithmetic and are")
    print("   covered by the last two rows.)")

    # ---- the third count ---------------------------------------------------
    head("THE THIRD COUNT — the `bigXi*` CONSUMER SURFACE")
    print("  This is the surface the hand census never counted at all, and it is the")
    print("  number that decided FORK over generalize-in-place: it is disjoint from the")
    print("  pairing census and crosses into the Salt/MR arc/count lane.")
    print()
    per = Counter()
    stats = {k: [0, 0, set()] for k in ("all", "head")}
    changed = git_changed()
    reconstructed = []
    for rel in files:
        with open(os.path.join(REPO, rel), encoding="utf-8") as fh:
            t = fh.read()
        occ = t.count("bigXi")
        if occ:
            per[rel] = occ
            stats["all"][0] += sum(1 for line in t.splitlines() if "bigXi" in line)
            stats["all"][1] += occ
            stats["all"][2].add(rel)
        # the HEAD scope: for a file this wave changed, count its HEAD bytes
        if rel in changed:
            th = git_show_head(rel)
            if th is None:
                continue           # untracked at HEAD: the file did not exist
            reconstructed.append(rel)
        else:
            th = t
        occ_h = th.count("bigXi")
        if occ_h:
            stats["head"][0] += sum(1 for line in th.splitlines() if "bigXi" in line)
            stats["head"][1] += occ_h
            stats["head"][2].add(rel)
    labels = {
        "all": "WORKING TREE, i.e. POST-W-F1",
        "head": f"AT git HEAD ({sha}), i.e. PRE-W-F1 — the comparable scope",
    }
    print("  TWO scopes are printed because W-F1 itself writes `bigXi`/`bigXiH` into the")
    print("  corpus.  The second is not a file exclusion — it re-reads every")
    print("  wave-modified file's HEAD bytes via `git show`, so it is the tree as it")
    print("  stood when the number of record was taken.  Files so reconstructed:")
    for rel in sorted(reconstructed) or ["    (none)"]:
        print(f"    - {rel}")
    print(f"    - {FORK_FILE}  (untracked at HEAD: counted as absent)")
    print()
    for b in ("all", "head"):
        ln, occ, fs = stats[b]
        print(f"  LINES {ln:>5} / OCCURRENCES {occ:>5}  across {len(fs):>2} files")
        print(f"        [{labels[b]}]")
    print(f"  expected (lines): {EXPECTED_BIGXI_LINES:>5}  across "
          f"{EXPECTED_BIGXI_FILES:>2} files   [08/15 pass, tree 8548842, pre-fork]")
    ln_b, _occ_b, fs_b = stats["head"]
    if (ln_b, len(fs_b)) != (EXPECTED_BIGXI_LINES, EXPECTED_BIGXI_FILES):
        drift.append(
            f"bigXi* at-HEAD lines/files: expected {EXPECTED_BIGXI_LINES}/"
            f"{EXPECTED_BIGXI_FILES}, measured {ln_b}/{len(fs_b)}")
    else:
        print(f"  -> the at-HEAD scope REPRODUCES the number of record "
              f"({EXPECTED_BIGXI_LINES} lines / {EXPECTED_BIGXI_FILES} files).")
    occ_tot = stats["all"][1]
    print()
    print("  ⚠ SUBSTRING HAZARD, for every future audit of this surface: `bigXi` is a")
    print("    PROPER PREFIX of `bigXiH`, `bigXi_bounded`, `bigXiArc`, `bigXiH_bounded`,")
    print("    …  so `grep -F \"bigXi\"` counts the fork's own names too.  Since W-F1 the")
    print("    two are no longer the same set.  Measured here:")
    bigxih_occ = sum(open(os.path.join(REPO, r), encoding="utf-8").read().count("bigXiH")
                     for r in files)
    print(f"      `bigXiH` occurrences salt-wide : {bigxih_occ}")
    print(f"      of the {occ_tot} `bigXi` hits, {bigxih_occ} are `bigXiH` prefixes.")
    print("    Any consumer of the 387 must say whether it means lines or occurrences,")
    print("    and whether it means pre- or post-fork.")
    print()
    print("  per-file `bigXi` occurrence counts:")
    for rel, c in sorted(per.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {c:>4}  {rel}")

    # ---- drift -------------------------------------------------------------
    head("DRIFT — reported, never reconciled")
    if not drift:
        print("  NONE.  Every expected number reproduces at its stated scope.")
    else:
        for d in drift:
            print(f"  * {d}")
        print()
        print("  Drift is reported, not fixed.  A number that moved is a fact about the")
        print("  tree, and the consumer of the number — not this script — decides what it")
        print("  means.")
    print()


if __name__ == "__main__":
    main()
    sys.exit(0)
