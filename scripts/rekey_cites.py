#!/usr/bin/env python3
"""Re-key hand-written `path/Leaf.lean:N` cites that an edit moves, verified by content.

  python3 scripts/rekey_cites.py BASE [HEAD]          census only (rc 1 if a cite is stale)
  python3 scripts/rekey_cites.py BASE [HEAD] --apply  rewrite the moved cites in the working tree
  python3 scripts/rekey_cites.py --self-test

BASE and HEAD are git revisions (HEAD defaults to `HEAD`). For every `.lean` file the diff
BASE..HEAD MODIFIES (not adds or deletes), the base and head texts are aligned with
`difflib.SequenceMatcher`. A base line inside an `equal` block maps to its head line, and its text
is the same by construction; a base line in a replaced or deleted block has NO head line.

A cite is read from each tracked text file AS IT IS AT BASE, in the forms `Leaf.lean:N`,
`Leaf.lean:N–M` and `Leaf.lean:N-M`, with or without a directory prefix. A prefix must match the
edited file's path; a bare leaf counts only when one tracked `.lean` file has that leaf name. Each
cite is classed:

  KEPT       its line(s) map to the same number
  RE-KEYED   its line(s) map to other numbers (rewritten with --apply)
  DONE       re-keyed already: at HEAD the citing file has the new cite and not the old
  REPORTED   a cited line has no head line (edited or deleted), a range lost its interior
             contiguity, or the target was RENAMED: NEVER rewritten, read by hand
  PRE-STALE  the cite was past the base file's end already: printed, not this edit's
  AMBIGUOUS  a bare leaf shared by several files: not read, counted

--apply edits a citing file only where the same cite text is present at HEAD, in its base order;
a citing file whose cite occurrences differ between BASE and HEAD is REPORTED for that cite.
Generated pages are skipped (their generators re-key them). Exit 0 when nothing is stale after the
run (no REPORTED, and no RE-KEYED left unapplied), 1 otherwise, 2 on a usage error.

LIMITS, printed with every verdict: only `.lean` targets; cites in other forms (`:N, M` lists,
"line N" prose) are not read; a cite written fresh at HEAD is not checked; content equality is per
line, so a cite of a line whose MEANING moved while its text stayed is KEPT or RE-KEYED as text.
"""
from __future__ import annotations

import difflib
import os
import re
import subprocess
import sys
from collections import Counter

GENERATED = {"docs/CATALOGUE.md", "docs/METHODS-CATALOGUE.md", "docs/methods-catalogue.tsv",
             "docs/FULCRUM-CENSUS.md", "docs/TACTICS-CATALOGUE.md"}
TEXT = (".lean", ".md", ".tex", ".tsv", ".py", ".txt", ".yml")
LIMITS = ("LIMITS: .lean targets only; forms Leaf.lean:N and :N–M / :N-M; lists and prose line "
          "numbers are not read; a cite written fresh at HEAD is not checked; content equality is "
          "per line (a line whose meaning moved but whose text did not is not caught).")


def git(root, *a):
    r = subprocess.run(["git", "-C", root, *a], capture_output=True, text=True, encoding="utf-8")
    if r.returncode:
        raise RuntimeError(f"git {' '.join(a)}: {r.stderr.strip()}")
    return r.stdout


def show(root, rev, path):
    r = subprocess.run(["git", "-C", root, "show", f"{rev}:{path}"], capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.stdout if r.returncode == 0 else None


def line_map(old: str, new: str) -> dict:
    a, b = old.split("\n"), new.split("\n")
    m = {}
    for tag, i1, i2, j1, _ in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal":
            for k in range(i2 - i1):
                m[i1 + k + 1] = j1 + k + 1
    return m


def occ_re(cite):
    # a bare cite must not match inside a longer path, a longer number, or the start of a range
    return re.compile(r"(?<![A-Za-z0-9_./])" + re.escape(cite) + r"(?![0-9]|[–-][0-9])")


def done_at_head(root, head, src, old, new):
    """The re-key is already in HEAD: the old cite is gone from the citing file and the new is present."""
    t = show(root, head, src)
    return t is not None and not occ_re(old).search(t) and bool(occ_re(new).search(t))


def census(root, base, head):
    out = git(root, "diff", "--name-status", "-M", base, head)   # -M: rename detection whatever the config
    edited = [ln.split("\t")[1] for ln in out.splitlines()
              if ln.startswith("M\t") and ln.endswith(".lean")]
    # a renamed .lean target: every cite of its OLD path is REPORTED (never skipped)
    renamed = [ln.split("\t")[1] for ln in out.splitlines()
               if ln[:1] in ("R", "D") and ln.split("\t")[1].endswith(".lean")]   # renamed or deleted
    files = git(root, "ls-tree", "-r", "--name-only", base).split()
    leaves = Counter(f.rsplit("/", 1)[-1] for f in files if f.endswith(".lean"))
    maps = {f: line_map(show(root, base, f), show(root, head, f)) for f in edited}
    nbase = {f: show(root, base, f).count("\n") + 1 for f in edited + renamed}
    for f in renamed:
        maps[f] = {}
    rows, cls = [], Counter()
    for src in files:
        if src in GENERATED or not src.endswith(TEXT):
            continue
        text = show(root, base, src)
        if text is None:
            continue
        for f in edited + renamed:
            leaf = f.rsplit("/", 1)[-1]
            pat = r"(?<![A-Za-z0-9_./])((?:[A-Za-z0-9_.]+/)*)" + re.escape(leaf) + r":(\d+)(?:([–-])(\d+))?"
            for mt in re.finditer(pat, text):
                pre = mt.group(1)
                if pre and not f.endswith(pre + leaf):
                    continue
                if not pre and leaves[leaf] > 1:
                    cls["AMBIGUOUS"] += 1
                    continue
                lo = int(mt.group(2)); hi = int(mt.group(4)) if mt.group(4) else lo
                nums = [lo] + ([hi] if mt.group(4) else [])
                span = [maps[f].get(n) for n in range(lo, hi + 1)]
                new = [maps[f].get(n) for n in nums]
                if hi > nbase[f]:
                    c, rep = "PRE-STALE", None            # past the base file's end: not this edit's
                elif any(x is None for x in span) or (span and span[-1] - span[0] != hi - lo):
                    c = "REPORTED"                          # an edited, deleted or inserted line inside
                    rep = None
                elif new == nums:
                    c, rep = "KEPT", mt.group(0)
                else:
                    c = "RE-KEYED"
                    rep = f"{pre}{leaf}:{new[0]}" + (f"{mt.group(3)}{new[1]}" if mt.group(4) else "")
                if c == "RE-KEYED" and done_at_head(root, head, src, mt.group(0), rep):
                    c = "DONE"
                cls[c] += 1
                rows.append(dict(src=src, target=f, cite=mt.group(0), cls=c, new=rep))
    return edited, rows, cls


def apply(root, base, head, rows):
    """Rewrite RE-KEYED cites in the working tree, matched by occurrence order per (src, cite)."""
    by_src = {}
    for r in rows:
        if r["cls"] == "RE-KEYED":
            by_src.setdefault(r["src"], []).append(r)
    unapplied = 0
    for src, rs in by_src.items():
        p = os.path.join(root, src)
        cur = open(p, encoding="utf-8").read()
        btext = show(root, base, src)
        for cite in sorted({r["cite"] for r in rs}):
            want = [r for r in rs if r["cite"] == cite]
            occ = occ_re(cite)
            nb, nh = len(occ.findall(btext)), len(occ.findall(cur))
            if nb != nh or len(want) != nb or len({r["new"] for r in want}) != 1:
                for r in want:
                    r["cls"] = "REPORTED"
                    r["why"] = f"occurrences base {nb} / head {nh} differ"
                unapplied += len(want)
                continue
            cur = occ.sub(want[0]["new"], cur)
        open(p, "w", encoding="utf-8").write(cur)
    return unapplied


def report(edited, rows, cls, applied):
    print(f"rekey_cites: edited {len(edited)} .lean file(s); cites KEPT {cls['KEPT']} · DONE at HEAD {cls['DONE']} · "
          f"RE-KEYED {cls['RE-KEYED']}{' (applied)' if applied else ''} · REPORTED {cls['REPORTED']} · "
          f"PRE-STALE (past the base file's end, not this edit's) {cls['PRE-STALE']} · "
          f"AMBIGUOUS (bare leaf, not read) {cls['AMBIGUOUS']}")
    for r in rows:
        if r["cls"] in ("RE-KEYED", "REPORTED", "PRE-STALE"):
            print(f"  {r['cls']:9s} {r['src']}: {r['cite']} -> {r['new'] or '(no head line: read by hand)'}"
                  + (f"  [{r['why']}]" if r.get("why") else ""))
    print(LIMITS)


def main(argv):
    if "--self-test" in argv:
        return self_test()
    args = [a for a in argv if not a.startswith("--")]
    if not 1 <= len(args) <= 2:
        print(__doc__)
        return 2
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    root = git(".", "rev-parse", "--show-toplevel").strip()
    edited, rows, cls = census(root, base, head)
    applied = "--apply" in argv
    if applied:
        apply(root, base, head, rows)
        cls = Counter(r["cls"] for r in rows) + Counter({"AMBIGUOUS": cls["AMBIGUOUS"]})
    report(edited, rows, cls, applied)
    stale = cls["REPORTED"] + (0 if applied else cls["RE-KEYED"])   # PRE-STALE is printed, not counted
    return 1 if stale else 0


def self_test():
    import tempfile
    ok = True

    def check(what, cond):
        nonlocal ok
        print(f"  {'ok ' if cond else 'BAD'} {what}")
        ok = ok and cond

    with tempfile.TemporaryDirectory() as d:
        g = lambda *a: git(d, *a)
        g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
        os.makedirs(os.path.join(d, "Salt"))
        tgt = "".join(f"line {i}\n" for i in range(1, 11))
        open(os.path.join(d, "Salt/A.lean"), "w").write(tgt)
        open(os.path.join(d, "Salt/B.lean"), "w").write("see Salt/A.lean:3 and A.lean:8–9 and A.lean:5\n"
                                                         "both forms: A.lean:8 then A.lean:8–9\n")
        open(os.path.join(d, "note.md"), "w").write("A.lean:10 · Salt/A.lean:1 · BA.lean:3\n")
        open(os.path.join(d, "Salt/BA.lean"), "w").write("x\n")
        g("add", "-A"); g("commit", "-q", "-m", "base")
        # head: two lines inserted above line 3, line 5 edited
        lines = tgt.split("\n")
        lines = lines[:2] + ["new a", "new b"] + lines[2:]
        lines[6] = "line 5 CHANGED"
        open(os.path.join(d, "Salt/A.lean"), "w").write("\n".join(lines))
        g("commit", "-q", "-am", "head")
        e, rows, cls = census(d, "HEAD~1", "HEAD")
        by = {r["cite"]: r for r in rows}
        check("a shifted cite is RE-KEYED to its new line", by["Salt/A.lean:3"]["new"] == "Salt/A.lean:5")
        check("a shifted range is RE-KEYED end to end", by["A.lean:8–9"]["new"] == "A.lean:10–11")
        check("a cite of a CHANGED line is REPORTED, never rewritten", by["A.lean:5"]["cls"] == "REPORTED")
        check("a line above the edit is KEPT", by["Salt/A.lean:1"]["cls"] == "KEPT")
        check("a later line in a second file is RE-KEYED", by["A.lean:10"]["new"] == "A.lean:12")
        un = apply(d, "HEAD~1", "HEAD", rows)
        b = open(os.path.join(d, "Salt/B.lean")).read()
        check("--apply rewrites the moved cites", "Salt/A.lean:5 and A.lean:10–11" in b)
        check("--apply leaves the REPORTED cite as written", "and A.lean:5\n" in b)
        check("nothing unapplied", un == 0)
        check("a bare cite and a range starting at the same line are re-keyed apart",
              "both forms: A.lean:10 then A.lean:10–11" in b)
        check("a longer leaf sharing the suffix (BA.lean:3) is not read",
              not any(r["src"] == "note.md" and r["cite"].endswith("A.lean:3") for r in rows))
        check("... and not rewritten", "BA.lean:3\n" in open(os.path.join(d, "note.md")).read())
        new = open(os.path.join(d, "Salt/A.lean")).read().split("\n")
        check("the re-keyed line's text equals the base line's (content check)", new[4] == "line 3")
        g("commit", "-q", "-am", "rekeyed")
        _, rows3, cls3 = census(d, "HEAD~2", "HEAD")
        check("after the re-key is committed, the census reads it DONE, not RE-KEYED",
              cls3["RE-KEYED"] == 0 and cls3["DONE"] == cls["RE-KEYED"] and cls3["REPORTED"] == cls["REPORTED"])
        # an insertion directly after a cited line moves nothing at or above it
        g("checkout", "-q", "--", "."); g("reset", "-q", "--hard", "HEAD~2")
        t2 = tgt.split("\n"); t2 = t2[:3] + ["inserted after 3"] + t2[3:]
        open(os.path.join(d, "Salt/A.lean"), "w").write("\n".join(t2))
        g("commit", "-q", "-am", "head2")
        _, rows2, _ = census(d, "HEAD~1", "HEAD")
        by2 = {r["cite"]: r for r in rows2}
        check("an insertion AFTER a cited line keeps it (no off-by-one)", by2["Salt/A.lean:3"]["cls"] == "KEPT")
        check("... and moves the line below it", by2["A.lean:5"]["new"] == "A.lean:6")
    with tempfile.TemporaryDirectory() as d:
        g = lambda *a: git(d, *a)
        g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
        g("config", "diff.renames", "false")          # the census must not depend on this (paper LOW 3)
        os.makedirs(os.path.join(d, "Salt"))
        ten = "".join(f"line {i}\n" for i in range(1, 11))
        for n in ("C", "E", "R"):
            open(os.path.join(d, f"Salt/{n}.lean"), "w").write(ten)
        open(os.path.join(d, "cites.md"), "w").write(
            "C.lean:3–6 · E.lean:3–6 · R.lean:2 · C.lean:99\n")
        g("add", "-A"); g("commit", "-q", "-m", "base")
        c = ten.split("\n"); c[4] = "line 5 EDITED"                      # interior edit of 3–6
        open(os.path.join(d, "Salt/C.lean"), "w").write("\n".join(c))
        e = ten.split("\n"); e = e[:4] + ["inserted"] + e[4:]             # interior insertion in 3–6
        open(os.path.join(d, "Salt/E.lean"), "w").write("\n".join(e))
        g("mv", "Salt/R.lean", "Salt/R2.lean")                              # a renamed target
        g("commit", "-q", "-am", "head")
        _, rows4, cls4 = census(d, "HEAD~1", "HEAD")
        b4 = {r["cite"]: r for r in rows4}
        check("a range whose INTERIOR line was edited is REPORTED (paper LOW 1)",
              b4.get("C.lean:3–6", {}).get("cls") == "REPORTED")
        check("a range that gained an INTERIOR line is REPORTED (paper LOW 1)",
              b4.get("E.lean:3–6", {}).get("cls") == "REPORTED")
        check("a cite into a RENAMED target is REPORTED, never skipped (paper LOW 2)",
              b4.get("R.lean:2", {}).get("cls") == "REPORTED")
        check("a cite past the base file's end is PRE-STALE, not this edit's",
              b4.get("C.lean:99", {}).get("cls") == "PRE-STALE")
    print("rekey_cites self-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
