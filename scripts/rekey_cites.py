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
  PINNED     the citing file says its citations refer to an ARCHIVED snapshot (a published
             manuscript): its cites are correct against the archive, so never re-keyed; counted

--apply edits a citing file only where the same cite text is present at HEAD, in its base order;
a citing file whose cite occurrences differ between BASE and HEAD is REPORTED for that cite.
A file is PINNED when it is a DECLARED published manuscript (PUBLISHED), or when, whitespace
flattened, its own text (a .tex file) says `citations refer to the archived snapshot`, or it is a main.tex whose
sibling ERRATA.md says `kept as published` / `kept as submitted` (an UNDECLARED pin, printed so it is
added to the list). A diff that EDITS a pinned file is REFUSED, rc 3, before any census or --apply. Generated pages are skipped (their generators re-key them). Exit 0 when nothing is stale after the
run (no REPORTED, and no RE-KEYED left unapplied), 1 otherwise, 2 on a usage error, 3 refused.

RECORDS: --apply also re-hashes a prose record. A cite inside a sentence a non-author has read is part of that
sentence's hash (claim-sha12 in .prose-lean-reads), so a re-key alone turns the record STALE-CLAIM and the required
prose check red. After the rewrite, a record of an edited citing file whose sentence was a claim sentence of that file
BEFORE the rewrite and is not one after it is re-hashed iff the old sentence with exactly the applied re-keys
substituted (simultaneously, as in the file) IS a claim sentence of the rewritten file, read by check_prose_lean's own
splitter. Only claim-sha12 changes; id, declaration, readers and date stand, because the read sentence and the new one
differ only by the cite numbers this tool verified. Anything else is RECORD-STALE, printed and counted (rc 1). A
.prose-lean-baseline row hit by a re-key is printed as BASELINE-HIT and NOT rewritten: the ratchet refuses a re-hashed
baseline row, so it needs a record (read by hand).

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
# Published manuscripts: their file:line locators cite an archived snapshot, so they stay byte-identical
# and a correction goes to their ERRATA (the helm's scope of condition 5, 10-27). Declared here; the two
# word roads below (the file's own clause, a sibling ERRATA's) catch one that is not declared yet.
PUBLISHED = ("papers/witness/main.tex",    # Zenodo snapshot; "citations refer to the archived snapshot"
             "papers/flagship/main.tex")   # its ERRATA: "kept as submitted"
PIN_PHRASE = "citations refer to the archived snapshot"
ERRATA_PHRASES = ("kept as published", "kept as submitted")
TEXT = (".lean", ".md", ".tex", ".tsv", ".py", ".txt", ".yml")
LIMITS = ("LIMITS: .lean targets only; forms Leaf.lean:N and :N–M / :N-M; lists and prose line "
          "numbers are not read; a cite written fresh at HEAD is not checked; content equality is "
          "per line (a line whose meaning moved but whose text did not is not caught); a record is re-hashed only "
          "under --apply (a re-key made by hand, read DONE, leaves its records to the prose check).")


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


def flat(t):
    return " ".join((t or "").split())


def pin_road(root, rev, src, text, published):
    """Why a citing file is pinned at rev (None if it is not): declared, its own clause, or its ERRATA."""
    if src in published:
        return "declared"
    if src.endswith(".tex") and PIN_PHRASE in flat(text):   # a manuscript's clause, never code quoting it
        return "own clause"
    if src.rsplit("/", 1)[-1] == "main.tex":
        er = show(root, rev, (src.rsplit("/", 1)[0] + "/" if "/" in src else "") + "ERRATA.md")
        if any(ph in flat(er) for ph in ERRATA_PHRASES):
            return "ERRATA"
    return None


def refusals(root, base, head, published=PUBLISHED):
    """Pinned manuscripts the diff BASE..HEAD edits: a re-key must never touch one."""
    out = git(root, "diff", "--name-only", base, head).split()
    return sorted(f for f in out if f.endswith(TEXT)
                  and pin_road(root, base, f, show(root, base, f), published))


def census(root, base, head, published=PUBLISHED):
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
        road = pin_road(root, base, src, text, published)
        for f in edited + renamed:
            leaf = f.rsplit("/", 1)[-1]
            pat = r"(?<![A-Za-z0-9_./])((?:[A-Za-z0-9_.]+/)*)" + re.escape(leaf) + r":(\d+)(?:([–-])(\d+))?"
            for mt in re.finditer(pat, text):
                pre = mt.group(1)
                if pre and not f.endswith(pre + leaf):
                    continue
                if road:
                    cls["PINNED"] += 1
                    rows.append(dict(src=src, target=f, cite=mt.group(0), cls="PINNED", new=None, road=road))
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
                cls[c] += 1
                rows.append(dict(src=src, target=f, cite=mt.group(0), cls=c, new=rep))
    mark_done(root, base, head, rows, cls)
    return edited, rows, cls


def mark_done(root, base, head, rows, cls):
    """A citing file's re-keys are DONE when HEAD's counts of every cite they touch equal the counts
    the re-keys predict from BASE. Counted per file, so a CHAIN (one cite's new number is another's
    old) reads DONE: asking only "is the old cite gone?" misreads it, since the old text is present
    as the next link's new value."""
    by = {}
    for r in rows:
        if r["cls"] == "RE-KEYED":
            by.setdefault(r["src"], []).append(r)
    for src, rs in by.items():
        b, h = show(root, base, src), show(root, head, src)
        if b is None or h is None:
            continue
        keys = {r["cite"] for r in rs} | {r["new"] for r in rs}
        want = {k: len(occ_re(k).findall(b)) for k in keys}
        for r in rs:
            want[r["cite"]] -= 1
            want[r["new"]] += 1
        if all(len(occ_re(k).findall(h)) == want[k] for k in keys) and \
                any(want[r["cite"]] != len(occ_re(r["cite"]).findall(b)) for r in rs):
            for r in rs:
                r["cls"] = "DONE"
            cls["RE-KEYED"] -= len(rs)
            cls["DONE"] += len(rs)


def apply(root, base, head, rows, log=None):
    """Rewrite RE-KEYED cites in the working tree, matched by occurrence order per (src, cite), all at
    once per file, so a chain of re-keys never rewrites a cite twice."""
    by_src = {}
    for r in rows:
        if r["cls"] == "RE-KEYED":
            by_src.setdefault(r["src"], []).append(r)
    unapplied = 0
    for src, rs in by_src.items():
        p = os.path.join(root, src)
        cur = open(p, encoding="utf-8").read()
        btext = show(root, base, src)
        spans, applied_subs = [], {}
        for cite in sorted({r["cite"] for r in rs}):
            want = [r for r in rs if r["cite"] == cite]
            occ = occ_re(cite)
            hits = list(occ.finditer(cur))
            nb, nh = len(occ.findall(btext)), len(hits)
            if nb != nh or len(want) != nb or len({r["new"] for r in want}) != 1:
                for r in want:
                    r["cls"] = "REPORTED"
                    r["why"] = f"occurrences base {nb} / head {nh} differ"
                unapplied += len(want)
                continue
            spans += [(m.start(), m.end(), want[0]["new"]) for m in hits]
            applied_subs[cite] = want[0]["new"]
        spans.sort()
        if log is not None and spans:
            log[src] = (cur, applied_subs)
        out, at = [], 0
        for st, en, new in spans:
            assert st >= at, "overlapping cites"
            out += [cur[at:st], new]; at = en
        open(p, "w", encoding="utf-8").write("".join(out) + cur[at:])
    return unapplied


def _cpl():
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import check_prose_lean
    return check_prose_lean


def claim_shas(cpl, rel, text):
    """{claim-sha12: sentence} for one file, read exactly as check_prose_lean.scan reads it."""
    if rel.endswith(".lean"):
        items, kw = [ds for ds, _ in cpl.docstring_items(text)], dict(headline=True, docstring=True)
    elif rel.endswith((".md", ".tex")):
        items, kw = cpl.prose_of(rel, text), dict(headline=cpl.is_headline(rel))
    else:
        return {}
    return {cpl.sha12(sn): sn for p in items for sn, _, _ in cpl.claim_sentences(p, **kw)}


def substitute(text, subs):
    """Every cite in subs replaced by its new value in ONE pass (a chain is never rewritten twice)."""
    if not subs:
        return text
    alt = "|".join(re.escape(c) for c in sorted(subs, key=len, reverse=True))
    rx = re.compile(r"(?<![A-Za-z0-9_./])(?:" + alt + r")(?![0-9]|[–-][0-9])")
    return rx.sub(lambda m: subs[m.group(0)], text)


def rehash_records(root, log):
    """Re-hash the .prose-lean-reads records whose sentences only the applied re-keys changed (see RECORDS).
    -> (rehashed, stale, baseline_hits): lists of (id-or-sha, path, detail)."""
    rehashed, stale, bhits = [], [], []
    if not log:
        return rehashed, stale, bhits
    cpl = _cpl()
    moved = {}                                   # path -> {old sha: (old sentence, sentence with the re-keys)}
    after = {}
    for src, (before, subs) in log.items():
        b = claim_shas(cpl, src, before)
        a = claim_shas(cpl, src, open(os.path.join(root, src), encoding="utf-8").read())
        after[src] = a
        moved[src] = {sh: (sn, substitute(sn, subs)) for sh, sn in b.items() if sh not in a}
    rp = os.path.join(root, cpl.READS_FILE)
    if os.path.exists(rp):
        lines = open(rp, encoding="utf-8").read().split("\n")
        for i, line in enumerate(lines):
            c = line.split("\t")
            if len(c) != 8 or c[1] not in moved or c[2] not in moved[c[1]]:
                continue
            old, new = moved[c[1]][c[2]]
            nsh = cpl.sha12(new)
            if new != old and after[c[1]].get(nsh) == new:
                rehashed.append((c[0], c[1], f"{c[2]} -> {nsh}"))
                c[2] = nsh
                lines[i] = "\t".join(c)
            else:
                stale.append((c[0], c[1], f"{c[2]}: the sentence changed beyond the re-keys, or the splitter cut it "
                              "differently: re-hash by hand after a read"))
        if rehashed:
            open(rp, "w", encoding="utf-8").write("\n".join(lines))
    bp = os.path.join(root, cpl.BASELINE_FILE)
    if os.path.exists(bp):
        for line in open(bp, encoding="utf-8").read().split("\n"):
            c = line.split("\t")
            if len(c) >= 2 and c[1] in moved and c[0] in moved[c[1]]:
                bhits.append((c[0], c[1], "a baselined sentence moved by a re-key: the ratchet refuses a re-hashed "
                              "baseline row, so give it a record (read by hand)"))
    return rehashed, stale, bhits


def report(edited, rows, cls, applied):
    print(f"rekey_cites: edited {len(edited)} .lean file(s); cites KEPT {cls['KEPT']} · DONE at HEAD {cls['DONE']} · "
          f"RE-KEYED {cls['RE-KEYED']}{' (applied)' if applied else ''} · REPORTED {cls['REPORTED']} · "
          f"PRE-STALE (past the base file's end, not this edit's) {cls['PRE-STALE']} · "
          f"AMBIGUOUS (bare leaf, not read) {cls['AMBIGUOUS']} · "
          f"PINNED (an archived manuscript's, never re-keyed) {cls['PINNED']}")
    pins = sorted({(r["src"], r["road"]) for r in rows if r["cls"] == "PINNED"})
    if pins:
        print(f"  PINNED files ({len(pins)}): " + ", ".join(f"{s} [{w}]" for s, w in pins))
    for s, w in pins:
        if w != "declared":
            print(f"  UNDECLARED {s}: pinned by its {w}; add it to PUBLISHED")
    for r in rows:
        if r["cls"] in ("RE-KEYED", "REPORTED", "PRE-STALE"):
            print(f"  {r['cls']:9s} {r['src']}: {r['cite']} -> {r['new'] or '(no head line: read by hand)'}"
                  + (f"  [{r['why']}]" if r.get("why") else ""))
    print(LIMITS)


def main_rc(root, args, applied=False, published=PUBLISHED):
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    bad = refusals(root, base, head, published)
    if bad:
        print(f"rekey_cites: REFUSED: {base}..{head} edits {len(bad)} published manuscript(s), which stay "
              "byte-identical (their locators cite an archived snapshot; a correction goes to their ERRATA): "
              + ", ".join(bad))
        return 3
    edited, rows, cls = census(root, base, head, published)
    recs = None
    if applied:
        log = {}
        apply(root, base, head, rows, log)
        cls = Counter(r["cls"] for r in rows) + Counter({"AMBIGUOUS": cls["AMBIGUOUS"]})
        recs = rehash_records(root, log)
    report(edited, rows, cls, applied)
    if recs is not None:
        rh, st, bh = recs
        print(f"  records: RE-HASHED {len(rh)} (only the re-keys changed the read sentence) · RECORD-STALE {len(st)} · "
              f"BASELINE-HIT {len(bh)}")
        for tag, xs in (("RE-HASHED", rh), ("RECORD-STALE", st), ("BASELINE-HIT", bh)):
            for k, p, why in xs:
                print(f"  {tag:12s} {p}: {k} {why}")
    stale = cls["REPORTED"] + (0 if applied else cls["RE-KEYED"])   # PRE-STALE is printed, not counted
    if recs is not None:
        stale += len(recs[1]) + len(recs[2])
    return 1 if stale else 0


def main(argv):
    if "--self-test" in argv:
        return self_test()
    args = [a for a in argv if not a.startswith("--")]
    if not 1 <= len(args) <= 2:
        print(__doc__)
        return 2
    return main_rc(git(".", "rev-parse", "--show-toplevel").strip(), args, "--apply" in argv)


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
    with tempfile.TemporaryDirectory() as d:
        g = lambda *a: git(d, *a)
        g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
        os.makedirs(os.path.join(d, "Salt"))
        ten = "".join(f"line {i}\n" for i in range(1, 11))
        open(os.path.join(d, "Salt/P.lean"), "w").write(ten)
        body = "see P.lean:7.\n"
        open(os.path.join(d, "pinned.tex"), "w").write(body + "file:line citations refer to\nthe archived snapshot.\n")
        open(os.path.join(d, "live.tex"), "w").write(body)
        g("add", "-A"); g("commit", "-q", "-m", "base")
        t = ten.split("\n"); t = ["inserted"] + t
        open(os.path.join(d, "Salt/P.lean"), "w").write("\n".join(t))
        g("commit", "-q", "-am", "head")
        _, rows5, cls5 = census(d, "HEAD~1", "HEAD")
        k5 = {(r["src"], r["cite"]): r for r in rows5}
        check("a manuscript pinned to an archive (clause hard-wrapped) is PINNED, not re-keyed",
              k5.get(("pinned.tex", "P.lean:7"), {}).get("cls") == "PINNED" and cls5["PINNED"] == 1)
        check("... and its control, the same text without the clause, is RE-KEYED",
              k5.get(("live.tex", "P.lean:7"), {}).get("new") == "P.lean:8")
        apply(d, "HEAD~1", "HEAD", rows5)
        check("--apply leaves the pinned manuscript byte-identical",
              open(os.path.join(d, "pinned.tex")).read().startswith(body))
        # a DECLARED published manuscript is pinned whatever its words (the helm's scope of condition 5)
        open(os.path.join(d, "kept.tex"), "w").write(body)
        g("add", "-A"); g("commit", "-q", "-m", "kept")
        t = ["inserted again"] + open(os.path.join(d, "Salt/P.lean")).read().split("\n")
        open(os.path.join(d, "Salt/P.lean"), "w").write("\n".join(t))
        g("commit", "-q", "-am", "head3")
        _, rows6, _ = census(d, "HEAD~1", "HEAD", published=("kept.tex",))
        k6 = {(r["src"], r["cite"]): r for r in rows6}
        check("a DECLARED published manuscript is PINNED though it carries no clause",
              k6.get(("kept.tex", "P.lean:7"), {}).get("cls") == "PINNED")
        check("... and the same text undeclared is RE-KEYED (control)",
              k6.get(("live.tex", "P.lean:8"), {}).get("new") == "P.lean:9")
        check("a diff that does not touch a published manuscript is not refused",
              refusals(d, "HEAD~1", "HEAD", published=("kept.tex",)) == [])
        open(os.path.join(d, "kept.tex"), "w").write("see P.lean:9.\n")
        g("commit", "-q", "-am", "edits the manuscript")
        check("a diff that EDITS a published manuscript is REFUSED, naming it",
              refusals(d, "HEAD~2", "HEAD", published=("kept.tex",)) == ["kept.tex"])
        check("... and main() exits 3 on it",
              main_rc(d, ["HEAD~2", "HEAD"], published=("kept.tex",)) == 3)
        # paper's flagship-shaped fixture: an undeclared main.tex kept as submitted by its sibling ERRATA
        os.makedirs(os.path.join(d, "pap"))
        open(os.path.join(d, "pap/main.tex"), "w").write("see P.lean:9.\n")
        open(os.path.join(d, "pap/ERRATA.md"), "w").write("The manuscript itself is kept as\nsubmitted.\n")
        g("add", "-A"); g("commit", "-q", "-m", "flagship-shaped")
        t = ["inserted thrice"] + open(os.path.join(d, "Salt/P.lean")).read().split("\n")
        open(os.path.join(d, "Salt/P.lean"), "w").write("\n".join(t))
        g("commit", "-q", "-am", "head4")
        _, rows7, _ = census(d, "HEAD~1", "HEAD", published=())
        k7 = {(r["src"], r["cite"]): r for r in rows7}
        check("an undeclared main.tex whose ERRATA keeps it as submitted is PINNED by its ERRATA",
              k7.get(("pap/main.tex", "P.lean:9"), {}).get("road") == "ERRATA")
        check("a non-.tex file QUOTING the clause (this tool) is not pinned",
              pin_road(d, "HEAD", "tool.py", "x = 'citations refer to the archived snapshot'", ()) is None)
    # the live repo: every manuscript a word road pins is DECLARED (derived from the tree's bytes)
    here = git(os.path.dirname(os.path.abspath(__file__)), "rev-parse", "--show-toplevel").strip()
    roads = {f: pin_road(here, "HEAD", f, show(here, "HEAD", f), ())
             for f in git(here, "ls-tree", "-r", "--name-only", "HEAD").split() if f.endswith(TEXT)}
    word = sorted(f for f, w in roads.items() if w)
    check(f"in this repo, the {len(word)} manuscript(s) a word road pins are all DECLARED, and the list "
          "names no file the tree lacks", word and set(word) <= set(PUBLISHED) and set(PUBLISHED) <= set(roads))
    # CHAINS: one cite's new number is another's old one (paper-free find, 10-27, a 168-cite batch)
    for direction, edit in (("down", lambda t: t[1:]), ("up", lambda t: ["ins"] + t)):
        with tempfile.TemporaryDirectory() as d:
            g = lambda *a: git(d, *a)
            g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
            os.makedirs(os.path.join(d, "Salt"))
            ten = "".join(f"line {i}\n" for i in range(1, 11))
            open(os.path.join(d, "Salt/C.lean"), "w").write(ten)
            open(os.path.join(d, "c.md"), "w").write("C.lean:5 and C.lean:6 and C.lean:7\n")
            g("add", "-A"); g("commit", "-q", "-m", "base")
            open(os.path.join(d, "Salt/C.lean"), "w").write("\n".join(edit(ten.split("\n"))))
            g("commit", "-q", "-am", "head")
            _, rows8, _ = census(d, "HEAD~1", "HEAD")
            un = apply(d, "HEAD~1", "HEAD", rows8)
            want = ("C.lean:4 and C.lean:5 and C.lean:6\n" if direction == "down"
                    else "C.lean:6 and C.lean:7 and C.lean:8\n")
            check(f"a CHAIN of re-keys ({direction}) is applied whole, nothing unapplied",
                  un == 0 and open(os.path.join(d, "c.md")).read() == want)
            g("commit", "-q", "-am", "rekeyed")
            _, _, cls9 = census(d, "HEAD~2", "HEAD")
            check(f"... and after the commit every link of the chain ({direction}) reads DONE",
                  cls9["DONE"] == 3 and cls9["RE-KEYED"] == 0 and cls9["REPORTED"] == 0)
    # RECORDS: a re-key inside a read sentence re-hashes its record (paper's root, 10-27: three PRs went red on it)
    cpl = _cpl()
    with tempfile.TemporaryDirectory() as d:
        g = lambda *a: git(d, *a)
        g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
        os.makedirs(os.path.join(d, "Salt"))
        lean = "theorem foo : True := trivial\n" + "".join(f"-- line {i}\n" for i in range(2, 11))
        open(os.path.join(d, "Salt/A.lean"), "w").write(lean)
        readme = ("# T\n\nWe proved foo at Salt/A.lean:3 and Salt/A.lean:4.\n\n"
                  "We proved foo again, see Salt/A.lean:2.\n\nWe proved foo with no cite.\n")
        open(os.path.join(d, "README.md"), "w").write(readme)
        g("add", "-A"); g("commit", "-q", "-m", "pre")
        sent = claim_shas(cpl, "README.md", readme)
        by_text = {v: k for k, v in sent.items()}
        s1 = "We proved foo at Salt/A.lean:3 and Salt/A.lean:4."
        s2 = "We proved foo with no cite."
        _, stmt = cpl.decl_statement(cpl.aan.Repo(d), "Salt/A.lean::foo")
        ss = cpl.sha12(stmt)
        recs = [f"r1\tREADME.md\t{by_text[s1]}\tSalt/A.lean::foo\t{ss}\tmath\tpaper\t2026-10-27",
                f"r2\tREADME.md\t{by_text[s2]}\tSalt/A.lean::foo\t{ss}\tmath\tpaper\t2026-10-27",
                f"r3\tREADME.md\t000000000000\tSalt/A.lean::foo\t{ss}\tmath\tpaper\t2026-10-27"]
        reads0 = "\n".join(recs) + "\n"
        base0 = f"{by_text['We proved foo again, see Salt/A.lean:2.']}\tREADME.md\tclaim\n"
        open(os.path.join(d, ".prose-lean-reads"), "w").write(reads0)
        open(os.path.join(d, ".prose-lean-baseline"), "w").write(base0)
        g("add", "-A"); g("commit", "-q", "-m", "base")
        t = lean.split("\n"); t = t[:1] + ["-- inserted"] + t[1:]          # every line below 1 moves down one
        open(os.path.join(d, "Salt/A.lean"), "w").write("\n".join(t))
        g("commit", "-q", "-am", "head")
        rc = main_rc(d, ["HEAD~1", "HEAD"], applied=True, published=())
        reads1 = open(os.path.join(d, ".prose-lean-reads")).read().split("\n")
        new1 = "We proved foo at Salt/A.lean:4 and Salt/A.lean:5."
        check("--apply re-keys a CHAIN inside one read sentence (3->4, 4->5)",
              new1 in open(os.path.join(d, "README.md")).read())
        check("... and re-hashes its record to the rewritten sentence's hash",
              reads1[0].split("\t")[2] == cpl.sha12(new1) != by_text[s1])
        check("... changing only claim-sha12 (id, declaration, readers, date stand)",
              reads1[0].split("\t")[:2] + reads1[0].split("\t")[3:] == recs[0].split("\t")[:2] + recs[0].split("\t")[3:])
        check("a record whose sentence carries no moved cite is byte-unchanged", reads1[1] == recs[1])
        check("a record already stale BEFORE the apply is not rewritten (not this re-key's)", reads1[2] == recs[2])
        check("a BASELINE row hit by a re-key is left as written (the ratchet refuses a re-hash) ...",
              open(os.path.join(d, ".prose-lean-baseline")).read() == base0)
        check("... and counted, so the run exits 1", rc == 1)
        found = cpl.scan(d)[0]
        stale_ids = sorted(m.split(":")[0] for _, _, c, m in found if c == "STALE-CLAIM")
        check("end to end: check_prose_lean reads r1 green after the apply (only r3, stale before, is STALE-CLAIM)",
              stale_ids == ["r3"])
    print("rekey_cites self-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
