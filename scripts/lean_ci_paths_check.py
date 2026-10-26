#!/usr/bin/env python3
"""lean_ci_paths_check.py — would a pull request's changed paths start `.github/workflows/lean_action_ci.yml`
under its `on.pull_request.paths` filter?

GitHub's documented filter semantics, reproduced here: a pattern matches the WHOLE path; `*` matches any run
of characters except `/`; `**` matches any run including `/`, and a leading `**/` also matches zero
directories; `?` matches one character that is not `/`. The workflow runs iff at least one changed path
matches at least one pattern. The pattern list is READ FROM THE WORKFLOW FILE, never typed here.

  python3 scripts/lean_ci_paths_check.py --files docs/RESULTS.md papers/x.tex   -> SKIP  (rc 1)
  python3 scripts/lean_ci_paths_check.py --files Salt/Foo.lean docs/RESULTS.md  -> RUN   (rc 0)
  python3 scripts/lean_ci_paths_check.py --self-test                             -> rc 0 iff every arm holds

LIMITS, printed beside every verdict: this reproduces the documented semantics and does not call GitHub; a
workflow skipped by its filter reports NO check (so `build` must stay required nowhere — measured
2026-10-25 against the branch protection); the `push` trigger (main only) carries no filter and is not modelled.
"""
import argparse, re, sys
import yaml

WF = ".github/workflows/lean_action_ci.yml"

def load_patterns(path=WF):
    with open(path, encoding="utf-8") as f:
        wf = yaml.safe_load(f)
    on = wf.get("on", wf.get(True))          # PyYAML reads a bare `on:` key as boolean True
    pr = (on or {}).get("pull_request") or {}
    pats = pr.get("paths")
    if not pats:
        raise SystemExit(f"no on.pull_request.paths in {path}")
    return list(pats)

def to_regex(pat):
    out, i = "", 0
    while i < len(pat):
        if pat.startswith("**/", i): out += "(?:.*/)?"; i += 3; continue
        if pat.startswith("**", i):  out += ".*";       i += 2; continue
        c = pat[i]
        out += "[^/]*" if c == "*" else "[^/]" if c == "?" else re.escape(c)
        i += 1
    return re.compile("^" + out + "$")

def decide(files, pats):
    rx = [(p, to_regex(p)) for p in pats]
    hits = [(f, p) for f in files for p, r in rx if r.match(f)]
    return ("RUN" if hits else "SKIP"), hits

FIXTURES = [  # (files, expected)
    (["docs/RESULTS.md", "papers/flagship/main.tex", ".prose-lean-reads"], "SKIP"),
    (["docs/CATALOGUE.md", "docs/methods-catalogue.tsv", "scripts/results_catalogue.py"], "SKIP"),
    (["Salt/MaynardK/MvJGen.lean"], "RUN"),
    (["Salt.lean"], "RUN"),
    (["Salt/Fulcrum/All.lean", "docs/RESULTS.md"], "RUN"),
    (["lakefile.lean"], "RUN"), (["lakefile.toml"], "RUN"), (["lake-manifest.json"], "RUN"), (["lean-toolchain"], "RUN"),
    (["docs/blueprints/brun-guide.md"], "RUN"),
    (["scripts/blueprint_lint.py"], "RUN"),
    ([".github/workflows/lean_action_ci.yml"], "RUN"),
    ([".github/workflows/scrub.yml"], "SKIP"),
    (["README.md", "LICENSE"], "SKIP"),
]

def self_test(path=WF):
    pats = load_patterns(path); fails = 0
    for files, want in FIXTURES:
        got, hits = decide(files, pats)
        ok = got == want; fails += (not ok)
        print(f"{'PASS' if ok else 'FAIL'}  {want:4s} {files}" + (f"  via {hits[0][1]}" if hits else ""))
    # MUTANT (red backwards): the list without the Lean glob must stop seeing a Lean file.
    mut = [p for p in pats if p != "**/*.lean"]
    got, _ = decide(["Salt/MaynardK/MvJGen.lean"], mut)
    ok = got == "SKIP"; fails += (not ok)
    print(f"{'PASS' if ok else 'FAIL'}  MUTANT: without '**/*.lean' a Lean file reads {got} (must be SKIP, so the arm is load-bearing)")
    # the list itself must carry the four inputs the helm named
    for must in ("**/*.lean", "lakefile.*", "lake-manifest.json", "lean-toolchain"):
        ok = must in pats; fails += (not ok); print(f"{'PASS' if ok else 'FAIL'}  list carries {must!r}")
    print(f"LIMITS: documented semantics reproduced, GitHub not called; `build` must stay required nowhere; push trigger unmodelled")
    print(f"self-test: {fails} FAIL over {len(FIXTURES)+5} arms")
    return 1 if fails else 0

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--files", nargs="*", default=None)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--workflow", default=WF)
    a = ap.parse_args()
    if a.self_test: return self_test(a.workflow)
    if a.files is None: ap.error("give --files or --self-test")
    verdict, hits = decide(a.files, load_patterns(a.workflow))
    print(f"{verdict}  ({len(a.files)} changed path(s); {len(hits)} match(es)" + (f", first {hits[0][0]} via {hits[0][1]}" if hits else "") + ")")
    print("LIMITS: documented semantics reproduced, GitHub not called; `build` must stay required nowhere")
    return 0 if verdict == "RUN" else 1

if __name__ == "__main__":
    sys.exit(main())
