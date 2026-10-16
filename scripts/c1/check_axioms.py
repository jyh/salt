#!/usr/bin/env python3
"""Fail on any axiom beyond propext, Classical.choice, Quot.sound in a build log's `#print axioms`.

usage: python3 scripts/c1/check_axioms.py BUILD_LOG AUDIT_LEAN
Every `#print axioms` line of AUDIT_LEAN must have produced a report in BUILD_LOG (a missing report
is a failure, never a pass), and every reported axiom must be one of the three.
"""
import re
import sys

OK = {"propext", "Classical.choice", "Quot.sound"}
log = open(sys.argv[1], encoding="utf-8", errors="replace").read()
want = re.findall(r"^#print axioms\s+(\S+)", open(sys.argv[2], encoding="utf-8").read(), re.M)
seen, bad = {}, []
for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    seen[name] = {a.strip() for a in axs.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    seen[name] = set()
for name, axs in seen.items():
    if axs - OK:
        bad.append("%s depends on %s" % (name, sorted(axs - OK)))
missing = [n for n in want if not any(s == n or s.endswith("." + n) for s in seen)]
for b in bad:
    print("AXIOM REFUSED:", b)
for m in missing:
    print("NO AXIOM REPORT for", m)
print("check_axioms: %d #print axioms in the audit file, %d reports in the log, %d refused, %d missing"
      % (len(want), len(seen), len(bad), len(missing)))
sys.exit(1 if bad or missing or not want else 0)
