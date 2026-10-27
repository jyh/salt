#!/usr/bin/env python3
"""Decide whether a C1 certificates run should proceed, or skip as superseded.

usage: python3 scripts/c1/should_run.py EVENT RUN_SHA MAIN_HEAD    prints run=true|false (and why)
       python3 scripts/c1/should_run.py --self-test

A run triggered by a completed "Lean Action CI" run on main (`workflow_run`) restores that run's own
build cache by its exact key, and the Lean workflow's cache retention keeps the newest main sha only.
When the runner queue delays a Lean run's last job, its `workflow_run` can fire after main has moved
on and retention has pruned the key: the restore misses and the run goes red on a sha that main has
already superseded (2026-10-26, run 40432683016, key for 2aa057fb). Such a run SKIPS, named, because
the newer head's own run checks the certificate on main. Every other event runs: the nightly
schedule, a dispatch, a pull request, and a `workflow_run` whose sha is still main's head.

LIMITS: the head is read when this step runs; if main moves between this check and the restore, the
restore can still miss (a window of seconds, not hours). A skip rests on the newer head's own run: if
that head's Lean run is cancelled or red, no workflow_run C1 checks main until the nightly schedule,
which always runs. If the freshness job itself fails, the workflow runs the certificate anyway.
"""
import sys


def decide(event, run_sha, main_head):
    """(run, reason). Only a workflow_run on a sha that is no longer main's head skips."""
    if event != "workflow_run":
        return True, f"{event}: always runs"
    if not main_head:
        return True, "main's head could not be read: run, and let the exact restore decide"
    if run_sha == main_head:
        return True, f"{run_sha[:8]} is main's head"
    return False, (f"superseded: {run_sha[:8]} is not main's head ({main_head[:8]}); "
                   f"main's own C1 run checks the certificate there")


def self_test():
    head, old = "c91aac2b" + "0" * 32, "2aa057fb" + "0" * 32
    cases = [
        ("tonight's order: an older sha completes after main moved on", ("workflow_run", old, head), False),
        ("a workflow_run on main's head runs", ("workflow_run", head, head), True),
        ("the nightly schedule runs", ("schedule", old, head), True),
        ("a dispatch runs, even on an old sha", ("workflow_dispatch", old, head), True),
        ("a pull request runs", ("pull_request", old, head), True),
        ("an unreadable head runs", ("workflow_run", old, ""), True),
    ]
    ok = True
    for what, args, want in cases:
        got = decide(*args)[0]
        print(f"  {'ok ' if got == want else 'BAD'} {what}")
        ok = ok and got == want
    print("should_run self-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        sys.exit(self_test())
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    run, why = decide(*sys.argv[1:4])
    print(f"run={'true' if run else 'false'}")
    print(why, file=sys.stderr)
