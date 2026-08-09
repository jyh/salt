#!/usr/bin/env python3
"""track_scan.py — INPUT GATHERER for a per-track demand-side scan.  READ-ONLY.

⚠️ WHAT IT DOES NOT DO, STATED FIRST BECAUSE THE SCOPE IS THE POINT
It does **not** produce a candidate row.  A candidate row is
    demand-side next step · class · the gate it needs · READING/INFERENCE marks · massif check
and every one of those is a JUDGEMENT.  A script can gather the three INPUTS a human needs to
make them — the governing doc, that track's flags tail, and the last landing in its code — and
nothing further.  **Claiming more would be the night's own defect: an instrument whose output is
mistaken for a finding.**

WHY IT IS COMMITTED AT ALL (the rung-4 test, silicon's successor form)
"If I vanished and my successor read nothing of mine, would this still work?"  The GATHERING is
reusable at every scan and is pure drudgery — three lookups per track, easy to do inconsistently
by hand at 2am.  The JUDGEMENT is not mechanizable and stays with the reader.  So this lands as
an executable and the report carries the rows.

READ-ONLY GUARANTEE: opens files for reading and shells out to `git log`.  It writes nothing,
creates nothing, and materializes no card tables in protected docs (maestro's rider (a)).

Usage:   python3 scripts/track_scan.py            # every track
         python3 scripts/track_scan.py chen bv    # named tracks
         python3 scripts/track_scan.py --selftest # run the built-in controls
"""
import re
import subprocess
import sys
from pathlib import Path

BP = Path("docs/blueprints")
FLAGS = BP / "flags.md"

# doc-stem -> code subdirectories under Salt/ that the track lands in.
# Deliberately explicit: a guessed mapping is an inference, and inferences get marked.
TRACKS = {
    "brun": ["Brun", "BrunLower"], "brun-guide": ["Brun", "BrunLower"],
    "bv": ["BV"], "chen": ["Chen"], "maynard": ["Maynard"], "maynard-guide": ["Maynard"],
    "sw": ["SW"], "p0": ["Chen"], "largesieve": ["LS"], "twinbar": ["TwinBar"],
    "parity-frontier": ["Parity"], "explicit12-design": ["Twelve"],
    "s2-inner-design": ["Maynard"], "lod-interface-design": ["Maynard"],
    "endgame-design": [], "landscape": [], "next-rung-scoping": [], "tactics": ["Tactic"],
}


def git(*args):
    try:
        return subprocess.run(["git", *args], capture_output=True, text=True,
                              timeout=30).stdout.strip()
    except Exception:
        return ""


def flags_tail(stem, n=2):
    """The last n flags.md section headers mentioning this track's name."""
    if not FLAGS.exists():
        return ["(flags.md absent)"]
    key = stem.split("-")[0].lower()
    hits = [ln.strip() for ln in FLAGS.read_text(encoding="utf-8").splitlines()
            if ln.startswith("## ") and key in ln.lower()]
    return hits[-n:] if hits else []


def scan(stem):
    doc = BP / f"{stem}.md"
    row = {"track": stem}
    row["doc_last_commit"] = git("log", "-1", "--format=%ad %h %s", "--date=short",
                                 "--", str(doc)) or "(never committed)"
    dirs = TRACKS.get(stem, [])
    row["code_dirs"] = dirs
    if dirs:
        paths = [f"Salt/{d}" for d in dirs]
        row["last_landing"] = git("log", "-1", "--format=%ad %h %s", "--date=short",
                                  "--", *paths) or "(no landings)"
    else:
        row["last_landing"] = "(no code mapping — design doc only)"
    row["flags_tail"] = flags_tail(stem)
    return row


def emit(row):
    print(f"### {row['track']}")
    print(f"  governing doc last commit : {row['doc_last_commit'][:120]}")
    print(f"  code dirs                 : {', '.join(row['code_dirs']) or '(none)'}")
    print(f"  last landing              : {row['last_landing'][:120]}")
    if row["flags_tail"]:
        for h in row["flags_tail"]:
            print(f"  flags tail                : {h[:120]}")
    else:
        print("  flags tail                : (no flags.md section names this track)")
    print()


def selftest():
    """Controls: run-on-itself, break-it, and refuse-empty (silicon's three)."""
    ok = True
    # CONTROL 1 — run on a known track; every field must be populated.
    r = scan("chen")
    for f in ("doc_last_commit", "last_landing"):
        if not r[f]:
            print(f"⛔ selftest: field {f} empty on a known track"); ok = False
    # CONTROL 2 — BREAK IT: a track with no code mapping must SAY so, not fake a landing.
    r2 = scan("landscape")
    if "no code mapping" not in r2["last_landing"]:
        print("⛔ selftest: unmapped track did not declare itself unmapped"); ok = False
    # CONTROL 3 — REFUSE EMPTY: a nonexistent track must not silently look clean.
    r3 = scan("this-track-does-not-exist")
    if "never committed" not in r3["doc_last_commit"]:
        print("⛔ selftest: nonexistent track reported as if it had a doc"); ok = False
    n = 0 if ok else 1
    print("selftest: all 3 controls pass" if n == 0 else "selftest: FAILURES above")
    return n


def main(argv):
    if len(argv) > 1 and argv[1] == "--selftest":
        return selftest()
    stems = argv[1:] if len(argv) > 1 else sorted(TRACKS)
    if not stems:
        print("REFUSE: no tracks selected — an empty population is not a scan.")
        return 2
    print(f"# track_scan — INPUTS ONLY, {len(stems)} track(s). Judgement is the reader's.\n")
    for s in stems:
        emit(scan(s))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
