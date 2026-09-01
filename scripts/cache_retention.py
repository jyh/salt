#!/usr/bin/env python3
"""Actions-cache retention for this repo: KEEP THE NEWEST main SHA ONLY.

Council 2026-09-01, ruling 5: retention = keep newest main sha only.

═══ WHY A RETENTION RULE EXISTS AT ALL ═══════════════════════════════════════
One `main` commit costs ~4.3 GB of the repo's 10 GiB Actions-cache budget,
because TWO caches are written per sha on the default branch:

    lake-Linux-X64-<toolchain>-<manifest>-<sha>   ~3.38 GB   (lean-action, path .lake)
    salt-lake-<os>-<hashFiles>-<sha>              ~0.91 GB   (this workflow, path .lake/build)

Measured 2026-09-01 20:3xZ, immediately after PR #14 merged:

    4,297,544,513 B   refs/heads/main   a697b9c9   (both entries)
    4,298,195,513 B   refs/heads/main   15e27a4f   (both entries)
      913,379,667 B   refs/pull/12/merge           (written pre-#14)
    ─────────────
    9,509,119,693 B = 88.6% of the 10 GiB cap, with TWO main shas stored.

⇒ THE CAP HOLDS TWO MAIN SHAS AND NO MORE. Without a retention rule the third
merge evicts something, and GitHub chooses what — which on 2026-09-01 chose
main's own pair and produced the cold → 240-min overrun → CANCELLED → save
SKIPPED → cold fixed point that burned three runs and 720 billed minutes.
PR #14 stopped PRs from *writing* to the cap. It does not stop main's own
history from accumulating. That is this file.

═══ THE RULE, AND WHY IT IS SHAPED THIS WAY ══════════════════════════════════
Keep every cache entry belonging to the NEWEST main sha; delete the rest of
main's. "Newest" is read from `createdAt`, NOT from the running job's own
`github.sha`, and that choice is deliberate:

  · Two main runs can finish out of order. Keying on the running job's sha lets
    a slower, OLDER run delete a NEWER run's freshly-saved entries. Keying on
    the store's own newest entry cannot: whoever saved last is what survives.
  · If this run's save FAILED, its sha is simply absent, and "newest" falls
    back to the newest sha that actually EXISTS. Deleting down to a sha that is
    not there is precisely how the fixed point above is re-entered, so the rule
    is written so that state cannot be expressed.

`--expect-sha` adds the complementary gate for the caller that knows its own
sha: if the named sha has no BUILD entry in the store, REFUSE and delete
nothing. That is the "my save did not land" signal, and it is the one moment
when a tidy-up is the worst possible act.

═══ WHAT THIS DELIBERATELY DOES NOT DO ═══════════════════════════════════════
· It does not touch any ref other than `--ref` (default `refs/heads/main`).
  The `refs/pull/*/merge` residue is a SEPARATE question with a separate cause
  (entries written before #14 landed); post-#14 no PR writes the cache, so that
  residue is a one-time cleanup and not a recurring pathology. Reported by
  `--report-other-refs`, never deleted here.
· It does not delete an entry it could not classify. A key with no trailing
  40-hex sha is reported and KEPT: an unrecognised key means the key format
  moved, and the safe response to "I no longer understand this store" is to
  stop, not to delete confidently.
  ⛔ AND ONE KEY FAMILY IN THIS REPO IS ALREADY IN THAT CLASS, NAMED HERE RATHER
    THAN LEFT FOR A READER TO DISCOVER: `seed_cache.yml` writes
    `salt-lake-<os>-<hashFiles>-seed-<run_id>` — a DECIMAL run id, not a sha. So
    a seed entry (~887 MB) is unclassified, is KEPT indefinitely by this rule,
    and is printed with a ⚠️ on every firing. That is the right default — the
    seed is the artifact that broke the 2026-09-01 deadlock, and deleting it
    automatically would re-arm the risk it was made to answer — but it is a
    DELIBERATE permanent occupant of ~8.7% of the cap, retired by a hand once
    main is reliably warm, not by this rule.
· It has no notion of "old". Age is not the criterion; membership in the newest
  sha's group is. An entry created a minute ago for a superseded sha is dead
  weight, and an entry created yesterday for the newest sha is the one thing
  standing between the next run and a 200-minute cold build.

Exit codes: 0 ok (plan printed, or applied)  ·  1 REFUSED by a safety gate
            2 usage/input error              ·  3 a delete call failed
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys

# A cache key ends with the 40-hex commit sha the entry was written for. Both
# key families in this repo do (`salt-lake-<os>-<hashFiles>-<sha>` and
# lean-action's `lake-Linux-X64-<toolchain>-<manifest>-<sha>`), which is what
# makes one classifier enough for both.
SHA_RE = re.compile(r"-([0-9a-f]{40})$")

# The BUILD cache — this workflow's own `.lake/build` entry, the one whose
# absence means a cold build. lean-action's entry is a bonus, not a floor:
# without it `lake exe cache get` refetches mathlib in ~4 minutes, whereas
# without ours the tree is rebuilt from source in ~200.
BUILD_KEY_PREFIX = "salt-lake-"


def classify(entries, ref):
    """Split raw `gh cache list` records into (on-ref classified, on-ref
    unclassified, other-ref). Pure, so the self-test drives it without a forge."""
    on_ref, unclassified, other = [], [], []
    for e in entries:
        if e.get("ref") != ref:
            other.append(e)
            continue
        m = SHA_RE.search(e.get("key", ""))
        if m:
            on_ref.append(dict(e, sha=m.group(1)))
        else:
            unclassified.append(e)
    return on_ref, unclassified, other


def plan(entries, ref, expect_sha=None, max_delete=20):
    """Return (keep, delete, newest_sha, refusal_or_None).

    `refusal` is a string when a safety gate fires; the caller must then delete
    NOTHING. Every gate below has a self-test arm that drives it red, because a
    gate never shown to fire is a comment."""
    on_ref, unclassified, other = classify(entries, ref)

    if not on_ref:
        # Distinct from "checked and already minimal": there was nothing to
        # check. The two must not print the same sentence — an absence-shaped
        # pass passes hardest when nothing ran (council law 8).
        return [], [], None, None

    newest = max(on_ref, key=lambda e: e["createdAt"])
    newest_sha = newest["sha"]
    keep = [e for e in on_ref if e["sha"] == newest_sha]
    delete = [e for e in on_ref if e["sha"] != newest_sha]

    # GATE 1 — never leave the ref with no BUILD entry. If the newest sha has
    # only lean-action's cache, deleting an older sha's build entry converts a
    # warm repo into a cold one, which is the exact failure this rule exists to
    # prevent. Keep everything and say why.
    if not any(e["key"].startswith(BUILD_KEY_PREFIX) for e in keep):
        return keep, [], newest_sha, (
            "newest sha %s has no %s* entry — deleting older shas would leave "
            "no build cache to restore" % (newest_sha[:8], BUILD_KEY_PREFIX)
        )

    # GATE 2 — the caller's own save must have landed. Absent means this run
    # saved nothing, and a tidy-up in that state re-enters the fixed point.
    if expect_sha is not None and not any(
        e["sha"] == expect_sha and e["key"].startswith(BUILD_KEY_PREFIX) for e in on_ref
    ):
        return keep, [], newest_sha, (
            "expected sha %s has no %s* entry on %s — this run's save did not "
            "land; refusing to delete anything" % (expect_sha[:8], BUILD_KEY_PREFIX, ref)
        )

    # GATE 3 — bound the blast radius. A store this rule has never seen (a key
    # format change, a ref reused by something else) should stop it, not be
    # cleaned up with confidence.
    if len(delete) > max_delete:
        return keep, [], newest_sha, (
            "delete set is %d entries, over --max-delete %d — refusing; "
            "inspect the store by hand" % (len(delete), max_delete)
        )

    return keep, delete, newest_sha, None


def gh_cache_list(repo, limit=100):
    out = subprocess.run(
        ["gh", "cache", "list", "-R", repo, "--limit", str(limit),
         "--json", "id,key,ref,sizeInBytes,createdAt"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        sys.stderr.write("cache_retention: gh cache list failed: %s\n" % out.stderr.strip())
        sys.exit(2)
    return json.loads(out.stdout or "[]")


def human(n):
    return "%s B (%.2f GB)" % (format(n, ","), n / 1e9)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default="jyh/salt")
    ap.add_argument("--ref", default="refs/heads/main")
    ap.add_argument("--expect-sha", default=None,
                    help="the calling run's sha; refuse if its build entry is absent")
    ap.add_argument("--max-delete", type=int, default=20)
    ap.add_argument("--from-file", default=None,
                    help="read `gh cache list --json` output from a file instead of calling gh")
    ap.add_argument("--apply", action="store_true",
                    help="actually delete; without it this is a dry run and deletes nothing")
    ap.add_argument("--report-other-refs", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.from_file:
        with open(args.from_file) as fh:
            entries = json.load(fh)
    else:
        entries = gh_cache_list(args.repo)

    keep, delete, newest_sha, refusal = plan(
        entries, args.ref, expect_sha=args.expect_sha, max_delete=args.max_delete
    )
    on_ref, unclassified, other = classify(entries, args.ref)

    print("cache_retention: repo=%s ref=%s entries_on_ref=%d" % (args.repo, args.ref, len(on_ref)))
    if unclassified:
        print("cache_retention: ⚠️ %d entry(s) on %s carry no trailing 40-hex sha — "
              "KEPT and not classified:" % (len(unclassified), args.ref))
        for e in unclassified:
            print("    keep(unclassified)  %s  %s" % (human(e["sizeInBytes"]), e["key"]))
    if args.report_other_refs and other:
        tot = sum(e["sizeInBytes"] for e in other)
        print("cache_retention: 📌 %d entry(s) on OTHER refs, %s — reported, NOT in scope:"
              % (len(other), human(tot)))
        for e in other:
            print("    other  %-22s %s  %s" % (e["ref"], human(e["sizeInBytes"]), e["key"]))

    if newest_sha is None:
        print("cache_retention: NOTHING TO CHECK — no classified entries on %s. "
              "(This is not 'already minimal'.)" % args.ref)
        return 0

    print("cache_retention: newest sha on %s = %s" % (args.ref, newest_sha))
    for e in keep:
        print("    KEEP    %s  %s" % (human(e["sizeInBytes"]), e["key"]))

    if refusal:
        sys.stderr.write("cache_retention: ⛔ REFUSED — %s\n" % refusal)
        sys.stderr.write("cache_retention: nothing was deleted.\n")
        return 1

    if not delete:
        print("cache_retention: ✅ already minimal — %d entry(s) kept, 0 to delete." % len(keep))
        return 0

    freed = sum(e["sizeInBytes"] for e in delete)
    for e in delete:
        print("    DELETE  %s  %s" % (human(e["sizeInBytes"]), e["key"]))
    print("cache_retention: %d entry(s) to delete, freeing %s"
          % (len(delete), human(freed)))

    if not args.apply:
        print("cache_retention: DRY RUN — nothing deleted. Pass --apply to act.")
        return 0

    rc = 0
    for e in delete:
        r = subprocess.run(["gh", "cache", "delete", str(e["id"]), "-R", args.repo],
                           capture_output=True, text=True)
        if r.returncode == 0:
            print("cache_retention: deleted id=%s" % e["id"])
        else:
            msg = (r.stderr or "").strip()
            sys.stderr.write("cache_retention: DELETE FAILED id=%s: %s\n" % (e["id"], msg))
            # ⛔ NAME THE LIKELIEST CAUSE RATHER THAN LEAVE A BARE 403 FOR A
            #   READER TO DECODE AT THE WRONG MOMENT. Measured 2026-09-01:
            #   `repos/jyh/salt/actions/permissions/workflow` reports
            #   `default_workflow_permissions: "read"`. A job-level
            #   `permissions:` block is meant to set this job's token
            #   regardless — but that is DOCUMENTED behaviour, not a
            #   measurement of this repo, and the two have already come apart
            #   here once today. So this branch states the hypothesis and where
            #   to check it; it does not assert it.
            if "403" in msg or "not accessible" in msg.lower():
                sys.stderr.write(
                    "cache_retention: ⇒ this reads like a TOKEN PERMISSION refusal, not a "
                    "missing cache. Check `gh api repos/<owner>/<repo>/actions/permissions/"
                    "workflow`; if `default_workflow_permissions` is \"read\" and this job's "
                    "`permissions: {actions: write}` did not override it, the retention job "
                    "cannot delete and the setting is the fix. NOTHING WAS DELETED.\n")
            rc = 3
    return rc


# ═══ SELF-TEST ════════════════════════════════════════════════════════════════
# ⛔ THE FIXTURES BELOW ARE CUT FROM THE REAL ARTIFACT, NOT INVENTED. Every key,
#   ref and size is a verbatim record from `gh cache list -R jyh/salt --json ...`
#   taken 2026-09-01 20:3xZ. A self-test over fixtures the author invented proves
#   internal consistency and never contact with the object — measured at this
#   seat the same day, when a three-cell detector went 3/3 GREEN against a log
#   format that does not exist.

REAL = [
    {"createdAt": "2026-09-01T20:32:03.433167Z", "id": 7218392585,
     "key": "lake-Linux-X64-754889babb91838e32edab1fc1197bb1f0fdfbaad18d5be7bb47b34f3158a6c2-0a66719698a20c4d4d3225082c60f71c2957d8f43281e7ce467f6d5c8968d654-a697b9c90b1d5b3d4cdb0b2cf48161cf03502154",
     "ref": "refs/heads/main", "sizeInBytes": 3383850038},
    {"createdAt": "2026-09-01T20:32:44.366669Z", "id": 7218414138,
     "key": "salt-lake-Linux-3a15ef9af7655c2915d2cf8ceac8b5ed79d97c73c0e88c8e77f3c9cf4da9b64a-a697b9c90b1d5b3d4cdb0b2cf48161cf03502154",
     "ref": "refs/heads/main", "sizeInBytes": 913694475},
    {"createdAt": "2026-09-01T19:07:15.730831Z", "id": 7215885599,
     "key": "lake-Linux-X64-754889babb91838e32edab1fc1197bb1f0fdfbaad18d5be7bb47b34f3158a6c2-0a66719698a20c4d4d3225082c60f71c2957d8f43281e7ce467f6d5c8968d654-15e27a4fe1abe586a826d484ed9e61e1ab3c8baa",
     "ref": "refs/heads/main", "sizeInBytes": 3384492860},
    {"createdAt": "2026-09-01T19:07:51.932888Z", "id": 7215907569,
     "key": "salt-lake-Linux-3a15ef9af7655c2915d2cf8ceac8b5ed79d97c73c0e88c8e77f3c9cf4da9b64a-15e27a4fe1abe586a826d484ed9e61e1ab3c8baa",
     "ref": "refs/heads/main", "sizeInBytes": 913702653},
    {"createdAt": "2026-09-01T20:03:29.436233Z", "id": 7217541071,
     "key": "salt-lake-Linux-3a15ef9af7655c2915d2cf8ceac8b5ed79d97c73c0e88c8e77f3c9cf4da9b64a-8f8f94f1c895ce51d8563bc3cee41e70750e0eda",
     "ref": "refs/pull/12/merge", "sizeInBytes": 913379667},
]

NEW = "a697b9c90b1d5b3d4cdb0b2cf48161cf03502154"
OLD = "15e27a4fe1abe586a826d484ed9e61e1ab3c8baa"
MAIN = "refs/heads/main"


def self_test():
    fails = []
    ran = []

    def check(name, cond, detail=""):
        ran.append(name)
        if cond:
            print("  ✅ %s" % name)
        else:
            print("  ⛔ %s  %s" % (name, detail))
            fails.append(name)

    print("cache_retention --self-test  (fixtures cut from the real store, 2026-09-01)")

    # 1 — the real store, as it stands: keep the newest sha's pair, delete the
    #     older sha's pair, and do not touch the PR ref.
    keep, delete, newest, refusal = plan(REAL, MAIN)
    check("real store: no refusal", refusal is None, str(refusal))
    check("real store: newest sha is the merge commit", newest == NEW, str(newest))
    check("real store: keeps 2", len(keep) == 2, str(len(keep)))
    check("real store: deletes 2", len(delete) == 2, str(len(delete)))
    check("real store: every delete is the older sha",
          all(e["sha"] == OLD for e in delete))
    check("real store: the PR ref is untouched",
          all(e["ref"] == MAIN for e in keep + delete))
    check("real store: frees 4,298,195,513 B",
          sum(e["sizeInBytes"] for e in delete) == 4298195513,
          str(sum(e["sizeInBytes"] for e in delete)))

    # 2 — CAN IT SAY "NOTHING TO DELETE"? A store already at one sha.
    one_sha = [e for e in REAL if e["ref"] == MAIN and NEW in e["key"]]
    keep, delete, newest, refusal = plan(one_sha, MAIN)
    check("already minimal: 0 deletes", delete == [] and refusal is None)
    check("already minimal: still keeps 2", len(keep) == 2)

    # 3 — GATE 1 drives RED: newest sha has lean-action's entry only.
    no_build = [e for e in REAL if e["ref"] == MAIN
                and not (NEW in e["key"] and e["key"].startswith(BUILD_KEY_PREFIX))]
    keep, delete, newest, refusal = plan(no_build, MAIN)
    check("gate 1 fires when the newest sha has no build entry",
          refusal is not None and "no salt-lake-* entry" in refusal, str(refusal))
    check("gate 1 deletes nothing", delete == [])

    # 4 — GATE 2 drives RED: --expect-sha names a sha whose save never landed.
    keep, delete, newest, refusal = plan(REAL, MAIN, expect_sha="0" * 40)
    check("gate 2 fires when the expected sha is absent",
          refusal is not None and "did not land" in refusal, str(refusal))
    check("gate 2 deletes nothing", delete == [])
    # ... and stays GREEN when the expected sha IS present, so it is not a gate
    #     that can only refuse.
    keep, delete, newest, refusal = plan(REAL, MAIN, expect_sha=NEW)
    check("gate 2 passes when the expected sha is present", refusal is None, str(refusal))
    check("gate 2 pass still deletes the older pair", len(delete) == 2)

    # 5 — GATE 3 drives RED.
    keep, delete, newest, refusal = plan(REAL, MAIN, max_delete=1)
    check("gate 3 fires on an over-large delete set",
          refusal is not None and "over --max-delete" in refusal, str(refusal))
    check("gate 3 deletes nothing", delete == [])

    # 6 — an unclassifiable key is KEPT, never deleted.
    odd = REAL + [{"createdAt": "2026-09-01T21:00:00Z", "id": 1, "ref": MAIN,
                   "key": "salt-lake-Linux-no-sha-here", "sizeInBytes": 1}]
    on_ref, unclassified, other = classify(odd, MAIN)
    check("unclassified key is not on the classified list", len(unclassified) == 1)
    keep, delete, newest, refusal = plan(odd, MAIN)
    check("unclassified key is never in the delete set",
          all("no-sha-here" not in e["key"] for e in delete))

    # 6b — THE REAL INSTANCE OF THAT CLASS, and it is not hypothetical: the seed
    #      workflow's key ends `-seed-<run_id>`, a DECIMAL id. Record verbatim
    #      from the store on 2026-09-01 (entry since evicted, which is exactly
    #      why it is pinned here rather than re-read).
    seeded = REAL + [{"createdAt": "2026-09-01T18:11:16.000000Z", "id": 7215637087,
                      "ref": MAIN, "sizeInBytes": 887132849,
                      "key": "salt-lake-Linux-3a15ef9af7655c2915d2cf8ceac8b5ed79d97c73c0e88c8e77f3c9cf4da9b64a-seed-33521573204"}]
    on_ref, unclassified, other = classify(seeded, MAIN)
    check("the seed workflow's key is unclassified (decimal run id, not a sha)",
          len(unclassified) == 1 and "seed-" in unclassified[0]["key"])
    keep, delete, newest, refusal = plan(seeded, MAIN)
    check("a seed entry is never deleted by this rule",
          all("-seed-" not in e["key"] for e in delete))
    check("a seed entry does not disturb the sha verdict",
          newest == NEW and len(delete) == 2, str(newest))

    # 7 — the empty store answers NOTHING TO CHECK, distinctly from "minimal".
    keep, delete, newest, refusal = plan([], MAIN)
    check("empty store yields newest=None (nothing to check)", newest is None)

    # 8 — the race the createdAt rule exists for: an OLDER sha saved LATER wins,
    #     because whoever saved last is what a subsequent run will restore.
    raced = [dict(e) for e in REAL if e["ref"] == MAIN]
    for e in raced:
        if OLD in e["key"]:
            e["createdAt"] = "2026-09-01T23:59:59.000000Z"
    keep, delete, newest, refusal = plan(raced, MAIN)
    check("race: the last-saved sha is the one kept", newest == OLD, str(newest))
    check("race: the other sha's pair is deleted",
          len(delete) == 2 and all(NEW in e["key"] for e in delete))

    # The count is DERIVED from the arms that actually ran, never typed: a typed
    # total stays green when an arm is deleted, which is the one edit a
    # regression is most likely to make.
    if fails:
        print("cache_retention --self-test: %d checks, %d FAILED: %s"
              % (len(ran), len(fails), ", ".join(fails)))
    else:
        print("cache_retention --self-test: ALL GREEN (%d checks)" % len(ran))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
