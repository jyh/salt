# Cloud Verify Report — day 1

## STARTED

- UTC start (this consolidated report): 2026-07-28T14:21:15Z
- HEAD commit under test: `486bd85` (branch `main`, `jyh/salt`)
- Toolchain: `leanprover/lean4:v4.32.0-rc1`
  - `lean --version`: Lean (version 4.32.0-rc1, x86_64-unknown-linux-gnu, commit b4812ae53eea93439ad5dce5a5c26591c31cb697, Release)
  - `lake --version`: Lake version 5.0.0-src+b4812ae (Lean version 4.32.0-rc1)
- Working clone: `/home/user/verify/salt-verify` (separate from the session's primary `/home/user/salt` checkout)

## Provenance note

This run began as a task specified under branch `cloud-trial-night-1` /
report `CLOUD-TRIAL-REPORT.md` (7 named-declaration axiom spot-checks, no
lean4checker stage). Partway through the `lake build` stage, a follow-up
instruction arrived in-session asking to retarget the deliverable to this
branch/report and to add a `lean4checker` replay stage plus an
`#audit_axioms`-build-log confirmation, while explicitly preserving the
in-progress build (not restarting it). That merge is honored here: the
original 7 axiom spot-checks are folded into this report's axiom-audit
section below, and `cloud-trial-night-1` / `CLOUD-TRIAL-REPORT.md` are
retired in favor of this branch/report.

## Stage 1 — toolchain + cache

- Status: **PASS**
- elan-installed toolchain matched `./lean-toolchain` (`v4.32.0-rc1`).
- `lake exe cache get`: attempted 8564 file(s) from the mathlib4 cache
  (`leanprover-community/mathlib4` @ `lakecache.blob.core.windows.net`);
  all 8564 decompressed successfully, no download errors observed in
  `cache_get.log`.

## Stage 2 — full kernel build (`lake build`)

- Status: **IN PROGRESS** (carried over, not restarted, across two
  container interruptions — see Notes)
- Progress at this checkpoint: **9072 / 9467** jobs built
- Errors so far: **0**
- Warnings so far: **173** (pre-existing style-lint warnings — long lines,
  unused variable names, deprecated `push_neg` — none touched/fixed, per
  instructions)
- Notes: the underlying container was reclaimed/restarted twice during this
  run (process table and free memory reset both times, disk and
  `.lake/build` oleans persisted). `lake build` was resumed in place each
  time; already-built oleans were not recompiled. Wall-clock timestamps in
  this report reflect real elapsed time including those gaps, not pure
  build compute time.

## Stage 3 — lean4checker replay

- Status: **NOT STARTED**

## Stage 4 — axiom audit

- Status: **NOT STARTED**
- Will confirm the `Salt/MR/All.lean` and `Salt/Entropy/All.lean`
  `#audit_axioms` build-log checkmarks (already visible streaming in the
  Stage 2 build log as `info: ... ✓ ... [3 axioms]` lines) plus explicit
  `#print axioms` spot-checks on:
  - `Salt.MR.seam_row_number`
  - `Salt.MR.hUG34_unconditional`
  - `Salt.MR.chi_floor_all_complete`
  - `Salt.MR.budget_head_grade_closed`
  - `Salt.MR.seam_row_calibratedK`
  - `Salt.MR.bigXiArcTight_twelve`
  - `Salt.MR.L1_lower_odd`

## Verdict

Pending — this section will be filled in once all stages complete.
