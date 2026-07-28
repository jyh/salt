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

- Status: **PASS**
- Final result: `Build completed successfully (9467 jobs).`
- Job count: **9467 / 9467**
- Errors: **0**
- Warnings: **257**, all pre-existing style-lint (none touched/fixed, per
  instructions). Breakdown of the top categories:
  - 180× line exceeds 100-character limit
  - 13× `push_neg` deprecated (prefer `push Not`)
  - 7× unscoped `maxHeartbeats` needs an explanatory comment
  - 6× unused variable name `hσhi` (plus a long tail of other single-use
    unused-variable warnings)
  - 4× "Unscoped option maxHeartbeats is not allowed"
  - a handful of `simp`/`simpa` style-flexibility lints
- Wall time: build spanned 2026-07-27T20:29:09Z through 2026-07-28T15:23Z
  real elapsed time; see Notes below — this is dominated by two container
  reclaim events, not by Lean compute time.
- Notes: the underlying container was reclaimed/restarted **twice** during
  this run (process table and free memory reset both times; disk and
  `.lake/build` oleans persisted across both). `lake build` was resumed in
  place each time via the same incremental invocation; already-built oleans
  were not recompiled, so no work was lost. Because of this, the wall-clock
  span above is not a meaningful measure of Lean build performance — treat
  it as elapsed real time only.

## Stage 3 — lean4checker replay

- Status: **NOT STARTED**

## Stage 4 — axiom audit

- Status: **PASS**
- Build-log confirmation: `#audit_axioms` (a build-failing in-repo command,
  `Salt/Tactic/AuditAxioms.lean`, whitelist
  `{propext, Classical.choice, Quot.sound}`) fired **3790** times across the
  16 track `All.lean` files during Stage 2
  (`BV BrunLower Chen Entropy ExpSum Fulcrum Goldbach HB HardyLittlewood MR
  Mertens SW TwinBar Vk Vmvt Weil`), including `Salt/MR/All.lean` and
  `Salt/Entropy/All.lean`. Every occurrence reported `✓ name [n axioms]`
  with `n ∈ {0,1,2,3}`; there were **zero** `#audit_axioms` errors in the
  build log (the command throws and fails the build on the first
  non-whitelisted axiom, so 0 errors + 9467/9467 success is itself a proof
  no offending axiom was found).
- Independent spot-check: rather than only trust the in-repo audit
  tactic, ran `#print axioms` directly (`lake env lean Scratch.lean`,
  scratch file not committed) against the 7 originally-specified target
  declarations. All 7 returned exactly `[propext, Classical.choice,
  Quot.sound]`:

  | Declaration | Axioms |
  |---|---|
  | `Salt.MR.seam_row_number` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.hUG34_unconditional` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.chi_floor_all_complete` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.budget_head_grade_closed` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.seam_row_calibratedK` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.bigXiArcTight_twelve` | `[propext, Classical.choice, Quot.sound]` |
  | `Salt.MR.L1_lower_odd` | `[propext, Classical.choice, Quot.sound]` |

## Verdict

Pending — Stage 3 (lean4checker) still to run. Stages 1, 2, 4: **PASS**.
