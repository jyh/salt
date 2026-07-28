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

- Status: **IN PROGRESS**
- Substitution note: `github.com/leanprover/lean4checker` is **deprecated**
  (its own README/HEAD commit says so). It was reintegrated into the Lean 4
  repo itself as `leanchecker`, shipped with every toolchain since v4.28.0
  (https://github.com/leanprover/lean4/pull/11887); no lean4checker tag
  exists for `v4.32.0-rc1` (the newest tag is `v4.29.0-rc8`, and master's
  own `lean-toolchain` still points at `v4.29.0-rc8`). Per the deprecation
  notice's own instructions, this replay uses the built-in `leanchecker`
  via `lake env leanchecker <module>` — the exact successor tool, at the
  exact pinned toolchain, so there is no version-mismatch risk this
  substitution would otherwise introduce.
- Method: enumerated all 891 `*.lean` files under `Salt/` and ran
  `lake env leanchecker Salt.<Module>` once per module (sequential,
  180s timeout per module), logging PASS/FAIL per module to
  `leanchecker_results.log` (not committed — too large/noisy; totals and
  any failures are summarized here).
- Checkpoint at this push: **450 / 891** modules checked, **0 confirmed
  kernel-rejection failures**. `Salt.Brun` and `Salt.Chen.AlphaSide` remain
  flagged from resource contention (see above); no new contention failures
  since.
- **Separate finding (not a checker failure):** `Salt.Keller.All` and
  `Salt.Keller.Counterexample` both failed with `Could not find any oleans
  for: ...` — i.e. leanchecker couldn't check them because Stage 2's `lake
  build` never produced oleans for them at all. Investigation: `Salt/Keller/`
  (2 files) holds a self-contained, dated (2026-07-21) kernel-checked
  verification of the Alpöge/Mathew/Fable counterexample to the Jacobian
  conjecture — topical, unrelated to the twin-primes tracks, and imports
  `Mathlib` directly (no other Salt dependency). It is **not imported by
  `Salt.lean`** (the file `lake build`'s default `Salt` target actually
  roots at), so it sits outside the built/kernel-checked library entirely —
  this is a scope gap in the project's own root import graph, not a defect
  Stage 2 should have caught (Stage 2's 9467/9467 was correctly scoped to
  what `Salt.lean` imports). Built directly to confirm it's valid content:
  `lake build Salt.Keller.All` succeeds standalone (8582 jobs, its own
  `#audit_axioms` block passes at `[3 axioms]` for all 8 listed
  declarations). Once the oleans exist, `leanchecker` will be run on both
  modules in isolation (deferred, same contention concern as `Salt.Brun`,
  since `Counterexample.lean` also does `import Mathlib` directly) and the
  result folded into the final verdict below.

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
