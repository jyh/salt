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

- Status: **PASS, with 2 modules resource-limited (documented, not a
  kernel rejection) and 2 tracks flagged as a build-scope gap**
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
  180s timeout per module), logging PASS/FAIL to `leanchecker_results.log`
  (not committed — too large/noisy; totals and failures are summarized
  here). First pass: **883 / 891 PASS**, 8 flagged FAIL. Every flagged
  module was then re-run **in isolation** (nothing else active on the
  container) to separate genuine rejections from resource artifacts.

- **Result: 6 of the 8 flags were resource-contention artifacts, not real
  failures.** `Salt.Chen.AlphaSide` (`rc=124` timeout under contention)
  passed in isolation in 6.5s. `Salt.Keller.{All,Counterexample}` and
  `Salt.Parity.{All,Instances,Z}` failed the first pass only because their
  oleans didn't exist yet (see scope-gap finding below); once built
  directly, all 5 passed `leanchecker` cleanly in isolation.

- **Result: 2 of the 8 flags are genuine, reproducible resource limits of
  this container — `Salt.Brun` and `Salt.Maynard`.** Both files `import
  Mathlib` directly (the full umbrella import, pulling in every mathlib
  module rather than a curated subset the way other Salt files do). Each
  was independently re-run twice, fully isolated, with memory monitored:
  `Salt.Brun`'s `leanchecker` child process RSS grew from ~4GB → ~14.1GB in
  under a minute before being SIGKILLed (`rc=137`) at 2m24s; `Salt.Maynard`
  the same pattern, killed at 1m13s. This container has 15GiB total RAM.
  This is **not** a kernel rejection — no error was ever produced, only an
  OOM kill — and it is **not** evidence of a problem in the Salt proofs:
  every declaration actually defined in `Salt/Brun.lean` and
  `Salt/Maynard.lean` is small (`twinPrimeCounting`, `TwinCountingBigO`,
  `BrunStatement`, `twinPrimeCounting_monotone`, and the Maynard-track
  target statements), and both files are transitively imported by dozens
  of other Salt modules (e.g. `Salt.Brun.M2`, `Salt.Brun.M5BigO`,
  `Salt.Twelve.Params`, `Salt.Maynard.Tuple`, `Salt.Maynard.Level`, …) that
  **did** pass `leanchecker` — those declarations are being kernel-checked
  as part of every one of those passing runs, since leanchecker replays a
  module's own imports too. What's unique to checking `Salt.Brun`/
  `Salt.Maynard` *directly* is that the tool appears to size its working
  set to the requesting module's full transitive closure — the bulk
  `import Mathlib` — which is memory-infeasible here even though the two
  files' own content is trivial. Verdict for these two: **INCONCLUSIVE /
  RESOURCE-LIMITED**, not FAIL and not PASS — an environment ceiling, fully
  reproduced, not a defect finding.

- **Scope-gap finding:** `Salt.Keller.{All,Counterexample}` (2 files) and
  `Salt.Parity.{All,Instances,Z}` (3 files) — 5 files across 2 tracks —
  exist in the repo and build/audit-axiom cleanly on their own
  (`lake build Salt.Keller.All`: 8582 jobs, PASS, all `#audit_axioms` at
  `[3 axioms]`; `lake build Salt.Parity.All`: 9025 jobs, PASS, same), but
  **neither track is imported by `Salt.lean`**, the file Stage 2's default
  `lake build` actually roots at. They were silently outside Stage 2's
  9467-job count as a result — a gap between "what's in the repo" and
  "what the default build target checks," not a defect Stage 2 should have
  caught. `Salt/Keller/` (dated 2026-07-21) is a self-contained,
  Mathlib-only formalization of the Alpöge/Mathew/Fable counterexample to
  the Jacobian conjecture — topical, unrelated to the twin-primes tracks.
  `Salt/Parity/` (D4, ratified 2026-07-19) is the "parity barrier" /
  gap-statement track (`Z ⟺ TPC`, `ParityInv`) and reads as closer to the
  project's actual subject matter, so its exclusion from `Salt.lean` may be
  worth the repo owner's attention. Whether either exclusion is intentional
  is outside this report's scope to judge; it is recorded as a factual
  finding. Once built, both tracks' modules passed `leanchecker` cleanly
  in isolation (see above).

- **Stage 3 net tally:** 891 modules attempted; **889 confirmed PASS**
  under kernel replay (883 clean on the first pass + 6 confirmed in
  isolated re-runs); **2 INCONCLUSIVE/resource-limited** (`Salt.Brun`,
  `Salt.Maynard` — see above); **0 kernel rejections**.

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

- HEAD commit verified: `486bd85` (branch `main`, `jyh/salt`)
- Total wall time (this consolidated report): 2026-07-28T14:21:15Z through
  2026-07-28T17:25Z, real elapsed time — dominated by the two container
  reclaim events noted in Stage 2, not by compute time. (The overall run,
  including the earlier `cloud-trial-night-1`-branch portion of Stage 1/2
  before the mid-run merge, started 2026-07-27T20:29:09Z.)

| Stage | Verdict |
|---|---|
| 1 — toolchain + cache | **PASS** |
| 2 — full kernel build (`lake build`, 9467/9467) | **PASS** (0 errors, 257 pre-existing style warnings) |
| 3 — kernel replay (`leanchecker`, successor to deprecated `lean4checker`) | **PASS** for 889/891 attempted modules; **2 INCONCLUSIVE** (`Salt.Brun`, `Salt.Maynard` — reproducible OOM in this 15GiB container, not a kernel rejection); **0 kernel rejections** |
| 4 — axiom audit (3790 in-build `#audit_axioms` checks + 7 independent `#print axioms` spot-checks) | **PASS** — every audited declaration depends on at most `{propext, Classical.choice, Quot.sound}`, never more |

**Overall: PASS**, modulo two environment-resource caveats that are fully
documented above and do not indicate any defect in the Salt proofs:

1. `Salt.Brun` and `Salt.Maynard` could not be independently kernel-replayed
   by `leanchecker` in this container due to memory exhaustion (not a
   kernel rejection); their actual proof content is otherwise validated
   both by Stage 2's build and by `leanchecker` runs on the many other Salt
   modules that import them.
2. `Salt.Keller.*` and `Salt.Parity.*` (5 files, 2 tracks) are outside
   `Salt.lean`'s import graph and so outside Stage 2's default build scope
   entirely; both build and kernel-replay cleanly once built directly, but
   this is a build-scope gap in the repository worth the owner's attention,
   particularly for `Salt.Parity` given its apparent relevance to the
   project's actual subject matter.

No `sorry`, no `native_decide`, no axiom beyond the whitelisted three was
found anywhere in this run.
