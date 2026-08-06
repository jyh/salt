# LEG 1 — THE EVIDENCE PACKAGE (mathematics)
### Harvested 2026-08-05, 21:30 PDT · TRIPLE-LEG1-HARVEST · Opus 5
### Every number below was MEASURED from the repo at harvest time.
### Nothing is quoted from memory or from another doc without saying so.

**Method rule for this file.** Each row carries the command or `file:line`
that produced it. Where a number could not be established, the row says
**UNVERIFIED** rather than carrying a plausible figure. Where a number is
softer than it looks, it is repeated in the *do-NOT-quote* list at the end.

Harvest state: branch `main`, HEAD `127de71`, working tree clean except
`claude.sh` (M) and two untracked exploration docs.

---

## 1. SCALE

| Quantity | Value | Command |
|---|---|---|
| Lean lines under `Salt/` | **652,312** | `find Salt -name '*.lean' \| xargs wc -l \| tail -1` |
| Same, tracked-only (cross-check) | **652,312** | `git ls-files -z 'Salt/**/*.lean' 'Salt/*.lean' \| xargs -0 cat \| wc -l` |
| `.lean` files under `Salt/` | **1,130** (all tracked; zero untracked) | `find Salt -name '*.lean' \| wc -l`; `git status --porcelain Salt/` empty |
| Declarations (line-initial `theorem`/`lemma`/`def`/`abbrev`/`instance`/`structure`/`inductive`) | **19,564** | `grep -rhoE '^ *(private \|protected \|noncomputable \|partial \|@\[[^]]*\] *)*(theorem\|lemma\|def\|abbrev\|instance\|structure\|inductive) ' --include='*.lean' Salt \| wc -l` |
| — of which `theorem` | 11,729 | same grep, per keyword |
| — of which `lemma` | 5,236 | same |
| — of which `def` | 2,133 | same |
| — `instance` / `structure` / `abbrev` / `inductive` | 99 / 115 / 15 / 2 | same |
| Commits on `main` | **1,940** | `git rev-list --count HEAD` |
| Commits across all refs | 1,952 | `git rev-list --all --count` |
| First commit | `ca6ae78`, **2026-07-06 23:17:39 -0700**, "Scaffold salt: Lean 4 + mathlib project targeting the Twin Prime Conjecture" | `git log --reverse --format='%H\|%ad\|%s' --date=iso \| head -1` |
| Elapsed | **30 days** (2026-07-06 → 2026-08-05) | arithmetic on the above |
| Toolchain | `leanprover/lean4:v4.32.0-rc1` | `cat lean-toolchain` |
| mathlib pin | `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` | `lake-manifest.json` |

**Rate, derived:** 652,312 ln / 30 days = **21,744 Lean lines per day**,
sustained, first commit to now.

### Breakdown by arc

`for d in Salt/*/; do find "$d" -name '*.lean' | wc -l; find "$d" -name '*.lean' -exec cat {} + | wc -l; done`

| Arc | Files | Lines | Share |
|---|---:|---:|---:|
| `Salt/MR/` (Matomäki–Radziwiłł / Chowla) | 360 | 306,790 | 47.0% |
| `Salt/Chen/` | 147 | 99,711 | 15.3% |
| `Salt/Maynard/` | 102 | 45,618 | 7.0% |
| `Salt/SW/` (Siegel–Walfisz, zero theory) | 88 | 41,477 | 6.4% |
| `Salt/HB/` (Heath-Brown engine) | 47 | 29,030 | 4.5% |
| `Salt/Entropy/` | 86 | 27,291 | 4.2% |
| `Salt/Goldbach/` | 64 | 22,030 | 3.4% |
| `Salt/Twelve/` (explicit gaps ≤ 12) | 35 | 19,645 | 3.0% |
| `Salt/TwinBar/` | 28 | 9,088 | 1.4% |
| `Salt/Vk/` (Vinogradov–Korobov) | 24 | 7,671 | 1.2% |
| `Salt/BV/` (Bombieri–Vinogradov) | 20 | 7,071 | 1.1% |
| `Salt/ExpSum/` | 13 | 6,488 | 1.0% |
| `Salt/Vmvt/` | 18 | 5,722 | 0.9% |
| `Salt/Weil/` | 23 | 5,687 | 0.9% |
| `Salt/BrunLower/` | 13 | 5,356 | 0.8% |
| `Salt/LS/` (large sieve) | 20 | 4,089 | 0.6% |
| `Salt/Brun/` | 13 | 2,856 | 0.4% |
| `Salt/Mertens/` | 7 | 2,439 | 0.4% |
| `Salt/Fulcrum/` | 6 | 1,064 | 0.2% |
| `Salt/Tactic/` | 5 | 961 | 0.1% |
| `Salt/HardyLittlewood/` | 3 | 949 | 0.1% |
| `Salt/Parity/` | 3 | 854 | 0.1% |
| `Salt/Keller/` (Jacobian counterexample) | 2 | 224 | <0.1% |
| top-level (`Basic`, `Brun`, `Maynard`) | 3 | — | — |

### Growth since the last recorded snapshot

`docs/exploration/pi-prep-0731.md:605-608` (prepared 2026-07-31) records
537,908 ln / 1,049 files / 1,735 commits / 16,542 declarations. Measured
today against that:

| | 7/31 (doc) | 8/05 (measured) | Δ (5 days) |
|---|---:|---:|---:|
| lines | 537,908 | 652,312 | **+114,404 (+21.3%)** |
| files | 1,049 | 1,130 | +81 |
| declarations | 16,542 | 19,564 | +3,022 |
| commits | 1,735 | 1,940 | +205 |

---

## 2. THE REGISTRY — `docs/RESULTS.md`

**Lint verdict, verbatim** (`python3 scripts/results_lint.py`, exit 0):

```
results_lint: OK — 73 rows, all verified (file exists, declaration exists, date + commit well-formed)
```

Independent re-count of the table by parsing `docs/RESULTS.md` for rows
beginning `` | ` `` gives **73**, agreeing with the lint.

| § in `RESULTS.md` | rows |
|---|---:|
| 1. Sieve / Brun | 5 |
| 2. Chen / Goldbach | 3 |
| 3. SW / BV / bounded gaps | 5 |
| 4. Zero theory (ZFR / Littlewood / zero-count) | 7 |
| 5. VMVT / VK | 1 |
| 6. Heath-Brown / Fulcrum / T-BAL | 5 |
| 7. TwinBar / Parity | 13 |
| 8. The MR / Chowla campaign | 21 |
| 9. Infrastructure firsts | 13 |
| **total** | **73** |

### The headline theorems, by the file's own grouping

Names, plain statements and `file:line` are as `docs/RESULTS.md` carries
them (lint has verified that each file exists and declares that name).

**§1 Sieve / Brun**
- `Salt.N6.N6_2` — Brun's theorem: the sum of reciprocals of the twin primes converges. `Salt/Brun/N6.lean:231`
- `Salt.M5BigO.N5_3` — `twinPrimeCounting N` is `O(N/(log N)²)`, explicit constant 25700. `Salt/Brun/M5BigO.lean:295`
- `Salt.BrunLower.twin_almost_prime` — infinitely many `n` with `Ω(n(n+2)) ≤ 20`. `Salt/BrunLower/TwinInstance.lean:771`
- `Salt.HardyLittlewood.twinCounting_upper_order` [tier-2] — `∃ C > 0`, `π₂(N) ≤ C·N/(log N)²`. `Salt/HardyLittlewood/Frame.lean:117`
- `Salt.HardyLittlewood.twinCounting_upper_sharp` — the same with `C ≤ 100` (here 90). `Salt/HardyLittlewood/Sharp.lean:786`

**§2 Chen / Goldbach**
- `Salt.Chen.chen_headline` — Chen's theorem, unconditional. `Salt/Chen/ChenTheorem.lean:32`
- `Salt.Goldbach.chen_goldbach` — Chen's second theorem, unconditional. `Salt/Goldbach/ChenGoldbach.lean:41`
- `Salt.Chen.no_readable_certificate` — the four-carrier-row no-go. `Salt/Chen/WeightNoGo.lean:82`

**§3 SW / BV / bounded gaps**
- `Salt.Maynard.bounded_gaps_from_eh_complete` — the Maynard capstone, no residual hypotheses. `Salt/Maynard/Complete.lean:1472`
- `Salt.Twelve.gaps_le_twelve` — explicit bounded gaps ≤ 12 (standing analytic inputs). `Salt/Twelve/GapsUncond.lean:1061`
- `Salt.BV.bounded_gaps_of_siegelWalfisz` — bounded gaps from Siegel–Walfisz. `Salt/BV/AbelCore.lean:757`
- `Salt.SW.siegelWalfisz_holds` — Siegel–Walfisz, unconditional. `Salt/SW/Gate.lean:150`
- `Salt.SW.bounded_gaps_unconditional` — bounded prime gaps, unconditionally. `Salt/SW/Gate.lean:376`

**§4 Zero theory**
- `Salt.SW.zeta_zero_free_region` — de la Vallée Poussin for ζ. `Salt/SW/ZetaZeroFree.lean:235`
- `Salt.SW.zero_free_region_all` — combined region for primitive characters, `c₀ = 1/126848`. `Salt/SW/ZeroFreeReal.lean:605`
- `Salt.ExpSum.zeta_growth_strip` — `‖ζ(σ+it)‖ ≤ C·t^{1−σ}(1+log t)`. `Salt/ExpSum/ZetaApprox.lean:562`
- `Salt.SW.LFunction_zero_count_near_one` — radius-resolved Prachar count. `Salt/SW/ZeroCountNearOne.lean:98`
- `Salt.Vk.zeta_zero_free_region_littlewood` — Littlewood-strength region, `c = 1/88214`. `Salt/Vk/Littlewood.lean:409`
- `Salt.Vk.zeta_zero_free_region_pow` — the power region, θ = 3/4. `Salt/Vk/GrowthPow.lean:1044`
- `Salt.MR.zeta_lower_all_t` — the all-`t` uniform ζ lower bound. `Salt/MR/ZetaLowerAllT.lean:273`

**§5 VMVT / VK**
- `Salt.Vmvt.vmvt` — the Vinogradov Mean Value Theorem (Thm 24.5), exponent source-exact. `Salt/Vmvt/Summit2.lean:151`

**§6 Heath-Brown / Fulcrum / T-BAL**
- `Salt.SW.dh_repulsion_ordered` — Deuring–Heilbronn repulsion, explicit `(b,c,k)`. `Salt/SW/TBalR8.lean:1752`
- `Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros` — the unconditional half. `Salt/Fulcrum/Dichotomy.lean:82`
- `Salt.Fulcrum.fulcrum_dichotomy` — `TwinPrimeConjecture ∨ NoSiegelZeros` given the engine at threshold `C`. `Salt/Fulcrum/Dichotomy.lean:102`
- `Salt.HB.hb_l2c_master_unconditional` — the L2c master, fully unconditional. `Salt/HB/L2cMasterUncond.lean:85`
- `Salt.HB.neutrality_rate` — the exchange-rate wall. `Salt/HB/SignRate.lean:53`

**§7 TwinBar / Parity** (13 rows; the load-bearing ones)
- `Salt.TwinBar.twin_bar` — `J₁F + J₂F ≤ 2·log2·I₂F`, the Polymath8b `k=2` bound. `Salt/TwinBar/Impossibility.lean:173`
- `Salt.TwinBar.no_twin_weight` — the k=2 impossibility. `Salt/TwinBar/Impossibility.lean:276`
- `Salt.TwinBar.M₂_squeeze` — `1.383 ≤ M₂ ≤ 2·log 2 < 2`. `Salt/TwinBar/Witness.lean:253`
- `Salt.TwinBar.twinB_min_implies_twins` · `Salt.TwinBar.wall_or_door` — the door and the partition. `Salt/TwinBar/TwinDoor.lean:270`, `:288`
- `Salt.TwinBar.least_k_theorem` — least `k` with `M_k > 2` is 5. `Salt/TwinBar/LeastK.lean:127`
- `Salt.SW.mmuRate_holds` — the effective Möbius summatory rate. `Salt/SW/MobiusRateClose.lean:1059`
- `Salt.TwinBar.parity_wall_unconditional` · `…no_parity_beating_certificate_unconditional` — `Salt/TwinBar/WallUnconditional.lean:31`, `:44`
- `Salt.TwinBar.Sep.wall_of_indistinguishable` — `Salt/TwinBar/Separation.lean:67`
- `Salt.Parity.TPC_implies_Z` · `Salt.Parity.sufficient_true_not_parityInv` (THE GAP THEOREM) · `Salt.Parity.Z_implies_TPC` — `Salt/Parity/Z.lean:216`, `:670`, `:687`

**§8 MR / Chowla** (21 rows; 7 of them the superseded-in-place `v1…v6` lineage)
- `Salt.MR.mvHilbertUniform_holds` — Montgomery–Vaughan generalized Hilbert inequality. `Salt/MR/MVCore2.lean:575`
- `Salt.MR.lambda_nonpret` — λ-non-pretentiousness, unconditional. `Salt/MR/NonPretClose.lean:49`
- `Salt.Entropy.Chowla.log_chowla_two_budget_head` · `…_door_only` — `Salt/Entropy/Chowla/SpineFinal.lean:750`, `:981`
- `Salt.MR.halasz_ball_decay` — `Salt/MR/HalaszCore.lean:440`
- `Salt.MR.thm_a2'` — the S7/S8 summit, Theorem A2′. `Salt/MR/ThmA2Rows.lean:636`
- `Salt.MR.mmuChiRate_holds_gated` — the χ-twisted `t`-uniform Möbius rate. `Salt/MR/PortClose.lean:157`
- **THE TOLL** — `towerDropSumFlat_ge_log_ratio` `:419`, `…_le_log_ratio_mul` `:443`, `towerFlat_width_ge` `:585`, `towerFlat_width_le` `:625`, all `Salt/Entropy/Chowla/TowerFlat.lean`; `towerShape_width_ge` `Salt/Entropy/Chowla/TowerShape.lean:362`
- **THE PEARL** — `Salt.MR.logChowla2_witnessed_scale_flat_L_v2` `Salt/MR/S16FlatFinal.lean:136` (row carries its own 8/02 defect note)
- `Salt.MR.logChowla2_ineffective_v6` — the terminal, predicate-free, no outer hypotheses. `Salt/MR/RegisterCompose.lean:345`
- `Salt.MR.cofkR_cofactorSupply_L_gk` — the register, inhabited. `Salt/MR/RegisterRepair.lean:476`
- `Salt.MR.cofkL_bulk_false_at_socket` — the register refutation (the corpus refuting its own earlier row). `Salt/MR/RegisterInhabit.lean:260`

**§9 Infrastructure firsts**
- `Salt.LS.analytic_LS` `:58` · `arithmetic_LS` `:91` · `char_LS` `:277` · `bdh` `:360` · `vaughan` `:91` — `Salt/LS/*.lean`
- `Salt.Chen.linear_sieve_upper_chain` `:377` · `…lower_chain` `:389` — `Salt/Chen/LinearSieve.lean`
- `Salt.Mertens.mertens_second_sharp` — `Salt/Mertens/Second.lean:216`
- `Salt.Weil.norm_kloosterman_le_two_sqrt` — the Weil bound `‖S(a,b;p)‖ ≤ 2√p`. `Salt/Weil/Descent.lean:206`
- `Keller.keller_not_injective` [tier-2] · `Keller.jacobian_conjecture_counterexample` — `Salt/Keller/Counterexample.lean:142`, `:159`
- `Salt.HB.fl_dim4_lower` / `fl_dim4_upper` — the fundamental lemma at sieve dimension 4. `Salt/HB/RosserDim4FL.lean:364`
- `Salt.HB.hbSieve_fl_sandwich` — N5's exit, dim-4 Rosser service layer. `Salt/HB/RosserDim4Instance.lean:564`

---

## 3. THE AXIOM POSTURE

### The whitelist

`Salt/Tactic/AuditAxioms.lean:48` — `auditWhitelist : List Name :=
[propext, Classical.choice, Quot.sound]`. `#audit_axioms` runs
`Lean.collectAxioms` at elaboration and **fails `lake build`** if any
transitive dependency lies outside the list. It is a build-time
assertion, not an out-of-band report: `Salt/Tactic/AuditAxioms.lean:9-24`
states the same, and the file notes it is a pure metaprogram adding no
axioms of its own.

### Coverage, measured

| Quantity | Value | Command |
|---|---|---|
| `#audit_axioms` invocations across `Salt/` | **166** | `grep -rc '#audit_axioms' --include='*.lean' Salt \| awk -F: '{s+=$2} END{print s}'` |
| Files carrying at least one invocation | 24 | `grep -rl '#audit_axioms' --include='*.lean' Salt \| wc -l` |
| Track manifests (`Salt/*/All.lean`) | 23 | `ls Salt/*/All.lean \| wc -l` |
| — of which carry a roll call | 20 (Brun, LS, Twelve do not; they are covered by `blueprint_lint`) | `grep -rc '#audit_axioms' Salt/*/All.lean` |
| **Declaration name-slots inside roll calls** | **6,356** | parser over `Salt/*/All.lean`, validated against `Salt/Weil/All.lean` (parser 60, manual `sed \| tr \| grep -c '^Salt\.'` 60) |
| **Distinct names** | **6,302** | same parser |
| Share of the 19,564 declarations named in a roll call | **32.2%** | 6,302 / 19,564 |

Largest ledgers: `Salt/MR/All.lean` 3,948 slots (123 invocations),
`Salt/Chen/All.lean` 716, `Salt/SW/All.lean` 408, `Salt/HB/All.lean` 257,
`Salt/Goldbach/All.lean` 226, `Salt/Entropy/All.lean` 203.

**The honest reading of 32.2%:** a named declaration's audit *transitively*
covers everything it depends on, so the fraction of the corpus reachable
from an audited name is far above 32% — but that reachability was **not
measured** here (it needs a build). Quote 6,302 named declarations and
166 build-time assertions; do **not** quote a percentage of the corpus as
"audited".

### Registry-row coverage

Every one of the 73 `RESULTS.md` rows carries an audit citation; **zero
rows carry `⚠ unaudited`** (the two `grep` hits for that token are the
column legend at `docs/RESULTS.md:43` and the struck-through standing
chore at `:183`). Cross-checking each row's headline name against the
roll-call name set:

- **65 / 73** rows are named directly in an `#audit_axioms` roll call.
- **8 / 73** are not — and all eight are exactly the rows whose Axioms
  column says `blueprint_lint P1/P3` instead: `Salt.N6.N6_2`,
  `Salt.M5BigO.N5_3`, `Salt.Twelve.gaps_le_twelve`, and the five
  `Salt.LS.*`. `scripts/blueprint_lint.py:50-59` lists 9 `HEADLINERS`
  audited by a separate `lake env lean` pass. The registry's own
  bookkeeping is therefore internally consistent — the exception set is
  named, not hidden.

10 rows cite `3 axioms (audited)` with no `file:line`; all 10 are
nonetheless present in a roll call by the check above.

### The three negatives

Naive `grep` over `Salt/` returns 269 `sorry`, 196 `native_decide`, 2
`axiom` — **every one of them inside a doc comment or string**. A
comment-stripping scan (block comments, line comments and string
literals removed; script kept at the harvest scratchpad) over all 1,130
files returns:

| Pattern | Naive grep | Comment-stripped |
|---|---:|---:|
| `sorry` | 269 | **0** |
| `native_decide` | 196 | **0** |
| `admit` | — | **0** |
| line-initial `axiom <name>` | 2 | **0** |

Commands: `grep -rnwE 'sorry' --include='*.lean' Salt | wc -l` (269) and
the stripped scan (0). **This is why the claim must be stated as
"verified in tactic position, not by prose grep"** — the naive grep is
loud and entirely false-positive, because the corpus documents its own
discipline in its docstrings.

Independent kernel replay on record: `docs/reports/lean4checker-local-1.md:11`
— "**259 / 259** salt-authored content modules … 0 failures", 2026-07-21,
a fresh Lean kernel running independently of the elaborator, plus the
Keller manifest replayed in full `--fresh` mode. **Scope caveat carried
forward from `docs/exploration/pi-prep-0731.md:616-618`: do not quote this
as "every declaration" until a full-scope re-run exists.** The corpus has
grown 21% since that replay, so the 259/259 figure is also **stale** as a
coverage statement.

---

## 4. THE UNATTENDED LEDGER — the key artifact

### 4.0 What is and is not knowable

`git` alone cannot say whether a human was present. What it *can* say is
when work landed. To get the other half, this harvest parsed the salt
seat's own session transcripts
(`~/.claude/projects/-Users-jyh-projects-claude-salt/*.jsonl`, 5 files,
78,171 JSONL records) and extracted the timestamps of **messages JYH
actually typed**.

**A correction worth recording.** The first pass counted 3,186 "human"
messages. Sampling showed most were `<task-notification>` blocks —
agent-completion notices injected with `role: "user"`. After filtering
those (1,457 rejected) and slash-command echoes (214 rejected), the true
count is **1,714 typed messages, 2026-07-07 → 2026-08-05**. Every
engagement number below uses the filtered set. Had this not been caught,
the ledger would have shown 98.5% of commits landing within 30 min of a
"human message" — a wrong conclusion drawn from a real file.

**Caveat, stated once and carried:** this measures the *salt seat only*.
Silence in the salt transcript does not prove JYH was asleep — he may
have been engaged in another seat. Read every silence figure as "no human
direction reached the salt seat", which is the right measure for leg 1.

### 4.1 The 14-day table (2026-07-23 → 2026-08-05, America/Los_Angeles)

Commands:
```sh
TZ=America/Los_Angeles git log --since='2026-07-23 00:00' \
  --date=format-local:'%Y-%m-%d %H:%M:%S' --format='%ad|%h|%s'
```
(Note: `--since='2026-07-23'` without a time is parsed as UTC and drops 58
commits — use the explicit time. Two commits in the window carry `+0000`
offsets from cloud runs, which is why `format-local` is required.)

| Date | Dow | Commits | In 21:00–05:00 | Typed JYH msgs (salt seat) | First msg | Last msg |
|---|---|---:|---:|---:|---|---|
| 2026-07-23 | Thu | 58 | 4 | 46 | 07:22 | 19:14 |
| 2026-07-24 | Fri | 36 | 0 | 46 | 07:15 | 17:45 |
| 2026-07-25 | Sat | 81 | 11 | 70 | 08:11 | 21:12 |
| 2026-07-26 | Sun | 67 | 4 | 60 | 08:28 | 20:35 |
| 2026-07-27 | Mon | 55 | 0 | 64 | 07:09 | 19:37 |
| 2026-07-28 | Tue | 58 | 9 | 42 | 06:13 | 21:09 |
| 2026-07-29 | Wed | 64 | 23 | 47 | 00:05 | 20:36 |
| 2026-07-30 | Thu | 82 | 23 | 44 | 00:46 | 20:45 |
| 2026-07-31 | Fri | 40 | 0 | 77 | 07:04 | 19:17 |
| 2026-08-01 | Sat | 23 | 2 | 15 | 08:39 | 20:50 |
| 2026-08-02 | Sun | 46 | 0 | 29 | 09:12 | 12:13 |
| 2026-08-03 | Mon | 42 | 0 | 19 | 09:09 | 18:31 |
| 2026-08-04 | Tue | 15 | 0 | 89 | 07:47 | 19:59 |
| 2026-08-05 | Wed | 45 | 0 | 39 | 07:06 | 21:26 |
| **TOTAL** | | **712** | **76 (10.7%)** | **687** | | |

Hour-of-day distribution of the 712 commits:

| Window | Commits | Share |
|---|---:|---:|
| 21:00–04:59 (sleep) | 76 | 10.7% |
| 19:00–20:59 (family) | 72 | 10.1% |
| 05:00–06:59 | 14 | 2.0% |
| 07:00–18:59 (planning) | 550 | 77.2% |

Peak hour is 10:00 (71 commits). **The sleep-window share is 10.7%, and
the last five days carry two night commits between them.** Anyone reading
the ledger for "the machine works while he sleeps" will not find it in the
21:00–05:00 column, and the column should not be offered as the proof.

### 4.2 The measure that does carry the claim — human-silence windows

For each commit, the elapsed time since JYH last typed into the salt seat:

| Gap since last typed message | Commits | Share |
|---|---:|---:|
| < 30 min | 462 | 64.9% |
| 30–60 min | 97 | 13.6% |
| 1–2 h | 98 | 13.8% |
| 2–4 h | 49 | 6.9% |
| 4–8 h | 6 | 0.8% |
| > 8 h | 0 | 0.0% |

That table is the *per-commit* view and it understates the case, because a
commit landing at hour 19 of a silence has the same "gap" bucket as one
landing at hour 1. The *window* view is the right one: how much landed
inside a stretch during which the seat heard nothing.

| Silence containing the landing | Commits | Share of 712 | Lean lines inserted |
|---|---:|---:|---:|
| ≥ 1 h | 334 | 46.9% | 193,289 |
| ≥ 2 h | 218 | 30.6% | 127,898 |
| ≥ 4 h | 104 | 14.6% | 44,985 |
| ≥ 8 h | 90 | 12.6% | 39,002 |
| ≥ 12 h | 48 | 6.7% | 22,610 |
| (all commits, 14 d) | 712 | 100% | 346,567 |

Lean insertions per commit from
`git log --since='2026-07-23 00:00' --numstat --format='@@%h'`, summing
the added-lines column for paths ending `.lean`.

**Top 10 salt-seat silence windows that contained landings:**

| Silence | From | To | Commits inside | Lean lines |
|---:|---|---|---:|---:|
| **20.9 h** | 08-02 12:13 | 08-03 09:09 | **26** | **12,310** |
| 14.4 h | 07-24 17:45 | 07-25 08:11 | 3 | 2,591 |
| 13.4 h | 07-31 19:17 | 08-01 08:39 | 2 | 0 |
| 13.3 h | 08-03 18:31 | 08-04 07:47 | 13 | 5,754 |
| 12.4 h | 08-01 20:50 | 08-02 09:12 | 3 | 1,955 |
| 12.0 h | 07-23 19:14 | 07-24 07:15 | 1 | 0 |
| 11.3 h | 07-25 21:12 | 07-26 08:28 | 9 | 3,995 |
| 10.6 h | 07-22 20:44 | 07-23 07:22 | 4 | 0 |
| 10.6 h | 07-27 19:37 | 07-28 06:13 | 9 | 0 |
| 10.6 h | 07-26 20:35 | 07-27 07:09 | 5 | 4,652 |

**The single best exhibit is the first row: 20 h 56 m with no human word
reaching the salt seat, 26 commits landed, 12,310 lines of Lean inserted.**

### 4.3 The longest unattended run (the caller's requested proxy, computed exactly)

The task brief assumed "longest run of consecutive commits with no human
message in between" was not knowable from git. Joined against the
transcript, it is:

**34 consecutive commits, 2026-08-05 14:32:06 → 17:51:48, span 3 h 19 m 42 s,
with zero typed human messages between the first and the last.**

| Time | Commit | Subject (truncated) |
|---|---|---|
| 14:32 | `3e9691b` | EPSILON-SHARP — ε₀ 10⁻⁶ → 2·10⁻⁵ (20×) and c₃ 10⁻⁷ → 1/75712 (132×) |
| 14:37 | `a6fde73` | N4b DESIGN v2 post-refutation (4 refuters, 3 HOLD) |
| 14:58 | `ac3bce1` | N4b DESIGN v3 — the delta verdicts folded |
| 15:03 | `f7adffd` | N4B-W0(i+ii) — the beta0 erase-split of efZeroSumM |
| 15:06 | `85ea9b6` | N4b D9 — HSEP-GAP scout verdict RESTATEMENT-VIABLE |
| 15:09 | `0a40efb` | N4B-W0(iii) — A3 BATCHING |
| 15:12 | `c0c05ef` | N4B-W0(iv) — the σ=1 relaxation |
| 15:13 | `e2dbbab` | N4B-W0(v) — pretenseSum_unconditional_absorbed |
| 15:20 | `7f9eb09` | N4B-W0(vi+vii) — the UN-COLLAPSED EF socket |
| 15:21 | `fb23c3c` | N4B-W0 flags entry — seven for seven |
| 15:29 | `94583b0` | N4B-W0.5(1) — the socket generalization |
| 15:32 | `cfbfc9c` | N4B-W0.5(2) — the BOX-EXACT re-instantiation |
| 15:35 | `f94cedb` | N4B-W1 — (L1) one-sided at s = 1, new `Salt/HB/Lemma7L.lean` |
| 15:36 | `4b0c657` | N4b D10 — W1 home, 1st attempt |
| 15:41 | `8c11173` | N4B-W0.5(3) — HSEP RETIRES AS A THEOREM |
| 15:51 | `de25341` | N4B-W2(housekeeping) — 18 owed audit roll-call rows |
| 16:03 | `dc97692` | N4B-W2(the composite transfer) — new `Salt/HB/Lemma7EF.lean` |
| 16:06 | `09ad84f` | N4B-W2(ledger row) — VERDICT CLOSES AT T-EXPONENT 6 |
| 16:10 | `91e7ada` | N4B-W2(the EF bridge) — psiDefect_norm_le_of_ef |
| 16:15 | `b375d90` | N4B-W2(the uniformisation) — rpow_c_add_one |
| 16:16 | `4b891ea` | N4B-W2(flags amendment) |
| 16:21 | `25b0819` | N4B-W2b(b) — hceil retired in both ranges |
| 16:30 | `0211dbf` | N4B-W2b(a) — closed-form envelope + end-to-end composite |
| 16:36 | `e0de5c0` | N4B-W2b(d) — the tail form |
| 16:37 | `b7a3d88` | N4B-W2b(flags) — new structural finding |
| 16:39 | `616b36d` | N4b D11 — the multiplicity correction |
| 16:53 | `394b1d1` | N4B-W3(integral) — THE CALCULUS HEART lands |
| 17:09 | `a08aab6` | N4B-W2c(c1+c2 core) |
| 17:10 | `e6f8a8a` | N4B-W3(segment+assembly) — the χ(p)=1 half KILLED in the kernel |
| 17:25 | `d802b99` | N4B-W2c(c3+c4) — RANGE B AT EVERY HEIGHT |
| 17:27 | `7e04049` | N4B-W2c(flags) |
| 17:36 | `f6ddddc` | N4B-W4(α+γ) — the product layer + THE ASSEMBLY TO (L2) |
| 17:44 | `014fb4f` | N4B-W4(β) — hseg + hcorr discharged |
| 17:51 | `fb44672` | N4B-W4(α′) — ppDefect ≤ 10/√⌊z⌋; both W3 rows CLOSED |

For comparison, the longest run computed from git alone (consecutive
commits all inside 21:00–05:00) is **29 commits, 2026-07-28 21:03:55 →
2026-07-29 04:01:55, span 6 h 58 m** (`441ae3e` … `0240672`). Runner-up
runs: 13 commits 07-29 21:29 → 07-30 02:43 (5 h 14 m); 13 commits 07-30
21:21 → 23:54; 11 commits 07-25 21:02 → 23:06.

### 4.4 Authorship

| Quantity | Value | Command |
|---|---|---|
| Commit authors, last 14 d | 1 — `Jason Hickey <jasonh@gmail.com>`, all 712 | `git log --since='2026-07-23 00:00' --format='%an <%ae>' \| sort \| uniq -c` |
| Commits carrying `Co-Authored-By: Claude Fable 5` | **566 / 712 (79.5%)** | `git log --since=… --format='%H%n%b%n---END---'` + awk |
| Authors all-time | `the pre-remap address` 1,108 · `jasonh@gmail.com` 809 · `Claude <noreply@anthropic.com>` 19 · `cloud-shift <jason@karyk.com>` 4 | `git log --format='%an <%ae>' \| sort \| uniq -c` |

**Do not quote the author field as evidence of who wrote the proofs** — it
is the committer identity, not the author of the mathematics. The
`Co-Authored-By` trailer is the honest signal, and it covers 79.5% of the
window (the remainder are ceremony/doc commits that skip the trailer).

---

## 5. THE 8/5 DAY — case study

`TZ=America/Los_Angeles git log --since='2026-08-05 00:00' --until='2026-08-06 00:00' --reverse --date=format-local:'%H:%M' --format='%ad|%h|%s'`

| Quantity | Value |
|---|---:|
| Commits | **45** |
| First → last | 10:24 → 18:36 (**8 h 12 m**) |
| Commits touching `.lean` | 31 |
| Lean insertions / deletions | **8,891 / 84** |
| All-files insertions / deletions | 11,104 / 94 |
| Distinct files touched | 20 (14 `.lean`) |
| New `.lean` files created | **8** |
| Declarations added (added lines matching a decl keyword) | **253** |
| Commits in the 21:00–05:00 window | **0** |
| Longest run with no typed human message | **34 commits / 3 h 20 m** (§4.3) |

New files: `Salt/HB/Lemma7.lean`, `Lemma7EF.lean`, `Lemma7F.lean`,
`Lemma7Kappa.lean`, `Lemma7L.lean`, `Lemma7Prod.lean`, `MOne.lean`,
`Salt/SW/EpsilonZero.lean`.

### "Thirteen waves in a day" — the true number

`docs/exploration/triple-campaign-0805.md:23-24` says "HB Lemma 7 assembled
8/5 in one day/night across 13 waves", and `:65` says "13 first-attempt
landings on 8/5". Counting distinct wave labels in the 45 subject lines:

| Wave family | Distinct labels | Commits |
|---|---:|---:|
| `N4B-W0`, `W0.5`, `W1`, `W2`, `W2b`, `W2c`, `W3`, `W4`, `W4.5` | 9 | 30 |
| `N4B-SYMSPLIT` | 1 | 2 |
| `M-ONE` | 1 | 1 |
| **HB Lemma 7 execution waves** | **11** | **33** |
| morning constants work (`Rrem absorption`, `EPSILON-ZERO`, `ZETA-INV-SHALLOW`, `EPSILON-SHARP`) | 4 | 4 |
| **all Lean-landing waves on 8/5** | **15** | **37** |
| design blocks (`DESIGN v2`, `v3`, `D9`, `D10`, `D11`) | 5 | 5 |
| scout dossiers (`N6-SCOUT`, `ONE-WALL-SCOUT`, `TAU-SHARP-SCOUT`) | 3 | 3 |

**The true count is 11 HB-Lemma-7 execution waves, or 15 Lean-landing
waves counting the morning's constants work — not 13.** Say 11 or 15,
whichever you mean, and never 13. "13 first-attempt landings" is
separately **UNVERIFIED**: first-attempt status is a `flags.md` claim, not
derivable from git, and it was not checked in this harvest.

Also note: the day's work ran 10:24–18:36 with **zero** commits in the
sleep window. 8/5 is an excellent exhibit for *throughput and
first-attempt density under a frozen design*; it is a poor exhibit for
*overnight autonomy*. Use 8/2→8/3 (§4.2, 20.9 h silence, 26 commits,
12,310 lines) for that.

---

## 6. THE PAPERS

| | `papers/witness/` | `papers/flagship/` |
|---|---|---|
| `main.tex` lines | **1,714** | **1,338** |
| `main.tex` bytes / mtime | 90,483 · 2026-08-04 19:12 | 69,097 · 2026-08-03 11:08 |
| `main.pdf` present | yes | yes |
| `main.pdf` size / mtime | **500,778 B · 2026-08-04 19:12** | **452,603 B · 2026-08-04 08:24** |
| PDF newer than source | equal timestamp (fresh) | yes (fresh) |
| Pages, from `main.log` | **20** | **17** |
| LaTeX errors in `main.log` (`^!`) | **0** | not checked |
| LaTeX warnings | 3 | not checked |
| `\leanname{…}` uses | **35** | 17 |
| `\leaninline{…}` uses | **137** | 135 |
| **Total statement-to-declaration keyings** | **172** | **152** |
| Distinct `\leanname` arguments | 20 | — |

`pdflatex` was **not run** (executors are working; the brief forbade
disturbing them). The "compiles" evidence is: a `main.pdf` exists, its
mtime matches or postdates its `main.tex`, and `main.log` records
`Output written on main.pdf (20 pages, 500778 bytes)` with zero `!`
errors. Commands: `ls -la papers/*/main.*`;
`grep -aoE 'Output written on main.pdf \([0-9]+ pages, [0-9]+ bytes\)' main.log`;
`grep -o '\leanname{' main.tex | wc -l`.

Also present: `papers/witness/ARXIV-PACKAGE.md` (3,495 B, 2026-08-05
12:34), `papers/witness/pi-overview-draft.md` (3,440 B, 2026-08-05 15:23),
`papers/flagship/floor-chen-seed.tex` (333 ln), `papers/flagship/inserts/`.
A stale `main.pdf` (377,028 B, 2026-07-19 19:25) sits at the repo root
with its aux files — **repo hygiene item**, unrelated to either paper
directory.

The witness paper's `\leanname`/`\leaninline` macros are defined at
`papers/witness/main.tex:75-76` and render as monospace — i.e. the keying
is typographic, and a reader can grep each name against the corpus. That
is the mechanism worth describing, and 172 keyed citations in a 20-page
paper is the number.

---

## 7. FIRSTS AND DEPTH MARKERS — quoted, not embellished

Every claim below is reproduced **exactly** as the repo states it. The
right-hand column says whether a *supporting prior-art note* exists in the
repo — not whether the claim is true.

| Claim, quoted verbatim | Source | Prior-art support in repo? |
|---|---|---|
| "**The first machine-checked Littlewood-strength zero-free region**" | `docs/RESULTS.md:94` | **YES** — `docs/exploration/pi-prep-0731.md:624-636` names the comparison set a referee will reach for (PrimeNumberTheoremAnd; Eberl–Loeffler *Formalizing zeta and L-functions in Lean*, arXiv:2503.00959; Eberl et al. Isabelle; Song–Yao Isabelle PNT) and states the prior state of the art as "classical de la Vallée Poussin shape". `docs/blueprints/next-rung-scoping.md:28-42` is the external-state survey. |
| "**The power zero-free region, θ = 3/4** — the first in any proof assistant" | `docs/RESULTS.md:95` | **YES** — same note; the paper hedges it as "To our knowledge … the first zero-free region with a power saving in the exponent verified in any proof assistant" (`papers/flagship/main.tex:255-258`). |
| "the first machine-checked negative result about a sieve method" | `docs/blueprints/twinbar.md:7` and `:27`; `docs/blueprints/flags.md:2611` ("The FIRST machine-checked negative result about a sieve method") | **PARTIAL** — asserted three times, no prior-art search recorded. |
| "To our knowledge the first machine-checked LOWER-bound sieve theorem anywhere" | `docs/blueprints/p0.md:100` (node B5) | **PARTIAL** — hedged "to our knowledge"; no search recorded. |
| "To our knowledge the first machine-checked Rosser–Iwaniec linear sieve" | `docs/blueprints/flags.md:3983` | **PARTIAL** — hedged; `next-rung-scoping.md:40-41` does state "AFP has the analytic-layer templates … but **zero sieve theory**", which supports it indirectly. |
| "first in a proof assistant" (Rosser–Iwaniec linear sieve, upper side) | `docs/RESULTS.md:170` | **PARTIAL** — the RESULTS row drops the "to our knowledge" hedge that `flags.md:3983` carries. **Recommend restoring the hedge.** |
| "To our knowledge the FIRST formalization of Siegel's theorem in any proof assistant" | `docs/blueprints/flags.md:3402` | **PARTIAL** — hedged; supported indirectly by "Nothing Siegel–Walfisz-shaped anywhere in Lean" (`next-rung-scoping.md:32-33`). |
| "believed the first FL at dimension > 1 in any proof assistant" | `docs/RESULTS.md:176` | **PARTIAL** — already double-hedged ("believed"); no search recorded. This is the correctly-worded model for the others. |
| "First Mertens lower bound + windowed second theorem in Lean anywhere" | `docs/blueprints/p0.md:100` (node PM1) | **YES (partial)** — the same row records the recon that produced it: "NOTHING windowed/lower exists in corpus OR mathlib; mathlib has NO Mertens at all". |
| "THE FIRST MACHINE-CHECKED WEIL-STRENGTH POINT-COUNT BOUND" | `docs/exploration/pilot.md:4199` | **NO** — a session-log banner, all-caps, no search recorded. |
| "the 1874 theorem, believed FIRST in any proof assistant" (`mertens_third`) | `docs/exploration/pilot.md:6425` | **PARTIAL** — hedged "believed"; no search recorded. Note `mertens_third` has **no `RESULTS.md` row**. |
| "To our knowledge no prior formalization of this machinery exists in any assistant" (Maynard–Tao) | `docs/blueprints/maynard-guide.md:65` | **YES (partial)** — `next-rung-scoping.md:35-39`: "**Nobody in any assistant** has: the large sieve, Bombieri–Vinogradov, Maynard–Tao in load-bearing form, or Chen. Even Vaughan's identity is unformalized." |

**What the papers themselves claim.** The flagship makes exactly two
firstness claims, both hedged and both about zero-free regions
(`papers/flagship/main.tex:106-108`, `:155-157`, `:255-258`). **The
witness paper makes no firstness claim at all** — `grep -n '\bfirst\b'`
over `papers/witness/main.tex` returns only ordinal and rhetorical uses.
That discipline is itself worth pointing at.

### Overclaim risk, named

1. `docs/RESULTS.md:170` states "first in a proof assistant" flat where the
   flags entry it derives from says "To our knowledge the first". The
   registry is the stronger-sounding document and the weaker-sourced one.
2. Four claims rest on a single all-caps session-log line with no recorded
   search: the Weil point-count bound, and the sieve-negative-result claim
   (three restatements of one assertion).
3. No claim in this table has a *dated, reproducible* prior-art search
   attached to it except through `pi-prep-0731.md` (zero-free regions) and
   `next-rung-scoping.md` (sieve theory / Maynard / BV). **Everything else
   should carry "to our knowledge" in public text**, and the two documented
   ones should carry their search date.

---

## 8. HEADLINE NUMBERS — safe to speak

Each of these was measured today, by a command recorded above.

1. **652,312 lines of Lean 4** over mathlib, **1,130 files**, **19,564
   declarations**, **1,940 commits** — built in **30 days** from a bare
   scaffold (first commit 2026-07-06 23:17 PDT).
2. **21,744 Lean lines per day, sustained, for 30 days.** The corpus grew
   **21.3% (+114,404 lines) in the last five days alone**.
3. **Zero `sorry`. Zero `native_decide`. Zero home-rolled axioms** —
   verified in tactic position by a comment-stripping scan over all 1,130
   files, not by prose grep (the naive grep returns 269 / 196 / 2, all in
   docstrings).
4. **Axiom base exactly `{propext, Classical.choice, Quot.sound}`,
   enforced at build time** by `#audit_axioms` — **166 invocations naming
   6,302 distinct declarations** across 24 files. A violation is a build
   failure, not a report.
5. **73 headline theorems in `docs/RESULTS.md`, all lint-verified**:
   `results_lint: OK — 73 rows, all verified (file exists, declaration
   exists, date + commit well-formed)`. **65 are named in a build-time
   audit roll call; the other 8 are covered by `blueprint_lint`'s separate
   pass, and the registry says so in its own Axioms column.**
6. Named results include: **Brun's theorem**; **Chen's theorem** and
   **Chen's second theorem**, unconditional; **Siegel–Walfisz,
   unconditional**; **bounded prime gaps, unconditionally**; **explicit
   bounded gaps ≤ 12**; the **Vinogradov Mean Value Theorem**; the **Weil
   bound for Kloosterman sums**; the **Montgomery–Vaughan generalized
   Hilbert inequality**; **Deuring–Heilbronn repulsion**; the **Alpöge
   counterexample to the Jacobian conjecture**.
7. **In the last 14 days: 712 commits, 346,567 Lean lines inserted.**
8. **46.9% of those commits (334) and 193,289 Lean lines landed during a
   stretch in which no human message reached the salt seat for at least an
   hour.** At the ≥8 h threshold: **90 commits, 39,002 lines.**
9. **The best single exhibit: 20 h 56 m of silence (2026-08-02 12:13 →
   08-03 09:09), 26 commits landed, 12,310 lines of Lean.**
10. **The longest unbroken run: 34 consecutive commits in 3 h 20 m
    (2026-08-05 14:32 → 17:51) with not one typed human word between the
    first and the last** — the assembly of HB Lemma 7 waves W0 through W4.
11. **8/5, measured: 45 commits in 8 h 12 m, 8,891 Lean insertions, 8 new
    files, 253 declarations, across 11 HB-Lemma-7 execution waves (15
    Lean-landing waves counting the morning).**
12. **79.5% of the last 14 days' commits (566/712) carry a
    `Co-Authored-By: Claude` trailer.**
13. **Two papers, both compiled and current**: the witness paper (20 pp,
    1,714 tex lines, **172 statement-to-declaration citations**) and the
    flagship (17 pp, 1,338 tex lines, 152 citations).
14. **Independent kernel replay: 259/259 modules, 0 failures** (2026-07-21,
    `docs/reports/lean4checker-local-1.md:11`) — *always with its scope
    caveat, see below*.

---

## 9. DO NOT QUOTE — the soft list

| Item | Why |
|---|---|
| **"13 waves on 8/5"** | Measured: **11** HB-Lemma-7 execution waves, or **15** Lean-landing waves counting the morning constants work. 13 matches neither. |
| **"13 first-attempt landings on 8/5"** | **UNVERIFIED.** First-attempt status is a `flags.md` narrative claim; not derivable from git and not checked here. |
| **"one person asleep" / "zero human hours" as a description of the 14 days** | The measured sleep-window (21:00–05:00) share is **10.7%**, and 77.2% of commits land 07:00–18:59. The last five days carry **two** night commits total. The autonomy claim is real but its unit is the **multi-hour silence window**, not the night. Use §4.2/§4.3, never the night column. |
| **"259/259 modules independently re-verified" without its caveat** | Two problems: (a) the report's own scope caveat — `pi-prep-0731.md:616-618` says do not read it as "every declaration"; (b) it is dated 2026-07-21 and the corpus has grown **21%** since. Say "as of 2026-07-21" and "content modules", or re-run. |
| **A percentage of the corpus described as "axiom-audited"** | 6,302 of 19,564 declarations (32.2%) are *named* in a roll call. Transitive coverage is much higher but was **not measured** (it needs a build). Quote the 6,302 and the 166 assertions; do not quote a coverage percentage. |
| **"256 numbered catches"** | The highest catch number in `docs/blueprints/flags.md` is indeed **#256**, but `grep -ioE 'catch #[0-9]+'` finds only **94 distinct numbers** cited in the file. 256 is a monotone counter, not a count of retrievable entries. Say "the catch ledger runs to #256", not "256 catches are recorded". |
| **"zero wrong proofs" / "no design error first discovered by the kernel"** | **UNVERIFIED here.** Both are `flags.md` / `main.tex:682-689` narrative claims. Not checkable from the repo state; needs its own audit before public use. |
| **The git author field as evidence of authorship** | All 712 commits in the window are authored `Jason Hickey`. The honest signal is the `Co-Authored-By: Claude Fable 5` trailer (566/712). |
| **"first in a proof assistant" without a hedge** (`docs/RESULTS.md:170`) | The source `flags.md:3983` hedges it; the registry does not. Restore the hedge before public use. |
| **"THE FIRST MACHINE-CHECKED WEIL-STRENGTH POINT-COUNT BOUND"** | Sole source is an all-caps session-log line (`docs/exploration/pilot.md:4199`) with no recorded prior-art search, and it has no `RESULTS.md` row. |
| **`mertens_third` as a headline** | Claimed "believed FIRST in any proof assistant" at `pilot.md:6425` but has **no `RESULTS.md` row** — so it is outside the lint-verified 73 and outside the registry's guarantees. |
| **"640K+ lines" (the campaign doc's figure)** | Measured today: **652,312**. Use the measured number; it is larger and it is checkable. |

---

## 10. WHAT SURPRISED THE HARVEST

1. **The unattended claim survives, but not in the form it was being told.**
   The night column is thin (10.7%, and ~0 for the last five days). The
   claim that *does* hold, with numbers: nearly half of all landings — and
   193,289 lines of Lean — occur inside stretches where the seat receives
   no human direction for an hour or more, with a 20 h 56 m / 26-commit /
   12,310-line exhibit at the top. The unit is the silence window.
2. **The transcript record was contaminated in a way that flattered the
   opposite conclusion.** `<task-notification>` blocks are injected as
   user-role messages. Counting them made it look as though 98.5% of
   commits landed within 30 minutes of a human message. Filtering them
   moved the ≥1 h figure from 0.3% to 21.5%. Any future ledger must filter
   `<task-notification>`, `<system-reminder>` and `<command-name>` — and
   should say so.
3. **`--since='2026-07-23'` and `--since='2026-07-23 00:00'` return
   different commit sets** (654 vs 712) — the bare date is parsed as UTC.
   Two commits in the window also carry `+0000` offsets from cloud runs.
   Every git figure here uses an explicit time and
   `--date=format-local` under `TZ=America/Los_Angeles`.
4. **The naive `sorry`/`native_decide` greps are catastrophically
   misleading** — 269 and 196 hits, every one a docstring. The corpus is
   penalized by its own documentation discipline. The claim must always be
   stated as "verified in tactic position", with the stripped scan beside
   it, or a skeptic running the obvious grep will conclude the opposite.
5. **The registry is honest where it would be easy not to be.** All 73
   rows carry an audit citation, zero carry `⚠ unaudited`, and the eight
   rows outside the build-time roll call are exactly the eight that say so
   in their own Axioms column. Superseded rows (`logChowla2_ineffective`
   v1→v6) are marked in place with the defect that killed them, including
   one the corpus found by refuting itself
   (`Salt.MR.cofkL_bulk_false_at_socket`, `Salt/MR/RegisterInhabit.lean:260`).
6. **The witness paper claims no firsts at all.** Zero firstness assertions
   in 1,714 lines. The overclaim risk lives entirely in the internal docs,
   not in the publication-track text — which means it is fixable before
   anything ships.
7. **The corpus grew 21% in the five days since the last snapshot was
   taken.** Any evidence page must carry a harvest date, because these
   numbers go stale in under a week.
