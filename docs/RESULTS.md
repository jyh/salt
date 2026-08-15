# THE TROPHY ROOM — the headline registry of the salt corpus

> **PRIORITY LANGUAGE (2026-08-11).** Every "first" in this register is a *surveyed as-of* claim — first **in any public artifact** as of the survey date, never an assertion of absence. Survey: `${SEAT_DIR}/briefs/2026-08-11-priority-audit.md` (adversary-cited, five lanes). Salt is a private tree; re-run the survey before any of these language is published. *Absence-by-grep lost every contested row in that audit.*

**READ THIS BEFORE ASSERTING ABSENCE.** If a result has a row here, it is in the
Lean kernel, on this branch, at the file and line shown. Three times in the week
of 2026-07-27 the seat reported landed work as open because a hand-maintained
index had gone stale; this document is the countermeasure, and it has mechanical
teeth (`scripts/results_lint.py`).

## THE LAW OF THIS DOCUMENT

1. **One row per headline result.** Publishable-tier theorems and the
   infrastructure firsts that carry them. Supporting lemmas belong in the
   audit ledgers (`Salt/*/All.lean`), not here.
2. **Every row carries a DATE and a COMMIT.** The date is the day the
   declaration first entered the tree, recovered by pickaxe over the file's
   own history (`git log -S"theorem <name>" --reverse -- <file>`), not the
   day the file was last touched.
3. **Chronology is the DATE FIELD, never file order.** Rows are grouped by
   arc and sorted by date inside an arc. Nothing about position in this file
   carries meaning.
4. **Superseded rows are marked `[SUPERSEDED → successor]` IN PLACE.** They
   are never deleted — a deleted row is how amnesia gets back in.
5. **Every row is lint-verified.** `python3 scripts/results_lint.py` checks
   that each row's file exists, that the file actually declares that name,
   and that the row has a well-formed date and commit. Green is required
   before any commit that touches this file.
6. **A new headline theorem adds its row in the SAME commit that lands it.**
   Not the next commit, not the ceremony afterwards. The same commit.
7. **This file states existence, not meaning.** The one-line statements are
   paraphrases for orientation. The Lean statement is the authority; when the
   two disagree, the Lean statement wins and the row gets fixed.

### The Axioms column

Every landed track carries an `#audit_axioms` ledger asserting its declarations
depend on at most `[propext, Classical.choice, Quot.sound]` (CLAUDE.md iron
rule 3). This column cites the certification rather than re-running it:

- **`3 (path:line)`** — three axioms, certified by the `#audit_axioms` block
  beginning at that line.
- **`3 (blueprint_lint P1/P3)`** — certified by `scripts/blueprint_lint.py`
  phase 1 (brun-guide card declarations) or phase 3 (the HEADLINERS list).
- **`⚠ unaudited`** — the theorem is sorry-free and in the kernel, but **no
  ledger names it and no audited declaration is known to depend on it**. This
  is a real gap in the audit surface, recorded here rather than papered over.
  Eight rows currently carry it; closing them is a standing chore (add the
  name to the track's `#audit_axioms` block).

### Related registers

[CAMPAIGNS.md](CAMPAIGNS.md) — one entry per campaign (goal, status, trail).
[blueprints/flags.md](blueprints/flags.md) — the numbered catches, the sole
authority on the method's record. [METHODS.md](METHODS.md), [OPERATIONS.md](OPERATIONS.md)
— the how. This file is the WHAT: the results themselves.

---

## 1. Sieve / Brun

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.N6.N6_2` | **Brun's theorem**: the sum of reciprocals of the twin primes converges. | Salt/Brun/N6.lean:231 | 2026-07-07 | `378712b` | 3 (blueprint_lint P3) |
| `Salt.M5BigO.N5_3` | `twinPrimeCounting N` is `O(N/(log N)²)` — explicit constant 25700. | Salt/Brun/M5BigO.lean:295 | 2026-07-07 | `3217afc` | 3 (blueprint_lint P1) |
| `Salt.BrunLower.twin_almost_prime` | Infinitely many `n` with `Ω(n(n+2)) ≤ 20` — the corpus's first lower-bound sieve. | Salt/BrunLower/TwinInstance.lean:771 | 2026-07-12 | `111a4d7` | 3 (Salt/BrunLower/All.lean:54) |
| `Salt.HardyLittlewood.twinCounting_upper_order` [tier-2] | Order-sharp packaging: `∃ C > 0`, `π₂(N) ≤ C·N/(log N)²` for all large `N`. | Salt/HardyLittlewood/Frame.lean:117 | 2026-07-17 | `8309019` | 3 (Salt/HardyLittlewood/All.lean:23) |
| `Salt.HardyLittlewood.twinCounting_upper_sharp` | The sharp-order twin upper bound: `C ≤ 100` (here 90) with `π₂(N) ≤ C·N/(log N)²` — a factor ≈285 off the landed 25700. | Salt/HardyLittlewood/Sharp.lean:786 | 2026-07-18 | `fb9371e` | 3 (Salt/HardyLittlewood/All.lean:23) |

## 2. Chen / Goldbach

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.Chen.chen_headline` | **Chen's theorem**, unconditional: infinitely many primes `p` with `p+2` prime or a product of two primes. | Salt/Chen/ChenTheorem.lean:32 | 2026-07-15 | `9306e04` | 3 (Salt/Chen/All.lean:193) |
| `Salt.Goldbach.chen_goldbach` | **Chen's second theorem**, unconditional: every sufficiently large even `N` is `p + q` with `p` prime and `q` a `P₂`. | Salt/Goldbach/ChenGoldbach.lean:41 | 2026-07-16 | `d68c855` | 3 (Salt/Goldbach/All.lean:86) |
| `Salt.Chen.no_readable_certificate` | Any certificate reading only the four carrier-row values `(a₁,a₂,a₃,s)` certifies nothing: its guaranteed twin mass is `≤ 0`. | Salt/Chen/WeightNoGo.lean:82 | 2026-07-16 | `db882a7` | 3 (Salt/Chen/All.lean:193) |

## 3. SW / BV / bounded gaps

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.Maynard.bounded_gaps_from_eh_complete` | The Maynard capstone: `BoundedGapsFromEH` with no residual hypotheses (`CompatFrontier` proved for every regime width). | Salt/Maynard/Complete.lean:1472 | 2026-07-09 | `418df26` | 3 axioms (audited) |
| `Salt.Twelve.gaps_le_twelve` | Explicit bounded gaps **≤ 12** (standing analytic inputs `WindowPNT`, `EHall`): for every `N`, two primes `p ≠ q > N` with `\|q−p\| ≤ 12`. | Salt/Twelve/GapsUncond.lean:1061 | 2026-07-11 | `6b24881` | 3 (blueprint_lint P3) |
| `Salt.BV.bounded_gaps_of_siegelWalfisz` | Bounded prime gaps from Siegel–Walfisz — the first Bombieri–Vinogradov chain consumed by a downstream theorem, in any public artifact as of 2026-08-11 (see the priority survey). | Salt/BV/AbelCore.lean:757 | 2026-07-12 | `fa06560` | 3 (Salt/BV/All.lean:58) |
| `Salt.SW.siegelWalfisz_holds` | **Siegel–Walfisz, unconditional**: `\|ψ(x;q,a) − x/φ(q)\| ≤ K·x/(log x)^A` uniformly for `q ≤ (log x)^C`, `a` reduced. | Salt/SW/Gate.lean:150 | 2026-07-13 | `0d6a613` | 3 (Salt/SW/All.lean:124) |
| `Salt.SW.bounded_gaps_unconditional` | **Bounded prime gaps, unconditionally**: `∃ C`, infinitely many prime pairs within `C`. The gate composed with the BV+Maynard chain. | Salt/SW/Gate.lean:376 | 2026-07-13 | `0d6a613` | 3 (Salt/SW/All.lean:124) |

## 4. Zero theory (ZFR / Littlewood / zero-count)

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.SW.zeta_zero_free_region` | de la Vallée Poussin for ζ: every zero with `Re ρ ≥ 1/2` obeys `Re ρ ≤ 1 − c₃/log(\|Im ρ\|+2)`. | Salt/SW/ZetaZeroFree.lean:235 | 2026-07-12 | `89799db` | 3 (Salt/SW/All.lean:124) |
| `Salt.SW.zero_free_region_all` | The combined zero-free region for primitive characters, one constant `c₀ = 1/126848`, off Siegel territory. | Salt/SW/ZeroFreeReal.lean:605 | 2026-07-12 | `fc1c75c` | 3 (Salt/SW/All.lean:124) |
| `Salt.ExpSum.zeta_growth_strip` | `‖ζ(σ+it)‖ ≤ C·t^{1−σ}(1+log t)` on `1/2 ≤ σ ≤ 1` — at `σ = 1` a genuine `O(log t)`. | Salt/ExpSum/ZetaApprox.lean:562 | 2026-07-17 | `7cbd0d0` | 3 (Salt/ExpSum/All.lean:32) |
| `Salt.SW.LFunction_zero_count_near_one` | Radius-resolved Prachar count: zeros of `L(·,χ)` in `closedBall 1 r`, with multiplicity, number `≤ 7200·(1 + r·log(q+2))`. | Salt/SW/ZeroCountNearOne.lean:98 | 2026-07-17 | `51205bb` | 3 (Salt/SW/All.lean:124) |
| `Salt.Vk.zeta_zero_free_region_littlewood` | **The first machine-checked Littlewood-strength zero-free region**: `Re ρ ≤ 1 − c·loglog\|Im ρ\|/log\|Im ρ\|` (`c = 1/88214`). | Salt/Vk/Littlewood.lean:409 | 2026-07-18 | `61f6ccf` | 3 (Salt/Vk/All.lean:52) |
| `Salt.Vk.zeta_zero_free_region_pow` | **The power zero-free region, θ = 3/4** — the first in any public artifact as of 2026-08-11 (see the priority survey): `Re ρ ≤ 1 − c/((log\|Im ρ\|)^{3/4}(loglog\|Im ρ\|)³)`. | Salt/Vk/GrowthPow.lean:1044 | 2026-07-18 | `65d361d` | 3 (Salt/Vk/All.lean:52) |
| `Salt.MR.zeta_lower_all_t` | The all-`t` uniform ζ lower bound: `c''/((log(\|t\|+3))^{3/4}·(loglog(\|t\|+16))⁴) ≤ ‖ζ(1+d'+it)‖`, pole point excluded. | Salt/MR/ZetaLowerAllT.lean:273 | 2026-07-18 | `d9e92ba` | 3 (Salt/MR/All.lean:399) |

## 5. VMVT / VK

The Vk massif's *exports* are the two zero-free regions in §4; the box/orbit
machinery beneath them is ledger-audited at `Salt/Vk/All.lean:52`.

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.Vmvt.vmvt` | **The Vinogradov Mean Value Theorem** (Theorem 24.5): for `k ≥ 2`, `J_k(x, kr) ≤ D(k,r)·x^{E(k,r)}` with the exponent source-EXACT. | Salt/Vmvt/Summit2.lean:151 | 2026-07-18 | `f779f43` | 3 (Salt/Vmvt/All.lean:39) |

## 6. Heath-Brown / Fulcrum / T-BAL

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.SW.dh_repulsion_ordered` | **Deuring–Heilbronn repulsion**, explicit `(b, c, k)`: a real-character Siegel zero `β₀` repels every nearby zero, on the `16/17` window, ordered `Re ρ ≤ β₀`. | Salt/SW/TBalR8.lean:1752 | 2026-07-18 | `f1b92ca` | 3 (Salt/SW/All.lean:124) |
| `Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros` | The dichotomy's unconditional half: `¬ FulcrumQualityMin C` yields the effective gap `NoSiegelZeros`. | Salt/Fulcrum/Dichotomy.lean:82 | 2026-07-19 | `c9f311e` | 3 (Salt/Fulcrum/All.lean:54) |
| `Salt.Fulcrum.fulcrum_dichotomy` | **The Fulcrum dichotomy**: given the Heath-Brown engine at threshold `C` as a hypothesis, `TwinPrimeConjecture ∨ NoSiegelZeros`. | Salt/Fulcrum/Dichotomy.lean:102 | 2026-07-19 | `c9f311e` | 3 (Salt/Fulcrum/All.lean:54) |
| `Salt.HB.hb_l2c_master_unconditional` | The L2c master, fully unconditional: the `hb_lemma2` conclusion from the bare four-hypothesis packet — no `hcount`, no `hLz0`, no residual. | Salt/HB/L2cMasterUncond.lean:85 | 2026-07-19 | `f8679a6` | 3 (Salt/HB/All.lean:54) |
| `Salt.HB.neutrality_rate` | The exchange-rate wall: `0 ≤ S⁽²⁾_f − S⁽¹⁾` unconditionally, and the rate bound `≤ EngineBound` under the budget hypothesis. | Salt/HB/SignRate.lean:53 | 2026-07-19 | `7711bad` | 3 (Salt/HB/All.lean:54) |

## 7. TwinBar / Parity

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.TwinBar.twin_bar` | For every continuous simplex weight `F`, `J₁F + J₂F ≤ 2·log2·I₂F` — the Polymath8b `k = 2` bound. | Salt/TwinBar/Impossibility.lean:173 | 2026-07-12 | `a7c1e42` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.no_twin_weight` | **The k=2 impossibility**: no continuous weight with positive `L²`-mass crosses the twin gate `2·I₂F < J₁F + J₂F`. | Salt/TwinBar/Impossibility.lean:276 | 2026-07-12 | `a7c1e42` | 3 (blueprint_lint P3; Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.M₂_squeeze` | **The two-sided squeeze** `1.383 ≤ M₂ ≤ 2·log 2 < 2`: an explicit rational witness below, `twin_bar` above. | Salt/TwinBar/Witness.lean:253 | 2026-07-12 | `d194d30` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.twinB_min_implies_twins` | The door: `TwinB_min → TwinPrimeConjecture` (past the threshold the twin sum is positive, so each `n` yields a survivor). | Salt/TwinBar/TwinDoor.lean:270 | 2026-07-15 | `4e210ad` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.wall_or_door` | The wall/door partition: any certificate capturing a positive proportion of the prime mass is NOT `SieveAgree`-tolerant at level `D`. | Salt/TwinBar/TwinDoor.lean:288 | 2026-07-15 | `4e210ad` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.least_k_theorem` | **The least-k theorem**: in the unmodified Maynard–Selberg class the least `k` with `M_k > 2` is `5` (no-go at 2,3,4; rational witness at 5). | Salt/TwinBar/LeastK.lean:127 | 2026-07-15 | `a84caff` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.SW.mmuRate_holds` | The effective Möbius summatory rate: for every `A > 0`, `\|M_μ(y)\| ≤ C·y/(log y)^A` past a threshold. On this the parity wall went unconditional. | Salt/SW/MobiusRateClose.lean:1059 | 2026-07-16 | `1a11dac` | 3 (Salt/SW/All.lean:124) |
| `Salt.TwinBar.parity_wall_unconditional` | **The effective parity wall, UNCONDITIONAL** — `parity_wall_effective` with its `LambdaSummatory` slot discharged by `mmuRate_holds`. | Salt/TwinBar/WallUnconditional.lean:31 | 2026-07-16 | `1a11dac` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.no_parity_beating_certificate_unconditional` | No tolerant certificate lower-bounds a positive fraction of the sifted sum — full stop, no hypotheses. | Salt/TwinBar/WallUnconditional.lean:44 | 2026-07-16 | `1a11dac` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.TwinBar.Sep.wall_of_indistinguishable` | The tolerant separation master: if a decoy `w` is reading-indistinguishable from `u` at budget `B`, then `Φ u ≤ cap w + 2B`. | Salt/TwinBar/Separation.lean:67 | 2026-07-16 | `2a59fce` | 3 (Salt/TwinBar/All.lean:70) |
| `Salt.Parity.TPC_implies_Z` | The Twin Prime Conjecture makes `Z θ A₀` hold, via the tautological twin-sufficient witness. | Salt/Parity/Z.lean:216 | 2026-07-19 | `cfba5b4` | 3 (Salt/Parity/All.lean:22) |
| `Salt.Parity.sufficient_true_not_parityInv` | **THE GAP THEOREM**: no twin-sufficient, true, parity-invariant completion predicate can exist at Brun grade (`θ ∈ (0,1/2)`, `A₀ ≤ 2`). | Salt/Parity/Z.lean:670 | 2026-07-19 | `5936e74` | 3 (Salt/Parity/All.lean:22) |
| `Salt.Parity.Z_implies_TPC` | On the certified window, `Z θ A₀` forces the Twin Prime Conjecture — with `TPC_implies_Z`, the equivalence `Z ⟺ TPC`. | Salt/Parity/Z.lean:687 | 2026-07-19 | `5936e74` | 3 (Salt/Parity/All.lean:22) |
| `Salt.TwinBar.parity_wall_corr_stable` | **[WALL-L2 — THE WALL, STRENGTHENED]** `parity_wall_unconditional`'s cap holds VERBATIM at `s₋ x` for the strictly larger class of certificates that need only be tolerant with respect to `SieveAgreeCorr`: reading the sieves' shift-2 correlation field on top of the three main-term fields buys a certificate nothing at the wall's own witnesses. It is a strengthening and not a restatement because `SieveAgreeCorr → SieveAgree`, so the tolerance hypothesis here is WEAKER than the landed wall's; it has content because the witness pair really does agree in the widened field (the `λλ` cross-term cancels between `s₊`/`s₋`, and the surviving one-point gap is `mmuRate`-controlled unconditionally). This is a strengthening of a NEGATIVE theorem at the real witnesses: nothing escapes the wall, crosses it, or evades it. It proves no lower bound, opens no positive rung, and says nothing about twin primes. | Salt/TwinBar/WallCorr.lean:220 | 2026-08-15 | `7c82089` | 3 (Salt/TwinBar/All.lean:178) |
| `Salt.Entropy.Chowla.twinDetecting'_imp` | **[WALL-L1 — THE STRENGTH LAW]** The polarity of the guarded detection notion, frozen in the kernel: `TwinDetecting' w → TwinDetecting w`, where `TwinDetecting'` (:75) is `TransportWall`'s `TwinDetecting` with the non-twin index held away from `0` (the conjunct `1 ≤ n`). The guarded notion is the STRONGER predicate, so the landed unguarded one carries the stronger wall and is never replaced; `TwinDetecting'` lands BESIDE it and is used only in this module's door and dichotomy statements, with `TransportWall.lean` byte-untouched. Boundary-map completion — no new claim about twins. | Salt/Entropy/Chowla/PinDichotomy.lean:82 | 2026-08-15 | `6332c2d` | 3 (Salt/Entropy/All.lean:454) |
| `Salt.Entropy.Chowla.blind_iff_const_fails_unguarded` | **[WALL-L1 — THE GUARD'S NECESSITY, KERNEL-VISIBLE]** At the landed unguarded definition the dichotomy is FALSE: the slack witness (`5` at `0`, `1` elsewhere) passes both slots and satisfies `TwinDetecting` at `(m, n) = (3, 0)` while being constantly `1` on `n ≥ 1` (`slack_witness_twinDetecting`, :98; the guard rejects it at :110). So the `1 ≤ n` guard is necessary rather than stylistic, and re-guarding the frozen definition in place would make that statement unprovable and break the build — the anti-repair fence is kernel-borne, not prose-borne. Boundary-map completion — no new claim about twins. | Salt/Entropy/Chowla/PinDichotomy.lean:119 | 2026-08-15 | `6332c2d` | 3 (Salt/Entropy/All.lean:454) |
| `Salt.Entropy.Chowla.blind_iff_const` **[THE PIN DICHOTOMY]** | **[WALL-L1]** Inside the slot class (`PmNormalized` + `PairCollapse`), twin-blindness is a single point: `¬ TwinDetecting' w` is EQUIVALENT to `w n = 1` for every `n ≥ 1`. The route is exact — global constancy of the pair correlation `k ↦ w k · w (k+2)` before anything else (the guarded hypothesis relates twin starts to non-twin starts and both classes are inhabited, at `3` and at `1`), then the seeds `n ∈ {1, 2, 4}` pin that constant to `+1` through complete multiplicativity, then the step `k ↦ k + 2` carries `+1` up from `w 1` and `w 2` over every index. No new claim about twins — boundary-map completion, zero flagship inches. | Salt/Entropy/Chowla/PinDichotomy.lean:137 | 2026-08-15 | `6332c2d` | 3 (Salt/Entropy/All.lean:454) |
| `Salt.Entropy.Chowla.pin_iff_detecting` | **[WALL-L1 — THE PIN IS DETECTION]** The dichotomy's contrapositive: inside the slot class, carrying a single `-1` at some `n ≥ 1` is equivalent to the guarded detection clause, with the two directions at `pinned_door` (:229) and `pin_minimal` (:235). So the weakest pin is already detection-sufficient and every detection-sufficient hypothesis above the slots factors through it — the bottom element, dual to `no_slot_derived_twin_linkage`. No new claim about twins — boundary-map completion, zero flagship inches. | Salt/Entropy/Chowla/PinDichotomy.lean:211 | 2026-08-15 | `6332c2d` | 3 (Salt/Entropy/All.lean:454) |
| `Salt.Entropy.Chowla.liouville_pinned` | **[WALL-L1 — THE CLASS IS INHABITED AWAY FROM THE CONSTANT]** `λ` sits on the detecting side at the separator `(m, n) = (3, 7)`: `λ3·λ5 = +1` against `λ7·λ9 = −1`, the `9`-side through `liouville_apply_mul`. So the dichotomy is vacuous on neither side. The descent route the proof uses carries its own positive control at `scripts/l1_gf2_control.py` — recast over `GF(2)` the seeds pin every sign below the cutoff, and dropping the `n = 4` seed exhibits a genuine second solution. No new claim about twins — boundary-map completion, zero flagship inches. | Salt/Entropy/Chowla/PinDichotomy.lean:260 | 2026-08-15 | `6332c2d` | 3 (Salt/Entropy/All.lean:454) |

## 8. The MR / Chowla campaign

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.MR.mvHilbertUniform_holds` | The Montgomery–Vaughan generalized Hilbert inequality, unconditional: `‖Σ_{i≠j} x_j x̄_i/(λ_j−λ_i)‖ ≤ (π/δ)·Σ‖x_i‖²`. | Salt/MR/MVCore2.lean:575 | 2026-07-19 | `c119b50` | 3 (Salt/MR/All.lean:399) |
| `Salt.MR.lambda_nonpret` | **λ-non-pretentiousness, unconditional**: `(1/4)·loglog x − 4·logloglog(\|t\|+16) − C ≤ 𝔻(λ, n^{it}; x)²` — the campaign's oldest open hypothesis, closed. | Salt/MR/NonPretClose.lean:49 | 2026-07-19 | `60537ef` | 3 (Salt/MR/All.lean:399) |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head` | The spine-budget head: the log-Chowla-2 contradiction with the AM–GM `t`/`g`/`hbudget1` residual discharged internally, `∀ extraFloor`. | Salt/Entropy/Chowla/SpineFinal.lean:750 | 2026-07-19 | `3aef39b` | 3 axioms (audited) |
| `Salt.Entropy.Chowla.log_chowla_two_door_only` | **The door-only terminal**: log-Chowla-2 does not fail, conditional on the Matomäki–Radziwiłł–Tao door ALONE — no other residual on any surface. | Salt/Entropy/Chowla/SpineFinal.lean:981 | 2026-07-19 | `3aef39b` | 3 axioms (audited) |
| `Salt.MR.halasz_ball_decay` | The Halász ball-decay exit stone: the head/tail split delivers the `(log X)^{−1/(32e)}` floor at the range-minimum head distance `M_range`. | Salt/MR/HalaszCore.lean:440 | 2026-07-20 | `9a2686c` | 3 (Salt/MR/All.lean:399) |
| `Salt.MR.thm_a2'` | **The S7/S8 summit**: Theorem A2′ in the kernel — the two-branch row capstone (`CapFreeFloor` branch unconditional), constants side by side. | Salt/MR/ThmA2Rows.lean:636 | 2026-07-27 | `6207cb2` | 3 (Salt/MR/All.lean:399) |
| `Salt.MR.mmuChiRate_holds_gated` | The χ-twisted `t`-uniform Möbius rate, unconditional: `‖Σ_{n≤y} μ(n)χ̄(n)n^{it}‖ ≤ C·y/(log y)^A` uniformly in `q ≤ (log y)^{12}`, `\|t\| ≤ y`. | Salt/MR/PortClose.lean:157 | 2026-07-30 | `6725743` | 3 (Salt/MR/All.lean:5463) |
| `Salt.Entropy.Chowla.towerDropSumFlat_ge_log_ratio` **[THE TOLL]** | The master law, lower half (sufficiency): `(1/(2A))·(w_J − w₀) ≤ S_J`, exactly — no relative loss. | Salt/Entropy/Chowla/TowerFlat.lean:419 | 2026-08-01 | `adb503f` | 3 axioms (audited) |
| `Salt.Entropy.Chowla.towerDropSumFlat_le_log_ratio_mul` **[THE TOLL]** | The master law, upper half (width necessity): `S_J ≤ (21/20)·(1/(2A))·(w_J − w₀)`. | Salt/Entropy/Chowla/TowerFlat.lean:443 | 2026-08-01 | `adb503f` | 3 axioms (audited) |
| `Salt.Entropy.Chowla.towerFlat_width_ge` **[THE TOLL]** | The width necessity: any crossing level forces `(λ₊+c) ≥ 4^{(20/21)A}·(λ₋+c)` — the honest form of KAPPA-SCOPE's `4^A`. | Salt/Entropy/Chowla/TowerFlat.lean:585 | 2026-08-01 | `adb503f` | 3 axioms (audited) |
| `Salt.Entropy.Chowla.towerFlat_width_le` **[THE TOLL]** | The no-overshoot companion: `(λ₊+c) ≤ (21/20)·4^A·(λ₋+c)`, bracketing the flat width in `[4^{(20/21)A}, (21/20)·4^A]`. | Salt/Entropy/Chowla/TowerFlat.lean:625 | 2026-08-01 | `adb503f` | 3 axioms (audited) |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2` **[THE PEARL]** | The witnessed flat-scale terminal at the LINEAR door: the crossing is gone from the surviving list; `A` symbolic and above the caller's `A₀`. **[8/02: the conclusion-side implication proved vacuous at the produced regime (the cap defect, found by the corpus's own Toll); the repaired lineage lives at the KlevF lever — see the v4-v6 rows]** | Salt/MR/S16FlatFinal.lean:136 | 2026-08-01 | `2040ee5` | 3 (Salt/MR/All.lean:7195) |
| `Salt.Entropy.Chowla.towerShape_width_ge` **[THE SHAPE-FREE TOLL]** | No shape of threshold schedule evades the toll: for ANY `φ ≥ A_b`, crossing forces `(c_b+λ_0)·4^{(20/21)A_b} ≤ c_b+λ_J`. | Salt/Entropy/Chowla/TowerShape.lean:362 | 2026-08-02 | `79c79ad` | 3 axioms (audited) |
| `Salt.MR.logChowla2_ineffective` | [SUPERSEDED → `logChowla2_ineffective_v4`; cap antecedent vacuous, CAP-SCOPE 2026-08-02] For EVERY depth `A₀`, a regime at window base `⌈e^{e^{3.2A}}⌉₊` with `A ≥ A₀`; outer hypothesis = the band-lane constant alone. No `x₀`, no `Hopq`, no Siegel. | Salt/MR/S16Uniform.lean:1061 | 2026-08-02 | `937aac9` | 3 (Salt/MR/All.lean:7215) |
| `Salt.MR.logChowla2_ineffective_v2` | [SUPERSEDED → `logChowla2_ineffective_v4`; cap antecedent vacuous, CAP-SCOPE 2026-08-02] The same, with the OUTER hypothesis list empty — the caller supplies only the depth `A₀`; the pin replaced by `Mfl ≤ flatDoorM A`. | Salt/MR/S16Uniform.lean:1707 | 2026-08-02 | `108d2c5` | 3 (Salt/MR/All.lean:7239) |
| `Salt.MR.logChowla2_ineffective_v3` | [SUPERSEDED → `logChowla2_ineffective_v4`] The composed terminal: three numeral riders left (`cs`, `T₀`, `Ks`), all on constants it produces. No band rider, no `Kc`/`Ct`/`Kq`, no Siegel hypothesis. **Its base-scale-cap antecedent is FALSE at the regime it produces (CAP-SCOPE 2026-08-02), so the implication is vacuous — do not cite.** | Salt/MR/S16Compose.lean:1112 | 2026-08-02 | `73d02e6` | 3 (Salt/MR/All.lean:7295) |
| `Salt.MR.logChowla2_ineffective_v4` | [SUPERSEDED → `logChowla2_ineffective_v5`] The classical `∃A` terminal with the base-scale cap DISCHARGED inside at the raised lever `KlevF A`, and the `T₀` rider re-cut onto its consumer's true tolerance `T₀ ≤ exp(√(flatDesignBase A)/2)`. Riders: `cs`, `T₀`, `Ks` on its own constants; conclusion-side: the builder's outer-scale ceiling `log x ≤ (31/ε)·H₊` and the co-factor supply, both at `KlevF A`. | Salt/MR/S16ComposeV4.lean:1002 | 2026-08-02 | `9647450` | 3 (Salt/MR/All.lean:7592) |
| `Salt.MR.logChowla2_ineffective_v5` | [SUPERSEDED → `logChowla2_ineffective_v6`] The classical `∃A` terminal with the base-scale cap AND the outer-scale ceiling both DISCHARGED inside at the raised lever `KlevF A`: `log x ≤ (31/ε)·H₊` is threaded down the whole uniform lane, so the **only** conclusion-side ask left is the co-factor supply. Riders: `cs`, `T₀`, `Ks` on its own constants, plus `XCeilRiderStrict ε g` on the caller's own outer-scale request (met by `g ≡ 0` and by the compose's own arm). **Its co-factor predicate is NOT dischargeable through the landed register `CofactorBulkL` (that register is FALSE at every socket this terminal produces — REGISTER-INHABIT 2026-08-03, row below); the REPAIRED ladder `D = ⌈log X⌉₊` discharges it, and `v6` is the result. The theorem itself is unaffected and citable.** | Salt/MR/XThread.lean:1367 | 2026-08-02 | `df19c2a` | 3 (Salt/MR/All.lean:7635) |
| `Salt.MR.cofkR_cofactorSupply_L_gk` | **[THE REGISTER, INHABITED]** ⟦RULING 9⟧'s co-factor supply `S16CofactorSupply_L_gk K Cq R M`, DISCHARGED at the repaired dilation ladder `D := ⌈log X⌉₊` with the predicate's own existential `C_R := 4·cofkRConst Cb` (not the pinned `gradeCR2 Cb`). All seventeen conjuncts of the refuted register are theorems: the band's true bottom `log B_v ≥ (1−1/loglog X)·log X` carries the divided window `log ⌊k₀/D⌋ ≥ (log X)/2`; every exit summand decays at rate `≥ ρ₂₉₃`; both contour boxes fall to `Tstar2_mono` + `Tstar2_le_self`; the `T`-window is `capfloor_core`'s `log 2T ≥ (log X)/2`. What is left: ONE scale gate (`cofkRThr`, absorbed by the design constant) and ONE named cushion (`K_vt`, Siegel-genre). | Salt/MR/RegisterRepair.lean:476 | 2026-08-03 | `b36f53a` | 3 (Salt/MR/All.lean:7736) |
| `Salt.MR.logChowla2_ineffective_v6` | **[THE TERMINAL, PREDICATE-FREE]** `v5` with the co-factor supply PROVEN INSIDE instead of asked for — no conclusion-side predicate remains. Outer hypotheses: NONE. Inner: `e^{-100} ≤ cs`, `T₀ ≤ exp(√(flatDesignBase A)/2)`, `e^{-100} ≤ Ks`, the caller's own `XCeilRiderStrict ε g`, and ONE cushion `32·K_vt(KlevF A, Q_m) + 32·(2 log M + log 4 + 50) ≤ (log H₊)/4` on the Siegel-genre constant whose third leg is `SiegelArm`'s EVT minimum of `‖L(s,χ)‖` uniform in `q` — the Siegel-zero obstruction itself, carried by name with the full trace behind it. Enabled by the `∃C_q ∀K` hoist (`RegisterCompose` §1–§2), which lets the design constant `A` be chosen after `C_q`. | Salt/MR/RegisterCompose.lean:345 | 2026-08-03 | `b36f53a` | 3 (Salt/MR/All.lean:7736) |
| `Salt.MR.cofkL_bulk_false_at_socket` | **[THE REGISTER REFUTATION]** The 17-conjunct co-factor register `CofactorBulkL` (the reduction of `v5`'s last predicate) is FALSE at every socket of every terminal regime, for every `T`: its own conjuncts force `24·cSq ≤ gradeCR2 Cb·(log X)^{−ρ₂₉₃}`, a fixed constant above an unbounded function of the scale. The defect is the trivial dilation ladder `D(j) = 1`; the repair is priced at `D ≥ (24·cSq)⁴·(1728·C_q)²·(log X)^{8θ₂₉₃}` (`cofk_dilation_price`), off the register's true law `Rbd ≤ (log X)^{−2θ₂₉₃}/√(1728·C_q)` (`s16cof_exit_decay`). | Salt/MR/RegisterInhabit.lean:260 | 2026-08-03 | `3ec67ba` | 3 (Salt/MR/All.lean:7685) |
| `Salt.MR.logChowla2_ineffective_v6_T0arm` | **[V7-C — ONE OF THE TWO FOUR-RIDER ARMS]** `v6` with the `T₀ ≤ exp(√(flatDesignBase A)/2)` arrow GONE and **four named inner riders** left (`e^{-100} ≤ cs`; `e^{-100} ≤ Ks`; the caller-side scale-request property `XCeilRiderStrict ε g`; the `K_vt` cushion); outer hypotheses none. `T₀` is minted before the design constant and is `A`-independent, so it joins `A`'s `max` as a sixth arm and the tolerance then clears it by three exponential levels; the margin is SHARP in tower height — the fourth level provably fails at EVERY `A ≥ 162`, not only at the design floor (`t0_arm_four_levels_fails`, V7C.lean:121, generalized at `02495bc`). Incomparable with `…_v6_csarm` by construction: each arm discharges a different rider of `v6` and neither implies the other. The mint's scope fences hold verbatim — the tolerance `ε` is opaque and bounded only from below (`1/500 ≤ ε`), the window is `(x/ω, x]` weighted by `1/n`, the shift is `n + 1`, the constants are ineffective, and nothing here bears on twin primes. `v6` is byte-untouched and remains citable. | Salt/MR/V7C.lean:177 | 2026-08-14 | `8b0bd31` | 3 (Salt/MR/All.lean:7821) |
| `Salt.MR.logChowla2_ineffective_v6_csarm` | **[V7-B — THE OTHER FOUR-RIDER ARM]** `v6` with the `e^{-100} ≤ cs` arrow GONE — the floor is DELIVERED as a proven conjunct of the `∃`-prefix, carried up all nine hops from the two leaves that mint the constant (`c_vk = 1/10^8`, `c₀ = 1/10^9`) — and **four named inner riders** left (`T₀ ≤ exp(√(flatDesignBase A)/2)`; `e^{-100} ≤ Ks`; the caller-side scale-request property `XCeilRiderStrict ε g`; the `K_vt` cushion); outer hypotheses none. Incomparable with `…_v6_T0arm` by construction: each arm discharges a different rider of `v6` and neither implies the other. The mint's scope fences hold verbatim — the tolerance `ε` is opaque and bounded only from below (`1/500 ≤ ε`), the window is `(x/ω, x]` weighted by `1/n`, the shift is `n + 1`, the constants are ineffective, and nothing here bears on twin primes. `v6` is byte-untouched and remains citable. | Salt/MR/V7B.lean:1839 | 2026-08-14 | `8b03281` | 3 (Salt/MR/All.lean:7856) |
| `Salt.MR.logChowla2_ineffective_v7` **[THE MINT]** | A machine-checked, witnessed-scale instance of the logarithmically averaged two-point Chowla bound, carrying **three named inner riders** (`e^{-100} ≤ Ks`; the caller-side scale-request property `XCeilRiderStrict ε g`; the Siegel-genre `K_vt` cushion), ineffective, outer hypotheses none — at one opaque tolerance and one produced window. It composes the two arms in one terminal: the `cs` floor arrives DELIVERED in the `∃`-prefix (V7-B) and the `T₀` arrow is discharged inside (V7-C). The scope, in its own bytes: the tolerance `ε` is opaque and bounded only from BELOW (`1/500 ≤ ε` is all that is exported), at one produced `ε` — not at every `ε` and not at any named value; the window is `(x/ω, x]` weighted by `1/n` against `ε · log ω`, a windowed partial sum rather than the full logarithmic average over `n ≤ x`; the shift is `n + 1` (the `2` counts the factors `λ(n)·λ(n+1)`); the design constant is produced by `Classical.choice` and `Ks` carries Siegel's ineffective constant, so no numerical scale is extractable; nothing here bears on twin primes — the transport wall is untouched at this rung. `v6`, `…_v6_csarm` and `…_v6_T0arm` are byte-untouched and remain citable. | Salt/MR/V7E.lean:74 | 2026-08-14 | `8548842` | 3 (Salt/MR/All.lean:7895) |
| `Salt.MR.logChowla2_ineffective_v7_g0` | **[THE MINT AT `g ≡ 0`]** The mint read at the trivial outer-scale request: **two named inner riders** (`e^{-100} ≤ Ks`; the Siegel-genre `K_vt` cushion), ineffective, outer hypotheses none. The scale-request rider is NOT discharged in general — it is VOID at this instance, because a caller who asks for nothing has nothing to prove — and the price is paid in the conclusion: `v7`'s `g R.Hhi R.ω ≤ R.x` conjunct becomes `0 ≤ R.x` and is dropped, so this instance makes no outer-scale demand at all. The `∃`-prefix is `v7`'s verbatim and the mint's scope fences hold unchanged: opaque tolerance bounded only from below (`1/500 ≤ ε`), the window `(x/ω, x]` weighted by `1/n`, the shift `n + 1`, ineffective constants, twins untouched. `logChowla2_ineffective_v7` is byte-untouched and remains the object of record. | Salt/MR/V7E.lean:221 | 2026-08-15 | `82fedba` | 3 (Salt/MR/All.lean:7921) |
| `Salt.Entropy.Chowla.spine_eps_constant_floor` | **[WALL-L2 — THE ε-FLOOR CONSUMPTION FENCE]** `log_chowla_two_budget_head`'s conclusion restated VERBATIM — so a change of shape from a single `ε` to an `∀ ε`-family would stop type-checking here — with the fence adjoined at that same `ε`: for any consumer demand `W` with `W z → 0` (a sieve density at unbounded `z`, or any rate-form saving), the demand `ε ≤ W z` fails from some scale on. The spine head's margin is a CONSTANT floored by construction constants, and this is a fact about the terminal's SHAPE rather than about the strength of its proof; the `MR` mint carries the same shape with `1/500 ≤ ε` in its `∃`-prefix. The fence stops a wave from wiring a constant-`ε` terminal into a slot that needs a rate. No claim about twins, about Chowla, or about the wall is made or implied. | Salt/Entropy/Chowla/SpineEpsFence.lean:102 | 2026-08-15 | `7c82089` | 3 (Salt/Entropy/All.lean:420) |

## 9. Infrastructure firsts

| Theorem (Lean name) | Plain statement (one line) | File:line | Date landed | Commit | Axioms |
|---|---|---|---|---|---|
| `Salt.LS.analytic_LS` | The analytic large sieve: `Σ_r ‖S_N(α_r)‖² ≤ (δ⁻¹ + 13N)·Σ_n ‖aₙ‖²` for `δ`-spaced points. | Salt/LS/AnalyticLS.lean:58 | 2026-07-11 | `4338437` | 3 (blueprint_lint P3) |
| `Salt.LS.arithmetic_LS` | The arithmetic large sieve over the reduced Farey fractions of order `Q`: bound `(Q² + 13N)·Σ‖cₙ‖²`. | Salt/LS/ArithmeticLS.lean:91 | 2026-07-11 | `b5d665e` | 3 (blueprint_lint P3) |
| `Salt.LS.char_LS` | The character-form large sieve over primitive Dirichlet characters. | Salt/LS/CharLS.lean:277 | 2026-07-11 | `1a2ed7e` | 3 (blueprint_lint P3) |
| `Salt.LS.bdh` | **Barban–Davenport–Halberstam** (pure large-sieve Barban form), explicit constant 6000. | Salt/LS/BDH.lean:360 | 2026-07-11 | `7a23770` | 3 (blueprint_lint P3) |
| `Salt.LS.vaughan` | **Vaughan's identity**, exact finite-sum form: `Λ n` as Type-I minus the small box plus the Type-II bilinear term. | Salt/LS/Vaughan.lean:91 | 2026-07-11 | `e3352d2` | 3 (blueprint_lint P3) |
| `Salt.Chen.linear_sieve_upper_chain` | **The Rosser–Iwaniec linear sieve**, upper side (BJS Theorem 6 (5)), chain form — first in a proof assistant. | Salt/Chen/LinearSieve.lean:377 | 2026-07-12 | `cf99c94` | 3 (Salt/Chen/All.lean:193) |
| `Salt.Chen.linear_sieve_lower_chain` | The Rosser–Iwaniec linear sieve, lower side (BJS Theorem 6 (6)), chain form. | Salt/Chen/LinearSieve.lean:389 | 2026-07-12 | `cf99c94` | 3 (Salt/Chen/All.lean:193) |
| `Salt.Mertens.mertens_second_sharp` | The sharp Mertens second theorem: `\|Σ_{p≤n} 1/p − (loglog n + M)\| ≤ 12/log n` for all `n ≥ 2`. | Salt/Mertens/Second.lean:216 | 2026-07-17 | `1c30efe` | 3 (Salt/Mertens/All.lean:25) |
| `Salt.Weil.norm_kloosterman_le_two_sqrt` | **The Weil bound** for Kloosterman sums: `‖S(a,b;p)‖ ≤ 2√p` for odd `p` and `a, b ≠ 0`. | Salt/Weil/Descent.lean:206 | 2026-07-17 | `5c9d9cf` | 3 (Salt/Weil/All.lean:39) |
| `Keller.keller_not_injective` [tier-2] | `Fmap : ℚ³ → ℚ³` is not injective (two distinct rational points with the same image). | Salt/Keller/Counterexample.lean:142 | 2026-07-21 | `a25042b` | 3 (Salt/Keller/All.lean:24) |
| `Keller.jacobian_conjecture_counterexample` | **The Alpöge counterexample to the Jacobian conjecture** (Thm 3.1) verified: `J.det = C(−2)` and `F` is not injective on `ℚ³`. | Salt/Keller/Counterexample.lean:159 | 2026-07-21 | `a25042b` | 3 (Salt/Keller/All.lean:24) |
| `Salt.HB.fl_dim4_lower` / `fl_dim4_upper` | The fundamental lemma at sieve dimension 4 (block-Brun): main-term defect ≤ flConst·e^{−flRate·s}, both sides — the first FL at dimension > 1 in any public artifact as of 2026-08-11 (see the priority survey). | Salt/HB/RosserDim4FL.lean:364 | 2026-08-03 | `8c62a10` | 3 axioms (audited) |
| `Salt.HB.hbSieve_fl_sandwich` | N5's exit: the dimension-4 Rosser-sieve service layer at Heath-Brown's sifted object — sandwich (2.2) PROVED (not axiom-assumed), W(z)+correction identification, the ρ₂/ρ₃ transfer; one carried analytic field (Λ* ≥ 0). | Salt/HB/RosserDim4Instance.lean:564 | 2026-08-03 | `5b2b87a` | 3 axioms (audited) |

---

## Standing chores

- ~~Close the eight `⚠ unaudited` rows~~ **DONE 2026-08-02 night** — all eight added to their track ledgers (Salt/Entropy/All.lean's AUDIT-ROWS block; Salt/Maynard/All.lean's first-ever audit block), build exit 0, every one at 3 axioms.
  - **Re-verified 2026-08-15**, and the finding behind the chore is retired at
    `docs/blueprints/flags.md` (⟦CLOSED 08/15 at the sitting — STALE-ON-ARRIVAL⟧,
    inside the 08/02 RESULTS-registry entry): the ledger rows are at
    `Salt/Entropy/All.lean:381-396`, `Salt/Maynard/All.lean:106-108` and
    `Salt/MR/All.lean:1433-1435`, all twelve declarations re-audited on those
    bytes at `[propext, Classical.choice, Quot.sound]` (`saltbuild EXIT=0`,
    `HEAD=82fedba`). No row in this file carries `⚠ unaudited` today.
- **`Salt.SW.dh_repulsion_ordered` has a namesake in a doc comment** at
  `Salt/SW/DHRepulsion.lean:267` (the frozen target contract, inside a fenced
  block). The live declaration is the TBalR8 one in this table.
- **Superseded rows**: none yet. When the HB engine discharges
  `fulcrum_dichotomy`'s `hEngine` slot unconditionally, mark the conditional
  row `[SUPERSEDED → <name>]` in place rather than editing it.
