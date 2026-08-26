/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Defs
import Salt.TwinBar.LogWeight
import Salt.TwinBar.SliceCS
import Salt.TwinBar.Tonelli
import Salt.TwinBar.Impossibility
import Salt.TwinBar.Witness
import Salt.TwinBar.RationalTie
import Salt.TwinBar.Enlarged
import Salt.TwinBar.ThreeBar
import Salt.TwinBar.Constrained
import Salt.TwinBar.ThreeBarAsm
import Salt.TwinBar.FourBar
import Salt.TwinBar.SimplexS
import Salt.TwinBar.Simplex4
import Salt.TwinBar.Simplex4Inner
import Salt.TwinBar.FourBarAsm
import Salt.TwinBar.LeastK
import Salt.TwinBar.TwinDoor
import Salt.TwinBar.LambdaRate
import Salt.TwinBar.ParityWall
import Salt.TwinBar.Wall
import Salt.TwinBar.WallUnconditional
import Salt.TwinBar.WallCorr
import Salt.TwinBar.SiegelTwin
import Salt.TwinBar.SiegelCorr
import Salt.TwinBar.SiegelCorrStrong
import Salt.TwinBar.TwistedSieve
import Salt.TwinBar.Separation
import Salt.TwinBar.TwinParitySieve
import Salt.Tactic.AuditAxioms

/-!
# The twin-bar rung (`twinbar`) — aggregate import

Design: `docs/blueprints/twinbar.md`. The flagship NEGATIVE result: for the twin
tuple `{0, 2}` (`k = 2`) the unmodified Maynard–Selberg variational gate
`θ·(J₁+J₂) > 2·I₂` is unsatisfiable by ANY continuous weight at ANY level of
distribution `θ ≤ 1`, because `J₁ F + J₂ F ≤ 2·log 2·I₂ F` with `2·log 2 < 2`
(Polymath8b arXiv:1407.4897, Lemma 6.1 + Cor. 6.4 at `k = 2`). Wired into
`Salt.lean` from the first commit; extended as the analytic nodes (T2–T6) land.

**The honesty contract (read before quoting the theorem).** The headliners H1/H2
(`twin_bar`, `twin_gate_fails`) and the impossibility H3 (`no_twin_weight`)
certify the exact boundary of the UNMODIFIED Maynard class: no continuous weight
`F`, at no equidistribution level `θ ≤ 1`, can push the Selberg functional past
the twin gate. This is the negative dual of the landed `M5_cert` (what the method
CAN do at `k = 5`, gaps ≤ 12). It does NOT claim "sieves cannot prove twin
primes": parity-breaking inputs — bilinear / type-II information à la
Friedlander–Iwaniec, Chen's switching — modify the functional, and a modified
functional is outside the scope of this bound. The Lean theorems are per-`F`
bounds over CONTINUOUS `F`; the standard density bridge to Polymath8b's L²-sup
`M₂` (eq. 33) is noted as a possible later strengthening, not part of the floor.

## Landed (node T1 — carriers + trivia)

`Defs`: the four Fable-frozen carriers `I₂`, `J₁`, `J₂`, `R₂`; nonnegativity of
the quadratic carriers (`I₂_nonneg`, `J₁_nonneg`, `J₂_nonneg`); the Cauchy–Schwarz
weights `w₁`, `w₂` with the magic identity `w₁ + w₂ ≡ 2` plus their `[0,2]` bounds
and continuity; and the `ContinuousOn (uncurry F) R₂ ⇒ IntervalIntegrable` slice
plumbing in both simplex directions (`slice₁_*`, `slice₂_*`: continuity, plain,
square, and weighted-square integrability) that T3/T4 consume.
-/

-- Build-time axiom audit: a stray axiom in the twinbar track fails `lake build`
-- here, not only at out-of-band lint time.
open Salt.Tactic in
#audit_axioms Salt.TwinBar.Sep.wall_of_indistinguishable
  Salt.TwinBar.Sep.no_readable_certificate_via_master
  Salt.TwinBar.Sep.parity_wall_via_master
  Salt.TwinBar.Sep.input_breaks_wall
  Salt.TwinBar.lamChi_mult Salt.TwinBar.abs_lamChi_le_tau
  Salt.TwinBar.twistedErrSum_le_tauRemainder Salt.TwinBar.twistedMainSum_euler
  Salt.TwinBar.siegel_correlation_strong
  Salt.TwinBar.boxEntry_reduces
  Salt.TwinBar.siegelSequence_implies_infinitely
  Salt.TwinBar.corrWindow_box Salt.TwinBar.residue_lower
  Salt.TwinBar.siegel_correlation_dichotomy
  Salt.TwinBar.infinitely_iff_not_noSiegel
  Salt.TwinBar.noSiegelZeros_iff_not_infinitely
  Salt.TwinBar.heathBrown_iff_dichotomy Salt.TwinBar.badHyp_false
  Salt.TwinBar.parity_wall_unconditional
  Salt.TwinBar.no_parity_beating_certificate_unconditional
  Salt.TwinBar.I₂_nonneg Salt.TwinBar.J₁_nonneg Salt.TwinBar.J₂_nonneg
  Salt.TwinBar.w₁_add_w₂ Salt.TwinBar.w₁_nonneg Salt.TwinBar.w₂_nonneg
  Salt.TwinBar.w₁_le_two Salt.TwinBar.w₂_le_two
  Salt.TwinBar.w₁_continuous Salt.TwinBar.w₂_continuous
  Salt.TwinBar.slice₁_continuousOn Salt.TwinBar.slice₂_continuousOn
  Salt.TwinBar.slice₁_intervalIntegrable Salt.TwinBar.slice₂_intervalIntegrable
  Salt.TwinBar.slice₁_sq_intervalIntegrable Salt.TwinBar.slice₂_sq_intervalIntegrable
  Salt.TwinBar.slice₁_weight_sq_intervalIntegrable
  Salt.TwinBar.slice₂_weight_sq_intervalIntegrable
  Salt.TwinBar.interval_CS Salt.TwinBar.sliceCS₁ Salt.TwinBar.sliceCS₂
  Salt.TwinBar.logWeight Salt.TwinBar.simplex_swap
  Salt.TwinBar.twin_bar Salt.TwinBar.twin_gate_fails Salt.TwinBar.no_twin_weight
  Salt.TwinBar.twin_witness Salt.TwinBar.M₂_squeeze
  Salt.TwinBar.twin_bar_asymmetric Salt.TwinBar.twin_bar_signed
  Salt.TwinBar.twin_bar_enlarged Salt.TwinBar.no_twin_weight_enlarged
  Salt.TwinBar.twin_bar_constrained Salt.TwinBar.no_twin_weight_constrained
  Salt.TwinBar.cs_bound_ignores_constraint Salt.TwinBar.admissible_witness
  Salt.TwinBar.three_bar Salt.TwinBar.no_triple_weight Salt.TwinBar.tripleBar_holds
  Salt.TwinBar.log_slice_CS Salt.TwinBar.w_sum_three
  Salt.TwinBar.three_halves_log_three_lt_two Salt.TwinBar.no_triple_weight_of_tripleBar
  Salt.TwinBar.two_fifths_below_threshold
  Salt.TwinBar.dirichlet₂ Salt.TwinBar.no_twin_certificate
  Salt.TwinBar.twin_certificate_example Salt.TwinBar.bridge_consistency
  Salt.TwinBar.siftedSum_sPlus Salt.TwinBar.siftedSum_sMinus
  Salt.TwinBar.lambda_mult_sum Salt.TwinBar.sPlus_rem_bound
  Salt.TwinBar.sMinus_rem_bound Salt.TwinBar.sieveAgree_pair
  Salt.TwinBar.I₄_nonneg Salt.TwinBar.J₁₄_nonneg Salt.TwinBar.J₂₄_nonneg
  Salt.TwinBar.J₃₄_nonneg Salt.TwinBar.J₄₄_nonneg
  Salt.TwinBar.w_sum_four Salt.TwinBar.logWeight_third
  Salt.TwinBar.log_slice_CS_third
  Salt.TwinBar.sliceCS₁₄ Salt.TwinBar.sliceCS₂₄
  Salt.TwinBar.sliceCS₃₄ Salt.TwinBar.sliceCS₄₄
  Salt.TwinBar.four_thirds_log_four_lt_two
  Salt.TwinBar.no_quad_weight_of_fourBar
  Salt.TwinBar.liouville_eq_chiSq_mul_moebius Salt.TwinBar.Mlambda_eq_sum_Mmu
  Salt.TwinBar.Mmu_abs_le Salt.TwinBar.Mlambda_rate
  Salt.TwinBar.LambdaSummatory_of_MmuRate
  Salt.TwinBar.lambdaSummatory_holds
  Salt.TwinBar.rosser_floor_undershoot Salt.TwinBar.rosser_floor_vs_prime_mass
  Salt.TwinBar.parity_wall Salt.TwinBar.parity_wall_effective
  Salt.TwinBar.no_parity_beating_certificate
  Salt.TwinBar.phiLowerR_tolerant Salt.TwinBar.phiLowerR_certificate
  Salt.TwinBar.rosserRemainder_sPlus_le Salt.TwinBar.rosserRemainder_sMinus_le
  Salt.TwinBar.witness_rosserRemainder_le Salt.TwinBar.sum_inv_Icc_le
  Salt.TwinBar.canonical_eq_region₃ Salt.TwinBar.w3order_eq_region₃
  Salt.TwinBar.psi_eq₃ Salt.TwinBar.region_integrable₃
  Salt.TwinBar.outer_marg₃_fst Salt.TwinBar.outer_marg₃_lst
  Salt.TwinBar.slice_fix_fst₃ Salt.TwinBar.slice_fix₄_fst
  Salt.TwinBar.slice_fix₄_snd Salt.TwinBar.Δ₃_one_eq_R₃
  Salt.TwinBar.Δ₃_isClosed Salt.TwinBar.Δ₃_isCompact
  Salt.TwinBar.Δ₃_measurableSet
  Salt.TwinBar.Δ₄_isClosed Salt.TwinBar.Δ₄_isCompact
  Salt.TwinBar.Δ₄_measurableSet Salt.TwinBar.Δ₄_eq_R₄
  Salt.TwinBar.psi₄ Salt.TwinBar.region_integrable₄
  Salt.TwinBar.outer_marg₄_fst Salt.TwinBar.outer_marg₄_swap
  Salt.TwinBar.j4order_eq_region Salt.TwinBar.j3order_eq_region
  Salt.TwinBar.psi_eq₄ Salt.TwinBar.reduce3_canonical_int
  Salt.TwinBar.outer_marg₃_lst_int Salt.TwinBar.canonical4_eq_region
  Salt.TwinBar.outer_marg₄_lst Salt.TwinBar.j2order_eq_region
  Salt.TwinBar.outer_marg₄_lst_swap
  Salt.TwinBar.J₁₄_bound Salt.TwinBar.J₂₄_bound
  Salt.TwinBar.J₃₄_bound Salt.TwinBar.J₄₄_bound
  Salt.TwinBar.four_bar Salt.TwinBar.fourBar_holds
  Salt.TwinBar.no_quad_weight
  Salt.TwinBar.maynard_closed_at_two Salt.TwinBar.maynard_closed_at_three
  Salt.TwinBar.maynard_closed_at_four Salt.TwinBar.maynard_open_at_five
  Salt.TwinBar.least_k_theorem
  Salt.TwinBar.twinC2_pos Salt.TwinBar.twinC2_multipliable
  Salt.TwinBar.twinB_min_implies_twins Salt.TwinBar.twin_survivor_of_pos
  Salt.TwinBar.twinTypeII_eventually_pos Salt.TwinBar.wall_or_door

/-! ⟦WALL-L2 — THE WALL AT CORRELATION GRANULARITY⟧ (`WallCorr`, 2026-08-15).

The landed wall caps certificates tolerant with respect to `SieveAgree` (the three
main-term fields plus a shared Rosser budget).  `WallCorr` WIDENS that interface by
the shift-2 correlation field `corr₂ s = ∑_{n ∈ s.support} s.weights n · s.weights
(n+2)` and shows the cap survives: since `SieveAgreeCorr → SieveAgree`, tolerance
with respect to the widened relation is a strictly WEAKER hypothesis on `Φ`, and
`parity_wall_corr_stable` still delivers `parity_wall_unconditional`'s bound at
`s₋ x`.

The content is the core identity `corr2_witness_diff_Mlambda`: at the Selberg witness
pair the `λλ` cross-term CANCELS — `(1 ± λ(n))(1 ± λ(n+2))` carries it with the same
sign in both witnesses — leaving the one-point gap `2·(M_λ(x) + M_λ(x+2))`, which
`corr2_witness_budget` puts at `O(x/(log x)^A)` unconditionally through the landed
`Salt.SW.mmuRate_holds`.  So the witness pair really does agree in the widened field,
at a sublinear budget: the strengthening is met, not evaded.

Scope: a NEGATIVE theorem strengthened at the real witnesses.  No lower bound, no
positive rung, nothing about twin primes — and nothing here escapes, crosses or
evades the wall. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.corr2_witness_diff
  Salt.TwinBar.corr2_witness_diff_Mlambda
  Salt.TwinBar.corr2_witness_budget
  Salt.TwinBar.phiLowerR_tolerant_corr
  Salt.TwinBar.parity_wall_corr
  Salt.TwinBar.parity_wall_corr_stable

/-! ⟦λ-BV WAVE 1 — B0⟧ (`TwinParitySieve`, 2026-08-20).

`twinParitySieve N P hP` is the landed twin `BoundingSieve` of `Salt/Brun/Sieve.lean`
with ONE field changed: the weights carry the parity pin `w(m) = 1 − λ(m)`.  Support,
modulus and the twin density `ν = ρ/·` are unchanged — the three ν obligations reuse the
`Salt.TwinSieve` proof terms verbatim — so every main-term object that reads only
`prodPrimes` and `nu` is definitionally the landed one, which is what the `rfl` simp
lemmas `twinParitySieve_prodPrimes` / `twinParitySieve_nu` exist to expose.

`totalMass` is pinned to the SUM FORM `∑ m ∈ support, weights m` rather than a closed
form (F-THIRD-REGIME): `twinParitySieve_totalMass` then READS it as
`N − ∑_{n ∈ [1,N]} λ(n(n+2))` through the `Finset.sum_image` injection idiom.  With the
`sMinus` idiom (`totalMass := N`) the `d = 1` atom would degenerate to two-point Chowla.

Scope: a DEFINITION plus three readings of it.  Nothing here bounds, signs or estimates
the Liouville sum — no arithmetic input is claimed, and none is used. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.twinParitySieve
  Salt.TwinBar.twinParitySieve_prodPrimes
  Salt.TwinBar.twinParitySieve_nu
  Salt.TwinBar.twinParitySieve_totalMass

/-! ⟦λ-BV WAVE 1 — B1⟧ (`TwinParitySieve`, 2026-08-20).

`L N d` is the Liouville sum over the twin values `n(n+2)`, `n ∈ [1,N]`, that `d` divides.
`rem_split` reads the twisted sieve's remainder as the LANDED twin remainder
`_root_.rem d N` (M2.lean:236) minus the Liouville discrepancy `L N d − ν(d)·L N 1` — for
EVERY `d`, with no side condition.  The `d = 0` atom is not a special case: `ν 0 = 0`,
`L N 0 = 0` and `rem 0 N = 0`, and the proof's final `ring` closes uniformly because
`(d : ℝ)⁻¹` is an atom to it.  `twinParitySieve_multSum` and `L_one` are its two readings.

`LiouvilleTwinDisp N P lvl B` NAMES the arithmetic input — the discrepancy summed over
`d ∣ P` below the level, bounded by `B`.  Its shape is `Salt.Chen.rosserRemainder`'s
verbatim (`ite` over the FULL divisor index, never a `filter`) so that the assembly pairs
the two sums term-by-term under `Finset.sum_le_sum`.

Scope: ONE identity and TWO definitions.  Nothing here asserts that any `B` is small — no
Chowla-type input is claimed, none is proved, and none is used.  `LiouvilleTwinDisp` is a
hypothesis-shaped `Prop`, unpopulated in wave 1. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.L
  Salt.TwinBar.L_one
  Salt.TwinBar.twinParitySieve_multSum
  Salt.TwinBar.rem_split
  Salt.TwinBar.LiouvilleTwinDisp

/-! ⟦λ-BV WAVE 1 — B2⟧ (`TwinParitySieve`, 2026-08-20).

The ten hypotheses of `Salt.Chen.brun_lower_ell1` (BrunEll1.lean:191), discharged at
`twinParitySieve` at the primary operating point `b = 1`, `λ = 1/4`,
`Λ = LamTwin (1/4) z`, `κ = 2λ`.

`htotalMass` is the pointwise-trivial one: every weight `1 − λ(m)` is nonnegative because
`λ(m) ≤ 1` (`liouville_real_le`, ParityWall.lean:98) — no sign, no size and no
cancellation is claimed for any Liouville sum (F-THIRD-REGIME).  `hMert` is the landed
`hMert_twinSieve` (MertensDischarge.lean:660) after a bare `change` — defeq only, the
brief's `exact`-after-`show` with `show` swapped out for the linter: `Wratio` reads only
`prodPrimes` and `nu`, and `twinParitySieve` shares both DEFINITIONALLY with the landed
twin sieve, so the ν(2)/ν(p) obligations are already discharged there.  `h12` is
`Salt.HB.lam_exp_lt_one` (RosserDim4.lean:740), `hLam` is `Salt.BrunLower.LamTwin_pos`
(MertensDischarge.lean:124), `hkappa` is `le_rfl`, `hb`/`hlam` are `norm_num`.

`hQ`, `hz`, `hzprimes` remain PARAMETERS, `hz` in the NAMED `zThresh (1/4) ≤ z` form
(= `loglog z ≥ 400`, what `hMert` consumes); `one_lt_of_zThresh` is the step down to the
door's own `1 < z`.  The cut keeps its ℕ-truncated-subtraction shape, reduced at `b = 1`
by `omega` (F-LEVEL), and stays symbolic in `Q` — no numeral is pinned.

Scope: a DOOR.  `siftedSum` is bounded BELOW by a main term minus `rosserRemainder`;
nothing here bounds that remainder, and nothing here claims anything about twin primes. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.twinParitySieve_totalMass_nonneg
  Salt.TwinBar.one_lt_of_zThresh
  Salt.TwinBar.twinParitySieve_hMert
  Salt.TwinBar.twinParitySieve_brun_lower_ell1

/-! ⟦λ-BV WAVE 1 — B3⟧ (`TwinParitySieve`, 2026-08-20).

The remainder majorant and the assembly.  `Btwin lvl = ⌊lvl⌋₊·(1 + log ⌊lvl⌋₊)` is the
EXPLICIT, unconditional bound for the untwisted half of `rem_split`: `twinRem_sum_le` runs
`rem_abs_le` (M2.lean:241, `|rem d| ≤ ρ(d)`) → `rho_squarefree_le` (M2.lean:206, `ρ ≤ 2^ω`
on the squarefree `d ∣ P`) → the M5Assembly.lean:209-239 re-index (`Finset.sum_filter`, then
`Finset.sum_le_sum_of_subset_of_nonneg` onto `Finset.Icc 1 ⌊lvl⌋₊`) → `sum_two_pow_omega_le`
(GehPp2.lean:113 — a ROOT-level declaration; that file carries no `namespace`).  The `3^ω`
constant of the landed idiom is replaced by `2^ω`, and its N4.2 `y⁴` step (M5Assembly.lean:240)
is NOT used.

`twinParitySieve_rosserRemainder_le` is the assembly `rosserRemainder ≤ Btwin lvl + B`: the
landed `rem_split` (TwinParitySieve.lean:131) plus the triangle inequality, term-by-term under
`Finset.sum_le_sum` — the pairing works because B1 gave `LiouvilleTwinDisp`
`rosserRemainder`'s shape verbatim (an `ite` over the FULL divisor index, never a `filter`).
The idiom is `goldBVSum_le_split` (A1.lean:286, body from :293); the second landed instance is
`switchSieve_rosserRemainder_split_le` (SwitchBV.lean:316, body from :321).

Scope: a DOOR still.  `Btwin` is explicit and unconditional; `B` is a PARAMETER, and wave 1
asserts nothing about its size.  No Liouville sum is signed, sized or cancelled anywhere in
this stanza, and nothing here is a twin-prime claim. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.Btwin
  Salt.TwinBar.twinRem_sum_le
  Salt.TwinBar.twinParitySieve_rosserRemainder_le

/-! ⟦λ-BV WAVE 1 — B4⟧ (`TwinParitySieve`, 2026-08-20).

The terminal, and the interface nobody had proved.  `one_le_ell1_level` is the DANGLING
INTERFACE between wave 1's two green halves — a gap no build reports: B3's consumer
`twinParitySieve_rosserRemainder_le` (TwinParitySieve.lean:292) demands `1 ≤ lvl`, B2's
producer `twinParitySieve_brun_lower_ell1` (:206) carries the level
`Q · (exp((1 + 2(exp Λ − 1)⁻¹)·log z) · 2^(2r−1))`, and nothing in the tree supplied
`1 ≤` that product.  All three factors are `≥ 1` separately, so no size input is needed
and `minLevel_mem` (BrunLower/Defs.lean:114) is NOT consumed — `2 ^ k ≥ 1` holds for every
`k : ℕ`, ℕ-truncation included.  `Q` is `hQ`; the exponent is nonnegative because
`LamTwin_pos` (MertensDischarge.lean:124) makes `(exp Λ − 1)⁻¹ > 0` and `one_lt_of_zThresh`
(TwinParitySieve.lean:164) makes `Real.log z ≥ 0`.

`twin_parity_survivor_or_chowla_of_liouvilleTwinDisp` is then `le_or_gt` on `siftedSum` and
`linarith`: B2's `mainTerm − rosserRemainder ≤ siftedSum` against B3's
`rosserRemainder ≤ Btwin + B`, at one and the same level.  The level stays in the RAW
ℕ-truncated form the door carries — no ℝ restatement of the exponent, no numeral pinned.

Scope: `B` is a PARAMETER.  Wave 1 asserts NOTHING about the size of the arithmetic input,
so NEITHER disjunct is a twin-prime claim.  The right disjunct is the survivor branch —
`0 < siftedSum` with weights `1 − λ` and support `∋ m ≥ 3` yields a sifted `m` with `Ω(m)`
odd — but that Chowla-conversion lemma is NAMED, not built in wave 1. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.one_le_ell1_level
  Salt.TwinBar.twin_parity_survivor_or_chowla_of_liouvilleTwinDisp

/-! ### The QUANTITATIVE pre-terminal — the wave-2 §7 extraction repair (2026-08-26, math)

The terminal above ends `rcases le_or_gt siftedSum 0` and returns `Or.inr hs` on the survivor
branch, so **the size is discarded**.  The λ-BV wave-2 §3 refuter pass
(`seat/briefs/2026-08-21-w2-0-design-block-DRAFT.md` §7, verdict 4) named that as an extraction
repair to *"adopt in any consumer"*.

⭐ **It is ROUTE-INDEPENDENT, which is why it lands even though the wave it was found in died.**
The same §7 killed wave-2's §3 log-collapse (*"no wave tables from §3"*: the ε-arithmetic is fatal
at the forced operating point, the sieve route is strictly dominated, and the prize was
overstated).  This repair survived all three verdicts because it is a statement about the LANDED
ℓ¹ chain and says nothing about the log-rebase.  ⇒ *A refuted design block is not an empty one —
its verdict section can carry findings that outlive the route.*

`…_lower_of_liouvilleTwinDisp` composes the three landed pieces (`:206` door + `:292` ℓ¹ split +
`:323` level) with no `le_or_gt`: `mainTerm − (Btwin lvl + B) ≤ siftedSum`.  The terminal follows
from it in two lines, so nothing is lost; the MARGIN is gained, and a consumer that only learns
`0 < siftedSum` cannot tell a survivor count of `1` from one of `N/log N`.
`…_pos_of_margin` is the interface form: the survivor branch DIRECTLY, gated on the single
explicit inequality `Btwin lvl + B < mainTerm`, rather than a disjunct the consumer must
eliminate.  *The two are equivalent as THEOREMS and not as INTERFACES; the verdict was about the
interface.*

⛔ **Scope is unchanged from wave 1 and must not be read up.**  `B` is still a PARAMETER, the
margin is still a HYPOTHESIS nothing here supplies, and **neither name is a twin-prime claim nor
produces a survivor.** -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.twinParitySieve_siftedSum_lower_of_liouvilleTwinDisp
  Salt.TwinBar.twinParitySieve_siftedSum_pos_of_margin
