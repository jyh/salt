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

/-! ### The `d = 1` ladder row vanishes — wave-2 §7 verdict 4, second extraction repair

`LiouvilleTwinDisp` sums `|L N d − ν(d)·L N 1|` over `P.divisors`.  **Its `d = 1` row is
IDENTICALLY ZERO** (`ν(1) = 1`, so the row is `|L N 1 − L N 1|`), and `liouvilleTwinDisp_iff_erase_one`
restates the whole predicate on `P.divisors.erase 1` — an EQUALITY, not a weakening.

⭐ **Why the refuters flagged it:** a reader pricing the supply ladder row-by-row looks at `d = 1`,
sees the full Liouville sum `L N 1`, and prices the two-point correlation THERE.  That row costs
nothing; the correlation is paid in the `ν(d)·L N 1` TAIL of every OTHER row.  ⇒ *A row that
MENTIONS the hard object is not a row that DEMANDS it.*

Route-independent, like the quantitative pre-terminal above: a statement about the LANDED
`LiouvilleTwinDisp`, which survived the verdicts that killed §3's log-rebase. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.nu_one
  Salt.TwinBar.twinDisp_row_one
  Salt.TwinBar.liouvilleTwinDisp_sum_erase_one
  Salt.TwinBar.liouvilleTwinDisp_iff_erase_one

/-! ### The log-weight comparison — wave-2 §7 verdict 4's *"unnamed B node"*

The log-rebase writes each divisor atom over an affine form `n = d·m + r`, `1 ≤ r ≤ d`, so the log
world's natural weight `1/n` becomes `1/(d·m + r)` while the atom is indexed by `m` and wants
`1/m`.  **The two agree to a factor of exactly 2, uniform in `d`, `m`, `r`:**
`d·m ≤ d·m + r ≤ d·(m+1) ≤ 2·d·m`, the last step being `m + 1 ≤ 2m`.

`…_le_div` is the same fact in the `1/m` normalisation — the affine weight is `(1/d)·(1/m)` up to
2, with both constants explicit.  ⭐ That is what makes the log-rebase's per-atom bookkeeping a
CONSTANT rather than a schedule: the `d`-dependence is exactly the `1/d` the divisor sum already
carries, and the leftover is bounded by 2 uniformly.

⛔ **Both hypotheses are load-bearing:** `r ≤ d` bounds the offset by one stride (without it no
constant exists), and `1 ≤ m` is what turns `m + 1` into `2m`.  The residue-class decomposition
supplies both.
⛔ **SCOPE — an INGREDIENT, not a wiring.** Pure arithmetic on the weights: it names no Liouville
sum, no atom and no consumer, and **nothing in the corpus consumes it yet.** -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.logWeight_affine_le
  Salt.TwinBar.logWeight_affine_le_div

/-! ### The tail-mass infinitude step — wave-2 §7 verdict 4's last extraction repair

§7 records it as *"infinitude via the tail-mass argument (genuinely EASIER in the log world — the
one argument FOR the rebase nobody made)"*.  **A nonnegative weight whose partial sums are
unbounded cannot be supported on a finite set.**

⭐ **Why it is the argument FOR the rebase.**  `0 < siftedSum` at each `N` gives a survivor `≤ N`
per `N` and **does NOT give infinitely many** — the witnesses could all be the same `n`.  What
upgrades one-per-`N` to infinitude is that a FIXED finite set carries only BOUNDED weight, so an
unbounded mass cannot live on finitely many terms.  In the log world the mass grows like `log N`
**unconditionally** (the subtracted two-point sum is Tao's own theorem) — exactly the divergence
this step consumes.  ⇒ *The rebase does not make this lemma easier; it makes its HYPOTHESIS
available.*

`…_of_lower_unbounded` is the shape a positivity chain actually hands over: a divergent lower bound
`f N ≤ ∑_{n<N} w n` rather than raw unboundedness.

⛔ **SCOPE — the abstract step ONLY.** It takes the divergence as a hypothesis, supplies nothing
toward it, **produces no survivor, and nothing in the corpus consumes it yet.** -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.support_infinite_of_partialSums_unbounded
  Salt.TwinBar.support_infinite_of_lower_unbounded

/-! ### The harmonic-progression count — wave-2 §3(3)'s "NEW small node", §7-verified

§3 named it (*"the log-count error per class of the harmonic progression sum is O(1)"*) and §7's
refuter pass **UPHELD it with an absolute `C₀ = 1, derived`** — one of only two §3 claims the pass
sustained. **The collapse ARGUMENT around it died; the ESTIMATE did not.**

`sum_inv_affine_le` sums the pointwise weight comparison over `m ∈ [1,M]` and composes with the
landed `sum_inv_Icc_le` (`Wall.lean:219`, `∑_{m≤M} 1/m ≤ 1 + log M`) to give
`∑ 1/(d·m+r) ≤ (1/d)·(1 + log M)` — **the constant is 1, absolute, and it is the landed harmonic
bound's, not a new estimate.** `sum_inv_affine_ge` is the other side at the factor 2 the comparison
costs.

⭐ **Both bounds carry `1/d` and nothing else `d`-dependent, uniformly in the residue `r`** — the
modulus enters exactly as the factor the divisor sum already carries. That is the content.

⛔ **SCOPE: estimates on the WEIGHTS.** They name no Liouville sum and no atom, and **nothing
consumes them yet** — the log-rebase they serve is design-tier and its §3 route is refuted. They
land because the estimate is **route-independent**: any log-world pricing of an affine-form atom
needs exactly this, and the refuters had already checked the constant. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_inv_affine_le
  Salt.TwinBar.sum_inv_affine_ge

/-! ### The twin-value Möbius unfolding — the DIRECT route's skeleton

§7's verdict 2 ruled wave-1's sieve chain **strictly dominated**: *"at fixed z the sifted log-mass
is a finite Möbius sum over the SAME atoms — no BoundingSieve, no door, no `Btwin`"*, and *"if
Tao-1.2-in-Lean ever lands, the DIRECT MÖBIUS route is the consumer."* This is that route's
bookkeeping, EXACT (an identity, not a sieve bound):

    `∑_{n ≤ N, (n(n+2),P)=1} w n = ∑_{d ∣ P} μ(d) · ∑_{n ≤ N, d ∣ n(n+2)} w n`

⛔ **Why the landed stone does not serve.** `Salt.SW.sum_coprime_eq_moebius_multiples`
(`SW/CoprimeBV.lean:98`) is the same classical unfolding but sifts the **INDEX**, reindexing inner
sums by `d = k·e`. Here the condition is on the **VALUE** `n(n+2)`, and that reindex does not
transport. *Same identity, different variable, and the difference is exactly the step that fails.*
The pointwise Möbius collapse DOES transport and is reused from
`Salt.SW.sum_divisors_moebius_real`, not re-derived.

⭐ The right-hand inner sums are precisely what `L` / `LiouvilleTwinDisp` already index — which is
what makes this the route's SKELETON rather than a new decomposition.

⛔ **SCOPE: bookkeeping. It does not advance the prize** — it removes the only non-Tao Lean
prerequisite §7 named. The ATOMS on its right are the open object (Tao Thm 1.2, Captain-gated).
⚠️ **Nothing consumes it yet, so on today's own dead-branch census it reads as a dead branch until
an atom supplier arrives.** Recorded so that reading is not a surprise. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_twinCoprime_eq_moebius_divisors

/-! ### Every `d ≥ 2` atom carries TWO objects at TWO strengths — verdict 4's LAST entry

§7's verdict 4 closes with *"the `d = 1` ladder row is IDENTICALLY ZERO … every `d ≥ 2` atom
carries TWO objects at TWO strengths"*. The first half is `twinDisp_row_one`; this is the second,
and it is the entry I had first glossed as an observation rather than a node.

The row `|L N d − ν(d)·L N 1|` names **two different Liouville sums** — the `d`-restricted
`L N d`, supplied by a correlation estimate at stride `d`, and the FULL `L N 1`, supplied by the
stride-1 estimate. Different objects, **different strengths**. The triangle inequality prices the
row as two INDEPENDENT demands, and `liouvilleTwinDisp_of_two_objects` lifts that to the whole
discrepancy input.

⭐ **An interface fact, not an estimate.** Without it a reader prices each row as a demand on a
DIFFERENCE — strictly harder than the conjunction of two bounds, and it needlessly couples the two
strengths.
⛔ **SUFFICIENT, not equivalent:** the split DISCARDS the cancellation between `L N d` and
`ν(d)·L N 1` that the difference form retains. A supplier that CAN exploit that cancellation should
use `LiouvilleTwinDisp` directly; this exists so that one which cannot is not blocked.
⚠️ Nothing consumes it yet — it reads as a dead branch on item 12c's census until a supplier
arrives. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.nu_nonneg
  Salt.TwinBar.twinDisp_row_le_two_objects
  Salt.TwinBar.liouvilleTwinDisp_of_two_objects

/-! ### The log-world twin mass, split — the Tao boundary as an equation

§3(1) writes the log-rebased mass as `Σ_{n≤N}(1 − λ(n)λ(n+2))/n = H_N − Σ λ(n)λ(n+2)/n` and notes
the subtracted sum is **Tao's own theorem** (1509.05422, forms `(1,0),(1,2)`, det `2 ≠ 0`). **§7
killed the COLLAPSE ARGUMENT built on that, not the DECOMPOSITION** — so what lands here is the
decomposition alone, with no asymptotics and no claim about either piece:

* `liouville_twinProd_mul` — `λ(n(n+2)) = λ(n)·λ(n+2)`, complete multiplicativity. **This is the
  step that turns the corpus's twin-VALUE spelling into Tao's two-point correlation at shift 2.**
* `sum_logTwin_split` / `…_shift` — the split into a harmonic head and that correlation, the second
  stated at Tao's own shape so a consumer does not re-derive multiplicativity at the seam.

⭐ **Why it is worth landing while the campaign is unruled:** it puts **the boundary between what
the corpus HAS and what the Tao campaign must SUPPLY on the page, in the kernel, as an equation.**
The head is `sum_inv_Icc_le`'s object; the tail is the Tao atom and nothing else.
⛔ **SCOPE: an IDENTITY** — no estimate, no asymptotic, no `o(1)`, neither piece bounded.
⚠️ Nothing consumes it yet; 12c's census reads it as a dead branch until the atom arrives. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.liouville_twinProd_mul
  Salt.TwinBar.sum_logTwin_split
  Salt.TwinBar.sum_logTwin_split_shift

/-! ### The harmonic LOWER bound — the divergence the tail-mass step consumes

`sum_inv_Icc_le` (`Wall.lean:219`) gives the UPPER half, `∑_{d≤n} 1/d ≤ 1 + log n`. The corpus had
**no matching lower bound over `Icc 1 n`** — `harmonic_window_bounds` (`LogMeasure.lean:115`) is
two-sided but over `Ioc (x/ω) x`, a different range — and the lower half is the one the log-world
argument actually needs: **it is what makes the head DIVERGE**, which is exactly the hypothesis
`support_infinite_of_lower_unbounded` takes.

⛔ **The sharp `n+1` is not cosmetic.** `log_succ_le_sum_inv_Icc` proves `log(n+1) ≤ ∑`; the naive
`log n ≤ ∑` CANNOT be proved by that induction, because the step would demand
`log(1 + 1/m) ≤ 1/(m+1)`, which is **false**. The plain form follows from the sharp one by
monotonicity, never the other way round.

`sum_inv_Icc_unbounded` packages it as the divergence statement itself. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.log_succ_le_sum_inv_Icc
  Salt.TwinBar.log_le_sum_inv_Icc
  Salt.TwinBar.sum_inv_Icc_unbounded

/-! ### ⭐ THE DIRECT ROUTE'S WIN CONDITION, ASSEMBLED — two named inputs and nothing else

Everything above composes into one statement:

    `Hmain − A  ≤  ∑_{n ≤ N, (n(n+2),P) = 1} (1 − λ(n(n+2)))/n`

given `hcount : Hmain ≤ ∑_{d∣P} μ(d)·∑_{n≤N, d∣n(n+2)} 1/n` and
`hatom : |∑_{d∣P} μ(d)·∑_{n≤N, d∣n(n+2)} λ(n(n+2))/n| ≤ A`.

⭐ **What makes it worth stating is what it does NOT contain.** No `BoundingSieve`, no door, no
`Btwin`, no `c₁`, no level — §7's verdict 2 said the direct route needs none of them, and the
assembly SHOWS it: the only inputs are the count and the atoms. Interface style is
`twinParitySieve_siftedSum_pos_of_margin`'s: **one inequality to beat, not a disjunct to
eliminate.**

⛔ **BOTH INPUTS ARE HYPOTHESES AND NEITHER IS SUPPLIED HERE.** `hcount` is the sifted harmonic
count — elementary, but it needs the residue structure of `n(n+2)` mod `d` (`rho`'s job, NOT done
here). `hatom` is the Tao two-point input, **the campaign object**. ⇒ *This is the SHAPE of the
prize, not the prize.*
⚠️ **§7's verdict 3 stands and must not be blurred:** without roughness, *"Ω(n(n+2)) odd infinitely
often"* is a three-line elementary theorem. The roughness — the coprimality restriction the two
inputs are indexed over — is the ENTIRE content, and is why this is stated at the SIFTED sum.

`sum_logTwin_split_on` is the `Icc`-free generalisation the skeleton needs, since the Möbius
expansion hands each divisor its own filtered index set. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_logTwin_split_on
  Salt.TwinBar.logSifted_lower_of_count_and_atoms

/-! ### Where `W` comes from on the direct route — the divisor-sum Euler bridge

The direct route's main term is `∑_{d∣P} μ(d)·ν(d)·H_N`, so the constant in front of the harmonic
head is `∑_{d∣P} μ(d)·ν(d)`. **That sum IS the sieve's `W`.**

⭐ **This is what makes §7's verdict 2 quantitative.** The verdict said the direct route needs no
`BoundingSieve` — true of the APPARATUS and **false of the CONSTANT**: `W` still appears, because
it is what `∑ μν` equals. ⇒ ***A ROUTE CAN SHED A MACHINE AND KEEP THE MACHINE'S NUMBER*** — worth
one named equation rather than a step buried in a longer proof.

Both halves were landed in `BrunLower/Lemma3.lean` and only needed composing:
`sum_divisors_eq_sum_powerset` (`:107`) with `sum_powerset_prod_neg_nu` (`:151`, the leading Euler
term), `moebius_nu_prod_eq` (`:141`) folding `μ`'s sign into the density product setwise.
`…_twinNu_eq_W` spells it at `twinParitySieve`, where `ν` is the landed twin density
definitionally. -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_divisors_moebius_nu_eq_W
  Salt.TwinBar.sum_divisors_moebius_twinNu_eq_W

/-! ### The per-class harmonic count — the reusable atom of `hcount`

`logSifted_lower_of_count_and_atoms` holds `hcount` as a hypothesis; discharging it means counting
`∑_{n ≤ N, d ∣ n(n+2)} 1/n`. By `Salt.TwinSieve.dvd_iff_mem_Rnat` that set is the union of `ρ(d)`
residue classes mod `d`, so the whole count is `ρ(d)` copies of a SINGLE class sum:

    `∑_{n ≤ N, n ≡ r (mod d)} 1/n  ≤  1 + (1/d)·(1 + log N)`     (`r < d`)

⭐ **The leading `1` is the class's smallest element and is unavoidable, not slack.** The affine
comparison needs `m ≥ 1`; the `m = 0` term (`n = r` itself) is outside its range and is bounded by
`1/r ≤ 1` separately. *A per-class count without that term is false as soon as `N ≥ r`.*

⛔ **ONE-SIDED, AND `hcount` NEEDS MORE — stated so the gap is visible rather than implied.**
`hcount` bounds the SIGNED sum `∑_d μ(d)·C_d` from below, so upper bounds on each `C_d` do not
discharge it: that needs the two-sided form `C_d = ν(d)·H + err_d` with `err_d` controlled, giving
`∑ μ(d)C_d = W·H + ∑ μ(d)err_d` (and `W` is `sum_divisors_moebius_nu_eq_W` above). **This is the
first half of that, not the whole of it.** -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_inv_class_le

/-! ### `sum_inv_affine_sub_harmonic` — the ADDITIVE error, and the second layer of the trap

    `0  ≤  (1/d)·∑_{m≤M} 1/m  −  ∑_{m≤M} 1/(d·m+r)  ≤  2/d`     (`r ≤ d`)

⛔⛔ **THE CARD ABOVE NAMED ONE LAYER OF THE TRAP AND THERE ARE TWO.** It records that
`sum_inv_class_le` is one-sided while `hcount` needs two sides. True — but the two-sided pair this
file already audits (`sum_inv_affine_le` + `sum_inv_affine_ge`) **does not discharge `hcount`
either**: that pair is a sandwich between `(1/d)·H` and `(1/(2d))·H`, which is **MULTIPLICATIVE**.
`∑_d μ(d)·C_d` is a CANCELLING sum whose value `W·H` is far smaller than its individual terms, so a
factor-2 slop per class does not perturb the main term — it destroys it.

⇒ 🔑 ***A SANDWICH IS NOT AN ERROR TERM. A SIGNED SUM NEEDS THE ERROR TO BE ADDITIVE, AND
"two-sided" ALONE DOES NOT SAY WHICH KIND YOU HAVE.*** *The gap here was not visible from the word
"two-sided"; it was visible only from asking what the CONSUMER does with the two sides.*

⭐ The error is **one-signed** (stated `0 ≤ … ≤ 2/d`, not with `|·|`) because a cancelling consumer
wants the sign, and **both the main term and the error carry `1/d` and nothing else `d`-dependent**
— which is what makes `∑_d μ(d)·err_d` summable against `W`.

📌 **REUSED, NOT RE-DERIVED:** the `∑_{m ≤ M} 1/m² ≤ 2` step is the landed
`Salt.TwinBar.sum_inv_sq_Icc_le` (`TwinBar/LambdaRate.lean:363`) — already in this file's namespace
and import closure, with exactly the range `Icc 1 M` and exactly the constant `2`. *A first search
for it under the `Salt.Chen` spelling found a different copy and would have cost an import.* -/
open Salt.Tactic in
#audit_axioms Salt.TwinBar.sum_inv_affine_sub_harmonic
