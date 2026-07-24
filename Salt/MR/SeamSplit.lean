/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Prop1Assembly

/-!
# SeamSplit — the eq-(24) seam as a PROVEN partition inequality (`SEAM-WAVE`)

The seam freeze `docs/exploration/seam-freeze-0724.md` at its ⟦AMENDMENT V2⟧ scope (the
refuter ruling of 2026-07-24).  The landed `int_U` rows (`AnnHead.prop_A3_T1_row_annular`,
`Prop1Assembly.prop_A3_T1_row_moment`) carry the §8 eq-(24) seam as a NAMED EQUALITY binder
`Itot = (annHead + Utail) + Imom`, and the 2026-07-24 audit (flags: "the hsplit/annHead
object mismatch") showed that binder is unsatisfiable at the intended instantiation.  This
file builds the honest replacement: a genuine, kernel-checked PARTITION of the annular mean
square of the dyadic polynomial `spoly`,

  `∫_{Ann} ‖spoly‖²  =  ∫_{Ann ∩ ball} ‖spoly‖²  +  ∫_{Ann \ ball} ‖spoly‖²`
                     `=  [ball leg]  +  ∫_{(Ann\ball) ∩ 𝒯tot}  +  ∫_{(Ann\ball) ∩ 𝒰}`,

with the ball leg bounded by `measure × sup²` through an UNCONDITIONAL Abel (partial
summation) inequality, the `𝒯`-leg collapsed by ONE monotonicity into `[-T,T]` (never a
`Σⱼ` of `J` copies — `J` grows with `X`; catch #253), and the `𝒰`-leg carried as the single
named binder whose supply is the §8.3 interior.

## The geometry (matching `DistHalasz.M_range`'s window)

* `seamT0 X = (log X)^{1/15}`, `seamRad X = (log X)^{1/16}` — the MR §2 frequency floor and
  the ball radius (the `1/16 < 1/15` separation is the T-0 card's ball geometry).
* `seamAnn X T = {t | seamT0 X ≤ |t| ∧ |t| ≤ T}` — the annulus.  For `seamT0 X ≤ T ≤ X` it
  sits inside `M_range`'s window `{|t| ≥ (logX)^{1/15}, |t| ≤ T + (logX)^{1/16}, |t| ≤ X}`
  (`seamAnn_subset_Mrange_window`), so a near-minimizer `t₁` of the window infimum is a
  legitimate ball center.
* `seamBall X t₁ = {t | |t - t₁| ≤ seamRad X}` — the ball, of measure exactly `2·seamRad X`.

## The stones

* `annulus_ball_far_split` [Z1] — the two-set `setIntegral` split (`integral_inter_add_sdiff`
  + integrability from continuity on the bounded annulus, via `Measure.integrableOn_of_bounded`
  — NOT compactness of the pieces, which are not compact).
* `spolyA`, `spoly_eq_abel`, `spoly_abel_sup` [Z2a] — the UNCONDITIONAL Abel inequality.
  `A_t(m) := Σ_{n ≤ m} aₙ n^{-it}` is the twisted partial sum; the DISCRETE summation by
  parts (Abel FROM 1, never the `−A(X)/X` two-endpoint identity — the closed-at-`X` trap)
  gives `spoly N a t = A_t(N)/N + Σ_{n<N} A_t(n)/(n(n+1))`, whence, on the dyadic support
  (`aₙ = 0` for `n ≤ X`, `X ≤ N ≤ 2X`), `‖spoly N a t‖ ≤ 2·S` whenever `‖A_t(m)‖ ≤ S·m`.
  The honest constant is `2` (the freeze's cap was `3`): the head term contributes `S` and
  the tail contributes at most `(#{X < n ≤ N}) · S/X ≤ S`.  NO ball-decay input is used —
  the sup hypothesis is a named binder downstream (see `prop_A3_T1_row_split`).
* `ball_leg_of_sup` [Z3] — `measure × sup²`: the ball leg is `≤ 2·seamRad X·(2S)²`.  The
  squaring happens ONCE, here (the Abel exit is the SUM bound, not its square).
* `continuous_primeBlockPoly`, `isClosed_blockSmallAt`, `measurableSet_Tset`,
  `measurableSet_Uset`, `sdiff_biUnion_Tset`, `seam_T_additivity`, `seam_TU_split` [Z4] —
  the `𝒯ⱼ/𝒰` partition machinery over the landed `Decomp` definitions.  `BlockSmallAt`'s
  set is an ARBITRARY intersection of closed sets (no countability needed); `Tset`/`Uset`
  are measurable (countable intersections); the disjoint additivity is
  `MeasureTheory.integral_biUnion_finset` fed by the landed `Tset_disjoint`,
  `Tset_Uset_disjoint` and `exists_Tset_or_mem_Uset`.
* `far_leg_collapse` [Z5] — the far leg bounded WITHOUT the `J`-factor: one monotonicity of
  the setIntegral into `[-T,T]`, through the `intervalIntegral ↔ setIntegral` bridge
  (`integral_of_le` + the null-endpoint `Icc/Ioc` equivalence).
* `prop_A3_T1_row_split` [Z6] — THE SEAM ROW: the assembled partition inequality, with the
  ball center `t₁` produced as a near-minimizer of `M_range`'s window infimum
  (`Real.lt_sInf_add_pos`, Nonempty only — no `BddBelow`, no minimality spent).  Its `𝒯`-leg
  is kept as the honest integral; `prop_A3_T1_row_split_crude` is the freeze's stated exit
  shape, with that leg collapsed into `∫_{-T}^{T}` (crude by construction — at that collapse
  the row no longer beats the trivial `Ann ⊆ [-T,T]` monotonicity, so the sharp row is the
  one that carries content).

## What is NOT here (the honest residual)

The pointwise ball sup `hSup` and the `𝒰`-leg bound `hU` are NAMED BINDERS.  V2's ruling:
`halasz_ball_decay` is a scalar re-arrangement, NOT a landed sum bound, so the ball sup has
no landed supply — its map is the open T1 frontier (`hpret`/`hbridge`/`hgrade`, HExit's
CODA), or the `L²`-route alternative.  `hU`'s supply is the §8.3 interior (L3-dyadic +
L9-hZ + L12-herr).  Every other leg in this file is proven.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2, §8; MRT v3 Appendix A.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-! ## §0 — the seam geometry -/

/-- **The frequency floor `T₀ = (log X)^{1/15}`** (MR §2's lower cutoff; `M_range`'s window
floor byte-for-byte). -/
def seamT0 (X : ℝ) : ℝ := (Real.log X) ^ (1 / 15 : ℝ)

/-- **The ball radius `r = (log X)^{1/16}`** — the T-0 card's ball geometry; `1/16 < 1/15`
keeps the ball/range separation. -/
def seamRad (X : ℝ) : ℝ := (Real.log X) ^ (1 / 16 : ℝ)

/-- **The annulus `Ann(T₀,T) = {t : T₀ ≤ |t| ≤ T}`** — the integration range of the seam
mean square (`lemma14_contour`'s datum). -/
def seamAnn (X T : ℝ) : Set ℝ := {t : ℝ | seamT0 X ≤ |t| ∧ |t| ≤ T}

/-- **The ball `B(t₁, r) = {t : |t − t₁| ≤ r}`** around the near-minimizer `t₁`. -/
def seamBall (X t₁ : ℝ) : Set ℝ := {t : ℝ | |t - t₁| ≤ seamRad X}

lemma seamT0_nonneg {X : ℝ} (hL : 0 ≤ Real.log X) : 0 ≤ seamT0 X :=
  Real.rpow_nonneg hL _

lemma seamRad_nonneg {X : ℝ} (hL : 0 ≤ Real.log X) : 0 ≤ seamRad X :=
  Real.rpow_nonneg hL _

lemma measurableSet_seamAnn (X T : ℝ) : MeasurableSet (seamAnn X T) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

lemma measurableSet_seamBall (X t₁ : ℝ) : MeasurableSet (seamBall X t₁) :=
  measurableSet_le (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    measurable_const

/-- The ball is the closed interval of radius `seamRad X` about `t₁`. -/
lemma seamBall_eq_Icc (X t₁ : ℝ) :
    seamBall X t₁ = Set.Icc (t₁ - seamRad X) (t₁ + seamRad X) := by
  ext t
  simp only [seamBall, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The ball has measure exactly `2r`. -/
lemma volume_seamBall (X t₁ : ℝ) :
    volume (seamBall X t₁) = ENNReal.ofReal (2 * seamRad X) := by
  rw [seamBall_eq_Icc, Real.volume_Icc]
  congr 1
  ring

/-- The annulus sits in `[-T, T]`. -/
lemma seamAnn_subset_Icc (X T : ℝ) : seamAnn X T ⊆ Set.Icc (-T) T :=
  fun _ ht => Set.mem_Icc.mpr (abs_le.mp ht.2)

/-- **The annulus sits inside `M_range`'s window** (the V2 hypotheses `hT₀ : T₀ ≤ T` and
`hTX : T ≤ X` at work): a frequency of the seam annulus is definitionally a window
membership witness, so the near-minimizer `t₁` of the window infimum is a lawful ball
center.  (MR Step 0 licenses `T ≤ X`; the consumer's `T = X/h₁ ≤ X`.) -/
lemma seamAnn_subset_Mrange_window {X T : ℝ} (hTX : T ≤ X) (hL : 0 ≤ Real.log X) :
    seamAnn X T ⊆ {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X} := by
  rintro t ⟨h1, h2⟩
  have h16 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hL _
  exact ⟨h1, by linarith, le_trans h2 hTX⟩

/-! ## §1 — integrability on the bounded pieces

Every piece of the split is a bounded measurable subset of `[-T,T]`, and the integrand is
continuous, so integrability is `Measure.integrableOn_of_bounded` (finite measure + a sup
from continuity on the COMPACT `[-T,T]`).  The pieces themselves are not compact — the
annulus minus a ball is not closed under the sdiff — so the compactness route is unavailable
and this is the correct tool. -/

/-- **The integrability workhorse.**  A continuous function is integrable on any measurable
subset of `[-T,T]`. -/
lemma integrableOn_of_continuous_subset_Icc {F : ℝ → ℝ} (hF : Continuous F) {s : Set ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hs : MeasurableSet s) (hsub : s ⊆ Set.Icc (-T) T) :
    IntegrableOn F s volume := by
  have hne : (Set.Icc (-T) T).Nonempty := ⟨T, Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩⟩
  obtain ⟨c, _, hmax⟩ :=
    (isCompact_Icc (a := -T) (b := T)).exists_isMaxOn hne hF.norm.continuousOn
  refine Measure.integrableOn_of_bounded (M := ‖F c‖) ?_ hF.aestronglyMeasurable ?_
  · refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem hs] with x hx
    exact hmax (hsub hx)

/-! ## §2 — Z1: the ball / far split of the annulus -/

/-- **Z1 — the annulus splits into its ball part and its far part**
(`annulus_ball_far_split`).  The two-set `setIntegral` identity
`∫_{Ann} = ∫_{Ann ∩ ball} + ∫_{Ann \ ball}` for a continuous integrand.  Measurability is
free (the annulus is an intersection of two closed `|·|`-conditions; the ball is closed) and
integrability comes from §1.

The V2 hypotheses `hT₀ : seamT0 X ≤ T` and `hTX : T ≤ X` are NOT needed for the split
itself — they govern the window inclusion, recorded separately as
`seamAnn_subset_Mrange_window` and consumed at the seam row.  Only `0 ≤ T` is used here (it
makes `[-T,T]` nonempty for the sup). -/
theorem annulus_ball_far_split {F : ℝ → ℝ} (hF : Continuous F) (X T t₁ : ℝ) (hT : 0 ≤ T) :
    (∫ t in seamAnn X T, F t)
      = (∫ t in seamAnn X T ∩ seamBall X t₁, F t)
        + ∫ t in seamAnn X T \ seamBall X t₁, F t :=
  (integral_inter_add_sdiff (measurableSet_seamBall X t₁)
    (integrableOn_of_continuous_subset_Icc hF hT (measurableSet_seamAnn X T)
      (seamAnn_subset_Icc X T))).symm

/-! ## §3 — Z2a: the unconditional Abel inequality -/

/-- **The twisted partial sum `A_t(m) = Σ_{1≤n≤m} aₙ/n^{it}`** — the Abel-summation partner
of `spoly` (`spoly N a t = Σ_{1≤n≤N} aₙ/n^{1+it}`): the `1/n` weight is exactly what the
summation by parts strips off. -/
def spolyA (a : ℕ → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, a n / (n : ℂ) ^ ((t : ℂ) * Complex.I)

/-- `aₙ/n^{1+it} = (aₙ/n^{it})/n` for `n ≠ 0` — the one cpow step behind the Abel identity. -/
lemma cterm_split {n : ℕ} (hn : n ≠ 0) (c : ℂ) (t : ℝ) :
    c / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      = (c / (n : ℂ) ^ ((t : ℂ) * Complex.I)) / (n : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hne : (n : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := fun h =>
    hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [Complex.cpow_add _ _ hn0, Complex.cpow_one]
  field_simp

/-- **The Abel identity (summation by parts FROM 1).**

  `spoly N a t = A_t(N)/N + Σ_{1≤n<N} A_t(n)/(n(n+1))`.

This is the CONVENTION-PROOF form: the sum starts at `1` (matching `spoly`'s own
`Finset.Icc 1 N`), so no endpoint of the coefficient support is ever assumed closed.  In
particular the two-endpoint identity `spoly = A(N)/N − A(X)/X + ∫_X^N A(u)/u² du` — which
silently assumes the dyadic window is closed at `X` — is NEVER used; the `[1,X]` head is
killed by the support hypothesis downstream instead.  The discrete form also avoids the
integral entirely: `1/n − 1/(n+1) = 1/(n(n+1))`. -/
lemma spoly_eq_abel (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    spoly N a t
      = spolyA a t N / (N : ℂ)
        + ∑ n ∈ Finset.Ico 1 N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)) := by
  induction N with
  | zero => simp [spoly, spolyA]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [spoly, spolyA]
    · have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hN1 : ((N : ℕ) : ℂ) + 1 ≠ 0 := by
        have hcast : ((N : ℕ) : ℂ) + 1 = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]
        exact Nat.cast_ne_zero.mpr (by omega)
      have hspoly : spoly (N + 1) a t
          = spoly N a t
            + a (N + 1) / ((N + 1 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
        simp only [spoly]
        exact Finset.sum_Icc_succ_top (by omega) _
      have hAstep : spolyA a t (N + 1)
          = spolyA a t N + a (N + 1) / ((N + 1 : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
        simp only [spolyA]
        exact Finset.sum_Icc_succ_top (by omega) _
      have hIco : (∑ n ∈ Finset.Ico 1 (N + 1), spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)))
          = (∑ n ∈ Finset.Ico 1 N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)))
            + spolyA a t N / ((N : ℂ) * ((N : ℂ) + 1)) :=
        Finset.sum_Ico_succ_top hN _
      rw [hspoly, ih, hAstep, hIco, cterm_split (n := N + 1) (by omega) (a (N + 1)) t]
      set c : ℂ := a (N + 1) / ((N + 1 : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) with hc
      set A : ℂ := spolyA a t N with hA
      set SS : ℂ := ∑ n ∈ Finset.Ico 1 N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)) with hSS
      push_cast
      field_simp
      ring

/-- **Z2a — THE UNCONDITIONAL ABEL INEQUALITY (`spoly_abel_sup`).**  For a dyadic
coefficient sequence (`aₙ = 0` for `n ≤ X`) with cutoff `X ≤ N ≤ 2X`, a linear bound on the
twisted partial sums transfers to the polynomial itself with an ABSOLUTE constant:

  `(∀ m ≤ N, ‖A_t(m)‖ ≤ S·m)  ⟹  ‖spoly N a t‖ ≤ 2·S`.

The page (honest, no `log`): the Abel identity contributes `‖A_t(N)‖/N ≤ S` from the head
term, and the tail `Σ_{1≤n<N} ‖A_t(n)‖/(n(n+1))` is supported on `X < n < N` (the support
hypothesis kills `n ≤ X`), where each term is `≤ S·n/(n(n+1)) = S/(n+1) ≤ S/X`; there are
at most `N − ⌊X⌋ − 1 ≤ X` such terms, so the tail is `≤ X·(S/X) = S`.  Total `2S` — inside
the freeze's `3S` cap, and better than the `(1+log 2)` continuous page.

No ball-decay input, no analytic hypothesis: the sup hypothesis is a named binder for the
consumer (see `prop_A3_T1_row_split`). -/
theorem spoly_abel_sup {N : ℕ} {a : ℕ → ℂ} {t X S : ℝ}
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hA : ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m) :
    ‖spoly N a t‖ ≤ 2 * S := by
  have hNR : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hX hXN
  have hS : 0 ≤ S := by
    have h := hA N le_rfl
    nlinarith [norm_nonneg (spolyA a t N)]
  -- the partial sums vanish below the dyadic window
  have hAzero : ∀ n : ℕ, (n : ℝ) ≤ X → spolyA a t n = 0 := by
    intro n hn
    refine Finset.sum_eq_zero (fun m hm => ?_)
    have hmn : (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hm).2
    rw [hsupp m (le_trans hmn hn), zero_div]
  -- the head term
  have hhead : ‖spolyA a t N / (N : ℂ)‖ ≤ S := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hNR]
    exact hA N le_rfl
  -- the tail term
  have hKX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX.le
  have hXK : X < ((⌊X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one X
  have htailterm : ∀ n ∈ Finset.Ico (⌊X⌋₊ + 1) N,
      ‖spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1))‖ ≤ S / X := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
    have hnR : ((⌊X⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hnorm : ‖((n : ℂ) * ((n : ℂ) + 1))‖ = (n : ℝ) * ((n : ℝ) + 1) := by
      have hc : ((n : ℕ) : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [norm_mul, Complex.norm_natCast, hc, Complex.norm_natCast]
      push_cast
      ring
    rw [norm_div, hnorm]
    have hAn : ‖spolyA a t n‖ ≤ S * (n : ℝ) := hA n (by omega)
    have hstep : ‖spolyA a t n‖ / ((n : ℝ) * ((n : ℝ) + 1)) ≤ S / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hAn, hnpos]
    refine hstep.trans ?_
    apply div_le_div_of_nonneg_left hS hX
    linarith
  have htail : ‖∑ n ∈ Finset.Ico 1 N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1))‖ ≤ S := by
    have hsub : Finset.Ico (⌊X⌋₊ + 1) N ⊆ Finset.Ico 1 N :=
      Finset.Ico_subset_Ico (by omega) le_rfl
    have hvanish : ∀ x ∈ Finset.Ico 1 N, x ∉ Finset.Ico (⌊X⌋₊ + 1) N →
        spolyA a t x / ((x : ℂ) * ((x : ℂ) + 1)) = 0 := by
      intro x hx hxni
      have hx2 := (Finset.mem_Ico.mp hx).2
      have hxK : x ≤ ⌊X⌋₊ := by
        by_contra hcon
        exact hxni (Finset.mem_Ico.mpr ⟨by omega, hx2⟩)
      have hxR : (x : ℝ) ≤ X := le_trans (by exact_mod_cast hxK) hKX
      rw [hAzero x hxR, zero_div]
    have hrestrict :
        (∑ n ∈ Finset.Ico 1 N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)))
          = ∑ n ∈ Finset.Ico (⌊X⌋₊ + 1) N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1)) :=
      (Finset.sum_subset hsub hvanish).symm
    have hcard : ((Finset.Ico (⌊X⌋₊ + 1) N).card : ℝ) ≤ X := by
      rw [Nat.card_Ico]
      by_cases hle : ⌊X⌋₊ + 1 ≤ N
      · rw [Nat.cast_sub hle]
        push_cast
        linarith
      · have hzero : N - (⌊X⌋₊ + 1) = 0 := by omega
        rw [hzero, Nat.cast_zero]
        exact hX.le
    rw [hrestrict]
    calc ‖∑ n ∈ Finset.Ico (⌊X⌋₊ + 1) N, spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1))‖
        ≤ ∑ n ∈ Finset.Ico (⌊X⌋₊ + 1) N, ‖spolyA a t n / ((n : ℂ) * ((n : ℂ) + 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ico (⌊X⌋₊ + 1) N, S / X := Finset.sum_le_sum htailterm
      _ = ((Finset.Ico (⌊X⌋₊ + 1) N).card : ℝ) * (S / X) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ X * (S / X) := by
          apply mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = S := by field_simp
  rw [spoly_eq_abel]
  refine (norm_add_le _ _).trans ?_
  linarith

/-! ## §4 — Z3: the ball leg -/

/-- **Z3 — the ball leg by `measure × sup²` (`ball_leg_of_sup`).**  Under the pointwise
partial-sum bound `hSup` on the ball, the ball leg of the annular mean square is

  `∫_{Ann ∩ ball} ‖spoly‖² ≤ 2r·(2S)²`,   `r = seamRad X = (log X)^{1/16}`.

The measure of `Ann ∩ ball` is at most that of the ball, exactly `2r`; the integrand is
bounded pointwise by `(2S)²` through `spoly_abel_sup`.  The SQUARING HAPPENS ONCE, here:
the Abel exit `‖spoly‖ ≤ 2S` is the sum bound, and this stone squares it — there is no
double squaring in the chain. -/
theorem ball_leg_of_sup {N : ℕ} {a : ℕ → ℂ} {X T t₁ S : ℝ}
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hT : 0 ≤ T)
    (hL : 0 ≤ Real.log X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, |t - t₁| ≤ seamRad X → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2)
      ≤ 2 * seamRad X * (2 * S) ^ 2 := by
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hmeas : MeasurableSet (seamAnn X T ∩ seamBall X t₁) :=
    (measurableSet_seamAnn X T).inter (measurableSet_seamBall X t₁)
  have hsub : seamAnn X T ∩ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hint : IntegrableOn (fun t : ℝ => ‖spoly N a t‖ ^ 2)
      (seamAnn X T ∩ seamBall X t₁) volume :=
    integrableOn_of_continuous_subset_Icc hcont hT hmeas hsub
  have hvol : volume (seamAnn X T ∩ seamBall X t₁) ≤ ENNReal.ofReal (2 * seamRad X) := by
    rw [← volume_seamBall X t₁]
    exact measure_mono Set.inter_subset_right
  have hfin : volume (seamAnn X T ∩ seamBall X t₁) < ⊤ :=
    lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have hrad : (0 : ℝ) ≤ 2 * seamRad X := by
    have := seamRad_nonneg (X := X) hL; linarith
  have htoReal : (volume (seamAnn X T ∩ seamBall X t₁)).toReal ≤ 2 * seamRad X := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hrad] at h
  have hdom : ∀ t ∈ seamAnn X T ∩ seamBall X t₁,
      ‖spoly N a t‖ ^ 2 ≤ (2 * S) ^ 2 := by
    intro t ht
    have hball : |t - t₁| ≤ seamRad X := ht.2
    have hpt : ‖spoly N a t‖ ≤ 2 * S :=
      spoly_abel_sup hX hXN hN2 hsupp (hSup t hball)
    exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
  calc (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2)
      ≤ ∫ _t in seamAnn X T ∩ seamBall X t₁, (2 * S) ^ 2 :=
        setIntegral_mono_on hint (integrableOn_const hfin.ne) hmeas hdom
    _ = (volume (seamAnn X T ∩ seamBall X t₁)).toReal • (2 * S) ^ 2 := setIntegral_const _
    _ = (volume (seamAnn X T ∩ seamBall X t₁)).toReal * (2 * S) ^ 2 := smul_eq_mul _ _
    _ ≤ 2 * seamRad X * (2 * S) ^ 2 :=
        mul_le_mul_of_nonneg_right htoReal (sq_nonneg _)

/-! ## §5 — Z4: the `𝒯ⱼ / 𝒰` partition machinery -/

/-- The prime block polynomial `Σ_{P≤p≤Q} f(p)/p^{1+it}` is continuous in `t` (a finite sum
of `continuous_cterm` terms; every index is a prime, hence nonzero). -/
lemma continuous_primeBlockPoly (f : ℕ → ℂ) (P Q : ℕ) :
    Continuous fun t : ℝ => primeBlockPoly f P Q t := by
  unfold primeBlockPoly
  refine continuous_finsetSum _ (fun p hp => ?_)
  have hp' : p.Prime := (Finset.mem_filter.mp hp).2
  exact continuous_cterm hp'.pos.ne' (f p)

/-- **`BlockSmallAt`'s set is CLOSED.**  It is an ARBITRARY intersection (over all
subdivisions `[P,Q] ⊆ [Pⱼ,Qⱼ]`) of the closed sublevel sets of the continuous
`‖primeBlockPoly‖`.  No countability is needed for closedness — that only enters when we
convert to measurability, where the index set is `ℕ` anyway. -/
lemma isClosed_blockSmallAt (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (j : ℕ) :
    IsClosed {t : ℝ | BlockSmallAt f Pseq Qseq δ j t} := by
  have hset : {t : ℝ | BlockSmallAt f Pseq Qseq δ j t}
      = ⋂ P : ℕ, ⋂ Q : ℕ, ⋂ (_ : Pseq j ≤ P), ⋂ (_ : Q ≤ Qseq j),
          {t : ℝ | ‖primeBlockPoly f P Q t‖ ≤ δ} := by
    ext t
    simp only [BlockSmallAt, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun P => isClosed_iInter fun Q => isClosed_iInter fun _ =>
    isClosed_iInter fun _ =>
      isClosed_le (continuous_primeBlockPoly f P Q).norm continuous_const

/-- `𝒰` is measurable (a countable intersection of the open complements of the
`BlockSmallAt` sets, over `j ∈ [1,J]`).  Restricting the intersection to the explicit range
`[1,J]` is what makes it countable-by-construction; plain measurability is all the split
needs. -/
lemma measurableSet_Uset (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) :
    MeasurableSet (Uset f Pseq Qseq δ J) := by
  have hset : Uset f Pseq Qseq δ J
      = ⋂ j ∈ Set.Icc 1 J, {t : ℝ | BlockSmallAt f Pseq Qseq δ j t}ᶜ := by
    ext t
    simp only [Uset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j hj1 hj2 => h j ⟨hj1, hj2⟩⟩
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => (isClosed_blockSmallAt f Pseq Qseq δ j).measurableSet.compl)

/-- `𝒯ⱼ` is measurable: for `1 ≤ j ≤ J` it is the closed `BlockSmallAt` set intersected with
the (countably many) open complements at the smaller indices `i < j`; outside that range it
is empty. -/
lemma measurableSet_Tset (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J j : ℕ) :
    MeasurableSet (Tset f Pseq Qseq δ J j) := by
  by_cases hj : 1 ≤ j ∧ j ≤ J
  · have hset : Tset f Pseq Qseq δ J j
        = {t : ℝ | BlockSmallAt f Pseq Qseq δ j t}
          ∩ ⋂ i ∈ Set.Ico 1 j, {t : ℝ | BlockSmallAt f Pseq Qseq δ i t}ᶜ := by
      ext t
      simp only [Tset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_Ico]
      constructor
      · rintro ⟨-, -, hs, hm⟩
        exact ⟨hs, fun i hi => hm i hi.1 hi.2⟩
      · rintro ⟨hs, hm⟩
        exact ⟨hj.1, hj.2, hs, fun i h1 h2 => hm i ⟨h1, h2⟩⟩
    rw [hset]
    exact (isClosed_blockSmallAt f Pseq Qseq δ j).measurableSet.inter
      (MeasurableSet.biInter (Set.to_countable _)
        (fun i _ => (isClosed_blockSmallAt f Pseq Qseq δ i).measurableSet.compl))
  · have hset : Tset f Pseq Qseq δ J j = ∅ := by
      ext t
      simp only [Tset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hj
    rw [hset]
    exact MeasurableSet.empty

/-- **`𝒯tot`** — the union of the `𝒯ⱼ` over the honest index range `j ∈ [1,J]`.  Keeping the
union as ONE object (rather than a `Σⱼ`) is what lets the far leg be bounded by a single
monotonicity: `J` grows with `X`, so a `J`-fold sum of interval bounds would be a false
economy (catch #253). -/
def seamTtot (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) : Set ℝ :=
  ⋃ j ∈ Finset.Icc 1 J, Tset f Pseq Qseq δ J j

lemma measurableSet_seamTtot (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) :
    MeasurableSet (seamTtot f Pseq Qseq δ J) :=
  Finset.measurableSet_biUnion _ (fun j _ => measurableSet_Tset f Pseq Qseq δ J j)

/-- **The annulus-restricted exhaustiveness.**  Off `𝒯tot`, every point lies in `𝒰`:
`R \ 𝒯tot = R ∩ 𝒰`.  This is the landed `exists_Tset_or_mem_Uset` (every real is in some
`𝒯ⱼ` or in `𝒰`) plus `Tset_Uset_disjoint`, restricted to an arbitrary `R`. -/
lemma sdiff_biUnion_Tset (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) (R : Set ℝ) :
    R \ seamTtot f Pseq Qseq δ J = R ∩ Uset f Pseq Qseq δ J := by
  have hcover : ∀ t : ℝ, t ∉ seamTtot f Pseq Qseq δ J ↔
      t ∈ Uset f Pseq Qseq δ J := by
    intro t
    constructor
    · intro hnot
      rcases exists_Tset_or_mem_Uset (f := f) (Pseq := Pseq) (Qseq := Qseq) (δ := δ)
        (J := J) t with ⟨j, hj⟩ | hU
      · exact absurd (Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hj.1, hj.2.1⟩) hj) hnot
      · exact hU
    · intro hU hmem
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp Tset_Uset_disjoint hj hU
  ext t
  constructor
  · rintro ⟨htR, hnot⟩
    exact ⟨htR, (hcover t).mp hnot⟩
  · rintro ⟨htR, htU⟩
    exact ⟨htR, (hcover t).mpr htU⟩

/-- **Z4(iv) — the disjoint additivity over the `𝒯ⱼ`** (`seam_T_additivity`).  The
`𝒯ⱼ`-part of `R` splits as a finite sum, via `MeasureTheory.integral_biUnion_finset` fed by
the landed pairwise disjointness `Tset_disjoint`.  (This is the granular form; the seam row
uses the union form of `seam_TU_split` instead, so no `J`-factor is ever created — catch
#253.) -/
theorem seam_T_additivity {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {δ : ℝ} {J : ℕ}
    {F : ℝ → ℝ} (hF : Continuous F) {R : Set ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hR : MeasurableSet R) (hRsub : R ⊆ Set.Icc (-T) T) :
    (∫ t in R ∩ seamTtot f Pseq Qseq δ J, F t)
      = ∑ j ∈ Finset.Icc 1 J, ∫ t in R ∩ Tset f Pseq Qseq δ J j, F t := by
  rw [seamTtot, Set.inter_iUnion₂]
  refine integral_biUnion_finset _ (fun j _ => hR.inter (measurableSet_Tset f Pseq Qseq δ J j))
    ?_ (fun j _ => integrableOn_of_continuous_subset_Icc hF hT
      (hR.inter (measurableSet_Tset f Pseq Qseq δ J j))
      (fun _ ht => hRsub ht.1))
  intro i _ j _ hij
  exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (Tset_disjoint hij)

/-- **Z4 — the two-set `𝒯tot / 𝒰` split of a bounded piece** (`seam_TU_split`).  For any
measurable `R ⊆ [-T,T]`,

  `∫_R F = ∫_{R ∩ ⋃ⱼ 𝒯ⱼ} F + ∫_{R ∩ 𝒰} F`.

The union form (rather than the `Σⱼ` form) is what the seam row consumes: it lets the whole
`𝒯`-side be bounded by ONE monotonicity into `[-T,T]`, so no factor of `J` (which grows with
`X`) is ever introduced. -/
theorem seam_TU_split {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {δ : ℝ} {J : ℕ}
    {F : ℝ → ℝ} (hF : Continuous F) {R : Set ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hR : MeasurableSet R) (hRsub : R ⊆ Set.Icc (-T) T) :
    (∫ t in R, F t)
      = (∫ t in R ∩ seamTtot f Pseq Qseq δ J, F t)
        + ∫ t in R ∩ Uset f Pseq Qseq δ J, F t := by
  have hint : IntegrableOn F R volume :=
    integrableOn_of_continuous_subset_Icc hF hT hR hRsub
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := F)
    (measurableSet_seamTtot f Pseq Qseq δ J) hint
  rw [sdiff_biUnion_Tset f Pseq Qseq δ J R] at hsplit
  exact hsplit.symm

/-! ## §6 — Z5: the far leg, collapsed -/

/-- **Z5 — the far leg without the `J`-factor** (`far_leg_collapse`).  Any measurable piece
of `[-T,T]` carries at most the full interval's mass, for a nonnegative integrand:

  `∫_s F ≤ ∫_{-T}^{T} F`.

Applied to `R ∩ ⋃ⱼ 𝒯ⱼ` (the union, already collapsed by `seam_TU_split`) this is ONE
monotonicity — never a `Σⱼ` of `J` separate copies of the interval bound (`J` grows with
`X`; catch #253).  The `intervalIntegral ↔ setIntegral` bridge is
`intervalIntegral.integral_of_le` plus the null-endpoint `Icc`/`Ioc` equivalence. -/
theorem far_leg_collapse {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    {s : Set ℝ} {T : ℝ} (hT : 0 ≤ T) (hsub : s ⊆ Set.Icc (-T) T) :
    (∫ t in s, F t) ≤ ∫ t in (-T)..T, F t := by
  have hint : IntegrableOn F (Set.Icc (-T) T) volume :=
    integrableOn_of_continuous_subset_Icc hF hT measurableSet_Icc Set.Subset.rfl
  have hmono : (∫ t in s, F t) ≤ ∫ t in Set.Icc (-T) T, F t :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hF0)
      (HasSubset.Subset.eventuallyLE hsub)
  rwa [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ## §7 — Z6: the seam row -/

/-- **Z6 — THE SEAM ROW (`prop_A3_T1_row_split`).**  The assembled, kernel-checked eq-(24)
partition inequality for the annular mean square of the dyadic seam polynomial:

  `∫_{Ann} ‖spoly N a t‖²  ≤  2r·(2S)²  +  ∫_{(Ann\ball) ∩ 𝒯tot} ‖spoly N a t‖²  +  U`,

`r = seamRad X = (log X)^{1/16}`, with the ball center `t₁` produced HERE as a near-minimizer
of `M_range`'s window infimum.

**The assembly** (the grouping that avoids double counting — the ball may meet both `𝒰` and
the `𝒯ⱼ`, so the partition is applied to `Ann \ ball`, not to `Ann`):

1. `∫_{Ann} = ∫_{Ann ∩ ball} + ∫_{Ann \ ball}`                     (`annulus_ball_far_split`)
2. `∫_{Ann ∩ ball} ≤ 2r·(2S)²`                                     (`ball_leg_of_sup` ⟸ Abel)
3. `∫_{Ann \ ball} = ∫_{(Ann\ball) ∩ 𝒯tot} + ∫_{(Ann\ball) ∩ 𝒰}`   (`seam_TU_split`)
4. `∫_{(Ann\ball) ∩ 𝒰} ≤ U`                                        (the binder `hU`)

The `𝒯`-leg is left as the honest INTEGRAL, not pre-collapsed: replacing it by `∫_{-T}^{T}`
(the crude placeholder of `prop_A3_T1_row_split_crude`, one `far_leg_collapse` away) yields a
statement weaker than the trivial `Ann ⊆ [-T,T]` monotonicity, so the sharp form is the one
that carries content.  Sharpening the `𝒯`-leg proper — MR's per-block Ramaré/moment
treatment — is §8's interior, not this wave's.

**Why this is a NEW statement.**  The landed rows (`prop_A3_T1_row_annular`,
`prop_A3_T1_row_moment`) are not consumable here: their `hsplit` demands `annHead` — the
full seam L-series at `Re = 1 + σ` — as the head object, and the 2026-07-24 audit showed
that object is `Θ(T)`-sized, the wrong family (flags: "the hsplit/annHead object mismatch").
The `≤`-weakened clones `prop_A3_T1_row_annular_le` / `prop_A3_T1_row_moment_le` land
alongside as the shape a genuine split can feed; THIS row is the genuine split, on the
dyadic object, at `Re = 1` throughout (NO `n^{-σ}` rescale — that was the B-pin's line,
retired with `annHead`).

**The two data are kept SEPARATE** (the datum conflation was fatal as drafted): the dyadic
`a : ℕ → ℂ` with `hsupp` feeds `spoly`, while the multiplicative seam datum
`seamCoeff (ellLin g) 1 t₀` feeds the `M_range` slot.  Merging them degenerates `pretDistSq`
(the dyadic `a` has `aₚ = 0` at every `p ≤ X`).

**The two named binders (the honest residual).**

* `hSup` — the pointwise ball sup, `‖A_t(m)‖ ≤ S·m` uniformly on the ball.  UNMET: V2's
  ruling is that `halasz_ball_decay` is a scalar re-arrangement, not a landed sum bound, so
  this has no landed supply.  Its map is the open T1 pointwise frontier (`hpret` via SupF's
  B-ladder, `hbridge`, `hgrade` — HExit's CODA), or the `L²`-route alternative (a Vtail-style
  tent argument at the ball scale, dropping pointwise entirely).  Discipline: any `M` in a
  future exit is stated in FLOOR form per scale — never `M_range` at `X` for a bound obtained
  at `u`.
* `hU` — the `𝒰`-leg.  Supply: the §8.3 interior (L3-dyadic + L9-hZ + L12-herr), the next
  design block; the balance `θ = ρ/3` at `ρ = 1/(32e)` is `c₀`-existential, never a literal
  exponent.

`t₁` is obtained by `Real.lt_sInf_add_pos` (Nonempty only — no `BddBelow`), and NO stone is
spent on minimality: the grade is range-uniform, `pretDistSq(…, t₁) < M_range + 1` is all a
consumer needs. -/
theorem prop_A3_T1_row_split
    (g : ℕ → ℂ) (t₀ : ℝ) (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ)
    (X T S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT₀ : seamT0 X ≤ T) (hTX : T ≤ X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) :
    ∃ t₁ : ℝ,
      ((Real.log X) ^ (1 / 15 : ℝ) ≤ |t₁| ∧ |t₁| ≤ T + (Real.log X) ^ (1 / 16 : ℝ)
          ∧ |t₁| ≤ X)
        ∧ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            < M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T + 1
        ∧ ((∀ t : ℝ, |t - t₁| ≤ seamRad X → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m) →
            (∫ t in (seamAnn X T \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
                ‖spoly N a t‖ ^ 2) ≤ U →
            (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
              ≤ 2 * seamRad X * (2 * S) ^ 2
                + (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
                    ‖spoly N a t‖ ^ 2) + U) := by
  -- the `M_range` window is nonempty: `t = seamT0 X` is a witness (`hT₀` and `hTX` at work)
  have hT0nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 15 : ℝ) := Real.rpow_nonneg hL _
  have h16nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hL _
  have hT₀' : (Real.log X) ^ (1 / 15 : ℝ) ≤ T := hT₀
  have hwin : ({t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X}).Nonempty := by
    refine ⟨(Real.log X) ^ (1 / 15 : ℝ), ?_⟩
    have habs : |(Real.log X) ^ (1 / 15 : ℝ)| = (Real.log X) ^ (1 / 15 : ℝ) :=
      abs_of_nonneg hT0nn
    rw [Set.mem_setOf_eq, habs]
    exact ⟨le_rfl, by linarith, by linarith⟩
  -- the near-minimizer `t₁` (Nonempty only — no `BddBelow`, no minimality spent)
  obtain ⟨v, hvmem, hvlt⟩ :=
    Real.lt_sInf_add_pos (hwin.image
      (fun t : ℝ => pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X))
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨t₁, ht₁win, rfl⟩ := hvmem
  refine ⟨t₁, ht₁win, hvlt, ?_⟩
  intro hSup hU
  -- the objects
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hR : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  -- 1. the ball / far split
  have h1 := annulus_ball_far_split (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont X T t₁ hT
  -- 2. the ball leg
  have h2 : (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2)
      ≤ 2 * seamRad X * (2 * S) ^ 2 :=
    ball_leg_of_sup hX hXN hN2 hT hL hsupp hSup
  -- 3. the `𝒯tot / 𝒰` split of the far part
  have h3 := seam_TU_split (f := fb) (Pseq := Pseq) (Qseq := Qseq) (δ := δ) (J := Jb)
    (F := fun t : ℝ => ‖spoly N a t‖ ^ 2) hcont hT hR hRsub
  linarith [h1, h2, h3, hU]

/-- **Z6′ — the seam row at the crude far leg (`prop_A3_T1_row_split_crude`).**
`prop_A3_T1_row_split` with the `𝒯`-leg collapsed by the ONE interval monotonicity of
`far_leg_collapse` (never a `Σⱼ` of `J` copies — catch #253):

  `∫_{Ann} ‖spoly N a t‖²  ≤  2r·(2S)²  +  ∫_{-T}^{T} ‖spoly N a t‖²  +  U`.

This is the freeze's stated exit shape, and it is where the far leg's honest §8 size lives
(the mean-value masses are `(2T + 20N)`-grade — the `T`-structure of the row is entirely in
this leg and in `hU`, never in the ball).  It is deliberately CRUDE: at this collapse the
statement no longer beats the trivial `Ann ⊆ [-T,T]` monotonicity, so consumers wanting
content should take the sharp row above and sharpen the `𝒯`-leg by MR's per-block
treatment. -/
theorem prop_A3_T1_row_split_crude
    (g : ℕ → ℂ) (t₀ : ℝ) (a : ℕ → ℂ) (N : ℕ)
    (fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ)
    (X T S U : ℝ)
    (hL : 0 ≤ Real.log X) (hT₀ : seamT0 X ≤ T) (hTX : T ≤ X) (hT : 0 ≤ T)
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) :
    ∃ t₁ : ℝ,
      ((Real.log X) ^ (1 / 15 : ℝ) ≤ |t₁| ∧ |t₁| ≤ T + (Real.log X) ^ (1 / 16 : ℝ)
          ∧ |t₁| ≤ X)
        ∧ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            < M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T + 1
        ∧ ((∀ t : ℝ, |t - t₁| ≤ seamRad X → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m) →
            (∫ t in (seamAnn X T \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
                ‖spoly N a t‖ ^ 2) ≤ U →
            (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2)
              ≤ 2 * seamRad X * (2 * S) ^ 2
                + (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2) + U) := by
  obtain ⟨t₁, ht₁win, ht₁min, hrow⟩ :=
    prop_A3_T1_row_split g t₀ a N fb Pseq Qseq δ Jb X T S U hL hT₀ hTX hT hX hXN hN2 hsupp
  refine ⟨t₁, ht₁win, ht₁min, fun hSup hU => ?_⟩
  have hcont : Continuous fun t : ℝ => ‖spoly N a t‖ ^ 2 :=
    (continuous_spoly N a).norm.pow 2
  have hRsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hfar : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
      ‖spoly N a t‖ ^ 2) ≤ ∫ t in (-T)..T, ‖spoly N a t‖ ^ 2 :=
    far_leg_collapse hcont (fun _ => sq_nonneg _) hT (fun _ ht => hRsub ht.1)
  linarith [hrow hSup hU, hfar]

end Salt.MR
