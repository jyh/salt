/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Salt.MR.HalaszLambda
import Salt.MR.HalaszKernel

/-!
# HALASZ-INFRA — the S1' representation LADDER (`HalaszRep`)

Scoping attack on the campaign's single named residual, S1' (`prop21_analog`, the
frozen statement in `Salt/MR/HalaszSeam.lean`'s module docstring): the `α,β`
double-integral re-expression of `hat_contour_rep`'s integrand
`(∑' n, aₙ/n^s)·hatKernel(s)` into the four-series product
`𝒮(s-α-β)·𝓛(s+β)·P₋(s-β)·P₊(s+β)`.  The seam executor reduced this to two pieces:

* **(a) the shifted-Dirichlet identity** `∫₀^η -F'(s+α+β) dβ = F(s+α) - F(s+α+η)`
  in the `ellLin`/`lambdaLin` PRODUCT form — the integrand being exactly
  `L(λ_lin)(z)·L(ℓ)(z) = -F'(z)` by the LANDED `ellLin_lseries_deriv` (L4');
* **(b) the three-way Fubini** among the `(α,β)∈[0,η]²` double integral, the
  `tsum` over `n`, and the full-line `t`-integral.

The house's thesis (tested here, not trusted): every interchange is absolutely
convergent with an explicit dominating function, so the identity decomposes into
single-interchange rungs, each landable.  This file lands the rungs that land and
maps the walls for the rest.

## Rungs landed

* **Rung A — `shifted_dirichlet_ftc`** (part (a), FULLY LANDED, unconditional).
  The FTC-along-a-vertical-segment identity: for `‖g p‖ ≤ 1`, base `w` with
  `1 < re w`, and `0 ≤ η`,
  `∫ β in 0..η, L(λ_lin g)(w+β)·L(ℓ g)(w+β) = L(ℓ g) w - L(ℓ g)(w+η)`.
  Consumes `ellLin_lseries_deriv` (product-form derivative) + mathlib FTC-2
  (`integral_eq_sub_of_hasDerivAt`) + `HasDerivAt.comp_ofReal`.  Supporting
  surfaces `abscissa_ellLin_le_one`, `abscissa_lambdaLin_le_one`,
  `continuousOn_LSeries_shift`, `intervalIntegrable_lambdaLin_mul_ellLin` are the
  reusable dominating-function infrastructure.

See the executor NOTES (returned to the house) for the resistance map on rungs
(b) — the finite-measure `α↔β` swap, the `β↔n` and `β↔t` swaps, and the `t↔n`
swap already discharged inside `hat_contour_rep`.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation
open ArithmeticFunction

variable (g : ℕ → ℂ)

/-! ## Abscissa-of-absolute-convergence bounds (the ≤ 1 window) -/

/-- `ℓ = ellLin g` is bounded by `1`, so its abscissa of absolute convergence is `≤ 1`. -/
lemma abscissa_ellLin_le_one (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (ellLin g) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => ellLin_norm_le_one g hg n⟩

/-- `λ_lin = lambdaLin g` is `L`-summable on `1 < re s` (dominated by von Mangoldt). -/
lemma lambdaLin_LSeriesSummable (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (lambdaLin g) s := by
  have hΛ : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable, ← summable_norm_iff] at hΛ ⊢
  refine hΛ.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => LSeries.norm_term_le s ?_)
  calc ‖lambdaLin g n‖ ≤ ArithmeticFunction.vonMangoldt n := lambdaLin_norm_le g hg n
    _ = ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Since `λ_lin` is summable for every real abscissa `> 1`, its abscissa is `≤ 1`. -/
lemma abscissa_lambdaLin_le_one (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (lambdaLin g) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy =>
    lambdaLin_LSeriesSummable g hg (by simpa using hy)

/-! ## Continuity / interval-integrability of the shifted product (the dominating side) -/

/-- The vertical-segment restriction `β ↦ L(a)(w+β)` is continuous on `[0,η]` when the
abscissa of `a` is `≤ 1` and `1 < re w` (so `re(w+β) > 1` along the whole segment). -/
lemma continuousOn_LSeries_shift {a : ℕ → ℂ}
    (ha : LSeries.abscissaOfAbsConv a ≤ 1) {w : ℂ} (hw : 1 < w.re) {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (fun β : ℝ => LSeries a (w + (β : ℂ))) (Set.uIcc 0 η) := by
  have hmaps : Set.MapsTo (fun β : ℝ => w + (β : ℂ)) (Set.uIcc 0 η)
      {z : ℂ | LSeries.abscissaOfAbsConv a < z.re} := by
    intro x hx
    have hxnn : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    have hre1 : (1 : ℝ) < (w + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    exact ha.trans_lt (by exact_mod_cast hre1)
  exact (LSeries_differentiableOn a).continuousOn.comp
    (continuous_const.add Complex.continuous_ofReal).continuousOn hmaps

/-- The product integrand `β ↦ L(λ_lin)(w+β)·L(ℓ)(w+β)` is interval-integrable on `[0,η]`
(continuous, hence integrable) — the explicit dominating function for part (a). -/
lemma intervalIntegrable_lambdaLin_mul_ellLin (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {w : ℂ} (hw : 1 < w.re) {η : ℝ} (hη : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => LSeries (lambdaLin g) (w + (β : ℂ)) * LSeries (ellLin g) (w + (β : ℂ)))
      volume 0 η :=
  ((continuousOn_LSeries_shift (abscissa_lambdaLin_le_one g hg) hw hη).mul
    (continuousOn_LSeries_shift (abscissa_ellLin_le_one g hg) hw hη)).intervalIntegrable

/-! ## Rung A — the shifted-Dirichlet FTC (part (a) of the S1' reduction) -/

/-- **Rung A — the shifted-Dirichlet identity (part (a), LANDED).**  Along the vertical
segment `β ∈ [0,η]` the product-form log-derivative integrates by the fundamental theorem
of calculus:
`∫₀^η L(λ_lin g)(w+β)·L(ℓ g)(w+β) dβ = L(ℓ g) w - L(ℓ g)(w+η)`.
The integrand is exactly `-F'(w+β)` with `F = L(ℓ g)` by the LANDED product-form derivative
`ellLin_lseries_deriv` (L4'); FTC-2 on `β ↦ -F(w+β)` (whose derivative is the integrand)
gives the endpoint difference.  This discharges reduction piece (a) of the frozen S1'
statement unconditionally.  (No division by any L-series: `F`'s zero set never enters.) -/
theorem shifted_dirichlet_ftc (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {w : ℂ} (hw : 1 < w.re)
    {η : ℝ} (hη : 0 ≤ η) :
    ∫ β in (0 : ℝ)..η,
        LSeries (lambdaLin g) (w + (β : ℂ)) * LSeries (ellLin g) (w + (β : ℂ))
      = LSeries (ellLin g) w - LSeries (ellLin g) (w + (η : ℂ)) := by
  have habsE : LSeries.abscissaOfAbsConv (ellLin g) ≤ 1 := abscissa_ellLin_le_one g hg
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) η,
      HasDerivAt (fun β : ℝ => -(LSeries (ellLin g) (w + (β : ℂ))))
        (LSeries (lambdaLin g) (w + (x : ℂ)) * LSeries (ellLin g) (w + (x : ℂ))) x := by
    intro x hx
    have hxnn : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    have hre1 : (1 : ℝ) < (w + (x : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hre : LSeries.abscissaOfAbsConv (ellLin g) < ((w + (x : ℂ)).re : EReal) :=
      habsE.trans_lt (by exact_mod_cast hre1)
    have hbase : HasDerivAt (LSeries (ellLin g))
        (deriv (LSeries (ellLin g)) (w + (x : ℂ))) (w + (x : ℂ)) :=
      (LSeries_hasDerivAt hre).differentiableAt.hasDerivAt
    have hadd : HasDerivAt (fun z : ℂ => w + z) 1 (x : ℂ) := by
      simpa using (hasDerivAt_id (x : ℂ)).const_add w
    have hH : HasDerivAt (fun z : ℂ => LSeries (ellLin g) (w + z))
        (deriv (LSeries (ellLin g)) (w + (x : ℂ))) (x : ℂ) := by
      simpa [Function.comp_def] using hbase.comp (x : ℂ) hadd
    have hG : HasDerivAt (fun β : ℝ => LSeries (ellLin g) (w + (β : ℂ)))
        (deriv (LSeries (ellLin g)) (w + (x : ℂ))) x := hH.comp_ofReal
    have hnegG := hG.neg
    rw [ellLin_lseries_deriv g hg hre1] at hnegG
    exact hnegG
  have hint := intervalIntegrable_lambdaLin_mul_ellLin g hg hw hη
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [key]
  simp only [Complex.ofReal_zero, add_zero]
  ring

/-! ## Part (b) — the single-interchange Fubini rungs (seam-shaped, domination explicit)

The three-way Fubini of the S1' residual (the `(α,β)∈[0,η]²` double integral, the
`tsum` over `n`, and the full-line `t`-integral) decomposes into single-interchange
rungs.  The mathlib surfaces `intervalIntegral_integral_swap` (interval-integral
Fubini) and `integral_tsum_of_summable_integral_norm` (already consumed by
`hat_contour_rep` for the `t↔n` swap) discharge the machinery; each rung is gated
only on its explicit dominating hypothesis.  These are the reusable rungs. -/

/-- **Rung C (`β↔n`) — the interval-integral / `tsum` interchange.**  Over the finite
segment `[0,η]`, the `β`-integral commutes with the `n`-sum, given per-`n`
interval-integrability and the SUMMABLE interval-integral-norm dominating function
(the `∑ ‖aₙ‖(X/n)^c`-pattern of K2').  A `volume.restrict (Ioc 0 η)` instance of
`integral_tsum_of_summable_integral_norm`. -/
theorem interval_integral_tsum_swap {F : ℕ → ℝ → ℂ} {η : ℝ} (hη : 0 ≤ η)
    (hF_int : ∀ n, IntervalIntegrable (F n) volume 0 η)
    (hF_sum : Summable fun n => ∫ β in (0 : ℝ)..η, ‖F n β‖) :
    ∑' n, (∫ β in (0 : ℝ)..η, F n β) = ∫ β in (0 : ℝ)..η, ∑' n, F n β := by
  have hint : ∀ n, Integrable (F n) (volume.restrict (Set.Ioc (0 : ℝ) η)) :=
    fun n => (hF_int n).1
  have hsum' : Summable fun n =>
      ∫ β, ‖F n β‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) η)) := by
    refine hF_sum.congr (fun n => ?_)
    rw [intervalIntegral.integral_of_le hη]
  have hswap := integral_tsum_of_summable_integral_norm hint hsum'
  simp_rw [intervalIntegral.integral_of_le hη]
  exact hswap

/-- **Rung B (`α↔β`) — the finite-square Fubini interchange (domination DISCHARGED).**
On the finite square `[0,η]²` the two interval integrals commute for a jointly
continuous integrand — the dominating function is supplied for free by continuity on
the compact square (bounded ⇒ integrable against the finite product measure).  A
`volume.restrict (uIoc 0 η)` instance of mathlib's `intervalIntegral_integral_swap`.
This rung carries NO residual: for the seam it applies once the four-series product
integrand is exhibited as jointly continuous in `(α,β)` (which it is, off the poles). -/
theorem interval_integral_swap_continuous {f : ℝ → ℝ → ℂ}
    (hf : Continuous (Function.uncurry f)) {η : ℝ} (hη : 0 ≤ η) :
    ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, f α β
      = ∫ β in (0 : ℝ)..η, ∫ α in (0 : ℝ)..η, f α β := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) η ×ˢ Set.Icc (0 : ℝ) η) :=
    isCompact_Icc.prod isCompact_Icc
  have hIntK : IntegrableOn (Function.uncurry f) (Set.Icc (0 : ℝ) η ×ˢ Set.Icc (0 : ℝ) η)
      (volume : Measure (ℝ × ℝ)) :=
    hf.continuousOn.integrableOn_compact hcompact
  have hsub : Set.uIoc (0 : ℝ) η ×ˢ Set.uIoc (0 : ℝ) η
      ⊆ Set.Icc (0 : ℝ) η ×ˢ Set.Icc (0 : ℝ) η := by
    rw [Set.uIoc_of_le hη]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc (0 : ℝ) η)).prod
        (volume.restrict (Set.uIoc (0 : ℝ) η))) := by
    rw [Measure.prod_restrict]
    exact hIntK.mono_set hsub
  have hswap := intervalIntegral_integral_swap
    (μ := volume.restrict (Set.uIoc (0 : ℝ) η)) (f := f) hprod
  simp_rw [intervalIntegral.integral_of_le hη] at hswap ⊢
  rw [Set.uIoc_of_le hη] at hswap
  exact hswap

/-- **Rung D (`β↔t`) — the segment / full-line Fubini interchange.**  The finite-segment
`β`-integral commutes with the full-line `t`-integral, given product-integrability of the
integrand on `(volume.restrict (Ι 0 η)).prod volume` — the explicit dominating function
for the seam is the `1/|s(s+1)| ~ 1/t²` hat-kernel decay (`hat_mellin_bound`) times the
finite measure of `[0,η]`.  A `μ = volume` instance of `intervalIntegral_integral_swap`. -/
theorem interval_integral_line_swap {f : ℝ → ℝ → ℂ} {η : ℝ}
    (h_int : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc (0 : ℝ) η)).prod volume)) :
    ∫ β in (0 : ℝ)..η, ∫ t : ℝ, f β t = ∫ t : ℝ, ∫ β in (0 : ℝ)..η, f β t :=
  intervalIntegral_integral_swap (μ := volume) h_int

/-- **Rung E (`t↔n`) — the full-line integral / `tsum` interchange.**  Over the full line,
the `t`-integral commutes with the `n`-sum, given per-`n` integrability and the SUMMABLE
line-integral-norm dominating function (the K2' `∑ ‖aₙ‖(X/n)^c` pattern).  This is exactly
the swap `hat_contour_rep` already discharges internally; here it is isolated as a reusable
rung — a `μ = volume` instance of `integral_tsum_of_summable_integral_norm`. -/
theorem line_integral_tsum_swap {F : ℕ → ℝ → ℂ}
    (hF_int : ∀ n, Integrable (F n) (volume : Measure ℝ))
    (hF_sum : Summable fun n => ∫ t : ℝ, ‖F n t‖) :
    ∑' n, (∫ t : ℝ, F n t) = ∫ t : ℝ, ∑' n, F n t :=
  integral_tsum_of_summable_integral_norm hF_int hF_sum

end Salt.MR
