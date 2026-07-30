/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LFunctionInvShallow

/-!
# ⟦THE MIRROR⟧ — the χ-twisted Möbius rate: `MobiusRateClose` re-run at `L(s,χ)`

The closing wave of the KMT port's centerpiece.  `Salt/MR/MobiusChiRate.lean` landed the
twisted-Perron SPINE (`mmu1Chi_eq_integral`, in `1/L` form at the shifted height) and the
REGION discharge (`LFunction_no_zero_in_box` / `_in_shifted_box`);
`Salt/MR/LFunctionInvShallow.lean` landed the ANALYTIC stone
(`lFunctionInvShallowVkSharp_holds`, the shallow `1/L` bound at the ratified sharp width
`vkShallowWidthSharp`).  What is left is exactly the mechanical mirror of
`Salt.SW.MobiusRateClose`: the contour shift, the budget, the de-smoothing — and that is this
file.

## The three phases, and what each mirrors

1. **§1 EDGES** (`mmu1Chi_contour_shift`) — the mirror of `Salt.SW.mmu1_contour_shift`.  The
   contour `Re s = c` is shifted onto the box `[σ₀, c] × [−T, T]`; because the integrand's
   L-factor is read at the SHIFTED argument `s − it`, the box's L-heights run over
   `[−T − t, T − t]`, all of size `≤ |t| + T`.  The statement is parametrized by an ANALYTIC
   CARRIER `g` agreeing with `s ↦ (L(s − it, χ⁻¹))⁻¹` on the `c`-line: for `χ ≠ 1` the carrier
   IS that inverse (`L(·,χ⁻¹)` is entire), and the principal row's carrier is the
   pole-normalized continuation (§5).  NO residue term, exactly as in the `q = 1` route.

2. **§2 BUDGET** (`mmu1Chi_rate_of_pinned`) — the mirror of `mmu1_shift_decay` +
   `mmuRate_smoothed`, at the PINNED parameters
   `L = log x`, `s = L^{1/10}`, `T = e^s`, `c = 1 + 1/L`, `H = 2x`,
   `σ₀ = 1 − shWidth c₅ H`, `shWidth c₅ H = c₅/((log H)^{3/4}(log log H)⁶)`.
   The `(log log H)⁶ = 4 + 2` is the sharp width's own price, re-read after the `q`-gate is
   spent: `q ≤ (log x)^{12}` turns `(log q + 1)² ≤ 169 (log log H)²` (§4), which is exactly
   the two extra loglogs.  The three edge terms are absorbed by `Salt.SW.pow_exp_absorb`, and
   the quasi-power `exp(−c L^{1/4}/(log L)⁶)` of the left edge beats every fixed `L^{−A}`
   through `L^{1/20} ≥ (log L)⁶` (eventually) — the same `tendsto_rpow_mul_exp_neg_mul` step
   the `q = 1` route uses.

3. **§3 DE-SMOOTH** (`mmuChiRate_of_smoothed`) — the mirror of `mmuRate_of_smoothed`, in ℂ
   (`‖·‖` for `|·|`; the twisted datum is not real).  Two-point Riesz de-smoothing at width
   `h = Y/(log Y)^{A+1}`, remainder `≤ (h+1)²` from `‖μ(n)χ̄(n)n^{it}‖ ≤ 1`.

§4 assembles the `χ ≠ 1` row (D1) and §5 records the principal row's residue.

## The traps, and where each is paid

* **the sharp width** — `vkShallowWidthSharp`, never `vkShallowWidth`: §4's `c₅` carries BOTH
  extra factors (`(log q+1)²` and `(log log H)⁴`), and the `q`-gate converts the first into the
  fifth and sixth loglog.
* **the four log scales** — `L = log x` (contour), `log H` with `H = 2x` (the L-function's
  height scale, `≤ 2L`), `log log H` (the region's third scale), `s = L^{1/10}` (truncation).
  Every step states which one it is at.
* **the height gate `|t| ≤ y`** — the box's L-heights are `≤ |t| + T ≤ x + T ≤ 2x = H`, which
  is where `H = 2x` comes from; the shallow bound and the region are both read AT `H`.
* **the carve-out** — the ξ₁/real-zero row rides in as the named hypothesis, in the STRONG
  `Re < 1/2` form (`carve_of_half`), i.e. exactly the shape wave P-7's Siegel fold delivers.
  Nothing here folds it.
-/

open MeasureTheory Complex Set ArithmeticFunction Filter DirichletCharacter
open scoped LSeries.notation ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace Salt.MR

/-! ## §1 — the residue-free twisted contour shift -/

set_option maxHeartbeats 1600000 in
-- The assembly threads the twisted Perron identity, the Goursat split and four edge/tail
-- integral estimates through one `set`-heavy proof term, exactly as its `q = 1` twin does.
/-- **§1 — THE TWISTED CONTOUR SHIFT.**  For `x ≥ 1`, an abscissa `c > 1`, a truncation height
`T > 0` and a shallow abscissa `0 < σ₀ < c`, let `g` be a carrier which

* agrees with `s ↦ (L(s − it, χ⁻¹))⁻¹` on the `c`-line (`hgcline`),
* is continuous along the `c`-line (`hgcont`),
* is analytic on the closed box `[σ₀, c] × [−T, T]` (`hgana`), and
* is bounded by `Bbox` on that box (`hgbox`).

Then the smoothed twisted Möbius mean obeys the explicit contour bound: two horizontal edges
`≤ (c−σ₀)·Bbox·x^c/T²` each, the left edge `≤ Bbox·x^{σ₀}·π/σ₀`, and the truncation tail
`≤ (1 + 1/(c−1))·x^c·(2/T)` — the tail constant is the `c`-line Dirichlet bound
(`norm_LFunction_inv_shifted_cline_le`), UNIFORM in the height, so the `log⁷` tail friction of
the ζ route never appears.  NO residue term: the carrier is analytic on the whole box. -/
theorem mmu1Chi_contour_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {x c T σ₀ Bbox : ℝ} {g : ℂ → ℂ}
    (hx : 1 ≤ x) (hc1 : 1 < c) (hT : 0 < T) (hσ₀pos : 0 < σ₀) (hσ₀c : σ₀ < c)
    (hBbox : 0 ≤ Bbox)
    (hgcline : ∀ v : ℝ, g ((c : ℂ) + (v : ℂ) * I)
        = (LFunction χ⁻¹ ((c : ℂ) + ((v - t : ℝ) : ℂ) * I))⁻¹)
    (hgcont : Continuous fun v : ℝ => g ((c : ℂ) + (v : ℂ) * I))
    (hgana : DifferentiableOn ℂ g
        (Salt.SW.closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I)))
    (hgbox : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → ‖g s‖ ≤ Bbox) :
    ‖Mmu1Chi χ t x‖ ≤ (1 / (2 * Real.pi)) *
      (2 * (c - σ₀) * Bbox * x ^ c / T ^ 2
        + Bbox * x ^ σ₀ * (Real.pi / σ₀)
        + (1 + 1 / (c - 1)) * x ^ c * (2 / T)) := by
  classical
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hcpos : (0 : ℝ) < c := by linarith
  have hcm1 : (0 : ℝ) < c - 1 := by linarith
  have hclineC : (0 : ℝ) ≤ 1 + 1 / (c - 1) := by positivity
  -- the `c`-line bound on the carrier
  have hcline : ∀ v : ℝ, ‖g ((c : ℂ) + (v : ℂ) * I)‖ ≤ 1 + 1 / (c - 1) := by
    intro v
    rw [hgcline v]
    exact norm_LFunction_inv_shifted_cline_le χ hc1 v t
  -- the integrand and its norm
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ s / (s * (s + 1)) * g s with hF
  have hFnorm : ∀ s : ℂ, ‖F s‖ = x ^ s.re * ‖(s * (s + 1))⁻¹‖ * ‖g s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, div_eq_mul_inv, ← norm_inv]
  -- integrability on the `c`-line
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + (v : ℂ) * I)) := by
    have hdenne : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) * (((c : ℂ) + (v : ℂ) * I) + 1) ≠ 0 :=
      fun v => mul_ne_zero (Salt.SW.s_ne_zero hcpos v) (Salt.SW.s1_ne_zero hcpos v)
    have hFcont : Continuous (fun v : ℝ => F ((c : ℂ) + (v : ℂ) * I)) := by
      simp only [hF]
      apply Continuous.mul
      · apply Continuous.div
        · exact (by fun_prop : Continuous fun v : ℝ => (c : ℂ) + (v : ℂ) * I).const_cpow
            (Or.inl hxC)
        · fun_prop
        · exact hdenne
      · exact hgcont
    refine Integrable.mono'
      ((Salt.SW.integrable_inv_c_sq_add_sq hcpos).const_mul (x ^ c * (1 + 1 / (c - 1))))
      hFcont.aestronglyMeasurable ?_
    filter_upwards with v
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    have h2 : ‖(((c : ℂ) + (v : ℂ) * I) * (((c : ℂ) + (v : ℂ) * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
      Salt.SW.norm_inv_denom_le hcpos v
    have hxcnn : (0 : ℝ) ≤ x ^ c := by positivity
    rw [hFnorm, hre]
    calc x ^ c * ‖(((c : ℂ) + (v : ℂ) * I) * (((c : ℂ) + (v : ℂ) * I) + 1))⁻¹‖
            * ‖g ((c : ℂ) + (v : ℂ) * I)‖
        ≤ x ^ c * (c ^ 2 + v ^ 2)⁻¹ * (1 + 1 / (c - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 hxcnn) (hcline v) (norm_nonneg _)
            (by positivity)
      _ = x ^ c * (1 + 1 / (c - 1)) * (c ^ 2 + v ^ 2)⁻¹ := by ring
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  have hFana : DifferentiableOn ℂ F (Salt.SW.closedRect zc wc) := by
    intro s hs
    have hs' := hs
    rw [Salt.SW.closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm] at hs'
    rw [Set.uIcc_of_le hσ₀c.le] at hs'
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs'
    obtain ⟨hsre, _hsim⟩ := hs'
    simp only [Set.mem_Icc] at hsre
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith [hsre.1]
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1]
    have hker : DifferentiableAt ℂ (fun z => (x : ℂ) ^ z / (z * (z + 1))) s := by
      apply DifferentiableAt.div
      · exact differentiableAt_id.const_cpow (Or.inl hxC)
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    exact hker.differentiableWithinAt.mul (hgana s hs)
  -- Goursat rearrangement
  have hgour := Salt.SW.rectBI_right_split hFana
  rw [hzc_re, hzc_im, hwc_re, hwc_im] at hgour
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  have hRnorm : ‖RIGHT‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- the Perron bridge
  have hbridge : Mmu1Chi χ t x = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I) := by
    rw [mmu1Chi_eq_integral χ t hx hc1]
    refine congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only [hF]
    rw [hgcline v]
  -- truncation split
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + (v : ℂ) * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + (v : ℂ) * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  set Cbnd : ℝ := x ^ c * Bbox / T ^ 2 with hCbnd
  have hxcpos : (0 : ℝ) < x ^ c := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  -- pointwise `F`-norm bound on a horizontal edge (Im = ±T)
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c,
      ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀pos]
    have hlogb : ‖g ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Bbox :=
      hgbox _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim, hτ])
    have hden : ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
        ≤ (u ^ 2 + τ ^ 2)⁻¹ := Salt.SW.norm_inv_denom_le hupos τ
    have hττ : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    have hxexp : x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx (by linarith [hu.2])
    have hinvle : (u ^ 2 + τ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg u])
    rw [hFnorm, hsre]
    calc x ^ u * ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
            * ‖g ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ x ^ u * (u ^ 2 + τ ^ 2)⁻¹ * Bbox :=
          mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
            (norm_nonneg _) (by positivity)
      _ ≤ x ^ c * (T ^ 2)⁻¹ * Bbox :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hxexp hinvle (by positivity) (by positivity)) hBbox
      _ = Cbnd := by rw [hCbnd]; ring
  have hTOPb : ‖TOPI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hTOPI]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz T (abs_of_pos hT))
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hBOTb : ‖BOTI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hBOTI]
    have hnegT : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hT]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz (-T) hnegT)
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  -- left edge
  have hLEFTb : ‖LEFT‖ ≤ Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (Salt.SW.integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hmapsto : Set.MapsTo (fun v : ℝ => (σ₀ : ℂ) + (v : ℂ) * I) (Set.uIcc (-T) T)
        (Salt.SW.closedRect zc wc) := by
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T), Set.mem_Icc] at hv
      rw [Salt.SW.closedRect, hzc_re, hzc_im, hwc_re, hwc_im, Complex.mem_reProdIm,
        Set.uIcc_of_le hσ₀c.le, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
      refine ⟨?_, ?_⟩
      · have hre : ((σ₀ : ℂ) + (v : ℂ) * I).re = σ₀ := by simp
        rw [Set.mem_Icc, hre]
        exact ⟨le_refl σ₀, hσ₀c.le⟩
      · have him : ((σ₀ : ℂ) + (v : ℂ) * I).im = v := by simp
        rw [Set.mem_Icc, him]
        exact hv
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + (v : ℂ) * I)) volume (-T) T :=
      (hFana.continuousOn.comp
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
        hmapsto).intervalIntegrable
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hBbox (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ ≤ Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := abs_le.mpr ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + (v : ℂ) * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + (v : ℂ) * I).im = v := by simp
      have hlogb : ‖g ((σ₀ : ℂ) + (v : ℂ) * I)‖ ≤ Bbox :=
        hgbox _ (by rw [hsre]) (by rw [hsre]; linarith) (by rw [hsim]; exact hvT)
      have hden : ‖(((σ₀ : ℂ) + (v : ℂ) * I) * (((σ₀ : ℂ) + (v : ℂ) * I) + 1))⁻¹‖
          ≤ (σ₀ ^ 2 + v ^ 2)⁻¹ := Salt.SW.norm_inv_denom_le hσ₀pos v
      rw [hFnorm, hsre]
      calc x ^ σ₀ * ‖(((σ₀ : ℂ) + (v : ℂ) * I) * (((σ₀ : ℂ) + (v : ℂ) * I) + 1))⁻¹‖
              * ‖g ((σ₀ : ℂ) + (v : ℂ) * I)‖
          ≤ x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ * Bbox :=
            mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
              (norm_nonneg _) (by positivity)
        _ = Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    calc ‖∫ v in (-T)..T, F ((σ₀ : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v in (-T)..T, ‖F ((σ₀ : ℂ) + (v : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-T)..T, Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith)
            hFleft_ii.norm hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, Bbox * x ^ σ₀ * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
          rw [integral_const_mul, Salt.SW.integral_inv_sq_add hσ₀pos]
  -- tail bound on the vertical `Re = c` line
  have hcompl_meas : MeasurableSet (Set.Ioc (-T) T)ᶜ := measurableSet_Ioc.compl
  have hTAILb : ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + (v : ℂ) * I)‖
      ≤ (1 + 1 / (c - 1)) * x ^ c * (2 / T) := by
    have hFint_on : IntegrableOn (fun v : ℝ => F ((c : ℂ) + (v : ℂ) * I))
        (Set.Ioc (-T) T)ᶜ := hFint.integrableOn
    have hg_int : IntegrableOn
        (fun v : ℝ => (1 + 1 / (c - 1)) * x ^ c * (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
      ((Salt.SW.integrable_inv_c_sq_add_sq hcpos).const_mul _).integrableOn
    calc ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, ‖F ((c : ℂ) + (v : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, (1 + 1 / (c - 1)) * x ^ c * (c ^ 2 + v ^ 2)⁻¹ := by
          refine setIntegral_mono_on hFint_on.norm hg_int hcompl_meas ?_
          intro v _
          have hsre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
          have hden : ‖(((c : ℂ) + (v : ℂ) * I) * (((c : ℂ) + (v : ℂ) * I) + 1))⁻¹‖
              ≤ (c ^ 2 + v ^ 2)⁻¹ := Salt.SW.norm_inv_denom_le hcpos v
          rw [hFnorm, hsre]
          calc x ^ c * ‖(((c : ℂ) + (v : ℂ) * I) * (((c : ℂ) + (v : ℂ) * I) + 1))⁻¹‖
                  * ‖g ((c : ℂ) + (v : ℂ) * I)‖
              ≤ x ^ c * (c ^ 2 + v ^ 2)⁻¹ * (1 + 1 / (c - 1)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) (hcline v)
                  (norm_nonneg _) (by positivity)
            _ = (1 + 1 / (c - 1)) * x ^ c * (c ^ 2 + v ^ 2)⁻¹ := by ring
      _ = (1 + 1 / (c - 1)) * x ^ c * ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ := by
          rw [integral_const_mul]
      _ ≤ (1 + 1 / (c - 1)) * x ^ c * (2 / T) :=
          mul_le_mul_of_nonneg_left (Salt.SW.tail_lorentzian_le hcpos hT) (by positivity)
  -- assemble
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + Bbox * x ^ σ₀ * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  rw [hbridge, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [htrunc]
  calc ‖RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + (v : ℂ) * I)‖
      ≤ ‖RIGHT‖ + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + (v : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀))
          + (1 + 1 / (c - 1)) * x ^ c * (2 / T) := by
        have h1 : ‖RIGHT‖
            ≤ 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * Bbox * x ^ c / T ^ 2 + Bbox * x ^ σ₀ * (Real.pi / σ₀)
          + (1 + 1 / (c - 1)) * x ^ c * (2 / T) := by ring

/-! ## §2 — the budget at the PINNED parameters

`L = log x`, `s = L^{1/10}`, `T = e^s`, `c = 1 + 1/L`, `H = 2x`, `σ₀ = 1 − pinW c₅ H`.  The
one arithmetic fact that makes the width work is
`L·pinW c₅ (2x) ≥ (c₅/128)·L^{1/5}`, from `log(2x) ≤ 2L`, `log log(2x) ≤ 2 log L` and the
eventual `(log L)⁶ ≤ L^{1/20}` — a QUASI-POWER saving, which beats every fixed `L^{−A}`.  The
truncation terms carry `e^{−s}` and are the binding ones; both are absorbed by the same
`x^r·e^{−bx} → 0` step the `q = 1` route uses. -/

/-- The pinned truncation height `T(x) = exp((log x)^{1/10})`. -/
def pinT (x : ℝ) : ℝ := Real.exp (Real.log x ^ ((1 : ℝ) / 10))

/-- The pinned shallow width at height `H`: the sharp χ-VK width with the conductor gate
already spent — `(log q + 1)² ≤ 169(log log H)²` at `q ≤ (log x)^{12}` turns
`vkShallowWidthSharp`'s `(log log H)⁴` into `(log log H)⁶`. -/
def pinW (c₅ H : ℝ) : ℝ :=
  c₅ / (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (6 : ℕ))

set_option maxHeartbeats 4000000 in
-- The budget threads the four log scales (`L`, `log 2x`, `log log 2x`, `s = L^{1/10}`), the
-- width's quasi-power lower bound and three edge absorptions through one `calc`; the
-- elaborator needs headroom past the default, exactly as `Salt.SW.mmu1_shift_decay` does.
/-- **§2 — THE BUDGET.**  Given the contour bound at the pinned parameters (`hshift`), the
smoothed twisted mean satisfies `‖M₁_{μχ̄}(t;x)‖ ≤ C·x/(log x)^A` for every fixed `A > 0`, with
`C` and the threshold depending only on `(c₅, K, m, A)` — in particular UNIFORMLY in `q`, `χ`
and `t`, which is what `MmuChiRate`'s quantifier order demands. -/
theorem mmu1Chi_rate_of_pinned {c₅ K X₁ : ℝ} {m : ℕ}
    (hc₅0 : 0 < c₅) (hc₅1 : c₅ ≤ 1) (hK1 : 1 ≤ K)
    (P : (q : ℕ) → DirichletCharacter ℂ q → Prop)
    (hshift : ∀ x : ℝ, X₁ ≤ x → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
      (q : ℝ) ≤ Real.log x ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ x →
        ‖Mmu1Chi χ t x‖ ≤ (1 / (2 * Real.pi)) *
          (2 * ((1 + 1 / Real.log x) - (1 - pinW c₅ (2 * x)))
                * (K * Real.log (2 * x) ^ m) * x ^ (1 + 1 / Real.log x) / pinT x ^ 2
            + (K * Real.log (2 * x) ^ m) * x ^ (1 - pinW c₅ (2 * x))
                * (Real.pi / (1 - pinW c₅ (2 * x)))
            + (Real.log x + 1) * x ^ (1 + 1 / Real.log x) * (2 / pinT x))) :
    ∀ A : ℝ, 0 < A → ∃ (C x₀ : ℝ), 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
        (q : ℝ) ≤ Real.log x ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ x →
          ‖Mmu1Chi χ t x‖ ≤ C * x / Real.log x ^ A := by
  intro A hA
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hπ := Real.pi_pos
  have he1 := Real.exp_pos 1
  set dd : ℝ := c₅ / 128 with hdddef
  have hdd0 : 0 < dd := by rw [hdddef]; positivity
  set aC : ℝ := (11 / 5) * K * 2 ^ m * Real.exp 1 + 4 * Real.exp 1 with haC
  set bC : ℝ := K * 2 ^ m * (10 * Real.pi / 9) with hbC
  have haC0 : 0 < aC := by
    rw [haC]
    have h1 : (0 : ℝ) < 11 / 5 * K * 2 ^ m * Real.exp 1 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hK0) h2m) he1
    have h2 : (0 : ℝ) < 4 * Real.exp 1 := by positivity
    linarith
  have hbC0 : 0 < bC := by
    rw [hbC]
    exact mul_pos (mul_pos hK0 h2m) (by positivity)
  set Ctot : ℝ := (1 / (2 * Real.pi)) * (aC + bC) with hCtot
  have hCtot0 : 0 < Ctot := by
    rw [hCtot]; exact mul_pos (by positivity) (by linarith)
  -- the four eventual conditions
  have hE2 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (Real.log x) ^ (6 : ℕ) ≤ Real.log x ^ ((1 : ℝ) / 20) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 20) (6 : ℝ) (by norm_num)
    have hev : ∀ᶠ Lv : ℝ in Filter.atTop,
        Real.log Lv ^ (6 : ℕ) ≤ Lv ^ ((1 : ℝ) / 20) := by
      filter_upwards [hlo.def (by norm_num : (0 : ℝ) < 1),
        Filter.eventually_ge_atTop (Real.exp 1)] with Lv hLv hLv1
      have hLvpos : (0 : ℝ) < Lv := lt_of_lt_of_le (Real.exp_pos 1) hLv1
      have hlogLv1 : (1 : ℝ) ≤ Real.log Lv := (Real.le_log_iff_exp_le hLvpos).mpr hLv1
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
        abs_of_nonneg (Real.rpow_nonneg hLvpos.le _), one_mul] at hLv
      have hcast : Real.log Lv ^ (6 : ℕ) = Real.log Lv ^ (6 : ℝ) := by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast]; exact hLv
    exact Real.tendsto_log_atTop.eventually hev
  have htend10 : Filter.Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have htend5 : Filter.Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 5))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp Real.tendsto_log_atTop
  have hE3 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ ((m : ℝ) + 1 + A) * Real.exp (-(Real.log x ^ ((1 : ℝ) / 10))) ≤ 1 := by
    have h0 : Filter.Tendsto (fun x : ℝ =>
        Real.log x ^ ((m : ℝ) + 1 + A) * Real.exp (-(Real.log x ^ ((1 : ℝ) / 10))))
        Filter.atTop (nhds 0) := by
      have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (10 * ((m : ℝ) + 1 + A)) 1 one_pos).comp htend10
      refine hbase.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul hlog0,
        show (1 : ℝ) / 10 * (10 * ((m : ℝ) + 1 + A)) = (m : ℝ) + 1 + A by ring, neg_mul, one_mul]
    filter_upwards [h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact hx
  have hE4 : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ ((m : ℝ) + 1 + A) * Real.exp (-(dd * Real.log x ^ ((1 : ℝ) / 5))) ≤ 1 := by
    have h0 : Filter.Tendsto (fun x : ℝ =>
        Real.log x ^ ((m : ℝ) + 1 + A) * Real.exp (-(dd * Real.log x ^ ((1 : ℝ) / 5))))
        Filter.atTop (nhds 0) := by
      have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (5 * ((m : ℝ) + 1 + A)) dd hdd0).comp htend5
      refine hbase.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul hlog0,
        show (1 : ℝ) / 5 * (5 * ((m : ℝ) + 1 + A)) = (m : ℝ) + 1 + A by ring, neg_mul]
    filter_upwards [h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact hx
  suffices h : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
        (q : ℝ) ≤ Real.log x ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ x →
          ‖Mmu1Chi χ t x‖ ≤ Ctot * x / Real.log x ^ A by
    rw [Filter.eventually_atTop] at h
    obtain ⟨x₀, hx₀⟩ := h
    exact ⟨Ctot, x₀, hCtot0, hx₀⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp 100)),
    Filter.eventually_ge_atTop X₁, hE2, hE3, hE4] with x hxE hxX1 hx2 hx3 hx4
  intro q _ χ hP hq t ht
  -- ⟦scale 1⟧ `L = log x`
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxE
  set Lg : ℝ := Real.log x with hLdef
  have hL100 : (101 : ℝ) ≤ Lg := by
    have h : Real.exp 100 ≤ Real.log x := by
      rw [← Real.log_exp (Real.exp 100)]
      exact Real.log_le_log (Real.exp_pos _) hxE
    rw [hLdef]; linarith
  have hLpos : (0 : ℝ) < Lg := by linarith
  have hL1 : (1 : ℝ) ≤ Lg := by linarith
  have hlogL1 : (1 : ℝ) ≤ Real.log Lg := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogL0 : (0 : ℝ) < Real.log Lg := by linarith
  -- ⟦scale 2⟧ `L₂ = log(2x)`, and ⟦scale 3⟧ `ℓ₂ = log L₂`
  have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hL2eq : Real.log (2 * x) = Real.log 2 + Lg := by
    rw [hLdef, Real.log_mul (by norm_num) hxpos.ne']
  have hL2lo : Lg ≤ Real.log (2 * x) := by
    rw [hL2eq]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hL2hi : Real.log (2 * x) ≤ 2 * Lg := by rw [hL2eq]; linarith
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  set l2 : ℝ := Real.log (Real.log (2 * x)) with hl2def
  have hl2lo : Real.log Lg ≤ l2 := by rw [hl2def]; exact Real.log_le_log hLpos hL2lo
  have hl2hi : l2 ≤ 2 * Real.log Lg := by
    rw [hl2def]
    calc Real.log (Real.log (2 * x)) ≤ Real.log (2 * Lg) :=
          Real.log_le_log hL2pos hL2hi
      _ = Real.log 2 + Real.log Lg := by rw [Real.log_mul (by norm_num) hLpos.ne']
      _ ≤ 2 * Real.log Lg := by linarith
  have hl21 : (1 : ℝ) ≤ l2 := le_trans hlogL1 hl2lo
  -- the width, and its two-sided estimate
  set R2 : ℝ := Real.log (2 * x) ^ ((3 : ℝ) / 4) with hR2def
  set RL : ℝ := Lg ^ ((3 : ℝ) / 4) with hRLdef
  have hRL0 : (0 : ℝ) < RL := by rw [hRLdef]; exact Real.rpow_pos_of_pos hLpos _
  have hR20 : (0 : ℝ) < R2 := by rw [hR2def]; exact Real.rpow_pos_of_pos hL2pos _
  have hRlo : RL ≤ R2 := by
    rw [hRLdef, hR2def]; exact Real.rpow_le_rpow hLpos.le hL2lo (by norm_num)
  have hRhi : R2 ≤ 2 * RL := by
    rw [hR2def, hRLdef]
    calc Real.log (2 * x) ^ ((3 : ℝ) / 4) ≤ (2 * Lg) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow hL2pos.le hL2hi (by norm_num)
      _ = 2 ^ ((3 : ℝ) / 4) * Lg ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) hLpos.le
      _ ≤ 2 * Lg ^ ((3 : ℝ) / 4) := by
          have h2 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
            calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          nlinarith [Real.rpow_pos_of_pos hLpos ((3 : ℝ) / 4)]
  have hden0 : (0 : ℝ) < R2 * l2 ^ (6 : ℕ) :=
    mul_pos hR20 (pow_pos (by linarith : (0 : ℝ) < l2) 6)
  set w : ℝ := pinW c₅ (2 * x) with hwset
  have hwdef : w = c₅ / (R2 * l2 ^ (6 : ℕ)) := by
    rw [hwset, pinW, ← hR2def, ← hl2def]
  have hw0 : 0 < w := by rw [hwdef]; exact div_pos hc₅0 hden0
  -- the width is small: `w ≤ 1/RL ≤ 1/10`
  have hRL10 : (10 : ℝ) ≤ RL := by
    rw [hRLdef]
    have h1 : (101 : ℝ) ^ ((3 : ℝ) / 4) ≤ Lg ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hL100 (by norm_num)
    have h2 : (10 : ℝ) ≤ (101 : ℝ) ^ ((3 : ℝ) / 4) := by
      have h3 : (10 : ℝ) = (10 ^ (4 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [show ((10 : ℝ) ^ (4 : ℕ)) = (10 : ℝ) ^ (4 : ℝ) by
              rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
          ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h3]
      have h4 : ((10 : ℝ) ^ (4 : ℕ)) ≤ (101 : ℝ) ^ (3 : ℕ) := by norm_num
      calc ((10 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ ((101 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) h4 (by norm_num)
        _ = (101 : ℝ) ^ ((3 : ℝ) / 4) := by
            rw [show ((101 : ℝ) ^ (3 : ℕ)) = (101 : ℝ) ^ (3 : ℝ) by
                  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
              ← Real.rpow_mul (by norm_num)]
            norm_num
    linarith
  have hwsmall : w ≤ 1 / 10 := by
    rw [hwdef, div_le_div_iff₀ hden0 (by norm_num)]
    have h1 : (1 : ℝ) ≤ l2 ^ (6 : ℕ) := one_le_pow₀ hl21
    have hR2ge : (10 : ℝ) ≤ R2 := le_trans hRL10 hRlo
    nlinarith [hR2ge, h1, hc₅1]
  set σ₀ : ℝ := 1 - w with hσ₀def
  have hσ₀9 : (9 : ℝ) / 10 ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  -- ⟦the quasi-power saving⟧ `L·w ≥ dd·L^{1/5}`
  have hLw : dd * Lg ^ ((1 : ℝ) / 5) ≤ Lg * w := by
    have hl26 : l2 ^ (6 : ℕ) ≤ 64 * Real.log Lg ^ (6 : ℕ) := by
      have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ l2) hl2hi 6
      calc l2 ^ (6 : ℕ) ≤ (2 * Real.log Lg) ^ (6 : ℕ) := h
        _ = 64 * Real.log Lg ^ (6 : ℕ) := by ring
    have hdenle : R2 * l2 ^ (6 : ℕ) ≤ 128 * (RL * Lg ^ ((1 : ℝ) / 20)) := by
      have h1 : R2 * l2 ^ (6 : ℕ) ≤ (2 * RL) * (64 * Real.log Lg ^ (6 : ℕ)) := by
        refine mul_le_mul hRhi hl26 (by positivity) (by linarith [hRL0])
      have h2 : Real.log Lg ^ (6 : ℕ) ≤ Lg ^ ((1 : ℝ) / 20) := by
        rw [hLdef] at hx2 ⊢; exact hx2
      nlinarith [h1, h2, hRL0, Real.rpow_pos_of_pos hLpos ((1 : ℝ) / 20)]
    have hLratio : Lg / (RL * Lg ^ ((1 : ℝ) / 20)) = Lg ^ ((1 : ℝ) / 5) := by
      have hne : Lg ^ ((4 : ℝ) / 5) ≠ 0 := (Real.rpow_pos_of_pos hLpos _).ne'
      rw [hRLdef, ← Real.rpow_add hLpos,
        show (3 : ℝ) / 4 + (1 : ℝ) / 20 = (4 : ℝ) / 5 by norm_num, div_eq_iff hne,
        ← Real.rpow_add hLpos, show (1 : ℝ) / 5 + (4 : ℝ) / 5 = 1 by norm_num, Real.rpow_one]
    have hstep : Lg * c₅ / (128 * (RL * Lg ^ ((1 : ℝ) / 20))) ≤ Lg * w := by
      rw [hwdef]
      rw [div_le_iff₀ (by positivity), mul_comm (Lg : ℝ) (c₅ / (R2 * l2 ^ (6 : ℕ)))]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hden0]
      nlinarith [hdenle, hc₅0, mul_pos hLpos hc₅0, hRL0,
        Real.rpow_pos_of_pos hLpos ((1 : ℝ) / 20)]
    refine le_trans (le_of_eq ?_) hstep
    have hRLne : RL ≠ 0 := hRL0.ne'
    have h20ne : Lg ^ ((1 : ℝ) / 20) ≠ 0 := (Real.rpow_pos_of_pos hLpos _).ne'
    rw [hdddef, ← hLratio]
    field_simp
  -- the pinned truncation height, and the two exponential shapes
  set sg : ℝ := Lg ^ ((1 : ℝ) / 10) with hsgdef
  have hsg0 : (0 : ℝ) < sg := by rw [hsgdef]; exact Real.rpow_pos_of_pos hLpos _
  have hTdef : pinT x = Real.exp sg := by rw [pinT, hsgdef, hLdef]
  have hT2 : pinT x ^ 2 = Real.exp (2 * sg) := by
    rw [hTdef, sq, ← Real.exp_add]; congr 1; ring
  have hTinv : (2 : ℝ) / pinT x = 2 * Real.exp (-sg) := by
    rw [hTdef, div_eq_mul_inv, ← Real.exp_neg]
  have hxc : x ^ (1 + 1 / Lg) = Real.exp 1 * x := by
    have hxinvL : x ^ (1 / Lg) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hxpos, ← hLdef, mul_one_div, div_self hLpos.ne']
    rw [Real.rpow_add hxpos, Real.rpow_one, hxinvL]; ring
  have hxσ : x ^ σ₀ = Real.exp (-(Lg * w)) * x := by
    rw [Real.rpow_def_of_pos hxpos,
      show Real.exp (-(Lg * w)) * x = Real.exp (-(Lg * w) + Lg) by
        rw [Real.exp_add, hLdef, Real.exp_log hxpos]]
    congr 1
    rw [← hLdef, hσ₀def]; ring
  -- the two `Lm`-scaled decay factors
  set Lm : ℝ := Lg ^ ((m : ℝ) + 1) with hLmdef
  have hLm0 : (0 : ℝ) < Lm := by rw [hLmdef]; exact Real.rpow_pos_of_pos hLpos _
  have hLApos : (0 : ℝ) < Lg ^ A := Real.rpow_pos_of_pos hLpos A
  have hsplitA : Lg ^ ((m : ℝ) + 1 + A) = Lm * Lg ^ A := by
    rw [hLmdef, ← Real.rpow_add hLpos]
  have hkey3 : Lm * Real.exp (-sg) ≤ 1 / Lg ^ A := by
    rw [le_div_iff₀ hLApos]
    calc Lm * Real.exp (-sg) * Lg ^ A = Lg ^ ((m : ℝ) + 1 + A) * Real.exp (-sg) := by
          rw [hsplitA]; ring
      _ ≤ 1 := by rw [hsgdef, hLdef] at *; exact hx3
  have hkey4 : Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))) ≤ 1 / Lg ^ A := by
    rw [le_div_iff₀ hLApos]
    calc Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))) * Lg ^ A
        = Lg ^ ((m : ℝ) + 1 + A) * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))) := by
          rw [hsplitA]; ring
      _ ≤ 1 := by rw [hLdef] at *; exact hx4
  -- the edge constant `B = K·log(2x)^m ≤ K·2^m·Lm`
  have hBle : K * Real.log (2 * x) ^ m ≤ K * 2 ^ m * Lm := by
    have h1 : Real.log (2 * x) ^ m ≤ (2 * Lg) ^ m := pow_le_pow_left₀ hL2pos.le hL2hi m
    have h2 : (2 * Lg) ^ m = 2 ^ m * Lg ^ m := by ring
    have h3 : Lg ^ m ≤ Lm := by
      rw [hLmdef, ← Real.rpow_natCast Lg m]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    calc K * Real.log (2 * x) ^ m ≤ K * (2 ^ m * Lg ^ m) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hK0.le
      _ ≤ K * 2 ^ m * Lm := by nlinarith [h3, h2m, hK0]
  have hBnn : (0 : ℝ) ≤ K * Real.log (2 * x) ^ m := by positivity
  -- the three terms
  have hterm1 : 2 * ((1 + 1 / Lg) - σ₀) * (K * Real.log (2 * x) ^ m) * x ^ (1 + 1 / Lg)
        / pinT x ^ 2
      ≤ ((11 / 5) * K * 2 ^ m * Real.exp 1) * (x * (Lm * Real.exp (-sg))) := by
    rw [hxc, hT2, div_eq_mul_inv, ← Real.exp_neg]
    have hcM : (1 + 1 / Lg) - σ₀ ≤ 11 / 10 := by
      have h1 : 1 / Lg ≤ 1 := by rw [div_le_one hLpos]; linarith
      rw [hσ₀def]; linarith [hwsmall]
    have hcm : (0 : ℝ) ≤ (1 + 1 / Lg) - σ₀ := by
      rw [hσ₀def]
      have h1L : (0 : ℝ) < 1 / Lg := by positivity
      linarith [hw0]
    have hfac : 2 * ((1 + 1 / Lg) - σ₀) * (K * Real.log (2 * x) ^ m)
        ≤ 2 * (11 / 10) * (K * 2 ^ m * Lm) := by
      have := mul_le_mul hcM hBle hBnn (by norm_num : (0 : ℝ) ≤ 11 / 10)
      nlinarith [this, hcm, hBnn, hBle, mul_nonneg hcm hBnn]
    have hexple : Real.exp (-(2 * sg)) ≤ Real.exp (-sg) :=
      Real.exp_le_exp.mpr (by linarith)
    calc 2 * ((1 + 1 / Lg) - σ₀) * (K * Real.log (2 * x) ^ m) * (Real.exp 1 * x)
            * Real.exp (-(2 * sg))
        ≤ 2 * (11 / 10) * (K * 2 ^ m * Lm) * (Real.exp 1 * x) * Real.exp (-(2 * sg)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfac (by positivity)) (Real.exp_pos _).le
      _ ≤ 2 * (11 / 10) * (K * 2 ^ m * Lm) * (Real.exp 1 * x) * Real.exp (-sg) := by
          apply mul_le_mul_of_nonneg_left hexple (by positivity)
      _ = ((11 / 5) * K * 2 ^ m * Real.exp 1) * (x * (Lm * Real.exp (-sg))) := by ring
  have hterm2 : (K * Real.log (2 * x) ^ m) * x ^ σ₀ * (Real.pi / σ₀)
      ≤ bC * (x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))))) := by
    have hπσ : Real.pi / σ₀ ≤ 10 * Real.pi / 9 := by
      rw [div_le_div_iff₀ hσ₀pos (by norm_num)]; nlinarith [hπ, hσ₀9]
    have hxσle : x ^ σ₀ ≤ Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))) * x := by
      rw [hxσ]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hLw])) hxpos.le
    calc (K * Real.log (2 * x) ^ m) * x ^ σ₀ * (Real.pi / σ₀)
        ≤ (K * 2 ^ m * Lm) * (Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))) * x)
            * (10 * Real.pi / 9) := by
          refine mul_le_mul (mul_le_mul hBle hxσle (Real.rpow_nonneg hxpos.le σ₀)
            (by positivity)) hπσ (by positivity) (by positivity)
      _ = bC * (x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))))) := by rw [hbC]; ring
  have hterm3 : (Lg + 1) * x ^ (1 + 1 / Lg) * (2 / pinT x)
      ≤ (4 * Real.exp 1) * (x * (Lm * Real.exp (-sg))) := by
    rw [hxc, hTinv]
    have hLLm : Lg + 1 ≤ 2 * Lm := by
      have h1 : Lg ≤ Lm := by
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hstep := Real.rpow_le_rpow_of_exponent_le hL1
          (show (1 : ℝ) ≤ (m : ℝ) + 1 by linarith)
        rw [Real.rpow_one] at hstep
        rw [hLmdef]; exact hstep
      linarith
    calc (Lg + 1) * (Real.exp 1 * x) * (2 * Real.exp (-sg))
        ≤ (2 * Lm) * (Real.exp 1 * x) * (2 * Real.exp (-sg)) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLLm (by positivity))
            (by positivity)
      _ = (4 * Real.exp 1) * (x * (Lm * Real.exp (-sg))) := by ring
  -- assemble
  have hsh := hshift x hxX1 q χ hP hq t ht
  rw [← hLdef, ← hwset, ← hσ₀def] at hsh
  refine le_trans hsh ?_
  have hsum : 2 * ((1 + 1 / Lg) - σ₀) * (K * Real.log (2 * x) ^ m) * x ^ (1 + 1 / Lg)
        / pinT x ^ 2
      + (K * Real.log (2 * x) ^ m) * x ^ σ₀ * (Real.pi / σ₀)
      + (Lg + 1) * x ^ (1 + 1 / Lg) * (2 / pinT x)
      ≤ aC * (x * (Lm * Real.exp (-sg)))
        + bC * (x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))))) := by
    rw [haC]
    have h := add_le_add (add_le_add hterm1 hterm2) hterm3
    nlinarith [h]
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
  have hfin1 : aC * (x * (Lm * Real.exp (-sg))) ≤ aC * (x / Lg ^ A) := by
    refine mul_le_mul_of_nonneg_left ?_ haC0.le
    calc x * (Lm * Real.exp (-sg)) ≤ x * (1 / Lg ^ A) :=
          mul_le_mul_of_nonneg_left hkey3 hxpos.le
      _ = x / Lg ^ A := by ring
  have hfin2 : bC * (x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5)))))
      ≤ bC * (x / Lg ^ A) := by
    refine mul_le_mul_of_nonneg_left ?_ hbC0.le
    calc x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5)))) ≤ x * (1 / Lg ^ A) :=
          mul_le_mul_of_nonneg_left hkey4 hxpos.le
      _ = x / Lg ^ A := by ring
  rw [hCtot]
  calc (1 / (2 * Real.pi)) * (aC * (x * (Lm * Real.exp (-sg)))
          + bC * (x * (Lm * Real.exp (-(dd * Lg ^ ((1 : ℝ) / 5))))))
      ≤ (1 / (2 * Real.pi)) * (aC * (x / Lg ^ A) + bC * (x / Lg ^ A)) := by
        apply mul_le_mul_of_nonneg_left (by linarith [hfin1, hfin2]) (by positivity)
    _ = (1 / (2 * Real.pi)) * (aC + bC) * x / Lg ^ A := by ring

/-! ### §2b — the pinned width sits below BOTH landed widths

`pinW c₅ (2x)` has to be ≤ the shallow bound's own width `vkShallowWidthSharp c₄ q (2x)` (for
the edge bound) AND ≤ half the region's `boxWidth` (for the zero-freeness — the HALF is what
makes `LFunction_no_zero_in_box` a contradiction, `boxWidth_pos`).  Both comparisons are
`(log q + 1) ≤ 13 log log(2x)`, i.e. the conductor gate `q ≤ (log x)^{12}` spent once. -/

/-- The pinned scale ladder: at `x ≥ exp(exp 100) + 3`, `log x ≥ 101`, `log x ≤ log 2x ≤
2 log x`, and `log log(2x) ≥ 100`. -/
lemma pin_scale_facts {x : ℝ} (hx : Real.exp (Real.exp 100) + 3 ≤ x) :
    (0 : ℝ) < x ∧ (101 : ℝ) ≤ Real.log x ∧ Real.log x ≤ Real.log (2 * x)
      ∧ Real.log (2 * x) ≤ 2 * Real.log x
      ∧ (100 : ℝ) ≤ Real.log (Real.log (2 * x)) := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hxpos : (0 : ℝ) < x := by linarith
  have hL1 : Real.exp 100 ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log hEpos (by linarith)
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hlo : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hxpos (by linarith)
  have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hhi : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']; linarith
  have hll : (100 : ℝ) ≤ Real.log (Real.log (2 * x)) := by
    have h1 : Real.log (Real.log x) ≤ Real.log (Real.log (2 * x)) :=
      Real.log_le_log hLpos hlo
    have h2 : (100 : ℝ) ≤ Real.log (Real.log x) := by
      rw [← Real.log_exp 100]
      exact Real.log_le_log (Real.exp_pos _) hL1
    linarith
  exact ⟨hxpos, by linarith, hlo, hhi, hll⟩

/-- **The conductor gate, spent.**  At `q ≤ (log x)^{12}`, `log q + 1 ≤ 13·log log(2x)`. -/
lemma logq_le_thirteen {q : ℕ} [NeZero q] {x : ℝ} (hx : Real.exp (Real.exp 100) + 3 ≤ x)
    (hq : (q : ℝ) ≤ Real.log x ^ (12 : ℕ)) :
    Real.log (q : ℝ) + 1 ≤ 13 * Real.log (Real.log (2 * x)) := by
  obtain ⟨hxpos, hL101, hlo, _hhi, hll⟩ := pin_scale_facts hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : Real.log (q : ℝ) ≤ 12 * Real.log (Real.log x) := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have h2 : Real.log (Real.log x) ≤ Real.log (Real.log (2 * x)) := Real.log_le_log hLpos hlo
  linarith

/-- `pinW c₅ (2x) ≤ vkShallowWidthSharp c₄ q (2x)` when `169 c₅ ≤ c₄`. -/
lemma pinW_le_sharp {c₄ c₅ : ℝ} (_hc₄0 : 0 < c₄) (hc₅0 : 0 < c₅) (h169 : 169 * c₅ ≤ c₄)
    {q : ℕ} [NeZero q] {x : ℝ} (hx : Real.exp (Real.exp 100) + 3 ≤ x)
    (hq : (q : ℝ) ≤ Real.log x ^ (12 : ℕ)) :
    pinW c₅ (2 * x) ≤ vkShallowWidthSharp c₄ q (2 * x) := by
  obtain ⟨hxpos, hL101, hlo, _hhi, hll⟩ := pin_scale_facts hx
  have hq13 := logq_le_thirteen (q := q) hx hq
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  have hR0 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL2pos _
  have hl0 : (0 : ℝ) < Real.log (Real.log (2 * x)) := by linarith
  have hlogq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hden1 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (2 * x)) ^ (6 : ℕ) := mul_pos hR0 (pow_pos hl0 6)
  have hden2 : (0 : ℝ) < (Real.log (q : ℝ) + 1) ^ 2 * Real.log (2 * x) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (2 * x)) ^ (4 : ℕ) :=
    mul_pos (mul_pos (by positivity) hR0) (pow_pos hl0 4)
  rw [pinW, vkShallowWidthSharp, div_le_div_iff₀ hden1 hden2]
  have hsq : (Real.log (q : ℝ) + 1) ^ 2 ≤ 169 * Real.log (Real.log (2 * x)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.log (q : ℝ) + 1 := by linarith
    have h := mul_self_le_mul_self h0 hq13
    nlinarith [h]
  have hprod : (0 : ℝ) ≤ Real.log (2 * x) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (2 * x)) ^ (4 : ℕ) := by positivity
  calc c₅ * ((Real.log (q : ℝ) + 1) ^ 2 * Real.log (2 * x) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (2 * x)) ^ (4 : ℕ))
      ≤ c₅ * ((169 * Real.log (Real.log (2 * x)) ^ 2)
          * Real.log (2 * x) ^ ((3 : ℝ) / 4) * Real.log (Real.log (2 * x)) ^ (4 : ℕ)) := by
        have := mul_le_mul_of_nonneg_right hsq hprod
        nlinarith [this, hc₅0]
    _ = 169 * c₅ * (Real.log (2 * x) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (2 * x)) ^ (6 : ℕ)) := by ring
    _ ≤ c₄ * (Real.log (2 * x) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (2 * x)) ^ (6 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right h169 hden1.le

/-- `pinW c₅ (2x) ≤ boxWidth c₀ (shallowA q) q (2x)/2` when `10²² c₅ ≤ c₀` — the HALF-width
that makes `LFunction_no_zero_in_box` a contradiction. -/
lemma pinW_le_boxWidth_half {c₀ c₅ : ℝ} (hc₀pos : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hc₅0 : 0 < c₅)
    (h22 : 10 ^ 22 * c₅ ≤ c₀) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : Real.exp (Real.exp 100) + 3 ≤ x) (hq : (q : ℝ) ≤ Real.log x ^ (12 : ℕ)) :
    pinW c₅ (2 * x) ≤ boxWidth c₀ (shallowA q) q (2 * x) / 2 := by
  obtain ⟨hxpos, hL101, hlo, _hhi, hll⟩ := pin_scale_facts hx
  have hq13 := logq_le_thirteen (q := q) hx hq
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  have hR0 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL2pos _
  have hl0 : (0 : ℝ) < Real.log (Real.log (2 * x)) := by linarith
  have hlogq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hHbig : Real.exp (Real.exp 100) + 1 ≤ 2 * x - 1 := by linarith
  have hlow := boxWidth_shallow_lower (q := q) hc₀pos hc₀1 hHbig
  rw [show (2 * x - 1 + 1) = 2 * x by ring] at hlow
  have hden3 : (0 : ℝ) < 10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (2 * x) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (2 * x)) ^ (3 : ℕ)) := by
    refine mul_pos (by norm_num) (mul_pos (mul_pos (by linarith) hR0) (pow_pos hl0 3))
  have hden1 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (2 * x)) ^ (6 : ℕ) := mul_pos hR0 (pow_pos hl0 6)
  have hgoal : pinW c₅ (2 * x)
      ≤ c₀ / (10 ^ 20 * ((Real.log (q : ℝ) + 1) * Real.log (2 * x) ^ ((3 : ℝ) / 4)
          * Real.log (Real.log (2 * x)) ^ (3 : ℕ))) / 2 := by
    rw [pinW, div_div, div_le_div_iff₀ hden1 (by positivity)]
    have hlD : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (2 * x)) ^ (3 : ℕ) := mul_pos hR0 (pow_pos hl0 3)
    have hstep1 : c₅ * (10 ^ 20 * ((Real.log (q : ℝ) + 1)
            * Real.log (2 * x) ^ ((3 : ℝ) / 4) * Real.log (Real.log (2 * x)) ^ (3 : ℕ)) * 2)
        ≤ c₅ * (10 ^ 20 * ((13 * Real.log (Real.log (2 * x)))
            * Real.log (2 * x) ^ ((3 : ℝ) / 4) * Real.log (Real.log (2 * x)) ^ (3 : ℕ)) * 2) := by
      have h := mul_le_mul_of_nonneg_right hq13 hlD.le
      nlinarith [h, hc₅0]
    have hfin : 26 * 10 ^ 20 * c₅ ≤ c₀ * Real.log (Real.log (2 * x)) ^ 2 := by
      have hl2 : (10 : ℝ) ^ 4 ≤ Real.log (Real.log (2 * x)) ^ 2 := by nlinarith [hll]
      nlinarith [hl2, h22, hc₀pos, hc₅0]
    have hprod := mul_nonneg (mul_nonneg hR0.le
      (pow_nonneg hl0.le 4)) (sub_nonneg.mpr hfin)
    nlinarith [hstep1, hprod]
  linarith [hgoal, hlow]

/-! ## §3 — de-smoothing `M₁_{μχ̄} → M_{μχ̄}` (the ℂ-valued mirror) -/

/-- Weighted twisted Möbius sum `∑_{n≤N} μ(n)χ̄(n)n^{it}·n` — the twisted `Salt.SW.Tsum`. -/
def TsumChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, muChiTw χ t n * (n : ℂ)

/-- `x·M₁_{μχ̄}(t;x) = x·M_{μχ̄}(t;⌊x⌋) − T_{μχ̄}(t;⌊x⌋)`. -/
lemma x_mul_Mmu1Chi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * Mmu1Chi χ t x
      = (x : ℂ) * MmuChi χ t ⌊x⌋₊ - TsumChi χ t ⌊x⌋₊ := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [Mmu1Chi, MmuChi_eq_sum_muChiTw, TsumChi, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  field_simp

/-- Split of `M_{μχ̄}` at `M ≤ N`. -/
lemma MmuChi_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {M N : ℕ} (h : M ≤ N) :
    MmuChi χ t N = MmuChi χ t M + ∑ n ∈ Finset.Ioc M N, muChiTw χ t n := by
  rw [MmuChi_eq_sum_muChiTw, MmuChi_eq_sum_muChiTw, Salt.SW.Icc_one_eq_Ioc_zero,
    Salt.SW.Icc_one_eq_Ioc_zero, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]

/-- Split of `T_{μχ̄}` at `M ≤ N`. -/
lemma TsumChi_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {M N : ℕ} (h : M ≤ N) :
    TsumChi χ t N = TsumChi χ t M + ∑ n ∈ Finset.Ioc M N, muChiTw χ t n * (n : ℂ) := by
  rw [TsumChi, TsumChi, Salt.SW.Icc_one_eq_Ioc_zero, Salt.SW.Icc_one_eq_Ioc_zero,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) h]

/-- **The de-smoothing identity, twisted.**  For `1 ≤ x ≤ y`,
`y·M₁(y) − x·M₁(x) = (y−x)·M_{μχ̄}(⌊x⌋) + ∑_{⌊x⌋<n≤⌊y⌋} μ(n)χ̄(n)n^{it}(y−n)`. -/
lemma desmooth_identity_chi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {x y : ℝ}
    (hx : (1 : ℝ) ≤ x) (hxy : x ≤ y) :
    (y : ℂ) * Mmu1Chi χ t y - (x : ℂ) * Mmu1Chi χ t x
      = ((y : ℂ) - (x : ℂ)) * MmuChi χ t ⌊x⌋₊
        + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n * ((y : ℂ) - (n : ℂ)) := by
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hsum : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n * ((y : ℂ) - (n : ℂ))
      = (y : ℂ) * (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n)
        - (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n * (n : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [x_mul_Mmu1Chi χ t hx0, x_mul_Mmu1Chi χ t hy0, MmuChi_split χ t hfl,
    TsumChi_split χ t hfl, hsum]
  ring

/-- **The remainder bound, twisted.**  For `1 ≤ x ≤ y`,
`‖∑_{⌊x⌋<n≤⌊y⌋} μ(n)χ̄(n)n^{it}(y−n)‖ ≤ (y−x+1)²` — the twist is 1-bounded
(`norm_muChiTw_le_one`), so this is the `q = 1` count verbatim. -/
lemma remainder_bound_chi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {x y : ℝ}
    (hx : (1 : ℝ) ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n * ((y : ℂ) - (n : ℂ))‖ ≤ (y - x + 1) ^ 2 := by
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  set d := (y - x + 1) with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖muChiTw χ t n * ((y : ℂ) - (n : ℂ))‖ ≤ d := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnle : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
    have hyn : 0 ≤ y - (n : ℝ) := by linarith
    have hxfl : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
    have hnlb : (⌊x⌋₊ : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hyd : y - (n : ℝ) ≤ d := by rw [hd]; linarith
    have hcast : ((y : ℂ) - (n : ℂ)) = ((y - (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hyn]
    calc ‖muChiTw χ t n‖ * (y - (n : ℝ))
        ≤ 1 * (y - (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (norm_muChiTw_le_one χ t n) hyn
      _ = y - (n : ℝ) := one_mul _
      _ ≤ d := hyd
  calc ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, muChiTw χ t n * ((y : ℂ) - (n : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖muChiTw χ t n * ((y : ℂ) - (n : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, d := Finset.sum_le_sum hterm
    _ = (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card • d := by rw [Finset.sum_const]
    _ = ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) * d := by rw [Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ d * d := by
        apply mul_le_mul_of_nonneg_right _ hd0
        rw [Nat.cast_sub hfl]
        have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
        have h2 : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
        rw [hd]; linarith
    _ = d ^ 2 := by ring

set_option maxHeartbeats 1600000 in
-- The de-smoothing threads the two-point identity, the remainder count and one `P·Q` scale
-- ladder through a single `calc`; the elaborator needs headroom past the default, exactly as
-- `Salt.SW.mmuRate_of_smoothed` does.
/-- **§3 — THE DE-SMOOTHING.**  The smoothed twisted rate (real `x`, at the gates
`q ≤ (log x)^{12}`, `|t| ≤ x`, and any side condition `P q χ`) implies the sharp rate on ℕ
at the SAME gates.  Two-point Riesz de-smoothing at width `h = Y/(log Y)^{A+1}`; the
remainder `≤ (h+1)²` is paid by the `Q·L = P` step.  `P` is a free side condition so that the
non-principal row (`χ ≠ 1`) and the principal row can each use this once. -/
theorem mmuChiRate_of_smoothed (P : (q : ℕ) → DirichletCharacter ℂ q → Prop)
    (hsm : ∀ A : ℝ, 0 < A → ∃ (C x₀ : ℝ), 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
          (q : ℝ) ≤ Real.log x ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ x →
            ‖Mmu1Chi χ t x‖ ≤ C * x / Real.log x ^ A) :
    ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
        (q : ℝ) ≤ Real.log y ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ (y : ℝ) →
          ‖MmuChi χ t y‖ ≤ C * y / Real.log y ^ A := by
  intro A hA
  obtain ⟨C', x₀', hC'pos, hb0⟩ := hsm (2 * A + 2) (by linarith)
  have hev_e : ∀ᶠ z : ℝ in Filter.atTop, Real.exp 1 ≤ z := Filter.eventually_ge_atTop _
  have hev_x0 : ∀ᶠ z : ℝ in Filter.atTop, x₀' ≤ z := Filter.eventually_ge_atTop _
  have hev_3P : ∀ᶠ z : ℝ in Filter.atTop, 3 * Real.log z ^ (A + 1) ≤ z := by
    have hlo := isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) (A + 1) (by norm_num)
    filter_upwards [hlo.def (by norm_num : (0 : ℝ) < 1 / 3), Filter.eventually_ge_atTop (1 : ℝ)]
      with z hz hz1
    have hzpos : (0 : ℝ) < z := by linarith
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hzpos,
        abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hz1) _)] at hz
    linarith
  have key : ∀ᶠ (y : ℕ) in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), P q χ →
        (q : ℝ) ≤ Real.log y ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ (y : ℝ) →
          ‖MmuChi χ t y‖ ≤ (5 * C' + 2) * (y : ℝ) / Real.log y ^ A := by
    have E1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_e
    have E2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_x0
    have E3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev_3P
    filter_upwards [E1, E2, E3] with y he hx0 h3P
    intro q _ χ hP hq t ht
    set Y : ℝ := (y : ℝ) with hY
    set Lg : ℝ := Real.log Y with hLdef
    set Q : ℝ := Lg ^ A with hQdef
    set Pw : ℝ := Lg ^ (A + 1) with hPdef
    have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos 1) he
    have hY1 : (1 : ℝ) ≤ Y := le_trans (Real.one_le_exp (by norm_num)) he
    have hL1 : (1 : ℝ) ≤ Lg := by
      rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
    have hLpos : (0 : ℝ) < Lg := by linarith
    have hPpos : (0 : ℝ) < Pw := by rw [hPdef]; exact Real.rpow_pos_of_pos hLpos _
    have hQpos : (0 : ℝ) < Q := by rw [hQdef]; exact Real.rpow_pos_of_pos hLpos _
    have hP1 : (1 : ℝ) ≤ Pw := by
      rw [hPdef]; calc (1 : ℝ) = (1 : ℝ) ^ (A + 1) := (Real.one_rpow _).symm
        _ ≤ Lg ^ (A + 1) := Real.rpow_le_rpow (by norm_num) hL1 (by linarith)
    have h3P' : 3 * Pw ≤ Y := h3P
    have hPY : Pw ≤ Y := by linarith
    set h : ℝ := Y / Pw with hh
    have hhpos : (0 : ℝ) < h := by rw [hh]; positivity
    have hhle : h ≤ Y := by rw [hh, div_le_iff₀ hPpos]; nlinarith [hP1, hYpos]
    have hYhle : Y ≤ Y + h := by linarith
    have hfloorY : ⌊Y⌋₊ = y := by rw [hY]; exact Nat.floor_natCast y
    have hPeq : Pw = Q * Lg := by rw [hPdef, hQdef, Real.rpow_add hLpos, Real.rpow_one]
    have hP2 : Lg ^ (2 * A + 2) = Pw * Pw := by
      rw [hPdef, show (2 * A + 2 : ℝ) = (A + 1) + (A + 1) by ring, Real.rpow_add hLpos]
    -- the smoothed bound at `Y` and at `Y + h`, at the transferred gates
    have hlogYh : Lg ≤ Real.log (Y + h) := by
      rw [hLdef]; exact Real.log_le_log hYpos hYhle
    have hgateY : (q : ℝ) ≤ Real.log Y ^ (12 : ℕ) := hq
    have hgateYh : (q : ℝ) ≤ Real.log (Y + h) ^ (12 : ℕ) := by
      refine le_trans hgateY ?_
      exact pow_le_pow_left₀ (by linarith) hlogYh 12
    have hR1Y : ‖Mmu1Chi χ t Y‖ ≤ C' * Y / Lg ^ (2 * A + 2) := by
      have := hb0 Y hx0 q χ hP hgateY t ht
      rwa [← hLdef] at this
    have hR1Yh : ‖Mmu1Chi χ t (Y + h)‖
        ≤ C' * (Y + h) / Real.log (Y + h) ^ (2 * A + 2) :=
      hb0 (Y + h) (by linarith) q χ hP hgateYh t (by linarith [ht])
    have h2A2 : (0 : ℝ) ≤ 2 * A + 2 := by linarith
    have hden : Lg ^ (2 * A + 2) ≤ Real.log (Y + h) ^ (2 * A + 2) :=
      Real.rpow_le_rpow (by linarith) hlogYh h2A2
    have hT1 : (Y + h) * ‖Mmu1Chi χ t (Y + h)‖ ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
      have hstep1 : (Y + h) * ‖Mmu1Chi χ t (Y + h)‖
          ≤ (Y + h) * (C' * (Y + h) / Real.log (Y + h) ^ (2 * A + 2)) :=
        mul_le_mul_of_nonneg_left hR1Yh (by linarith)
      have hnum : C' * (Y + h) ^ 2 ≤ 4 * C' * Y ^ 2 := by
        nlinarith [mul_nonneg hC'pos.le (mul_nonneg (by linarith : (0 : ℝ) ≤ Y - h)
          (by linarith : (0 : ℝ) ≤ 3 * Y + h))]
      have hstep2 : (Y + h) * (C' * (Y + h) / Real.log (Y + h) ^ (2 * A + 2))
          ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
        rw [show (Y + h) * (C' * (Y + h) / Real.log (Y + h) ^ (2 * A + 2))
              = C' * (Y + h) ^ 2 / Real.log (Y + h) ^ (2 * A + 2) by ring]
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
      linarith
    have hT2 : Y * ‖Mmu1Chi χ t Y‖ ≤ C' * Y ^ 2 / Lg ^ (2 * A + 2) := by
      have := mul_le_mul_of_nonneg_left hR1Y (le_of_lt hYpos)
      rw [show Y * (C' * Y / Lg ^ (2 * A + 2)) = C' * Y ^ 2 / Lg ^ (2 * A + 2) by ring] at this
      exact this
    have hid := desmooth_identity_chi χ t hY1 hYhle
    rw [hfloorY] at hid
    set S : ℂ := ∑ n ∈ Finset.Ioc y ⌊Y + h⌋₊,
        muChiTw χ t n * (((Y + h : ℝ) : ℂ) - (n : ℂ)) with hSdef
    have hSbd : ‖S‖ ≤ (h + 1) ^ 2 := by
      have hr := remainder_bound_chi χ t hY1 hYhle
      rw [hfloorY] at hr
      rw [show Y + h - Y + 1 = h + 1 by ring] at hr
      rw [hSdef]
      exact hr
    have hMeq : ((h : ℝ) : ℂ) * MmuChi χ t y
        = ((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h) - (Y : ℂ) * Mmu1Chi χ t Y - S := by
      have hcast : (((Y + h : ℝ) : ℂ) - (Y : ℂ)) = ((h : ℝ) : ℂ) := by push_cast; ring
      rw [← hcast]
      linear_combination -hid
    have hcore : h * ‖MmuChi χ t y‖ ≤ 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := by
      have habs : h * ‖MmuChi χ t y‖
          = ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h) - (Y : ℂ) * Mmu1Chi χ t Y - S‖ := by
        rw [← hMeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhpos]
      rw [habs]
      calc ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h) - (Y : ℂ) * Mmu1Chi χ t Y - S‖
          ≤ ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h)‖ + ‖(Y : ℂ) * Mmu1Chi χ t Y‖ + ‖S‖ := by
            calc ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h) - (Y : ℂ) * Mmu1Chi χ t Y - S‖
                ≤ ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h) - (Y : ℂ) * Mmu1Chi χ t Y‖
                    + ‖S‖ := norm_sub_le _ _
              _ ≤ ‖((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h)‖ + ‖(Y : ℂ) * Mmu1Chi χ t Y‖
                    + ‖S‖ := by
                  linarith [norm_sub_le (((Y + h : ℝ) : ℂ) * Mmu1Chi χ t (Y + h))
                    ((Y : ℂ) * Mmu1Chi χ t Y)]
        _ = (Y + h) * ‖Mmu1Chi χ t (Y + h)‖ + Y * ‖Mmu1Chi χ t Y‖ + ‖S‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < Y + h), abs_of_pos hYpos]
        _ ≤ 4 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + C' * Y ^ 2 / Lg ^ (2 * A + 2)
              + (h + 1) ^ 2 := by linarith [hT1, hT2, hSbd]
        _ = 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := by ring
    have hclean : 5 * C' * Y ^ 2 + (Y + Pw) ^ 2 ≤ (5 * C' + 2) * Y ^ 2 * Lg := by
      nlinarith [mul_nonneg (mul_nonneg hC'pos.le (sq_nonneg Y)) (by linarith : (0 : ℝ) ≤ Lg - 1),
        mul_nonneg (sq_nonneg Y) (by linarith : (0 : ℝ) ≤ Lg - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ Y - 3 * Pw) (by linarith : (0 : ℝ) ≤ Y + Pw),
        sq_nonneg Pw]
    have key2 : 5 * C' * Y ^ 2 / (Pw * Pw) + (Y / Pw + 1) ^ 2
        ≤ (5 * C' + 2) * Y ^ 2 / (Pw * Q) := by
      have e1 : (Y / Pw + 1) ^ 2 = (Y + Pw) ^ 2 / (Pw * Pw) := by field_simp
      rw [e1, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      calc (5 * C' * Y ^ 2 + (Y + Pw) ^ 2) * (Pw * Q)
          ≤ ((5 * C' + 2) * Y ^ 2 * Lg) * (Pw * Q) :=
            mul_le_mul_of_nonneg_right hclean (by positivity)
        _ = (5 * C' + 2) * Y ^ 2 * (Pw * Pw) := by rw [hPeq]; ring
    refine le_of_mul_le_mul_left ?_ hhpos
    calc h * ‖MmuChi χ t y‖
        ≤ 5 * C' * Y ^ 2 / Lg ^ (2 * A + 2) + (h + 1) ^ 2 := hcore
      _ = 5 * C' * Y ^ 2 / (Pw * Pw) + (Y / Pw + 1) ^ 2 := by rw [hP2, hh]
      _ ≤ (5 * C' + 2) * Y ^ 2 / (Pw * Q) := key2
      _ = h * ((5 * C' + 2) * Y / Q) := by rw [hh]; field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨5 * C' + 2, N, by positivity, hN⟩

/-! ## §4 — ⟦D1 THE MIRROR⟧: the non-principal row of `MmuChiRate`

Everything composes here: §1's contour shift with the carrier `g s = (L(s − it, χ⁻¹))⁻¹`
(entire for `χ⁻¹ ≠ 1`, so no pole normalization anywhere), the landed edge bound
`lFunctionInvShallowVkSharp_holds` at `H = 2x`, the landed region discharge
`LFunction_no_zero_in_shifted_box`, §2's budget and §3's de-smoothing.  The ξ₁/real-zero row
rides in as the named hypothesis in the STRONG `Re < 1/2` form — the shape wave P-7's Siegel
fold delivers, and exactly what `MmuChiRate_residue_sharp` already carries. -/

/-- **THE ξ₁ CARVE-OUT, AT THE WIDTH** ⟦R-1, wave CLOSE⟧ — the real-zero hypothesis in the
shape the Siegel fold actually delivers.

`PortAssembly.lean` §7 is the adjudication: the STRONG form (`Re ρ < 1/2` for every real zero)
is a GRH fragment — Chowla's conjecture for real `χ` — and NO threshold in `H` or restriction of
the `q`-range weakens it, so it is not Siegel-foldable.  The WIDTH form below IS: at
`q ≤ (log H)^{12}` Siegel with `ε = 1/16` beats `vkShallowWidth (10⁻⁶) q H`, because
`q^{1/16} ≤ (log H)^{3/4}` is exactly the width's own leading factor (`16 = 12/(3/4)`).

Two gates ride with it, and both are free downstream: the modulus gate `q ≤ (log H)^{12}` is
`MmuChiRate`'s own, and the threshold `H₀` — which carries Siegel's INEFFECTIVITY — folds into
`MmuChiRate`'s `∃ x₀`.  This is the WEAKER hypothesis: `xiCarveWidth_of_half` derives it from
the strong form through `carve_of_half`, which is all `mmuChiRate_nonprincipal` ever used. -/
def XiCarveWidth (H₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ H : ℝ, H₀ ≤ H → (q : ℝ) ≤ Real.log H ^ (12 : ℕ) →
    ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 →
      ρ.re ≤ 1 - vkShallowWidth (1 / 10 ^ 6) q H

/-- The strong `Re < 1/2` form implies the width form at every threshold above the region's
floor (`carve_of_half`), so the ⟦R-1⟧ restatement loses nothing that was provable before. -/
lemma xiCarveWidth_of_half {H₀ : ℝ} (hH₀ : Real.exp (Real.exp 100) + 1 ≤ H₀)
    (hhalf : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2) :
    XiCarveWidth H₀ :=
  fun q _ χ hχ1 _H hH _ => carve_of_half (le_trans hH₀ hH) (hhalf q χ hχ1)

set_option maxHeartbeats 4000000 in
-- The assembly threads the shallow package, the two width comparisons, the shifted-box
-- discharge and four carrier properties into one application of §1, then §2 and §3; the
-- elaborator needs headroom well past the default.
/-- **⟦D1⟧ THE NON-PRINCIPAL ROW.**  For every `χ ≠ 1` mod `q`, at the ⟦D1⟧-amended gates
(`|t| ≤ y`, `q ≤ (log y)^{12}`), `‖∑_{n ≤ y} μ(n)χ̄(n)n^{it}‖ ≤ C·y/(log y)^A` for every
`A > 0`, with `C` and `y₀` uniform in `q`, `χ`, `t`.  Conditional ONLY on the ξ₁/Siegel
carve-out ⟦R-1: in the WIDTH form `XiCarveWidth H₀`, the shape P-7's fold delivers; the
threshold `H₀` is spent as the pinned `X₁`, i.e. it rides inside the conclusion's `∃ x₀`⟧. -/
theorem mmuChiRate_nonprincipal {H₀ : ℝ} (hH₀ : Real.exp (Real.exp 100) + 3 ≤ H₀)
    (hxi : XiCarveWidth H₀) :
    ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        (q : ℝ) ≤ Real.log y ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ (y : ℝ) →
          ‖MmuChi χ t y‖ ≤ C * y / Real.log y ^ A := by
  obtain ⟨c₄, K, m, hc₄0, hK0, Hinv⟩ := lFunctionInvShallowVkSharp_holds
  obtain ⟨c₀', hc₀'pos, hcl'⟩ := Salt.SW.zero_free_region_all'
  set c₀ : ℝ := min c₀' 1 with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc₀'pos zero_lt_one
  have hc₀1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀le : c₀ ≤ c₀' := min_le_left _ _
  set c₅ : ℝ := min 1 (min (c₄ / 169) (c₀ / 10 ^ 22)) with hc₅def
  have hcA : c₅ ≤ c₄ / 169 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcB : c₅ ≤ c₀ / 10 ^ 22 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hc₅1 : c₅ ≤ 1 := min_le_left _ _
  have hc₅0 : 0 < c₅ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have h169 : 169 * c₅ ≤ c₄ := by rw [le_div_iff₀ (by norm_num)] at hcA; linarith
  have h22 : 10 ^ 22 * c₅ ≤ c₀ := by rw [le_div_iff₀ (by norm_num)] at hcB; linarith
  set Kp : ℝ := max 1 (K * 13 ^ m) with hKpdef
  have hKp1 : (1 : ℝ) ≤ Kp := le_max_left _ _
  have hKple : K * 13 ^ m ≤ Kp := le_max_right _ _
  refine mmuChiRate_of_smoothed (fun q χ => χ ≠ 1) ?_
  refine mmu1Chi_rate_of_pinned (c₅ := c₅) (K := Kp) (m := 2 * m)
    (X₁ := H₀) hc₅0 hc₅1 hKp1 (fun q χ => χ ≠ 1) ?_
  intro x hxH₀ q _ χ hχ1 hq t ht
  -- ⟦R-1⟧ the pinned floor is now `H₀`; the old scale floor is one `le_trans` away
  have hxX1 : Real.exp (Real.exp 100) + 3 ≤ x := le_trans hH₀ hxH₀
  obtain ⟨hxpos, hL101, hL2lo, hL2hi, hll⟩ := pin_scale_facts hxX1
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  have hχinv1 : χ⁻¹ ≠ 1 := by intro h; exact hχ1 (by rw [← inv_inv χ, h, inv_one])
  -- ⟦the abscissae⟧
  set W : ℝ := pinW c₅ (2 * x) with hWdef
  have hWsharp : W ≤ vkShallowWidthSharp c₄ q (2 * x) :=
    pinW_le_sharp hc₄0 hc₅0 h169 hxX1 hq
  have hWbox : W ≤ boxWidth c₀ (shallowA q) q (2 * x) / 2 :=
    pinW_le_boxWidth_half hc₀pos hc₀1 hc₅0 h22 hxX1 hq
  have hbwhalf : boxWidth c₀ (shallowA q) q (2 * x) ≤ 1 / 2 := boxWidth_le_half _ _ _ _
  have hW4 : W ≤ 1 / 4 := by linarith
  have hW0 : 0 < W := by
    rw [hWdef, pinW]
    have hR0 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL2pos _
    have hl0 : (0 : ℝ) < Real.log (Real.log (2 * x)) := by linarith
    exact div_pos hc₅0 (mul_pos hR0 (pow_pos hl0 6))
  set σ₀ : ℝ := 1 - W with hσ₀def
  have hσ₀pos : (0 : ℝ) < σ₀ := by rw [hσ₀def]; linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hinvL1 : 1 / Real.log x ≤ 1 := by rw [div_le_one hLpos]; linarith
  have hinvL0 : (0 : ℝ) < 1 / Real.log x := by positivity
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc2 : c ≤ 2 := by rw [hcdef]; linarith
  have hσ₀c : σ₀ < c := by rw [hσ₀def, hcdef]; linarith
  set T : ℝ := pinT x with hTdef
  have hT0 : 0 < T := by rw [hTdef, pinT]; exact Real.exp_pos _
  have hTx : T ≤ x := by
    rw [hTdef, pinT]
    have h1 : Real.log x ^ ((1 : ℝ) / 10) ≤ Real.log x := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ Real.log x by linarith)
        (show (1 : ℝ) / 10 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    calc Real.exp (Real.log x ^ ((1 : ℝ) / 10)) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr h1
      _ = x := Real.exp_log hxpos
  -- ⟦the shifted point's coordinates⟧
  have hshre : ∀ s : ℂ, (s - (t : ℂ) * I).re = s.re := by intro s; simp
  have hshim : ∀ s : ℂ, (s - (t : ℂ) * I).im = s.im - t := by intro s; simp
  -- ⟦the classical region at χ⁻¹⟧
  have hcl : ∀ {ρ : ℂ}, LFunction χ⁻¹ ρ = 0 → 1 / 2 ≤ ρ.re →
      ((χ⁻¹).primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
      ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    intro ρ hρ0 hρre hor
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hlogpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      apply Real.log_pos
      nlinarith [abs_nonneg ρ.im]
    have hmono : c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₀' / Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
      (div_le_div_iff_of_pos_right hlogpos).mpr hc₀le
    linarith [hcl' q χ⁻¹ hχinv1 hρ0 hρre hor, hmono]
  -- ⟦the carve-out, at both heights the two consumers need⟧
  -- ⟦R-1⟧ the width form is read directly at each height; the modulus gate transfers by
  -- `log x ≤ log(2x)` and `log x ≤ log(2x−1)` (both `≥ x` at `x ≥ 1`).
  have hlogx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hq2x : (q : ℝ) ≤ Real.log (2 * x) ^ (12 : ℕ) :=
    le_trans hq (pow_le_pow_left₀ hlogx0 hL2lo 12)
  have hq2x1 : (q : ℝ) ≤ Real.log (2 * x - 1) ^ (12 : ℕ) :=
    le_trans hq (pow_le_pow_left₀ hlogx0
      (Real.log_le_log hxpos (by linarith)) 12)
  have hcarve2x : ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 →
      ρ.re ≤ 1 - vkShallowWidth (1 / 10 ^ 6) q (2 * x) :=
    hxi q χ hχ1 (2 * x) (by linarith) hq2x
  have hcarveBox : ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 →
      ρ.re ≤ 1 - boxWidth c₀ (shallowA q) q (2 * x) := by
    intro ρ h0 him
    have h1 := hxi q χ hχ1 (2 * x - 1) (by linarith) hq2x1 ρ h0 him
    have h2 := boxWidth_le_carve (c₀ := c₀) (q := q) (H := 2 * x - 1) (by linarith)
    rw [show (2 * x - 1 + 1) = 2 * x by ring] at h2
    linarith
  -- ⟦no zero in the shifted box⟧
  have hne : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T →
      LFunction χ⁻¹ (s - (t : ℂ) * I) ≠ 0 := by
    intro s h1 h2 h3 h0
    refine LFunction_no_zero_in_shifted_box hχinv1 (A := shallowA q) (c₀ := c₀) (t := t)
      (T := T) (H := 2 * x) one_le_shallowA hc₀pos (by linarith) ?_ shallowA_gate hcl
      hcarveBox h0 ?_ ?_
    · calc |t| + T ≤ x + x := add_le_add ht hTx
        _ = 2 * x := by ring
    · rw [hshre]; rw [hσ₀def] at h1; linarith
    · rw [hshim, show s.im - t + t = s.im by ring]; exact h3
  -- ⟦the carrier⟧
  have hgbox : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T →
      ‖(LFunction χ⁻¹ (s - (t : ℂ) * I))⁻¹‖ ≤ Kp * Real.log (2 * x) ^ (2 * m) := by
    intro s h1 h2 h3
    have hpt : s - (t : ℂ) * I = ((s.re : ℝ) : ℂ) + ((s.im - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hIm2 : |s.im - t| ≤ 2 * x := by
      have := abs_sub (s.im) t
      calc |s.im - t| ≤ |s.im| + |t| := abs_sub _ _
        _ ≤ T + x := add_le_add h3 ht
        _ ≤ 2 * x := by linarith
    have hb := Hinv q χ⁻¹ hχinv1 (2 * x) (by linarith) hcarve2x s.re (s.im - t)
      (by rw [hσ₀def] at h1; linarith) (by linarith) hIm2
    rw [hpt]
    refine le_trans hb ?_
    -- `K((log q+1)·log 2x)^m ≤ Kp·log(2x)^{2m}`
    have hq13 := logq_le_thirteen (q := q) hxX1 hq
    have hlself : Real.log (Real.log (2 * x)) ≤ Real.log (2 * x) :=
      Real.log_le_self hL2pos.le
    have hbase : (Real.log (q : ℝ) + 1) * Real.log (2 * x)
        ≤ 13 * Real.log (2 * x) ^ 2 := by nlinarith [hq13, hlself, hL2pos]
    have hbase0 : (0 : ℝ) ≤ (Real.log (q : ℝ) + 1) * Real.log (2 * x) :=
      mul_nonneg (by linarith [Real.log_natCast_nonneg q]) hL2pos.le
    have hpow : ((Real.log (q : ℝ) + 1) * Real.log (2 * x)) ^ m
        ≤ 13 ^ m * Real.log (2 * x) ^ (2 * m) := by
      calc ((Real.log (q : ℝ) + 1) * Real.log (2 * x)) ^ m
          ≤ (13 * Real.log (2 * x) ^ 2) ^ m := pow_le_pow_left₀ hbase0 hbase m
        _ = 13 ^ m * Real.log (2 * x) ^ (2 * m) := by
            rw [mul_pow, ← pow_mul]
    calc K * ((Real.log (q : ℝ) + 1) * Real.log (2 * x)) ^ m
        ≤ K * (13 ^ m * Real.log (2 * x) ^ (2 * m)) :=
          mul_le_mul_of_nonneg_left hpow hK0.le
      _ = (K * 13 ^ m) * Real.log (2 * x) ^ (2 * m) := by ring
      _ ≤ Kp * Real.log (2 * x) ^ (2 * m) :=
          mul_le_mul_of_nonneg_right hKple (by positivity)
  have hrect : ∀ s : ℂ, s ∈ Salt.SW.closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I) →
      σ₀ ≤ s.re ∧ s.re ≤ c ∧ |s.im| ≤ T := by
    intro s hs
    have hzre : ((σ₀ : ℂ) - (T : ℂ) * I).re = σ₀ := by simp
    have hzim : ((σ₀ : ℂ) - (T : ℂ) * I).im = -T := by simp
    have hwre : ((c : ℂ) + (T : ℂ) * I).re = c := by simp
    have hwim : ((c : ℂ) + (T : ℂ) * I).im = T := by simp
    rw [Salt.SW.closedRect, hzre, hzim, hwre, hwim, Complex.mem_reProdIm,
      Set.uIcc_of_le hσ₀c.le, Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hre, him⟩ := hs
    simp only [Set.mem_Icc] at hre him
    exact ⟨hre.1, hre.2, abs_le.mpr ⟨him.1, him.2⟩⟩
  have hgana : DifferentiableOn ℂ (fun s : ℂ => (LFunction χ⁻¹ (s - (t : ℂ) * I))⁻¹)
      (Salt.SW.closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I)) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hrect s hs
    have hd : DifferentiableAt ℂ (fun z : ℂ => LFunction χ⁻¹ (z - (t : ℂ) * I)) s :=
      (differentiable_LFunction hχinv1 _).comp s (by fun_prop)
    exact (hd.inv (hne s h1 h2 h3)).differentiableWithinAt
  have hgcline : ∀ v : ℝ, (LFunction χ⁻¹ (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I))⁻¹
      = (LFunction χ⁻¹ ((c : ℂ) + ((v - t : ℝ) : ℂ) * I))⁻¹ := by
    intro v
    congr 2
    push_cast
    ring
  have hgcont : Continuous fun v : ℝ =>
      (LFunction χ⁻¹ (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I))⁻¹ := by
    have hcont : Continuous fun v : ℝ =>
        LFunction χ⁻¹ (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) :=
      (differentiable_LFunction hχinv1).continuous.comp (by fun_prop)
    refine hcont.inv₀ (fun v => ?_)
    refine LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv1) ?_
    have hre : (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I).re = c := by simp
    rw [hre]; linarith
  have hBbox0 : (0 : ℝ) ≤ Kp * Real.log (2 * x) ^ (2 * m) :=
    mul_nonneg (by linarith) (pow_nonneg hL2pos.le _)
  -- ⟦§1, then the tail constant rewrite⟧
  refine le_trans (mmu1Chi_contour_shift χ t hx1 hc1 hT0 hσ₀pos hσ₀c hBbox0
    hgcline hgcont hgana hgbox) ?_
  have heq : (1 : ℝ) + 1 / (c - 1) = Real.log x + 1 := by
    rw [hcdef, show (1 + 1 / Real.log x) - 1 = 1 / Real.log x by ring, one_div_one_div]
    ring
  rw [heq]

/-! ## §5 — the composition, and the residue: the χ₀ row

`MmuChiRate` quantifies over EVERY `χ` mod `q`, so §4 is one of two rows.  The principal row
is stated here as its own `Prop` and the composition is recorded; what closes it is named
precisely, and it is NOT the mirror (the mirror above serves it verbatim) but ONE analytic
input, the `ζ` twin of `lFunctionInvShallowVkSharp_holds`. -/

/-- **The principal row of the slot** (`χ = 1` mod `q`), at the same ⟦D1⟧-amended gates. -/
def MmuChiRatePrincipal : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ = 1 →
      (q : ℝ) ≤ Real.log y ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ (y : ℝ) →
        ‖MmuChi χ t y‖ ≤ C * y / Real.log y ^ A

/-- **The two rows compose into the slot.**  A `by_cases` on `χ = 1`, with the two constants
and thresholds maximized. -/
theorem mmuChiRate_of_rows
    (hnp : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
          (q : ℝ) ≤ Real.log y ^ (12 : ℕ) → ∀ t : ℝ, |t| ≤ (y : ℝ) →
            ‖MmuChi χ t y‖ ≤ C * y / Real.log y ^ A)
    (hpr : MmuChiRatePrincipal) : MmuChiRate := by
  intro A hA
  obtain ⟨C₁, y₁, hC₁, hb₁⟩ := hnp A hA
  obtain ⟨C₂, y₂, hC₂, hb₂⟩ := hpr A hA
  refine ⟨max C₁ C₂, max y₁ y₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro y hy q _ χ hqg t ht
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : y₂ ≤ y := le_trans (le_max_right _ _) hy
  have hLnn : (0 : ℝ) ≤ Real.log y ^ A := Real.rpow_nonneg (Real.log_natCast_nonneg y) A
  have hynn : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  by_cases hχ : χ = 1
  · refine le_trans (hb₂ y hy2 q χ hχ hqg t ht) ?_
    gcongr
    exact le_max_right _ _
  · refine le_trans (hb₁ y hy1 q χ hχ hqg t ht) ?_
    gcongr
    exact le_max_left _ _

/-- **⟦THE MIRROR'S DELIVERABLE⟧ — `MmuChiRate` from the two named inputs.**  The ξ₁/Siegel
carve-out (wave P-7's fold, ⟦R-1⟧ in the WIDTH form `XiCarveWidth H₀`) plus the principal row.
This is `MmuChiRate_residue_sharp` with its `LFunctionInvShallowVkSharp` slot DISCHARGED (that
Prop is landed, `lFunctionInvShallowVkSharp_holds`) and its mechanical mirror LANDED (§§1–4):
what is left is exactly the χ₀ row. -/
theorem mmuChiRate_of_carve_and_principal {H₀ : ℝ}
    (hH₀ : Real.exp (Real.exp 100) + 3 ≤ H₀) (hxi : XiCarveWidth H₀)
    (hpr : MmuChiRatePrincipal) : MmuChiRate :=
  mmuChiRate_of_rows (mmuChiRate_nonprincipal hH₀ hxi) hpr

/-- **The bridge to O3, threaded.**  `LambdaChiSummatory A` at the fold's own gates
(`q ≤ (log y)^{11}`, `|t| ≤ ⌊√y⌋`) from the two named inputs — the composition
`LambdaChiSummatory_of_MmuChiRate ∘ mmuChiRate_of_carve_and_principal`. -/
theorem lambdaChiSummatory_of_carve_and_principal {H₀ : ℝ}
    (hH₀ : Real.exp (Real.exp 100) + 3 ≤ H₀) (hxi : XiCarveWidth H₀)
    (hpr : MmuChiRatePrincipal) (A : ℝ) (hA : 0 < A) : LambdaChiSummatory A :=
  LambdaChiSummatory_of_MmuChiRate (mmuChiRate_of_carve_and_principal hH₀ hxi hpr) A hA

/-! ## §6 — ⟦D2 THE χ₀ ROW⟧: reduced to ONE analytic `Prop`

The principal row goes through the SAME mirror, with the pole-normalized carrier

  `g s = mmuG (s − it) · (P_q(s − it))⁻¹`,   `P_q(s) = ∏_{p ∣ q}(1 − p^{−s})`,

because mathlib's `LFunctionTrivChar_eq_mul_riemannZeta` factors `L(s,1) = P_q(s)·ζ(s)` and the
corpus's `Salt.SW.mmuG = (·−1)/Zc` is the analytic continuation of `1/ζ` through the pole.  The
Euler factor is FREE: on `Re ≥ 3/4` every `‖p^{−s}‖ ≤ 3/4`, so `‖P_q(s)⁻¹‖ ≤ 4^{ω(q)} ≤ q²`, a
fixed power of `log H` at `q ≤ (log x)^{12}` — which `pinW`'s `(log H)^m` edge shape absorbs.
No `2^{ω(q)}` sum, no divisor bookkeeping: the inclusion–exclusion route's honest inverse is a
sum over ALL `q`-smooth-supported `n ≤ y` (the Dirichlet inverse of `μ·χ₀` restricted to
divisors of `rad q` is `n ↦ [n ∣ q^∞]`, NOT `d ∣ rad q`), and it is strictly worse. -/

/-- The principal row's Euler factor `P_q(s) = ∏_{p ∣ q}(1 − p^{−s})`. -/
def eulerFac (q : ℕ) (s : ℂ) : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

lemma eulerFac_differentiable (q : ℕ) : Differentiable ℂ (eulerFac q) := by
  intro s
  have h : DifferentiableAt ℂ (∏ p ∈ q.primeFactors, fun z : ℂ => (1 : ℂ) - (p : ℂ) ^ (-z)) s := by
    refine DifferentiableAt.finsetProd (fun p hp => ?_)
    have hp0 : (p : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiableAt_const 1).sub ((differentiableAt_id.neg).const_cpow (Or.inl hp0))
  have heq : (∏ p ∈ q.primeFactors, fun z : ℂ => (1 : ℂ) - (p : ℂ) ^ (-z))
      = fun z : ℂ => ∏ p ∈ q.primeFactors, ((1 : ℂ) - (p : ℂ) ^ (-z)) := by
    funext z; simp [Finset.prod_apply]
  rw [heq] at h
  exact h

/-- Each Euler factor is `≥ 1/4` in modulus on `Re s ≥ 3/4` (`‖p^{−s}‖ ≤ 2^{−3/4} ≤ 3/4`). -/
lemma norm_one_sub_prime_cpow_ge {p : ℕ} (hpp : p.Prime) {s : ℂ} (hs : 3 / 4 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    simp
  have h1 : (p : ℝ) ^ (-s.re) ≤ (3 : ℝ) / 4 := by
    rw [Real.rpow_neg hppos.le]
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ^ s.re := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ s.re :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ (p : ℝ) ^ s.re := Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
    have ha0 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have ha2 : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 2 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hage : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith [ha0, ha2]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  calc (1 : ℝ) / 4 ≤ 1 - ‖(p : ℂ) ^ (-s)‖ := by rw [hnorm]; linarith
    _ ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
        have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
        simpa using this

/-- `1 ≤ 4^{ω(q)}·‖P_q(s)‖` on `Re s ≥ 3/4` — the product form of the per-factor bound. -/
lemma one_le_pow_mul_norm_eulerFac (q : ℕ) {s : ℂ} (hs : 3 / 4 ≤ s.re) :
    1 ≤ (4 : ℝ) ^ q.primeFactors.card * ‖eulerFac q s‖ := by
  rw [eulerFac, norm_prod]
  have h1 : (1 : ℝ) / 4 ^ q.primeFactors.card
      ≤ ∏ p ∈ q.primeFactors, ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    rw [one_div, ← inv_pow, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have := norm_one_sub_prime_cpow_ge (Nat.prime_of_mem_primeFactors hp) hs
    rw [inv_eq_one_div]; linarith
  have h2 : (0 : ℝ) < (4 : ℝ) ^ q.primeFactors.card := by positivity
  rw [← div_le_iff₀' h2]
  linarith [h1]

lemma eulerFac_ne_zero (q : ℕ) {s : ℂ} (hs : 3 / 4 ≤ s.re) : eulerFac q s ≠ 0 := by
  intro h
  have h1 := one_le_pow_mul_norm_eulerFac q hs
  rw [h, norm_zero, mul_zero] at h1
  linarith

/-- `2^{ω(q)} ≤ q` — from `∏_{p ∣ q} p ∣ q` and `p ≥ 2`. -/
lemma two_pow_omega_le {q : ℕ} (hq : 0 < q) : 2 ^ q.primeFactors.card ≤ q := by
  calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

/-- **The Euler factor is free.**  `‖P_q(s)⁻¹‖ ≤ q²` on `Re s ≥ 3/4`. -/
lemma norm_eulerFac_inv_le {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 3 / 4 ≤ s.re) :
    ‖(eulerFac q s)⁻¹‖ ≤ (q : ℝ) ^ 2 := by
  have hne := eulerFac_ne_zero q hs
  have hpos : (0 : ℝ) < ‖eulerFac q s‖ := norm_pos_iff.mpr hne
  have h1 := one_le_pow_mul_norm_eulerFac q hs
  have h7 : (0 : ℝ) < (4 : ℝ) ^ q.primeFactors.card := by positivity
  have h6 : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_omega_le hq
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card := by positivity
  have h2 : (4 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ 2 := by
    have h4 : (4 : ℝ) ^ q.primeFactors.card
        = (2 : ℝ) ^ q.primeFactors.card * (2 : ℝ) ^ q.primeFactors.card := by
      rw [← mul_pow]; norm_num
    rw [h4]; nlinarith [h5, h6]
  have h8 : (1 : ℝ) / (4 : ℝ) ^ q.primeFactors.card ≤ ‖eulerFac q s‖ := by
    rw [div_le_iff₀ h7]; nlinarith [h1]
  rw [norm_inv]
  calc ‖eulerFac q s‖⁻¹ ≤ ((1 : ℝ) / (4 : ℝ) ^ q.primeFactors.card)⁻¹ :=
        (inv_le_inv₀ hpos (by positivity)).mpr h8
    _ = (4 : ℝ) ^ q.primeFactors.card := by rw [one_div, inv_inv]
    _ ≤ (q : ℝ) ^ 2 := h2

/-- **⟦THE ONE OPEN ANALYTIC INPUT⟧ — the `ζ` twin of `lFunctionInvShallowVkSharp_holds`.**
At the SAME sharp width read at `q = 1` (`vkShallowWidthSharp c₄ 1 H = c₄/((log H)^{3/4}
(log log H)⁴)`, since `log 1 = 0`): the shallow box is zero-free and the continuation
`Salt.SW.mmuG = (·−1)/Zc` of `1/ζ` is polynomially bounded there.

This is `Salt.SW.zeta_inv_shallow` moved from the CLASSICAL width `c₄/log⁹(|t|+2)` to the VK
width — the ONLY thing between this file and `MmuChiRate`.  See the residue note below for the
route and for why the landed `Salt.MR.zeta_pow_lower`/`zeta_lower_all_t` (VK width, but only on
`Re ≥ 1`) do not give it. -/
def ZetaInvShallowVk : Prop :=
  ∃ (c₄ K : ℝ) (m : ℕ), 0 < c₄ ∧ 0 < K ∧
    ∀ H : ℝ, Real.exp (Real.exp 100) + 1 ≤ H →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 - vkShallowWidthSharp c₄ 1 H ≤ ρ.re →
          |ρ.im| ≤ H → False) ∧
      (∀ σ τ : ℝ, 1 - vkShallowWidthSharp c₄ 1 H ≤ σ → σ ≤ 2 → |τ| ≤ H →
        ‖Salt.SW.mmuG ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ K * Real.log H ^ m)

/-- `pinW c₅ (2x) ≤ 1/4` — the crude smallness the Euler-factor bound needs. -/
lemma pinW_le_quarter {c₅ : ℝ} (hc₅1 : c₅ ≤ 1) {x : ℝ}
    (hx : Real.exp (Real.exp 100) + 3 ≤ x) : pinW c₅ (2 * x) ≤ 1 / 4 := by
  obtain ⟨hxpos, hL101, hL2lo, _hL2hi, hll⟩ := pin_scale_facts hx
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  have hR1 : (1 : ℝ) ≤ Real.log (2 * x) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hl0 : (0 : ℝ) < Real.log (Real.log (2 * x)) := by linarith
  have hl6 : (4 : ℝ) ≤ Real.log (Real.log (2 * x)) ^ (6 : ℕ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hll 6
    nlinarith [h]
  rw [pinW, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hR1, hl6, hc₅1]

set_option maxHeartbeats 4000000 in
-- The principal row threads the pole-normalized carrier (mmuG × the Euler factor) through §1,
-- §2 and §3; the elaborator needs headroom well past the default, as in §4.
/-- **⟦D2⟧ THE χ₀ ROW, from the ζ twin.**  `ZetaInvShallowVk → MmuChiRatePrincipal`: the
principal row of the slot, at the same ⟦D1⟧-amended gates, with the SAME mirror. -/
theorem mmuChiRatePrincipal_of_zetaShallow (hz : ZetaInvShallowVk) : MmuChiRatePrincipal := by
  obtain ⟨c₄, K, m, hc₄0, hK0, Hz⟩ := hz
  set c₅ : ℝ := min 1 (c₄ / 169) with hc₅def
  have hc₅1 : c₅ ≤ 1 := min_le_left _ _
  have hc₅0 : 0 < c₅ := lt_min one_pos (by positivity)
  have hcA : c₅ ≤ c₄ / 169 := min_le_right _ _
  have h169 : 169 * c₅ ≤ c₄ := by rw [le_div_iff₀ (by norm_num)] at hcA; linarith
  set Kp : ℝ := max 1 K with hKpdef
  have hKp1 : (1 : ℝ) ≤ Kp := le_max_left _ _
  have hKple : K ≤ Kp := le_max_right _ _
  refine mmuChiRate_of_smoothed (fun q χ => χ = 1) ?_
  refine mmu1Chi_rate_of_pinned (c₅ := c₅) (K := Kp) (m := m + 24)
    (X₁ := Real.exp (Real.exp 100) + 3) hc₅0 hc₅1 hKp1 (fun q χ => χ = 1) ?_
  intro x hxX1 q _ χ hχ1 hq t ht
  subst hχ1
  obtain ⟨hxpos, hL101, hL2lo, hL2hi, hll⟩ := pin_scale_facts hxX1
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL2pos : (0 : ℝ) < Real.log (2 * x) := by linarith
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  -- ⟦the abscissae⟧
  set W : ℝ := pinW c₅ (2 * x) with hWdef
  have hq1cast : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (12 : ℕ) := by
    push_cast
    exact one_le_pow₀ (by linarith)
  have hWsharp : W ≤ vkShallowWidthSharp c₄ 1 (2 * x) :=
    pinW_le_sharp hc₄0 hc₅0 h169 hxX1 hq1cast
  have hW4 : W ≤ 1 / 4 := pinW_le_quarter hc₅1 hxX1
  have hW0 : 0 < W := by
    rw [hWdef, pinW]
    have hR0 : (0 : ℝ) < Real.log (2 * x) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL2pos _
    have hl0 : (0 : ℝ) < Real.log (Real.log (2 * x)) := by linarith
    exact div_pos hc₅0 (mul_pos hR0 (pow_pos hl0 6))
  set σ₀ : ℝ := 1 - W with hσ₀def
  have hσ₀pos : (0 : ℝ) < σ₀ := by rw [hσ₀def]; linarith
  have hσ₀34 : (3 : ℝ) / 4 ≤ σ₀ := by rw [hσ₀def]; linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hinvL1 : 1 / Real.log x ≤ 1 := by rw [div_le_one hLpos]; linarith
  have hinvL0 : (0 : ℝ) < 1 / Real.log x := by positivity
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc2 : c ≤ 2 := by rw [hcdef]; linarith
  have hσ₀c : σ₀ < c := by rw [hσ₀def, hcdef]; linarith
  set T : ℝ := pinT x with hTdef
  have hT0 : 0 < T := by rw [hTdef, pinT]; exact Real.exp_pos _
  have hTx : T ≤ x := by
    rw [hTdef, pinT]
    have h1 : Real.log x ^ ((1 : ℝ) / 10) ≤ Real.log x := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ Real.log x by linarith)
        (show (1 : ℝ) / 10 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    calc Real.exp (Real.log x ^ ((1 : ℝ) / 10)) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr h1
      _ = x := Real.exp_log hxpos
  have hshre : ∀ s : ℂ, (s - (t : ℂ) * I).re = s.re := by intro s; simp
  have hshim : ∀ s : ℂ, (s - (t : ℂ) * I).im = s.im - t := by intro s; simp
  obtain ⟨Hzf, Hbd⟩ := Hz (2 * x) (by linarith)
  -- ⟦`Zc ≠ 0` on the shifted box⟧
  have hZcne : ∀ s : ℂ, σ₀ ≤ s.re → |s.im| ≤ T → Salt.SW.Zc (s - (t : ℂ) * I) ≠ 0 := by
    intro s h1 h3
    by_cases he : s - (t : ℂ) * I = 1
    · rw [he, Salt.SW.Zc_one]; exact one_ne_zero
    · rw [Salt.SW.Zc_eq_of_ne he]
      refine mul_ne_zero (sub_ne_zero.mpr he) (fun hζ => Hzf _ hζ ?_ ?_)
      · rw [hshre]; rw [hσ₀def] at h1; linarith
      · rw [hshim]
        calc |s.im - t| ≤ |s.im| + |t| := abs_sub _ _
          _ ≤ T + x := add_le_add h3 ht
          _ ≤ 2 * x := by linarith
  -- ⟦the carrier's box bound⟧
  have hgbox : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T →
      ‖Salt.SW.mmuG (s - (t : ℂ) * I) * (eulerFac q (s - (t : ℂ) * I))⁻¹‖
        ≤ Kp * Real.log (2 * x) ^ (m + 24) := by
    intro s h1 h2 h3
    have hpt : s - (t : ℂ) * I = ((s.re : ℝ) : ℂ) + ((s.im - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hIm2 : |s.im - t| ≤ 2 * x := by
      calc |s.im - t| ≤ |s.im| + |t| := abs_sub _ _
        _ ≤ T + x := add_le_add h3 ht
        _ ≤ 2 * x := by linarith
    have hb1 : ‖Salt.SW.mmuG (s - (t : ℂ) * I)‖ ≤ K * Real.log (2 * x) ^ m := by
      rw [hpt]
      exact Hbd s.re (s.im - t) (by rw [hσ₀def] at h1; linarith) (by linarith) hIm2
    have hre34 : (3 : ℝ) / 4 ≤ (s - (t : ℂ) * I).re := by rw [hshre]; linarith
    have hb2 : ‖(eulerFac q (s - (t : ℂ) * I))⁻¹‖ ≤ (q : ℝ) ^ 2 :=
      norm_eulerFac_inv_le hqpos hre34
    have hq24 : (q : ℝ) ^ 2 ≤ Real.log (2 * x) ^ 24 := by
      have hq12 : (q : ℝ) ≤ Real.log (2 * x) ^ (12 : ℕ) :=
        le_trans hq (pow_le_pow_left₀ (by linarith) hL2lo 12)
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      calc (q : ℝ) ^ 2 ≤ (Real.log (2 * x) ^ (12 : ℕ)) ^ 2 := by
            exact pow_le_pow_left₀ hq0 hq12 2
        _ = Real.log (2 * x) ^ 24 := by rw [← pow_mul]
    have hKnn : (0 : ℝ) ≤ K * Real.log (2 * x) ^ m := by positivity
    calc ‖Salt.SW.mmuG (s - (t : ℂ) * I) * (eulerFac q (s - (t : ℂ) * I))⁻¹‖
        = ‖Salt.SW.mmuG (s - (t : ℂ) * I)‖ * ‖(eulerFac q (s - (t : ℂ) * I))⁻¹‖ := norm_mul _ _
      _ ≤ (K * Real.log (2 * x) ^ m) * Real.log (2 * x) ^ 24 :=
          mul_le_mul hb1 (le_trans hb2 hq24) (norm_nonneg _) hKnn
      _ = K * Real.log (2 * x) ^ (m + 24) := by rw [pow_add]; ring
      _ ≤ Kp * Real.log (2 * x) ^ (m + 24) :=
          mul_le_mul_of_nonneg_right hKple (by positivity)
  -- ⟦analyticity on the box⟧
  have hrect : ∀ s : ℂ, s ∈ Salt.SW.closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I) →
      σ₀ ≤ s.re ∧ s.re ≤ c ∧ |s.im| ≤ T := by
    intro s hs
    have hzre : ((σ₀ : ℂ) - (T : ℂ) * I).re = σ₀ := by simp
    have hzim : ((σ₀ : ℂ) - (T : ℂ) * I).im = -T := by simp
    have hwre : ((c : ℂ) + (T : ℂ) * I).re = c := by simp
    have hwim : ((c : ℂ) + (T : ℂ) * I).im = T := by simp
    rw [Salt.SW.closedRect, hzre, hzim, hwre, hwim, Complex.mem_reProdIm,
      Set.uIcc_of_le hσ₀c.le, Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hre, him⟩ := hs
    simp only [Set.mem_Icc] at hre him
    exact ⟨hre.1, hre.2, abs_le.mpr ⟨him.1, him.2⟩⟩
  have hgana : DifferentiableOn ℂ
      (fun s : ℂ => Salt.SW.mmuG (s - (t : ℂ) * I) * (eulerFac q (s - (t : ℂ) * I))⁻¹)
      (Salt.SW.closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c : ℂ) + (T : ℂ) * I)) := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hrect s hs
    have hsh : DifferentiableAt ℂ (fun z : ℂ => z - (t : ℂ) * I) s := by fun_prop
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => Salt.SW.mmuG (z - (t : ℂ) * I)) s := by
      have h := (Salt.SW.mmuG_differentiableAt (hZcne s h1 h3)).comp s hsh
      exact h
    have hre34 : (3 : ℝ) / 4 ≤ (s - (t : ℂ) * I).re := by rw [hshre]; linarith
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => eulerFac q (z - (t : ℂ) * I)) s := by
      have h := (eulerFac_differentiable q _).comp s hsh
      exact h
    exact ((hd1.mul (hd2.inv (eulerFac_ne_zero q hre34))).differentiableWithinAt)
  -- ⟦the `c`-line: the factorization and the continuity⟧
  have hcline_ne1 : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I ≠ 1 := by
    intro v h
    have hre : (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I).re = c := by simp
    rw [h] at hre; simp at hre; linarith
  have hcline_re : ∀ v : ℝ, 1 < (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I).re := by
    intro v
    have hre : (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I).re = c := by simp
    rw [hre]; exact hc1
  have hcline_ζ : ∀ v : ℝ, riemannZeta (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) ≠ 0 :=
    fun v => riemannZeta_ne_zero_of_one_lt_re (hcline_re v)
  have hcline_Zc : ∀ v : ℝ, Salt.SW.Zc (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) ≠ 0 := by
    intro v
    rw [Salt.SW.Zc_eq_of_ne (hcline_ne1 v)]
    exact mul_ne_zero (sub_ne_zero.mpr (hcline_ne1 v)) (hcline_ζ v)
  have hcline_euler : ∀ v : ℝ, eulerFac q (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) ≠ 0 := by
    intro v
    refine eulerFac_ne_zero q ?_
    have hre : (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I).re = c := by simp
    rw [hre]; linarith
  have hgcline : ∀ v : ℝ,
      Salt.SW.mmuG (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)
          * (eulerFac q (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I))⁻¹
        = (LFunction (1 : DirichletCharacter ℂ q)⁻¹
            ((c : ℂ) + ((v - t : ℝ) : ℂ) * I))⁻¹ := by
    intro v
    have harg : ((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I = (c : ℂ) + ((v - t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [inv_one, harg]
    have hne1 : (c : ℂ) + ((v - t : ℝ) : ℂ) * I ≠ 1 := by rw [← harg]; exact hcline_ne1 v
    have hζ : riemannZeta ((c : ℂ) + ((v - t : ℝ) : ℂ) * I) ≠ 0 := by
      rw [← harg]; exact hcline_ζ v
    have hfac : LFunction (1 : DirichletCharacter ℂ q) ((c : ℂ) + ((v - t : ℝ) : ℂ) * I)
        = (∏ p ∈ q.primeFactors,
              (1 - (p : ℂ) ^ (-((c : ℂ) + ((v - t : ℝ) : ℂ) * I))))
            * riemannZeta ((c : ℂ) + ((v - t : ℝ) : ℂ) * I) :=
      LFunctionTrivChar_eq_mul_riemannZeta hne1
    rw [Salt.SW.mmuG_eq_zeta_inv hne1 hζ, hfac, mul_inv, eulerFac]
    ring
  have hgcont : Continuous fun v : ℝ =>
      Salt.SW.mmuG (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)
        * (eulerFac q (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I))⁻¹ := by
    have hline : Continuous fun v : ℝ => ((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I := by fun_prop
    have hc1' : Continuous fun v : ℝ => Salt.SW.mmuG (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) := by
      have hrw : (fun v : ℝ => Salt.SW.mmuG (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I))
          = fun v : ℝ => ((((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) - 1)
              / Salt.SW.Zc (((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) := by
        funext v; rw [Salt.SW.mmuG]
      rw [hrw]
      exact (by fun_prop : Continuous fun v : ℝ =>
        ((((c : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) - 1)).div
          (Salt.SW.Zc_differentiable.continuous.comp hline) hcline_Zc
    exact hc1'.mul (((eulerFac_differentiable q).continuous.comp hline).inv₀ hcline_euler)
  have hBbox0 : (0 : ℝ) ≤ Kp * Real.log (2 * x) ^ (m + 24) :=
    mul_nonneg (by linarith) (pow_nonneg hL2pos.le _)
  refine le_trans (mmu1Chi_contour_shift (1 : DirichletCharacter ℂ q) t hx1 hc1 hT0 hσ₀pos
    hσ₀c hBbox0 hgcline hgcont hgana hgbox) ?_
  have heq : (1 : ℝ) + 1 / (c - 1) = Real.log x + 1 := by
    rw [hcdef, show (1 + 1 / Real.log x) - 1 = 1 / Real.log x by ring, one_div_one_div]
    ring
  rw [heq]

/-- **⟦THE MIRROR'S FULL DELIVERABLE⟧ — `MmuChiRate` from TWO named analytic inputs.**  The
ξ₁/Siegel carve-out (wave P-7's fold, strong form) and the ζ shallow twin at VK width.
Everything else — the twisted contour shift, the budget, the de-smoothing, the χ-VK edge bound
and region, the χ₀ row's pole normalization and Euler factor — is landed. -/
theorem mmuChiRate_of_carve_and_zetaShallow {H₀ : ℝ}
    (hH₀ : Real.exp (Real.exp 100) + 3 ≤ H₀) (hxi : XiCarveWidth H₀)
    (hz : ZetaInvShallowVk) : MmuChiRate :=
  mmuChiRate_of_carve_and_principal hH₀ hxi (mmuChiRatePrincipal_of_zetaShallow hz)

/-- The O3 bridge at the full pair of inputs. -/
theorem lambdaChiSummatory_of_carve_and_zetaShallow {H₀ : ℝ}
    (hH₀ : Real.exp (Real.exp 100) + 3 ≤ H₀) (hxi : XiCarveWidth H₀)
    (hz : ZetaInvShallowVk) (A : ℝ) (hA : 0 < A) : LambdaChiSummatory A :=
  LambdaChiSummatory_of_MmuChiRate (mmuChiRate_of_carve_and_zetaShallow hH₀ hxi hz) A hA

/-! ### ⟦THE RESIDUE — the χ₀ row, and exactly what closes it⟧

After §6 the χ₀ row is REDUCED, in the kernel, to ONE analytic `Prop`:
`mmuChiRatePrincipal_of_zetaShallow : ZetaInvShallowVk → MmuChiRatePrincipal`.  Everything
mechanical is landed; the residue is `ZetaInvShallowVk` and nothing else.  What §6 pays, and
what it does not, recorded because the accounting is the finding:

1. the carrier is the pole-normalized `g s = mmuG (s − it)·(P_q(s − it))⁻¹` — the naive inverse
   will NOT do, because `L(·, 1 mod q)` has a POLE at `s = 1` (mathlib's value there is junk);
   `Salt.SW.mmuG = (·−1)/Zc` is the corpus's landed continuation of `1/ζ` and
   `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` supplies the factorization.  LANDED;
2. the Euler factor is FREE: `‖P_q(s)⁻¹‖ ≤ 4^{ω(q)} ≤ q²` on `Re ≥ 3/4` (`norm_eulerFac_inv_le`,
   via `2^{ω(q)} ≤ q`), and `q ≤ (log x)^{12}` makes that `≤ (log H)^{24}`, absorbed by §2's
   `K·(log H)^m` edge shape.  LANDED, and it is why NO `2^{ω(q)}` summation appears;
3. the box's non-vanishing of `ζ` and of every `1 − p^{−s}`: the second is free (same estimate),
   the FIRST is folded into `ZetaInvShallowVk`'s first conjunct — the ζ zero-free region at VK
   width, which the corpus HAS above the landed floor (`Salt.Vk.zeta_zero_free_region_pow`) and
   classically below it, so that conjunct is a composition, not a stone.

**So the ONE open input is the ζ twin of `lFunctionInvShallowVkSharp_holds`** — the second
conjunct of `ZetaInvShallowVk`, i.e. the `q = 1` shallow bound at VK width, which the corpus
does NOT have: the landed
`Salt.SW.zeta_inv_shallow` is at the CLASSICAL width `c₄/log⁹(|t|+2)`, worth only
`|t| ≤ exp((log y)^{1−δ})` of height (the ⟦D1⟧ audit's own arithmetic), and the landed
`Salt.MR.zeta_pow_lower` / `zeta_lower_all_t` are at VK width but only on `Re ≥ 1` — a lower
bound to the RIGHT of the 1-line, from which no shallow bound follows: the Cauchy/MVT transport
to `Re = 1 − w` costs a full power of `log H` in the width (`Salt.SW.zeta_lower_shallow`'s own
route: width `log⁻⁹`, value `log⁻⁷`), and a width `≪ 1/log H` gives NO saving at `|t| ≍ y`.

**The route, and the one place it differs from §1 of `LFunctionInvShallow`.**  Same Landau ball:
`Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` on the NORMALIZED `Zc/Zc(c)` (the pole patch:
`Zc` is entire, `Zc 1 = 1`, and the ratio kills the `‖s−1‖ ≍ |τ|` factor because
`‖c−1‖/‖s−1‖ ≥ 1/2` on the segment — the pole is FAR at large `|τ|`), growth from the landed
`Salt.Vk.zeta_growth_pow`, region from the landed `Salt.Vk.zeta_zero_free_region_pow`, and the
reference floor from the landed `Salt.MR.zeta_pow_lower_far` (`‖ζ((1+d')+iτ)‖ ≥ d'/32`,
unconditional — the exact ζ analogue of `LFunction_near_one_lower`).  Below the VK floor
`|τ| ≤ T₀` the landed `Salt.SW.zeta_lower_shallow` / `Zc_patch_lower` give CONSTANTS (no `q`,
so unlike the χ case there is no Pólya–Vinogradov arm).  Estimated at §1+§2's length again
(~300–500 ln); the private `Salt.MR.zeta_near_bound_core` is the closest landed relative and
is NOT reusable across modules as written (it is `private`).

No `ω(q)`/`2^{ω(q)}` bookkeeping is needed on this route — item 2 above replaces it by the
crude `(1 − 2^{−1/2})^{−ω(q)} ≤ q²` bound, which the `(log H)^m` shape absorbs.  That is the
one simplification the Euler-product route buys over the divisor/inclusion–exclusion route
(whose honest inverse is a sum over ALL `q`-smooth-supported `n ≤ y`, not over `d ∣ rad q`). -/

end Salt.MR

end
