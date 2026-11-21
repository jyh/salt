/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.VonKoch
import Salt.SW.ContourShift

/-!
# O106 row R1, nodes N5, N6 — the rectangle, its residue at `s = 1`, and the edges

Under RH, `Zc` has no zero on `Re s > 1/2`, so

`φ(s) := (1 − (s − 1)·logDeriv Zc s) · y^s / s`

is holomorphic on the closed rectangle `[σ₀, c₀] × [−T, T]` for `1/2 < σ₀ < 1 < c₀`. This is the
refuter pass's repair 2: written through `Zc`, `φ(1) = y`, while the `ζ` form reads `0` at `1`.
The residues-lite Cauchy formula (`Salt.SW.rectBI_cif_eq`) then gives
`rectBI (σ₀ − iT) (c₀ + iT) (φ / (s − 1)) = 2πi · y`. Off `s = 1`,
`φ(s)/(s − 1) = −ζ′/ζ(s) · y^s/s` (`phiR_div_eq`), which is the Perron integrand on `Re s > 1`.
-/

namespace Salt.RH

open Complex Salt.SW

/-- The residue-carrying numerator. -/
noncomputable def phiR (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * logDeriv Zc s) * (y : ℂ) ^ s / s

theorem phiR_one {y : ℝ} : phiR y 1 = y := by
  simp [phiR]

/-- `logDeriv Zc` is differentiable wherever `Zc ≠ 0`. -/
theorem differentiableAt_logDeriv_Zc {s : ℂ} (hs : Zc s ≠ 0) :
    DifferentiableAt ℂ (logDeriv Zc) s := by
  have han : AnalyticAt ℂ Zc s := Zc_differentiable.analyticAt s
  have hd : DifferentiableAt ℂ (deriv Zc) s := han.deriv.differentiableAt
  have : logDeriv Zc = fun z => deriv Zc z / Zc z := by
    funext z; rw [logDeriv_apply]
  rw [this]
  exact hd.div (Zc_differentiable s) hs

theorem differentiableAt_phiR (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (phiR y) s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hZ := differentiableAt_logDeriv_Zc (zc_ne_zero_of_half_lt hRH hs)
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (y : ℂ) ^ z) s :=
    (differentiableAt_id.const_cpow (Or.inl hy0))
  unfold phiR
  refine DifferentiableAt.div ?_ differentiableAt_id hs0
  refine DifferentiableAt.mul ?_ hpow
  exact (differentiableAt_const _).sub ((differentiableAt_id.sub_const _).mul hZ)

/-- **N5.** Under RH, for `1/2 < σ₀ < 1 < c₀` and `T > 0`,
`rectBI (σ₀ − iT) (c₀ + iT) (φ / (s − 1)) = 2πi · y`. -/
theorem rectBI_phiR_eq (hRH : RiemannHypothesis) {y σ₀ c₀ T : ℝ} (hy : 0 < y)
    (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) (h2 : 1 < c₀) (hT : 0 < T) :
    rectBI ((σ₀ : ℂ) - (T : ℂ) * I) ((c₀ : ℂ) + (T : ℂ) * I) (fun s => phiR y s / (s - 1))
      = 2 * (Real.pi : ℂ) * I * y := by
  have hdiff : DifferentiableOn ℂ (phiR y)
      (closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c₀ : ℂ) + (T : ℂ) * I)) := by
    intro s hs
    have hre : s.re ∈ Set.uIcc σ₀ c₀ := by
      have := (Complex.mem_reProdIm.mp hs).1
      simpa using this
    have hre' : σ₀ ≤ s.re := by
      rw [Set.uIcc_of_le (by linarith)] at hre; exact hre.1
    exact (differentiableAt_phiR hRH hy (by linarith)).differentiableWithinAt
  have h := rectBI_cif_eq (p := 1) hdiff (by simp; linarith) (by simp; linarith)
    (by refine ⟨?_, ?_⟩ <;> simp <;> linarith) (by refine ⟨?_, ?_⟩ <;> simp <;> linarith)
  rw [h, phiR_one]

/-- Off `s = 1`, with `ζ s ≠ 0`, the integrand is `−ζ′/ζ(s) · y^s / s`. -/
theorem phiR_div_eq {y : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    phiR y s / (s - 1) = -logDeriv riemannZeta s * Salt.MR.pk y s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hZc : Zc =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz1
    exact Zc_eq_of_ne hz1
  have hdz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd : deriv Zc s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hZc.deriv_eq]
    have h' : HasDerivAt (fun z => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id' s).sub_const 1).mul hdz.hasDerivAt
    rw [h'.deriv]
    ring
  have hld : logDeriv Zc s = 1 / (s - 1) + logDeriv riemannZeta s := by
    rw [logDeriv_apply, logDeriv_apply, hd, Zc_eq_of_ne hs1]
    field_simp
  unfold phiR Salt.MR.pk
  rw [hld]
  field_simp
  ring

/-! ## N6 — the three other edges -/

/-- The integrand through `Zc`: `φ/(s − 1) = (1/(s − 1) − logDeriv Zc s) · y^s/s`, for `s ≠ 1`. -/
theorem phiR_div_eq_Zc {y : ℝ} {s : ℂ} (hs1 : s ≠ 1) :
    phiR y s / (s - 1) = (1 / (s - 1) - logDeriv Zc s) * Salt.MR.pk y s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold phiR Salt.MR.pk
  field_simp

theorem norm_pk_eq {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖Salt.MR.pk y s‖ = y ^ s.re / ‖s‖ := by
  unfold Salt.MR.pk
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]

/-- The pointwise edge bound, from N3's constant `K`. -/
theorem norm_edge_le {K y : ℝ} (_hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv Zc s‖ ≤ K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 0 < y) {s : ℂ} (hs1 : 1 / 4 ≤ ‖s - 1‖) (h1 : 1 / 2 < s.re) (h2 : s.re ≤ 23 / 10) :
    ‖phiR y s / (s - 1)‖
      ≤ (4 + K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2))) * (y ^ s.re / ‖s‖) := by
  have hne : s ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hs1; norm_num at hs1
  rw [phiR_div_eq_Zc hne, norm_mul, norm_pk_eq hy]
  have hinv : ‖1 / (s - 1)‖ ≤ 4 := by
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsum : ‖1 / (s - 1) - logDeriv Zc s‖
      ≤ 4 + K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2)) :=
    le_trans (norm_sub_le _ _) (add_le_add hinv (hK s h1 h2))
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

/-- `∫_{−T}^{T} 1/(1 + |v|) dv = 2 log(1 + T)`. -/
theorem integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ v in (-T)..T, 1 / (1 + |v|) = 2 * Real.log (1 + T) := by
  have hcont : Continuous fun v : ℝ => 1 / (1 + |v|) := by
    refine Continuous.div continuous_const (by fun_prop) fun v => ?_
    have := abs_nonneg v; linarith
  have hpos : ∫ v in (0 : ℝ)..T, 1 / (1 + |v|) = Real.log (1 + T) := by
    have h1 : ∫ v in (0 : ℝ)..T, 1 / (1 + |v|) = ∫ v in (0 : ℝ)..T, 1 / (1 + v) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hT] at hv
      simp only [abs_of_nonneg hv.1]
    rw [h1]
    have h2 : ∫ v in (0 : ℝ)..T, 1 / (1 + v) = ∫ u in (1 : ℝ)..(1 + T), 1 / u := by
      have := intervalIntegral.integral_comp_add_left (fun u : ℝ => 1 / u) (1 : ℝ)
        (a := 0) (b := T)
      simp at this ⊢
    rw [h2, integral_one_div_of_pos one_pos (by linarith), div_one]
  have hneg : ∫ v in (-T)..(0 : ℝ), 1 / (1 + |v|) = Real.log (1 + T) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := T) (fun v : ℝ => 1 / (1 + |v|))
    simp only [abs_neg, neg_zero] at this
    rw [← this, hpos]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg, hpos]
  ring

/-- **N6, the left edge.** For `1/2 < σ₀ ≤ 3/4`, `T ≥ 0`:
`‖∫_{−T}^{T} φ(σ₀ + iv)/(σ₀ + iv − 1) dv‖ ≤ A · y^{σ₀} · 8 log(1 + T)`,
`A = 4 + K log(T + 3)(1 + 1/(σ₀ − 1/2))`. -/
theorem left_edge_le {K y σ₀ T : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv Zc s‖ ≤ K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 0 < y) (h0 : 1 / 2 < σ₀) (h1 : σ₀ ≤ 3 / 4) (hT : 0 ≤ T) :
    ‖∫ v in (-T)..T, phiR y ((σ₀ : ℂ) + (v : ℂ) * I) / (((σ₀ : ℂ) + (v : ℂ) * I) - 1)‖
      ≤ (4 + K * Real.log (T + 3) * (1 + 1 / (σ₀ - 1 / 2))) * y ^ σ₀ * (8 * Real.log (1 + T)) := by
  set A : ℝ := 4 + K * Real.log (T + 3) * (1 + 1 / (σ₀ - 1 / 2)) with hA
  have hd0 : 0 < σ₀ - 1 / 2 := by linarith
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hbound : ∀ v : ℝ, v ∈ Set.Ioc (-T) T →
      ‖phiR y ((σ₀ : ℂ) + (v : ℂ) * I) / (((σ₀ : ℂ) + (v : ℂ) * I) - 1)‖
        ≤ A * y ^ σ₀ * (4 * (1 / (1 + |v|))) := by
    intro v hv
    set s : ℂ := (σ₀ : ℂ) + (v : ℂ) * I with hs
    have hre : s.re = σ₀ := by simp [hs]
    have him : s.im = v := by simp [hs]
    have hs1 : 1 / 4 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hre, Complex.one_re, abs_of_neg (by linarith)] at h
      linarith
    have hpt := norm_edge_le hK0 hK hy hs1 (by rw [hre]; exact h0) (by rw [hre]; linarith)
    rw [hre, him] at hpt
    have hvT : |v| ≤ T := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
    have hlog : Real.log (|v| + 3) ≤ Real.log (T + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hfac : 4 + K * Real.log (|v| + 3) * (1 + 1 / (σ₀ - 1 / 2)) ≤ A := by
      rw [hA]
      have : K * Real.log (|v| + 3) ≤ K * Real.log (T + 3) := mul_le_mul_of_nonneg_left hlog hK0
      nlinarith [show (0 : ℝ) ≤ 1 + 1 / (σ₀ - 1 / 2) by positivity]
    have hsn : (1 + |v|) / 4 ≤ ‖s‖ := by
      have hr := Complex.abs_re_le_norm s
      have hi := Complex.abs_im_le_norm s
      rw [hre, abs_of_pos (by linarith)] at hr
      rw [him] at hi
      linarith
    have hsn0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) hsn
    have hinv : y ^ σ₀ / ‖s‖ ≤ y ^ σ₀ * (4 * (1 / (1 + |v|))) := by
      rw [div_le_iff₀ hsn0]
      have hy0 : 0 ≤ y ^ σ₀ := by positivity
      have : 1 ≤ 4 * (1 / (1 + |v|)) * ‖s‖ := by
        rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      nlinarith
    calc ‖phiR y s / (s - 1)‖
        ≤ (4 + K * Real.log (|v| + 3) * (1 + 1 / (σ₀ - 1 / 2))) * (y ^ σ₀ / ‖s‖) := hpt
      _ ≤ A * (y ^ σ₀ * (4 * (1 / (1 + |v|)))) :=
          mul_le_mul hfac hinv (by positivity) hA0
      _ = A * y ^ σ₀ * (4 * (1 / (1 + |v|))) := by ring
  have hcont : Continuous fun v : ℝ => 1 / (1 + |v|) := by
    refine Continuous.div continuous_const (by fun_prop) fun v => ?_
    have := abs_nonneg v; linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (MeasureTheory.ae_of_all MeasureTheory.volume hbound)
    ((hcont.const_mul 4).const_mul (A * y ^ σ₀) |>.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_one_add_abs hT] at hle
  linarith

/-- **N6, a horizontal edge** at height `b` with `|b| ≥ 1`, over `[σ₀, c₀]` with `1/2 < σ₀ ≤ c₀ ≤ 2`
and `y ≥ 1`. -/
theorem horiz_edge_le {K y σ₀ c₀ b : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv Zc s‖ ≤ K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 1 ≤ y) (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ c₀) (h1 : c₀ ≤ 2) (hb : 1 ≤ |b|) :
    ‖∫ x in σ₀..c₀, phiR y ((x : ℂ) + (b : ℂ) * I) / (((x : ℂ) + (b : ℂ) * I) - 1)‖
      ≤ (4 + K * Real.log (|b| + 3) * (1 + 1 / (σ₀ - 1 / 2))) * (y ^ c₀ / |b|) * (c₀ - σ₀) := by
  set A : ℝ := 4 + K * Real.log (|b| + 3) * (1 + 1 / (σ₀ - 1 / 2)) with hA
  have hd0 : 0 < σ₀ - 1 / 2 := by linarith
  have hb0 : 0 < |b| := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₀ c₀,
      ‖phiR y ((x : ℂ) + (b : ℂ) * I) / (((x : ℂ) + (b : ℂ) * I) - 1)‖ ≤ A * (y ^ c₀ / |b|) := by
    intro x hx
    rw [Set.uIoc_of_le h01] at hx
    set s : ℂ := (x : ℂ) + (b : ℂ) * I with hs
    have hre : s.re = x := by simp [hs]
    have him : s.im = b := by simp [hs]
    have hs1 : 1 / 4 ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, him, Complex.one_im, sub_zero] at h
      linarith
    have hx0 : 1 / 2 < x := by linarith [hx.1]
    have hpt0 := norm_edge_le (y := y) hK0 hK (by linarith) hs1 (by rw [hre]; exact hx0)
      (by rw [hre]; linarith [hx.2])
    rw [hre, him] at hpt0
    have hfac : 4 + K * Real.log (|b| + 3) * (1 + 1 / (x - 1 / 2)) ≤ A := by
      rw [hA]
      have h1' : 1 / (x - 1 / 2) ≤ 1 / (σ₀ - 1 / 2) :=
        one_div_le_one_div_of_le hd0 (by linarith [hx.1])
      have hl : 0 ≤ K * Real.log (|b| + 3) :=
        mul_nonneg hK0 (Real.log_nonneg (by linarith))
      nlinarith
    have hsn : |b| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s; rwa [him] at this
    have hyx : y ^ x ≤ y ^ c₀ := Real.rpow_le_rpow_of_exponent_le hy (by linarith [hx.2])
    have hq : y ^ x / ‖s‖ ≤ y ^ c₀ / |b| :=
      div_le_div₀ (by positivity) hyx hb0 hsn
    calc _ ≤ (4 + K * Real.log (|b| + 3) * (1 + 1 / (x - 1 / 2))) * (y ^ x / ‖s‖) := hpt0
      _ ≤ A * (y ^ c₀ / |b|) := mul_le_mul hfac hq (by positivity)
          (by have : 0 ≤ K * Real.log (|b| + 3) := mul_nonneg hK0 (Real.log_nonneg (by linarith))
              positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (show (0 : ℝ) ≤ c₀ - σ₀ by linarith)] at this
  exact this

end Salt.RH
