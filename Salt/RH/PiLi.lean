/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.VonKochFinal

/-!
# O106 row R2 — the prime-counting form: `RiemannHypothesis → PiLi2 3`

The core, `piLi2_of_vonKoch : VonKochPsi 3 → PiLi2 3`, carries NO hypothesis on ζ:
* `|θ(t) − t| ≤ C₁ √t (log t)³` from `VonKochPsi 3` and Mathlib's `|ψ − θ| ≤ 2 √t log t`;
* `Li₂(x) = x / log x − 2 / log 2 + ∫₂ˣ dt / log² t` (FTC on `t / log t`);
* Mathlib's `π(x) = θ(x) / log x + ∫₂ˣ θ(t) / (t log² t) dt`;
so `π(x) − Li₂(x) = (θ(x) − x)/log x + 2/log 2 + ∫₂ˣ (θ(t) − t)/(t log² t) dt`, and the integral is
`≤ C₁ log x ∫₂ˣ t^{−1/2} dt ≤ 2 C₁ √x log x`.
-/

namespace Salt.RH

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `θ` from `VonKochPsi 3`. -/
theorem theta_sub_le_of_vonKoch (hV : VonKochPsi 3) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ t : ℝ, 2 ≤ t →
    |Chebyshev.theta t - t| ≤ C₁ * Real.sqrt t * Real.log t ^ 3 := by
  obtain ⟨C₀, hC₀⟩ := hV
  have hl2 := log_two_pos'
  refine ⟨max C₀ 0 + 2 / Real.log 2 ^ 2, by positivity, fun t ht => ?_⟩
  have h1 := hC₀ t ht
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show (1 : ℝ) ≤ t by linarith)
  have hl : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlt0 : 0 < Real.log t := by linarith
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hlog : Real.log t ≤ Real.log t ^ 3 / Real.log 2 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hl2.le hl 2
    nlinarith
  have hA : C₀ * Real.sqrt t * Real.log t ^ 3 ≤ max C₀ 0 * Real.sqrt t * Real.log t ^ 3 := by
    have h0 : 0 ≤ Real.sqrt t * Real.log t ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) h0
    linarith [mul_assoc C₀ (Real.sqrt t) (Real.log t ^ 3),
      mul_assoc (max C₀ 0) (Real.sqrt t) (Real.log t ^ 3)]
  have hB : 2 * Real.sqrt t * Real.log t ≤ 2 / Real.log 2 ^ 2 * Real.sqrt t * Real.log t ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Real.sqrt t by positivity)
    calc 2 * Real.sqrt t * Real.log t ≤ 2 * Real.sqrt t * (Real.log t ^ 3 / Real.log 2 ^ 2) := this
      _ = 2 / Real.log 2 ^ 2 * Real.sqrt t * Real.log t ^ 3 := by ring
  have htri : |Chebyshev.theta t - t|
      ≤ |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
    have := abs_sub_le (Chebyshev.theta t) (Chebyshev.psi t) t
    rw [abs_sub_comm (Chebyshev.theta t) (Chebyshev.psi t)] at this
    linarith
  have : (max C₀ 0 + 2 / Real.log 2 ^ 2) * Real.sqrt t * Real.log t ^ 3
      = max C₀ 0 * Real.sqrt t * Real.log t ^ 3
        + 2 / Real.log 2 ^ 2 * Real.sqrt t * Real.log t ^ 3 := by ring
  linarith

/-- `Li₂(x) = x / log x − 2 / log 2 + ∫₂ˣ dt / log² t`. -/
theorem Li2_eq {x : ℝ} (hx : 2 ≤ x) :
    Li2 x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, 2 ≤ t := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; exact ht.1
  have hlog : ∀ t ∈ Set.uIcc (2 : ℝ) x, Real.log t ≠ 0 := fun t ht =>
    (Real.log_pos (by linarith [hpos t ht])).ne'
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun t => t / Real.log t) (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [hpos t ht]
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) (hlog t ht)
    have e : (1 * Real.log t - id t * t⁻¹) / Real.log t ^ 2
        = 1 / Real.log t - 1 / Real.log t ^ 2 := by
      have hl := hlog t ht
      simp only [id, one_mul, mul_inv_cancel₀ ht0]
      field_simp
    rw [e] at h
    exact h
  have hc1 : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
    refine ContinuousOn.div continuousOn_const ?_ hlog
    exact Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]
  have hc2 : ContinuousOn (fun t : ℝ => 1 / Real.log t ^ 2) (Set.uIcc 2 x) := by
    refine ContinuousOn.div continuousOn_const ?_ fun t ht => pow_ne_zero 2 (hlog t ht)
    exact (Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]).pow 2
  have hint := (hc1.sub hc2).intervalIntegrable (μ := MeasureTheory.volume)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable] at hftc
  unfold Li2
  linarith

/-- The error identity. -/
theorem primeCounting_sub_Li2 {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li2 x
      = (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, Li2_eq hx]
  have hθ : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) x, 2 ≤ t := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; exact ht.1
  have hc2 : ContinuousOn (fun t : ℝ => 1 / Real.log t ^ 2) (Set.uIcc 2 x) := by
    refine ContinuousOn.div continuousOn_const ?_ fun t ht =>
      pow_ne_zero 2 (Real.log_pos (by linarith [hpos t ht])).ne'
    exact (Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]).pow 2
  have hcong : ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
      = ∫ t in (2 : ℝ)..x, (Chebyshev.theta t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [hpos t ht]
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [hpos t ht])).ne'
    field_simp
  rw [hcong, intervalIntegral.integral_sub hθ hc2.intervalIntegrable]
  have hl0 : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp
  ring

/-- The integral term: `‖∫₂ˣ (θ t − t)/(t log² t) dt‖ ≤ 2 C₁ log x √x`. -/
theorem integral_err_le {C₁ x : ℝ} (hC₁ : 0 ≤ C₁)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C₁ * Real.sqrt t * Real.log t ^ 3)
    (hx : 2 ≤ x) :
    ‖∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖
      ≤ 2 * C₁ * Real.log x * Real.sqrt x := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hpt : ∀ t ∈ Set.Ioc (2 : ℝ) x,
      ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤ C₁ * Real.log x * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have ht2 : 2 < t := ht.1
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hrp : t ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt t := by
      rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, one_div]
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, hrp]
    have h1 := hθ t ht2.le
    rw [div_le_iff₀ hden]
    have hlog : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
    calc |Chebyshev.theta t - t| ≤ C₁ * Real.sqrt t * Real.log t ^ 3 := h1
      _ = C₁ * Real.log t * (1 / Real.sqrt t) * (t * Real.log t ^ 2) := by
          have e : C₁ * Real.log t * (1 / Real.sqrt t) * (t * Real.log t ^ 2)
              = C₁ * Real.log t ^ 3 * (t / Real.sqrt t) := by ring
          rw [e, Real.div_sqrt]; ring
      _ ≤ C₁ * Real.log x * (1 / Real.sqrt t) * (t * Real.log t ^ 2) := by
          gcongr
  have hint : IntervalIntegrable (fun t : ℝ => C₁ * Real.log x * t ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 2 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hle := intervalIntegral.norm_integral_le_of_norm_le hx
    (MeasureTheory.ae_of_all MeasureTheory.volume hpt) hint
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))] at hle
  have hx0 : 0 ≤ x := by linarith
  have hval : (x ^ (-(1 / 2 : ℝ) + 1) - (2 : ℝ) ^ (-(1 / 2 : ℝ) + 1)) / (-(1 / 2 : ℝ) + 1)
      ≤ 2 * Real.sqrt x := by
    have e : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
    rw [e, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  calc ‖∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖
      ≤ C₁ * Real.log x * ((x ^ (-(1 / 2 : ℝ) + 1) - (2 : ℝ) ^ (-(1 / 2 : ℝ) + 1))
          / (-(1 / 2 : ℝ) + 1)) := hle
    _ ≤ C₁ * Real.log x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hval (by positivity)
    _ = 2 * C₁ * Real.log x * Real.sqrt x := by ring

/-- **R2, the core: `VonKochPsi 3 → PiLi2 3`** (no hypothesis on `ζ`). -/
theorem piLi2_of_vonKoch (hV : VonKochPsi 3) : PiLi2 3 := by
  obtain ⟨C₁, hC₁, hθ⟩ := theta_sub_le_of_vonKoch hV
  set l : ℝ := Real.log 2 with hl
  have hl0 : 0 < l := log_two_pos'
  have hl1 : l < 1 := by
    have := Real.log_two_lt_d9; rw [hl]; linarith
  refine ⟨(3 * C₁ + 2) / l ^ 4, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L : ℝ := Real.log x with hL
  have hLl : l ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := lt_of_lt_of_le hl0 hLl
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  rw [primeCounting_sub_Li2 hx]
  have hI := integral_err_le hC₁ hθ hx
  have hT := hθ x hx
  -- the three terms
  have t1 : |(Chebyshev.theta x - x) / L| ≤ C₁ * Real.sqrt x * L ^ 2 := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    calc |Chebyshev.theta x - x| ≤ C₁ * Real.sqrt x * L ^ 3 := hT
      _ = C₁ * Real.sqrt x * L ^ 2 * L := by ring
  have hS : 0 ≤ Real.sqrt x * L ^ 3 := by positivity
  -- powers of l
  have hl2 : l ^ 4 ≤ l ^ 2 := pow_le_pow_of_le_one hl0.le hl1.le (by norm_num)
  have hl3 : l ^ 4 ≤ l ^ 3 := pow_le_pow_of_le_one hl0.le hl1.le (by norm_num)
  have hl1' : l ^ 4 ≤ l := by
    have := pow_le_pow_of_le_one hl0.le hl1.le (show 1 ≤ 4 by norm_num); simpa using this
  have hl4 : 0 < l ^ 4 := by positivity
  -- each term ≤ (coefficient / l⁴) √x L³
  have u1 : C₁ * Real.sqrt x * L ^ 2 ≤ C₁ / l ^ 4 * (Real.sqrt x * L ^ 3) := by
    have : L ^ 2 * l ^ 4 ≤ L ^ 3 := by
      have : L ^ 2 * l ^ 4 ≤ L ^ 2 * l := mul_le_mul_of_nonneg_left hl1' (by positivity)
      have : L ^ 2 * l ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left hLl (by positivity)
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hl4]
    have h0 : 0 ≤ C₁ * Real.sqrt x := by positivity
    nlinarith
  have u2 : 2 * C₁ * L * Real.sqrt x ≤ 2 * C₁ / l ^ 4 * (Real.sqrt x * L ^ 3) := by
    have : L * l ^ 4 ≤ L ^ 3 := by
      have h1 : L * l ^ 4 ≤ L * l ^ 2 := mul_le_mul_of_nonneg_left hl2 hL0.le
      have h2 : l ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hl0.le hLl 2
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hl4]
    have h0 : 0 ≤ 2 * C₁ * Real.sqrt x := by positivity
    nlinarith
  have u3 : 2 / l ≤ 2 / l ^ 4 * (Real.sqrt x * L ^ 3) := by
    have hL3 : l ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hl0.le hLl 3
    have : l ^ 3 ≤ Real.sqrt x * L ^ 3 := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hl4, div_mul_eq_mul_div, div_le_iff₀ hl0]
    nlinarith
  have hsum : (3 * C₁ + 2) / l ^ 4 * Real.sqrt x * L ^ 3
      = C₁ / l ^ 4 * (Real.sqrt x * L ^ 3) + 2 * C₁ / l ^ 4 * (Real.sqrt x * L ^ 3)
        + 2 / l ^ 4 * (Real.sqrt x * L ^ 3) := by ring
  have h2l : |2 / l| = 2 / l := abs_of_pos (by positivity)
  calc |(Chebyshev.theta x - x) / L + 2 / l
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / L| + |2 / l|
        + |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| := by
        have := abs_add_le ((Chebyshev.theta x - x) / L + 2 / l)
          (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        have := abs_add_le ((Chebyshev.theta x - x) / L) (2 / l)
        linarith
    _ ≤ C₁ * Real.sqrt x * L ^ 2 + 2 / l + 2 * C₁ * L * Real.sqrt x := by
        rw [h2l]; rw [Real.norm_eq_abs] at hI; linarith
    _ ≤ (3 * C₁ + 2) / l ^ 4 * Real.sqrt x * L ^ 3 := by linarith

/-- **R2.** Under RH, `|π(x) − Li₂(x)| ≤ C √x (log x)³` for `x ≥ 2`. -/
theorem piLi2_three_of_RH (hRH : RiemannHypothesis) : PiLi2 3 :=
  piLi2_of_vonKoch (vonKochPsi_three_of_RH hRH)

end Salt.RH
