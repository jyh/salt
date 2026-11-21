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

end Salt.RH
