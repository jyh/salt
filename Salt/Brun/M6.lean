/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# M6 — summability bridge (blueprint milestone)

Analytic facts feeding the final Abel-summation step from the counting bound
`twinPrimeCounting N = O(N/(log N)²)` to convergence of `Σ 1/p` over twin
primes. The main assembly (N6.2) additionally needs the counting bound
(N5.3), still downstream of the M1 fundamental theorem; the self-contained
integrability fact (N6.1) is proved here.
-/

open MeasureTheory Filter Real Set Topology

/-- N6.1: `t ↦ 1/(t·(log t)²)` is integrable near `+∞`. Its antiderivative
`g t = -(log t)⁻¹` is differentiable on `[2, ∞)`, has nonnegative derivative
`g' t = 1/(t·(log t)²)` there, and tends to `0` at infinity; so
`integrableOn_Ioi_deriv_of_nonneg'` makes `g'` integrable on `(2, ∞)`, a
member of `atTop`. -/
theorem integrableAtFilter_inv_id_mul_log_sq :
    IntegrableAtFilter (fun t => 1 / (t * Real.log t ^ 2)) atTop := by
  refine ⟨Ioi 2, Ioi_mem_atTop 2, ?_⟩
  have hderiv : ∀ x ∈ Ici (2 : ℝ),
      HasDerivAt (fun t => -(Real.log t)⁻¹) (1 / (x * Real.log x ^ 2)) x := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    have hx0 : x ≠ 0 := by positivity
    have hxlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t => (Real.log t)⁻¹) (-x⁻¹ / (Real.log x) ^ 2) x := h1.inv hxlog
    have h3 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-x⁻¹ / (Real.log x) ^ 2)) x := h2.neg
    convert h3 using 1
    field_simp
  have hpos : ∀ x ∈ Ioi (2 : ℝ), 0 ≤ 1 / (x * Real.log x ^ 2) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    positivity
  have htendsto : Tendsto (fun t => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa using this.neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htendsto
