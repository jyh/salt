import Mathlib

/-!
# N6.1 — Closed forms for the g-integrals

Here `g(u) = 1/(1 + A·u)` for a real parameter `A > 0`.  The four facts below
are the elementary `intervalIntegral` computations that N6.x consumes.  They are
stated for arbitrary real `A > 0`, `T ≥ 0` (no `k`-dependence baked in).
-/

namespace Salt.Maynard

open intervalIntegral MeasureTheory Set

/-- The affine map `u ↦ 1 + A·u` has derivative `A` at every point. -/
private theorem hasDerivAt_affine (A x : ℝ) : HasDerivAt (fun u => 1 + A * u) A x := by
  simpa using ((hasDerivAt_id x).const_mul A).const_add (1:ℝ)

/-- `∫₀^T 1/(1+Au) du = log(1+AT)/A`. -/
theorem integral_g (A T : ℝ) (hA : 0 < A) (hT : 0 ≤ T) :
    ∫ u in (0:ℝ)..T, 1 / (1 + A * u) = Real.log (1 + A * T) / A := by
  have huIcc : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT
  have hAne : A ≠ 0 := hA.ne'
  have hpos : ∀ x ∈ uIcc (0:ℝ) T, (0:ℝ) < 1 + A * x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hderiv : ∀ x ∈ uIcc (0:ℝ) T,
      HasDerivAt (fun u => Real.log (1 + A * u) / A) (1 / (1 + A * x)) x := by
    intro x hx
    have hxne : (1 + A * x) ≠ 0 := (hpos x hx).ne'
    have h2 := (hasDerivAt_affine A x).log hxne
    have h3 := h2.div_const A
    have hval : A / (1 + A * x) / A = 1 / (1 + A * x) := by field_simp
    rw [← hval]; exact h3
  have hint : IntervalIntegrable (fun u => 1 / (1 + A * u)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    · exact fun x hx => (hpos x hx).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₀^T 1/(1+Au)² du = T/(1+AT)`. -/
theorem integral_g_sq (A T : ℝ) (hA : 0 < A) (hT : 0 ≤ T) :
    ∫ u in (0:ℝ)..T, 1 / (1 + A * u) ^ 2 = T / (1 + A * T) := by
  have huIcc : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT
  have hAne : A ≠ 0 := hA.ne'
  have hpos : ∀ x ∈ uIcc (0:ℝ) T, (0:ℝ) < 1 + A * x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hderiv : ∀ x ∈ uIcc (0:ℝ) T,
      HasDerivAt (fun u => (-1 / A) * (1 + A * u)⁻¹) (1 / (1 + A * x) ^ 2) x := by
    intro x hx
    have hxne : (1 + A * x) ≠ 0 := (hpos x hx).ne'
    have h2 := (hasDerivAt_affine A x).inv hxne
    have h3 := h2.const_mul (-1 / A)
    have hval : (-1 / A) * (-A / (1 + A * x) ^ 2) = 1 / (1 + A * x) ^ 2 := by field_simp
    rw [← hval]; exact h3
  have hint : IntervalIntegrable (fun u => 1 / (1 + A * u) ^ 2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
    · exact fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hTne : (1 + A * T) ≠ 0 := (hpos T (by rw [huIcc]; exact ⟨hT, le_rfl⟩)).ne'
  simp only [mul_zero, add_zero, inv_one, mul_one]
  field_simp
  ring

/-- `∫₀^T u/(1+Au)² du = (log(1+AT) − AT/(1+AT))/A²`. -/
theorem integral_u_g_sq (A T : ℝ) (hA : 0 < A) (hT : 0 ≤ T) :
    ∫ u in (0:ℝ)..T, u / (1 + A * u) ^ 2
      = (Real.log (1 + A * T) - A * T / (1 + A * T)) / A ^ 2 := by
  have huIcc : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT
  have hAne : A ≠ 0 := hA.ne'
  have hpos : ∀ x ∈ uIcc (0:ℝ) T, (0:ℝ) < 1 + A * x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hderiv : ∀ x ∈ uIcc (0:ℝ) T,
      HasDerivAt (fun u => (Real.log (1 + A * u) + (1 + A * u)⁻¹) / A ^ 2)
        (x / (1 + A * x) ^ 2) x := by
    intro x hx
    have hxne : (1 + A * x) ≠ 0 := (hpos x hx).ne'
    have h2 := (hasDerivAt_affine A x).log hxne
    have h3 := (hasDerivAt_affine A x).inv hxne
    have h4 := (h2.add h3).div_const (A ^ 2)
    have hval : (A / (1 + A * x) + -A / (1 + A * x) ^ 2) / A ^ 2 = x / (1 + A * x) ^ 2 := by
      field_simp; ring
    rw [← hval]; exact h4
  have hint : IntervalIntegrable (fun u => u / (1 + A * u) ^ 2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
    · exact fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hTne : (1 + A * T) ≠ 0 := (hpos T (by rw [huIcc]; exact ⟨hT, le_rfl⟩)).ne'
  simp only [mul_zero, add_zero, Real.log_one, inv_one, zero_add]
  field_simp
  ring

/-- `∫₀^T u²/(1+Au)² du ≤ T/A²` (from `(u/(1+Au))² ≤ 1/A²`). -/
theorem integral_u_sq_g_sq_le (A T : ℝ) (hA : 0 < A) (hT : 0 ≤ T) :
    ∫ u in (0:ℝ)..T, u ^ 2 / (1 + A * u) ^ 2 ≤ T / A ^ 2 := by
  have huIcc : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT
  have hAne : A ≠ 0 := hA.ne'
  have hpos : ∀ x ∈ uIcc (0:ℝ) T, (0:ℝ) < 1 + A * x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hf : IntervalIntegrable (fun u => u ^ 2 / (1 + A * u) ^ 2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (continuous_pow 2).continuousOn
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
    · exact fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  have hg : IntervalIntegrable (fun _ => 1 / A ^ 2) volume 0 T :=
    intervalIntegral.intervalIntegrable_const
  calc ∫ u in (0:ℝ)..T, u ^ 2 / (1 + A * u) ^ 2
      ≤ ∫ _ in (0:ℝ)..T, 1 / A ^ 2 := by
        apply integral_mono_on hT hf hg
        intro x hx
        have hx0 : 0 ≤ x := hx.1
        have hd1 : (0:ℝ) < (1 + A * x) ^ 2 := by positivity
        have hd2 : (0:ℝ) < A ^ 2 := by positivity
        rw [div_le_iff₀ hd1, one_div, inv_mul_eq_div, le_div_iff₀ hd2]
        nlinarith [mul_nonneg hA.le hx0]
    _ = T / A ^ 2 := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        ring

end Salt.Maynard
