/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LargeValues
import Salt.MR.MVHilbert
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# MR track, P-lane: Halász's inequality for integers — Lemma 9, step-2 kernel

Source pins: MR arXiv v4 `1501.04585v4` Lemma 9 (`[20, Thm 9.6]`); the frozen shape
(S8 MR-CORE freeze, `[P3]`) is

  `Σ_{t∈𝒯} |A(it)|² ≪ (N + |𝒯|·√T)·log(2T)·Σ‖aₙ‖²`   (`𝒯 ⊆ [−T,T]` well-spaced).

Route (P3 resistance map): (1) `l2_duality` (`MVHilbert.lean`) turns the target into
the dual bilinear form `Σ_{n≤N} |Σ_r bᵣ·n^{itᵣ}|² ≤ Δ·Σ‖bᵣ‖²`; (2) expanding the
square, the **off-diagonal** carries the discrete exponential-sum kernel
`|Σ_{n≤N} n^{iu}|`, whose decay is the un-landed analytic piece; (3) a well-spaced
harmonic sum `Σ_{r≠s} (1+|tᵣ−tₛ|)⁻¹ ≪ |𝒯|·log T`; (4) assembly (the `√T` enters via
the source's range split).

**This file lands step (2)'s kernel** — `exp_sum_decay` — as an honest, reusable
corpus stone, together with its analytic supporting chain:

* `exp_int_eval` / `exp_int_modulus` — the integral core
  `∫₁ᴺ x^{iu} dx = (N^{1+iu}−1)/(1+iu)`, with `‖·‖ ≤ (N+1)/√(1+u²)` (`~ N/(1+|u|)`).
* `expILog_sub_unitIntegral_le` — the per-unit-interval Euler–Maclaurin defect
  `≤ |u|/(k+1)` (a mean-value / `∫‖f′‖` argument, `f′ = f·iu/x`).
* `sum_int_comparison` — the summed defect `‖Σ − ∫‖ ≤ 1 + |u|·Σ(k+1)⁻¹`.
* `exp_sum_decay` — combined: `‖Σ_{n=1}^N n^{iu}‖ ≤ (N+1)/√(1+u²) + 1 + |u|(1+log N)`.

The genuinely classical bound `|Σ_{n≤N} n^{iu}| ≪ N/(1+|u|)` holds **only** in the
range `|u| ≲ √N` (the defect `|u|(1+log N)` dominates the head beyond it); this range
split is exactly where the `√T` of the frozen shape is born — carried to the L9
assembly (steps 3–4), the campaign's named residual for this node.
-/

namespace Salt.MR

open scoped BigOperators
open Complex intervalIntegral MeasureTheory

/-- d/dx [x·exp(iu log x)/(1+iu)] = exp(iu log x), for x>0. -/
theorem hasDerivAt_expILogDiv (u x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ))
        / (1 + Complex.I * (u : ℂ)))
      (Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  have hlog : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx0).ofReal_comp
  have hψ : HasDerivAt (fun y : ℝ => Complex.I * (u : ℂ) * ((Real.log y : ℝ) : ℂ))
      (Complex.I * (u : ℂ) * ((x⁻¹ : ℝ) : ℂ)) x :=
    hlog.const_mul (Complex.I * (u : ℂ))
  have hg : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (u : ℂ) * ((Real.log y : ℝ) : ℂ)))
      (Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))
        * (Complex.I * (u : ℂ) * ((x⁻¹ : ℝ) : ℂ))) x := hψ.cexp
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hne : (1 + Complex.I * (u : ℂ)) ≠ 0 := by
    intro h
    have hre : (1 + Complex.I * (u : ℂ)).re = 0 := by rw [h]; simp
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.one_re] at hre
  have hxg2 := (hid.mul hg).div_const (1 + Complex.I * (u : ℂ))
  have heq : (1 * Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))
      + (x : ℂ) * (Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))
          * (Complex.I * (u : ℂ) * ((x⁻¹ : ℝ) : ℂ)))) / (1 + Complex.I * (u : ℂ))
      = Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)) := by
    rw [div_eq_iff hne]; push_cast; field_simp
  rw [heq] at hxg2
  simpa using hxg2


/-- The integrand exp(iu log x) is continuous on [1,b]. -/
theorem continuousOn_expILog_Icc (u b : ℝ) (hb : 1 ≤ b) :
    ContinuousOn (fun x : ℝ => Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)))
      (Set.uIcc 1 b) := by
  have hsub : Set.uIcc (1:ℝ) b ⊆ {x : ℝ | x ≠ 0} := by
    rw [Set.uIcc_of_le hb]
    intro x hx
    simp only [Set.mem_setOf_eq]
    exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)
  apply ContinuousOn.cexp
  apply ContinuousOn.const_mul
  apply Complex.continuous_ofReal.comp_continuousOn
  exact Real.continuousOn_log.mono hsub

/-- ∫_1^b exp(iu log x) dx = (b·exp(iu log b) − 1)/(1+iu). -/
theorem exp_int_eval (u b : ℝ) (hb : 1 ≤ b) :
    (∫ x in (1:ℝ)..b, Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)))
      = ((b : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log b : ℂ)) - 1)
        / (1 + Complex.I * (u : ℂ)) := by
  have hint : IntervalIntegrable
      (fun x : ℝ => Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))) volume 1 b :=
    (continuousOn_expILog_Icc u b hb).intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) b,
      HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ))
        / (1 + Complex.I * (u : ℂ)))
        (Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact hasDerivAt_expILogDiv u x (lt_of_lt_of_le one_pos hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    Complex.ofReal_one]
  rw [div_sub_div_same]

/-- ‖1 + I u‖ = √(1+u²). -/
theorem norm_one_add_Iu (u : ℝ) : ‖(1 + Complex.I * (u : ℂ))‖ = Real.sqrt (1 + u ^ 2) := by
  have : (1 + Complex.I * (u : ℂ)) = ((1 : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_add_mul_I]
  norm_num

/-- ‖exp(I u log b)‖ = 1 (purely imaginary exponent). -/
theorem norm_exp_Iu_log (u b : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (Real.log b : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (Complex.I * (u : ℂ) * (Real.log b : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [this, Real.exp_zero]

/-- The integral modulus bound: ‖∫_1^b exp(iu log x)dx‖ ≤ (b+1)/√(1+u²). -/
theorem exp_int_modulus (u b : ℝ) (hb : 1 ≤ b) :
    ‖∫ x in (1:ℝ)..b, Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))‖
      ≤ (b + 1) / Real.sqrt (1 + u ^ 2) := by
  rw [exp_int_eval u b hb, norm_div, norm_one_add_Iu]
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hnum : ‖(b : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log b : ℂ)) - 1‖ ≤ b + 1 := by
    calc ‖(b : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log b : ℂ)) - 1‖
        ≤ ‖(b : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (Real.log b : ℂ))‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = b + 1 := by
          rw [norm_mul, norm_exp_Iu_log, mul_one, norm_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hb0]
  have hden : (0:ℝ) ≤ Real.sqrt (1 + u ^ 2) := Real.sqrt_nonneg _
  gcongr

/-- HasDerivAt for f(x)=exp(iu log x): f'(x) = exp(iu log x)·(I u / x). -/
theorem hasDerivAt_expILog (u x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ)))
      (Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))
        * (Complex.I * (u : ℂ) * ((x⁻¹ : ℝ) : ℂ))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    (Real.hasDerivAt_log hx0).ofReal_comp
  exact (hlog.const_mul (Complex.I * (u : ℂ))).cexp

/-- ‖f'(x)‖ = |u|/x for x>0. -/
theorem norm_deriv_expILog (u x : ℝ) (hx : 0 < x) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))
        * (Complex.I * (u : ℂ) * ((x⁻¹ : ℝ) : ℂ))‖ = |u| / x := by
  rw [norm_mul, norm_exp_Iu_log, one_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hx)]
  rw [div_eq_mul_inv]

/-- Per-interval comparison: ‖f(k+1) − ∫_{k+1}^{k+2} f‖ ≤ |u|/(k+1). -/
theorem expILog_sub_unitIntegral_le (u : ℝ) (k : ℕ) :
    ‖Complex.exp (Complex.I * (u : ℂ) * (Real.log ((k : ℝ) + 1) : ℂ))
        - ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2),
            Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))‖
      ≤ |u| / ((k : ℝ) + 1) := by
  set C : ℝ := |u| / ((k : ℝ) + 1) with hC
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hle : ((k : ℝ) + 1) ≤ (k : ℝ) + 2 := by linarith
  set f : ℝ → ℂ := fun y => Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ)) with hf
  have hfold : Complex.exp (Complex.I * (u : ℂ) * (Real.log ((k : ℝ) + 1) : ℂ))
      = f ((k : ℝ) + 1) := rfl
  rw [hfold]
  -- MVT on the segment [k+1, k+2]
  have hseg : ∀ y ∈ Set.Icc ((k:ℝ)+1) ((k:ℝ)+2), ‖f y - f ((k:ℝ)+1)‖ ≤ C * ‖y - ((k:ℝ)+1)‖ := by
    intro y hy
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun y => Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ))
          * (Complex.I * (u : ℂ) * ((y⁻¹ : ℝ) : ℂ)))
      ?_ ?_ (convex_Icc _ _) (Set.mem_Icc.mpr ⟨le_refl _, hle⟩) hy
    · intro z hz
      exact (hasDerivAt_expILog u z (lt_of_lt_of_le hk1 hz.1)).hasDerivWithinAt
    · intro z hz
      rw [norm_deriv_expILog u z (lt_of_lt_of_le hk1 hz.1)]
      exact div_le_div_of_nonneg_left (abs_nonneg u) hk1 hz.1
  -- f(k+1) = ∫ const over unit interval
  have hconst : (∫ _x in ((k:ℝ)+1)..((k:ℝ)+2), f ((k:ℝ)+1)) = f ((k:ℝ)+1) := by
    rw [intervalIntegral.integral_const, show ((k:ℝ)+2) - ((k:ℝ)+1) = 1 by ring, one_smul]
  -- integrability of f on the interval
  have hcontf : ContinuousOn f (Set.uIcc ((k:ℝ)+1) ((k:ℝ)+2)) := by
    rw [Set.uIcc_of_le hle]
    have hsub : Set.Icc ((k:ℝ)+1) ((k:ℝ)+2) ⊆ {x : ℝ | x ≠ 0} := by
      intro x hx; exact ne_of_gt (lt_of_lt_of_le hk1 hx.1)
    apply ContinuousOn.cexp; apply ContinuousOn.const_mul
    exact Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono hsub)
  have hint : IntervalIntegrable f volume ((k:ℝ)+1) ((k:ℝ)+2) := hcontf.intervalIntegrable
  have hsub2 : (∫ x in ((k:ℝ)+1)..((k:ℝ)+2), (f ((k:ℝ)+1) - f x))
      = f ((k:ℝ)+1) - ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), f x := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const hint, hconst]
  rw [← hsub2]
  calc ‖∫ x in ((k:ℝ)+1)..((k:ℝ)+2), (f ((k:ℝ)+1) - f x)‖
      ≤ ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), ‖f ((k:ℝ)+1) - f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ _x in ((k:ℝ)+1)..((k:ℝ)+2), C := by
        apply intervalIntegral.integral_mono_on hle
        · exact (continuousOn_const.sub hcontf).norm.intervalIntegrable
        · exact _root_.intervalIntegrable_const
        · intro x hx
          rw [norm_sub_rev]
          refine (hseg x hx).trans ?_
          rw [Real.norm_eq_abs]
          have hx1 : |x - ((k:ℝ)+1)| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
          nlinarith [abs_nonneg u, hk1, div_nonneg (abs_nonneg u) hk1.le]
    _ = C := by rw [intervalIntegral.integral_const]; simp; ring

/-- The integrand is continuous on any interval bounded below by a positive number. -/
theorem continuousOn_expILog (u a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun x : ℝ => Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)))
      (Set.uIcc a b) := by
  apply ContinuousOn.cexp; apply ContinuousOn.const_mul
  apply Complex.continuous_ofReal.comp_continuousOn
  apply Real.continuousOn_log.mono
  intro x hx
  rcases le_total a b with hab | hab
  · rw [Set.uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  · rw [Set.uIcc_of_ge hab] at hx
    exact ne_of_gt (lt_of_lt_of_le hb hx.1)

/-- The integral over [1,N] telescopes into unit intervals. -/
theorem integral_telescope (u : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∫ x in (1:ℝ)..(N:ℝ), Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)))
      = ∑ k ∈ Finset.range (N - 1),
          ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)) := by
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)))
    (a := fun k => (k : ℝ) + 1) (n := N - 1) (μ := volume)
    (fun k _ =>
      (continuousOn_expILog u _ _ (by positivity) (by positivity)).intervalIntegrable)
  have e0 : ((0:ℕ):ℝ) + 1 = (1:ℝ) := by norm_num
  have eN : ((N - 1 : ℕ):ℝ) + 1 = (N:ℝ) := by rw [Nat.cast_sub hN]; push_cast; ring
  rw [e0, eN] at key
  rw [← key]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast; ring

/-- Sum-integral comparison: ‖Σ_{n=1}^N n^{iu} − ∫_1^N x^{iu} dx‖
    ≤ 1 + |u|·Σ_{k<N-1} 1/(k+1). -/
theorem sum_int_comparison (u : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)))
        - ∫ x in (1:ℝ)..(N:ℝ), Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ))‖
      ≤ 1 + |u| * ∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ) + 1) := by
  set F : ℝ → ℂ := fun x => Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)) with hF
  have hreindex : (∑ n ∈ Finset.Icc 1 N, F (n : ℝ))
      = ∑ k ∈ Finset.range (N - 1), F ((k : ℝ) + 1) + F (N : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega]
    have hs := Finset.sum_range_succ (fun i => F ((1 + i : ℕ) : ℝ)) (N - 1)
    rw [Nat.sub_add_cancel hN] at hs
    rw [hs]
    congr 1
    · apply Finset.sum_congr rfl; intro k _; congr 1; push_cast; ring
    · congr 1; have : (1 + (N - 1) : ℕ) = N := by omega
      rw [this]
  rw [hreindex, integral_telescope u N hN]
  have hcollect : (∑ k ∈ Finset.range (N - 1), F ((k:ℝ)+1) + F (N:ℝ))
      - ∑ k ∈ Finset.range (N - 1), ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), F x
      = F (N:ℝ) + ∑ k ∈ Finset.range (N - 1),
          (F ((k:ℝ)+1) - ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), F x) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hcollect]
  calc ‖F (N:ℝ) + ∑ k ∈ Finset.range (N - 1),
          (F ((k:ℝ)+1) - ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), F x)‖
      ≤ ‖F (N:ℝ)‖ + ‖∑ k ∈ Finset.range (N - 1),
          (F ((k:ℝ)+1) - ∫ x in ((k:ℝ)+1)..((k:ℝ)+2), F x)‖ := norm_add_le _ _
    _ ≤ 1 + ∑ k ∈ Finset.range (N - 1), |u| / ((k:ℝ)+1) := by
        gcongr
        · rw [hF]; exact le_of_eq (norm_exp_Iu_log u (N:ℝ))
        · refine (norm_sum_le _ _).trans ?_
          apply Finset.sum_le_sum; intro k _
          exact expILog_sub_unitIntegral_le u k
    _ = 1 + |u| * ∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ)+1) := by
        rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl
        intro k _; rw [mul_one_div]


/-- The truncated harmonic sum equals the harmonic number. -/
theorem sum_range_one_div_succ_eq_harmonic (m : ℕ) :
    (∑ k ∈ Finset.range m, (1:ℝ) / ((k:ℝ) + 1)) = (harmonic m : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [one_div, add_comm]

/-- **`exp_sum_decay`** — the honest exponential-sum bound.  For `1 ≤ N`,
`‖Σ_{n=1}^N n^{iu}‖ ≤ (N+1)/√(1+u²) + 1 + |u|·(1 + log N)`.
The first term (integral head) decays like `N/(1+|u|)`; the residual
`1 + |u|(1+log N)` is the sum-integral (Euler–Maclaurin) defect. -/
theorem exp_sum_decay (u : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ ((N : ℝ) + 1) / Real.sqrt (1 + u ^ 2) + (1 + |u| * (1 + Real.log N)) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  set S := ∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)) with hS
  set I := ∫ x in (1:ℝ)..(N:ℝ), Complex.exp (Complex.I * (u : ℂ) * (Real.log x : ℂ)) with hI
  have htri : ‖S‖ ≤ ‖S - I‖ + ‖I‖ := by
    calc ‖S‖ = ‖(S - I) + I‖ := by rw [sub_add_cancel]
      _ ≤ ‖S - I‖ + ‖I‖ := norm_add_le _ _
  refine htri.trans ?_
  have hcomp : ‖S - I‖ ≤ 1 + |u| * ∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ) + 1) :=
    sum_int_comparison u N hN
  have hmod : ‖I‖ ≤ ((N:ℝ) + 1) / Real.sqrt (1 + u ^ 2) := exp_int_modulus u (N:ℝ) hN1
  -- harmonic: Σ_{range(N-1)} 1/(k+1) ≤ 1 + log N
  have hmono : (∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ) + 1))
      ≤ ∑ k ∈ Finset.range N, (1:ℝ) / ((k:ℝ) + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [Finset.mem_range] at *; omega
    · intro i _ _; positivity
  have hharm : (∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ) + 1)) ≤ 1 + Real.log N :=
    le_trans (hmono.trans_eq (sum_range_one_div_succ_eq_harmonic N)) (harmonic_le_one_add_log N)
  have hu : |u| * ∑ k ∈ Finset.range (N - 1), (1:ℝ) / ((k:ℝ) + 1)
      ≤ |u| * (1 + Real.log N) := mul_le_mul_of_nonneg_left hharm (abs_nonneg u)
  linarith [hcomp, hmod, hu]

/-! ## Step (2)/(1) — the dual bilinear form (via `l2_duality`)

`l2_duality` (`MVHilbert.lean`) turns the frozen L9 target into the dual bound
`Σ_{n≤N} ‖Σ_r bᵣ·n^{-ir}‖² ≤ Δ·Σ‖bᵣ‖²`.  Expanding the square gives the diagonal
`N·Σ‖bᵣ‖²` (`dualPoly_diagonal`) plus an off-diagonal whose kernel is the discrete
exponential sum `Σ_{n≤N} n^{i(r−s)}`, bounded pairwise by `exp_sum_decay`
(`dualPoly_offdiag_norm_le`). -/

/-- The dual Dirichlet polynomial: `n ↦ Σ_{r∈𝒯} bᵣ · n^{-ir}`. -/
noncomputable def dualPoly (𝒯 : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ 𝒯, b r * Complex.exp (-(Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)))

/-- Per-`n` expansion of `‖dualPoly‖²` into the `𝒯×𝒯` double sum with the kernel
`exp(i(r−s) log n)`. -/
theorem dualPoly_sq_expand (𝒯 : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) :
    ((‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ)
      = ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, (starRingEnd ℂ) (b r) * b s
          * Complex.exp (Complex.I * (((r : ℝ) - (s : ℝ)) : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
  have hcm : ((‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (dualPoly 𝒯 b n) * dualPoly 𝒯 b n := by
    rw [Complex.sq_norm]; exact Complex.normSq_eq_conj_mul_self
  rw [hcm]
  have hconj : (starRingEnd ℂ) (dualPoly 𝒯 b n)
      = ∑ r ∈ 𝒯, (starRingEnd ℂ) (b r)
          * Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    unfold dualPoly
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_mul]
  rw [hconj]
  unfold dualPoly
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  have hexp :
      Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (((r : ℝ) - (s : ℝ)) : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc (starRingEnd ℂ) (b r) * Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ))
        * (b s * Complex.exp (-(Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ))))
      = (starRingEnd ℂ) (b r) * b s
          * (Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ))
              * Complex.exp (-(Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))) := by ring
    _ = (starRingEnd ℂ) (b r) * b s
          * Complex.exp (Complex.I * (((r : ℝ) - (s : ℝ)) : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        rw [hexp]

/-- Summed expansion: `Σ_{n≤N} ‖dualPoly‖²` = the `𝒯×𝒯` double sum against the
exponential-sum kernel `Σ_{n≤N} exp(i(r−s) log n)`. -/
theorem dualPoly_sum_expand (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ))
      = ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, (starRingEnd ℂ) (b r) * b s
          * ∑ n ∈ Finset.Icc 1 N,
              Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ)) := by
  simp_rw [dualPoly_sq_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum]

/-- **The dual-form diagonal split.**  `Σ_{n≤N} ‖dualPoly‖²` equals the diagonal
`N·Σ_r ‖bᵣ‖²` plus the off-diagonal double sum (the piece bounded by
`exp_sum_decay`). -/
theorem dualPoly_diagonal (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ))
      = (N : ℂ) * ∑ r ∈ 𝒯, ((‖b r‖ ^ 2 : ℝ) : ℂ)
        + ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
            * ∑ n ∈ Finset.Icc 1 N,
                Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ)) := by
  rw [dualPoly_sum_expand, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hdiagK : (∑ n ∈ Finset.Icc 1 N,
      Complex.exp (Complex.I * (((r:ℝ) - (r:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ))) = (N : ℂ) := by
    simp only [sub_self, mul_zero, zero_mul, Complex.exp_zero,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hconjsq : (starRingEnd ℂ) (b r) * b r = ((‖b r‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [← Finset.add_sum_erase _ _ hr]
  congr 1
  rw [hdiagK, hconjsq, mul_comm]

/-- **The off-diagonal norm bound** — where `exp_sum_decay` enters the dual form.
Each pair `r≠s` contributes the exponential-sum kernel `Σ_{n≤N} n^{i(r−s)}`, bounded
by `exp_sum_decay` at `u = r−s`. -/
theorem dualPoly_offdiag_norm_le (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
        * ∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ))‖
      ≤ ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, ‖b r‖ * ‖b s‖
          * (((N:ℝ) + 1) / Real.sqrt (1 + ((r:ℝ) - (s:ℝ)) ^ 2)
              + (1 + |(r:ℝ) - (s:ℝ)| * (1 + Real.log N))) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  gcongr
  simpa only [Complex.ofReal_sub] using exp_sum_decay ((r:ℝ) - (s:ℝ)) N hN

/-! ## Step (3) — the well-spaced harmonic double sum (`F1`)

The off-diagonal head branch `(N+1)/√(1+(r−s)²)`, summed against a well-spaced set
`𝒯 ⊆ [−T,T]`, contributes only `≪ N·|𝒯|·log(2T)`.  The mechanism (this section's
stones): well-spacing (`|x−y| ≥ 1` for `x ≠ y`) forces the reciprocal-distance row
sum to be harmonic — the integer parts of the one-sided distances inject into
`[1, ⌊2T⌋]`, so `Σ_{s≠r} 1/√(1+(r−s)²) ≤ 2(1 + log 2T)` per row.

**Scope note (the L9 residual, LOUD).** This F1 stone controls only the head branch.
The frozen `√T` grade of `halasz_integers` (MR Lemma 9 = Ten Lectures Thm 8, Ch. 7 §6
p.140 (30)) is born from the *van der Corput* exp-sum bound `Z(iu) ≪ N/|u| + √|u|·log|u|`
(Ten Lectures (33)/(34), via Poisson/Thm 3.8) — **not** from `exp_sum_decay`, whose
Euler–Maclaurin defect is the *linear* `|u|(1+log N)`.  Summed over the far pairs
(`|u|` up to `2T`), that linear defect gives `≪ |𝒯|·T·log N`, off the frozen grade by a
full factor `√T`.  See `halasz_integers_of_vanDerCorput` for the assembly that closes
once the `√|u|` bound is supplied. -/

/-- `Σ_{j=1}^{M} 1/j = Σ_{k<M} 1/(k+1)` (an `Icc`↔`range` reindex). -/
theorem sum_Icc_one_div_eq_range (M : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (j : ℝ) = ∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show M + 1 - 1 = M by omega]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [add_comm (1 : ℝ) (k : ℝ)]

/-- If `g` is injective on `F` with values in `[1, M]`, then `Σ_{m∈F} 1/(g m) ≤ 1 + log M`.
A generic-domain analogue of `sum_inv_image_le`; the image injects into `[1,M]`, where the
harmonic head bound applies. -/
theorem sum_inv_le_one_add_log {α : Type*} (F : Finset α) (M : ℕ) (g : α → ℕ)
    (hginj : ∀ a ∈ F, ∀ b ∈ F, g a = g b → a = b)
    (hg1 : ∀ m ∈ F, 1 ≤ g m) (hgM : ∀ m ∈ F, g m ≤ M) :
    ∑ m ∈ F, (1 : ℝ) / (g m : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · have hFe : F = ∅ := by
      by_contra hne
      obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := hg1 m hm; have h2 := hgM m hm; omega
    subst hM0
    rw [hFe, Finset.sum_empty, Nat.cast_zero, Real.log_zero, add_zero]
    norm_num
  · have himg : (∑ j ∈ F.image g, (1 : ℝ) / (j : ℝ)) = ∑ m ∈ F, (1 : ℝ) / ((g m : ℕ) : ℝ) :=
      Finset.sum_image hginj
    rw [← himg]
    have hsub : F.image g ⊆ Finset.Icc 1 M := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨m, hm, rfl⟩ := hj
      rw [Finset.mem_Icc]
      exact ⟨hg1 m hm, hgM m hm⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => by positivity)) ?_
    rw [sum_Icc_one_div_eq_range]
    exact (sum_range_one_div_succ_eq_harmonic M).le.trans (harmonic_le_one_add_log M)

/-- Well-spacing makes `s ↦ ⌊y s⌋₊` injective on `G ⊆ 𝒯` whenever `y ≥ 0` and `y`'s
differences match `𝒯`'s (the two one-sided distance maps `s−r`, `r−s`). -/
theorem floor_inj_wellspaced (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (G : Finset ℝ) (hG : G ⊆ 𝒯) (y : ℝ → ℝ)
    (hy0 : ∀ s ∈ G, 0 ≤ y s)
    (hydiff : ∀ s₁ ∈ G, ∀ s₂ ∈ G, |y s₁ - y s₂| = |s₁ - s₂|) :
    ∀ s₁ ∈ G, ∀ s₂ ∈ G, ⌊y s₁⌋₊ = ⌊y s₂⌋₊ → s₁ = s₂ := by
  intro s₁ h₁ s₂ h₂ hfl
  by_contra hne
  have hsp : 1 ≤ |s₁ - s₂| := hws s₁ (hG h₁) s₂ (hG h₂) hne
  have hlt : |y s₁ - y s₂| < 1 := by
    have e1 : (⌊y s₁⌋₊ : ℝ) ≤ y s₁ := Nat.floor_le (hy0 s₁ h₁)
    have e2 : y s₁ < (⌊y s₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have e3 : (⌊y s₂⌋₊ : ℝ) ≤ y s₂ := Nat.floor_le (hy0 s₂ h₂)
    have e4 : y s₂ < (⌊y s₂⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hfl] at e1 e2
    rw [abs_lt]
    constructor <;> linarith
  rw [hydiff s₁ h₁ s₂ h₂] at hlt
  linarith

/-- One-sided head-branch row bound: `g s = ⌊|r−s|₊⌋` injective on `G` into `[1,⌊2T⌋]`
with `(g s : ℝ) ≤ √(1+(r−s)²)` gives `Σ_{s∈G} 1/√(1+(r−s)²) ≤ 1 + log(2T)`. -/
theorem recip_side_le (T : ℝ) (hT : 1 ≤ T) (r : ℝ) (G : Finset ℝ) (g : ℝ → ℕ)
    (hginj : ∀ a ∈ G, ∀ b ∈ G, g a = g b → a = b)
    (hg1 : ∀ s ∈ G, 1 ≤ g s)
    (hgM : ∀ s ∈ G, g s ≤ ⌊2 * T⌋₊)
    (hgle : ∀ s ∈ G, (g s : ℝ) ≤ Real.sqrt (1 + (r - s) ^ 2)) :
    ∑ s ∈ G, 1 / Real.sqrt (1 + (r - s) ^ 2) ≤ 1 + Real.log (2 * T) := by
  have hM1 : 1 ≤ ⌊2 * T⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hMpos : (0 : ℝ) < (⌊2 * T⌋₊ : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM1
  calc ∑ s ∈ G, 1 / Real.sqrt (1 + (r - s) ^ 2)
      ≤ ∑ s ∈ G, (1 : ℝ) / (g s : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        apply one_div_le_one_div_of_le
        · have := hg1 s hs
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        · exact hgle s hs
    _ ≤ 1 + Real.log (⌊2 * T⌋₊ : ℝ) := sum_inv_le_one_add_log G ⌊2 * T⌋₊ g hginj hg1 hgM
    _ ≤ 1 + Real.log (2 * T) := by
        have hle : (⌊2 * T⌋₊ : ℝ) ≤ 2 * T := Nat.floor_le (by linarith)
        have := Real.log_le_log hMpos hle
        linarith

/-- **`F1` (row form).** For a well-spaced `𝒯 ⊆ [−T,T]` and `r ∈ 𝒯`, the reciprocal
head-branch row sum is harmonic: `Σ_{s∈𝒯\{r}} 1/√(1+(r−s)²) ≤ 2(1 + log 2T)`. -/
theorem wellspaced_recip_row (𝒯 : Finset ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) (r : ℝ) (hr : r ∈ 𝒯) :
    ∑ s ∈ 𝒯.erase r, 1 / Real.sqrt (1 + (r - s) ^ 2) ≤ 2 * (1 + Real.log (2 * T)) := by
  classical
  set Gp := (𝒯.erase r).filter (fun s => r < s) with hGp
  set Gm := (𝒯.erase r).filter (fun s => ¬ r < s) with hGm
  have hsplit : ∑ s ∈ 𝒯.erase r, 1 / Real.sqrt (1 + (r - s) ^ 2)
      = (∑ s ∈ Gp, 1 / Real.sqrt (1 + (r - s) ^ 2))
        + ∑ s ∈ Gm, 1 / Real.sqrt (1 + (r - s) ^ 2) :=
    (Finset.sum_filter_add_sum_filter_not (𝒯.erase r) (fun s => r < s) _).symm
  rw [hsplit]
  have hGp_sub : Gp ⊆ 𝒯 :=
    fun s hs => Finset.mem_of_mem_erase (Finset.mem_filter.mp hs).1
  have hGm_sub : Gm ⊆ 𝒯 :=
    fun s hs => Finset.mem_of_mem_erase (Finset.mem_filter.mp hs).1
  have hbp : ∑ s ∈ Gp, 1 / Real.sqrt (1 + (r - s) ^ 2) ≤ 1 + Real.log (2 * T) := by
    apply recip_side_le T hT r Gp (fun s => ⌊s - r⌋₊)
    · refine floor_inj_wellspaced 𝒯 hws Gp hGp_sub (fun s => s - r) ?_ ?_
      · intro s hs; have : r < s := (Finset.mem_filter.mp hs).2; linarith
      · intro s₁ _ s₂ _; rw [show (s₁ - r) - (s₂ - r) = s₁ - s₂ by ring]
    · intro s hs
      have hlt : r < s := (Finset.mem_filter.mp hs).2
      have hne : s ≠ r := ne_of_gt hlt
      have hd : 1 ≤ |s - r| := hws s (hGp_sub hs) r hr hne
      rw [abs_of_pos (by linarith : (0 : ℝ) < s - r)] at hd
      exact Nat.le_floor (by push_cast; linarith)
    · intro s hs
      have hs𝒯 := Set.mem_Icc.mp (hsub s (hGp_sub hs))
      have hr𝒯 := Set.mem_Icc.mp (hsub r hr)
      exact Nat.floor_le_floor (by linarith [hs𝒯.2, hr𝒯.1])
    · intro s hs
      have hlt : r < s := (Finset.mem_filter.mp hs).2
      calc ((⌊s - r⌋₊ : ℕ) : ℝ) ≤ s - r := Nat.floor_le (by linarith)
        _ = |r - s| := by rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < s - r)]
        _ = Real.sqrt ((r - s) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (1 + (r - s) ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg (r - s)])
  have hbm : ∑ s ∈ Gm, 1 / Real.sqrt (1 + (r - s) ^ 2) ≤ 1 + Real.log (2 * T) := by
    apply recip_side_le T hT r Gm (fun s => ⌊r - s⌋₊)
    · refine floor_inj_wellspaced 𝒯 hws Gm hGm_sub (fun s => r - s) ?_ ?_
      · intro s hs; have : ¬ r < s := (Finset.mem_filter.mp hs).2
        have : s ≤ r := not_lt.mp this; linarith
      · intro s₁ _ s₂ _; rw [show (r - s₁) - (r - s₂) = -(s₁ - s₂) by ring, abs_neg]
    · intro s hs
      have hle : s ≤ r := not_lt.mp (Finset.mem_filter.mp hs).2
      have hne : s ≠ r := (Finset.mem_erase.mp (Finset.mem_filter.mp hs).1).1
      have hlt : s < r := lt_of_le_of_ne hle hne
      have hd : 1 ≤ |s - r| := hws s (hGm_sub hs) r hr hne
      rw [abs_of_neg (by linarith : s - r < 0)] at hd
      exact Nat.le_floor (by push_cast; linarith)
    · intro s hs
      have hs𝒯 := Set.mem_Icc.mp (hsub s (hGm_sub hs))
      have hr𝒯 := Set.mem_Icc.mp (hsub r hr)
      exact Nat.floor_le_floor (by linarith [hs𝒯.1, hr𝒯.2])
    · intro s hs
      have hle : s ≤ r := not_lt.mp (Finset.mem_filter.mp hs).2
      calc ((⌊r - s⌋₊ : ℕ) : ℝ) ≤ r - s := Nat.floor_le (by linarith)
        _ = |r - s| := (abs_of_nonneg (by linarith)).symm
        _ = Real.sqrt ((r - s) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (1 + (r - s) ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg (r - s)])
  linarith [hbp, hbm]

/-- **`F1` (double-sum form).** The well-spaced harmonic double sum of the head branch:
`Σ_{r∈𝒯} Σ_{s≠r} 1/√(1+(r−s)²) ≤ |𝒯|·2(1 + log 2T)`. -/
theorem wellspaced_harmonic_double (𝒯 : Finset ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, 1 / Real.sqrt (1 + (r - s) ^ 2)
      ≤ (𝒯.card : ℝ) * (2 * (1 + Real.log (2 * T))) := by
  calc ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, 1 / Real.sqrt (1 + (r - s) ^ 2)
      ≤ ∑ _r ∈ 𝒯, 2 * (1 + Real.log (2 * T)) :=
        Finset.sum_le_sum (fun r hr => wellspaced_recip_row 𝒯 T hT hws hsub r hr)
    _ = (𝒯.card : ℝ) * (2 * (1 + Real.log (2 * T))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Steps (2)–(4) — the conditional assembly (the `√T` socket)

`exp_sum_decay` cannot reach the frozen `√T` (its defect is linear in `|u|`; see the
scope note above).  We instead abstract the exponential-sum control into a **van der
Corput socket** `hZ : ‖Σ_{n≤N} n^{iu}‖ ≤ Cvdc·(N/√(1+u²) + √(1+|u|)·(1+log(2+|u|)))`
— the **honest** shape of Montgomery, *Ten Lectures* p. 141 (33), `Z(it) ≪ N/t +
√t·log t` (the `log` on the middle term is irreducible at this process level: (34)
gives `√U` per dyadic block on `√t ≤ U ≤ t`, and (33) sums `≈ ½log₂ t` such blocks;
VDC's SCOUT corrected the earlier log-free misattribution).  We land the *entire*
duality + diagonal + split-row assembly on top of it.  The residual for the
unconditional L9 is then precisely this one honest analytic input over the middle
frequency band `1 ≤ |u| ≤ N²` (the `|u| ≤ 1` and `|u| ≥ N²` corners are discharged
unconditionally in `Salt/MR/VanDerCorput.lean`). -/

/-- The van der Corput kernel envelope, **honest-log form**
`K'(r,s) = N/√(1+(r−s)²) + √(1+|r−s|)·(1+log(2+|r−s|))`.  The tail carries the
`log` of *Ten Lectures* (33) (`Z(it) ≪ N/t + √t·log t`); the socket–source gap
scouted by VDC is thereby closed at the statement level (the socket is no longer
strictly stronger than the source). -/
noncomputable def vdcKernel (N : ℕ) (r s : ℝ) : ℝ :=
  (N : ℝ) / Real.sqrt (1 + (r - s) ^ 2)
    + Real.sqrt (1 + |r - s|) * (1 + Real.log (2 + |r - s|))

lemma vdcKernel_nonneg (N : ℕ) (r s : ℝ) : 0 ≤ vdcKernel N r s := by
  unfold vdcKernel
  have hlog : 0 ≤ 1 + Real.log (2 + |r - s|) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |r - s| by have := abs_nonneg (r - s); linarith)
    linarith
  have h1 : 0 ≤ (N : ℝ) / Real.sqrt (1 + (r - s) ^ 2) := by positivity
  have h2 : 0 ≤ Real.sqrt (1 + |r - s|) * (1 + Real.log (2 + |r - s|)) :=
    mul_nonneg (Real.sqrt_nonneg _) hlog
  linarith

lemma vdcKernel_symm (N : ℕ) (r s : ℝ) : vdcKernel N r s = vdcKernel N s r := by
  unfold vdcKernel
  rw [show (s - r) ^ 2 = (r - s) ^ 2 by ring, abs_sub_comm]

/-- **`F2` — the off-diagonal bound under the van der Corput socket.** Mirrors
`dualPoly_offdiag_norm_le` with `hZ` replacing `exp_sum_decay`. -/
theorem dualPoly_offdiag_vdc_le (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) (Cvdc : ℝ)
    (hZ : ∀ u : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
          ≤ Cvdc * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
              + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)))) :
    ‖∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
        * ∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ))‖
      ≤ ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, ‖b r‖ * ‖b s‖ * (Cvdc * vdcKernel N r s) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  unfold vdcKernel
  gcongr
  simpa only [Complex.ofReal_sub] using hZ ((r:ℝ) - (s:ℝ))

/-- **Row bound (consumes `F1`), honest-log form.** The full `𝒯`-row of `vdcKernel`
(head via `F1`, tail by the per-term max `|r−s| ≤ 2T`) is
`≤ N(3 + 2 log 2T) + |𝒯|·√(1+2T)·(1+log(2+2T))`.  The two logarithms sit in
**separate** terms — the head's `log 2T` and the tail's `log(2+2T)` add, never
multiply (the maestro's "single-log grade"): the `√T`-term's log is confined to it. -/
theorem vdcKernel_row_le (𝒯 : Finset ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) (N : ℕ) (r : ℝ) (hr : r ∈ 𝒯) :
    ∑ s ∈ 𝒯, vdcKernel N r s
      ≤ (N : ℝ) * (1 + 2 * (1 + Real.log (2 * T)))
        + (𝒯.card : ℝ) * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) := by
  have hhead : ∑ s ∈ 𝒯, (N : ℝ) / Real.sqrt (1 + (r - s) ^ 2)
      ≤ (N : ℝ) * (1 + 2 * (1 + Real.log (2 * T))) := by
    have h1 : ∑ s ∈ 𝒯, (N : ℝ) / Real.sqrt (1 + (r - s) ^ 2)
        = (N : ℝ) * ∑ s ∈ 𝒯, 1 / Real.sqrt (1 + (r - s) ^ 2) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun s _ => (mul_one_div _ _).symm)
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    rw [← Finset.add_sum_erase _ _ hr]
    have hrr : (1 : ℝ) / Real.sqrt (1 + (r - r) ^ 2) = 1 := by rw [sub_self]; norm_num
    rw [hrr]
    linarith [wellspaced_recip_row 𝒯 T hT hws hsub r hr]
  have htail : ∑ s ∈ 𝒯, Real.sqrt (1 + |r - s|) * (1 + Real.log (2 + |r - s|))
      ≤ (𝒯.card : ℝ) * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) := by
    calc ∑ s ∈ 𝒯, Real.sqrt (1 + |r - s|) * (1 + Real.log (2 + |r - s|))
        ≤ ∑ _s ∈ 𝒯, Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)) := by
          apply Finset.sum_le_sum
          intro s hs
          have hr𝒯 := Set.mem_Icc.mp (hsub r hr)
          have hs𝒯 := Set.mem_Icc.mp (hsub s hs)
          have hd : |r - s| ≤ 2 * T := by
            rw [abs_le]; constructor <;> linarith [hr𝒯.1, hr𝒯.2, hs𝒯.1, hs𝒯.2]
          have hsqrt_le : Real.sqrt (1 + |r - s|) ≤ Real.sqrt (1 + 2 * T) :=
            Real.sqrt_le_sqrt (by linarith)
          have hlog_le : Real.log (2 + |r - s|) ≤ Real.log (2 + 2 * T) :=
            Real.log_le_log (by positivity) (by linarith)
          have h2 : 0 ≤ 1 + Real.log (2 + |r - s|) := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |r - s| by
              have := abs_nonneg (r - s); linarith)
            linarith
          exact mul_le_mul hsqrt_le (by linarith) h2 (Real.sqrt_nonneg _)
      _ = (𝒯.card : ℝ) * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  unfold vdcKernel
  rw [Finset.sum_add_distrib]
  exact add_le_add hhead htail

/-- **`F3` — the AM–GM full-square collapse.** With a uniform `𝒯`-row bound `B` on the
symmetric `vdcKernel`, the full bilinear square is diagonal-dominated:
`Σ_r Σ_s ‖bᵣ‖‖bₛ‖·K(r,s) ≤ B·Σ_r ‖bᵣ‖²`. -/
theorem vdc_fullsquare_le (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) (B : ℝ)
    (hrow : ∀ r ∈ 𝒯, ∑ s ∈ 𝒯, vdcKernel N r s ≤ B) :
    ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ * ‖b s‖ * vdcKernel N r s
      ≤ B * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
  have hP : ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ ^ 2 * vdcKernel N r s
      ≤ B * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro r hr
    rw [← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hrow r hr) (by positivity)
  have hQ : ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b s‖ ^ 2 * vdcKernel N r s
      ≤ B * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum; intro s hs
    rw [← Finset.mul_sum, mul_comm B (‖b s‖ ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsymm : ∑ r ∈ 𝒯, vdcKernel N r s = ∑ r ∈ 𝒯, vdcKernel N s r :=
      Finset.sum_congr rfl (fun r _ => vdcKernel_symm N r s)
    rw [hsymm]; exact hrow s hs
  have h2 : 2 * (∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ * ‖b s‖ * vdcKernel N r s)
      ≤ (∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ ^ 2 * vdcKernel N r s)
        + ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b s‖ ^ 2 * vdcKernel N r s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro r _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro s _
    have hk := vdcKernel_nonneg N r s
    nlinarith [sq_nonneg (‖b r‖ - ‖b s‖), norm_nonneg (b r), norm_nonneg (b s), hk]
  linarith [hP, hQ, h2]

/-- **The dual `L²` bound under the van der Corput socket.** Combining
`dualPoly_diagonal` (the `N`-diagonal) with the socketed off-diagonal (`F2`) and the
AM–GM collapse (`F3`): `Σ_{n≤N} ‖dualPoly‖² ≤ (N + Cvdc·B)·Σ_r ‖bᵣ‖²`. -/
theorem dualsq_le_of_vdc (𝒯 : Finset ℝ) (b : ℝ → ℂ) (N : ℕ) (Cvdc : ℝ) (hCvdc : 0 ≤ Cvdc)
    (hZ : ∀ u : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
          ≤ Cvdc * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
              + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))))
    (B : ℝ) (hrow : ∀ r ∈ 𝒯, ∑ s ∈ 𝒯, vdcKernel N r s ≤ B) :
    ∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2
      ≤ ((N : ℝ) + Cvdc * B) * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
  have hLnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hSnn : 0 ≤ ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := Finset.sum_nonneg (fun r _ => by positivity)
  have hoff : ‖∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
        * ∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ))‖
      ≤ Cvdc * B * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
    refine (dualPoly_offdiag_vdc_le 𝒯 b N Cvdc hZ).trans ?_
    have hstep1 : ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, ‖b r‖ * ‖b s‖ * (Cvdc * vdcKernel N r s)
        ≤ ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ * ‖b s‖ * (Cvdc * vdcKernel N r s) := by
      apply Finset.sum_le_sum; intro r _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset r 𝒯)
      intro s _ _
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg hCvdc (vdcKernel_nonneg N r s))
    refine hstep1.trans ?_
    have hfac : ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ * ‖b s‖ * (Cvdc * vdcKernel N r s)
        = Cvdc * ∑ r ∈ 𝒯, ∑ s ∈ 𝒯, ‖b r‖ * ‖b s‖ * vdcKernel N r s := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    rw [hfac, mul_assoc]
    exact mul_le_mul_of_nonneg_left (vdc_fullsquare_le 𝒯 b N B hrow) hCvdc
  have key : ∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2
      ≤ (N : ℝ) * (∑ r ∈ 𝒯, ‖b r‖ ^ 2)
        + ‖∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
            * ∑ n ∈ Finset.Icc 1 N,
                Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ))‖ := by
    have hcast : ((∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ)
        = (N : ℂ) * ((∑ r ∈ 𝒯, ‖b r‖ ^ 2 : ℝ) : ℂ)
          + ∑ r ∈ 𝒯, ∑ s ∈ 𝒯.erase r, (starRingEnd ℂ) (b r) * b s
              * ∑ n ∈ Finset.Icc 1 N,
                  Complex.exp (Complex.I * (((r:ℝ) - (s:ℝ)) : ℂ) * (Real.log (n:ℝ) : ℂ)) := by
      rw [Complex.ofReal_sum, dualPoly_diagonal 𝒯 b N, Complex.ofReal_sum]
    have e1 : ∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2
        = ‖((∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLnn]
    have e2 : ‖(N : ℂ) * ((∑ r ∈ 𝒯, ‖b r‖ ^ 2 : ℝ) : ℂ)‖
        = (N : ℝ) * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hSnn]
    rw [e1, hcast]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [e2]
  rw [add_mul]
  linarith [key, hoff]

/-- **`halasz_integers_log_split` (T1) — the split-log primal grade.**  The honest
intermediate before the frozen collapse: the two logarithms stay in **separate** terms
(`log 2T` on the `N`-head, `log(2+2T)` on the `|𝒯|·√(1+2T)`-tail — they *add*, never
multiply; the maestro's "single-log grade"):
`Σ_{t∈𝒯} ‖A(it)‖²
   ≤ (3(Cvdc+1)·N·(1+log 2T) + (Cvdc+1)·|𝒯|·√(1+2T)·(1+log(2+2T)))·Σ‖aₙ‖²`,
for well-spaced `𝒯 ⊆ [−T,T]`, `T ≥ 1`.  Route: `dualsq_le_of_vdc` at the split `F1`-row
(`vdcKernel_row_le`), through `l2_duality` (`dpoly` primal ← `dualPoly` l²-adjoint).  The
frozen `(N+|𝒯|√T)·log` shape (`halasz_integers_of_vanDerCorput`) is its collapse.  The
sole analytic input is the honest-log socket `hZ` (see the section note). -/
theorem halasz_integers_log_split (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (Cvdc : ℝ) (hCvdc : 0 ≤ Cvdc)
    (hZ : ∀ u : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
          ≤ Cvdc * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
              + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)))) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ (3 * (Cvdc + 1) * (N : ℝ) * (1 + Real.log (2 * T))
          + (Cvdc + 1) * (𝒯.card : ℝ)
              * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  classical
  set L := Real.log (2 * T) with hLdef
  have hLnn : 0 ≤ L := Real.log_nonneg (by linarith)
  set S := (𝒯.card : ℝ) with hSdef
  have hSnn : 0 ≤ S := Nat.cast_nonneg _
  set B := (N : ℝ) * (1 + 2 * (1 + L))
      + S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) with hBdef
  have hrow : ∀ r ∈ 𝒯, ∑ s ∈ 𝒯, vdcKernel N r s ≤ B := by
    intro r hr; rw [hBdef, hLdef, hSdef]; exact vdcKernel_row_le 𝒯 T hT hws hsub N r hr
  set Δ := 3 * (Cvdc + 1) * (N : ℝ) * (1 + L)
      + (Cvdc + 1) * S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) with hΔdef
  have hMnn : 0 ≤ 1 + Real.log (2 + 2 * T) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * T by linarith); linarith
  have hSMnn : 0 ≤ S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) :=
    mul_nonneg hSnn (mul_nonneg (Real.sqrt_nonneg _) hMnn)
  have hΔnn : 0 ≤ Δ := by
    rw [hΔdef]
    have h1 : 0 ≤ 3 * (Cvdc + 1) * (N : ℝ) * (1 + L) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Nat.cast_nonneg N))
        (by linarith)
    have h2 : 0 ≤ (Cvdc + 1) * S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))) :=
      mul_nonneg (mul_nonneg (by linarith) hSnn) (mul_nonneg (Real.sqrt_nonneg _) hMnn)
    linarith
  have hconst : (N : ℝ) + Cvdc * B ≤ Δ := by
    have part_a : (N : ℝ) * (1 + Cvdc * (1 + 2 * (1 + L)))
        ≤ 3 * (Cvdc + 1) * (N : ℝ) * (1 + L) := by
      have inner : 1 + Cvdc * (1 + 2 * (1 + L)) ≤ 3 * (Cvdc + 1) * (1 + L) := by
        nlinarith [mul_nonneg hCvdc hLnn, hCvdc, hLnn]
      nlinarith [mul_le_mul_of_nonneg_left inner (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
    have part_b : Cvdc * (S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))))
        ≤ (Cvdc + 1) * (S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)))) :=
      mul_le_mul_of_nonneg_right (by linarith) hSMnn
    have hLHS : (N : ℝ) + Cvdc * B
        = (N : ℝ) * (1 + Cvdc * (1 + 2 * (1 + L)))
          + Cvdc * (S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)))) := by
      rw [hBdef]; ring
    have hRHS : Δ = 3 * (Cvdc + 1) * (N : ℝ) * (1 + L)
        + (Cvdc + 1) * (S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)))) := by
      rw [hΔdef]; ring
    rw [hLHS, hRHS]; exact add_le_add part_a part_b
  -- the dual bound (via dualsq_le_of_vdc), phrased for `l2_duality`
  have hdual : ∀ b : ℝ → ℂ,
      ∑ n ∈ Finset.Icc 1 N,
          ‖∑ r ∈ 𝒯, (starRingEnd ℂ) (Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)))
              * b r‖ ^ 2
        ≤ Δ * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 := by
    intro b
    have hconv : ∀ n : ℕ,
        (∑ r ∈ 𝒯, (starRingEnd ℂ) (Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)))
            * b r) = dualPoly 𝒯 b n := by
      intro n
      unfold dualPoly
      apply Finset.sum_congr rfl; intro r _
      have hct : (starRingEnd ℂ) (Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)))
          = Complex.exp (-(Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
        rw [← Complex.exp_conj]
        congr 1
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
      rw [hct, mul_comm]
    calc ∑ n ∈ Finset.Icc 1 N,
            ‖∑ r ∈ 𝒯, (starRingEnd ℂ) (Complex.exp (Complex.I * (r : ℂ)
                * (Real.log (n : ℝ) : ℂ))) * b r‖ ^ 2
        = ∑ n ∈ Finset.Icc 1 N, ‖dualPoly 𝒯 b n‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro n _; rw [hconv n]
      _ ≤ ((N : ℝ) + Cvdc * B) * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 :=
          dualsq_le_of_vdc 𝒯 b N Cvdc hCvdc hZ B hrow
      _ ≤ Δ * ∑ r ∈ 𝒯, ‖b r‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hconst (Finset.sum_nonneg fun r _ => by positivity)
  have hprimal := (l2_duality 𝒯 (Finset.Icc 1 N)
    (fun r n => Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ))) hΔnn).mpr hdual a
  have hdp : ∀ r : ℝ,
      (∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)) * a n)
        = dpoly N a r := by
    intro r; unfold dpoly; apply Finset.sum_congr rfl; intro n _; rw [mul_comm]
  calc ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      = ∑ r ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N,
          Complex.exp (Complex.I * (r : ℂ) * (Real.log (n : ℝ) : ℂ)) * a n‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro r _; rw [hdp r]
    _ ≤ Δ * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := hprimal

/-- **`F4` — the conditional `halasz_integers` (frozen √T shape).**  The
`halasz_integers_log_split` grade collapsed to the frozen shape at the honest absolute
constant **4** (was `3` on VDC's earlier log-free socket; the extra `(1+log(2+2T))` tail
costs a bare `O(1)` factor — noted loudly, per the maestro's convention):
`Σ_{t∈𝒯} ‖A(it)‖² ≤ 4(Cvdc+1)·(N + |𝒯|√T)·(1 + log 2T)·Σ‖aₙ‖²`, for well-spaced
`𝒯 ⊆ [−T,T]`, `T ≥ 1`, via `√(1+2T) ≤ 2√T` and `1+log(2+2T) ≤ 2(1+log 2T)` (both honest).
The **only** input beyond the landed corpus is `hZ` — the *Ten Lectures* (33) van der
Corput bound `Z(iu) ≪ N/|u| + √|u|·log|u|` — discharged unconditionally on `|u| ≤ 1` and
`|u| ≥ N²` (`Salt/MR/VanDerCorput.lean`); the middle band `1 ≤ |u| ≤ N²` is the
campaign's named residual for L9 (the dyadic assembly / ExpSum LITT-COVER). -/
theorem halasz_integers_of_vanDerCorput (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (Cvdc : ℝ) (hCvdc : 0 ≤ Cvdc)
    (hZ : ∀ u : ℝ, ‖∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
          ≤ Cvdc * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
              + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)))) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ 4 * (Cvdc + 1) * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine (halasz_integers_log_split N a T hT 𝒯 hws hsub Cvdc hCvdc hZ).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun n _ => by positivity)
  set L := Real.log (2 * T) with hLdef
  set S := (𝒯.card : ℝ) with hSdef
  have hLnn : 0 ≤ L := Real.log_nonneg (by linarith)
  have hSnn : 0 ≤ S := Nat.cast_nonneg _
  have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hst : 0 ≤ S * Real.sqrt T := mul_nonneg hSnn hsqrtT
  have h1L : (0 : ℝ) ≤ 1 + L := by linarith
  have hsq : Real.sqrt (1 + 2 * T) ≤ 2 * Real.sqrt T := by
    rw [show (2 : ℝ) * Real.sqrt T = Real.sqrt (4 * T) by
      rw [Real.sqrt_mul (by norm_num) T, show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hMnn : 0 ≤ 1 + Real.log (2 + 2 * T) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * T by linarith); linarith
  have hM : 1 + Real.log (2 + 2 * T) ≤ 2 * (1 + L) := by
    have hTpos : (0 : ℝ) < 2 * T := by linarith
    have h2 : Real.log (2 + 2 * T) ≤ Real.log (2 * (2 * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (2 * (2 * T)) = Real.log 2 + L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hTpos), ← hLdef]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hhead : 3 * (Cvdc + 1) * (N : ℝ) * (1 + L) ≤ 4 * (Cvdc + 1) * (N : ℝ) * (1 + L) := by
    have hbase : 0 ≤ (Cvdc + 1) * (N : ℝ) * (1 + L) :=
      mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg N)) h1L
    nlinarith [hbase]
  have hprod : Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)) ≤ 4 * Real.sqrt T * (1 + L) := by
    calc Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T))
        ≤ (2 * Real.sqrt T) * (2 * (1 + L)) := mul_le_mul hsq hM hMnn (by positivity)
      _ = 4 * Real.sqrt T * (1 + L) := by ring
  have htail : (Cvdc + 1) * S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)))
      ≤ 4 * (Cvdc + 1) * (S * Real.sqrt T) * (1 + L) := by
    calc (Cvdc + 1) * S * (Real.sqrt (1 + 2 * T) * (1 + Real.log (2 + 2 * T)))
        ≤ (Cvdc + 1) * S * (4 * Real.sqrt T * (1 + L)) := by
          apply mul_le_mul_of_nonneg_left hprod
          exact mul_nonneg (by linarith) hSnn
      _ = 4 * (Cvdc + 1) * (S * Real.sqrt T) * (1 + L) := by ring
  nlinarith [hhead, htail]

end Salt.MR
