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

end Salt.MR
