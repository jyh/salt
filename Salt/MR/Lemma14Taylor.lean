/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronSharp
import Salt.MR.ParsevalSL

/-!
# S8 MR-CORE, node A3a-R2 — the U-slab Taylor main term (Lemma 14, stone S-B)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
p. 22 (Lemma 14; frozen statement transcribed verbatim in `Salt.MR.ParsevalSL`).

In Lemma 14's proof the critical-line Perron integral splits at `T₀ = (log X)^{1/15}`.
On the **low slab** `|t| ≤ T₀` the object is (in `ParsevalAsm`'s normalization)

`Uⱼ(x) := I · ∫_{|t|≤T₀} A(1+it) · ((x+hⱼ)^{1+it} − x^{1+it})/(1+it) dt`
(with `A(1+it) = ∑ aₘ/m^{1+it}`).

This file lands the claim that the **weighted difference** `(1/h₁)U₁ − (1/h₂)U₂` is small.

## The honest page (the mechanism)

Factor the kernel through `sharp_kernel_factor`:
`((x+h)ˢ − xˢ)/s = xˢ·((1+h/x)ˢ − 1)/s`.  A **second-order Taylor** expansion (`taylor2_bound`)
writes `((1+u)ˢ − 1)/s = u + r(u,s)` with `‖r(u,s)‖ ≤ |t|·u²` on the line `s = 1+it`
(`u = h/x`).  The **leading term** `u = h/x` is `h`-linear, so after the `1/hⱼ` weighting it
becomes `1/x`, **independent of `hⱼ`** — hence it CANCELS EXACTLY in `(1/h₁)U₁ − (1/h₂)U₂`
(this is the key `xˢ·(1/x)` cancellation, `uSlab_integrand_diff_norm_le`).  What survives is the
remainder, controlled pointwise by `‖A(1+it)‖·|t|·h₂/x`.

Integrating over the slab (`|t| ≤ T₀`, `∫|t| ≤ 2T₀²` via the sup bound), with the **trivial**
triangle bound `‖A(1+it)‖ ≤ ∑_{X≤m≤4X} 1/m = O(1)` (the short slab needs no cancellation among
the `aₘ` — the Parseval / mean-square machinery `lpoly_mean_sq_bound` is for the `Vⱼ` tail, NOT
the `Uⱼ` main term), one gets

`‖(1/h₁)U₁ − (1/h₂)U₂‖ ≤ 4·(∑ 1/m)·T₀²·(h₂/x)`   (`uSlab_diff_bound` / `uSlab_dpolyA_diff_bound`).

**The exponent check (did `2/15` survive?).**  With `x ≥ X`, `h₂ ≤ X/(log X)^{1/5}` and
`T₀ = (log X)^{1/15}`:
`T₀²·(h₂/x) ≤ (log X)^{2/15}·(log X)^{−1/5} = (log X)^{2/15−3/15} = (log X)^{−1/15}`
(`taylor_grade_arith`).  So the **pointwise** bound is `≪ (log X)^{−1/15}`
(`uSlab_taylor_main`), and its **square** is `≪ (log X)^{−2/15} = 1/T₀²` (`uSlab_taylor_main_sq`) —
exactly the `1/(log X)^{2/15}` main term of Lemma 14 (an `x`-uniform bound, so the `(1/X)∫_X^{2X}`
average is trivial on top).  **`2/15` survives with an `(log X)^{1/15}` margin to spare.**

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## B1 — the pointwise second-order Taylor bound on the line `Re s = 1`. -/

/-- **First-order segment bound at the pure-imaginary exponent** (`s = it`, `Re = 0`).
For `t : ℝ`, `v ≥ 0`: `‖(1+v)^{it} − 1‖ ≤ |t|·v`.  The `c = 0` companion of
`PerronSharp.cpow_ratio_seg_bound`: the MVT on `y ↦ y^{it}` over `[1,1+v]`, whose derivative
`it·y^{it−1}` has norm `|t|·y^{−1} ≤ |t|` for `y ≥ 1`.  Feeds the second-order Taylor bound. -/
theorem cpow_it_seg_bound (t : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ‖((1 + v : ℝ) : ℂ) ^ ((t : ℂ) * I) - 1‖ ≤ |t| * v := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp
  · have hwne : (t : ℂ) * I ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
      exact ht
    have hwnorm : ‖(t : ℂ) * I‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hderiv : ∀ y ∈ Icc (1 : ℝ) (1 + v),
        HasDerivWithinAt (fun z : ℝ => (z : ℂ) ^ ((t : ℂ) * I))
          ((t : ℂ) * I * (y : ℂ) ^ ((t : ℂ) * I - 1)) (Icc (1 : ℝ) (1 + v)) y := by
      intro y hy
      have hy0 : y ≠ 0 := by rw [mem_Icc] at hy; nlinarith [hy.1]
      exact (hasDerivAt_ofReal_cpow_const hy0 hwne).hasDerivWithinAt
    have hbound : ∀ y ∈ Icc (1 : ℝ) (1 + v),
        ‖(t : ℂ) * I * (y : ℂ) ^ ((t : ℂ) * I - 1)‖ ≤ |t| := by
      intro y hy
      rw [mem_Icc] at hy
      have hy1 : (1 : ℝ) ≤ y := hy.1
      have hy0 : 0 < y := by linarith
      rw [norm_mul, hwnorm, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
        show ((t : ℂ) * I - 1).re = -1 by simp]
      have hle : y ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
      calc |t| * y ^ (-1 : ℝ) ≤ |t| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg t)
        _ = |t| := mul_one _
    have hmvt := (convex_Icc (1 : ℝ) (1 + v)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    rw [Complex.ofReal_one, Complex.one_cpow] at hmvt
    calc ‖((1 + v : ℝ) : ℂ) ^ ((t : ℂ) * I) - 1‖ ≤ |t| * ‖(1 + v) - (1 : ℝ)‖ := hmvt
      _ = |t| * v := by rw [show (1 + v) - (1 : ℝ) = v by ring, Real.norm_of_nonneg hv]

/-- **Second-order Taylor bound** (`A3a-R2`, stone B1).  On the line `s = 1 + it`, for `u ≥ 0`,
`‖((1+u)ˢ − 1)/s − u‖ ≤ |t|·u²`.  This is the "`xˢ(h/x + O(|s|(h/x)²))`" expansion MR use on the
U-slab (v4 p. 22): `((1+u)ˢ−1)/s = ∫₀ᵘ (1+w)^{s−1} dw`, so the difference from the linear term `u`
is `∫₀ᵘ ((1+w)^{s−1} − 1) dw`, bounded via `cpow_it_seg_bound` (`s − 1 = it`).  Proven by the MVT
on `w ↦ (1+w)ˢ/s − 1/s − w`, whose derivative is `(1+w)^{s−1} − 1`. -/
theorem taylor2_bound (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖(((1 + u : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) - 1) / ((1 : ℂ) + (t : ℂ) * I) - (u : ℂ)‖
      ≤ |t| * u ^ 2 := by
  set s : ℂ := (1 : ℂ) + (t : ℂ) * I with hs
  have hsne : s ≠ 0 := by
    rw [hs]; intro h
    have hre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
    rw [h] at hre; simp at hre
  have hderiv : ∀ y ∈ Icc (1 : ℝ) (1 + u),
      HasDerivWithinAt (fun z : ℝ => (z : ℂ) ^ s / s - (z : ℂ))
        ((y : ℂ) ^ (s - 1) - 1) (Icc (1 : ℝ) (1 + u)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by rw [mem_Icc] at hy; nlinarith [hy.1]
    have h3 : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
    have hcomb : HasDerivAt (fun z : ℝ => (z : ℂ) ^ s / s - (z : ℂ))
        (s * (y : ℂ) ^ (s - 1) / s - 1) y :=
      ((hasDerivAt_ofReal_cpow_const hy0 hsne).div_const s).sub h3
    rw [mul_div_cancel_left₀ _ hsne] at hcomb
    exact hcomb.hasDerivWithinAt
  have hbound : ∀ y ∈ Icc (1 : ℝ) (1 + u), ‖(y : ℂ) ^ (s - 1) - 1‖ ≤ |t| * u := by
    intro y hy
    rw [mem_Icc] at hy
    have hexp : s - 1 = (t : ℂ) * I := by rw [hs]; ring
    have hkey := cpow_it_seg_bound t (show (0 : ℝ) ≤ y - 1 by linarith [hy.1])
    rw [show ((1 + (y - 1) : ℝ) : ℂ) = (y : ℂ) by push_cast; ring] at hkey
    rw [hexp]
    calc ‖(y : ℂ) ^ ((t : ℂ) * I) - 1‖ ≤ |t| * (y - 1) := hkey
      _ ≤ |t| * u := by gcongr; linarith [hy.2]
  have hmvt := (convex_Icc (1 : ℝ) (1 + u)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  have heq : (fun z : ℝ => (z : ℂ) ^ s / s - (z : ℂ)) (1 + u)
        - (fun z : ℝ => (z : ℂ) ^ s / s - (z : ℂ)) 1
      = (((1 + u : ℝ) : ℂ) ^ s - 1) / s - (u : ℂ) := by
    simp only [Complex.ofReal_one, Complex.one_cpow]
    push_cast
    ring
  rw [heq, show (1 + u) - (1 : ℝ) = u by ring, Real.norm_of_nonneg hu] at hmvt
  calc ‖(((1 + u : ℝ) : ℂ) ^ s - 1) / s - (u : ℂ)‖ ≤ |t| * u * u := hmvt
    _ = |t| * u ^ 2 := by ring

/-! ## The U-slab object (in `ParsevalAsm`'s `I · ∫` normalization). -/

/-- The sharp Perron kernel `((x+h)^{1+it} − x^{1+it})/(1+it)` on the critical line. -/
def uKernel (x h t : ℝ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
    / ((1 : ℂ) + (t : ℂ) * I)

/-- The **U-slab** object `Uⱼ(x) = I · ∫_{|t|≤T₀} A(1+it)·uKernel dt` — the low-`|t|` truncation of
the sharp Perron representation, in `ParsevalAsm`'s `I · ∫` normalization (`Aperron_eq_sum`). -/
def uSlab (A : ℝ → ℂ) (x h T₀ : ℝ) : ℂ :=
  I * ∫ t in (-T₀)..T₀, A t * uKernel x h t

/-- `t ↦ uKernel x h t` is continuous (base `x+h > 0`, `x > 0` off the branch cut; denominator
`1 + it ≠ 0`). -/
lemma uKernel_continuous {x h : ℝ} (hx : 0 < x) (hxh : 0 < x + h) :
    Continuous (fun t : ℝ => uKernel x h t) := by
  have hbase1 : ((x + h : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxh.ne'
  have hbase2 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hden : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hdenne : ∀ t : ℝ, (1 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have hre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
    rw [h] at hre; simp at hre
  change Continuous (fun t : ℝ =>
    (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
      / ((1 : ℂ) + (t : ℂ) * I))
  exact ((hden.const_cpow (Or.inl hbase1)).sub (hden.const_cpow (Or.inl hbase2))).div hden hdenne

/-! ## B2 + B3 — the exact cancellation and the slab bound. -/

/-- **B2 — the exact `hⱼ`-linear cancellation, pointwise in `t`.**  The weighted-difference
integrand `(1/h₁)·(A·uKernel₁) − (1/h₂)·(A·uKernel₂)` has its `xˢ·(1/x)` leading terms cancel
(they are `hⱼ`-independent), leaving only the second-order Taylor remainder, of norm
`≤ 2·M·|t|·(h₂/x)` (`M ≥ ‖A t‖`). -/
lemma uSlab_integrand_diff_norm_le (A : ℝ → ℂ) {x h₁ h₂ M : ℝ}
    (hx : 0 < x) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (hh12 : h₁ ≤ h₂)
    (hM : ∀ t, ‖A t‖ ≤ M) (t : ℝ) :
    ‖((1 / h₁ : ℝ) : ℂ) * (A t * uKernel x h₁ t)
        - ((1 / h₂ : ℝ) : ℂ) * (A t * uKernel x h₂ t)‖
      ≤ 2 * M * |t| * (h₂ / x) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM t)
  have hxne : x ≠ 0 := hx.ne'
  have hh1ne : h₁ ≠ 0 := hh1.ne'
  have hh2ne : h₂ ≠ 0 := hh2.ne'
  have hxh1 : 0 < x + h₁ := by linarith
  have hxh2 : 0 < x + h₂ := by linarith
  set s : ℂ := (1 : ℂ) + (t : ℂ) * I with hs
  set xs : ℂ := ((x : ℝ) : ℂ) ^ s with hxsdef
  set k₁ : ℂ := (((1 + h₁ / x : ℝ) : ℂ) ^ s - 1) / s with hk1
  set k₂ : ℂ := (((1 + h₂ / x : ℝ) : ℂ) ^ s - 1) / s with hk2
  set r₁ : ℂ := k₁ - ((h₁ / x : ℝ) : ℂ) with hr1
  set r₂ : ℂ := k₂ - ((h₂ / x : ℝ) : ℂ) with hr2
  have huk1 : uKernel x h₁ t = xs * k₁ := sharp_kernel_factor hx hxh1 s
  have huk2 : uKernel x h₂ t = xs * k₂ := sharp_kernel_factor hx hxh2 s
  have hkr1 : k₁ = r₁ + ((h₁ / x : ℝ) : ℂ) := by rw [hr1]; ring
  have hkr2 : k₂ = r₂ + ((h₂ / x : ℝ) : ℂ) := by rw [hr2]; ring
  have hb1 : ‖r₁‖ ≤ |t| * (h₁ / x) ^ 2 := by rw [hr1, hk1]; exact taylor2_bound t (by positivity)
  have hb2 : ‖r₂‖ ≤ |t| * (h₂ / x) ^ 2 := by rw [hr2, hk2]; exact taylor2_bound t (by positivity)
  have hh1c : (h₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh1ne
  have hh2c : (h₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh2ne
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
  have key : ((1 / h₁ : ℝ) : ℂ) * (A t * uKernel x h₁ t)
        - ((1 / h₂ : ℝ) : ℂ) * (A t * uKernel x h₂ t)
      = A t * xs * (((1 / h₁ : ℝ) : ℂ) * r₁ - ((1 / h₂ : ℝ) : ℂ) * r₂) := by
    rw [huk1, huk2, hkr1, hkr2]
    push_cast
    field_simp
    ring
  rw [key]
  have hxsnorm : ‖xs‖ = x := by
    rw [hxsdef, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      show s.re = 1 by rw [hs]; simp, Real.rpow_one]
  have hD : ‖((1 / h₁ : ℝ) : ℂ) * r₁ - ((1 / h₂ : ℝ) : ℂ) * r₂‖ ≤ 2 * |t| * (h₂ / x ^ 2) := by
    calc ‖((1 / h₁ : ℝ) : ℂ) * r₁ - ((1 / h₂ : ℝ) : ℂ) * r₂‖
        ≤ ‖((1 / h₁ : ℝ) : ℂ) * r₁‖ + ‖((1 / h₂ : ℝ) : ℂ) * r₂‖ := norm_sub_le _ _
      _ = (1 / h₁) * ‖r₁‖ + (1 / h₂) * ‖r₂‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₁),
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₂)]
      _ ≤ (1 / h₁) * (|t| * (h₁ / x) ^ 2) + (1 / h₂) * (|t| * (h₂ / x) ^ 2) := by gcongr
      _ = |t| * (h₁ / x ^ 2) + |t| * (h₂ / x ^ 2) := by rw [div_pow, div_pow]; field_simp
      _ ≤ |t| * (h₂ / x ^ 2) + |t| * (h₂ / x ^ 2) := by gcongr
      _ = 2 * |t| * (h₂ / x ^ 2) := by ring
  calc ‖A t * xs * (((1 / h₁ : ℝ) : ℂ) * r₁ - ((1 / h₂ : ℝ) : ℂ) * r₂)‖
      = ‖A t‖ * x * ‖((1 / h₁ : ℝ) : ℂ) * r₁ - ((1 / h₂ : ℝ) : ℂ) * r₂‖ := by
        rw [norm_mul, norm_mul, hxsnorm]
    _ ≤ M * x * (2 * |t| * (h₂ / x ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hM t) hx.le) hD (norm_nonneg _)
          (mul_nonneg hM0 hx.le)
    _ = 2 * M * |t| * (h₂ / x) := by field_simp

/-- **B3 — the U-slab weighted-difference bound.**  For a bounded weight `‖A t‖ ≤ M`, `x > 0`,
`0 < h₁ ≤ h₂`, `T₀ ≥ 0`:
`‖(1/h₁)·U₁ − (1/h₂)·U₂‖ ≤ 4·M·T₀²·(h₂/x)`.
The `xˢ·(1/x)` leading term cancels (`uSlab_integrand_diff_norm_le`); the surviving second-order
remainder is integrated over the slab `|t| ≤ T₀` with the sup bound
(`norm_integral_le_of_norm_le_const`, `∫|t| ≤ 2T₀²`). -/
theorem uSlab_diff_bound (A : ℝ → ℂ) {x h₁ h₂ T₀ M : ℝ}
    (hx : 0 < x) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hT : 0 ≤ T₀)
    (hAc : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ T₀ - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ T₀‖
      ≤ 4 * M * T₀ ^ 2 * (h₂ / x) := by
  have hh2 : 0 < h₂ := lt_of_lt_of_le hh1 hh12
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hfracnn : (0 : ℝ) ≤ h₂ / x := by positivity
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith
  have hcont1 : Continuous (fun t => A t * uKernel x h₁ t) :=
    hAc.mul (uKernel_continuous hx (by linarith))
  have hcont2 : Continuous (fun t => A t * uKernel x h₂ t) :=
    hAc.mul (uKernel_continuous hx (by linarith))
  have hInt1 : IntervalIntegrable
      (fun t => ((1 / h₁ : ℝ) : ℂ) * (A t * uKernel x h₁ t)) volume (-T₀) T₀ :=
    (continuous_const.mul hcont1).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable
      (fun t => ((1 / h₂ : ℝ) : ℂ) * (A t * uKernel x h₂ t)) volume (-T₀) T₀ :=
    (continuous_const.mul hcont2).intervalIntegrable _ _
  have e1 : ((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ T₀
      = I * ∫ t in (-T₀)..T₀, ((1 / h₁ : ℝ) : ℂ) * (A t * uKernel x h₁ t) := by
    rw [uSlab, intervalIntegral.integral_const_mul]; ring
  have e2 : ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ T₀
      = I * ∫ t in (-T₀)..T₀, ((1 / h₂ : ℝ) : ℂ) * (A t * uKernel x h₂ t) := by
    rw [uSlab, intervalIntegral.integral_const_mul]; ring
  rw [e1, e2, ← mul_sub, ← intervalIntegral.integral_sub hInt1 hInt2,
    norm_mul, Complex.norm_I, one_mul]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * M * T₀ * (h₂ / x)) ?_).trans_eq ?_
  · intro t ht
    have htle : |t| ≤ T₀ := by
      rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.mpr ⟨by linarith, h2⟩
      · exfalso; linarith
    calc ‖((1 / h₁ : ℝ) : ℂ) * (A t * uKernel x h₁ t)
            - ((1 / h₂ : ℝ) : ℂ) * (A t * uKernel x h₂ t)‖
        ≤ 2 * M * |t| * (h₂ / x) := uSlab_integrand_diff_norm_le A hx hh1 hh2 hh12 hM t
      _ ≤ 2 * M * T₀ * (h₂ / x) := by gcongr
  · rw [show T₀ - (-T₀) = 2 * T₀ by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * T₀)]; ring

/-! ## The concrete Dirichlet polynomial `A(1+it) = ∑ aₘ/m^{1+it}`. -/

/-- The critical-line Dirichlet polynomial `A(1+it) = ∑_{m∈s0} aₘ/m^{1+it}` (MR's `A(s)` at
`s = 1+it`; matches `ParsevalAsm`'s inner sum with `c = 1`). -/
def dpolyA (a : ℕ → ℂ) (s0 : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)

/-- The **trivial** (triangle) bound `‖A(1+it)‖ ≤ ∑ 1/m`, uniform in `t` — all the U-slab main term
needs (no cancellation among the `aₘ`). -/
lemma dpolyA_norm_le (a : ℕ → ℂ) (s0 : Finset ℕ) (hpos : ∀ m ∈ s0, 0 < m)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1) (t : ℝ) :
    ‖dpolyA a s0 t‖ ≤ ∑ m ∈ s0, 1 / (m : ℝ) := by
  change ‖∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)‖ ≤ ∑ m ∈ s0, 1 / (m : ℝ)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hpos m hm
  rw [norm_div, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hmpos,
    show ((1 : ℂ) + (t : ℂ) * I).re = 1 by simp, Real.rpow_one]
  gcongr
  exact ha m hm

/-- `t ↦ A(1+it)` is continuous (finite sum of continuous terms; each base `m > 0`). -/
lemma dpolyA_continuous (a : ℕ → ℂ) (s0 : Finset ℕ) (hpos : ∀ m ∈ s0, 0 < m) :
    Continuous (fun t : ℝ => dpolyA a s0 t) := by
  change Continuous (fun t : ℝ => ∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
  apply continuous_finsetSum
  intro m hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (hpos m hm).ne'
  apply Continuous.div continuous_const
  · exact (by fun_prop : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I)).const_cpow (Or.inl hmC)
  · intro t; simp [Complex.cpow_eq_zero_iff, hmC]

/-- **The U-slab bound for the concrete Dirichlet weight** — the `ParsevalAsm`-normalized U-slab
weighted difference, `≤ 4·(∑ 1/m)·T₀²·(h₂/x)`. -/
theorem uSlab_dpolyA_diff_bound (a : ℕ → ℂ) (s0 : Finset ℕ) {x h₁ h₂ T₀ : ℝ}
    (hx : 0 < x) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hT : 0 ≤ T₀)
    (hpos : ∀ m ∈ s0, 0 < m) (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T₀
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T₀‖
      ≤ 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * T₀ ^ 2 * (h₂ / x) :=
  uSlab_diff_bound (dpolyA a s0) hx hh1 hh12 hT (dpolyA_continuous a s0 hpos)
    (fun t => dpolyA_norm_le a s0 hpos ha t)

/-! ## The grade — `T₀²·(h₂/x) ≤ (log X)^{−1/15}` (the `2/15` check). -/

/-- **The exponent bookkeeping.**  With `x ≥ X`, `h₂ ≤ X·(log X)^{−1/5}` and `T₀ = (log X)^{1/15}`:
`T₀²·(h₂/x) ≤ (log X)^{−1/15}` — i.e. `(log X)^{2/15}·(log X)^{−1/5} = (log X)^{−1/15}`.  This is
what makes the U-slab main term `≪ 1/T₀² = 1/(log X)^{2/15}` after squaring. -/
lemma taylor_grade_arith {x h₂ X : ℝ}
    (hX : 1 < X) (hxX : X ≤ x) (hh2 : 0 ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) :
    ((Real.log X) ^ (1 / 15 : ℝ)) ^ 2 * (h₂ / x) ≤ (Real.log X) ^ (-(1 / 15 : ℝ)) := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hXne : X ≠ 0 := hXpos.ne'
  have hT2 : ((Real.log X) ^ (1 / 15 : ℝ)) ^ 2 = (Real.log X) ^ (2 / 15 : ℝ) := by
    rw [← Real.rpow_natCast ((Real.log X) ^ (1 / 15 : ℝ)) 2, ← Real.rpow_mul hL.le]
    norm_num
  have hfrac : h₂ / x ≤ (Real.log X) ^ (-(1 / 5 : ℝ)) := by
    calc h₂ / x ≤ h₂ / X := by gcongr
      _ ≤ (X * (Real.log X) ^ (-(1 / 5 : ℝ))) / X := by gcongr
      _ = (Real.log X) ^ (-(1 / 5 : ℝ)) := by
          rw [mul_comm, mul_div_assoc, div_self hXne, mul_one]
  rw [hT2]
  calc (Real.log X) ^ (2 / 15 : ℝ) * (h₂ / x)
      ≤ (Real.log X) ^ (2 / 15 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ)) := by gcongr
    _ = (Real.log X) ^ (-(1 / 15 : ℝ)) := by rw [← Real.rpow_add hL]; norm_num

/-- **Stone S-B (`A3a-R2`), the pointwise form.**  The U-slab weighted difference for the Dirichlet
weight is `≪ (log X)^{−1/15}`, uniformly in `x ∈ [X, ∞)`, at `T₀ = (log X)^{1/15}`, `x ≥ X`,
`1 ≤ h₁ ≤ h₂ ≤ X/(log X)^{1/5}`, `‖aₘ‖ ≤ 1` on `s0`.  Combines `uSlab_dpolyA_diff_bound` with
`taylor_grade_arith`. -/
theorem uSlab_taylor_main (a : ℕ → ℂ) (s0 : Finset ℕ) {x h₁ h₂ X : ℝ}
    (hX : 1 < X) (hxX : X ≤ x)
    (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hpos : ∀ m ∈ s0, 0 < m) (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ ((Real.log X) ^ (1 / 15 : ℝ))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ ((Real.log X) ^ (1 / 15 : ℝ))‖
      ≤ 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * (Real.log X) ^ (-(1 / 15 : ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (lt_trans zero_lt_one hX) hxX
  have hh1' : 0 < h₁ := lt_of_lt_of_le zero_lt_one hh1
  have hh2' : 0 ≤ h₂ := le_trans (le_trans zero_le_one hh1) hh12
  have hT : 0 ≤ (Real.log X) ^ (1 / 15 : ℝ) := Real.rpow_nonneg (Real.log_pos hX).le _
  have hbound := uSlab_dpolyA_diff_bound a s0 hx0 hh1' hh12 hT hpos ha
  have hgrade := taylor_grade_arith hX hxX hh2' hh2X
  calc ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ ((Real.log X) ^ (1 / 15 : ℝ))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ ((Real.log X) ^ (1 / 15 : ℝ))‖
      ≤ 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * ((Real.log X) ^ (1 / 15 : ℝ)) ^ 2 * (h₂ / x) := hbound
    _ = 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * (((Real.log X) ^ (1 / 15 : ℝ)) ^ 2 * (h₂ / x)) := by ring
    _ ≤ 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * (Real.log X) ^ (-(1 / 15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hgrade (by positivity)

/-- **Stone S-B, the squared / `2/15` form.**  The square of the U-slab weighted difference is
`≪ (log X)^{−2/15} = 1/T₀²` — exactly the `1/(log X)^{2/15}` main term of Lemma 14 (an `x`-uniform
bound, so the `(1/X)∫_X^{2X}` average carries through trivially). -/
theorem uSlab_taylor_main_sq (a : ℕ → ℂ) (s0 : Finset ℕ) {x h₁ h₂ X : ℝ}
    (hX : 1 < X) (hxX : X ≤ x)
    (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hpos : ∀ m ∈ s0, 0 < m) (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ ((Real.log X) ^ (1 / 15 : ℝ))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ ((Real.log X) ^ (1 / 15 : ℝ))‖ ^ 2
      ≤ 16 * (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by
  have hL : 0 < Real.log X := Real.log_pos hX
  have hmain := uSlab_taylor_main a s0 hX hxX hh1 hh12 hh2X hpos ha
  have hbnn : (0 : ℝ) ≤ 4 * (∑ m ∈ s0, 1 / (m : ℝ)) * (Real.log X) ^ (-(1 / 15 : ℝ)) := by
    positivity
  calc ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ ((Real.log X) ^ (1 / 15 : ℝ))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ ((Real.log X) ^ (1 / 15 : ℝ))‖ ^ 2
      ≤ (4 * (∑ m ∈ s0, 1 / (m : ℝ)) * (Real.log X) ^ (-(1 / 15 : ℝ))) ^ 2 := by
        gcongr
    _ = 16 * (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by
        have he : ((Real.log X) ^ (-(1 / 15 : ℝ))) ^ 2 = (Real.log X) ^ (-(2 / 15 : ℝ)) := by
          rw [← Real.rpow_natCast ((Real.log X) ^ (-(1 / 15 : ℝ))) 2, ← Real.rpow_mul hL.le]
          norm_num
        rw [mul_pow, mul_pow, he]; ring

end Salt.MR
