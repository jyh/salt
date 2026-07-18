/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Taylor

/-!
# VMVT-VK rung R2 — the block reduction (`VK-SHIFT`)

Three ingredients feeding R4:

* `eR_lipschitz` — `‖eR x − eR y‖ ≤ 2π|x−y|` (mean-value inequality: `‖eR′‖ ≡ 2π`).
* `norm_sum_eR_sub_le` / `block_reduction` — replacing the log phase by its Taylor
  polynomial in a block sum costs `≤ 2π·#·R_taylor`.
* `sum_Ioc_shift_boundary` — the shift identity `‖S − S_y‖ ≤ 2y` (the two windows
  differ by `2y` boundary terms of unit modulus).
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum
open scoped BigOperators ComplexConjugate

/-! ## The character is `2π`-Lipschitz -/

/-- The derivative of the character: `eR′(t) = eR t · (2πI)`, norm `2π`. -/
lemma hasDerivAt_eR (t : ℝ) : HasDerivAt eR (eR t * (2 * (π : ℂ) * Complex.I)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hf : HasDerivAt (fun s : ℝ => 2 * (π : ℂ) * Complex.I * (s : ℂ))
      (2 * (π : ℂ) * Complex.I) t := by
    simpa using h0.const_mul (2 * (π : ℂ) * Complex.I)
  exact hf.cexp

/-- `‖2πI‖ = 2π` (as a complex scalar). -/
lemma norm_two_pi_I : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
  have hrw : (2 : ℂ) * (π : ℂ) * Complex.I = ((2 * π : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- **VK-SHIFT primitive.**  The normalized character is `2π`-Lipschitz:
`‖eR x − eR y‖ ≤ 2π·|x − y|`. -/
theorem eR_lipschitz (x y : ℝ) : ‖eR x - eR y‖ ≤ 2 * π * |x - y| := by
  have hcontER : Continuous eR := by unfold Salt.ExpSum.eR; fun_prop
  have hint : IntervalIntegrable (fun t => eR t * (2 * (π : ℂ) * Complex.I)) volume y x :=
    (hcontER.mul continuous_const).intervalIntegrable y x
  have hFTC : ∫ t in y..x, eR t * (2 * (π : ℂ) * Complex.I) = eR x - eR y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_eR t) hint
  rw [← hFTC]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * π) ?_).trans_eq rfl
  intro t _
  rw [norm_mul, norm_eR, one_mul]
  exact le_of_eq norm_two_pi_I

/-! ## The block reduction: log phase ↦ Taylor polynomial -/

/-- **Block reduction (sum form).**  Replacing the phases `f` by `g` in a character
sum costs at most `2π·∑|f − g|`. -/
theorem norm_sum_eR_sub_le {ι : Type*} (A : Finset ι) (f g : ι → ℝ) :
    ‖∑ n ∈ A, eR (f n) - ∑ n ∈ A, eR (g n)‖ ≤ 2 * π * ∑ n ∈ A, |f n - g n| := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ n ∈ A, (eR (f n) - eR (g n))‖
      ≤ ∑ n ∈ A, ‖eR (f n) - eR (g n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ A, 2 * π * |f n - g n| :=
        Finset.sum_le_sum (fun n _ => eR_lipschitz (f n) (g n))
    _ = 2 * π * ∑ n ∈ A, |f n - g n| := by rw [Finset.mul_sum]

/-- **Block reduction (uniform form).**  If every phase error is `≤ R` on a block `A`,
the character sums differ by `≤ 2π·#A·R`. -/
theorem block_reduction {ι : Type*} (A : Finset ι) (f g : ι → ℝ) (R : ℝ)
    (hR : ∀ n ∈ A, |f n - g n| ≤ R) :
    ‖∑ n ∈ A, eR (f n) - ∑ n ∈ A, eR (g n)‖ ≤ 2 * π * ((A.card : ℝ) * R) := by
  refine (norm_sum_eR_sub_le A f g).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ n ∈ A, |f n - g n|
      ≤ ∑ _n ∈ A, R := Finset.sum_le_sum hR
    _ = (A.card : ℝ) * R := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The shift identity -/

/-- A window `Ioc a (a + y)` carries a character-bounded sum `≤ y` (`y` unit terms). -/
private lemma norm_sum_Ioc_le {z : ℤ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1) (a : ℤ) (y : ℕ) :
    ‖∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n‖ ≤ (y : ℝ) := by
  have hcard : (Finset.Ioc a (a + (y : ℤ))).card = y := by rw [Int.card_Ioc]; omega
  calc ‖∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n‖
      ≤ ∑ n ∈ Finset.Ioc a (a + (y : ℤ)), ‖z n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc a (a + (y : ℤ)), (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => hz n)
    _ = (y : ℝ) := by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

/-- **VK-SHIFT shift identity.**  A window `Ioc a (a+P)` and its `y`-shift
`Ioc (a+y) (a+P+y)` (`y ≤ P`) carry character sums differing by `≤ 2y`
(the two boundary strips of `y` unit-modulus terms). -/
theorem sum_Ioc_shift_boundary {z : ℤ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1)
    (a : ℤ) (P y : ℕ) (hyP : y ≤ P) :
    ‖(∑ n ∈ Finset.Ioc a (a + (P : ℤ)), z n)
        - ∑ n ∈ Finset.Ioc (a + (y : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n‖ ≤ 2 * (y : ℝ) := by
  have hle_ay : a ≤ a + (y : ℤ) := le_add_of_nonneg_right (by positivity)
  have hle_yP : a + (y : ℤ) ≤ a + (P : ℤ) := by
    have : (y : ℤ) ≤ (P : ℤ) := by exact_mod_cast hyP
    linarith
  have hle_PPy : a + (P : ℤ) ≤ a + (P : ℤ) + (y : ℤ) := le_add_of_nonneg_right (by positivity)
  have splitIoc : ∀ p q r : ℤ, p ≤ q → q ≤ r →
      (∑ n ∈ Finset.Ioc p r, z n) = (∑ n ∈ Finset.Ioc p q, z n) + ∑ n ∈ Finset.Ioc q r, z n := by
    intro p q r hpq hqr
    rw [← Finset.Ioc_union_Ioc_eq_Ioc hpq hqr,
      Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl q))]
  have hc1 := splitIoc a (a + (y : ℤ)) (a + (P : ℤ)) hle_ay hle_yP
  have hc2 := splitIoc (a + (y : ℤ)) (a + (P : ℤ)) (a + (P : ℤ) + (y : ℤ)) hle_yP hle_PPy
  have hEq : (∑ n ∈ Finset.Ioc a (a + (P : ℤ)), z n)
        - ∑ n ∈ Finset.Ioc (a + (y : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n
      = (∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n)
        - ∑ n ∈ Finset.Ioc (a + (P : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n := by
    rw [hc1, hc2]; ring
  rw [hEq]
  have hb1 : ‖∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n‖ ≤ (y : ℝ) := norm_sum_Ioc_le hz a y
  have hb2 : ‖∑ n ∈ Finset.Ioc (a + (P : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n‖ ≤ (y : ℝ) :=
    norm_sum_Ioc_le hz (a + (P : ℤ)) y
  calc ‖(∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n)
          - ∑ n ∈ Finset.Ioc (a + (P : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n‖
      ≤ ‖∑ n ∈ Finset.Ioc a (a + (y : ℤ)), z n‖
        + ‖∑ n ∈ Finset.Ioc (a + (P : ℤ)) (a + (P : ℤ) + (y : ℤ)), z n‖ := norm_sub_le _ _
    _ ≤ (y : ℝ) + (y : ℝ) := add_le_add hb1 hb2
    _ = 2 * (y : ℝ) := by ring

end Salt.Vk
