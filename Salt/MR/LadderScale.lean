/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4MeanSq

/-!
# The ladder's scale page (`LadderScale`)

The ladder and mean-square consumers open their frame at a scale `X` with
`exp (exp 1) ≤ X`, `exp 2 ≤ log X`, `(Xd : ℝ) = X` and `N = 2 · Xd`, then re-derive the same
eleven facts about `X`, `Xd` and `N` (the tactics catalogue's "scale page"). This module states
them once.
-/

namespace Salt.MR

/-- The scale page: from `hXee : exp (exp 1) ≤ X`, `hlX2 : exp 2 ≤ log X`, `hXd : (Xd : ℝ) = X`
and `hNXd : N = 2 * Xd`, the eleven facts the ladder consumers use, in their order:
`exp 1 ≤ X`, `3 ≤ X`, `0 < X`, `0 < log X`, `X ≤ Xd`, `1 ≤ Xd`, `2 * Xd ≤ N`, `N ≤ 2 * Xd`,
`X ≤ N`, `N ≤ 2 * X` and `N ≤ 4 * Xd` (the last six as reals where they compare with `X`). -/
theorem ladder_scale_page {X : ℝ} {N Xd : ℕ} (hXee : Real.exp (Real.exp 1) ≤ X)
    (hlX2 : Real.exp 2 ≤ Real.log X) (hXd : (Xd : ℝ) = X) (hNXd : N = 2 * Xd) :
    Real.exp 1 ≤ X ∧ (3 : ℝ) ≤ X ∧ (0 : ℝ) < X ∧ (0 : ℝ) < Real.log X ∧ X ≤ (Xd : ℝ) ∧
      1 ≤ Xd ∧ 2 * Xd ≤ N ∧ (N : ℝ) ≤ 2 * (Xd : ℝ) ∧ X ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * X ∧
      (N : ℝ) ≤ 4 * (Xd : ℝ) := by
  have hXe : Real.exp 1 ≤ X := le_trans exp_one_le_exp_exp_one hXee
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three hXee)
  have hX0 : (0 : ℝ) < X := by linarith
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 2) hlX2
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by rw [hXd]; linarith
  have hNcast : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  refine ⟨hXe, hX3, hX0, hLX0, le_of_eq hXd.symm, by exact_mod_cast hXd1', le_of_eq hNXd.symm,
    by rw [hNcast, hXd], by rw [hNcast]; linarith, le_of_eq hNcast, by rw [hNcast, hXd]; linarith⟩

end Salt.MR
