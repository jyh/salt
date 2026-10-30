/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The door-close scale facts (`DoorCloseScale`)

The door-close and row consumers open their frame at a natural scale `Xd` with
`exp (exp 1) ≤ Xd` and `exp 2 ≤ log Xd`, then re-derive the same four facts about it in thirteen
lines (the tactics catalogue's door-close block). This module states them once; it needs nothing
but Mathlib.
-/

namespace Salt.MR

/-- From `hXee : exp (exp 1) ≤ Xd` and `hlX2 : exp 2 ≤ log Xd` (as reals): `0 < Xd`, `1 ≤ Xd`,
`1 < log Xd` and `exp 1 ≤ log Xd`. The second uses `1 ≤ exp (exp 1)`, the third `3 ≤ exp 2`,
both from `Real.add_one_le_exp`. -/
theorem door_close_scale {Xd : ℕ} (hXee : Real.exp (Real.exp 1) ≤ ((Xd : ℕ) : ℝ))
    (hlX2 : Real.exp 2 ≤ Real.log ((Xd : ℕ) : ℝ)) :
    (0 : ℝ) < ((Xd : ℕ) : ℝ) ∧ 1 ≤ Xd ∧ (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) ∧
      Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  refine ⟨hX0, hXd1, by linarith, le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2⟩

end Salt.MR
