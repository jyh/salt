/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The window's two endpoints at `Tann = 2T`

Every row instance of the A2 ladder that reads its window at the doubled height `Tann = 2T`
derives the same three facts by hand before it calls the row: the lower endpoint
`2·(X/h) ≤ 2·T`, the upper endpoint `2·T ≤ X`, and `0 < 2·T`. The last comes from
`0 < X/h` (`div_pos`) and the first. This file states the three facts once.

The 30 call sites that took them inline are in `A3Middle` (4), `ThmA2Linear` (18) and
`ThmA2Rows` (8); there they are used as `h2a`, `h2b` and `h2T0`. The lemma is over the reals and
imports nothing beyond Mathlib.

The same 30 sites also derived their SCALE PAGE by hand (`0 < X`, `4 ≤ exp 2`, `exp 1 ≤ log X`,
`4 ≤ log X`, `0 ≤ log X` from `exp 1 ≤ X` and `exp 2 ≤ log X`); `scalePage_facts` states it once.

## Main results
* `windowEnds_facts` — the two endpoints and the positivity of `2·T`.
* `scalePage_facts` — the scale page.
-/

namespace Salt.MR

/-- **The window's two endpoints at `Tann = 2T`.** From `0 < X`, `0 < h`, `X/h ≤ T` and
`2·T ≤ X`: `2·(X/h) ≤ 2·T`, `2·T ≤ X` and `0 < 2·T`. -/
theorem windowEnds_facts {X h T : ℝ} (hX0 : 0 < X) (hh : 0 < h) (hT : X / h ≤ T)
    (hTX : 2 * T ≤ X) :
    2 * (X / h) ≤ 2 * T ∧ (2 : ℝ) * T ≤ X ∧ (0 : ℝ) < 2 * T := by
  have hXh : (0 : ℝ) < X / h := div_pos hX0 hh
  exact ⟨by linarith, hTX, by linarith⟩

/-- **The scale page.** From `exp 1 ≤ X` and `exp 2 ≤ log X`: `0 < X`, `4 ≤ exp 2`, `exp 1 ≤ log X`,
`4 ≤ log X` and `0 ≤ log X`, in the order the call sites name them (`hX0 he2 hLXe hL4 hL0`). -/
theorem scalePage_facts {X : ℝ} (hXe : Real.exp 1 ≤ X) (hlX2 : Real.exp 2 ≤ Real.log X) :
    (0 : ℝ) < X ∧ (4 : ℝ) ≤ Real.exp 2 ∧ Real.exp 1 ≤ Real.log X ∧ (4 : ℝ) ≤ Real.log X ∧
      (0 : ℝ) ≤ Real.log X := by
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  exact ⟨lt_of_lt_of_le (Real.exp_pos 1) hXe, he2,
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2, hL4, by linarith⟩

end Salt.MR
