/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The free block's closing arithmetic (O13-e candidate #49, TACTICS-CATALOGUE #4)

Role: one lemma for the last step of a shifted-block mean-square bound, shared by 12 sites in
five `Salt/MR` row files. Each site has already reduced its block sum `S` to
`b * (P ^ 2 * m + 4 * (P ^ 2 / a))`, where `b` is the block's right end, `a` its left end, `P`
the window length and `m` the row's mean-square constant. The free block gives `b ≤ 2 * A + 4`
and `b ≤ 2 * a`. The first comparison prices the `m` term at `2 * A + 4`; the second turns the
slack term `4 * P ^ 2 / a` into `8 * P ^ 2`, because `b / a ≤ 2`. Each site was a 33-line chain
of named comparisons (`hBs2` · `hBAs` · `h1`–`h3` · `hsplit` · `hr` · `hgoal`).
-/

namespace Salt.MR

/-- The free block's closing arithmetic: from `S ≤ b * (P ^ 2 * m + 4 * (P ^ 2 / a))`,
`b ≤ 2 * A + 4`, `b ≤ 2 * a`, `0 < a` and `0 ≤ m`, the bound
`S ≤ 2 * m * P ^ 2 * A + (4 * m + 8) * P ^ 2`. -/
theorem free_block_tail {S b a A P m : ℝ} (hex : S ≤ b * (P ^ 2 * m + 4 * (P ^ 2 / a)))
    (hbA : b ≤ 2 * A + 4) (hba : b ≤ 2 * a) (ha : 0 < a) (hm : 0 ≤ m) :
    S ≤ 2 * m * P ^ 2 * A + (4 * m + 8) * P ^ 2 := by
  have hP : 0 ≤ P ^ 2 := sq_nonneg P
  have h1 : b * (P ^ 2 * m) ≤ (2 * A + 4) * (P ^ 2 * m) :=
    mul_le_mul_of_nonneg_right hbA (mul_nonneg hP hm)
  have h2 : b * (4 * (P ^ 2 / a)) ≤ 2 * a * (4 * (P ^ 2 / a)) :=
    mul_le_mul_of_nonneg_right hba (by positivity)
  have h3 : 2 * a * (4 * (P ^ 2 / a)) = 8 * P ^ 2 := by
    field_simp
    ring
  nlinarith [h1, h2, h3, hex]

end Salt.MR
