/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The stride receipts' pinned constants

The stride and band receipts at shift `h` (`StridePairReceipt` ×2 · `StridePairReceiptG` ×2 ·
`StridePairReceiptG12b` · `TierSBand`) each opened by fixing the same constants and the same
facts about them: the leaf numerals `log 4 = 2·log 2` with both `d9` bounds on `log 2`, the
constants `c_{D3} = 1/4` and `C = h·(1 + 2·(2·log 4)) = h·(1 + 8·log 2)`, and the pin
`ε = 1/(500·h)` with `0 < ε ≤ 1/2`. They are fixed here once. Each site keeps its own `δ₀` mint
(`hval`), whose dyadic divisor differs between the receipts.

## Main result
* `stride_pin_facts` — the three constants, by their defining equations, and the facts the
  receipts read about them.
-/

namespace Salt.MR

/-- **The stride receipts' pinned constants.** For `0 < h` there are `c_{D3} = 1/4`,
`C = h·(1 + 2·(2·log 4))` and `ε = 1/(500·h)` (in `ℚ`) with `0 < log 4`, `log 2` between
`0.6931471803` and `0.6931471808` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`),
`log 4 = 2·log 2`, `0 < c_{D3}`, `0 < 1 + 8·log 2` (so it is nonzero), `C = h·(1 + 8·log 2)`,
`0 < C`, `(ε : ℝ) = 1/(500·h)`, `0 < ε` and `ε ≤ 1/2`. The constants are returned by their
equations, so a receipt reads them as names. -/
theorem stride_pin_facts (h : ℕ) (hh : 0 < h) :
    ∃ (cD3 C : ℝ) (ε : ℚ),
      cD3 = 1 / 4 ∧ C = (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧ ε = 1 / (500 * (h : ℚ))
      ∧ 0 < Real.log 4 ∧ Real.log 2 < 0.6931471808 ∧ 0.6931471803 < Real.log 2
      ∧ Real.log 4 = 2 * Real.log 2 ∧ 0 < cD3 ∧ (0 : ℝ) < 1 + 8 * Real.log 2
      ∧ (1 : ℝ) + 8 * Real.log 2 ≠ 0 ∧ C = (h : ℝ) * (1 + 8 * Real.log 2) ∧ 0 < C
      ∧ ((ε : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) ∧ (0 : ℝ) < (ε : ℝ) ∧ 0 < ε ∧ ε ≤ 1 / 2 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = (h : ℝ) * (1 + 2 * (2 * Real.log 4)) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hLpos : (0 : ℝ) < 1 + 8 * Real.log 2 := by linarith
  have hLne : (1 : ℝ) + 8 * Real.log 2 ≠ 0 := ne_of_gt hLpos
  have hCval : C = (h : ℝ) * (1 + 8 * Real.log 2) := by rw [hCdef, hlog4eq]; ring
  have hC : 0 < C := by rw [hCval]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / (500 * (h : ℚ)) := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / (500 * (h : ℝ)) := by rw [hεdef]; push_cast; ring
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; positivity
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεQ1 : ε ≤ 1 / 2 := by
    have hhQ : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    rw [hεdef]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  exact ⟨cD3, C, ε, hcD3def, hCdef, hεdef, hlog4, hlog2lt, hlog2gt, hlog4eq, hcD3, hLpos, hLne,
    hCval, hC, hεR, hεR0, hεQpos, hεQ1⟩

end Salt.MR
