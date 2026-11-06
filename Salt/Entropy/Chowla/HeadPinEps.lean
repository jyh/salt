/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The head's `ε := 1/500` pin

The flat heads (`HloExport` · `HloExportFlat` · `S16Uniform` · `V6SiegelFree` · `S16Compose` ·
`V7SiegelFree` · `XThread`) each pin `ε := 1/500` against the three head constants `cE`, `cD3`
(both `≥ 1/4`) and `C` (`0 < C ≤ 6.55`), and read the same facts about it: its value in `ℚ` and
in `ℝ`, its positivity, the four ceilings `ε ≤ cE/(32·log 4)`, `ε < 1/2`, `ε ≤ cD3/16`,
`ε ≤ cD3/(16·C)`, `ε ≤ 1/2` and `ε² < 1/2`, and the `δ₀` floor
`1/838400 ≤ cD3/(16·C)·ε/4`. This file states them once.

## Main result
* `eps500_pin_facts` — the pin and its facts.
-/

namespace Salt.Entropy.Chowla

/-- **The head's `ε := 1/500` pin.** For `1/4 ≤ cE`, `1/4 ≤ cD3` and `0 < C ≤ 655/100` there is
`ε = 1/500` in `ℚ` with `(ε : ℝ) = 1/500`, `0 < (ε : ℝ)`, `0 < ε`, `ε ≤ cE/(32·log 4)`,
`ε < 1/2`, `ε ≤ cD3/16`, `ε ≤ cD3/(16·C)`, `ε ≤ 1/2`, `ε² < 1/2` and
`1/838400 ≤ cD3/(16·C)·ε/4`. -/
theorem eps500_pin_facts {cE cD3 C : ℝ} (hcEge : 1 / 4 ≤ cE) (hcD3ge : 1 / 4 ≤ cD3)
    (hC : 0 < C) (hCnum : C ≤ 655 / 100) :
    ∃ ε : ℚ, ε = 1 / 500 ∧ ((ε : ℚ) : ℝ) = 1 / 500 ∧ (0 : ℝ) < (ε : ℝ) ∧ 0 < ε ∧
      (ε : ℝ) ≤ cE / (32 * Real.log 4) ∧ (ε : ℝ) < 1 / 2 ∧ (ε : ℝ) ≤ cD3 / 16 ∧
      (ε : ℝ) ≤ cD3 / (16 * C) ∧ ε ≤ 1 / 2 ∧ (ε : ℝ) ^ 2 < 1 / 2 ∧
      (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / 500 := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / 500 := by rw [hεdef]; norm_num
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; norm_num
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    rw [hεR, le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by rw [hεR]; norm_num
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    rw [hεR, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    rw [hεR, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
  have hεQ1 : ε ≤ 1 / 2 := by rw [hεdef]; norm_num
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by rw [hεR]; norm_num
  have hδ₀ge : (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    rw [hεR]; linarith
  exact ⟨ε, hεdef, hεR, hεR0, hεQpos, hεcE, hε_half_lt, hε_D3, hε_D3C, hεQ1, hε2, hδ₀ge⟩

end Salt.Entropy.Chowla
