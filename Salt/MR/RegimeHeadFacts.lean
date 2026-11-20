/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinear

/-!
# The head facts at a flat-road regime

Fifteen flat-road discharges receive a regime `R` with `R.eps = ε` and
`R.Hlo = flatWitFloor ε β A Hopq`, at `ε ≥ 1/500` and `A ≥ 162`, and each derived the same four
facts inline: `1 ≤ flatDoorM A`, `1/2^9 ≤ R.eps`, `exp (3.2·A) ≤ log R.Hlo` and
`loglogFloor50 ≤ R.Hlo`. They are derived here once.

## Main result
* `regime_flat_head_facts` — the four facts, as one conjunction.
* `regime_flat_head_facts_mul` — the same at a pin `1/(500·k) ≤ ε` for a charge `k`, with
  `1/(2^9·k) ≤ R.eps` (seven further discharges, at `k = c`, `h` or `8103`).
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The head facts at a flat-road regime.** For a regime `R` with `R.eps = ε ≥ 1/500` and
`R.Hlo = flatWitFloor ε β A Hopq`, at `A ≥ 162`: `1 ≤ flatDoorM A`, `1/2^9 ≤ R.eps`,
`exp (3.2·A) ≤ log R.Hlo` and `loglogFloor50 ≤ R.Hlo`. -/
theorem regime_flat_head_facts {R : ChowlaRegime} {ε : ℚ} {β A : ℝ} {Hopq : ℕ}
    (hReps : R.eps = ε) (hHlo : R.Hlo = flatWitFloor ε β A Hopq)
    (hεpin : (1 : ℚ) / 500 ≤ ε) (hA162 : 162 ≤ A) :
    1 ≤ flatDoorM A
      ∧ (1 : ℚ) / 2 ^ 9 ≤ R.eps
      ∧ Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ)
      ∧ loglogFloor50 ≤ R.Hlo := by
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA162)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  exact ⟨hM1, heps, hlo, hfl⟩

/-- **The head facts at a flat-road regime pinned at a charge `k`.** As
`regime_flat_head_facts`, with the pin `1/(500·k) ≤ ε` for a charge `0 < k` in place of
`1/500 ≤ ε`, and so `1/(2^9·k) ≤ R.eps` in place of `1/2^9 ≤ R.eps`. -/
theorem regime_flat_head_facts_mul {R : ChowlaRegime} {ε : ℚ} {β A : ℝ} {Hopq k : ℕ}
    (hk : 0 < k) (hReps : R.eps = ε) (hHlo : R.Hlo = flatWitFloor ε β A Hopq)
    (hεpin : (1 : ℚ) / (500 * (k : ℚ)) ≤ ε) (hA162 : 162 ≤ A) :
    1 ≤ flatDoorM A
      ∧ (1 : ℚ) / (2 ^ 9 * (k : ℚ)) ≤ R.eps
      ∧ Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ)
      ∧ loglogFloor50 ≤ R.Hlo := by
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA162)
  have heps : (1 : ℚ) / (2 ^ 9 * (k : ℚ)) ≤ R.eps := by
    rw [hReps]
    have hle : (1 : ℚ) / (2 ^ 9 * (k : ℚ)) ≤ 1 / (500 * (k : ℚ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [hkQ]
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  exact ⟨hM1, heps, hlo, hfl⟩

end Salt.MR
