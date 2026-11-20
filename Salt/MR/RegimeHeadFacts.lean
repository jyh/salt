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

end Salt.MR
