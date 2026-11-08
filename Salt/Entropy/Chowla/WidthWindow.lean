/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.Regime

/-!
# The width window of a regime

A regime's majorant field `hPHheadroom` (`8·(4^⌊ε²H₊⌋₊)²·ω ≤ x`), read against an `x`-ceiling
`log x ≤ 31/ε · H₊`, leaves room for the width: `log ω + ε²·H₊ ≤ 31/ε · H₊`. The flat-door
and stride receipts (`FlatDoorAllGradesBand` · `FlatDoorEpsRung2` · `StrideDoorAllGrades` ·
`StridePairReceipt` · `TierSBand` · `XThread`) each derived it inline as their `hωgate`.

Route: with `n = ⌊ε²H₊⌋₊` and `P = 4^n`, `log 8 + 2·log P + log ω ≤ log x` from the field;
`log P = n·log 4` with `n ≥ ε²H₊ − 1`; `log 4 ≥ 1.3862` and `log 8 ≥ 2.0794` from the `d9`
bound on `log 2`; and the coprimality floor `ε²H₊ ≥ 2` (from `hcoprime`, `1 ≤ a` and
`H₋ ≤ H₊`). One `nlinarith` closes it.

## Main result
* `ChowlaRegime.width_window` — `log ω + ε²·H₊ ≤ 31/ε · H₊` from `R.eps = ε` and the ceiling.
-/

namespace Salt.Entropy.Chowla

/-- **The width window.** For a regime `R` with `R.eps = eps` and the `x`-ceiling
`log x ≤ 31/eps · H₊`: `log ω + eps²·H₊ ≤ 31/eps · H₊`. The majorant field `hPHheadroom` gives
`log 8 + 2·n·log 4 + log ω ≤ log x` at `n = ⌊eps²H₊⌋₊ ≥ eps²H₊ − 1`, and the coprimality floor
`eps²H₊ ≥ 2` pays the constants. -/
theorem ChowlaRegime.width_window (R : ChowlaRegime) {eps : ℚ} (hReps : R.eps = eps)
    (hRx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) :
    Real.log ((R.ω : ℕ) : ℝ) + (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ)
      ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  set P : ℕ := 4 ^ ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hPdef
  set n : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hndef
  have hPH : 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) ≤ ((R.x : ℕ) : ℝ) := R.hPHheadroom
  have hP1 : (1 : ℝ) ≤ ((P : ℕ) : ℝ) := by
    rw [hPdef]
    have : (1 : ℕ) ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  have hω1 : (1 : ℝ) ≤ ((R.ω : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ R.ω := le_trans (by norm_num) R.hω
    exact_mod_cast this
  -- `log 8 + 2·log P + log ω ≤ log x`
  have hpos : (0 : ℝ) < 8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ) := by positivity
  have hlogle : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
      ≤ Real.log ((R.x : ℕ) : ℝ) := Real.log_le_log hpos hPH
  have hsplit : Real.log (8 * ((P : ℕ) : ℝ) ^ 2 * ((R.ω : ℕ) : ℝ))
      = Real.log 8 + 2 * Real.log ((P : ℕ) : ℝ) + Real.log ((R.ω : ℕ) : ℝ) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast
    ring
  -- `log P = n·log 4 ≥ (ε²H₊ − 1)·log 4`
  have hlogP : Real.log ((P : ℕ) : ℝ) = (n : ℝ) * Real.log 4 := by
    rw [hPdef]
    have h4 : ((4 ^ n : ℕ) : ℝ) = (4 : ℝ) ^ n := by push_cast; ring
    rw [h4, Real.log_pow]
  have hnge : (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1 ≤ (n : ℝ) := by
    have hQ : R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) < (n : ℚ) + 1 := by
      rw [hndef]; exact Nat.lt_floor_add_one _
    have hR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hQ
    rw [hReps] at hR
    linarith
  have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
    have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [h]; linarith [Real.log_two_gt_d9]
  have hlog8 : (2.0794 : ℝ) ≤ Real.log 8 := by
    have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [h]; linarith [Real.log_two_gt_d9]
  -- ⟦THE COPRIMALITY FLOOR⟧ `ε²·H₊ ≥ 2`
  have hcop : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) := by
    have hQ : ((R.a : ℕ) : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) / 2 := R.hcoprime
    have ha1 : (1 : ℚ) ≤ ((R.a : ℕ) : ℚ) := by exact_mod_cast R.ha
    have hQ2 : (2 : ℚ) ≤ R.eps ^ 2 * ((R.Hlo : ℕ) : ℚ) := by linarith
    have hR2 : (2 : ℝ) ≤ (R.eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) := by exact_mod_cast hQ2
    rw [hReps] at hR2
    have hmono : (eps : ℝ) ^ 2 * ((R.Hlo : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast R.hHlohi) (sq_nonneg _)
    linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith [hlogle, hsplit, hlogP, hnge, hlog4, hlog8, hRx, hcop, hnn]

end Salt.Entropy.Chowla
