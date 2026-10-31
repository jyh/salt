/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinear
import Salt.MR.RegisterRepair

/-!
# The co-factor supply's inputs at a flat-road regime

The flat-door discharges (`DoorReceipt` · `DoorReceiptSiegelFree` · `V6SiegelFree` ×2 · `V7C` ·
`V7E` · `V7Ks` · `V7Rated` · `V7SiegelFree` ×3) each fire the flat road and receive a regime `R`
with `R.eps = ε`, `R.Hlo = flatWitFloor ε β A Hopq`, the `x`-ceiling at `31/ε` and the design
bound `3.2·A ≤ log log R.Hlo`. Each then derived the same eight facts inline, the inputs of the
co-factor supply (`hcofR …`) and of the base-scale cap (`s16_baseScaleCap96_L_at_klevF`). They are
derived here once, from `ε ≥ 1/500`, `A ≥ 162` and the threshold `cofkRThr Cq Cb Xsk Y0 ≤ A`.

## Main result
* `regime_flat_supply_facts` — the eight facts, as one conjunction.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The supply's inputs at a flat-road regime.** For a regime `R` with `R.eps = ε ≥ 1/500`,
`R.Hlo = flatWitFloor ε β A Hopq`, `log R.x ≤ 31/ε · R.Hhi` and `3.2·A ≤ log log R.Hlo`, at
`A ≥ 162` with `cofkRThr Cq Cb Xsk Y0 ≤ A`: `1/500 ≤ R.eps` (in `ℚ` and in `ℝ`), the
`x`-ceiling at `31/R.eps`, `1 ≤ flatDoorM A`, `518 ≤ log log R.Hlo` (as `3.2·162 = 518.4`),
`loglogFloor50 ≤ R.Hlo`, `exp (3.2·A) ≤ log R.Hlo`, and the threshold
`cofkRThr Cq Cb Xsk Y0 ≤ log R.Hlo` (through `A < 3.2·A + 1 ≤ exp (3.2·A)`). -/
theorem regime_flat_supply_facts {R : ChowlaRegime} {ε : ℚ} {β A : ℝ} {Hopq : ℕ}
    {Cq Cb Xsk Y0 : ℝ} (hReps : R.eps = ε) (hHlo : R.Hlo = flatWitFloor ε β A Hopq)
    (hRx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hεpin : (1 : ℚ) / 500 ≤ ε) (hA162 : 162 ≤ A) (hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A) :
    (1 : ℚ) / 500 ≤ R.eps
      ∧ Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)
      ∧ 1 ≤ flatDoorM A
      ∧ (1 : ℝ) / 500 ≤ (R.eps : ℝ)
      ∧ (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ))
      ∧ loglogFloor50 ≤ R.Hlo
      ∧ Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ)
      ∧ cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / 500 ≤ (R.eps : ℝ) := by
    rw [hReps]
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith only [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  exact ⟨heps500, hxceil, hM1, heps500R, h518, hfl, hlo, hthrgate⟩

end Salt.MR
