/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.Regime

/-!
# The stride shrink's facts at a pinned regime

The stride and band receipts (`StridePairReceipt` · `StridePairReceiptG` ·
`StridePairReceiptG12b` · `TierSBand` · `TierSBandU`) each read the same five facts off a regime
`R` whose `ε` is pinned at `1/(500·k)` with `1 ≤ k ≤ N` and whose lower endpoint is
`R.Hlo = a·B`: the two `ε` bounds `R.eps ≤ 1/500` and `1/L ≤ R.eps` (for any `L ≥ 500·N`), and
the shrink's divisibility, quotient and floor at stride `a`. This file states them once.

## Main result
* `stride_shrink_facts` — the five facts.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **The stride shrink's facts at a pinned regime.** If `R.eps = ε = 1/(500·k)` with
`0 < k ≤ N`, `500·N ≤ L`, `R.Hlo = a·B` and `0 < a`, then `R.eps ≤ 1/500`, `1/L ≤ R.eps`,
`a ∣ R.a·R.Hlo`, `R.a·R.Hlo / a = R.a·B` and `B ≤ R.a·R.Hlo / a`. -/
theorem stride_shrink_facts (R : ChowlaRegime) {ε : ℚ} {k N : ℕ} {L : ℚ} {a B : ℕ}
    (hReps : R.eps = ε) (hεeq : ε = 1 / (500 * (k : ℚ))) (hk : 0 < k) (hkN : k ≤ N)
    (hL : 500 * (N : ℚ) ≤ L) (hHlo : R.Hlo = a * B) (ha : 0 < a) :
    R.eps ≤ 1 / 500 ∧ 1 / L ≤ R.eps ∧ a ∣ R.a * R.Hlo ∧ R.a * R.Hlo / a = R.a * B ∧
      B ≤ R.a * R.Hlo / a := by
  have hkQ : ((k : ℕ) : ℚ) ≤ N := by exact_mod_cast hkN
  have hkQ1 : (1 : ℚ) ≤ ((k : ℕ) : ℚ) := by exact_mod_cast hk
  have heps500 : R.eps ≤ 1 / 500 := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hepsL : 1 / L ≤ R.eps := by
    rw [hReps, hεeq]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hdiv : a ∣ R.a * R.Hlo := by
    rw [hHlo]
    exact (dvd_mul_right a B).mul_left R.a
  have hquot : R.a * R.Hlo / a = R.a * B := by
    rw [hHlo, show R.a * (a * B) = a * (R.a * B) by ring]
    exact Nat.mul_div_cancel_left _ ha
  have hBle : B ≤ R.a * R.Hlo / a := by
    rw [hquot]
    exact Nat.le_mul_of_pos_left _ R.ha
  exact ⟨heps500, hepsL, hdiv, hquot, hBle⟩

end Salt.MR
