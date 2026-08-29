/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The entropy-deficit cap (SPINE-BUDGET rung R4)

The final analytic clearance of the Liouville entropy-decrement budget: the
per-`H` gap between the prime-window log-cardinality `log P_H` and the residue
datum's entropy `H[Y_H]` never exceeds `log 2`.

This is Tao arXiv:1509.05422v2 (3.9) in its consumed direction.  The residue
near-uniformity bound `entropy_residueWindow_ge`
(`ResidueUniform.lean`) reads

  `log P_H − log(1 + u) ≤ H[Y_H]`,   `u := 8·P_H²·ω/x`,

and the regime's per-`H` (3.9) headroom `pH_headroom_at` (`Regime.lean`) gives
`8·P_H²·ω ≤ x`, i.e. `u ≤ 1`.  Monotonicity of `log` on `1 + u ≤ 2` closes
`log(1 + u) ≤ log 2`, and the deficit inherits the cap.

Per the SPINE-BUDGET freeze (cover point CC2) ONLY the `≤ log 2` direction is
consumed downstream; the `≥ 0` companion is deliberately NOT proved here — it is
not a phantom obligation of the budget.
-/
import Salt.Entropy.Chowla.ResidueUniform
import Salt.Entropy.Chowla.Regime

open MeasureTheory Real Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### The entropy deficit cap -/

/-- **The entropy-deficit cap (SPINE-BUDGET R4).**  For every admissible `H ≤ H₊`
    of the regime `R`, the prime-window log-cardinality exceeds the residue
    entropy by at most `log 2`:

      `log P_H − H[Y_H] ≤ log 2`.

    Route: `entropy_residueWindow_ge` (the honest (3.9) deficit bound) gives
    `log P_H − log(1 + u) ≤ H[Y_H]` with `u := 8·P_H²·ω/x`; the regime headroom
    `pH_headroom_at` gives `8·P_H²·ω ≤ x`, hence `u ≤ 1`; `log` monotone on
    `0 < 1 + u ≤ 2` closes `log(1 + u) ≤ log 2`.  Only the `≤ log 2` direction is
    consumed (freeze CC2); the `≥ 0` companion is intentionally omitted. -/
theorem deficit_le_log_two (R : ChowlaRegime) {H : ℕ} (hhi : H ≤ R.Hhi) :
    Real.log (PH R.eps H) - H[residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ Real.log 2 := by
  -- the honest (3.9) deficit bound: `log P_H − log(1 + u) ≤ H[Y_H]`
  have hent := entropy_residueWindow_ge R.eps H R.hx R.hω R.hωx
  -- the regime's per-`H` headroom field: `8·P_H²·ω ≤ x`
  have hhead := pH_headroom_at R hhi
  have hxpos : (0 : ℝ) < (R.x : ℝ) := by
    have hx2 : 0 < R.x := by have := R.hx; omega
    exact_mod_cast hx2
  -- name the correction term `u := 8·P_H²·ω/x` (folds into `hent`)
  set u : ℝ := 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) / (R.x : ℝ) with hu
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hxpos]; exact hhead
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  -- `log` monotone on `0 < 1 + u ≤ 2` (only the `≤` direction; freeze CC2)
  have hlog : Real.log (1 + u) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  -- assemble: `log P_H − H[Y_H] ≤ log(1 + u) ≤ log 2`
  linarith [hent, hlog]

end Salt.Entropy.Chowla
