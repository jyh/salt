/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithRho

/-!
# Two bounds on the strata residual (`StrataBounds`)

`strataResidual H = 1 + log (arcDen 12 H)` and `RSanDoorRho ρ H = ρ / strataResidual H ^ 2`.
The door assemblies prove the same two facts inline at each gate: `1 ≤ strataResidual H` once
`1 ≤ arcDen 12 H`, and then `RSanDoorRho ρ H ≤ rSanWitness H` once `ρ ≤ 1` (the tactics
catalogue's candidate #2, 28 sites in 14 files). This module states them once.
-/

namespace Salt.MR

/-- `1 ≤ strataResidual H` whenever `1 ≤ arcDen 12 H`: the logarithm is then nonnegative.
The `H`-weighted form is `one_le_strataResidualH`. -/
theorem one_le_strataResidual {H : ℕ} (h : (1 : ℝ) ≤ arcDen 12 H) : 1 ≤ strataResidual H := by
  have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg h
  unfold strataResidual
  linarith

/-- `RSanDoorRho ρ H ≤ rSanWitness H` when `ρ ≤ 1` and `1 ≤ strataResidual H`: the quotient
`ρ / strataResidual H ^ 2` is at most `1`, and `rSanWitness H = max 1 (4 · arcDen 12 H)`. -/
theorem RSanDoorRho_le_rSanWitness {ρ : ℝ} (hρ : ρ ≤ 1) {H : ℕ} (hSR : 1 ≤ strataResidual H) :
    RSanDoorRho ρ H ≤ rSanWitness H := by
  have hsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
  have h1 : RSanDoorRho ρ H ≤ 1 := by
    unfold RSanDoorRho
    rw [div_le_one (by nlinarith)]
    linarith
  exact le_trans h1 (le_max_left _ _)

end Salt.MR
