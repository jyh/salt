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
catalogue's candidate #2, 28 sites in 14 files). This module states them once, and states the
whole gate they serve (`gate6_of_j0_floor`).
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

/-- **⟦gate 6⟧ ⟦G2⟧ at a `j₀`-floor**, stated once. The door assemblies discharge this gate binder
with the same proof at 28 sites: `1 ≤ arcDen 12 H` on the regime (`one_le_arcDen_of_regime`), the
two bounds above, and `g2_of_j0_floor` at the floor `hj0`. `j₀` is implicit, so one lemma serves
both floors in use (`doorRowFloor M` and `doorRowFloorL M`). -/
theorem gate6_of_j0_floor (R : Salt.Entropy.Chowla.ChowlaRegime) {ρ : ℝ} (hρ1 : ρ ≤ 1) {j₀ : ℕ}
    (hj0 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ (j₀ : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * RSanDoorRho ρ H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀ := by
  intro H hlo hhi
  have hSR1 := one_le_strataResidual (one_le_arcDen_of_regime (R := R) hlo)
  have hRSle := RSanDoorRho_le_rSanWitness hρ1 hSR1
  have hG := g2_of_j0_floor H (hj0 H hlo hhi)
  linarith

end Salt.MR
