/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4NonCoprime

/-!
# The arc regime's two weaker forms (`ArcRegimeWeaken`)

The door consumers receive the arc hypothesis `128 · arcDen 12 H ^ 3 ≤ H` on the regime's
range `R.Hlo ≤ H ≤ R.Hhi` and re-derive the same two weaker forms from it at every site:
`8 · arcDen 12 H ^ 3 ≤ H` and `128 · arcDen 12 H ^ 2 ≤ H` (the tactics catalogue's arc
block). Both follow from `1 ≤ arcDen 12 H` on the regime. This module states them once.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- From the arc hypothesis `128 · arcDen 12 H ^ 3 ≤ H` on the regime:
`8 · arcDen 12 H ^ 3 ≤ H`. -/
theorem arcDen_cube_le_of_arc3 {R : ChowlaRegime}
    (harc3 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
  intro H hlo hhi
  have h1 := harc3 H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  nlinarith [h1, harc1]

/-- From the arc hypothesis `128 · arcDen 12 H ^ 3 ≤ H` on the regime:
`128 · arcDen 12 H ^ 2 ≤ H`. -/
theorem arcDen_sq_le_of_arc3 {R : ChowlaRegime}
    (harc3 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
  intro H hlo hhi
  have h1 := harc3 H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  nlinarith [h1, harc1]

end Salt.MR
