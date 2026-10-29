/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Data.Nat.Notation

/-!
# The regime-floor block (`RegimeFloors`)

The capstone consumers open a regime `R` under the window hypothesis
`hU : max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor`, with the fields `hU1 : U1floor ≤ R.Hlo`
and `hRcap : R.Hlo ≤ max Hcap U1floor`, and then re-derive the base pin `R.Hlo = U1floor` and the
two regime floors `loglogFloor50 ≤ R.Hlo`, `arcFloor36 ≤ R.Hlo` in ten lines (the tactics
catalogue's candidate #4, 38 sites in 22 files). This module states that block once. It is generic
in the two floors, so it needs neither definition.
-/

namespace Salt.MR

/-- From `hU : max Hcap (max a b) ≤ U1`, `hlo : U1 ≤ Hlo` and `hcap : Hlo ≤ max Hcap U1`:
`Hlo = U1` (the cap is `U1`, since `Hcap ≤ U1`), and both floors `b ≤ Hlo`, `a ≤ Hlo`.
At a site `a = arcFloor36`, `b = loglogFloor50`, `Hlo = R.Hlo`, `U1 = U1floor`. -/
theorem regime_floors_of_U1 {Hcap U1 Hlo a b : ℕ} (hU : max Hcap (max a b) ≤ U1)
    (hlo : U1 ≤ Hlo) (hcap : Hlo ≤ max Hcap U1) : Hlo = U1 ∧ b ≤ Hlo ∧ a ≤ Hlo := by
  omega

end Salt.MR
