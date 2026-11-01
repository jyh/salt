/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The flat head's four floors under a regime's `Hlo`

The flat-head exports mint two floors, `Hopq = max (max H₀red H₀D3) H₀xi` and
`F = max Hopq (budgetFloorFlat ε β A)`, choose a regime whose `Hlo` lies above `max F e`, and then
read off, each time by hand, that `Hlo` lies above `F`, `H₀xi`, the budget floor and
`max H₀red H₀D3`. This file states those four facts once.

The twelve call sites that took them inline are `HloExportFlat`, `HloExportFlatH` (two),
`FlatDoorEpsChain`, `FlatDoorEpsRung2`, `FlatDoorStandoff`, `S16Compose`, `S16ComposeLH`,
`S16Uniform`, `V6SiegelFree`, `V7SiegelFree` and `XThread`; there they are used as `hFlo`,
`hxiHlo`, `hbudHlo` and `hredHlo`. The lemma is over naturals and imports nothing beyond
Mathlib, so the `Salt.MR` sites and the `Salt.Entropy` sites can both read it.

## Main results
* `flatHeadFloors_facts` — the four floors under `Hlo`.
-/

namespace Salt.Entropy.Chowla

/-- **The flat head's floors.** For `Hopq = max (max r d) x`, `F = max Hopq b` and
`max F e ≤ h`: `F ≤ h`, `x ≤ h`, `b ≤ h` and `max r d ≤ h`. -/
theorem flatHeadFloors_facts {Hopq F r d x b e h : ℕ} (hOpqdef : Hopq = max (max r d) x)
    (hFdef : F = max Hopq b) (hRHlo : max F e ≤ h) :
    F ≤ h ∧ x ≤ h ∧ b ≤ h ∧ max r d ≤ h := by
  subst hOpqdef hFdef
  simp only [max_le_iff] at hRHlo ⊢
  omega

end Salt.Entropy.Chowla
