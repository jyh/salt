/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.PsiToPi
import Salt.Maynard.LevelConsume

/-!
# V6 — the headline composition (conditional form)

`bounded_gaps_of_siegelWalfisz_of_bridge`: bounded prime gaps from the
`SiegelWalfisz` gate plus the `PsiToPiTransfer` bridge, by instantiating the
landed Maynard chain (`bounded_gaps_from_level`, Rung 4b — built for exactly
this day). When node V4-core discharges `PsiToPiTransfer`, the final
`bounded_gaps_of_siegelWalfisz (hSW : SiegelWalfisz)` is this same
composition with the bridge argument gone.
-/

namespace Salt.BV

/-- **Bounded prime gaps, conditional on Siegel–Walfisz + the ψ→π bridge.**
The Bombieri–Vinogradov chain (`psi_BV_of_siegelWalfisz'` →
`hasLevel_half_of_siegelWalfisz_of_bridge`) feeding the landed Maynard
consumer. -/
theorem bounded_gaps_of_siegelWalfisz_of_bridge (hSW : SiegelWalfisz)
    (hT : PsiToPiTransfer) :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  Salt.Maynard.bounded_gaps_from_level
    (hasLevel_half_of_siegelWalfisz_of_bridge hSW hT)

end Salt.BV
