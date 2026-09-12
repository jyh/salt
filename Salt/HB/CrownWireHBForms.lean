/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.CrownWireHB
import Salt.HB.Lemma5Bilinear

/-!
# The HB wire IS the forms wire at the twin pair

One theorem: `hbDataHB` (`Salt/HB/CrownWireHB.lean` §1) and `hbDataForms … HBForms.twin`
(`Salt/HB/Lemma5Bilinear.lean`) are the same `HBSieveData`, by `rfl`.

**WHY IT HAS ITS OWN MODULE.**  The two objects live on opposite sides of an import boundary
that is deliberate.  `Salt.HB.Lemma5Bilinear` is not in the crown's import cone and does not
belong there — the crown does not need HB's bilinear machinery to state its wire — so the wire
in §1 is spelled out inline rather than defined as an instance of the general forms wire.  That
inline spelling is a CHOICE, and a choice of that kind should have a theorem behind it rather
than a comment.  This module is the only place where both objects are in scope, so it is where
the identity is recorded; importing it costs the crown nothing, because nothing on the crown
path imports it.

Nothing here bears on twin primes.
-/

namespace Salt.HB

open Salt.SW Salt.BrunLower

variable {q : ℕ}

/-- **W-a.4 — the HB wire is Wave B's forms wire at the twin pair.**  `hbDataHB` and
`Salt.N7.hbDataForms … Salt.N7.HBForms.twin` are the same `HBSieveData`, definitionally:
`HBForms.l₁ twin k = 4·k + 1`, `l₂ twin k = 4·k + 3`, and `hbFormsWindow twin q x` is the
`(l, q) = 1` filter of `(x, 2x]`.  Class **A**, cap 15.  Consumer: Wave C-2 (its bilinear
machinery is stated at `hbDataForms`; `N7Exit` is stated at `hbDataHB`). -/
theorem hbDataHB_eq_hbDataForms_twin (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) :
    hbDataHB χ hsq hz x = Salt.N7.hbDataForms χ hsq hz Salt.N7.HBForms.twin x := rfl

end Salt.HB
