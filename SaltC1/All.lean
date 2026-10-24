/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.All
import SaltC1.MaynardK.Bridge54
import SaltC1.MaynardK.All
import SaltC1.MaynardK.Tuple54
import SaltC1.MaynardK.Gaps270
import SaltC1.MaynardK.SiegelFree
import Salt.Tactic.AuditAxioms

/-!
# `SaltC1` — bounded gaps with gap at most 270

The `k = 54` certificate (`Cert54`), its bridge to the Lean side (`Bridge54`), the k = 54 layer of
Maynard's argument (`MaynardK`), the diameter-270 tuple (`Tuple54`) and the gap theorem
(`Gaps270`): H₁ ≤ 270 via DHL[54, 2] — Polymath 8b (arXiv:1407.4897v4) Thm 3.9(vii) (M₅₄ > 4.00238,
p. 14) with the Bombieri–Vinogradov theorem (p. 14), and H(54) = 270 (Figure 3, p. 75).
Nothing here bears on twin primes.
-/

-- Build-time axiom audit: a stray axiom (including `sorryAx`) on the headline path fails the
-- build here.
open Salt.Tactic in
#audit_axioms SaltC1.MaynardK.maynard_54_tuple270 SaltC1.MaynardK.gaps_le_270

-- From a Siegel standoff and from the 7/8 statement (SiegelFree), by proof terms that do not use
-- Siegel's theorem (O13).
open Salt.Tactic in
#audit_axioms SaltC1.MaynardK.gaps_le_270_of_standoff SaltC1.MaynardK.gaps_le_270_of_sevenEighths
