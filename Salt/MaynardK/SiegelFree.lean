/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Gaps636
import Salt.MaynardK.Gaps600
import Salt.SW.StandoffCert

/-!
# Bounded gaps from a Siegel standoff

`gaps_le_636` and `gaps_le_600` reach Siegel's theorem by two roads, both through
Siegel–Walfisz: the long-window prime number theorem `windowPNT_holds` (through
`Salt.Chen.psiTot_pnt`) and level `1/2`, `hasLevel_half_of_siegelWalfisz siegelWalfisz_holds`.
Both roads now take the Siegel–Walfisz statement as a hypothesis (`windowPNT_holds_of_SW`,
`psiTot_pnt_of_SW`), and the landed level interface `gaps_le_of_level_of_slack` takes the two
results as hypotheses.

This module feeds both roads `Salt.SW.siegelWalfisz_of_standoff`. That proof assumes
`NoSiegelZerosAt c`: for every `q > 1`, no primitive quadratic character `χ ≠ 1` mod `q` has a
real `L`-zero `β < 1` above `1 − c / log q`. It does not use Siegel's theorem, as
`Salt.SW.StandoffCert` certifies.

## What this does and does not say

* The conclusions are those of `gaps_le_636` and `gaps_le_600`, under one hypothesis.
* The certificate below is about the PROOF TERM: the constant closure of each `_of_standoff`
  theorem contains none of `siegel_theorem`, `siegel_L_one_exceptional` and `L1_lower_siegel`,
  while those of `gaps_le_636` and `gaps_le_600` contain `siegel_theorem` (the positive
  controls). `#print axioms` cannot see this.
* The gap bounds are the landed ones. Nothing here makes a constant explicit, and the
  mathematics is classical.
-/

namespace Salt.MaynardK

open Salt.Maynard

/-- **Bounded gaps, at most 636, from a Siegel standoff.** If, for one fixed `c > 0`, no
primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, there are infinitely many pairs of distinct primes at distance at most 636, by
a proof that does not use Siegel's theorem (certified below). -/
theorem gaps_le_636_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-636 : ℤ) 636 :=
  gaps_le_636_of_level (windowPNT_holds_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS))
    (Salt.BV.hasLevel_half_of_siegelWalfisz (Salt.SW.siegelWalfisz_of_standoff hc hS))

/-- **Bounded gaps, at most 600, from a Siegel standoff.** The same, with Engelsma's tuple
(Maynard's Theorem 1.3 bound), under the same hypothesis. -/
theorem gaps_le_600_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-600 : ℤ) 600 :=
  @gaps_le_of_level_of_slack engelsmaTuple (@winSlackM105_ev engelsmaTuple hSeq_engelsma_le_743)
    hSeq_engelsma_le_743 600 hSeq_engelsma_diam_le_600
    (windowPNT_holds_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS))
    (Salt.BV.hasLevel_half_of_siegelWalfisz (Salt.SW.siegelWalfisz_of_standoff hc hS))

end Salt.MaynardK

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.MaynardK.gaps_le_636 Salt.SW.siegel_theorem
#assert_reaches Salt.MaynardK.gaps_le_600 Salt.SW.siegel_theorem
#assert_reaches Salt.Maynard.windowPNT_holds Salt.SW.siegel_theorem

-- The `_of_SW` roads reach none of the three: Siegel–Walfisz is their hypothesis.
#assert_not_reaches Salt.Maynard.windowPNT_holds_of_SW Salt.SW.siegel_theorem
#assert_not_reaches Salt.Chen.psiTot_pnt_of_SW Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.MaynardK.gaps_le_636_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MaynardK.gaps_le_636_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MaynardK.gaps_le_636_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MaynardK.gaps_le_600_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MaynardK.gaps_le_600_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MaynardK.gaps_le_600_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.MaynardK.gaps_le_636_of_standoff 3 Salt.MaynardK.gaps_le_636
#assert_conclusion_is Salt.MaynardK.gaps_le_600_of_standoff 3 Salt.MaynardK.gaps_le_600
#assert_conclusion_is Salt.Maynard.windowPNT_holds_of_SW 1 Salt.Maynard.windowPNT_holds
#assert_conclusion_is Salt.Chen.psiTot_pnt_of_SW 1 Salt.Chen.psiTot_pnt

#closure_report Salt.MaynardK.gaps_le_636_of_standoff
#closure_report Salt.MaynardK.gaps_le_600_of_standoff
