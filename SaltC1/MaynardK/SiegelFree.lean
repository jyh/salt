/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Gaps270
import Salt.MaynardK.SiegelFree
import Salt.TwinBar.SevenEighthsStandoff

/-!
# Bounded gaps at most 270 from a Siegel standoff (O13)

`gaps_le_270` reaches Siegel's theorem by the two roads `Salt.MaynardK.SiegelFree` names for
`gaps_le_636` and `gaps_le_600`: `windowPNT_holds` and `hasLevel_half_of_siegelWalfisz
siegelWalfisz_holds`, both discharged inside `gaps_le_of_slack` (`Capstone54`). The landed
interface form `gaps_le_of_level_of_slack` takes the two results as hypotheses, and this module
feeds it the `_of_SW` roads at `Salt.SW.siegelWalfisz_of_standoff`, in `gaps_le_600_of_standoff`'s
form. The 7/8 instance takes `Salt.TwinBar.noSiegelZerosAt_of_sevenEighths` at `c = (log 2)/8`.

## What this does and does not say

* The conclusion is that of `gaps_le_270`, under one hypothesis (`NoSiegelZerosAt c`, or the
  repository's restatement `DirichletSevenEighths`, which is a HYPOTHESIS here).
* The certificate below is about the PROOF TERM: the constant closure of each theorem contains
  none of `siegel_theorem`, `siegel_L_one_exceptional` and `L1_lower_siegel`, while that of
  `gaps_le_270` contains `siegel_theorem` (the positive control). `#print axioms` cannot see this.
* The gap bound is the landed one. Nothing here makes a constant explicit, and the mathematics
  is classical. Nothing here bears on twin primes.
-/

namespace SaltC1.MaynardK

open Salt.Maynard

/-- **Bounded gaps, at most 270, from a Siegel standoff.** If, for one fixed `c > 0`, no
primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, there are infinitely many pairs of distinct primes at distance at most 270, by
a proof that does not use Siegel's theorem (certified below). -/
theorem gaps_le_270_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-270 : ℤ) 270 :=
  @gaps_le_of_level_of_slack polymath54Tuple (@winSlackM54_ev polymath54Tuple hSeq_polymath_le_270)
    hSeq_polymath_le_270 270 hSeq_polymath_diam_le_270
    (windowPNT_holds_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS))
    (Salt.BV.hasLevel_half_of_siegelWalfisz (Salt.SW.siegelWalfisz_of_standoff hc hS))

private theorem log_two_div_eight_pos : 0 < Real.log 2 / 8 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- Bounded gaps at most 270 from the 7/8 statement, without Siegel's theorem. -/
theorem gaps_le_270_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-270 : ℤ) 270 :=
  gaps_le_270_of_standoff log_two_div_eight_pos (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h)

end SaltC1.MaynardK

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches SaltC1.MaynardK.gaps_le_270 Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches SaltC1.MaynardK.gaps_le_270_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statement.
#assert_conclusion_is SaltC1.MaynardK.gaps_le_270_of_standoff 3 SaltC1.MaynardK.gaps_le_270
#assert_conclusion_is SaltC1.MaynardK.gaps_le_270_of_sevenEighths 1 SaltC1.MaynardK.gaps_le_270
