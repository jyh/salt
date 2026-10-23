/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorStandoff
import Salt.TwinBar.SevenEighthsStandoff
import Salt.SW.StandoffCert

/-!
# Theorem 4.25 from the 7/8 statement, through the standoff (O13)

`logChowla2_epsFamily_flatDoor_floor_of_standoff` (`FlatDoorStandoff.lean`) is Theorem 4.25's
conclusion under `NoSiegelZerosAt cS`.  `Salt.TwinBar.noSiegelZerosAt_of_sevenEighths`
(`SevenEighthsStandoff.lean`) gives that standoff at `cS = (log 2)/8` from
`Salt.TwinBar.DirichletSevenEighths`.  This module composes the two, in the form the 7/8
compositions of three primes, bounded gaps and both Chen theorems take there.

## What this does and does not say

* The theorem below is an implication from `DirichletSevenEighths`, by a proof term that does not
  use Siegel's theorem: the certificate at the foot says it reaches none of
  `Salt.SW.siegel_theorem` · `Salt.SW.siegel_L_one_exceptional` · `Salt.SW.L1_lower_siegel`.
* ⚠ LIMIT, beside the verdict: it is CONDITIONAL on `DirichletSevenEighths`, this repository's
  restatement of the 7/8 statement as cited (see `SevenEighthsClaim.lean` for how far that
  restatement is checked against the original); it is a reach certificate, not a claim that the
  result is effective, and the constants below the standoff are those of the landed proofs.
* Nothing here bears on twin primes, and nothing here claims priority.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

private theorem log_two_div_eight_pos' : 0 < Real.log 2 / 8 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- **Theorem 4.25 from the 7/8 statement, without Siegel's theorem.** -/
theorem logChowla2_epsFamily_flatDoor_floor_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (extraFloor : ℕ) :
    ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω :=
  logChowla2_epsFamily_flatDoor_floor_of_standoff log_two_div_eight_pos'
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) ε hε0 hε extraFloor

end Salt.MR

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+: Theorem 4.25 as landed reaches Siegel's theorem.
#assert_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_holds Salt.SW.siegel_theorem

-- THE CERTIFICATE: the composition reaches none of the three Siegel names.
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_sevenEighths
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_sevenEighths
  Salt.SW.L1_lower_siegel

-- TOKEN CHECK: the conclusion is the landed statement (one binder, the hypothesis).
#assert_conclusion_is Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_sevenEighths 1
  Salt.MR.logChowla2_epsFamily_flatDoor_floor_holds
