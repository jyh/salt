/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SevenEighthsStandoff
import Salt.SW.GapsStandoff

/-!
# Bounded gaps from the 7/8 statement, through the standoff (O13)

`noSiegelZerosAt_of_sevenEighths` (`SevenEighthsStandoff.lean`) is the standoff at
`c = (log 2)/8` from `DirichletSevenEighths`; here it is fed to
`Salt.SW.bounded_gaps_of_standoff` (`GapsStandoff.lean`).

## What this does and does not say

* The theorem is an implication from `DirichletSevenEighths`, by a proof term that does not use
  Siegel's theorem (certified below).
* `DirichletSevenEighths` is this repository's restatement, and a HYPOTHESIS here; see
  `SevenEighthsClaim.lean` for what it is and is not.
* The gap `C` is still a Lean `∃`. The mathematics is classical, and nothing here claims priority.
-/

namespace Salt.TwinBar

/-- `0 < log 2 / 8`: the positivity of the standoff constant `c = (log 2)/8` that
`bounded_gaps_of_sevenEighths` hands to `Salt.SW.bounded_gaps_of_standoff`. -/
private theorem log_two_div_eight_pos' : 0 < Real.log 2 / 8 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- Bounded gaps between primes from the 7/8 statement, without Siegel's theorem. -/
theorem bounded_gaps_of_sevenEighths (h : DirichletSevenEighths) :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  Salt.SW.bounded_gaps_of_standoff log_two_div_eight_pos' (noSiegelZerosAt_of_sevenEighths h)

end Salt.TwinBar

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+: the unconditional form reaches Siegel's theorem.
#assert_reaches Salt.SW.bounded_gaps_unconditional Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.TwinBar.bounded_gaps_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.bounded_gaps_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.bounded_gaps_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECK: the conclusion is the landed statement (one binder, the hypothesis).
#assert_conclusion_is Salt.TwinBar.bounded_gaps_of_sevenEighths 1 Salt.SW.bounded_gaps_unconditional
