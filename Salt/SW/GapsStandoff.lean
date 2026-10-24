/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.StandoffCert

/-!
# Bounded gaps from a Siegel standoff (O13)

`bounded_gaps_unconditional` (`Gate.lean`) is `Salt.BV.bounded_gaps_of_siegelWalfisz` fed
`siegelWalfisz_holds`, and `siegelWalfisz_holds` reaches `siegel_theorem`. This module feeds the
same interface `siegelWalfisz_of_standoff` instead. That proof assumes `NoSiegelZerosAt c`: for
every `q > 1`, no primitive quadratic character `χ ≠ 1` mod `q` has a real `L`-zero `β < 1`
above `1 − c / log q`. It does not use Siegel's theorem, as `Salt.SW.StandoffCert` certifies.

## What this does and does not say

* The conclusion is that of `bounded_gaps_unconditional`, under one hypothesis.
* The certificate below is about the PROOF TERM: the constant closure of
  `bounded_gaps_of_standoff` contains none of `siegel_theorem`, `siegel_L_one_exceptional` and
  `L1_lower_siegel`, while that of `bounded_gaps_unconditional` contains `siegel_theorem` (the
  positive control). `#print axioms` cannot see this.
* The gap `C` is still a Lean `∃`, as in the landed theorem. The mathematics is classical.
-/

namespace Salt.SW

/-- **Bounded gaps from a Siegel standoff.** If, for one fixed `c > 0`, no primitive quadratic
character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above `1 − c / log q`, then some `C`
bounds infinitely many gaps between distinct primes, by a proof that does not use Siegel's
theorem (certified below). -/
theorem bounded_gaps_of_standoff {c : ℝ} (hc : 0 < c) (hS : NoSiegelZerosAt c) :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  Salt.BV.bounded_gaps_of_siegelWalfisz (siegelWalfisz_of_standoff hc hS)

end Salt.SW

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.SW.bounded_gaps_unconditional Salt.SW.siegel_theorem

-- The interface reaches none of the three: Siegel–Walfisz is its hypothesis.
#assert_not_reaches Salt.BV.bounded_gaps_of_siegelWalfisz Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.SW.bounded_gaps_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.SW.bounded_gaps_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.SW.bounded_gaps_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECK: the conclusion is the landed statement.
#assert_conclusion_is Salt.SW.bounded_gaps_of_standoff 3 Salt.SW.bounded_gaps_unconditional
