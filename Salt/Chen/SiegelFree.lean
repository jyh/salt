/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenTheorem
import Salt.SW.StandoffCert

/-!
# Chen's theorem from a Siegel standoff

`chen_headline` reaches Siegel's theorem through Siegel–Walfisz on two roads: Bombieri–Vinogradov
at saving `11` (`a12_hBV_A1`, `a12_hBV_A2`, through `psi_BV_of_siegelWalfisz'`) and the prime
number theorem with a rate (`psiTot_pnt`, through `lambda_mass_lower` and the count keystone),
plus the conductor descent (`psiAP_sub_psiTot_bound`). Every declaration on those roads now takes
the Siegel–Walfisz statement as a hypothesis (the `_of_SW` forms), and each unconditional name
instantiates it at `Salt.SW.siegelWalfisz_holds` with its statement unchanged.

This module instantiates the chain at `Salt.SW.siegelWalfisz_of_standoff`. That proof assumes
`NoSiegelZerosAt c`: for every `q > 1`, no primitive quadratic character `χ ≠ 1` mod `q` has a
real `L`-zero `β < 1` above `1 − c / log q`. It does not use Siegel's theorem, as
`Salt.SW.StandoffCert` certifies.

## What this does and does not say

* The conclusion is that of `chen_headline`, under one hypothesis.
* The certificate below is about the PROOF TERM: the constant closure of
  `chen_headline_of_standoff` contains none of `siegel_theorem`, `siegel_L_one_exceptional` and
  `L1_lower_siegel`, while that of `chen_headline` contains `siegel_theorem`. `#print axioms`
  cannot see this.
* Nothing here makes a constant explicit, and the mathematics is classical.
-/

namespace Salt.Chen

/-- **Chen's theorem from a Siegel standoff.** If, for one fixed `c > 0`, no primitive
quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above `1 − c / log q`,
there are infinitely many primes `p` with `p + 2` a prime or a product of two primes, by a proof
that does not use Siegel's theorem (certified below). -/
theorem chen_headline_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS)

end Salt.Chen

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see), one per road: the headline, the
-- Bombieri–Vinogradov row, the prime-number-theorem row and the conductor descent.
#assert_reaches Salt.Chen.chen_headline Salt.SW.siegel_theorem
#assert_reaches Salt.Chen.a12_hBV_A1 Salt.SW.siegel_theorem
#assert_reaches Salt.Chen.lambda_mass_lower Salt.SW.siegel_theorem
#assert_reaches Salt.Chen.psiAP_sub_psiTot_bound Salt.SW.siegel_theorem

-- The `_of_SW` chain reaches none of the three: Siegel–Walfisz is its hypothesis.
#assert_not_reaches Salt.Chen.chen_headline_of_SW Salt.SW.siegel_theorem
#assert_not_reaches Salt.Chen.chen_headline_of_SW Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Chen.chen_headline_of_SW Salt.SW.L1_lower_siegel

-- THE CERTIFICATE.
#assert_not_reaches Salt.Chen.chen_headline_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Chen.chen_headline_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Chen.chen_headline_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.Chen.chen_headline_of_standoff 3 Salt.Chen.chen_headline
#assert_conclusion_is Salt.Chen.chen_headline_of_SW 1 Salt.Chen.chen_headline

#closure_report Salt.Chen.chen_headline_of_standoff
