/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.ChenGoldbach
import Salt.SW.StandoffCert

/-!
# Chen's Goldbach-form theorem from a Siegel standoff

`chen_goldbach` reaches Siegel's theorem through Siegel–Walfisz on the same roads as
`chen_headline`: Bombieri–Vinogradov at saving `11` (`gold_a12_hBV_A1`, `gold_a12_hBV_A2`), the
prime number theorem with a rate (`psiTot_pnt`, through `lambda_mass_lower` and
`gold_hcount_seam`) and the conductor descent (`psiAP_sub_psiTot_bound`). Each declaration on
those roads now takes the Siegel–Walfisz statement as a hypothesis (the `_of_SW` forms).

This module instantiates the chain at `Salt.SW.siegelWalfisz_of_standoff`, under
`NoSiegelZerosAt c`: for every `q > 1`, no primitive quadratic character `χ ≠ 1` mod `q` has a
real `L`-zero `β < 1` above `1 − c / log q`.

## What this does and does not say

* The conclusion is that of `chen_goldbach`, under one hypothesis.
* The certificate below is about the PROOF TERM: the constant closure of
  `chen_goldbach_of_standoff` contains none of `siegel_theorem`, `siegel_L_one_exceptional` and
  `L1_lower_siegel`, while that of `chen_goldbach` contains `siegel_theorem`.
* `N₀` is still a Lean `∃`, not a numeral, and the mathematics is classical.
-/

open Salt.Chen

namespace Salt.Goldbach

/-- **Chen's Goldbach-form theorem from a Siegel standoff.** If, for one fixed `c > 0`, no
primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, every sufficiently large even `N` is `p + q` with `p` prime and `q` a prime or
a product of two primes, by a proof that does not use Siegel's theorem (certified below). -/
theorem chen_goldbach_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ IsP2 2 q :=
  chen_goldbach_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS)

end Salt.Goldbach

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see), one per road.
#assert_reaches Salt.Goldbach.chen_goldbach Salt.SW.siegel_theorem
#assert_reaches Salt.Goldbach.gold_a12_hBV_A1 Salt.SW.siegel_theorem
#assert_reaches Salt.Goldbach.gold_hcount_seam Salt.SW.siegel_theorem

-- The `_of_SW` chain reaches none of the three.
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_SW Salt.SW.siegel_theorem
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_SW Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_SW Salt.SW.L1_lower_siegel

-- THE CERTIFICATE.
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Goldbach.chen_goldbach_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.Goldbach.chen_goldbach_of_standoff 3 Salt.Goldbach.chen_goldbach
#assert_conclusion_is Salt.Goldbach.chen_goldbach_of_SW 1 Salt.Goldbach.chen_goldbach

#closure_report Salt.Goldbach.chen_goldbach_of_standoff
