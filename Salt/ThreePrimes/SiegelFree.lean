/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ThreePrimes.Assembly
import Salt.SW.StandoffCert

/-!
# Three primes from a Siegel standoff

`three_primes` (`Assembly.lean`) uses one input about primes in progressions: Siegel–Walfisz,
called once, in `psiAP_error_uniform_of_SW` (`MajorArc.lean`). Every step from that call to
`three_primes` now takes the Siegel–Walfisz statement as a hypothesis (the `_of_SW` forms), and
the unconditional names instantiate it at `Salt.SW.siegelWalfisz_holds`, whose proof uses Siegel's
theorem.

This module instantiates it at `Salt.SW.siegelWalfisz_of_standoff` instead. That proof assumes
`NoSiegelZerosAt c`: for every `q > 1`, no primitive quadratic character `χ ≠ 1` mod `q` has a
real `L`-zero `β < 1` above `1 − c / log q`. It does not use Siegel's theorem, as
`Salt.SW.StandoffCert` certifies.

## What this does and does not say

* It is the same three-primes conclusion as `three_primes`, under one hypothesis.
* The certificate below is about the PROOF TERM: the transitive constant closure of
  `three_primes_of_standoff` contains none of `siegel_theorem`, `siegel_L_one_exceptional` and
  `L1_lower_siegel`, while that of `three_primes` contains `siegel_theorem` (the positive
  control). `#print axioms` cannot see this; both print the same three axioms.
* `N₀` is still a Lean `∃`, not a numeral. Removing Siegel's theorem removes the one input
  whose constant is ineffective in the classical sense; it does not make the other constants
  explicit, and this module does not claim it does.
* The mathematics is classical. Classically, a standoff with an EXPLICIT constant makes
  Vinogradov's theorem effective; `NoSiegelZerosAt c` with an arbitrary `c`, as here, does not, and
  this development computes no constant.
-/

namespace Salt.ThreePrimes

/-- **Vinogradov's three-primes theorem from a Siegel standoff.** If, for one fixed `c > 0`,
no primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, every sufficiently large odd number is a sum of three primes, by a proof that
does not use Siegel's theorem (certified below). -/
theorem three_primes_of_standoff {c : ℝ} (hc : 0 < c) (hS : Salt.SW.NoSiegelZerosAt c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N :=
  three_primes_of_SW (Salt.SW.siegelWalfisz_of_standoff hc hS)

end Salt.ThreePrimes

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see): the unconditional theorem and its
-- first `_of_SW` consumer reach Siegel's theorem.
#assert_reaches Salt.ThreePrimes.three_primes Salt.SW.siegel_theorem
#assert_reaches Salt.ThreePrimes.psiAP_error_uniform Salt.SW.siegel_theorem

-- The `_of_SW` chain itself reaches none of the three: Siegel–Walfisz is its hypothesis.
#assert_not_reaches Salt.ThreePrimes.three_primes_of_SW Salt.SW.siegel_theorem
#assert_not_reaches Salt.ThreePrimes.three_primes_of_SW Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.ThreePrimes.three_primes_of_SW Salt.SW.L1_lower_siegel

-- THE CERTIFICATE.
#assert_not_reaches Salt.ThreePrimes.three_primes_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.ThreePrimes.three_primes_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.ThreePrimes.three_primes_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.ThreePrimes.three_primes_of_standoff 3 Salt.ThreePrimes.three_primes
#assert_conclusion_is Salt.ThreePrimes.three_primes_of_SW 1 Salt.ThreePrimes.three_primes

#closure_report Salt.ThreePrimes.three_primes_of_standoff
