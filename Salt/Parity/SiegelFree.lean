/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Parity.Instances
import Salt.Chen.SiegelFree
import Salt.Goldbach.SiegelFree

/-!
# The two Chen parity instances from a Siegel standoff

`parityInv_chen_headline` and `parityInv_chen_second` (`Salt/Parity/Instances.lean`) apply
`parityInv_of_closed` to `chen_headline` and `chen_goldbach`, so they reach Siegel's theorem
through those two (O13 census addendum 7, the flagship paper's citations). This module applies
`parityInv_of_closed` to their standoff twins, `chen_headline_of_standoff` and
`chen_goldbach_of_standoff`.

## What this does and does not say

* Each conclusion is that of its unconditional instance, under one hypothesis:
  `NoSiegelZerosAt c` for one fixed `c > 0` (`Salt.SW.NoSiegelZerosAt`).
* The certificate below is about the PROOF TERMS: their constant closures contain none of
  `siegel_theorem`, `siegel_L_one_exceptional` and `L1_lower_siegel` (`Salt.SW.StandoffCert`).
* As with the unconditional instances, `parityInv_of_closed` carries no arithmetic content: a
  closed proposition is parity-invariant. These exist so that every Lean name the paper cites
  that reaches `siegel_theorem` has a standoff form. ⚠️ Nothing here bears on twin primes.
-/

/-- `parityInv_chen_headline` from a Siegel standoff: `parityInv_of_closed` applied to
`chen_headline_of_standoff` (`hc`, `hS`). -/
theorem parityInv_chen_headline_of_standoff {c : ℝ} (hc : 0 < c)
    (hS : Salt.SW.NoSiegelZerosAt c) (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => {p : ℕ | p.Prime ∧ Salt.Chen.IsP2 2 (p + 2)}.Infinite) :=
  Salt.Parity.parityInv_of_closed θ A₀ (Salt.Chen.chen_headline_of_standoff hc hS)

/-- `parityInv_chen_second` from a Siegel standoff: `parityInv_of_closed` applied to
`chen_goldbach_of_standoff` (`hc`, `hS`). -/
theorem parityInv_chen_second_of_standoff {c : ℝ} (hc : 0 < c)
    (hS : Salt.SW.NoSiegelZerosAt c) (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀ (fun _ => ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ Salt.Chen.IsP2 2 q) :=
  Salt.Parity.parityInv_of_closed θ A₀ (Salt.Goldbach.chen_goldbach_of_standoff hc hS)

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches parityInv_chen_headline Salt.SW.siegel_theorem
#assert_reaches parityInv_chen_second Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches parityInv_chen_headline_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches parityInv_chen_headline_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches parityInv_chen_headline_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches parityInv_chen_second_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches parityInv_chen_second_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches parityInv_chen_second_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: after `c hc hS`, each type is the landed instance's (`∀ θ A₀, …`).
#assert_conclusion_is parityInv_chen_headline_of_standoff 3 parityInv_chen_headline
#assert_conclusion_is parityInv_chen_second_of_standoff 3 parityInv_chen_second

#print axioms parityInv_chen_headline_of_standoff
#print axioms parityInv_chen_second_of_standoff
