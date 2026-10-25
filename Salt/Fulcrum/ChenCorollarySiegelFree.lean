/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Fulcrum.ChenCorollary
import Salt.Chen.SiegelFree
import Salt.TwinBar.SevenEighthsStandoff
import Salt.SW.StandoffCert

/-!
# Chen's almost-prime corollary from a Siegel standoff

`chen_omega_prod_le_three` (`ChenCorollary.lean`) is `chen_headline` plus arithmetic: `Ω(p) = 1`
for a prime `p`, and `p + 2` a prime or a product of two primes gives `Ω(p + 2) ≤ 2`. Its proof
reaches Siegel's theorem only through `chen_headline` (census addendum 7,
`docs/exploration/o13-rung4-census-2026-10-24.md`). This module runs the same arithmetic on
`chen_headline_of_standoff` (`Salt/Chen/SiegelFree.lean`) and on its 7/8 instance
`chen_headline_of_sevenEighths` (`Salt/TwinBar/SevenEighthsStandoff.lean`).

## What this does and does not say

* The conclusion is that of `chen_omega_prod_le_three`, under the standoff `NoSiegelZerosAt c`
  for one `c > 0`, or under the 7/8 statement `DirichletSevenEighths`.
* The certificate below is about the PROOF TERM: its constant closure contains none of
  `siegel_theorem`, `siegel_L_one_exceptional` and `L1_lower_siegel`.
* `chen_omega_prod_le_three` itself is unchanged; the arithmetic step is restated here as
  `omega_le_three_of_chen`, so the merged proof is not edited.
* Nothing here makes a constant explicit, and the mathematics is classical.
-/

open ArithmeticFunction

namespace Salt.Fulcrum

/-- The arithmetic step of `chen_omega_prod_le_three`, from any proof of Chen's set being
infinite: a prime `p` with `p + 2` a prime or a product of two primes has `Ω(p·(p+2)) ≤ 3`, so
the target set contains Chen's set. -/
theorem omega_le_three_of_chen
    (h : {p : ℕ | p.Prime ∧ Salt.Chen.IsP2 2 (p + 2)}.Infinite) :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite := by
  apply h.mono
  intro p hp
  obtain ⟨hpp, hP2⟩ := hp
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hp20 : p + 2 ≠ 0 := by omega
  have hΩp : cardFactors p = 1 := cardFactors_apply_prime hpp
  have hΩp2 : cardFactors (p + 2) ≤ 2 := by
    rcases hP2 with hpr | ⟨a, b, ha, hb, hab, -, -⟩
    · have h1 : cardFactors (p + 2) = 1 := cardFactors_apply_prime hpr
      omega
    · have h2 : cardFactors (p + 2) = 2 := by
        rw [hab, cardFactors_mul ha.ne_zero hb.ne_zero,
          cardFactors_apply_prime ha, cardFactors_apply_prime hb]
      omega
  refine ⟨hpp, ?_⟩
  rw [cardFactors_mul hp0 hp20, hΩp]
  omega

/-- **`Ω(p·(p+2)) ≤ 3` infinitely often, from a Siegel standoff.** If, for one fixed `c > 0`, no
primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, there are infinitely many primes `p` with `Ω(p·(p+2)) ≤ 3`, by a proof that does
not use Siegel's theorem (certified below). -/
theorem chen_omega_prod_le_three_of_standoff {c : ℝ} (hc : 0 < c)
    (hS : Salt.SW.NoSiegelZerosAt c) :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite :=
  omega_le_three_of_chen (Salt.Chen.chen_headline_of_standoff hc hS)

/-- `Ω(p·(p+2)) ≤ 3` infinitely often from the 7/8 statement, without Siegel's theorem. -/
theorem chen_omega_prod_le_three_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths) :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite :=
  omega_le_three_of_chen (Salt.TwinBar.chen_headline_of_sevenEighths h)

end Salt.Fulcrum

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+: the unconditional corollary reaches Siegel's theorem (through `chen_headline`).
#assert_reaches Salt.Fulcrum.chen_omega_prod_le_three Salt.SW.siegel_theorem

-- The arithmetic step reaches none of the three: Chen's set is its hypothesis.
#assert_not_reaches Salt.Fulcrum.omega_le_three_of_chen Salt.SW.siegel_theorem
#assert_not_reaches Salt.Fulcrum.omega_le_three_of_chen Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Fulcrum.omega_le_three_of_chen Salt.SW.L1_lower_siegel

-- THE CERTIFICATES.
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths
  Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statement.
#assert_conclusion_is Salt.Fulcrum.chen_omega_prod_le_three_of_standoff 3
  Salt.Fulcrum.chen_omega_prod_le_three
#assert_conclusion_is Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths 1
  Salt.Fulcrum.chen_omega_prod_le_three

#closure_report Salt.Fulcrum.chen_omega_prod_le_three_of_standoff
