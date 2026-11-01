/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Fulcrum.ChenCorollary
import Salt.Chen.SiegelFree
import Salt.TwinBar.SevenEighthsStandoff

/-!
# Chen's almost-prime corollary from a Siegel standoff

`chen_omega_prod_le_three` (`Salt/Fulcrum/ChenCorollary.lean`) is `chen_headline` plus counting:
a prime `p` with `p + 2` a `P₂` has `Ω(p·(p+2)) ≤ 3`. It reaches Siegel's theorem through
`chen_headline` (O13 census addendum 7, the flagship paper's citations). This module runs the
same counting on `Salt.Chen.chen_headline_of_standoff`, and composes it with the 7/8 statement
(`chen_omega_prod_le_three_of_sevenEighths`).

## What this does and does not say

* The conclusion is that of `chen_omega_prod_le_three`, under one hypothesis: `NoSiegelZerosAt c`
  for one fixed `c > 0` (`Salt.SW.NoSiegelZerosAt`).
* The certificate below is about the PROOF TERM: its constant closure contains none of
  `siegel_theorem`, `siegel_L_one_exceptional` and `L1_lower_siegel` (`Salt.SW.StandoffCert`).
* ⚠️ Nothing here bears on twin primes: `Ω(p·(p+2)) ≤ 3` is a Chen by-product, as the
  unconditional file already says.
-/

open ArithmeticFunction Salt.Chen

namespace Salt.Fulcrum

/-- **Chen's almost-prime corollary from a Siegel standoff.** If, for one fixed `c > 0`, no
primitive quadratic character `χ ≠ 1` mod `q > 1` has a real `L`-zero `β < 1` above
`1 − c / log q`, there are infinitely many primes `p` with `Ω(p·(p+2)) ≤ 3`. The counting is
`chen_omega_prod_le_three`'s, run on `chen_headline_of_standoff` (`hc`, `hS`). -/
theorem chen_omega_prod_le_three_of_standoff {c : ℝ} (hc : 0 < c)
    (hS : Salt.SW.NoSiegelZerosAt c) :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite := by
  apply (chen_headline_of_standoff hc hS).mono
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

/-- **Chen's almost-prime corollary from the 7/8 statement**, without Siegel's theorem: the
standoff form at `c = (log 2)/8`, which `noSiegelZerosAt_of_sevenEighths` supplies. -/
theorem chen_omega_prod_le_three_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths) :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite :=
  chen_omega_prod_le_three_of_standoff (div_pos (Real.log_pos one_lt_two) (by norm_num))
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h)

end Salt.Fulcrum

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.Fulcrum.chen_omega_prod_le_three Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECK: the conclusion is the landed statement.
#assert_conclusion_is Salt.Fulcrum.chen_omega_prod_le_three_of_standoff 3
  Salt.Fulcrum.chen_omega_prod_le_three
#assert_conclusion_is Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths 1
  Salt.Fulcrum.chen_omega_prod_le_three

#closure_report Salt.Fulcrum.chen_omega_prod_le_three_of_standoff

#print axioms Salt.Fulcrum.chen_omega_prod_le_three_of_standoff
#print axioms Salt.Fulcrum.chen_omega_prod_le_three_of_sevenEighths
