/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SevenEighthsClaim
import Salt.SW.StandoffGate
import Salt.ThreePrimes.SiegelFree
import Salt.MaynardK.SiegelFree
import Salt.Chen.SiegelFree
import Salt.Goldbach.SiegelFree

/-!
# The 7/8 statement, restated, through the standoff

`DirichletSevenEighths` (`SevenEighthsClaim.lean`) is this repository's restatement, over its own
mathlib, of the statement OpenAI proves in Lean over a newer mathlib. It is a HYPOTHESIS here.
`noSiegelZeros_of_sevenEighths` derives `NoSiegelZeros`, with `(log 2)/8` as the witness inside its
proof. This module states that constant: `noSiegelZerosAt_of_sevenEighths` is the standoff at
`c = (log 2)/8`, and each `_of_standoff` theorem of the Siegel-free modules is then instantiated
at it.

## What this does and does not say

* Each theorem below is an implication from `DirichletSevenEighths`, by a proof term that does
  not use Siegel's theorem (each `_of_standoff` theorem carries that certificate).
* `DirichletSevenEighths` is NOT OpenAI's theorem: the two mathlib versions agree on the
  definitions the statement names directly, and below them their equivalence is not checked.
* The standoff constant `(log 2)/8` is explicit; `N₀` and the other constants in these proofs are
  not computed.
* The mathematics is classical, and nothing here claims priority.
-/

open Complex DirichletCharacter

namespace Salt.TwinBar

/-- **The 7/8 statement gives the standoff at `c = (log 2)/8`.** A real zero `β < 1` of a
nontrivial character has `β ≤ 7/8` by the hypothesis, and `7/8 ≤ 1 − (log 2)/(8 log q)` for
`q ≥ 2`. -/
theorem noSiegelZerosAt_of_sevenEighths (h : DirichletSevenEighths) :
    Salt.SW.NoSiegelZerosAt (Real.log 2 / 8) := by
  intro q _ χ hq _ _ hχ β hβ _
  have h78 : β ≤ 7 / 8 := by
    by_contra hlt
    exact h q χ (s := (β : ℂ)) (by simpa using not_le.mp hlt) (fun h1 => hχ h1.1) hβ
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hlogqpos : 0 < Real.log q := lt_of_lt_of_le hlog2 hlogq
  have hc : Real.log 2 / 8 / Real.log q ≤ 1 / 8 := by
    rw [div_le_iff₀ hlogqpos]
    linarith
  linarith

/-- `0 < log 2 / 8`: the standoff constant of `noSiegelZerosAt_of_sevenEighths` is positive. -/
private theorem log_two_div_eight_pos : 0 < Real.log 2 / 8 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- Vinogradov's three-primes theorem from the 7/8 statement, without Siegel's theorem. -/
theorem three_primes_of_sevenEighths (h : DirichletSevenEighths) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N :=
  Salt.ThreePrimes.three_primes_of_standoff log_two_div_eight_pos
    (noSiegelZerosAt_of_sevenEighths h)

/-- Bounded gaps at most 636 from the 7/8 statement, without Siegel's theorem. -/
theorem gaps_le_636_of_sevenEighths (h : DirichletSevenEighths) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-636 : ℤ) 636 :=
  Salt.MaynardK.gaps_le_636_of_standoff log_two_div_eight_pos
    (noSiegelZerosAt_of_sevenEighths h)

/-- Bounded gaps at most 600 from the 7/8 statement, without Siegel's theorem. -/
theorem gaps_le_600_of_sevenEighths (h : DirichletSevenEighths) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-600 : ℤ) 600 :=
  Salt.MaynardK.gaps_le_600_of_standoff log_two_div_eight_pos
    (noSiegelZerosAt_of_sevenEighths h)

/-- Chen's theorem from the 7/8 statement, without Siegel's theorem. -/
theorem chen_headline_of_sevenEighths (h : DirichletSevenEighths) :
    {p : ℕ | p.Prime ∧ Salt.Chen.IsP2 2 (p + 2)}.Infinite :=
  Salt.Chen.chen_headline_of_standoff log_two_div_eight_pos (noSiegelZerosAt_of_sevenEighths h)

/-- Chen's Goldbach-form theorem from the 7/8 statement, without Siegel's theorem. -/
theorem chen_goldbach_of_sevenEighths (h : DirichletSevenEighths) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ Salt.Chen.IsP2 2 q :=
  Salt.Goldbach.chen_goldbach_of_standoff log_two_div_eight_pos
    (noSiegelZerosAt_of_sevenEighths h)

end Salt.TwinBar

open Salt.SW.StandoffCert

#assert_targets_exist

-- P+: the unconditional forms reach Siegel's theorem.
#assert_reaches Salt.ThreePrimes.three_primes Salt.SW.siegel_theorem
#assert_reaches Salt.Chen.chen_headline Salt.SW.siegel_theorem

-- THE CERTIFICATE: the standoff lemma and each composition, against all three names.
#assert_not_reaches Salt.TwinBar.noSiegelZerosAt_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.noSiegelZerosAt_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.noSiegelZerosAt_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.TwinBar.three_primes_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.three_primes_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.three_primes_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.TwinBar.gaps_le_636_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.gaps_le_636_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.gaps_le_636_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.TwinBar.gaps_le_600_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.gaps_le_600_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.gaps_le_600_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.TwinBar.chen_headline_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.chen_headline_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.chen_headline_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.TwinBar.chen_goldbach_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.TwinBar.chen_goldbach_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.TwinBar.chen_goldbach_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: each conclusion is the landed statement (one binder, the hypothesis).
#assert_conclusion_is Salt.TwinBar.three_primes_of_sevenEighths 1 Salt.ThreePrimes.three_primes
#assert_conclusion_is Salt.TwinBar.gaps_le_636_of_sevenEighths 1 Salt.MaynardK.gaps_le_636
#assert_conclusion_is Salt.TwinBar.gaps_le_600_of_sevenEighths 1 Salt.MaynardK.gaps_le_600
#assert_conclusion_is Salt.TwinBar.chen_headline_of_sevenEighths 1 Salt.Chen.chen_headline
#assert_conclusion_is Salt.TwinBar.chen_goldbach_of_sevenEighths 1 Salt.Goldbach.chen_goldbach
