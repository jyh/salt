/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Lower-bound Möbius plumbing for `BoundingSieve` (blueprint `p0`, node B1)

The exact **lower-bound dual** of mathlib's upper Selberg-sieve plumbing
(`Mathlib/NumberTheory/SelbergSieve.lean`): `IsUpperMoebius`,
`siftedSum_le_sum_of_upperMoebius`, `siftedSum_le_mainSum_errSum_of_upperMoebius`.

A sequence `μ⁻` is *lower Möbius* when `∑_{d∣n} μ⁻(d) ≤ [n = 1]` for all `n`
(the reversed inequality of `IsUpperMoebius`).  Such coefficients yield a **lower**
bound on the sifted sum, with the error term entering with a **flipped sign**
(`≥ mainSum − errSum`).  The proofs mirror the mathlib originals line-by-line, with
`≤` reversed and `le_abs_self` replaced by `neg_abs_le`.

Stated over `BoundingSieve` exactly as mathlib states its upper counterpart — this
material is mathlib-worthy and belongs upstream in `namespace BoundingSieve`.
-/

open Finset Nat ArithmeticFunction

namespace Salt.BrunLower

open BoundingSieve

variable {s : BoundingSieve}

/-- A sequence of coefficients `μ⁻` is **lower Möbius** if `μ⁻ * ζ ≤ μ * ζ`, i.e.
`∑_{d∣n} μ⁻(d) ≤ [n = 1]` for every `n`.  The reversed inequality of mathlib's
`IsUpperMoebius`; such coefficients yield a lower bound on the sifted sum. -/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (∑ d ∈ n.divisors, muMinus d) ≤ (if n = 1 then 1 else 0)

/-- Lower-bound dual of `siftedSum_le_sum_of_upperMoebius`: lower-Möbius coefficients
underestimate the sifted sum. -/
theorem siftedSum_ge_sum_of_lowerMoebius (muMinus : ℕ → ℝ) (h : IsLowerMoebius muMinus) :
    ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d ≤ s.siftedSum := by
  have hμ : ∀ n, (∑ d ∈ n.divisors, muMinus d) ≤ (if n = 1 then 1 else 0) := h
  calc ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d
      = ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
          if d ∣ n then s.weights n * muMinus d else 0 := ?caseC
    _ = ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := ?caseB
    _ ≤ s.siftedSum := ?caseA
  case caseA =>
    rw [siftedSum_eq_sum_support_mul_ite]
    gcongr with n
    exact hμ (Nat.gcd s.prodPrimes n)
  case caseB =>
    symm
    simp_rw [mul_sum, ← sum_filter]
    congr with n
    congr 1
    rw [← Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
    ext x; simp +contextual [Nat.dvd_gcd_iff]
  case caseC =>
    symm
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]

/-- Lower-bound dual of `siftedSum_le_mainSum_errSum_of_upperMoebius`, with the error
term entering with a **flipped sign**: `totalMass · mainSum − errSum ≤ siftedSum`. -/
theorem siftedSum_ge_mainSum_errSum_of_lowerMoebius (muMinus : ℕ → ℝ)
    (h : IsLowerMoebius muMinus) :
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤ s.siftedSum := by
  have hkey : -s.errSum muMinus ≤ ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    calc -s.errSum muMinus
        = ∑ d ∈ divisors s.prodPrimes, -(|muMinus d| * |s.rem d|) := by
          rw [errSum, Finset.sum_neg_distrib]
      _ ≤ ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
          apply Finset.sum_le_sum
          intro d _
          rw [← abs_mul]
          exact neg_abs_le _
  have hsplit : ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d
      = s.totalMass * s.mainSum muMinus + ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [mainSum, mul_sum, ← Finset.sum_add_distrib]
    congr 1 with d
    rw [rem]; ring
  have hge := siftedSum_ge_sum_of_lowerMoebius muMinus h (s := s)
  rw [hsplit] at hge
  linarith

end Salt.BrunLower
