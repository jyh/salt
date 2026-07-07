/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# M3 — main term, Mertens-free (blueprint milestone)

Self-contained analytic facts feeding the `G(z) ≥ c(log z)²` bound. Facts that
depend on the sieve's `nu`/`selbergTerms` (not yet built — see N2.6/N3.2) are
deferred; only the divisor-count/prime-factor arithmetic that stands on its
own is proved here.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Omega

/-- N3.3 (part 1): `τ(m) ≤ 2^Ω(m)` — the divisor-count function is bounded by
`2` to the power of the number of prime factors counted with multiplicity.
For `m = ∏ p^a`, `τ(m) = ∏(a+1) ≤ ∏2^a = 2^Ω(m)` since `a+1 ≤ 2^a` for all
`a`. Part 2 (`ν*(m) ≥ τ(m)/m` for odd `m`) needs `ν*` from N3.2, which needs
the sieve instance (N2.6) — not restated here. -/
theorem card_divisors_le_two_pow_cardFactors {m : ℕ} (hm : m ≠ 0) :
    m.divisors.card ≤ 2 ^ Ω m := by
  rw [Nat.card_divisors hm, cardFactors_eq_sum_factorization, Finsupp.sum,
    ← Nat.support_factorization]
  calc m.factorization.support.prod (fun p => m.factorization p + 1)
      ≤ m.factorization.support.prod (fun p => 2 ^ m.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => by omega)
        intro p _
        exact Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ = 2 ^ (∑ p ∈ m.factorization.support, m.factorization p) := by
        rw [← Finset.prod_pow_eq_pow_sum]
