/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# M4 — error term bounds (blueprint milestone)

Bounds on the error terms in the Selberg sieve.
-/

/-- Number of distinct prime divisors of `n`. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- N4.1: For squarefree `d`, the prime-power bound `6^ω(d) ≤ d³`.
For squarefree `d`, `d = ∏ p ∈ d.primeFactors, p` (unique factorization with
each prime to the first power). Since every prime `p ≥ 2` satisfies
`6 ≤ p^3` (as `2^3 = 8 ≥ 6`), we get
`6^ω(d) = ∏ p ∈ d.primeFactors, 6 ≤ ∏ p ∈ d.primeFactors, p^3 = d^3`.
-/
theorem six_pow_omega_le_d_cubed {d : ℕ} (hd : Squarefree d) : 6 ^ omega d ≤ d ^ 3 := by
  unfold omega
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd
  calc 6 ^ d.primeFactors.card
      = ∏ _p ∈ d.primeFactors, (6 : ℕ) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ d.primeFactors, p ^ 3 := by
        apply Finset.prod_le_prod (fun _ _ => by omega)
        intro p hp
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        nlinarith [hp2, sq_nonneg p]
    _ = (∏ p ∈ d.primeFactors, p) ^ 3 := by rw [← Finset.prod_pow]
    _ = d ^ 3 := by rw [hprod]
