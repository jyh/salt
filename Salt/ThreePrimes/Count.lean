/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.MajorArc

/-!
# Three primes: counting with weights

These are lemmas L1–L3 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 0 and 1).

The proof counts representations `N = n₁ + n₂ + n₃` with the weight `Λ(n₁)Λ(n₂)Λ(n₃)`:

  `R(N) = Σ_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃)`.

* **Counting becomes an integral.** Expanding `S(α)³` and integrating against `e(−Nα)`,
  orthogonality keeps exactly the triples summing to `N`, so `R(N) = ∫₀¹ S(α)³ e(−Nα) dα`. This is
  the identity the whole proof evaluates. It is the same computation as the singular integral's
  count, with the weights `Λ` in place of `1`.
* **The weights cost little, and they convert back to primes.** A triple of primes carries weight
  `log p₁ · log p₂ · log p₃ ≤ (log N)³`. Every other triple with nonzero weight has a proper prime
  power `p^k` (`k ≥ 2`) in some slot. Those powers weigh `ψ(N) − θ(N) ≤ 2√N log N` in total, and the
  other two slots weigh at most a constant times `N (log N)²`. So

    `R(N) ≤ (log N)³ · r(N) + C N^{3/2} (log N)³`,

  where `r(N)` counts the ordered triples of primes summing to `N`. Since the main term is of size
  `N²`, a lower bound `R(N) ≫ N²` forces `r(N) > 0`.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction
open Salt.ExpSum (eR norm_eR)

/-- **The weighted count** `R(N) = Σ_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃)`, over `1 ≤ nᵢ ≤ N`. -/
noncomputable def weightedCount (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
    if a + b + c = N then vonMangoldt a * vonMangoldt b * vonMangoldt c else 0

/-- **The prime count** `r(N)`: the number of ordered triples of primes `(p₁, p₂, p₃)` with
`p₁ + p₂ + p₃ = N`. -/
noncomputable def primeTripleCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun t =>
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = N)).card

/-- **Counting becomes an integral:** `R(N) = ∫₀¹ S(α)³ e(−Nα) dα`. -/
theorem weightedCount_eq_integral (N : ℕ) :
    ((weightedCount N : ℝ) : ℂ)
      = ∫ α in (0 : ℝ)..1, primeExpSum N α ^ 3 * eR (-(N : ℝ) * α) := by
  sorry

/-- **From weights back to primes:** there is a `C` with
`R(N) ≤ (log N)³ · r(N) + C N^{3/2} (log N)³` for every `N ≥ 2`. -/
theorem weightedCount_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      weightedCount N
        ≤ Real.log N ^ 3 * primeTripleCount N + C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3 := by
  sorry

/-- **A large weighted count forces three primes:** if `R(N) > C N^{3/2} (log N)³`, with `C` the
constant of `weightedCount_le`, then `N` is a sum of three primes. -/
theorem exists_three_primes_of_weightedCount {C : ℝ}
    (hC : ∀ N : ℕ, 2 ≤ N →
      weightedCount N
        ≤ Real.log N ^ 3 * primeTripleCount N + C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3)
    {N : ℕ} (hN : 2 ≤ N)
    (hR : C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3 < weightedCount N) :
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  sorry

end Salt.ThreePrimes
