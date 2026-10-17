/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude

Proofs in this file are adapted from gersh/ternary-goldbach-lean,
commit 27df23af6a712895f22204d0d81102baa74f0ebe,
Math/Problems/TernaryGoldbach/CircleMethodDecomposition/Core.lean and
Math/Problems/TernaryGoldbach/Core/Lemmas.lean,
Copyright (c) 2026 Gershon Bialer, released under Apache 2.0.
-/
import Mathlib
import Salt.ThreePrimes.Ramanujan

/-!
# Three primes: the singular series

These are lemmas L11–L13 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 4
and 5).

When the major arcs are cubed and integrated, the arc at `a/q` contributes
`(μ(q)/φ(q))³ e(−Na/q)` times the singular integral. Summing over the `a` coprime to `q` turns the
phases into the Ramanujan sum `c_q(N)`, and `μ(q)³ = μ(q)`. Summing over `q` gives the **singular
series**

  `𝔖(N) = Σ_{q ≥ 1} μ(q) c_q(N) / φ(q)³`,

the arithmetic density of representations of `N` as a sum of three primes. This file shows what
the main term needs from it.

* **It converges absolutely.** Its `q`-th term is at most `μ(q)²/φ(q)²` in size, by the trivial
  bound `|c_q(N)| ≤ φ(q)`, and `Σ_q μ(q)²/φ(q)²` converges.
* **It is an Euler product.** The term is multiplicative in `q`: `μ` and `φ` are, and so is `c_q(N)`
  (`ramanujanSum_mul_of_coprime`). It also vanishes unless `q` is squarefree. So the series is a
  product over primes of `1 + μ(p) c_p(N)/φ(p)³`, and with `c_p(N) = p − 1` or `−1` that factor is
  `1 − 1/(p−1)²` if `p ∣ N` and `1 + 1/(p−1)³` if `p ∤ N`.
* **It vanishes for even `N` and is bounded below for odd `N`.** At `p = 2` the factor is `0` when
  `2 ∣ N`, which is the parity obstruction: three odd primes have an odd sum. When `N` is odd that
  factor is `2`, and every other factor is at least `1 − 1/(p−1)² ≥ 3/4`. Their product converges,
  so it is at least a constant `c₀ > 0` that does not depend on `N`. This is the only place in the
  proof that uses `N` odd.

The tail `Σ_{q > P}` that completes the truncated series (plan, Step 4b) is bounded where it is
used, with the major arcs.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction

/-- **The `q`-th term of the singular series**, `μ(q) c_q(N) / φ(q)³`. -/
noncomputable def singularTerm (N q : ℕ) : ℂ :=
  ((moebius q : ℂ) / (Nat.totient q : ℂ) ^ 3) * ramanujanSum q N

/-- **The singular series** `𝔖(N) = Σ_q μ(q) c_q(N) / φ(q)³`. -/
noncomputable def singularSeries (N : ℕ) : ℂ :=
  ∑' q : ℕ, singularTerm N q

/-- **The local factor at a prime `p`**: `1 − 1/(p−1)²` if `p ∣ N`, and `1 + 1/(p−1)³` otherwise. At
`p = 2` it is `0` for even `N` and `2` for odd `N`. -/
noncomputable def localFactor (N p : ℕ) : ℝ :=
  if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- **The Ramanujan sum is multiplicative in the modulus:** `c_{q₁q₂}(n) = c_{q₁}(n) c_{q₂}(n)` when
`gcd(q₁, q₂) = 1`. By the Chinese remainder theorem, a residue coprime to `q₁q₂` is a pair of
residues coprime to `q₁` and to `q₂`, and the phase `e(na/(q₁q₂))` factors accordingly. -/
theorem ramanujanSum_mul_of_coprime {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  sorry

/-- **The size of a term:** `|μ(q) c_q(N)/φ(q)³| ≤ μ(q)²/φ(q)²`, from `|c_q(N)| ≤ φ(q)` and
`|μ(q)| = μ(q)²`. (Both sides are `0` at `q = 0`.) -/
theorem norm_singularTerm_le (N q : ℕ) :
    ‖singularTerm N q‖ ≤ ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 := by
  sorry

/-- **The singular series converges absolutely.** -/
theorem summable_norm_singularTerm (N : ℕ) : Summable (fun q : ℕ => ‖singularTerm N q‖) := by
  sorry

/-- **The Euler product:** `𝔖(N) = Π_p (local factor at p)`. -/
theorem singularSeries_eq_tprod (N : ℕ) :
    singularSeries N = ((∏' p : Nat.Primes, localFactor N p : ℝ) : ℂ) := by
  sorry

/-- **For even `N` the singular series vanishes**, through its factor at `p = 2`. -/
theorem singularSeries_eq_zero_of_even {N : ℕ} (hN : Even N) : singularSeries N = 0 := by
  sorry

/-- **For odd `N` the singular series is bounded below** by a constant `c₀ > 0` independent of
`N`. -/
theorem singularSeries_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ N : ℕ, Odd N → c₀ ≤ ∏' p : Nat.Primes, localFactor N p := by
  sorry

end Salt.ThreePrimes
