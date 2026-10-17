/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ExpSum.Basic
import Salt.LS.Parseval

/-!
# Three primes: the singular integral

These are lemmas L9 and L10 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Step 4a).

On a major arc, `S(a/q + β)` is approximated by `(μ(q)/φ(q)) v(β)`, where

  `v(β) = Σ_{1 ≤ n ≤ N} e(nβ)`

is the same exponential sum with every weight replaced by `1`. When the approximation is cubed and
integrated over the arc, what is left after the arithmetic is the **singular integral**
`∫ v(β)³ e(−Nβ) dβ` over `|β| ≤ δ`, with `δ = P/N` the arc's half-width.

* **Over the whole circle it is a count.** Expanding the cube and integrating term by term,
  orthogonality `∫₀¹ e(mβ) dβ = [m = 0]` keeps exactly the triples with `n₁ + n₂ + n₃ = N`, so
  `∫₀¹ v(β)³ e(−Nβ) dβ = #{(n₁, n₂, n₃) : nᵢ ≥ 1, n₁ + n₂ + n₃ = N} = C(N − 1, 2) = (N−1)(N−2)/2`.
  A reader can check this by hand: it is the number of ways to cut `N` stones into three non-empty
  heaps.
* **Truncating it to the arc costs `O(1/δ²)`.** `v` is a geometric sum, so `|v(β)| ≤ 1/(2|β|)` for
  `0 < |β| ≤ 1/2`, and then `∫_{δ ≤ |β| ≤ 1/2} |v|³ ≤ 1/(8δ²)`. With `δ = P/N` this is
  `O(N²/P²)`, smaller than the main term `N²/2` by the factor `P²`.

The bridge lemma `LS_e_eq_eR` says that the two names this corpus uses for `x ↦ exp(2πix)` (one
from the large-sieve files, one from the exponential-sum files) are the same function, so the
orthogonality proved for one serves the other.
-/

namespace Salt.ThreePrimes

open Salt.ExpSum (eR norm_eR)

/-- The two spellings of `e(x) = exp(2πix)` in this corpus, `Salt.LS.e` and `Salt.ExpSum.eR`, are
the same function. -/
theorem LS_e_eq_eR (x : ℝ) : Salt.LS.e x = eR x := rfl

/-- **The unweighted exponential sum** `v(β) = Σ_{1 ≤ n ≤ N} e(nβ)`. -/
noncomputable def expSumOne (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, eR ((n : ℝ) * β)

/-- **The trivial bound** `|v(β)| ≤ N`: `N` phases of modulus one. -/
theorem norm_expSumOne_le (N : ℕ) (β : ℝ) : ‖expSumOne N β‖ ≤ N := by
  sorry

/-- **The geometric-sum bound** `|v(β)| ≤ 1/(2|β|)` for `0 < |β| ≤ 1/2`. The sum is
`e(β)(e(Nβ) − 1)/(e(β) − 1)`, its numerator has modulus at most `2`, and
`|e(β) − 1| = 2|sin(πβ)| ≥ 4|β|` on that range. -/
theorem norm_expSumOne_le_inv (N : ℕ) {β : ℝ} (hβ : 0 < |β|) (hβ' : |β| ≤ 1 / 2) :
    ‖expSumOne N β‖ ≤ 1 / (2 * |β|) := by
  sorry

/-- **The singular integral over the whole circle is a count:** `∫₀¹ v(β)³ e(−Nβ) dβ = C(N − 1, 2)`,
the number of ordered triples of positive integers summing to `N`. -/
theorem integral_expSumOne_cube (N : ℕ) :
    (∫ β in (0 : ℝ)..1, expSumOne N β ^ 3 * eR (-(N : ℝ) * β)) = ((N - 1).choose 2 : ℂ) := by
  sorry

/-- **The singular integral truncated to a major arc:** over `|β| ≤ δ` it differs from
`C(N − 1, 2)` by at most `1/(4δ²)`. -/
theorem integral_expSumOne_cube_trunc (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ‖(∫ β in (-δ)..δ, expSumOne N β ^ 3 * eR (-(N : ℝ) * β)) - ((N - 1).choose 2 : ℂ)‖
      ≤ 1 / (4 * δ ^ 2) := by
  sorry

end Salt.ThreePrimes
