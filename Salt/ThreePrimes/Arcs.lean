/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.MinorArc

/-!
# Three primes: the major and minor arcs

These are lemma L4 and the minor-arc half of Step 6 of the three-primes plan
(`docs/plans/three-primes-PLAN.md`, Steps 2 and 6a).

Fix `P ≥ 1` and the half-width `δ = P/N`. **The major arc** at a fraction `a/q`, with `q ≤ P`,
`1 ≤ a ≤ q` and `gcd(a, q) = 1`, is the interval `[a/q − δ, a/q + δ]`. We work on the period window
`(δ, 1 + δ]` instead of `[0, 1)`. The arc at `1/1` then sits inside the window, at `1`, rather than
wrapping around `0`, and every other arc sits inside it too once `N ≥ 2P²`.

* **The arcs are disjoint** once `N > 2P³`. Two distinct fractions with denominators at most `P`
  differ by at least `1/(qq′) ≥ 1/P²`, which exceeds `2δ = 2P/N`. This is what lets the major-arc
  integral be computed one arc at a time, each with its own approximation.
* **Off the arcs, `S` is small.** For `α` in the window and on no arc, Dirichlet's theorem with
  `Q = ⌊N/P⌋` gives a fraction `a/q` in lowest terms, `q ≤ Q`, with `|α − a/q| ≤ 1/(q(Q + 1))`. That
  is within `δ` of `a/q`, and `1 ≤ a ≤ q` because `α` lies in the window. So if `q ≤ P`, then `α` is
  on the arc at `a/q`, which it is not. Hence `P < q ≤ N/P`, and also `|α − a/q| ≤ 1/q²`.
  Vinogradov's estimate (`norm_primeExpSum_le_minor`) then gives `N/√q ≤ N/√P` and `√(Nq) ≤ N/√P`:

    `|S(α)| ≤ K (2N/√P + N^{7/8}) (log N)³`.
-/

namespace Salt.ThreePrimes

/-- **The major arc** at `a/q`: the interval `[a/q − P/N, a/q + P/N]`. -/
def majorArc (N P q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - (P : ℝ) / N) ((a : ℝ) / q + (P : ℝ) / N)

/-- **The arcs' labels** `(q, a)`: `1 ≤ q ≤ P`, `1 ≤ a ≤ q`, `gcd(a, q) = 1`. -/
def arcIndex (P : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P) ×ˢ (Finset.Icc 1 P)).filter (fun x => x.2 ≤ x.1 ∧ Nat.Coprime x.2 x.1)

/-- **The major arcs are disjoint** once `N > 2P³`: distinct fractions with denominators at most
`P` are at least `1/P²` apart, more than the arcs' total width `2P/N`. -/
theorem majorArc_disjoint {N P : ℕ} (hN : 2 * P ^ 3 < N) {x y : ℕ × ℕ} (hx : x ∈ arcIndex P)
    (hy : y ∈ arcIndex P) (hxy : x ≠ y) :
    Disjoint (majorArc N P x.1 x.2) (majorArc N P y.1 y.2) := by
  sorry

/-- **Every major arc lies in the window** `(P/N, 1 + P/N]` once `N > 2P²`. -/
theorem majorArc_subset_window {N P : ℕ} (hP : 1 ≤ P) (hN : 2 * P ^ 2 < N) {x : ℕ × ℕ}
    (hx : x ∈ arcIndex P) :
    majorArc N P x.1 x.2 ⊆ Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N) := by
  sorry

/-- **Off the major arcs, `S` is small:** there is a `K` such that, for `N > 2P²` and every `α` in
the window that lies on no major arc, `|S(α)| ≤ K (2N/√P + N^{7/8}) (log N)³`. -/
theorem norm_primeExpSum_le_off_arcs :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N P : ℕ) (α : ℝ), 2 ≤ N → 1 ≤ P → 2 * P ^ 2 < N →
      α ∈ Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N) →
      (∀ x ∈ arcIndex P, α ∉ majorArc N P x.1 x.2) →
        ‖primeExpSum N α‖
          ≤ K * (2 * (N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((7 : ℝ) / 8)) * Real.log N ^ 3 := by
  sorry

end Salt.ThreePrimes
