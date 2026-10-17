/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.Arcs
import Salt.ThreePrimes.Count
import Salt.ThreePrimes.SingularSeries
import Salt.ThreePrimes.SingularIntegral

/-!
# Three primes: the assembly

These are lemmas L20 and L21 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 7
and 8), and the theorem: **every sufficiently large odd number is a sum of three primes.**

Take `P = ⌊(log N)^{10}⌋` and `δ = P/N`, and write `f(α) = S(α)³ e(−Nα)`.

1. **The count is an integral over one period.** `R(N) = ∫₀¹ f`, and `f` has period `1`, so
   `R(N) = ∫ f` over the window `(δ, 1 + δ]` too (`weightedCount_eq_window`).
2. **Split the window** into the disjoint major arcs and what is left, the minor arcs
   (`integral_window_split`).
3. **The minor arcs contribute `o(N²)`.** There `|S| ≤ K (2N/√P + N^{7/8}) (log N)³`, and
   `∫ |S|² ≤ Σ_{n ≤ N} Λ(n)² ≤ C N log N` by Parseval. So the minor integral is at most
   `K C (2N²(log N)⁴/√P + N^{15/8}(log N)⁴)`, and `√P ≈ (log N)⁵` beats `(log N)⁴`
   (`norm_integral_minorArcs_le`).
4. **Each major arc contributes its main term.** On the arc at `a/q`, `S = (μ(q)/φ(q)) v + E`
   with `|E| ≤ K N/(log N)^{34}` (the major-arc approximation, with `B = 10`). The cube's error is
   at most `3|E| (N log N)²`, and the arc has length `2P/N`, so the error is
   `O(P N²/(log N)^{32})`. Over the at most `P²` arcs that totals `O(N²/(log N)²)`
   (`norm_majorArc_integral_sub_le`).
5. **The phases collect into the singular series.** Summing `e(−Na/q)` over the `a` coprime to `q`
   gives `c_q(N)` (`sum_phases_eq_ramanujanSum`), and `μ(q)³ = μ(q)`. So the main terms add up to
   `(Σ_{q ≤ P} μ(q) c_q(N)/φ(q)³) · J_δ` (`sum_arcIndex_main`).
6. **Complete both.** `J_δ = C(N − 1, 2) + O(N²/P²)` (the singular integral), and
   `Σ_{q ≤ P} = 𝔖(N) − (a tail)`. The tail is at most `Σ_{q > P} μ(q)²/φ(q)²`, which tends to `0`
   as `P → ∞`, uniformly in `N` (`tendsto_singular_tail`). **No rate is needed**: the theorem asks
   only for sufficiently large `N`.
7. **For odd `N`, `𝔖(N) ≥ c₀ > 0`,** so `R(N) ≥ (c₀/8) N²` once `N` is large
   (`weightedCount_lower`). Counting with weights cost at most `C N^{3/2}(log N)³`, far less, so
   `N` is a sum of three primes (`three_primes`).
-/

namespace Salt.ThreePrimes

open ArithmeticFunction Filter Topology
open Salt.ExpSum (eR norm_eR)

/-- **The arc parameter** `P = ⌊(log N)^{10}⌋`. -/
noncomputable def arcParam (N : ℕ) : ℕ := ⌊Real.log N ^ (10 : ℕ)⌋₊

/-- **The circle-method integrand** `f(α) = S(α)³ e(−Nα)`. -/
noncomputable def circleIntegrand (N : ℕ) (α : ℝ) : ℂ :=
  primeExpSum N α ^ 3 * eR (-(N : ℝ) * α)

/-- **The period window** `(P/N, 1 + P/N]`. -/
def arcWindow (N P : ℕ) : Set ℝ := Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N)

/-- **The minor arcs**: the window with the major arcs removed. -/
def minorArcs (N P : ℕ) : Set ℝ :=
  arcWindow N P \ ⋃ x ∈ arcIndex P, majorArc N P x.1 x.2

/-- **Step 1:** the weighted count is the integral of `f` over the window, by periodicity. -/
theorem weightedCount_eq_window (N P : ℕ) :
    ((weightedCount N : ℝ) : ℂ) = ∫ α in arcWindow N P, circleIntegrand N α := by
  sorry

/-- **Step 2:** the window splits into the disjoint major arcs and the minor arcs. -/
theorem integral_window_split {N P : ℕ} (hP : 1 ≤ P) (hN : 2 * P ^ 3 < N) :
    ∫ α in arcWindow N P, circleIntegrand N α
      = ∑ x ∈ arcIndex P, (∫ α in majorArc N P x.1 x.2, circleIntegrand N α)
        + ∫ α in minorArcs N P, circleIntegrand N α := by
  sorry

/-- **Step 3, the minor arcs:** `|∫_𝔪 f| ≤ sup_𝔪 |S| · ∫ |S|²`, with Parseval and the off-arc
bound. -/
theorem norm_integral_minorArcs_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N P : ℕ, 2 ≤ N → 1 ≤ P → 2 * P ^ 2 < N →
      ‖∫ α in minorArcs N P, circleIntegrand N α‖
        ≤ K * (2 * (N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((7 : ℝ) / 8)) * Real.log N ^ 3
            * ((N : ℝ) * Real.log N) := by
  sorry

/-- **Step 4, one major arc:** the integral over the arc at `a/q` is
`(μ(q)/φ(q))³ e(−Na/q) J_δ` up to `O(P N²/(log N)^{32})`. -/
theorem norm_majorArc_integral_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ x ∈ arcIndex (arcParam N),
      ‖(∫ α in majorArc N (arcParam N) x.1 x.2, circleIntegrand N α)
          - ((moebius x.1 : ℂ) / (x.1.totient : ℂ)) ^ 3 * eR (-(N : ℝ) * x.2 / x.1)
            * ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
                expSumOne N β ^ 3 * eR (-(N : ℝ) * β)‖
        ≤ K * (arcParam N : ℝ) * (N : ℝ) ^ 2 / Real.log N ^ 32 := by
  sorry

/-- **Step 5, the phases:** `Σ_{1 ≤ a ≤ q, gcd(a, q) = 1} e(−Na/q) = c_q(N)`, through
`a ↦ q − a`. -/
theorem sum_phases_eq_ramanujanSum (N q : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q), eR (-(N : ℝ) * a / q)
      = ramanujanSum q N := by
  sorry

/-- **Step 5, the main terms collect:** summed over the arcs, `(μ(q)/φ(q))³ e(−Na/q)` is the
truncated singular series `Σ_{q ≤ P} μ(q) c_q(N)/φ(q)³`. -/
theorem sum_arcIndex_main (N P : ℕ) :
    ∑ x ∈ arcIndex P, ((moebius x.1 : ℂ) / (x.1.totient : ℂ)) ^ 3 * eR (-(N : ℝ) * x.2 / x.1)
      = ∑ q ∈ Finset.Icc 1 P, singularTerm N q := by
  sorry

/-- **Step 6, the tail:** `Σ_{q > P} μ(q)²/φ(q)² → 0` as `P → ∞`. -/
theorem tendsto_singular_tail :
    Tendsto (fun P : ℕ => ∑' q : ℕ,
      if P < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 else 0) atTop (𝓝 0) := by
  sorry

/-- **Step 7:** for odd `N`, the weighted count is eventually at least `c N²` for some `c > 0`. -/
theorem weightedCount_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Odd N → c * (N : ℝ) ^ 2 ≤ weightedCount N := by
  sorry

/-- **Vinogradov's three-primes theorem:** every sufficiently large odd number is a sum of three
primes. -/
theorem three_primes :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  sorry

end Salt.ThreePrimes
