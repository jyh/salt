/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.PrimeWindow

/-!
# The additive-energy escape (Tao 1509.05422 §3, footnote 4), spine node W3-AE-d

The frozen quadruple-count of the log-Chowla footnote-4 escape: the additive
energy of the prime window `𝒫_H = {p prime : ε²H/2 < p ≤ ε²H}` — the number of
additive quadruples `(p₁,p₂,p₃,p₄) ∈ 𝒫_H⁴` with `p₁ + p₂ = p₃ + p₄` — is
`≪_ε H³ / log⁴ H` in the regime.

This file isolates the SIEVE content in one named hypothesis.  The chain
(recon S1–S7) is:

1. **Parseval / `Σ r(n)²` form.**  `E[𝒫_H] = ∑_{n ∈ 𝒫_H+𝒫_H} r(n)²` where
   `r(n) = #{(p₁,p₂) ∈ 𝒫_H² : p₁+p₂ = n}` (mathlib `addEnergy_eq_sum_sq'`,
   ℕ-safe — no `[Fintype]`).
2. **The r(n) sieve bound.**  The binary-Goldbach upper sieve gives
   `r(n) ≪ (N/log²N)·𝔖(n)` with `N = ε²H` and `𝔖` the singular series, and
   `∑_{n ~ 2N} 𝔖(n)² ≪ N`; hence `E[𝒫_H] ≪ (N/log²N)²·N = N³/log⁴N`.

The pure reduction `addEnergy_le_of_r_bound` (route-independent) folds the whole
of step 2 into a single hypothesis `∑_{n ∈ 𝒫_H+𝒫_H} rbound(n)² ≤ …`, so the
analytic-sieve content lives in ONE place and the additive combinatorics is
discharged here.  See `docs/exploration/s3-a3-design.md`, section "The
additive-energy escape — FROZEN (W3-cd-R0)".
-/

open scoped BigOperators Pointwise Combinatorics.Additive

namespace Salt.Entropy.Chowla

/-- The **representation count** `r(n) = #{(p₁,p₂) ∈ s × t : p₁ + p₂ = n}` for two
finsets `s t : Finset ℕ`.  This is the fiber cardinality appearing in the
`Σ r(n)²` form of the additive energy (mathlib `addEnergy_eq_sum_sq'`). -/
def repCount (s t : Finset ℕ) (n : ℕ) : ℕ :=
  {xy ∈ s ×ˢ t | xy.1 + xy.2 = n}.card

lemma addEnergy_eq_sum_repCount_sq (s t : Finset ℕ) :
    Finset.addEnergy s t = ∑ n ∈ s + t, (repCount s t n) ^ 2 := by
  rw [Finset.addEnergy_eq_sum_sq']
  rfl

/-- **The route-independent reduction** (W3-AE-d spine, isolation step).  Given a
pointwise upper bound `repCount s t n ≤ rbound n` on the representation count by a
nonnegative function `rbound`, the additive energy is bounded by the sum of
squares of `rbound` over the sumset.  All the analytic-sieve content is thus
isolated in the single hypothesis `hpt` (the `r(n)` bound) plus the downstream
control of `∑ rbound(n)²`.  (No sign hypothesis on `rbound` is needed: the
pointwise bound `0 ≤ repCount ≤ rbound` forces `rbound ≥ 0` at every point.) -/
lemma addEnergy_le_of_r_bound (s t : Finset ℕ) (rbound : ℕ → ℝ)
    (hpt : ∀ n, (repCount s t n : ℝ) ≤ rbound n) :
    (Finset.addEnergy s t : ℝ) ≤ ∑ n ∈ s + t, (rbound n) ^ 2 := by
  rw [addEnergy_eq_sum_repCount_sq]
  push_cast
  refine Finset.sum_le_sum (fun n _ => ?_)
  have h0 : (0 : ℝ) ≤ (repCount s t n : ℝ) := Nat.cast_nonneg _
  have h1 := hpt n
  nlinarith [h0, h1]

/-- **The frozen W3-AE-d statement, sieve-parametric** (the SEAM for the Lemma
3.5 assembly).  Given a per-`H` majorant `rbound H` of the representation count
`r(n) = #{(p₁,p₂) ∈ 𝒫_H² : p₁+p₂ = n}` (hypothesis `hpt` — the binary-Goldbach
upper sieve `r(n) ≪ (ε²H/log²H)·𝔖(n)`) together with the sum-of-squares control
`∑_{n ∈ 𝒫_H+𝒫_H} rbound(n)² ≪_ε H³/log⁴H` (hypothesis `hsq` — the singular-series
second moment `∑ 𝔖² ≪ N`), the additive energy of the prime window is
`≪_ε H³/log⁴H`.

The analytic-number-theory content is isolated entirely in `hpt` and `hsq`; this
theorem is the pure additive-combinatorial glue (`addEnergy_le_of_r_bound` ∘
`hsq`).  Whoever lands the two sieve hypotheses obtains the frozen escape count
`W3-AE-d` verbatim.  Constant `C` and threshold `H₀` may depend on `ε`
(matching Tao's `≪_{a,h,ε}`); both are quantified OUTSIDE `H`. -/
theorem W3_AE_d_of_sieve (eps : ℚ) (rbound : ℕ → ℕ → ℝ)
    (hpt : ∀ H n,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ) ≤ rbound H n)
    (hsq : ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H, (rbound H n) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      (Finset.addEnergy (primeWindow eps H) (primeWindow eps H) : ℝ)
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  obtain ⟨C, hC, H₀, hH₀, hbd⟩ := hsq
  refine ⟨C, hC, H₀, hH₀, fun H hH => ?_⟩
  exact le_trans
    (addEnergy_le_of_r_bound (primeWindow eps H) (primeWindow eps H) (rbound H) (hpt H))
    (hbd H hH)

end Salt.Entropy.Chowla
