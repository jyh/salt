/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.LowerMoebius
import Salt.BrunLower.Pointwise
import Salt.BrunLower.MainTerm
import Salt.BrunLower.BlockDecomp
import Salt.BrunLower.WRatio
import Salt.BrunLower.Lemma3
import Salt.BrunLower.Remainder

/-!
# The frozen both-sided Brun pair `brun_lower`/`brun_upper` (blueprint `p0`, node B5)

The HEADLINE of the P0 rung: Halberstam–Richert's Théorème 2 (*A new look at Brun's
sieve*, Mém. SMF **25** (1971) 97–106), assembled from the landed pieces with **no new
mathematics** — a pure composition of interfaces.

## The lower bound (load-bearing; P1 consumes this side)

```
  X·W(z)·(1 − 2λ^{2b}e^{2λ}/(1 − λ²e^{2+2λ})) − Σ_{d|P(z)} χ₂(d)|R_d|  ≤  S
```

Chain: node B1 (`siftedSum_ge_mainSum_errSum_of_lowerMoebius`) at the lower-Möbius system
`μ·[χ₂]` (node B2, `isLowerMoebius_moebius_chiTwo`) reduces `S` to `X·mainSum − errSum`.
The main term is closed by `mainSum_ge_of_lower'` (node B3a, the fully composed endpoint)
with `hcorr` discharged by `hcorr_lower` (node B3a′) and the (2.16) density inputs supplied
by `Wratio_le_exp`/`windowSum_le` (node B3b) from the Mertens interface `hMert`/`hkappa`.
The error term is bounded by `remainder_prod_bound_of_R` (node B4) after the `|μ·[χ₂]| ≤ [χ₂]`
absorption (`|μ| ≤ 1`).

## The upper bound

The mirror, with mathlib's own upper plumbing
(`siftedSum_le_mainSum_errSum_of_upperMoebius`) at `μ·[χ₁]`
(`isUpperMoebius_moebius_chiOne`), `mainSum_le_of_upper'`/`hcorr_upper`, and B4 at `ν = 1`.

## Hypothesis inventory (the UNION the landed inputs demand)

Everything below is exactly what the composed endpoints require; nothing derivable is
re-required.  `hMert`/`hkappa` are B3b's (2.16) interface (P1 discharges them at the twin
instance, `p0.md` catch #19 — no hidden `z₀`); `(R)` is `hR`, `(Ω)` is `hωA`/`hA`, and the
multiplicative shape `hωprod` is B4's.  `htotalMass : 0 ≤ X` is the sieve's own
`X = |𝒜|`-approximation nonnegativity (implicit in H-R's statement) — needed to carry the
main-term comparison through the `X·` factor.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.BrunLower

open BoundingSieve

/-! ## The error term: `errSum(μ·[χ_ν]) ≤ (2.12) product` -/

/-- The B1/mathlib error term against the block-Brun system `μ·[χ_ν]` is bounded by H-R's
remainder product (2.12): `|μ(d)·[χ_ν(d)]| ≤ [χ_ν(d)]` (as `|μ| ≤ 1` and the indicator is
`{0,1}`), then `remainder_prod_bound_of_R` (node B4). -/
theorem errSum_le_remainder_prod (s : BoundingSieve) {Lam z A : ℝ} {b side : ℕ} {ω : ℕ → ℝ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b) (hside : side = 1 ∨ side = 2) (hA : 1 ≤ A)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hωnn : ∀ p, p.Prime → 0 ≤ ω p) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hωprod : ∀ d, Squarefree d → ω d = ∏ p ∈ d.primeFactors, ω p)
    (hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ ω d) :
    s.errSum (fun d => (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0))
      ≤ (1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b - side + 1)
        * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
            (1 + A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2 := by
  have hB4 := remainder_prod_bound_of_R (Lam := Lam) (z := z) (A := A) (b := b) (side := side)
    (N := s.prodPrimes) (ω := ω) (R := s.rem)
    hLam hz hb hside hA s.prodPrimes_squarefree hzprimes hωnn hωA hωprod hR
  refine le_trans ?_ hB4
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d _
  have hμ : |(μ d : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  by_cases hc : chi Lam z side b d
  · simp only [if_pos hc, mul_one]
    exact mul_le_of_le_one_left (abs_nonneg _) hμ
  · simp [if_neg hc]

/-! ## The frozen pair -/

/-- **`brun_lower`** — H-R Théorème 2, lower bound (node B5, the load-bearing side).
Assembled by composition: B1's lower Möbius plumbing at `μ·[χ₂]` (B2), the fully composed
lower main-term endpoint `mainSum_ge_of_lower'` (B3a) with `hcorr_lower` (B3a′) and the
(2.16) density inputs from `Wratio_le_exp`/`windowSum_le` (B3b), and the remainder product
`remainder_prod_bound_of_R` (B4).  `hMert`/`hkappa` are B3b's Mertens interface (`p0.md`
catch #19; P1 discharges them at the twin instance). -/
theorem brun_lower (s : BoundingSieve) {lam Lam z kappa : ℝ} {b : ℕ} {A : ℝ} (ω : ℕ → ℝ)
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (hLam : 0 < Lam) (hz : 1 < z) (htotalMass : 0 ≤ s.totalMass)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hkappa : kappa ≤ 2 * lam)
    (hMert : ∀ n ∈ Finset.Icc 1 (minLevel Lam z),
      Real.log (Wratio s Lam z n) ≤ (n : ℝ) * kappa)
    (hA : 1 ≤ A)
    (hωnn : ∀ p, p.Prime → 0 ≤ ω p) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hωprod : ∀ d, Squarefree d → ω d = ∏ p ∈ d.primeFactors, ω p)
    (hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ ω d) :
    s.totalMass * W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        - (1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b - 1)
          * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
              (1 + A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2
      ≤ s.siftedSum := by
  -- (1) B1: reduce the sifted sum to `X·mainSum − errSum`.
  have hB1 := siftedSum_ge_mainSum_errSum_of_lowerMoebius
    (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0))
    (isLowerMoebius_moebius_chiTwo (Lam := Lam) (z := z) (b := b) hb) (s := s)
  -- (2) main term: the fully composed lower endpoint, `hcorr` + (2.16) discharged.
  have hmain := mainSum_ge_of_lower' s hb hlam h12
    (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le)
    (Wratio_le_exp s hkappa hMert) (windowSum_le s hkappa hMert)
    (hcorr_lower s hLam hz hb hzprimes)
  have hmul := mul_le_mul_of_nonneg_left hmain htotalMass
  -- (3) error term: the (2.12) remainder product at `ν = 2`.
  have herr := errSum_le_remainder_prod s (side := 2) hLam hz hb (Or.inr rfl) hA
    hzprimes hωnn hωA hωprod hR
  rw [show 2 * b - 2 + 1 = 2 * b - 1 from by omega] at herr
  -- assemble.
  rw [mul_assoc]
  linarith [hB1, hmul, herr]

/-- **`brun_upper`** — H-R Théorème 2, upper bound (node B5).  The mirror of `brun_lower`
through mathlib's own upper Möbius plumbing at `μ·[χ₁]` (B2), the composed upper endpoint
`mainSum_le_of_upper'` (B3a) with `hcorr_upper` (B3a′) and (2.16), and B4 at `ν = 1`. -/
theorem brun_upper (s : BoundingSieve) {lam Lam z kappa : ℝ} {b : ℕ} {A : ℝ} (ω : ℕ → ℝ)
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (hLam : 0 < Lam) (hz : 1 < z) (htotalMass : 0 ≤ s.totalMass)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hkappa : kappa ≤ 2 * lam)
    (hMert : ∀ n ∈ Finset.Icc 1 (minLevel Lam z),
      Real.log (Wratio s Lam z n) ≤ (n : ℝ) * kappa)
    (hA : 1 ≤ A)
    (hωnn : ∀ p, p.Prime → 0 ≤ ω p) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hωprod : ∀ d, Squarefree d → ω d = ∏ p ∈ d.primeFactors, ω p)
    (hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ ω d) :
    s.siftedSum
      ≤ s.totalMass * W s * (1 + 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        + (1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b)
          * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
              (1 + A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2 := by
  -- (1) mathlib upper plumbing: `S ≤ X·mainSum + errSum`.
  have hU := siftedSum_le_mainSum_errSum_of_upperMoebius
    (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
    (isUpperMoebius_moebius_chiOne (Lam := Lam) (z := z) (b := b) hb) (s := s)
  -- (2) main term: the fully composed upper endpoint.
  have hmain := mainSum_le_of_upper' s hb hlam h12
    (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le)
    (Wratio_le_exp s hkappa hMert) (windowSum_le s hkappa hMert)
    (hcorr_upper s hLam hz hb hzprimes)
  have hmul := mul_le_mul_of_nonneg_left hmain htotalMass
  -- (3) error term at `ν = 1`.
  have herr := errSum_le_remainder_prod s (side := 1) hLam hz hb (Or.inl rfl) hA
    hzprimes hωnn hωA hωprod hR
  rw [show 2 * b - 1 + 1 = 2 * b from by omega] at herr
  -- assemble.
  rw [mul_assoc]
  linarith [hU, hmul, herr]

end Salt.BrunLower
