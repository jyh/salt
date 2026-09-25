/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.HardyLittlewood.Frame
import Salt.HardyLittlewood.Sharp

/-!
# HL-3c — the elementary Selberg twin bound `π₂(N) ≤ (16·Π₂ + ε)·N/(log N)²`

The Selberg sieve applied to `{n(n+2) : n ≤ N}` (dimension 2, level `N^(1−δ)`) gives
`π₂(N) ≤ (8 + ε)·𝔖·N/(log N)² = (16·Π₂ + ε)·N/(log N)²`, eight times the
Hardy–Littlewood prediction `𝔖 = 2·Π₂`. `Sharp.lean` stops at `C = 90` because it
bounds the Selberg denominator below by a squared odd-harmonic sum, which loses the
factor `Π₂/2` against the true dimension-2 mean value

  `mainTermSum z = Σ_{ℓ < z, ℓ odd squarefree} ∏_{p ∣ ℓ} 2/(p−2) ∼ (log z)²/(8·Π₂)`.

This file proves that mean value from below. Every term in the chain is nonnegative:

* **M1** `mainTermSum z ≥ Σ_{n < z, n odd} 2^Ω(n)/n` (group `n` by its radical; the
  inner sum is a truncated product of geometric series `Σ_k (2/p)^k = 2/(p−2)`).
* **M2** on odd `n`, `2^Ω = β ∗ τ` with `β` multiplicative, `β(p) = 0`,
  `β(p^k) = 2^(k−2)` for `k ≥ 2`, so `β ≥ 0`.
* **M3** `Σ_{a,b odd, ab ≤ y} 1/(ab) ≥ (log y)²/8 − A·(log y + 1)`.
* **M4** `Σ_{m ∣ R} β(m)/m ≥ (1−η)/Π₂` for a suitable odd `R` (a finite Euler product,
  `∏_{2<p≤Q} (1 + 1/(p(p−2))) = 1/∏_{2<p≤Q}(1 − (p−1)⁻²) → 1/Π₂`).
* **M5** the mean value `mainTermSum z ≥ (1−η)·(log z)²/(8·Π₂)` for large `z`.
* **M6** the sieve at level `N^(1−δ)`, counting EVEN divisors too
  (`selbergTerms (2ℓ) = selbergTerms ℓ`), which doubles the denominator.

The `(4+ε)·𝔖 = 8·Π₂` constant is a different theorem (Bombieri–Davenport). It sieves the
shifted primes `{p + 2}` at Bombieri–Vinogradov level and is not attempted here.
-/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-! ## M1 — from the squarefree main term to `2^Ω` -/

/-- `2^Ω(n)` on odd `n`, and `0` on even `n` (including `n = 0`). -/
noncomputable def pow2Omega (n : ℕ) : ℝ :=
  if Odd n then (2 : ℝ) ^ (ArithmeticFunction.cardFactors n) else 0

/-- `Σ_{n < x} 2^Ω(n)/n` over odd `n`. -/
noncomputable def oddOmegaSum (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range x, pow2Omega n / n

/-- **M1.** -/
theorem mainTermSum_ge_oddOmegaSum (z : ℕ) :
    oddOmegaSum z ≤ Salt.M3Assembly.mainTermSum z := by
  sorry

/-! ## M2 — `2^Ω = β ∗ τ` on odd `n`, with `β ≥ 0` -/

/-- `β(m) = ∏_{p^k ∥ m} b(k)` with `b(1) = 0`, `b(k) = 2^(k−2)` for `k ≥ 2`, on odd `m`;
`0` on even `m`. -/
noncomputable def betaT (m : ℕ) : ℝ :=
  if Odd m then
    ∏ p ∈ m.primeFactors,
      (if m.factorization p = 1 then 0 else (2 : ℝ) ^ (m.factorization p - 2))
  else 0

/-- **M2a.** -/
theorem betaT_nonneg (m : ℕ) : 0 ≤ betaT m := by
  sorry

/-- **M2b.** The convolution identity on odd `n`. -/
theorem pow2Omega_eq_sum (n : ℕ) (hn : Odd n) :
    pow2Omega n = ∑ m ∈ n.divisors, betaT m * ((n / m).divisors.card : ℝ) := by
  sorry

/-! ## M3 — the odd divisor sum -/

/-- `Σ_{a,b odd, a·b ≤ y} 1/(a·b)`, i.e. `Σ_{k ≤ y, k odd} τ(k)/k`. -/
noncomputable def oddDivSum (y : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 y).filter Odd, ∑ b ∈ (Finset.Icc 1 y).filter Odd,
    if a * b ≤ y then 1 / ((a : ℝ) * b) else 0

/-- **M3.** -/
theorem oddDivSum_ge : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℕ, 1 ≤ y →
    (Real.log y) ^ 2 / 8 - A * (Real.log y + 1) ≤ oddDivSum y := by
  sorry

/-! ## M5a — the convolution lower bound (M1 · M2 · a finite `m`-range) -/

/-- **M5a.** For odd `R`, `Σ_{n<x odd} 2^Ω(n)/n ≥ Σ_{m ∣ R} β(m)/m · oddDivSum((x−1)/m)`. -/
theorem oddOmegaSum_ge_conv (R x : ℕ) (hR : Odd R) :
    ∑ m ∈ R.divisors, betaT m / m * oddDivSum ((x - 1) / m) ≤ oddOmegaSum x := by
  sorry

/-! ## M4 — the finite Euler product reaches `1/Π₂` -/

/-- **M4.** -/
theorem betaSum_ge {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, Odd R ∧ (1 - η) / Pi2 ≤ ∑ m ∈ R.divisors, betaT m / m := by
  sorry

/-! ## M5 — the dimension-2 mean value -/

/-- **M5. The mean value.** `mainTermSum z ≥ (1−η)·(log z)²/(8·Π₂)` for all large `z`. -/
theorem mainTermSum_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ z : ℕ in atTop, (1 - η) * (Real.log z) ^ 2 / (8 * Pi2) ≤ Salt.M3Assembly.mainTermSum z := by
  sorry

/-! ## M6 — the sieve at level `N^(1−δ)`, even divisors included -/

/-- **HL-3c — the elementary Selberg twin bound.** For every `ε > 0`,
`π₂(N) ≤ (16·Π₂ + ε)·N/(log N)²` for all large `N`. -/
theorem twinCounting_upper_selberg {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (twinPrimeCounting N : ℝ) ≤ (16 * Pi2 + ε) * N / (Real.log N) ^ 2 := by
  sorry

end Salt.HardyLittlewood.Sel
