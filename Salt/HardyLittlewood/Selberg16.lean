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
  have h : oddOmegaSum z = ∑ m ∈ (Finset.range z).filter Odd, Salt.M3Expansion.nuStar m := by
    rw [oddOmegaSum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : Odd n
    · simp [pow2Omega, hn, Salt.M3Expansion.nuStar]
    · simp [pow2Omega, hn]
  rw [h, Salt.M3Assembly.mainTermSum]
  exact Salt.M3Expansion.nuStar_sum_le_gTwin_sum z

/-! ## M2 — `2^Ω = β ∗ τ` on odd `n`, with `β ≥ 0` -/

/-- `β(m) = ∏_{p^k ∥ m} b(k)` with `b(1) = 0`, `b(k) = 2^(k−2)` for `k ≥ 2`, on odd `m`;
`0` on even `m`. -/
noncomputable def betaT (m : ℕ) : ℝ :=
  if Odd m then
    ∏ p ∈ m.primeFactors,
      (if m.factorization p = 1 then 0 else (2 : ℝ) ^ (m.factorization p - 2))
  else 0

/-- The local factor of `betaT`: `b(k) = 0` at `k = 1`, `2^(k−2)` otherwise (`b(0) = 1`). -/
noncomputable def betaLoc (k : ℕ) : ℝ := if k = 1 then 0 else (2 : ℝ) ^ (k - 2)

lemma betaT_eq_prod {m : ℕ} (hm : Odd m) :
    betaT m = ∏ p ∈ m.primeFactors, betaLoc (m.factorization p) := by
  simp [betaT, hm, betaLoc]

/-- **W0a.** `betaT` is multiplicative on coprime odd arguments. -/
theorem betaT_mul {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : Nat.Coprime a b) :
    betaT (a * b) = betaT a * betaT b := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [betaT_eq_prod (ha.mul hb), betaT_eq_prod ha, betaT_eq_prod hb,
    Nat.primeFactors_mul ha0 hb0, Finset.prod_union hab.disjoint_primeFactors,
    Nat.factorization_mul ha0 hb0]
  congr 1
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have : b.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpb
      exact (Finset.disjoint_left.mp hab.disjoint_primeFactors) hp
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpb, hb0⟩)
    simp [this]
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have : a.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpa
      exact (Finset.disjoint_left.mp hab.disjoint_primeFactors)
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpa, ha0⟩) hp
    simp [this]

/-- **W0b.** `betaT (p^k) = b(k)` for an odd prime `p`. -/
theorem betaT_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    betaT (p ^ k) = betaLoc k := by
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  rw [betaT_eq_prod hodd]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [betaLoc]
  · rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
      hp.factorization_pow, Finsupp.single_eq_same]

lemma betaT_one : betaT 1 = 1 := by simp [betaT]

/-- **M2a.** -/
theorem betaT_nonneg (m : ℕ) : 0 ≤ betaT m := by
  unfold betaT
  split_ifs
  · exact Finset.prod_nonneg (fun p _ => by split_ifs <;> positivity)
  · exact le_rfl

/-! ## M3 — the odd divisor sum -/

/-- `Σ_{a,b odd, a·b ≤ y} 1/(a·b)`, i.e. `Σ_{k ≤ y, k odd} τ(k)/k`. -/
noncomputable def oddDivSum (y : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 y).filter Odd, ∑ b ∈ (Finset.Icc 1 y).filter Odd,
    if a * b ≤ y then 1 / ((a : ℝ) * b) else 0

end Salt.HardyLittlewood.Sel
