/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude

The definitions and results in this file are adapted from Arend Mellendijk's
SelbergSieve project (https://github.com/amellendijk/selberg-sieve4,
`SelbergSieve/Selberg.lean`, Copyright (c) 2023 Arend Mellendijk, Apache 2.0),
whose sieve-foundation layer is already part of mathlib as
`Mathlib/NumberTheory/SelbergSieve.lean`.
-/
import Mathlib

/-!
# Selberg weights (blueprint N1.1 — the M1 port layer)

The truncated optimal weights of the Selberg Λ² sieve, against mathlib's
`SelbergSieve` structure: the bounding sum `S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ)`
(positive, since `g > 0` on divisors of `P` and `ℓ = 1` qualifies), the
weights themselves, their support (`d ∣ P`, `d² ≤ y`), and `w 1 = 1`.

N1.2 (`|w d| ≤ 1`), N1.3 (`mainSum = 1/S`), and N1.4 (the fundamental
theorem) continue the port in later work; see the guide's R1/A1.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.SelbergPort

variable (s : SelbergSieve)

open Classical in
/-- The Selberg bounding sum `S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ)` — the `G(√y)` of
the classical fundamental theorem (blueprint N1.3 convention). -/
noncomputable def selbergBoundingSum : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0

theorem selbergBoundingSum_pos : 0 < selbergBoundingSum s := by
  rw [selbergBoundingSum, ← Finset.sum_filter]
  apply Finset.sum_pos
  · intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    exact BoundingSieve.selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, ?_⟩
    simpa using s.one_le_level

theorem selbergBoundingSum_ne_zero : selbergBoundingSum s ≠ 0 :=
  ne_of_gt (selbergBoundingSum_pos s)

open Classical in
/-- N1.1: the truncated optimal Selberg weights. Classically
`λ_d = μ(d) · (g-weighted partial sums) / S`; here in the arithmetic form of
the reference formalization. -/
noncomputable def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * ((μ d : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ *
      ∑ m ∈ s.prodPrimes.divisors,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬d ∣ s.prodPrimes) :
    selbergWeights s d = 0 := by
  rw [selbergWeights, if_neg hd]

/-- N1.1 (support): the weights vanish beyond the truncation `d² ≤ y`. -/
theorem selbergWeights_eq_zero {d : ℕ} (hd : ¬(d : ℝ) ^ 2 ≤ s.level) :
    selbergWeights s d = 0 := by
  rw [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    rintro ⟨hym, -⟩
    apply hd
    calc ((d : ℝ)) ^ 2 ≤ ((d * m : ℕ) : ℝ) ^ 2 := by
          have h1 : (d : ℝ) ≤ ((d * m : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_mul_of_pos_right d (Nat.pos_of_mem_divisors hm)
          have h0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith
      _ ≤ s.level := hym
  · rfl

/-- N1.1: `w 1 = 1` — the normalization the Λ² machinery requires
(`upperMoebius_lambdaSquared` consumes exactly this). -/
theorem selbergWeights_one : selbergWeights s 1 = 1 := by
  rw [selbergWeights, if_pos (one_dvd _)]
  rw [s.nu_mult.1, BoundingSieve.selbergTerms_isMultiplicative.1]
  simp only [inv_one, one_mul, moebius_apply_one, Int.cast_one]
  have hsum : (∑ m ∈ s.prodPrimes.divisors,
      if (m : ℝ) ^ 2 ≤ s.level ∧ m.Coprime 1 then s.selbergTerms m else 0)
      = selbergBoundingSum s := by
    rw [selbergBoundingSum]
    exact Finset.sum_congr rfl fun m _ => by simp
  rw [hsum, inv_mul_cancel₀ (selbergBoundingSum_ne_zero s)]

end Salt.SelbergPort
