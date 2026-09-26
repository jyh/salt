/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M2b — `2^Ω = β ∗ τ` on odd `n` (statement frozen at salt `66fd0d0d`). -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- Partial sums of the local factor: `Σ_{i ≤ k+1} b(i) = 2^k`. -/
lemma betaLoc_range_sum (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), betaLoc i = (2 : ℝ) ^ k := by
  induction k with
  | zero => simp [Finset.sum_range_succ, betaLoc]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have : betaLoc (k + 1 + 1) = (2 : ℝ) ^ k := by
      simp [betaLoc]
    rw [this, pow_succ]; ring

/-- The local identity: `Σ_{i + j = k} b(i)·(j + 1) = 2^k`. -/
lemma betaLoc_antidiag_sum (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, betaLoc ij.1 * ((ij.2 : ℝ) + 1) = (2 : ℝ) ^ k := by
  induction k with
  | zero => simp [betaLoc]
  | succ k ih =>
    rw [Finset.Nat.sum_antidiagonal_succ']
    have hsplit : ∑ p ∈ Finset.antidiagonal k,
          betaLoc (p.1, p.2 + 1).1 * (((p.1, p.2 + 1).2 : ℕ) + 1 : ℝ)
        = ∑ p ∈ Finset.antidiagonal k, betaLoc p.1 * ((p.2 : ℝ) + 1)
          + ∑ p ∈ Finset.antidiagonal k, betaLoc p.1 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast; ring
    rw [hsplit, ih, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => betaLoc i)]
    rcases k with _ | k
    · simp [betaLoc]; norm_num
    · rw [show (k + 1).succ = k + 2 from rfl, betaLoc_range_sum]
      have : betaLoc (k + 1 + 1) = (2 : ℝ) ^ k := by simp [betaLoc]
      simp only [Nat.cast_zero, zero_add, mul_one, this]
      rw [pow_succ, pow_succ]; ring

lemma betaT_zero : betaT 0 = 0 := by simp [betaT]


/-- `betaT` as an arithmetic function. -/
noncomputable def betaA : ArithmeticFunction ℝ := ⟨betaT, betaT_zero⟩

lemma betaA_apply (n : ℕ) : betaA n = betaT n := rfl

lemma betaA_isMultiplicative : betaA.IsMultiplicative := by
  refine ⟨betaT_one, fun {m n} hmn => ?_⟩
  simp only [betaA_apply]
  by_cases hm : Odd m
  · by_cases hn : Odd n
    · exact betaT_mul hm hn hmn
    · have : ¬ Odd (m * n) := by rw [Nat.odd_mul]; tauto
      simp [betaT, this, hn]
  · have : ¬ Odd (m * n) := by rw [Nat.odd_mul]; tauto
    simp [betaT, this, hm]

lemma pow2Omega_zero : pow2Omega 0 = 0 := by simp [pow2Omega]

/-- `pow2Omega` as an arithmetic function. -/
noncomputable def pow2OmegaA : ArithmeticFunction ℝ := ⟨pow2Omega, pow2Omega_zero⟩

lemma pow2OmegaA_apply (n : ℕ) : pow2OmegaA n = pow2Omega n := rfl

lemma pow2OmegaA_isMultiplicative : pow2OmegaA.IsMultiplicative := by
  refine ⟨by simp [pow2OmegaA_apply, pow2Omega], fun {m n} hmn => ?_⟩
  simp only [pow2OmegaA_apply]
  by_cases hm : Odd m
  · by_cases hn : Odd n
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      simp [pow2Omega, hm, hn, hm.mul hn, ArithmeticFunction.cardFactors_mul hm0 hn0, pow_add]
    · have : ¬ Odd (m * n) := by rw [Nat.odd_mul]; tauto
      simp [pow2Omega, this, hn]
  · have : ¬ Odd (m * n) := by rw [Nat.odd_mul]; tauto
    simp [pow2Omega, this, hm]

/-- The convolution `β ∗ τ` at an odd prime power is `2^k`. -/
lemma betaA_mul_sigma_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    (betaA * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ)) (p ^ k) = (2 : ℝ) ^ k := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y =>
      betaA x * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ) y),
    Nat.sum_divisors_prime_pow hp, ← betaLoc_antidiag_sum k,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => betaLoc i * ((j : ℝ) + 1))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.pow_div hik hp.pos, betaA_apply, betaT_prime_pow hp hp2,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  push_cast; ring

/-- **M2b.** The convolution identity on odd `n`. -/
theorem pow2Omega_eq_sum (n : ℕ) (hn : Odd n) :
    pow2Omega n = ∑ m ∈ n.divisors, betaT m * ((n / m).divisors.card : ℝ) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hR : ∑ m ∈ n.divisors, betaT m * ((n / m).divisors.card : ℝ)
      = (betaA * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ)) n := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y =>
        betaA x * (ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ) y)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [betaA_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.sigma_zero_apply]
  rw [hR, ← pow2OmegaA_apply,
    pow2OmegaA_isMultiplicative.multiplicative_factorization _ hn0,
    (betaA_isMultiplicative.mul
      (ArithmeticFunction.isMultiplicative_sigma.natCast)).multiplicative_factorization _ hn0]
  refine Finsupp.prod_congr (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ n := Nat.dvd_of_mem_primeFactors (by simpa using hp)
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr this)
  rw [betaA_mul_sigma_prime_pow hpp hp2, pow2OmegaA_apply]
  simp [pow2Omega, (hpp.odd_of_ne_two hp2).pow, ArithmeticFunction.cardFactors_apply_prime_pow hpp]

end Salt.HardyLittlewood.Sel
