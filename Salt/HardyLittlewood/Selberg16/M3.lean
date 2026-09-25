/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M3 — the odd divisor sum `≥ (log y)²/8 − A(log y + 1)`

Statement frozen at salt `66fd0d0d`. -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- Peeling the top index off a sum over the odd elements of `Icc 1 (n+1)`. -/
lemma sumOdd_succ (φ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ (Finset.Icc 1 (n + 1)).filter (fun i => Odd i), φ i
      = ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), φ i
        + (if Odd (n + 1) then φ (n + 1) else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]

lemma oddHarmonicSum_succ (n : ℕ) :
    oddHarmonicSum (n + 1) = oddHarmonicSum n
      + (if Odd (n + 1) then ((n + 1 : ℕ) : ℝ)⁻¹ else 0) := by
  unfold oddHarmonicSum
  exact sumOdd_succ (fun i => (i : ℝ)⁻¹) n

/-- The symmetric-square identity `2·Σ_a H(a)/a = H(n)² + Σ_a 1/a²` (odd `a ≤ n`). -/
lemma two_sum_H_div (n : ℕ) :
    2 * ∑ a ∈ (Finset.Icc 1 n).filter (fun i => Odd i), oddHarmonicSum a * (a : ℝ)⁻¹
      = oddHarmonicSum n ^ 2
        + ∑ a ∈ (Finset.Icc 1 n).filter (fun i => Odd i), ((a : ℝ)⁻¹) ^ 2 := by
  induction n with
  | zero => simp [oddHarmonicSum]
  | succ n ih =>
    rw [sumOdd_succ, sumOdd_succ, oddHarmonicSum_succ]
    by_cases h : Odd (n + 1)
    · simp only [h, if_true]
      linear_combination ih
    · simp only [h, if_false, add_zero]
      exact ih

/-- Upper bound `H(n) ≤ log n / 2 + 3/2` for `n ≥ 1`. -/
lemma oddHarmonicSum_le (n : ℕ) (hn : 1 ≤ n) :
    oddHarmonicSum n ≤ Real.log n / 2 + 3 / 2 := by
  rw [oddHarmonicSum_eq]
  have h1 : harmonic n ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have h2 : Real.log ↑(n / 2 + 1) ≤ harmonic (n / 2) := log_add_one_le_harmonic (n / 2)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : Real.log n - Real.log 2 ≤ Real.log ↑(n / 2 + 1) := by
    rw [← Real.log_div hnpos.ne' (by norm_num)]
    apply Real.log_le_log (by positivity)
    have hlt : n < 2 * (n / 2 + 1) := by omega
    have : (n : ℝ) < 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [div_le_iff₀ (by norm_num)]; linarith
  linarith

/-- The inner sum at a fixed odd `a` is `(1/a)·H(⌊y/a⌋)`. -/
lemma inner_eq (y a : ℕ) (ha : 1 ≤ a) :
    ∑ b ∈ (Finset.Icc 1 y).filter Odd, (if a * b ≤ y then 1 / ((a : ℝ) * b) else 0)
      = (a : ℝ)⁻¹ * oddHarmonicSum (y / a) := by
  rw [← Finset.sum_filter]
  have hset : ((Finset.Icc 1 y).filter Odd).filter (fun b => a * b ≤ y)
      = (Finset.Icc 1 (y / a)).filter (fun i => Odd i) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm b a]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      refine ⟨⟨⟨h1, ?_⟩, h2⟩, h3⟩
      nlinarith
  rw [hset, oddHarmonicSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [one_div, mul_inv]

/-- `H(⌊y/a⌋) ≥ H(y) − H(a) − 3` for `1 ≤ a ≤ y`. -/
lemma H_div_ge (y a : ℕ) (ha : 1 ≤ a) (hay : a ≤ y) :
    oddHarmonicSum y - oddHarmonicSum a - 3 ≤ oddHarmonicSum (y / a) := by
  have hq : 1 ≤ y / a := (Nat.one_le_div_iff (by omega)).mpr hay
  have hlt : y < a * (y / a + 1) := Nat.lt_mul_div_succ y (by omega)
  have hnat : y ≤ 2 * a * (y / a) := by nlinarith
  have hy1 : 1 ≤ y := le_trans ha hay
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hqpos : (0 : ℝ) < ((y / a : ℕ) : ℝ) := by exact_mod_cast hq
  have hylog : Real.log y ≤ Real.log 2 + Real.log a + Real.log ((y / a : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) hapos.ne', ← Real.log_mul (by positivity) hqpos.ne']
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
    exact_mod_cast hnat
  have e1 := oddHarmonicSum_ge (y / a)
  have e2 := oddHarmonicSum_ge a
  have e3 := oddHarmonicSum_le y hy1
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- **M3.** -/
theorem oddDivSum_ge : ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℕ, 1 ≤ y →
    (Real.log y) ^ 2 / 8 - A * (Real.log y + 1) ≤ oddDivSum y := by
  refine ⟨6, by norm_num, fun y hy => ?_⟩
  set S := (Finset.Icc 1 y).filter (fun i => Odd i) with hS
  set H := oddHarmonicSum y with hH
  have hHdef : H = ∑ a ∈ S, (a : ℝ)⁻¹ := rfl
  -- step 1: the hyperbola rewrite
  have hdiv : oddDivSum y = ∑ a ∈ S, (a : ℝ)⁻¹ * oddHarmonicSum (y / a) := by
    unfold oddDivSum
    refine Finset.sum_congr rfl (fun a ha => ?_)
    exact inner_eq y a (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  -- step 2: termwise lower bound
  have hlow : ∑ a ∈ S, (a : ℝ)⁻¹ * (H - oddHarmonicSum a - 3) ≤ oddDivSum y := by
    rw [hdiv]
    refine Finset.sum_le_sum (fun a ha => ?_)
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at ha
    have hapos : (0 : ℝ) ≤ (a : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (H_div_ge y a ha.1.1 ha.1.2) hapos
  have hexp : ∑ a ∈ S, (a : ℝ)⁻¹ * (H - oddHarmonicSum a - 3)
      = (H - 3) * H - ∑ a ∈ S, oddHarmonicSum a * (a : ℝ)⁻¹ := by
    rw [hHdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  -- step 3: the symmetric square, with Σ 1/a² ≤ H
  have hsym := two_sum_H_div y
  have hQ : ∑ a ∈ S, ((a : ℝ)⁻¹) ^ 2 ≤ H := by
    rw [hHdef]
    refine Finset.sum_le_sum (fun a ha => ?_)
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at ha
    have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1.1
    have h0 : 0 ≤ (a : ℝ)⁻¹ := by positivity
    have : (a : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    nlinarith
  -- step 4: the logarithmic sandwich
  have hLo := oddHarmonicSum_ge y
  have hHi := oddHarmonicSum_le y hy
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
  have key : (Real.log y) ^ 2 / 8 - 6 * (Real.log y + 1) ≤ H ^ 2 / 2 - 7 / 2 * H := by
    have hc : (1 - Real.log 2) / 2 ≤ 1 / 2 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
    have hge : Real.log y / 2 - 1 / 2 ≤ H := by linarith
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hge), sq_nonneg (H - Real.log y / 2)]
  linarith

end Salt.HardyLittlewood.Sel
