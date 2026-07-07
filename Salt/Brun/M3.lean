/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# M3 — main term, Mertens-free (blueprint milestone)

Self-contained analytic facts feeding the `G(z) ≥ c(log z)²` bound. Facts that
depend on the sieve's `nu`/`selbergTerms` (not yet built — see N2.6/N3.2) are
deferred; only the divisor-count/prime-factor arithmetic that stands on its
own is proved here.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Omega

/-- N3.3 (part 1): `τ(m) ≤ 2^Ω(m)` — the divisor-count function is bounded by
`2` to the power of the number of prime factors counted with multiplicity.
For `m = ∏ p^a`, `τ(m) = ∏(a+1) ≤ ∏2^a = 2^Ω(m)` since `a+1 ≤ 2^a` for all
`a`. Part 2 (`ν*(m) ≥ τ(m)/m` for odd `m`) needs `ν*` from N3.2, which needs
the sieve instance (N2.6) — not restated here. -/
theorem card_divisors_le_two_pow_cardFactors {m : ℕ} (hm : m ≠ 0) :
    m.divisors.card ≤ 2 ^ Ω m := by
  rw [Nat.card_divisors hm, cardFactors_eq_sum_factorization, Finsupp.sum,
    ← Nat.support_factorization]
  calc m.factorization.support.prod (fun p => m.factorization p + 1)
      ≤ m.factorization.support.prod (fun p => 2 ^ m.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => by omega)
        intro p _
        exact Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ = 2 ^ (∑ p ∈ m.factorization.support, m.factorization p) := by
        rw [← Finset.prod_pow_eq_pow_sum]

/-- The sum of `1/i` over even `i ∈ Icc 1 n` is half the harmonic number of
`n / 2` (reindex `i = 2j`). -/
lemma even_sum_eq_half_harmonic (n : ℕ) :
    ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Even i), (i : ℝ)⁻¹
      = (1 / 2 : ℝ) * harmonic (n / 2) := by
  have hset : (Finset.Icc 1 n).filter (fun i => Even i) =
      (Finset.Icc 1 (n / 2)).image (fun j => 2 * j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, hj⟩
      exact ⟨j, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, hij⟩
      exact ⟨⟨by omega, by omega⟩, j, by omega⟩
  rw [hset, Finset.sum_image (fun j1 _ j2 _ h => by omega)]
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  field_simp

/-- The sum of `1/a` over odd `a ∈ Icc 1 n`. -/
noncomputable def oddHarmonicSum (n : ℕ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), (i : ℝ)⁻¹

lemma oddHarmonicSum_eq (n : ℕ) :
    oddHarmonicSum n = harmonic n - (1 / 2 : ℝ) * harmonic (n / 2) := by
  unfold oddHarmonicSum
  rw [eq_sub_iff_add_eq, ← even_sum_eq_half_harmonic n]
  rw [harmonic_eq_sum_Icc]
  push_cast
  have hsplit : (Finset.Icc 1 n).filter (fun i => Odd i) ∪
      (Finset.Icc 1 n).filter (fun i => Even i) = Finset.Icc 1 n := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    rw [← Nat.not_even_iff_odd]
    tauto
  have hdisj : Disjoint ((Finset.Icc 1 n).filter (fun i => Odd i))
      ((Finset.Icc 1 n).filter (fun i => Even i)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter] at hi hi'
    exact (Nat.not_even_iff_odd.mpr hi.2) hi'.2
  conv_rhs => rw [← hsplit]
  rw [Finset.sum_union hdisj]

/-- N3.5: `Σ_{a≤n, odd} 1/a ≥ (log n)/2 - C` for the explicit constant
`C = (1 - log 2)/2`. Via `harmonic n ≥ log(n+1)` and
`harmonic(n/2) ≤ 1 + log(n/2)` (mathlib's `Harmonic/Bounds.lean`), applied to
`oddHarmonicSum n = harmonic n - harmonic(n/2)/2`. -/
theorem oddHarmonicSum_ge (n : ℕ) :
    oddHarmonicSum n ≥ (Real.log n) / 2 - (1 - Real.log 2) / 2 := by
  have hCpos : 0 ≤ (1 - Real.log 2) / 2 := by
    have : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  rw [oddHarmonicSum_eq]
  match n, Nat.lt_or_ge n 2 with
  | 0, _ => simp; linarith
  | 1, _ => norm_num [harmonic]; linarith
  | (n + 2), _ =>
    have hn0 : n + 2 ≠ 0 := by omega
    have h1 : Real.log ((n + 2) + 1 : ℕ) ≤ harmonic (n + 2) := log_add_one_le_harmonic (n + 2)
    have h2 : harmonic ((n + 2) / 2) ≤ 1 + Real.log ((n + 2) / 2 : ℕ) :=
      harmonic_le_one_add_log ((n + 2) / 2)
    have h3 : Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log (((n + 2) + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast; linarith
    have hdiv_pos : (0 : ℝ) < (((n + 2) / 2 : ℕ) : ℝ) := by
      have : 1 ≤ (n + 2) / 2 := by omega
      exact_mod_cast this
    have h4 : Real.log (((n + 2) / 2 : ℕ) : ℝ) ≤ Real.log ((n + 2 : ℕ) : ℝ) - Real.log 2 := by
      rw [← Real.log_div (by positivity : ((n + 2 : ℕ) : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      apply Real.log_le_log (by positivity)
      have hh : ((n + 2) / 2 : ℕ) * 2 ≤ n + 2 := Nat.div_mul_le_self (n + 2) 2
      have : (((n + 2) / 2 : ℕ) : ℝ) * 2 ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hh
      linarith
    linarith
