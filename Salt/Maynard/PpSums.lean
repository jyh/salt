/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehPp2
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The `k`-uniform divisor-power sums (node PP3-SUMS)

The `k`-generalisation of `GehPp2`'s `sum_two_pow_omega_le` (the `k = 2` case).  We bound the
sums `∑_{q ≤ Q} k^{ω(q)}` and `∑_{q ≤ Q} k^{ω(q)}/q` with the polylog **exponent
explicit in `k`** and an absolute constant `C₀ = 1` — the explicitness PP3-ASSEMBLY needs
so that `k ≤ √(log x / loglog x)` makes the bound `≤ Q · x^{o(1)}`.

The engine is the classical binomial identity
`k^{ω(q)} = ∑_{d ∣ q, d squarefree} (k−1)^{ω(d)}` (`pow_succ_omega_eq`, proven via
`Finset.prod_one_add` over `q.primeFactors`), the divisor swap `Finset.sum_comm'`, and the
harmonic multiple bound `Salt.LS.sum_inv_dvd_multiples_le`.  A one-line induction on `k` then
gives, with **`C₀ = 1`**:

* `sum_k_pow_omega_div_le` : `∑_{q ≤ Q} k^{ω(q)}/q ≤ (1 + log Q)^k`;
* `sum_k_pow_omega_le`     : `∑_{q ≤ Q} k^{ω(q)} ≤ Q · (1 + log Q)^{k−1}`.
-/

open Finset

namespace Salt.Maynard

/-- **The binomial identity.** `(k+1)^{ω(n)} = ∑_{d ∣ n, d squarefree} k^{ω(d)}`.
Both sides are `∑_{S ⊆ primeFactors n} k^{|S|}`: the left via `∏_{p}(1 + k) = (1+k)^{ω(n)}`
(`Finset.prod_one_add`), the right via `Nat.sum_divisors_filter_squarefree` and
`Nat.primeFactors_prod`. -/
lemma pow_succ_omega_eq {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ n.primeFactors.card
      = ∑ d ∈ n.divisors.filter Squarefree, (k : ℝ) ^ d.primeFactors.card := by
  have hR : ∑ d ∈ n.divisors.filter Squarefree, (k : ℝ) ^ d.primeFactors.card
      = ∑ t ∈ n.primeFactors.powerset, (k : ℝ) ^ t.card := by
    rw [Nat.sum_divisors_filter_squarefree hn]
    have hbridge : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
      rw [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
    rw [hbridge]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have heq : (t.val.prod).primeFactors = t := by
      rw [Finset.prod_val]; exact Nat.primeFactors_prod hprime
    rw [heq]
  have hL : ((k + 1 : ℕ) : ℝ) ^ n.primeFactors.card
      = ∑ t ∈ n.primeFactors.powerset, (k : ℝ) ^ t.card := by
    have hconst : ((k + 1 : ℕ) : ℝ) = 1 + (k : ℝ) := by push_cast; ring
    rw [hconst, ← Finset.prod_const (1 + (k : ℝ)),
      Finset.prod_one_add (f := fun _ : ℕ => (k : ℝ))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [Finset.prod_const]
  rw [hL, hR]

/-- The membership swap for `Finset.sum_comm'`: a pair `(q, d)` with `q ∈ [1,Q]` and `d` a
squarefree divisor of `q` is the same as `d` a squarefree number in `[1,Q]` and `q` a multiple
of `d` in `[1,Q]`. -/
lemma mem_swap_iff (Q q d : ℕ) :
    (q ∈ Finset.Icc 1 Q ∧ d ∈ q.divisors.filter Squarefree)
      ↔ (q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q)
          ∧ d ∈ (Finset.Icc 1 Q).filter Squarefree) := by
  constructor
  · rintro ⟨hqI, hdf⟩
    rw [Finset.mem_filter, Nat.mem_divisors] at hdf
    rw [Finset.mem_Icc] at hqI
    obtain ⟨⟨hdq, _⟩, hsf⟩ := hdf
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdq (by omega)
    have hdQ : d ≤ Q := le_trans (Nat.le_of_dvd (by omega) hdq) hqI.2
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_Icc.mpr hqI, hdq⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_Icc.mpr ⟨hd1, hdQ⟩, hsf⟩
  · rintro ⟨hqf, hdf⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hqf
    rw [Finset.mem_filter] at hdf
    obtain ⟨⟨hq1, hqQ⟩, hdq⟩ := hqf
    refine ⟨Finset.mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdq, by omega⟩, hdf.2⟩

/-- `∑_{q ∈ [1,Q], d ∣ q} 1 ≤ Q/d`. -/
lemma sum_ones_filter_dvd_le (Q d : ℕ) :
    ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) ≤ (Q : ℝ) / d := by
  have hIcc : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

/-- `0 ≤ 1 + log Q`. -/
lemma one_add_log_nonneg (Q : ℕ) : (0 : ℝ) ≤ 1 + Real.log Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  · have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith [Real.log_nonneg h1]

/-- **The harmonic reduction step.** `∑ (k+1)^{ω(q)}/q ≤ (1 + log Q) · ∑ k^{ω(q)}/q`. -/
lemma reduction_div (Q k : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card / q
      ≤ (1 + Real.log Q) * ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q := by
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card / q
        = ∑ d ∈ q.divisors.filter Squarefree,
            (k : ℝ) ^ d.primeFactors.card * ((1 : ℝ) / q) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [← Finset.sum_mul, ← pow_succ_omega_eq (by omega : q ≠ 0) k, mul_one_div]
  calc ∑ q ∈ Finset.Icc 1 Q, ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card / q
      = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ q.divisors.filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card * ((1 : ℝ) / q) := Finset.sum_congr rfl hterm
    _ = ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q),
            (k : ℝ) ^ d.primeFactors.card * ((1 : ℝ) / q) :=
        Finset.sum_comm' (fun q d => mem_swap_iff Q q d)
    _ = ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card
            * ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card * ((1 + Real.log Q) / d) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        exact mul_le_mul_of_nonneg_left
          (Salt.LS.sum_inv_dvd_multiples_le d Q hd.1.1 hd.1.2) (by positivity)
    _ = (1 + Real.log Q) * ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card / d := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (1 + Real.log Q) * ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q := by
        refine mul_le_mul_of_nonneg_left ?_ (one_add_log_nonneg Q)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)

/-- **The count reduction step.** `∑ (k+1)^{ω(q)} ≤ Q · ∑ k^{ω(q)}/q`. -/
lemma reduction_count (Q k : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card
      ≤ (Q : ℝ) * ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q := by
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card
        = ∑ d ∈ q.divisors.filter Squarefree, (k : ℝ) ^ d.primeFactors.card * (1 : ℝ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [← Finset.sum_mul, ← pow_succ_omega_eq (by omega : q ≠ 0) k, mul_one]
  calc ∑ q ∈ Finset.Icc 1 Q, ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card
      = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ q.divisors.filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card * (1 : ℝ) := Finset.sum_congr rfl hterm
    _ = ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q),
            (k : ℝ) ^ d.primeFactors.card * (1 : ℝ) :=
        Finset.sum_comm' (fun q d => mem_swap_iff Q q d)
    _ = ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card
            * ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card * ((Q : ℝ) / d) := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact mul_le_mul_of_nonneg_left (sum_ones_filter_dvd_le Q d) (by positivity)
    _ = (Q : ℝ) * ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
          (k : ℝ) ^ d.primeFactors.card / d := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (Q : ℝ) * ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg Q)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)

/-- **Target 2: the harmonic divisor-power sum.**  `∑_{q ≤ Q} k^{ω(q)}/q ≤ (1 + log Q)^k`
for every `k` (`C₀ = 1`, exponent `= k`).  Induction on `k`: the `0` case isolates the single
`q = 1` term; the step is `reduction_div`. -/
theorem sum_k_pow_omega_div_le (Q k : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q ≤ (1 + Real.log Q) ^ k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, pow_zero]
    have hle : ∀ q ∈ Finset.Icc 1 Q,
        (0 : ℝ) ^ q.primeFactors.card / q ≤ if q = 1 then (1 : ℝ) else 0 := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      by_cases hq1 : q = 1
      · subst hq1; simp [Nat.primeFactors_one]
      · have hne : q.primeFactors.card ≠ 0 := by
          rw [Finset.card_ne_zero, Nat.nonempty_primeFactors]; omega
        rw [zero_pow hne, zero_div, if_neg hq1]
    calc ∑ q ∈ Finset.Icc 1 Q, (0 : ℝ) ^ q.primeFactors.card / q
        ≤ ∑ q ∈ Finset.Icc 1 Q, if q = 1 then (1 : ℝ) else 0 := Finset.sum_le_sum hle
      _ ≤ 1 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : ((Finset.Icc 1 Q).filter (fun q => q = 1)).card ≤ 1 :=
            Finset.card_le_one.mpr (fun a ha b hb => by
              rw [Finset.mem_filter] at ha hb; rw [ha.2, hb.2])
          calc (((Finset.Icc 1 Q).filter (fun q => q = 1)).card : ℝ)
              ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcard
            _ = 1 := by norm_num
  | succ k ih =>
    calc ∑ q ∈ Finset.Icc 1 Q, ((k + 1 : ℕ) : ℝ) ^ q.primeFactors.card / q
        ≤ (1 + Real.log Q) * ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card / q :=
          reduction_div Q k
      _ ≤ (1 + Real.log Q) * (1 + Real.log Q) ^ k :=
          mul_le_mul_of_nonneg_left ih (one_add_log_nonneg Q)
      _ = (1 + Real.log Q) ^ (k + 1) := by rw [pow_succ]; ring

/-- **Target 1: the divisor-power sum.**  `∑_{q ≤ Q} k^{ω(q)} ≤ Q · (1 + log Q)^{k−1}`
for `1 ≤ k` (`C₀ = 1`, exponent `= k − 1`).  `reduction_count` peels one factor and the
residual harmonic sum is bounded by `sum_k_pow_omega_div_le`. -/
theorem sum_k_pow_omega_le (Q k : ℕ) (hk : 1 ≤ k) :
    ∑ q ∈ Finset.Icc 1 Q, (k : ℝ) ^ q.primeFactors.card
      ≤ (Q : ℝ) * (1 + Real.log Q) ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc ∑ q ∈ Finset.Icc 1 Q, ((m + 1 : ℕ) : ℝ) ^ q.primeFactors.card
      ≤ (Q : ℝ) * ∑ q ∈ Finset.Icc 1 Q, (m : ℝ) ^ q.primeFactors.card / q :=
        reduction_count Q m
    _ ≤ (Q : ℝ) * (1 + Real.log Q) ^ m :=
        mul_le_mul_of_nonneg_left (sum_k_pow_omega_div_le Q m) (Nat.cast_nonneg Q)

end Salt.Maynard
