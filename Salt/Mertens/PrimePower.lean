/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.MertensDischarge

/-!
# The prime-power correction constant `B` (MERTENS arc, node MERT-2)

The Mertens constant decomposition writes, for the Euler product over primes,
`-log ∏_{p ≤ x} (1 - 1/p) = (∑_{p ≤ x} 1/p) + B_x`, where the *prime-power
correction* collects the higher terms of the Mercator series
`-log(1 - 1/p) = ∑_{k ≥ 1} p^{-k}/k`.  Peeling off the `k = 1` term `1/p`
leaves the tail `∑_{k ≥ 2} p^{-k}/k`, and

`B := ∑_p ∑_{k ≥ 2} p^{-k}/k`

is a convergent double series (the *prime-power constant*).  This file provides:

* `mertensB` — the constant, as a double `tsum` (inner sum reindexed `k ↦ k+2`);
* `mertensB_summable`, `mertensB_nonneg`, `mertensB_le_two` — convergence, sign,
  and an explicit upper bound;
* `neg_log_prod_eq` — the finite Euler-product bridge identity over any finite
  set of primes;
* `mertensB_tail_le` — the `p > x` tail estimate `|B - B_x| ≤ 2/(x-1)`.

The per-prime engine is `Real.hasSum_pow_div_log_of_abs_lt_one`
(`-log(1-x) = ∑' x^(n+1)/(n+1)`); the `p`-series tail uses the corpus
`Salt.BrunLower.sum_one_div_sq_le`.
-/

namespace Salt.Mertens

open scoped BigOperators

/-! ## The inner prime-power sum `∑_{k ≥ 2} p^{-k}/k` -/

/-- For a prime-sized modulus `p ≥ 2`, the ratio `1/p` has absolute value `< 1`. -/
lemma inv_prime_abs_lt_one (p : ℕ) (hp : 2 ≤ p) : |1 / (p : ℝ)| < 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < 1 / (p : ℝ) := div_pos one_pos hp0
  rw [abs_of_pos hpos, div_lt_one hp0]
  have : (1 : ℝ) < (p : ℝ) := by
    have : 1 < p := by omega
    exact_mod_cast this
  linarith

/-- `B_p := ∑_{k ≥ 2} p^{-k}/k`, indexed with `k ↦ k + 2`, so the summand is
`1 / ((k+2) · p^(k+2))`. -/
noncomputable def ppInner (p : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2))

/-- The inner sum is nonnegative (each term is). -/
lemma ppInner_nonneg (p : ℕ) : 0 ≤ ppInner p :=
  tsum_nonneg (fun _ => by positivity)

/-- The key termwise geometric domination: `1/((k+2)·p^(k+2)) ≤ (1/p)^2 · (1/2)^k`
for `p ≥ 2`. -/
lemma ppInner_term_le (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2)) ≤ (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hxpos : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hxle : (1 / (p : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hp
  have e1 : 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2))
      = (1 / (p : ℝ)) ^ (k + 2) / ((k : ℝ) + 2) := by
    rw [one_div_pow, div_div]
    ring
  rw [e1]
  calc (1 / (p : ℝ)) ^ (k + 2) / ((k : ℝ) + 2)
      ≤ (1 / (p : ℝ)) ^ (k + 2) := by
        apply div_le_self (by positivity)
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
    _ = (1 / (p : ℝ)) ^ k * (1 / (p : ℝ)) ^ 2 := by rw [pow_add]
    _ ≤ (1 / 2 : ℝ) ^ k * (1 / (p : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ hxpos hxle k
    _ = (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k := by ring

/-- The inner sum converges (geometric domination). -/
lemma ppInner_summable (p : ℕ) (hp : 2 ≤ p) :
    Summable (fun k : ℕ => 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2))) := by
  have hmaj : Summable (fun k : ℕ => (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun k => ppInner_term_le p hp k) hmaj

/-- Explicit per-prime bound: `B_p ≤ 2/p²`. -/
lemma ppInner_le (p : ℕ) (hp : 2 ≤ p) : ppInner p ≤ 2 / (p : ℝ) ^ 2 := by
  have hmaj : Summable (fun k : ℕ => (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ppInner p
      ≤ ∑' k : ℕ, (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum (fun k => ppInner_term_le p hp k)
          (ppInner_summable p hp) hmaj
    _ = (1 / (p : ℝ)) ^ 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := tsum_mul_left
    _ = (1 / (p : ℝ)) ^ 2 * 2 := by rw [tsum_geometric_two]
    _ = 2 / (p : ℝ) ^ 2 := by rw [one_div_pow]; ring

/-- The Mercator identity, peeled: `B_p = -log(1 - 1/p) - 1/p`. -/
lemma ppInner_eq (p : ℕ) (hp : 2 ≤ p) :
    ppInner p = -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) := by
  have key : -Real.log (1 - 1 / (p : ℝ)) = 1 / (p : ℝ) + ppInner p := by
    have hHS := Real.hasSum_pow_div_log_of_abs_lt_one (inv_prime_abs_lt_one p hp)
    rw [← hHS.tsum_eq, hHS.summable.tsum_eq_zero_add]
    congr 1
    · simp
    · rw [ppInner]
      apply tsum_congr
      intro n
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [one_div_pow]
      push_cast
      field_simp
      ring
  linarith [key]

/-! ## The Euler-product bridge (finite version) -/

/-- **Euler-product bridge.** For any finite set `S` of primes,
`-log ∏_{p ∈ S} (1 - 1/p) = (∑_{p ∈ S} 1/p) + ∑_{p ∈ S} B_p`. -/
lemma neg_log_prod_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    -Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ)))
      = (∑ p ∈ S, 1 / (p : ℝ)) + ∑ p ∈ S, ppInner p := by
  have hne : ∀ p ∈ S, (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
    intro p hp
    have hlt : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast (show 0 < p from (hS p hp).pos))]
      exact_mod_cast (hS p hp).one_lt
    linarith
  have hterm : ∀ p ∈ S, Real.log (1 - 1 / (p : ℝ)) = -(1 / (p : ℝ) + ppInner p) := by
    intro p hp
    rw [ppInner_eq p (hS p hp).two_le]; ring
  rw [Real.log_prod hne, Finset.sum_congr rfl hterm,
    Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib]

/-! ## The constant `B` -/

/-- The prime-power correction constant `B = ∑_p ∑_{k ≥ 2} p^{-k}/k`. -/
noncomputable def mertensB : ℝ := ∑' p : Nat.Primes, ppInner (p : ℕ)

/-- `mertensB` is the double series from the blueprint. -/
lemma mertensB_eq_double_tsum :
    mertensB = ∑' p : Nat.Primes, ∑' k : ℕ, 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2)) := rfl

/-- `B ≥ 0`. -/
lemma mertensB_nonneg : 0 ≤ mertensB := tsum_nonneg (fun _ => ppInner_nonneg _)

/-- The comparison `p`-series `∑_n 2/n²` converges. -/
lemma summable_two_div_sq : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  exact (h.mul_left 2).congr (fun n => by ring)

/-- The double series defining `B` converges. -/
lemma mertensB_summable : Summable (fun p : Nat.Primes => ppInner (p : ℕ)) :=
  Summable.of_nonneg_of_le (fun _ => ppInner_nonneg _)
    (fun p => ppInner_le _ p.2.two_le) (summable_two_div_sq.subtype _)

/-! ## The tail estimate and the explicit bound -/

/-- The prime-indicator bound on `ℕ`: `𝟙_{prime}(n) · B_n ≤ 2/n²` for every `n`. -/
lemma indicator_ppInner_le (n : ℕ) :
    Set.indicator {p : ℕ | Nat.Prime p} ppInner n ≤ 2 / (n : ℝ) ^ 2 := by
  rw [Set.indicator_apply]
  by_cases hp : n ∈ {p : ℕ | Nat.Prime p}
  · rw [if_pos hp]
    have hpr : Nat.Prime n := hp
    exact ppInner_le n hpr.two_le
  · rw [if_neg hp]; positivity

/-- `B` as a single `tsum` over `ℕ` with the prime indicator. -/
lemma mertensB_eq_tsum_indicator :
    mertensB = ∑' n : ℕ, Set.indicator {p : ℕ | Nat.Prime p} ppInner n :=
  tsum_subtype {p : ℕ | Nat.Prime p} ppInner

/-- Partial sum `B_N := ∑_{p < N} B_p` (primes below the natural cutoff `N`). -/
noncomputable def mertensB_partial (N : ℕ) : ℝ := ∑ p ∈ Nat.primesBelow N, ppInner p

/-- **Tail estimate.** For `N ≥ 2`, `|B - B_N| ≤ 2/(N-1)`. -/
lemma mertensB_tail_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensB - mertensB_partial N| ≤ 2 / ((N : ℝ) - 1) := by
  set f : ℕ → ℝ := Set.indicator {p : ℕ | Nat.Prime p} ppInner with hf
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n; rw [hf]; exact Set.indicator_nonneg (fun m _ => ppInner_nonneg m) n
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg (fun n => indicator_ppInner_le n) summable_two_div_sq
  have hB : mertensB = ∑' n, f n := mertensB_eq_tsum_indicator
  have hpart : mertensB_partial N = ∑ n ∈ Finset.range N, f n := by
    rw [mertensB_partial, hf,
      show Nat.primesBelow N = Finset.filter (fun p => Nat.Prime p) (Finset.range N) from rfl,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have htail : mertensB - mertensB_partial N = ∑' i, f (i + N) := by
    have hsplit := Summable.sum_add_tsum_nat_add N hf_summable
    rw [hB, hpart]; linarith [hsplit]
  rw [htail, abs_of_nonneg (tsum_nonneg (fun i => hf_nonneg (i + N)))]
  have hmaj_sum : Summable (fun i : ℕ => 2 / ((i + N : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff N).mpr summable_two_div_sq
  have hshift_sum : Summable (fun i : ℕ => f (i + N)) :=
    (summable_nat_add_iff N).mpr hf_summable
  calc ∑' i, f (i + N)
      ≤ ∑' i, 2 / ((i + N : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum (fun i => indicator_ppInner_le (i + N)) hshift_sum hmaj_sum
    _ ≤ 2 / ((N : ℝ) - 1) := by
        apply Summable.tsum_le_of_sum_range_le hmaj_sum
        intro K
        have hrange : ∑ i ∈ Finset.range K, 1 / ((i + N : ℕ) : ℝ) ^ 2
            = ∑ j ∈ Finset.Ico N (N + K), 1 / (j : ℝ) ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel_left]
          apply Finset.sum_congr rfl
          intro i _
          rw [Nat.add_comm N i]
        have hle : ∑ j ∈ Finset.Ico N (N + K), 1 / (j : ℝ) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
          calc ∑ j ∈ Finset.Ico N (N + K), 1 / (j : ℝ) ^ 2
              ≤ ∑ j ∈ Finset.Icc N (N + K), 1 / (j : ℝ) ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
                  (fun j _ _ => by positivity)
            _ ≤ 1 / ((N : ℝ) - 1) := Salt.BrunLower.sum_one_div_sq_le hN
        calc ∑ i ∈ Finset.range K, 2 / ((i + N : ℕ) : ℝ) ^ 2
            = 2 * ∑ i ∈ Finset.range K, 1 / ((i + N : ℕ) : ℝ) ^ 2 := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          _ = 2 * ∑ j ∈ Finset.Ico N (N + K), 1 / (j : ℝ) ^ 2 := by rw [hrange]
          _ ≤ 2 * (1 / ((N : ℝ) - 1)) := by
              apply mul_le_mul_of_nonneg_left hle (by norm_num)
          _ = 2 / ((N : ℝ) - 1) := by ring

/-- Explicit upper bound `B ≤ 2` (the `N = 2` tail bound: no primes below `2`). -/
lemma mertensB_le_two : mertensB ≤ 2 := by
  have h := mertensB_tail_le 2 (le_refl 2)
  rw [mertensB_partial, Nat.primesBelow_two, Finset.sum_empty, sub_zero,
    abs_of_nonneg mertensB_nonneg] at h
  norm_num at h
  exact h

end Salt.Mertens
