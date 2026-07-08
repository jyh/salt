/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard
import Salt.Maynard.Rankin

/-!
# N5.2 — the EH consumption

The single most important use of the level-of-distribution hypothesis `EH`.
We bound the `(3k)^{ω(q)}`-weighted sum of prime-count discrepancies over
squarefree moduli `q < ⌊√N⌋ + 1` by `C · N / (log N)^2`.

## Route (Cauchy–Schwarz)

Write `w q = (3k)^{ω q}`, `D q = maxDiscrepancy N q`, and sum over
`S = (range Q).filter Squarefree` with `Q = ⌊N^{1/2}⌋₊ + 1`. Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) gives

  `(Σ w·D)² ≤ (Σ w²·D) · (Σ D)`.

* The **Rankin factor** `Σ w²·D`: with the trivial discrepancy bound
  `D q ≤ N/φ(q) + 1` (N0.2) and `w² = (9k²)^{ω}`, Rankin's bound
  (`rankin_bound` at `L = 9k²`) controls `Σ (9k²)^ω/φ(q) ≤ (C₁ log Q)^{9k²}`,
  a fixed power of `log`.  This yields `Σ w²·D ≤ 2N (C₁ log N)^{9k²}`.
* The **EH factor** `Σ D`: dominated by the full `Icc 1 ⌊√N⌋` sum, which `EH
  (1/2)` bounds by `CA · N / (log N)^A` for **any** `A`.  Choosing
  `A = 9k² + 4` past the Rankin power makes the product

  `(Σ w·D)² ≤ 2N(C₁ log N)^{9k²} · CA N/(log N)^{9k²+4}
           = (2 CA C₁^{9k²}) · N² / (log N)^4`,

  and taking square roots gives the `N/(log N)^2` bound with
  `C = √(2 CA C₁^{9k²})`.

The `∀A` strength of `EH` is exactly what defeats the fixed-power Rankin
factor. Class C.
-/

open Finset

namespace Salt.Maynard

/-- **Trivial discrepancy bound** (from N0.2 `primesCount_le` and `π(x) ≤ x`).
For every modulus `q`, `maxDiscrepancy N q ≤ N/φ(q) + 1`.  Both
`π(N;q,a) ≤ N/q + 1 ≤ N/φ(q) + 1` and `π(N)/φ(q) ≤ (N+1)/φ(q) ≤ N/φ(q) + 1`
are bounded by the same `M`, so their difference is too. -/
theorem maxDiscrepancy_le_trivial (N q : ℕ) :
    maxDiscrepancy N q ≤ (N : ℝ) / (Nat.totient q : ℝ) + 1 := by
  unfold maxDiscrepancy
  split
  · positivity
  · rename_i hq
    rw [Finset.sup'_le_iff]
    intro a ha
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hφ1N : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hqpos
    have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hφ1N
    have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast hφ1N
    -- bound A := π(N;q,a)
    have hA1 : (primesCount N q a : ℝ) ≤ (N : ℝ) / (Nat.totient q : ℝ) + 1 := by
      have h := primesCount_le N q a hq
      have hcast : (primesCount N q a : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by exact_mod_cast h
      have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) := Nat.cast_div_le
      have hqle : (N : ℝ) / (q : ℝ) ≤ (N : ℝ) / (Nat.totient q : ℝ) := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div (N : ℝ) (Nat.totient q : ℝ)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact one_div_le_one_div_of_le hφpos (by exact_mod_cast Nat.totient_le q)
      linarith [hcast, hdiv, hqle]
    have hA0 : (0 : ℝ) ≤ (primesCount N q a : ℝ) := by positivity
    -- bound B := π(N)/φ(q)
    have hB1 : (primesCount N 1 0 : ℝ) / (Nat.totient q : ℝ)
        ≤ (N : ℝ) / (Nat.totient q : ℝ) + 1 := by
      have h := primesCount_le N 1 0 (by norm_num)
      have hcast : (primesCount N 1 0 : ℝ) ≤ (N : ℝ) + 1 := by
        have h' : primesCount N 1 0 ≤ N / 1 + 1 := h
        simp only [Nat.div_one] at h'
        exact_mod_cast h'
      rw [div_le_iff₀ hφpos]
      have heq : ((N : ℝ) / (Nat.totient q : ℝ) + 1) * (Nat.totient q : ℝ)
          = (N : ℝ) + (Nat.totient q : ℝ) := by field_simp
      rw [heq]
      linarith [hcast, hφ1]
    have hB0 : (0 : ℝ) ≤ (primesCount N 1 0 : ℝ) / (Nat.totient q : ℝ) := by positivity
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- **N5.2 — EH consumption.** Under `EH (1/2)`, the `(3k)^{ω(q)}`-weighted
sum of maximal prime-count discrepancies over squarefree moduli
`q < ⌊N^{1/2}⌋₊ + 1` is `≤ C · N / (log N)^2` for `N` large — small enough to
be absorbed by the main term.  `C = √(2·CA·C₁^{9k²})` with `C₁` the Rankin
constant at `L = 9k²` and `CA` the `EH` constant at level `A = 9k² + 4`. -/
theorem eh_error_small (k : ℕ) (hEH : EH (1 / 2)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (Finset.range (⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1)).filter Squarefree,
          ((3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
        ≤ C * (N : ℝ) / (Real.log N) ^ 2 := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound (9 * k ^ 2)
  obtain ⟨CA, hCA⟩ := hEH ((9 * k ^ 2 + 4 : ℕ) : ℝ) (by positivity)
  refine ⟨Real.sqrt (2 * CA * C₁ ^ (9 * k ^ 2)), 2, ?_⟩
  intro N hN2
  -- basic real facts
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1R : (1 : ℝ) < (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1R
  set qmax := ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊ with hqmax
  set S := (Finset.range (qmax + 1)).filter Squarefree with hSdef
  -- Q = qmax + 1 facts
  have hqmax1 : 1 ≤ qmax := by
    rw [hqmax]
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hQ2 : 2 ≤ qmax + 1 := by omega
  have hQleN : qmax + 1 ≤ N := by
    have hlt : qmax < N := by
      rw [hqmax, Nat.floor_lt (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ))]
      have h := Real.rpow_lt_rpow_of_exponent_lt hN1R (by norm_num : (1 / 2 : ℝ) < 1)
      rwa [Real.rpow_one] at h
    omega
  have hQNreal : ((qmax + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hQleN
  have hQ1r : (1 : ℝ) ≤ ((qmax + 1 : ℕ) : ℝ) := by
    have : 1 ≤ qmax + 1 := by omega
    exact_mod_cast this
  set LHS := ∑ q ∈ S, ((3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q) with hLHS
  -- ===== Cauchy–Schwarz setup =====
  have hfg : ∑ q ∈ S, ((3 * k : ℝ) ^ q.primeFactors.card * Real.sqrt (maxDiscrepancy N q))
        * Real.sqrt (maxDiscrepancy N q) = LHS := by
    rw [hLHS]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [mul_assoc, Real.mul_self_sqrt (maxDiscrepancy_nonneg N q)]
  have hff : ∑ q ∈ S, ((3 * k : ℝ) ^ q.primeFactors.card * Real.sqrt (maxDiscrepancy N q)) ^ 2
        = ∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [mul_pow, Real.sq_sqrt (maxDiscrepancy_nonneg N q)]
    congr 1
    rw [← pow_mul, mul_comm q.primeFactors.card 2, pow_mul]
    congr 1
    push_cast; ring
  have hgg : ∑ q ∈ S, (Real.sqrt (maxDiscrepancy N q)) ^ 2 = ∑ q ∈ S, maxDiscrepancy N q :=
    Finset.sum_congr rfl (fun q _ => Real.sq_sqrt (maxDiscrepancy_nonneg N q))
  have hLHSsq : LHS ^ 2
      ≤ (∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
        * (∑ q ∈ S, maxDiscrepancy N q) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun q => (3 * k : ℝ) ^ q.primeFactors.card * Real.sqrt (maxDiscrepancy N q))
      (fun q => Real.sqrt (maxDiscrepancy N q))
    rw [hfg, hff, hgg] at hcs
    exact hcs
  -- ===== EH factor: Σ D ≤ CA · N / (log N)^{9k²+4} =====
  have hsub : S ⊆ Finset.Icc 1 qmax := by
    intro q hq
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqlt, hqsf⟩ := hq
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hqsf.ne_zero, by omega⟩
  have hE : (∑ q ∈ S, maxDiscrepancy N q) ≤ CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 4) := by
    calc (∑ q ∈ S, maxDiscrepancy N q)
        ≤ ∑ q ∈ Finset.Icc 1 qmax, maxDiscrepancy N q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => maxDiscrepancy_nonneg N q)
      _ ≤ CA * (N : ℝ) / (Real.log N) ^ ((9 * k ^ 2 + 4 : ℕ) : ℝ) := hCA N hN2
      _ = CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 4) := by rw [Real.rpow_natCast]
  have hEnn : 0 ≤ ∑ q ∈ S, maxDiscrepancy N q :=
    Finset.sum_nonneg (fun q _ => maxDiscrepancy_nonneg N q)
  have hCAnn : 0 ≤ CA := by
    by_contra hcon
    rw [not_le] at hcon
    have hden : 0 < (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 4) := div_pos hNpos (pow_pos hlogN _)
    have hbad : CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 4) < 0 := by
      rw [mul_div_assoc]
      exact mul_neg_of_neg_of_pos hcon hden
    linarith [hE, hEnn]
  -- ===== Rankin factor: Σ w²·D ≤ 2N (C₁ log N)^{9k²} =====
  have hP : (∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
      ≤ 2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2) := by
    have hterm : ∀ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q
        ≤ 2 * (N : ℝ) * (((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) := by
      intro q hq
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨hqlt, hqsf⟩ := hq
      set t := ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card with ht
      have htnn : 0 ≤ t := by positivity
      have hqpos : 0 < q := Nat.pos_of_ne_zero hqsf.ne_zero
      have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hφN : (Nat.totient q : ℝ) ≤ (N : ℝ) := by
        have h1 : Nat.totient q ≤ q := Nat.totient_le q
        have h2 : q ≤ N := by omega
        exact_mod_cast le_trans h1 h2
      have hD := maxDiscrepancy_le_trivial N q
      have key1 : t * maxDiscrepancy N q ≤ t * ((N : ℝ) / (Nat.totient q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hD htnn
      have hstep : t ≤ (N : ℝ) * t / (Nat.totient q : ℝ) := by
        rw [le_div_iff₀ hφpos]
        nlinarith [mul_nonneg htnn (sub_nonneg.mpr hφN)]
      have key2 : t * ((N : ℝ) / (Nat.totient q : ℝ) + 1)
          ≤ 2 * (N : ℝ) * (t / (Nat.totient q : ℝ)) := by
        have e1 : t * ((N : ℝ) / (Nat.totient q : ℝ) + 1)
            = (N : ℝ) * t / (Nat.totient q : ℝ) + t := by ring
        have e2 : 2 * (N : ℝ) * (t / (Nat.totient q : ℝ))
            = (N : ℝ) * t / (Nat.totient q : ℝ) + (N : ℝ) * t / (Nat.totient q : ℝ) := by ring
        rw [e1, e2]; linarith [hstep]
      exact key1.trans key2
    have hRank : ∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
        ≤ (C₁ * Real.log ((qmax + 1 : ℕ) : ℝ)) ^ (9 * k ^ 2) := by
      have h := hC₁ (qmax + 1) hQ2
      rw [← hSdef] at h
      exact h
    have hbase : 0 ≤ C₁ * Real.log ((qmax + 1 : ℕ) : ℝ) :=
      mul_nonneg (by linarith) (Real.log_nonneg hQ1r)
    have hmono : C₁ * Real.log ((qmax + 1 : ℕ) : ℝ) ≤ C₁ * Real.log N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply (Real.log_le_log_iff (by positivity) hNpos).mpr hQNreal
    calc ∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q
        ≤ ∑ q ∈ S, 2 * (N : ℝ)
            * (((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 2 * (N : ℝ)
            * ∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (N : ℝ) * (C₁ * Real.log ((qmax + 1 : ℕ) : ℝ)) ^ (9 * k ^ 2) :=
          mul_le_mul_of_nonneg_left hRank (by positivity)
      _ ≤ 2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hbase hmono _
  -- ===== combine =====
  have hPnn : 0 ≤ ∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg N q))
  have hbP : 0 ≤ 2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2) :=
    mul_nonneg (by positivity) (pow_nonneg (mul_nonneg (by linarith) (le_of_lt hlogN)) _)
  set Kc := 2 * CA * C₁ ^ (9 * k ^ 2) with hKc
  have hKcnn : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg (by norm_num) hCAnn) (pow_nonneg (by linarith) _)
  have hlogNne : Real.log N ≠ 0 := ne_of_gt hlogN
  have h1ne : (Real.log N) ^ (9 * k ^ 2) ≠ 0 := pow_ne_zero _ hlogNne
  have h4ne : (Real.log N) ^ 4 ≠ 0 := pow_ne_zero _ hlogNne
  have hchain : LHS ^ 2 ≤ Kc * (N : ℝ) ^ 2 / (Real.log N) ^ 4 := by
    calc LHS ^ 2
        ≤ (∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
            * (∑ q ∈ S, maxDiscrepancy N q) := hLHSsq
      _ ≤ (2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2))
            * (CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 4)) :=
          mul_le_mul hP hE hEnn hbP
      _ = Kc * (N : ℝ) ^ 2 / (Real.log N) ^ 4 := by
          rw [hKc, mul_pow, pow_add]
          field_simp
  -- take square roots
  have hsq : (Real.sqrt Kc) ^ 2 = Kc := Real.sq_sqrt hKcnn
  have htgt : (Real.sqrt Kc * (N : ℝ) / (Real.log N) ^ 2) ^ 2
      = Kc * (N : ℝ) ^ 2 / (Real.log N) ^ 4 := by
    rw [div_pow, mul_pow, hsq]; ring
  refine (abs_le_of_sq_le_sq' ?_ ?_).2
  · rw [htgt]; exact hchain
  · positivity

end Salt.Maynard
