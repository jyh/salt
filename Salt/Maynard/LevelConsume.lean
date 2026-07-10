/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard
import Salt.Maynard.Rankin
import Salt.Maynard.EHConsume
import Salt.Maynard.Level
import Salt.Maynard.FrontierFinal
import Salt.Maynard.Complete

/-!
# Rung 4b — EH consumption under `HasLevel` (`lod_error_pow`)

Design: `docs/blueprints/lod-interface-design.md`, node L2.  The `eh_error_pow`
analog under the BV-shaped `HasLevel (1/2)`: identical Cauchy–Schwarz +
Rankin + level bound, with the modulus range shrunk from `⌊√N⌋` to the haircut
range `⌊√N/(log N)^B'⌋` that `HasLevel` controls.  The sieve's real moduli
(`W·R² ≈ N^{2/5}`) sit well inside this shrunk range, so the downstream
consumer (`S2m_ge_compatMain_lod`) is unaffected.
-/

open Finset Filter

namespace Salt.Maynard

/-- **L2 — the level-of-distribution error bound.** Under `HasLevel (1/2)`, the
`(3k)^ω`-weighted discrepancy over squarefree moduli `≤ √N/(log N)^B'` is
`O(N/(log N)^B)`.  Same proof as `eh_error_pow`; only the modulus range shrinks
to the `HasLevel` haircut `B'` (existentially returned). -/
theorem lod_error_pow (k B : ℕ) (hB : 1 ≤ B) (hLoD : HasLevel (1 / 2)) :
    ∃ (C B' : ℝ) (N₀ : ℕ), 0 ≤ B' ∧ ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (Finset.range (⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊ + 1)).filter Squarefree,
          ((3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
        ≤ C * (N : ℝ) / (Real.log N) ^ B := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound (9 * k ^ 2)
  obtain ⟨B', CA, hB'0, hCA⟩ := hLoD ((9 * k ^ 2 + 2 * B : ℕ) : ℝ) (by
    have h : 0 < 9 * k ^ 2 + 2 * B := by omega
    exact_mod_cast h)
  refine ⟨Real.sqrt (2 * CA * C₁ ^ (9 * k ^ 2)), B', 3, hB'0, ?_⟩
  intro N hN3
  -- basic real facts
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN1R : (1 : ℝ) < (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1R
  have hlog1 : 1 ≤ Real.log N := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; linarith
      _ ≤ (N : ℝ) := hNR
  have hlogB'pos : (0 : ℝ) < (Real.log N) ^ B' := Real.rpow_pos_of_pos hlogN B'
  have hlogB'ge1 : (1 : ℝ) ≤ (Real.log N) ^ B' := Real.one_le_rpow hlog1 hB'0
  set qmax := ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊ with hqmax
  set S := (Finset.range (qmax + 1)).filter Squarefree with hSdef
  set LHS := ∑ q ∈ S, ((3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q) with hLHS
  -- `qmax ≤ ⌊√N⌋ < N`
  have hsqrtN : (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B' ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hlogB'pos]
    nlinarith [Real.rpow_nonneg hNpos.le (1 / 2 : ℝ), hlogB'ge1]
  have hqmaxleN : qmax < N := by
    have h1 : qmax ≤ ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊ := Nat.floor_le_floor hsqrtN
    have h2 : ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊ < N := by
      rw [Nat.floor_lt (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ))]
      have h := Real.rpow_lt_rpow_of_exponent_lt hN1R (by norm_num : (1 / 2 : ℝ) < 1)
      rwa [Real.rpow_one] at h
    omega
  by_cases hq0 : qmax = 0
  · -- trivial: `S = ∅` (only `0 ∈ range 1`, and `0` is not squarefree)
    have hSempty : S = ∅ := by
      rw [hSdef, hq0]
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq
      rw [Finset.mem_range] at hq
      interval_cases q
      exact not_squarefree_zero
    rw [hLHS, hSempty, Finset.sum_empty]
    positivity
  · have hqmax1 : 1 ≤ qmax := Nat.one_le_iff_ne_zero.mpr hq0
    have hQ2 : 2 ≤ qmax + 1 := by omega
    have hQleN : qmax + 1 ≤ N := by omega
    have hQNreal : ((qmax + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hQleN
    have hQ1r : (1 : ℝ) ≤ ((qmax + 1 : ℕ) : ℝ) := by
      have : 1 ≤ qmax + 1 := by omega
      exact_mod_cast this
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
    -- ===== level factor: Σ D ≤ CA · N / (log N)^{9k²+2B} =====
    have hsub : S ⊆ Finset.Icc 1 qmax := by
      intro q hq
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨hqlt, hqsf⟩ := hq
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr hqsf.ne_zero, by omega⟩
    have hE : (∑ q ∈ S, maxDiscrepancy N q)
        ≤ CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 2 * B) := by
      calc (∑ q ∈ S, maxDiscrepancy N q)
          ≤ ∑ q ∈ Finset.Icc 1 qmax, maxDiscrepancy N q :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => maxDiscrepancy_nonneg N q)
        _ ≤ CA * (N : ℝ) / (Real.log N) ^ ((9 * k ^ 2 + 2 * B : ℕ) : ℝ) := hCA N (by omega)
        _ = CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 2 * B) := by rw [Real.rpow_natCast]
    have hEnn : 0 ≤ ∑ q ∈ S, maxDiscrepancy N q :=
      Finset.sum_nonneg (fun q _ => maxDiscrepancy_nonneg N q)
    have hCAnn : 0 ≤ CA := by
      by_contra hcon
      rw [not_le] at hcon
      have hden : 0 < (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 2 * B) :=
        div_pos hNpos (pow_pos hlogN _)
      have hbad : CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 2 * B) < 0 := by
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
    have hbP : 0 ≤ 2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2) :=
      mul_nonneg (by positivity) (pow_nonneg (mul_nonneg (by linarith) (le_of_lt hlogN)) _)
    set Kc := 2 * CA * C₁ ^ (9 * k ^ 2) with hKc
    have hKcnn : 0 ≤ Kc := by
      rw [hKc]
      exact mul_nonneg (mul_nonneg (by norm_num) hCAnn) (pow_nonneg (by linarith) _)
    have hlogNne : Real.log N ≠ 0 := ne_of_gt hlogN
    have hchain : LHS ^ 2 ≤ Kc * (N : ℝ) ^ 2 / (Real.log N) ^ (2 * B) := by
      calc LHS ^ 2
          ≤ (∑ q ∈ S, ((9 * k ^ 2 : ℕ) : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q)
              * (∑ q ∈ S, maxDiscrepancy N q) := hLHSsq
        _ ≤ (2 * (N : ℝ) * (C₁ * Real.log N) ^ (9 * k ^ 2))
              * (CA * (N : ℝ) / (Real.log N) ^ (9 * k ^ 2 + 2 * B)) :=
            mul_le_mul hP hE hEnn hbP
        _ = Kc * (N : ℝ) ^ 2 / (Real.log N) ^ (2 * B) := by
            rw [hKc, mul_pow, pow_add]
            field_simp
    have hsq : (Real.sqrt Kc) ^ 2 = Kc := Real.sq_sqrt hKcnn
    have htgt : (Real.sqrt Kc * (N : ℝ) / (Real.log N) ^ B) ^ 2
        = Kc * (N : ℝ) ^ 2 / (Real.log N) ^ (2 * B) := by
      rw [div_pow, mul_pow, hsq, ← pow_mul, mul_comm B 2]
    refine (abs_le_of_sq_le_sq' ?_ ?_).2
    · rw [htgt]; exact hchain
    · positivity

/-! ## L3a — the shrunk-range EH modulus bound (`EH_range_lod`) -/

/-- **L3a — shrunk-range `EH_range`.**  For a fixed haircut `B' ≥ 0`, the sieve
modulus range `W k₀ · R²` (with `R = ⌊N'^{1/5}⌋₊`) sits inside the shrunk range
`⌊N'^{1/2}/(log N')^{B'}⌋₊` once `N'` is large.  `W k₀` is a constant, so
`W·R² ≤ W·N'^{2/5}` and `W·(log N')^{B'} ≤ N'^{1/10}` eventually
(`eventually_poly_beats_polylog`). -/
theorem EH_range_lod (k₀ : ℕ) (B' : ℝ) (hB'0 : 0 ≤ B') :
    ∃ Nr : ℕ, ∀ N' : ℕ, Nr ≤ N' →
      W k₀ * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) ^ 2
        ≤ ⌊(N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B'⌋₊ := by
  have hWpos : (0 : ℝ) < (W k₀ : ℝ) := by
    have : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
    exact_mod_cast this
  have hev := eventually_poly_beats_polylog ⌈B'⌉₊ ((1 : ℝ) / 10) (W k₀ : ℝ) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨Nr0, hNr0⟩ := eventually_atTop.mp hevN
  refine ⟨max Nr0 3, fun N' hN' => ?_⟩
  have hNr0le : Nr0 ≤ N' := le_trans (le_max_left _ _) hN'
  have hN3 : 3 ≤ N' := le_trans (le_max_right _ _) hN'
  have hpoly : (W k₀ : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ ≤ (N' : ℝ) ^ ((1 : ℝ) / 10) :=
    hNr0 N' hNr0le
  have hx1 : (1 : ℝ) < (N' : ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hxpos : (0 : ℝ) < (N' : ℝ) := by linarith
  have hlogx : 0 < Real.log N' := Real.log_pos hx1
  have hdom : (Real.log N') ^ B' ≤ (1 + Real.log N') ^ ⌈B'⌉₊ := by
    calc (Real.log N') ^ B' ≤ (1 + Real.log N') ^ B' :=
          Real.rpow_le_rpow hlogx.le (by linarith) hB'0
      _ ≤ (1 + Real.log N') ^ (⌈B'⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil B')
      _ = (1 + Real.log N') ^ ⌈B'⌉₊ := Real.rpow_natCast _ _
  have hWlog : (W k₀ : ℝ) * (Real.log N') ^ B' ≤ (N' : ℝ) ^ ((1 : ℝ) / 10) := by
    calc (W k₀ : ℝ) * (Real.log N') ^ B'
        ≤ (W k₀ : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ :=
          mul_le_mul_of_nonneg_left hdom hWpos.le
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 10) := hpoly
  have hR2 : (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ ((2 : ℝ) / 5) :=
    R_sq_le N' (by omega)
  have hmul : (W k₀ : ℝ) * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2
      ≤ (N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B' := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogx B')]
    calc (W k₀ : ℝ) * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2 * (Real.log N') ^ B'
        = (W k₀ : ℝ) * (Real.log N') ^ B' * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2 := by ring
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 10) * (N' : ℝ) ^ ((2 : ℝ) / 5) :=
          mul_le_mul hWlog hR2 (by positivity) (by positivity)
      _ = (N' : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
  apply Nat.le_floor
  push_cast
  exact hmul

/-- Eventual monotonicity of the shrunk range `y^{1/2}/(log y)^{B'}` once
`2·B' ≤ log N`: for `2 ≤ N ≤ x` with `log N ≥ 2B'`, the haircut range at `N` is
`≤` the haircut range at `x`.  (The map is increasing for `y ≥ e^{2B'}`; the
threshold `log N ≥ 2B'` is folded into `S2m_ge_compatMain_lod_uniform`'s `N₀`.) -/
lemma range_haircut_mono (B' : ℝ) (hB'0 : 0 ≤ B') (N x : ℕ)
    (hN2 : 2 ≤ N) (hNx : N ≤ x) (hN2B' : 2 * B' ≤ Real.log N) :
    (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'
      ≤ (x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B' := by
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hxNR : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogNx : Real.log N ≤ Real.log x := Real.log_le_log hNpos hxNR
  have key : Real.log N / 2 - Real.log (Real.log N) * B'
      ≤ Real.log x / 2 - Real.log (Real.log x) * B' := by
    have hlogdiff : Real.log (Real.log x) - Real.log (Real.log N)
        ≤ (Real.log x - Real.log N) / Real.log N := by
      have hd : Real.log (Real.log x / Real.log N) ≤ Real.log x / Real.log N - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogx hlogN)
      rw [Real.log_div hlogx.ne' hlogN.ne'] at hd
      rw [sub_div, div_self hlogN.ne']
      linarith [hd]
    have hba : (0 : ℝ) ≤ Real.log x - Real.log N := by linarith
    have hstep : B' * (Real.log x - Real.log N) / Real.log N
        ≤ (Real.log x - Real.log N) / 2 := by
      rw [div_le_div_iff₀ hlogN (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hN2B', hba, mul_nonneg (show (0 : ℝ) ≤ Real.log N - 2 * B' by linarith) hba]
    have hchain : Real.log (Real.log x) * B' - Real.log (Real.log N) * B'
        ≤ (Real.log x - Real.log N) / 2 := by
      calc Real.log (Real.log x) * B' - Real.log (Real.log N) * B'
          = B' * (Real.log (Real.log x) - Real.log (Real.log N)) := by ring
        _ ≤ B' * ((Real.log x - Real.log N) / Real.log N) :=
            mul_le_mul_of_nonneg_left hlogdiff hB'0
        _ = B' * (Real.log x - Real.log N) / Real.log N := by ring
        _ ≤ (Real.log x - Real.log N) / 2 := hstep
    linarith [hchain]
  have hNe : (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'
      = Real.exp (Real.log N / 2 - Real.log (Real.log N) * B') := by
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hlogN, ← Real.exp_sub]
    congr 1; ring
  have hxe : (x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'
      = Real.exp (Real.log x / 2 - Real.log (Real.log x) * B') := by
    rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hlogx, ← Real.exp_sub]
    congr 1; ring
  rw [hNe, hxe]
  exact Real.exp_le_exp.mpr key

/-! ## L3b — R-uniform LoD consumption (`S2m_ge_compatMain_lod_uniform`) -/

/-- **L3b — R-uniform LoD consumption.**  The `S2m_ge_compatMain_eh_uniform`
analog under `HasLevel (1/2)`: identical conclusion, with the modulus-range
hypothesis shrunk to the haircut range `⌊√N/(log N)^{B'}⌋₊` returned by
`lod_error_pow`.  The extra haircut `B'` is existentially returned and the
`N₀`-threshold additionally forces `log N ≥ 2·B'` so the shrunk range is
monotone across the shifted endpoints (`range_haircut_mono`).  Everything else
is verbatim `S2m_ge_compatMain_eh_uniform`. -/
theorem S2m_ge_compatMain_lod_uniform (k K₀ : ℕ) (hk : 1 ≤ k) (hK₀ : 1 ≤ K₀)
    (hLoD : HasLevel (1 / 2)) :
    ∃ (C₀ B' : ℝ) (N₀ : ℕ), 0 ≤ C₀ ∧ 0 ≤ B' ∧ ∀ (R ν₀ : ℕ) (T : ℝ), 2 ≤ R →
      (∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k)) →
      ∀ N : ℕ, N₀ ≤ N → R ≤ N →
        (W k * R ^ 2 ≤ ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊) →
      ∀ m : Fin k,
        S2m k K₀ N R ν₀ m (yTensor k R T)
          ≥ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
              * s2CompatFormM k R (W k) m (yTensor k R T)
            - C₀ * (1 + Real.log R) ^ (2 * k + 2) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
  classical
  obtain ⟨Clam, hClam0, hdisc⟩ := abs_S2m_sub_compatMain_le_disc_R_uniform k K₀ hK₀
  obtain ⟨C, B', N₁, hB'0, hEHb⟩ := lod_error_pow k (2 * k + 4) (by omega) hLoD
  have hCnn : 0 ≤ C := by
    set x₀ := max N₁ 2 with hx₀
    have hmax2 : 2 ≤ x₀ := le_max_right N₁ 2
    have hb := hEHb x₀ (le_max_left N₁ 2)
    have hx0pos : 0 < x₀ := by omega
    have hlogx0 : 0 < Real.log x₀ :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x₀ by omega))
    have hLHS0 : (0 : ℝ) ≤ ∑ q ∈ (Finset.range (⌊(x₀ : ℝ) ^ (1 / 2 : ℝ)
          / (Real.log x₀) ^ B'⌋₊ + 1)).filter Squarefree,
        (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x₀ q :=
      Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x₀ q))
    have hpos : 0 < (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) :=
      div_pos (by exact_mod_cast hx0pos) (pow_pos hlogx0 _)
    by_contra hCneg
    have hbad : C * (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) < 0 := by
      rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos (not_le.mp hCneg) hpos
    linarith [hLHS0, hb, hbad]
  refine ⟨2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1), B',
    max (max (max 2 N₁) (D₀ k)) ⌈Real.exp (2 * B')⌉₊, ?_, hB'0, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * Clam ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h1 hCnn) (by positivity)
  intro R ν₀ T hR hν₀ N hN0 hRN hrange m
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  -- regime facts from `N₀ ≤ N`
  have hN0a : max (max 2 N₁) (D₀ k) ≤ N := le_trans (le_max_left _ _) hN0
  have hle2N1 : max 2 N₁ ≤ N := le_trans (le_max_left _ _) hN0a
  have hD0N : D₀ k ≤ N := le_trans (le_max_right _ _) hN0a
  have hexp2N : ⌈Real.exp (2 * B')⌉₊ ≤ N := le_trans (le_max_right _ _) hN0
  have h2N : 2 ≤ N := le_trans (le_max_left 2 N₁) hle2N1
  have hN1N : N₁ ≤ N := le_trans (le_max_right 2 N₁) hle2N1
  have hNpos : 0 < N := by omega
  have hhm : hSeq k m ≤ N := le_trans (hSeq_le_D₀ k m) hD0N
  have hNleK0N : N ≤ K₀ * N := Nat.le_mul_of_pos_left N (by omega)
  have hlogN0 : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hlogN2B' : 2 * B' ≤ Real.log N := by
    have h1 : Real.exp (2 * B') ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hexp2N)
    calc 2 * B' = Real.log (Real.exp (2 * B')) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) h1
  have endpoint : ∀ x : ℕ, N ≤ x → x ≤ (K₀ + 1) * N →
      ∑ q ∈ (Finset.range (W k * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    intro x hNx hxub
    have hNxr : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
    have hmono : ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊
        ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      Nat.floor_mono (range_haircut_mono B' hB'0 N x h2N hNx hlogN2B')
    have hWRx : W k * R ^ 2 ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      le_trans hrange hmono
    have hsub : (Finset.range (W k * R ^ 2 + 1)).filter Squarefree
        ⊆ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter Squarefree :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))
    have hlogx0 : 0 < Real.log x :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x by omega))
    have hlogxN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hNpos) hNxr
    have hd1pos : 0 < (Real.log x) ^ (2 * k + 4) := pow_pos hlogx0 _
    have hd2pos : 0 < (Real.log N) ^ (2 * k + 4) := pow_pos hlogN0 _
    have hd21 : (Real.log N) ^ (2 * k + 4) ≤ (Real.log x) ^ (2 * k + 4) :=
      pow_le_pow_left₀ hlogN0.le hlogxN _
    calc ∑ q ∈ (Finset.range (W k * R ^ 2 + 1)).filter Squarefree,
            (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ ∑ q ∈ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter
            Squarefree, (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun q _ _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x q))
      _ ≤ C * (x : ℝ) / (Real.log x) ^ (2 * k + 4) := hEHb x (le_trans hN1N hNx)
      _ ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
          rw [div_le_div_iff₀ hd1pos hd2pos]
          have hxubr : (x : ℝ) ≤ ((K₀ : ℝ) + 1) * (N : ℝ) := by exact_mod_cast hxub
          have step_num : C * (x : ℝ) ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) := by
            calc C * (x : ℝ) ≤ C * (((K₀ : ℝ) + 1) * (N : ℝ)) :=
                  mul_le_mul_of_nonneg_left hxubr hCnn
              _ = C * ((K₀ : ℝ) + 1) * (N : ℝ) := by ring
          have hcnum : 0 ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) :=
            mul_nonneg (mul_nonneg hCnn (by positivity)) (by positivity)
          exact mul_le_mul step_num hd21 (pow_nonneg hlogN0.le _) hcnum
  have hexp : (K₀ + 1) * N = K₀ * N + N := by ring
  have hx1lb : N ≤ K₀ * N + hSeq k m := le_trans hNleK0N (Nat.le_add_right _ _)
  have hx1ub : K₀ * N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hx2ub : N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hEP1 := endpoint (K₀ * N + hSeq k m) hx1lb hx1ub
  have hEP2 := endpoint (N + hSeq k m) (Nat.le_add_right _ _) hx2ub
  have hfib1 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (K₀ * N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (K₀ * N + hSeq k m) q)
  have hfib2 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (N + hSeq k m) q)
  have hsplit : (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
      = (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)))
        + (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
            ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
              (if IsCollisionPair d e then 0
               else maxDiscrepancy (N + hSeq k m) (qMod k d e))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, add_zero]
    · simp only [if_neg hcol]
  have hDiscSum : (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
      ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
        + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    rw [hsplit]
    exact add_le_add (le_trans hfib1 hEP1) (le_trans hfib2 hEP2)
  have hLnn : 0 ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)
  have hfinal : |S2m k K₀ N R ν₀ m (yTensor k R T)
        - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
            * s2CompatFormM k R (W k) m (yTensor k R T)|
      ≤ 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
          * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    refine le_trans (hdisc R ν₀ T hR hν₀ m N hRN) ?_
    calc Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
          * (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
              ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
                (if IsCollisionPair d e then 0
                 else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                      + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
        ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
            * (C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
              + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)) :=
          mul_le_mul_of_nonneg_left hDiscSum hLnn
      _ = 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
            * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by ring
  have := (abs_le.mp hfinal).1
  linarith

/-! ## L4a — the analytic frontier under `HasLevel` (`analyticFrontier_lod`) -/

/-- **L4a — the analytic frontier under `HasLevel (1/2)`.**  Copy of
`analyticFrontier_holds'` with `EH (1/2)` replaced by `HasLevel (1/2)`: the
`S2m_ge_compatMain_lod_uniform` consumer returns an extra haircut `B'`, and the
modulus-range fact is discharged by `EH_range_lod` (its threshold `Nr` folded
into the largeness bound `B`).  Every other conjunct is verbatim. -/
theorem analyticFrontier_lod (k₀ : ℕ) (c : ℝ) (Nc : ℕ) (hLoD : HasLevel (1 / 2))
    (hk3072 : 3072 ≤ k₀) (hlogk : 300 ≤ Real.log k₀) (hc0 : 0 < c)
    (_hdom : (282175488 : ℝ) ≤ c * Real.log k₀)
    (hckey : ∀ N : ℕ, Nc ≤ N → c * (N : ℝ) / Real.log N
      ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ))
    (hCompat : CompatFrontier k₀ ((k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀))
    (N : ℕ) :
    ∃ (N' R ν₀ : ℕ) (T C₀ Cs : ℝ), N ≤ N' ∧ 0 < N' ∧ 0 < Real.log N' ∧
      1 ≤ A1 k₀ R (W k₀) T ∧
      (∀ m : Fin k₀,
        c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) ≤ deltaPi k₀ 64 N' m) ∧
      (∀ m : Fin k₀,
        (1 / 16 : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 * (A1 k₀ R (W k₀) T) ^ (k₀ - 1)
          ≤ s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)) ∧
      (∀ m : Fin k₀,
        deltaPi k₀ 64 N' m / (Nat.totient (W k₀) : ℝ)
            * s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)
          - C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4)
            ≤ S2m k₀ 64 N' R ν₀ m (yTensor k₀ R T)) ∧
      (S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
          + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)) ∧
      ((Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R * Real.log k₀ / 2916
        ≤ (k₀ : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 / (A1 k₀ R (W k₀) T)) ∧
      (c * (N' : ℝ) / (2 * Real.log N')
        ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ)) ∧
      (Real.log N' / 6 ≤ Real.log R) ∧
      (Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) ∧
      ((k₀ : ℝ)
          * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) := by
  classical
  have hk0pos : 0 < k₀ := by omega
  have hlogkpos : (0 : ℝ) < Real.log k₀ := by linarith
  have hkR : (1 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 1 < k₀)
  set T := (k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀ with hTdef
  have hTpos : (0 : ℝ) < T := by rw [hTdef]; positivity
  have hT1 : 1 ≤ T := T_ge_one hk0pos hlogk
  have hρpos : (0 : ℝ) < T / (k₀ : ℝ) := div_pos hTpos (by exact_mod_cast hk0pos)
  have hD : 12 * k₀ ^ 2 ≤ D₀ k₀ := by
    have h1 : (12 : ℕ) * k₀ ^ 2 ≤ k₀ ^ 3 := by
      calc 12 * k₀ ^ 2 ≤ k₀ * k₀ ^ 2 := by
            apply Nat.mul_le_mul_right; omega
        _ = k₀ ^ 3 := by ring
    exact le_trans h1 (le_max_left _ _)
  obtain ⟨ν₀, hν₀⟩ := exists_nu0 k₀
  obtain ⟨C₀, B', N₀eh, hC₀0, hB'0, hEHfun⟩ :=
    S2m_ge_compatMain_lod_uniform k₀ 64 (by omega) (by norm_num) hLoD
  obtain ⟨Nr, hEHrange⟩ := EH_range_lod k₀ B' hB'0
  obtain ⟨C0s, hC0s0, hC0sle⟩ := S1_trivial_error_le'_uniform k₀ (W k₀)
  set Cs := 2 ^ (k₀ + 1) * C0s with hCsdef
  have hCs0 : 0 ≤ Cs := by rw [hCsdef]; positivity
  set B : ℕ := max (2 ^ 30) (max N₀eh (max Nr Nc)) with hBdef
  have hcombined := hCompat.and ((eventually_D0_le k₀ c hc0).and ((eventually_herr1 k₀ Cs hCs0).and
    ((eventually_herr2 k₀ C₀ hC₀0).and ((eventually_rho_logR_ge k₀ T (Real.log 8) hρpos).and
    ((eventually_logR_ge ((k₀ : ℝ) * Real.log k₀ * Real.log 2)).and
    ((eventually_phiW_logR_ge k₀ (errA1 k₀ (W k₀) * ((k₀ : ℝ) * Real.log k₀))).and
    ((eventually_phiW_logR_ge k₀ (18 * (k₀ : ℝ) * errB1 k₀ (W k₀))).and
    (eventually_ge_atTop B))))))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcombined
  set N' := max N₀ N with hN'def
  have hgeN₀ : N₀ ≤ N' := le_max_left _ _
  have hNleN' : N ≤ N' := le_max_right _ _
  obtain ⟨hcompat', hD0', herr1', herr2', hrho', hlogRbig, hthrA', hthrB', hgeB⟩ :=
    hN₀ N' hgeN₀
  have hB1 : (2 : ℕ) ^ 30 ≤ N' := le_trans (le_max_left _ _) hgeB
  have hBN₀eh : N₀eh ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hgeB
  have hBinner : max Nr Nc ≤ N' :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hgeB
  have hBNr : Nr ≤ N' := le_trans (le_max_left _ _) hBinner
  have hBNc : Nc ≤ N' := le_trans (le_max_right _ _) hBinner
  have hN'2 : 2 ≤ N' := le_trans (by norm_num) hB1
  have hN'pos : 0 < N' := by omega
  have hN'r2 : (2 : ℝ) ^ 30 ≤ (N' : ℝ) := by exact_mod_cast hB1
  have h32 : (32 : ℝ) ≤ (N' : ℝ) := by
    have : (32 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    linarith [hN'r2]
  have hlogN'pos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  set R := ⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ with hRdef
  have hR : 2 ≤ R := R_ge_two N' h32
  have hRleN' : R ≤ N' := R_le_N' N' (by omega)
  have hrange : W k₀ * R ^ 2 ≤ ⌊(N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B'⌋₊ := by
    rw [hRdef]; exact hEHrange N' hBNr
  have hρR : Real.log 8 ≤ T / (k₀ : ℝ) * Real.log (R : ℝ) := hrho'
  have hX : 4 ≤ R0 k₀ R T := R0_ge_four k₀ R T hR hρR
  have hblog2 : bParam k₀ R * Real.log 2 ≤ 1 := bParam_log2_le k₀ R (by omega) hR hlogRbig
  have hbLo : (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) :=
    hbLo_of k₀ R T hk3072 hR hlogk hTdef hρR hblog2
  have hEA_r := hEA_ratio_of k₀ R (by omega) hR hthrA'
  have hEB_r := hEB_ratio_of k₀ R (by omega) hR hthrB'
  refine ⟨N', R, ν₀, T, C₀, Cs, hNleN', hN'pos, hlogN'pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A1_ge_one k₀ R T (by omega)
  · intro m
    have hd := deltaPi_lower_of k₀ c Nc hckey m N' hBNc
    have hhs : (hSeq k₀ m : ℝ) ≤ (D₀ k₀ : ℝ) := by exact_mod_cast hSeq_le_D₀ k₀ m
    linarith [hd, hhs]
  · exact hcompat'
  · intro m
    exact hEHfun R ν₀ T hR hν₀ N' hBN₀eh hRleN' hrange m
  · have hS1' := S1_conj_of k₀ 64 N' R ν₀ T C0s (by omega) hD (by norm_num) hR hC0s0 hC0sle
    calc S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 2 * ((64 - 1) * N' / (W k₀) : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
            + 2 ^ (k₀ + 1) * C0s * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2) := hS1'
      _ = 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
            + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2) := by rw [hCsdef]; ring
  · exact ratio_core_lower k₀ R T (by omega) hR hTdef hT1 hX hbLo hEA_r hEB_r
  · have hhalf : c * (N' : ℝ) / Real.log N' - c * (N' : ℝ) / (2 * Real.log N')
        = c * (N' : ℝ) / (2 * Real.log N') := by
      field_simp; ring
    linarith [hD0', hhalf.le, hhalf.ge]
  · exact logR_lower N' hN'r2
  · exact herr1'
  · exact herr2'

/-! ## L4b — the LoD capstone (`bounded_gaps_from_level`) -/

/-- **L4b — bounded gaps from the level of distribution (carrying `CompatFrontier`).**
Copy of `bounded_gaps_from_eh_final` wired through `analyticFrontier_lod`. -/
theorem bounded_gaps_from_level_final
    (hCompat : ∀ k₀ : ℕ, 3072 ≤ k₀ → 300 ≤ Real.log k₀ →
      CompatFrontier k₀ ((k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀)) :
    HasLevel (1 / 2) → ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧
      p.Prime ∧ q.Prime ∧ (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) := by
  intro hLoD
  obtain ⟨c, Nc, hc0, hckey⟩ := primes_in_interval_ge
  set k₀ := max (max 3072 ⌈Real.exp (282175488 / c)⌉₊) ⌈Real.exp 300⌉₊ with hk₀def
  have hk3072 : 3072 ≤ k₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hlogk : (300 : ℝ) ≤ Real.log k₀ := by
    have h1 : Real.exp 300 ≤ (k₀ : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_right _ _
    have h2 : Real.log (Real.exp 300) ≤ Real.log k₀ := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hdom : (282175488 : ℝ) ≤ c * Real.log k₀ := by
    have hM : (282175488 : ℝ) / c ≤ Real.log k₀ := by
      have h1 : Real.exp (282175488 / c) ≤ (k₀ : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        have : (⌈Real.exp (282175488 / c)⌉₊ : ℝ) ≤ (k₀ : ℝ) := by
          exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
        exact this
      have h2 : Real.log (Real.exp (282175488 / c)) ≤ Real.log k₀ :=
        Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have h := mul_le_mul_of_nonneg_left hM hc0.le
    have e : c * (282175488 / c) = 282175488 := by field_simp
    linarith [h, e.le, e.ge]
  refine bounded_gaps_reduces k₀ (fun N => ?_)
  obtain ⟨N', R, ν₀, T, C₀, Cs, hNleN', hNpos, hlogNpos, hA1ge1, hDpi, hcompat,
    hEHres, hS1, hratio, hδlb, hlogR, herr1, herr2⟩ :=
    analyticFrontier_lod k₀ c Nc hLoD hk3072 hlogk hc0 hdom hckey
      (hCompat k₀ hk3072 hlogk) N
  have hδ0 : 0 ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) :=
    le_trans (by positivity) hδlb
  refine ⟨N', R, ν₀, yTensor k₀ R T, hNleN', ?_⟩
  exact win_core k₀ N' R ν₀ T c C₀ Cs (by omega) hNpos hlogNpos hc0 hδ0 hA1ge1
    hDpi hcompat hEHres hS1 hratio hδlb hlogR hdom herr1 herr2

/-- **L4b — bounded gaps from `HasLevel (1/2)`.**  The LoD-shaped capstone,
discharging `CompatFrontier` with the EH-free `compatFrontier_holds`. -/
theorem bounded_gaps_from_level :
    HasLevel (1 / 2) → ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧
      p.Prime ∧ q.Prime ∧ (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  bounded_gaps_from_level_final compatFrontier_holds

/-- **Consistency check.**  The LoD chain subsumes the EH one: `EH (1/2)` gives
`HasLevel (1/2)` (`EH_hasLevel`), so `bounded_gaps_from_level` recovers
`BoundedGapsFromEH`. -/
theorem bounded_gaps_from_eh' : BoundedGapsFromEH :=
  fun hEH => bounded_gaps_from_level (EH_hasLevel hEH)

end Salt.Maynard
