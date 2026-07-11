/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.LevelConsume

/-!
# W5-2 — the EH consumers at level `θ★`

Design: `docs/blueprints/explicit12-design.md`, card **W5-2** + pre-flight
finding 3.  These are the level-`θ★`/range-`N^{θ★/2}` twins of the θ=1/2-pinned
EH consumers landed in `LevelConsume`/`FrontierFinal`.  The endgame ratio needs
`(θ★/2)·M₅ > 1`, which fails at `θ = 1/2` but holds at `θ★ = 1999/2000`
(margin `7.6×10⁻⁴`); EH is *consumed* at the strictly larger level
`θ₊ = 3999/4000 > θ★` so that `W'·R² ≤ N^{θ₊}` holds eventually at
`R = ⌊N^{θ★/2}⌋` with `W'` fixed.

The landed chain is θ=1/2 / `R = N^{1/5}`-pinned by LITERALS, not structure, so
every twin here is a literal swap
`(1/2:ℝ) → (3999/4000:ℝ)`, `1/5 → 1999/4000`, `2/5 → 3998/4000`,
`1/10 → 1/4000`, with `norm_num` reproving the exponent arithmetic — EXCEPT
`logR_lower_theta`, whose floor-slack exponent split needs a chosen split
constant `ρ` (threaded to `win_core`, W5-6).

Constants: `θ★ = 1999/2000`, `θ★/2 = 1999/4000`, level `θ₊ = 3999/4000`,
`R = ⌊N^{1999/4000}⌋₊`, `R² ≤ N^{3998/4000} = N^{θ★}`, haircut margin
`θ₊ − θ★ = 1/4000`.
-/

open Finset Filter

namespace Salt.Maynard

/-! ## The level-θ★ error bound (`lod_error_pow_theta`) -/

/-- **`lod_error_pow` at level `θ₊ = 3999/4000`.**  Verbatim `lod_error_pow`
with the two semantic `(1/2:ℝ)` literals (the sum range `⌊N^{θ₊}/(log N)^{B'}⌋₊`
and the `hsqrtN`/exponent-`<1` step) swapped to `(3999/4000:ℝ)`, and the level
hypothesis `HasLevel (3999/4000)`.  The Cauchy–Schwarz + Rankin + level-bound
body is exponent-agnostic, so the only arithmetic change is `(3999/4000 < 1)`
replacing `(1/2 < 1)`. -/
theorem lod_error_pow_theta (k B : ℕ) (hB : 1 ≤ B) (hLoD : HasLevel (3999 / 4000)) :
    ∃ (C B' : ℝ) (N₀ : ℕ), 0 ≤ B' ∧ ∀ N : ℕ, N₀ ≤ N →
      ∑ q ∈ (Finset.range
          (⌊(N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'⌋₊ + 1)).filter Squarefree,
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
  set qmax := ⌊(N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'⌋₊ with hqmax
  set S := (Finset.range (qmax + 1)).filter Squarefree with hSdef
  set LHS := ∑ q ∈ S, ((3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy N q) with hLHS
  -- `qmax ≤ ⌊N^{θ₊}⌋ < N`
  have hsqrtN : (N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B' ≤ (N : ℝ) ^ (3999 / 4000 : ℝ) := by
    rw [div_le_iff₀ hlogB'pos]
    nlinarith [Real.rpow_nonneg hNpos.le (3999 / 4000 : ℝ), hlogB'ge1]
  have hqmaxleN : qmax < N := by
    have h1 : qmax ≤ ⌊(N : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ := Nat.floor_le_floor hsqrtN
    have h2 : ⌊(N : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ < N := by
      rw [Nat.floor_lt (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (3999 / 4000 : ℝ))]
      have h := Real.rpow_lt_rpow_of_exponent_lt hN1R (by norm_num : (3999 / 4000 : ℝ) < 1)
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

/-! ## Facts about `R = ⌊N'^{θ★/2}⌋₊`, θ★/2 = 1999/4000 -/

/-- **`R_sq_le` at θ★/2.**  `R² ≤ N'^{3998/4000} = N'^{θ★}`.  Literal swap
`1/5 → 1999/4000`, `2/5 → 3998/4000`; `norm_num` on `2·(1999/4000) = 3998/4000`. -/
lemma R_sq_le_theta (N' : ℕ) (hN' : 1 ≤ N') :
    (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ (3998 / 4000 : ℝ) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ (1999 / 4000 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hRle : (⌊x ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ≤ x ^ (1999 / 4000 : ℝ) := Nat.floor_le hx5pos.le
  have hRnn : (0 : ℝ) ≤ (⌊x ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by positivity
  calc (⌊x ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (x ^ (1999 / 4000 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hRnn hRle 2
    _ = x ^ (3998 / 4000 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1999 / 4000 : ℝ)) 2, ← Real.rpow_mul hxpos.le]; norm_num

/-- **`logR_upper` at θ★/2.**  `log R ≤ (1999/4000)·log N'`.  Literal swap. -/
lemma logR_upper_theta (N' : ℕ) (hN' : 1 ≤ N') :
    Real.log (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ≤ (1999 / 4000 : ℝ) * Real.log N' := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ (1999 / 4000 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hx5ge1 : (1 : ℝ) ≤ x ^ (1999 / 4000 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hRle : (⌊x ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ≤ x ^ (1999 / 4000 : ℝ) := Nat.floor_le hx5pos.le
  have hRpos : (0 : ℝ) < (⌊x ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x ^ (1999 / 4000 : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast hx5ge1)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlog := Real.log_le_log hRpos hRle
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- **`logR_lower` at θ★/2 — the one C-flavored node (the ρ-split).**  Lower
bound on `log R` for `R = ⌊N'^{θ★/2}⌋₊`, parameterized by the split constant
`ρ`.  For any `0 ≤ ρ` and any `N'` large enough that `N'^{1999/4000 − ρ} ≥ 2`
(the floor-slack absorber, mirroring the landed `x^{1/30} ≥ 2`), we get
`log R ≥ ρ·log N'`.  The rest-exponent `1999/4000 − ρ` plays the role of the
landed `1/30`.  `ρ` is the OUTPUT CONSTANT threaded to `win_core` (W5-6), which
drives `ρ ↑ 1999/4000` so that `log R/log N' → θ★/2` — the two-sided limit
pinned together with `logR_upper_theta`.  (Concrete clean instance:
`ρ = 1959/4000`, rest `= 1/100`, threshold `N' ≥ 2^100`; but the endgame's
zero-slack margin forces `ρ` arbitrarily close to `1999/4000`, hence the
parameterization.) -/
lemma logR_lower_theta (ρ : ℝ) (hρ0 : 0 ≤ ρ) (N' : ℕ) (hN1 : 1 ≤ N')
    (hrest : (2 : ℝ) ≤ (N' : ℝ) ^ (1999 / 4000 - ρ : ℝ)) :
    ρ * Real.log N' ≤ Real.log (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN1
  have hxpos : (0 : ℝ) < x := by linarith
  set R := ⌊x ^ (1999 / 4000 : ℝ)⌋₊ with hR
  have hexp : ρ + (1999 / 4000 - ρ) = (1999 / 4000 : ℝ) := by ring
  have hsplit : x ^ (1999 / 4000 : ℝ) = x ^ (ρ : ℝ) * x ^ (1999 / 4000 - ρ : ℝ) := by
    rw [← Real.rpow_add hxpos, hexp]
  have hxρpos : (0 : ℝ) < x ^ (ρ : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hxρge1 : (1 : ℝ) ≤ x ^ (ρ : ℝ) := Real.one_le_rpow hx1 hρ0
  have hbig : 2 * x ^ (ρ : ℝ) ≤ x ^ (1999 / 4000 : ℝ) := by
    rw [hsplit]; nlinarith [hrest, hxρpos]
  have hfloor : x ^ (1999 / 4000 : ℝ) - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one (x ^ (1999 / 4000 : ℝ)); rw [← hR] at this; linarith
  have hRge : x ^ (ρ : ℝ) ≤ (R : ℝ) := by nlinarith [hfloor, hbig, hxρge1]
  have hlog := Real.log_le_log hxρpos hRge
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- Eventual form of `logR_lower_theta`: for any fixed `ρ < 1999/4000`,
eventually `ρ·log N' ≤ log R`.  This is the `∀ᶠ`-shape `win_core` consumes;
`ρ ↑ 1999/4000` (with `logR_upper_theta` above) pins `log R/log N' → θ★/2`. -/
lemma eventually_logR_lower_theta (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1999 / 4000) :
    ∀ᶠ N' : ℕ in atTop,
      ρ * Real.log N' ≤ Real.log (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by
  have hpos : (0 : ℝ) < 1999 / 4000 - ρ := by linarith
  have htend := tendsto_rpow_atTop hpos
  have hev := tendsto_natCast_atTop_atTop.eventually (htend.eventually_ge_atTop 2)
  filter_upwards [hev, eventually_ge_atTop 1] with N' h2 hN1
  exact logR_lower_theta ρ hρ0 N' hN1 h2

/-- **`R_ge_two` at θ★/2.**  `2 ≤ R` for `N' ≥ 8`.  The landed `32 = 2^5`
threshold (exp `1/5`) becomes `8 = 2^3`: `8^{1999/4000} = 2^{5997/4000} ≥ 2`
since `5997/4000 ≥ 1`. -/
lemma R_ge_two_theta (N' : ℕ) (hN' : (8 : ℝ) ≤ (N' : ℝ)) :
    2 ≤ ⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ := by
  set x := (N' : ℝ) with hx
  have hge : (2 : ℝ) ≤ x ^ (1999 / 4000 : ℝ) := by
    have h2 : ((8 : ℝ)) ^ (1999 / 4000 : ℝ) ≤ x ^ (1999 / 4000 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hN' (by norm_num)
    have he : (2 : ℝ) ≤ ((8 : ℝ)) ^ (1999 / 4000 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ ((3 : ℝ) * (1999 / 4000)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith [h2, he]
  exact Nat.le_floor (by exact_mod_cast hge)

/-- **`R_le_N'` at θ★/2.**  `R ≤ N'` for `N' ≥ 1`.  θ-agnostic (exp `< 1`);
literal swap. -/
lemma R_le_N'_theta (N' : ℕ) (hN' : 1 ≤ N') :
    ⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ ≤ N' := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hle : x ^ (1999 / 4000 : ℝ) ≤ x := by
    calc x ^ (1999 / 4000 : ℝ) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one _
  calc ⌊x ^ (1999 / 4000 : ℝ)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hle
    _ = N' := by rw [hx, Nat.floor_natCast]

/-! ## The level-θ★ EH modulus range (`EH_range_theta`) -/

/-- **`EH_range_lod` at θ★.**  For a fixed modulus `W'` and haircut `B' ≥ 0`, the
sieve modulus range `W'·R²` (with `R = ⌊N'^{θ★/2}⌋₊`) sits inside the level-`θ₊`
haircut range `⌊N'^{θ₊}/(log N')^{B'}⌋₊` once `N'` is large.  `W'` is a constant,
so `W'·R² ≤ W'·N'^{θ★}` and `W'·(log N')^{B'} ≤ N'^{1/4000}` eventually
(`eventually_poly_beats_polylog` at exponent `1/4000 = θ₊ − θ★`), and
`1/4000 + 3998/4000 = 3999/4000 = θ₊`. -/
theorem EH_range_theta (W' : ℕ) (hW' : 0 < W') (B' : ℝ) (hB'0 : 0 ≤ B') :
    ∃ Nr : ℕ, ∀ N' : ℕ, Nr ≤ N' →
      W' * (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊) ^ 2
        ≤ ⌊(N' : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N') ^ B'⌋₊ := by
  have hWpos : (0 : ℝ) < (W' : ℝ) := by exact_mod_cast hW'
  have hev := eventually_poly_beats_polylog ⌈B'⌉₊ ((1 : ℝ) / 4000) (W' : ℝ) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨Nr0, hNr0⟩ := eventually_atTop.mp hevN
  refine ⟨max Nr0 3, fun N' hN' => ?_⟩
  have hNr0le : Nr0 ≤ N' := le_trans (le_max_left _ _) hN'
  have hN3 : 3 ≤ N' := le_trans (le_max_right _ _) hN'
  have hpoly : (W' : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ ≤ (N' : ℝ) ^ ((1 : ℝ) / 4000) :=
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
  have hWlog : (W' : ℝ) * (Real.log N') ^ B' ≤ (N' : ℝ) ^ ((1 : ℝ) / 4000) := by
    calc (W' : ℝ) * (Real.log N') ^ B'
        ≤ (W' : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ :=
          mul_le_mul_of_nonneg_left hdom hWpos.le
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 4000) := hpoly
  have hR2 : (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ (3998 / 4000 : ℝ) :=
    R_sq_le_theta N' (by omega)
  have hmul : (W' : ℝ) * (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2
      ≤ (N' : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N') ^ B' := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogx B')]
    calc (W' : ℝ) * (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2 * (Real.log N') ^ B'
        = (W' : ℝ) * (Real.log N') ^ B' * (⌊(N' : ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2 := by ring
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 4000) * (N' : ℝ) ^ (3998 / 4000 : ℝ) :=
          mul_le_mul hWlog hR2 (by positivity) (by positivity)
      _ = (N' : ℝ) ^ (3999 / 4000 : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
  apply Nat.le_floor
  push_cast
  exact hmul

/-! ## Eventual range-monotonicity at θ★ (`range_haircut_mono_theta`) -/

/-- **`range_haircut_mono` at θ★.**  Eventual monotonicity of the level-`θ₊`
haircut range `y^{θ₊}/(log y)^{B'}` once `2·B' ≤ log N` (the landed threshold,
stronger than the exact `(4000/3999)·B' ≤ log N` needed here).  For `2 ≤ N ≤ x`,
the range at `N` is `≤` the range at `x`.  Consumed by
`S2mW_ge_compatMain_theta_uniform` (W5-3) across the shifted window endpoints. -/
lemma range_haircut_mono_theta (B' : ℝ) (hB'0 : 0 ≤ B') (N x : ℕ)
    (hN2 : 2 ≤ N) (hNx : N ≤ x) (hN2B' : 2 * B' ≤ Real.log N) :
    (N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'
      ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B' := by
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hxNR : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogNx : Real.log N ≤ Real.log x := Real.log_le_log hNpos hxNR
  have key : (3999 / 4000 : ℝ) * Real.log N - Real.log (Real.log N) * B'
      ≤ (3999 / 4000 : ℝ) * Real.log x - Real.log (Real.log x) * B' := by
    have hlogdiff : Real.log (Real.log x) - Real.log (Real.log N)
        ≤ (Real.log x - Real.log N) / Real.log N := by
      have hd : Real.log (Real.log x / Real.log N) ≤ Real.log x / Real.log N - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogx hlogN)
      rw [Real.log_div hlogx.ne' hlogN.ne'] at hd
      rw [sub_div, div_self hlogN.ne']
      linarith [hd]
    have hba : (0 : ℝ) ≤ Real.log x - Real.log N := by linarith
    have hstep : B' * (Real.log x - Real.log N) / Real.log N
        ≤ (3999 / 4000 : ℝ) * (Real.log x - Real.log N) := by
      rw [div_le_iff₀ hlogN]
      nlinarith [hN2B', hba, mul_nonneg (show (0 : ℝ) ≤ Real.log N - 2 * B' by linarith) hba,
        mul_nonneg hlogN.le hba]
    have hchain : Real.log (Real.log x) * B' - Real.log (Real.log N) * B'
        ≤ (3999 / 4000 : ℝ) * (Real.log x - Real.log N) := by
      calc Real.log (Real.log x) * B' - Real.log (Real.log N) * B'
          = B' * (Real.log (Real.log x) - Real.log (Real.log N)) := by ring
        _ ≤ B' * ((Real.log x - Real.log N) / Real.log N) :=
            mul_le_mul_of_nonneg_left hlogdiff hB'0
        _ = B' * (Real.log x - Real.log N) / Real.log N := by ring
        _ ≤ (3999 / 4000 : ℝ) * (Real.log x - Real.log N) := hstep
    linarith [hchain]
  have hNe : (N : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log N) ^ B'
      = Real.exp ((3999 / 4000 : ℝ) * Real.log N - Real.log (Real.log N) * B') := by
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hlogN, ← Real.exp_sub]
    congr 1; ring
  have hxe : (x : ℝ) ^ (3999 / 4000 : ℝ) / (Real.log x) ^ B'
      = Real.exp ((3999 / 4000 : ℝ) * Real.log x - Real.log (Real.log x) * B') := by
    rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hlogx, ← Real.exp_sub]
    congr 1; ring
  rw [hNe, hxe]
  exact Real.exp_le_exp.mpr key

end Salt.Maynard
