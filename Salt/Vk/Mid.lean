/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Window
import Salt.Vk.PowRegion

/-!
# VMVT-VK rung R5b (schedule half) — the `k(t)`-schedule mid-branch bound (`VK-MID`)

`vk_window_mid` completes WALL 1: at the freeze's `k(t)`-schedule (`k = max(19, ⌈L^{1/4}⌉)`,
`r = ⌈k·log 4k²⌉`, `m = ⌈L/j⌉` with `L = log t`, `j = log N`), for any dyadic scale `N` in the
mid routing band — `N^{vkTheta t} ≥ 2` (the low boundary, implying `j ≥ 693·L^{3/4}ℓ²`, well above
the freeze's `j_cut = 96·L^{3/4}ℓ²`) and `10j < L` (the high boundary) — the ζ-phase window obeys

  `‖∑_{(N,2N]} eR(phi t n)‖ ≤ 10·N·exp(−vkTheta t · log N)`,

the exact per-block shape R6's σ-weighted ladder consumes (the `P^{−ρ}` saving is folded into
`exp(−Θj)` via `ρ·log P ≥ Θ·j`, which holds with `~10⁴ℓ³` slack).  All parameters (`P`, `Y`, `ρ`)
are internal; the interface is `(t, N)` + the schedule + the two routing predicates + the height
floor `log t ≥ e^100` (astronomically lazy; the region's `T₀` is `exp(exp(1100))`-grade anyway).

Margin ledger (at the routing floor `j = 693·A³ℓ²`, `A = L^{1/4}`): `k ≤ (11/10)A`,
`log k ≤ (28/100)ℓ`, `r ≤ (6/10)kℓ` give `8·lnD ≤ 8·(6 + 1/100)·A³ℓ² < (1/2)·693·A³ℓ² ≤ (1−β)j`
(margin ≈ 7×), and `ρ ≥ 1/(64A²ℓ)`, `log P ≥ j/2` give `ρ·log P ≥ j/(128A²ℓ) ≥ Θj·(5.4·10⁴ℓ³)`.
-/

namespace Salt.Vk

open Finset Real Salt.ExpSum
open scoped BigOperators

/-- The `hD` P-floor budget, extracted to a minimal context: at the schedule bounds
`A ≤ k ≤ (11/10)A`, `r ≤ (6/10)kℓ`, `log k ≤ (28/100)ℓ`, `A ≥ 26`, `ℓ ≥ 100`, the degree cost
`8·lnD = 8(k·log 16k + 24k²r·log k)` is `≤ 52·A³·ℓ²` (worst-case coefficient `5.9 + 0.4 < 6.5`,
times 8). -/
private lemma vk_lnD_budget {k r : ℕ} {A ℓ : ℝ}
    (hkR_lo : A ≤ (k : ℝ)) (hkR_ub : (k : ℝ) ≤ 11 / 10 * A) (hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ)
    (hlnk_ub : Real.log k ≤ 28 / 100 * ℓ) (hlnk0 : 0 ≤ Real.log k) (hr0R : (0 : ℝ) < (r : ℝ))
    (hk0R : (0 : ℝ) < (k : ℝ)) (hl21 : Real.log 2 ≤ 1) (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) :
    8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ 52 * A ^ 3 * ℓ ^ 2 := by
  have hlog16k : Real.log (16 * (k : ℝ)) ≤ 4 + 28 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hk0R)]
    have h16 : Real.log 16 ≤ 4 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith [hl21]
    linarith [hlnk_ub]
  have hT1 : (k : ℝ) * Real.log (16 * k) ≤ 4 / 10 * A * ℓ := by
    have h1 : (k : ℝ) * Real.log (16 * k) ≤ (11 / 10 * A) * (4 + 28 / 100 * ℓ) := by
      apply mul_le_mul hkR_ub hlog16k _ (by positivity)
      apply Real.log_nonneg; nlinarith [hkR_lo, hA26]
    nlinarith [h1, hA0, hℓ100, mul_nonneg hA0.le (show (0 : ℝ) ≤ ℓ by linarith)]
  have hk2 : (k : ℝ) ^ 2 ≤ (11 / 10 * A) ^ 2 := by nlinarith [hkR_ub, hkR_lo, hA0]
  have hrk : (r : ℝ) ≤ 6 / 10 * (11 / 10 * A) * ℓ := by
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have hkr_lnk : (k : ℝ) ^ 2 * (r : ℝ) * Real.log k
      ≤ (11 / 10 * A) ^ 2 * (6 / 10 * (11 / 10 * A) * ℓ) * (28 / 100 * ℓ) :=
    mul_le_mul (mul_le_mul hk2 hrk hr0R.le (by positivity)) hlnk_ub hlnk0 (by positivity)
  have hT2 : 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log k ≤ 6 * A ^ 3 * ℓ ^ 2 := by
    nlinarith [hkr_lnk, hA0, hℓ0, mul_pos (pow_pos hA0 3) (pow_pos hℓ0 2)]
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hAℓ : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
    have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]
  linarith [hT1, hT2, hAℓ]

/-- `A·ℓ ≤ A³·ℓ²` on the schedule floor `A ≥ 26`, `ℓ ≥ 100` (via `A²ℓ ≥ 1`). -/
private lemma vk_Aℓ_cube {A ℓ : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]

/-- The `P^{−ρ} → exp(−Θj)` saving, extracted: with `ρ ≥ 1/(12A²ℓ)`, `log P ≥ j/2`, the width
`Θ = 1/(1000·A³ℓ²)` obeys `Θ·j ≤ ρ·log P` (the `A²ℓ ≫ 1` slack, `~5·10⁴ℓ³`). -/
private lemma vk_theta_saving {A ℓ j ρ LP : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hj0 : (0 : ℝ) < j) (hρpos : (0 : ℝ) < ρ)
    (hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ) (hLP : j / 2 ≤ LP) :
    (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ ρ * LP := by
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hstep2 : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) ≤ ρ * LP :=
    mul_le_mul hρlo hLP (by positivity) hρpos.le
  have hcompare : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ (1 / (12 * A ^ 2 * ℓ)) * (j / 2) := by
    have hAℓ2600 : (2600 : ℝ) ≤ A * ℓ := by nlinarith [hA26, hℓ100]
    have hden : 24 * (A ^ 2 * ℓ) ≤ 1000 * (A ^ 3 * ℓ ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ A ^ 2 * ℓ by positivity)
        (show (0 : ℝ) ≤ 1000 * (A * ℓ) - 24 by linarith [hAℓ2600])]
    have hL : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j = j / (1000 * (A ^ 3 * ℓ ^ 2)) := by
      field_simp
    have hR : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) = j / (24 * (A ^ 2 * ℓ)) := by field_simp; ring
    rw [hL, hR]
    gcongr
  linarith [hstep2, hcompare]

set_option maxHeartbeats 4000000 in
-- ~55 staged log/rpow bound facts thread through `nlinarith`/`linarith` over a large local context;
-- the heavy pure-arithmetic blocks are extracted (`vk_lnD_budget`, `vk_theta_saving`, `vk_Aℓ_cube`),
-- but the residual schedule bookkeeping still exceeds the default budget.
/-- **WALL 1 end-to-end (mid branch)** — the `k(t)`-schedule window bound.  For `log t ≥ e^100`,
`N ≥ 2` in the mid band (`N^Θ ≥ 2`, `10·log N < log t`), with `k, r, m` per the freeze schedule,
the dyadic ζ-phase window at `N` saves a full `exp(−vkTheta t · log N)` factor. -/
theorem vk_window_mid {t : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) := by
  -- ## Opaque scalars (defeq-storm avoidance)
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log t := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ x : ℝ, x = Real.log N := ⟨_, rfl⟩
  rw [← hLdef] at hL100 hk hm hjhi
  rw [← hjdef] at hm hjhi hroute ⊢
  obtain ⟨ℓ, hℓdef⟩ : ∃ x : ℝ, x = Real.log L := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ, x = L ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hAdef] at hk
  -- ## Base positivity
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hL1 : (1 : ℝ) < L := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hL100
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN1R : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : (0 : ℝ) < j := by rw [hjdef]; exact Real.log_pos hN1R
  have hN1 : 1 ≤ N := by omega
  -- ## A bounds: exp 25 ≤ A, 26 ≤ A
  have hAexp : A = Real.exp (ℓ * (1 / 4)) := by
    rw [hAdef, Real.rpow_def_of_pos hL0, hℓdef]
  have hA25 : Real.exp 25 ≤ A := by
    rw [hAexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hA26 : (26 : ℝ) ≤ A := by
    have : (26 : ℝ) ≤ Real.exp 25 := by linarith [Real.add_one_le_exp (25 : ℝ)]
    linarith
  have hA0 : (0 : ℝ) < A := by linarith
  -- ## k = ⌈A⌉ and its bounds
  have hkA : k = ⌈A⌉₊ := by
    rw [hk, max_eq_right]
    have h1 : (19 : ℝ) ≤ (⌈A⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil A)
    exact_mod_cast h1
  have hkR_lo : A ≤ (k : ℝ) := by rw [hkA]; exact Nat.le_ceil A
  have hkR_ub : (k : ℝ) ≤ 11 / 10 * A := by
    rw [hkA]
    have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
    linarith [hA26]
  have hk19 : 19 ≤ k := by rw [hk]; exact le_max_left _ _
  have hk0R : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hA0 hkR_lo
  have hl20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- ## log k ≤ (28/100)·ℓ
  have hlogA : Real.log A = ℓ / 4 := by
    rw [hAdef, Real.log_rpow hL0, ← hℓdef]; ring
  have hlnk_ub : Real.log k ≤ 28 / 100 * ℓ := by
    have h1 : Real.log k ≤ Real.log (11 / 10 * A) := Real.log_le_log hk0R hkR_ub
    rw [Real.log_mul (by norm_num) (ne_of_gt hA0), hlogA] at h1
    have h2 : Real.log (11 / 10) ≤ 1 / 10 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 10 by norm_num)]
    linarith [hℓ100]
  have hlnk0 : (0 : ℝ) ≤ Real.log k := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  -- ## r ≤ (6/10)·k·ℓ
  have hlog4k2 : Real.log (4 * (k : ℝ) ^ 2) ≤ 2 + 56 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [hl21]
    push_cast; linarith [hlnk_ub]
  have hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) := by
      apply mul_nonneg hk0R.le
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
      nlinarith
    have h1 : (⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ : ℝ)
        < (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) + 1 := Nat.ceil_lt_add_one h0
    have h2 : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (k : ℝ) * (2 + 56 / 100 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog4k2 hk0R.le
    have h3 : (k : ℝ) * 100 ≤ (k : ℝ) * ℓ := mul_le_mul_of_nonneg_left hℓ100 hk0R.le
    nlinarith [h1, h2, h3, hk0R]
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_ceil_iff]
    apply mul_pos hk0R
    apply Real.log_pos
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
    nlinarith
  have hr0R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  -- ## Θ in A/ℓ form and the j floor
  have hA3eq : L ^ ((3 : ℝ) / 4) = A ^ 3 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hL0.le]
    norm_num
  have hΘval : vkTheta t = 1 / 1000 / (A ^ 3 * ℓ ^ 2) := by
    rw [vkTheta, ← hLdef, ← hℓdef, hA3eq]
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hjlo : 693 * (A ^ 3 * ℓ ^ 2) ≤ j := by
    have h1 := hroute
    rw [hΘval] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hD0] at h1
    nlinarith [Real.log_two_gt_d9, hD0.le, h1]
  -- ## The m band
  have hLj10 : (10 : ℝ) < L / j := by rw [lt_div_iff₀ hj0]; linarith
  have hm11 : 11 ≤ m := by
    have h1 : 10 < m := by
      rw [hm]
      exact_mod_cast Nat.lt_ceil.mpr (by exact_mod_cast hLj10)
    omega
  have hLj0 : (0 : ℝ) ≤ L / j := by positivity
  have hm_ub : (m : ℝ) < L / j + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one hLj0
  have hL_A4 : L = A ^ 4 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hL0.le]
    norm_num
  have hℓ2ge : (10000 : ℝ) ≤ ℓ ^ 2 := by nlinarith [hℓ100]
  have hA2ge : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hLj_ub : L / j ≤ A / 693 := by
    have hstep : L * 693 ≤ A * j := by
      have h1 : A * (693 * (A ^ 3 * ℓ ^ 2)) ≤ A * j := mul_le_mul_of_nonneg_left hjlo hA0.le
      have h2 : A * (693 * (A ^ 3 * ℓ ^ 2)) = 693 * L * ℓ ^ 2 := by rw [hL_A4]; ring
      rw [h2] at h1
      nlinarith [h1, hℓ2ge, hL0.le]
    rw [div_le_div_iff₀ hj0 (by norm_num)]
    linarith [hstep]
  have hmA : (m : ℝ) ≤ A / 693 + 1 := le_trans hm_ub.le (by linarith [hLj_ub])
  have hmk : m + 8 ≤ k := by
    have h1 : (m : ℝ) + 8 ≤ (k : ℝ) := by nlinarith [hmA, hA26, hkR_lo]
    exact_mod_cast h1
  -- ## The scale window N^{m−1} < t ≤ N^m
  have hNexp : ∀ n : ℕ, (N : ℝ) ^ n = Real.exp ((n : ℝ) * j) := by
    intro n
    rw [Real.exp_nat_mul, hjdef, Real.exp_log hN0R]
  have htexp : t = Real.exp L := by rw [hLdef, Real.exp_log ht0]
  have hthi : t ≤ (N : ℝ) ^ m := by
    have h1 : L / j ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil _
    have h2 : L ≤ (m : ℝ) * j := by rw [div_le_iff₀ hj0] at h1; linarith
    rw [htexp, hNexp m]
    exact Real.exp_le_exp.mpr h2
  have htlo : (N : ℝ) ^ (m - 1) < t := by
    have h1 : (m : ℝ) - 1 < L / j := by linarith [hm_ub]
    have h2 : ((m : ℝ) - 1) * j < L := by rw [lt_div_iff₀ hj0] at h1; linarith
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [htexp, hNexp (m - 1), hcast]
    exact Real.exp_lt_exp.mpr h2
  -- ## `P`, `Y`, `ρ` and `β`
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊ := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 / (16 * (k : ℝ) * r) := ⟨_, rfl⟩
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hβ0 : (0 : ℝ) ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hk1R]
    have : (m : ℝ) + 2 ≤ (k : ℝ) := by
      have : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
      linarith
    linarith
  -- ## The `hD` P-floor:  8·lnD ≤ (1−β)·j
  have hlnD_ub : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ 52 * A ^ 3 * ℓ ^ 2 :=
    vk_lnD_budget hkR_lo hkR_ub hr_ub hlnk_ub hlnk0 hr0R hk0R hl21 hA26 hℓ100 hA0 hℓ0
  have hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N := by
    rw [← hjdef]
    have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 654 / 1000 := by
      rw [div_le_iff₀ hk1R]
      nlinarith [hmA, hkR_lo, hA26]
    have hβj : (346 / 1000) * j ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * j := by
      apply mul_le_mul_of_nonneg_right _ hj0.le
      linarith [hle]
    have hfloor : 52 * A ^ 3 * ℓ ^ 2 ≤ (346 / 1000) * j := by
      have h : (346 / 1000) * (693 * (A ^ 3 * ℓ ^ 2)) ≤ (346 / 1000) * j :=
        mul_le_mul_of_nonneg_left hjlo (by norm_num)
      nlinarith [h, hD0.le]
    linarith only [hlnD_ub, hfloor, hβj]
  -- ## The `j`-floor for `vk_window_scale`
  have hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N := by
    rw [← hjdef]
    have hkℓ : 2 * ((k : ℝ) + 1) + 4 * (28 / 100) * ℓ + 8 ≤ (346 / 1000) * j := by
      have hbig : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := vk_Aℓ_cube hA26 hℓ100 hA0 hℓ0
      have hjge : 693 * (A * ℓ) ≤ j := le_trans (by nlinarith [hbig, hD0.le]) hjlo
      nlinarith [hjge, hkR_ub, hA0, hℓ100, hA26]
    have h1 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ 2 * ((k : ℝ) + 1) := by nlinarith [hl21, hk0R]
    have h2 : 4 * Real.log k ≤ 4 * (28 / 100) * ℓ := by linarith [hlnk_ub]
    have hj346 : (346 / 1000) * j ≤ j := by nlinarith [hj0]
    linarith only [h1, h2, hkℓ, hj346]
  -- ## Fold `P^{−ρ}` into `exp(−Θ·j)`:  ρ·log P ≥ Θ·j
  have hlPlo : (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N ≤ Real.log P :=
    vk_logP_ge hN1 hPdef
  have hlogN0 : (0 : ℝ) ≤ Real.log N := by rw [← hjdef]; exact hj0.le
  have hlP_half : j / 2 ≤ Real.log P := by
    have hβle : (1 : ℝ) / 2 ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
      have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hk1R]; nlinarith [hmA, hkR_lo, hA26]
      linarith [hle]
    have hstep : (1 : ℝ) / 2 * Real.log N ≤ Real.log P :=
      le_trans (mul_le_mul_of_nonneg_right hβle hlogN0) hlPlo
    rw [hjdef]; linarith only [hstep]
  have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hr_ub2 : (16 * (k : ℝ) * r) ≤ 16 * (11 / 10 * A) * (6 / 10 * (11 / 10 * A) * ℓ) := by
    apply mul_le_mul (by nlinarith [hkR_ub, hA0]) _ hr0R.le (by positivity)
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have h16kr : (0 : ℝ) < 16 * (k : ℝ) * r := mul_pos (mul_pos (by norm_num) hk0R) hr0R
  have hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ := by
    rw [hρdef, div_le_div_iff₀ (by positivity) h16kr]
    nlinarith [hr_ub2, hA0, hℓ0]
  have hΘlogN : vkTheta t * j ≤ ρ * Real.log P := by
    rw [hΘval]
    exact vk_theta_saving hA26 hℓ100 hj0 hρpos hρlo hlP_half
  -- ## Assemble
  have hbound := vk_window_scale (k := k) (r := r) (m := m) (N := N) (P := P) (Y := Y)
    (ρ := ρ) (t := t) hk19 hr hρdef hm11 hmk hN1 hPdef hYdef htlo hthi hDf hjf
  refine le_trans hbound ?_
  -- `10 N P^{−ρ} ≤ 10 N exp(−Θ j)` since `P^{−ρ} = exp(−ρ logP) ≤ exp(−Θ j)`
  have hPρ : (P : ℝ) ^ (-ρ) = Real.exp (-(ρ * Real.log P)) := by
    have hPpos : (0 : ℝ) < (P : ℝ) := by
      rw [hPdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (by rw [Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hN0R _)
    rw [Real.rpow_def_of_pos hPpos]; congr 1; ring
  rw [hPρ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith [hΘlogN])

end Salt.Vk
