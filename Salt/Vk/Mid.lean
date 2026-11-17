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
      apply Real.log_nonneg; linarith only [hA26, hkR_lo]
    nlinarith only [hkR_ub, hlnk0, hlnk_ub, hℓ100, h1, hA26, hkR_lo, (Nat.cast_nonneg _ : 0 ≤ ↑k)]
  have hk2 : (k : ℝ) ^ 2 ≤ (11 / 10 * A) ^ 2 := by nlinarith [hkR_ub, hkR_lo, hA0]
  have hrk : (r : ℝ) ≤ 6 / 10 * (11 / 10 * A) * ℓ := by
    apply le_trans hr_ub; nlinarith only [hkR_ub, hlnk0, hlnk_ub]
  have hkr_lnk : (k : ℝ) ^ 2 * (r : ℝ) * Real.log k
      ≤ (11 / 10 * A) ^ 2 * (6 / 10 * (11 / 10 * A) * ℓ) * (28 / 100 * ℓ) :=
    mul_le_mul (mul_le_mul hk2 hrk hr0R.le (by positivity)) hlnk_ub hlnk0 (by positivity)
  have hT2 : 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log k ≤ 6 * A ^ 3 * ℓ ^ 2 := by
    linarith only [hkr_lnk, mul_pos (pow_pos hA0 3) (pow_pos hℓ0 2)]
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith only [hkR_ub, hA26, (Nat.cast_nonneg _ : 0 ≤ ↑k)]
  have hAℓ : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
    have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith only [hℓ100, hA2, sq_nonneg A]
    linarith only [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]
  linarith [hT1, hT2, hAℓ]

/-- `A·ℓ ≤ A³·ℓ²` on the schedule floor `A ≥ 26`, `ℓ ≥ 100` (via `A²ℓ ≥ 1`). -/
private lemma vk_Aℓ_cube {A ℓ : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith only [hA26]
  have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith only [hℓ100, hA2, sq_nonneg A]
  linarith only [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]

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
    have hAℓ2600 : (2600 : ℝ) ≤ A * ℓ := by nlinarith only [hA26, hℓ100]
    have hden : 24 * (A ^ 2 * ℓ) ≤ 1000 * (A ^ 3 * ℓ ^ 2) := by
      linarith only [mul_nonneg (show (0 : ℝ) ≤ A ^ 2 * ℓ by positivity)
          (show (0 : ℝ) ≤ 1000 * (A * ℓ) - 24 by linarith [hAℓ2600])]
    have hL : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j = j / (1000 * (A ^ 3 * ℓ ^ 2)) := by
      field_simp
    have hR : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) = j / (24 * (A ^ 2 * ℓ)) := by field_simp; ring
    rw [hL, hR]
    gcongr
  linarith [hstep2, hcompare]

section VkPrefix

open Complex

/-! ## The prefix ladder (min-trick) -/

/-- **Prefix ladder.**  The prefix-of-window analogue of `vk_ladder_bound`: given per-sub-block
**prefix** bounds `‖∑_{(c i, z]} f‖ ≤ 8·P^{1−ρ}` (`c i = min(N+iP)(2N)`, any `z ≤ c(i+1)`), every
prefix `(N, y]` (`N < y ≤ 2N`) obeys `‖∑_{(N,y]} f‖ ≤ 10·N·P^{−ρ}`.  Via the clipped endpoint
sequence `c' i = min (c i) y` (monotone, `c' 0 = N`, `c' Q = y`) fed through `vk_sum_Ioc_split`. -/
theorem vk_ladder_prefix {E : Type*} [NormedAddCommGroup E] (f : ℤ → E)
    {P N : ℕ} {ρ : ℝ} (hP : 1 ≤ P) (h4P : 4 * P ≤ N)
    (hBp : ∀ i, i < ⌈(N : ℝ) / (P : ℝ)⌉₊ → ∀ z : ℤ,
      min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) < z →
      z ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) →
      ‖∑ n ∈ Finset.Ioc (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)) z, f n‖
        ≤ 8 * (P : ℝ) ^ (1 - ρ))
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, f n‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h4PR : 4 * (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4P
  set Q : ℕ := ⌈(N : ℝ) / (P : ℝ)⌉₊ with hQdef
  set c : ℕ → ℤ := fun i => min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) with hc
  set c' : ℕ → ℤ := fun i => min (c i) y with hc'
  have hc0 : c 0 = (N : ℤ) := by simp only [hc, Nat.cast_zero, zero_mul, add_zero]; omega
  have hQP : (N : ℝ) ≤ (Q : ℝ) * (P : ℝ) := by
    have hle : (N : ℝ) / (P : ℝ) ≤ (Q : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hP0] at hle; exact hle
  have hcQ : c Q = 2 * (N : ℤ) := by
    simp only [hc]
    apply min_eq_right
    have : (N : ℤ) ≤ (Q : ℤ) * (P : ℤ) := by exact_mod_cast hQP
    linarith
  -- c' is monotone; c' 0 = N, c' Q = y
  have hc'mono : Monotone c' := by
    intro i j hij
    simp only [hc', hc]
    have : (i : ℤ) * (P : ℤ) ≤ (j : ℤ) * (P : ℤ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
    omega
  have hc'0 : c' 0 = (N : ℤ) := by simp only [hc', hc0]; omega
  have hc'Q : c' Q = y := by simp only [hc', hcQ]; omega
  -- telescope the prefix
  have hsplit := vk_sum_Ioc_split f c' hc'mono Q
  rw [hc'0, hc'Q] at hsplit
  rw [hsplit]
  -- per-block prefix bound
  have hblk : ∀ i ∈ Finset.range Q,
      ‖∑ n ∈ Finset.Ioc (c' i) (c' (i + 1)), f n‖ ≤ 8 * (P : ℝ) ^ (1 - ρ) := by
    intro i hi
    have hiQ : i < Q := Finset.mem_range.mp hi
    by_cases hlt : c' i < c' (i + 1)
    · -- nonempty prefix of block i: c' i = c i
      have hci : c' i = c i := by
        simp only [hc'] at hlt ⊢
        have hle : c' (i + 1) ≤ y := by simp only [hc']; omega
        omega
      have hz2 : c' (i + 1) ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) := by
        simp only [hc', hc]; push_cast; omega
      rw [hci]
      refine hBp i hiQ (c' (i + 1)) ?_ hz2
      change c i < c' (i + 1)
      rw [← hci]; exact hlt
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
      positivity
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hblk) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- arithmetic: Q · 8 P^{1-ρ} ≤ 10 N P^{-ρ}   (identical to vk_ladder_bound)
  have hQlt : (Q : ℝ) < (N : ℝ) / (P : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hQPub : (Q : ℝ) * (P : ℝ) ≤ (N : ℝ) + (P : ℝ) := by
    calc (Q : ℝ) * (P : ℝ) ≤ ((N : ℝ) / (P : ℝ) + 1) * (P : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt hQlt) hP0.le
      _ = (N : ℝ) + (P : ℝ) := by field_simp
  have h4PQ : 4 * (P : ℝ) * (Q : ℝ) ≤ 5 * (N : ℝ) := by linarith only [hQPub, h4PR]
  have hPsplit : (P : ℝ) ^ (1 - ρ) = (P : ℝ) * (P : ℝ) ^ (-ρ) := by
    rw [show (1 : ℝ) - ρ = 1 + (-ρ) by ring, Real.rpow_add hP0, Real.rpow_one]
  have hPρnn : (0 : ℝ) ≤ (P : ℝ) ^ (-ρ) := Real.rpow_nonneg hP0.le _
  rw [hPsplit]
  have hstep : (Q : ℝ) * (8 * ((P : ℝ) * (P : ℝ) ^ (-ρ)))
      = (8 * ((P : ℝ) * (Q : ℝ))) * (P : ℝ) ^ (-ρ) := by ring
  rw [hstep]
  apply mul_le_mul_of_nonneg_right _ hPρnn
  linarith only [hQPub, h4PR]

/-! ## The prefix window bound (schedule-agnostic) -/

/-- Per-block `vk_block_core` at an interior block `N₀ ∈ [N, 2N]` (copy of `Window.vk_block_at`,
the private full-window helper, re-exposed here to feed the prefix ladder). -/
private lemma vk_block_prefix_at {k r P P' Y N N₀ : ℕ} {t ρ : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hP' : P' ≤ P)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hNle : N ≤ N₀) (hN₀le : N₀ ≤ 2 * N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖ ≤ 8 * (P : ℝ) ^ (1 - ρ) := by
  have hN0pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := lt_of_lt_of_le hN0pos (by exact_mod_cast hNle)
  have hNleR : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hNle
  have hN₀leR : (N₀ : ℝ) ≤ (2 * N : ℝ) := by exact_mod_cast hN₀le
  have hπ : (0 : ℝ) < 2 * π := by positivity
  refine vk_block_core hk hr hρ hP' hY hD ?_ ⟨js, ?_, ?_, ?_, ?_⟩
  · have hkey : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k :=
      le_trans hW1 (by gcongr)
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    calc t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k := hkey
      _ = ((N₀ : ℝ))⁻¹ * (N₀ : ℝ) ^ (k + 1) := by
          rw [pow_succ, mul_comm ((N₀ : ℝ) ^ k) (N₀ : ℝ), ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hN₀0), one_mul]
  · rw [Finset.mem_Icc]; exact ⟨hjs2, hjsk⟩
  · have hpow : ((N₀ : ℝ)) ^ (js + 1) ≤ ((2 * N : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN₀0.le hN₀leR _
    calc (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
        ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := hW2a
      _ ≤ t / (2 * π * ((N₀ : ℝ)) ^ (js + 1)) := by gcongr
  · have hpow : ((N : ℝ)) ^ (js + 1) ≤ ((N₀ : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN0pos.le hNleR _
    calc t * (Y : ℝ) / (2 * π * ((N₀ : ℝ)) ^ (js + 1))
        ≤ t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) := by gcongr
      _ ≤ 1 / 6 := hW2b
  · calc 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := hW2c
      _ ≤ (N₀ : ℝ) := hNleR

/-- **Prefix window bound.**  Prefix-of-window analogue of `vk_window_bound`: same five per-scale
worst-case `vk_block_core` hypotheses, but concluding the *prefix* bound
`‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}` for every `N < y ≤ 2N`.  Via `vk_ladder_prefix` with the
per-sub-block prefix bounds from `vk_block_prefix_at`. -/
theorem vk_window_prefix {k r P Y N : ℕ} {t ρ : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hP : 1 ≤ P) (h4P : 4 * P ≤ N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ))
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  apply vk_ladder_prefix (fun n => eR (phi t n)) hP h4P ?_ y hy1 hy2
  intro i hi z hz1 hz2
  have hN0Z : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hiP0 : (0 : ℤ) ≤ (i : ℤ) * (P : ℤ) := by positivity
  have hage : (N : ℤ) ≤ min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    le_min (by linarith) (by linarith)
  have hbma : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ (P : ℤ) := by
    have hstep : ((i : ℤ) + 1) * (P : ℤ) = (i : ℤ) * (P : ℤ) + (P : ℤ) := by ring
    have hP0Z : (0 : ℤ) ≤ (P : ℤ) := by positivity
    omega
  set N₀ : ℕ := (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hN₀def
  set P' : ℕ := (z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hP'def
  have haN₀ : (N₀ : ℤ) = min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (le_trans hN0Z hage)
  have hP'val : (P' : ℤ) = z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (by linarith [hz1])
  have hzval : z = (N₀ : ℤ) + (P' : ℤ) := by rw [haN₀, hP'val]; ring
  have hNleN₀ : N ≤ N₀ := by
    have : (N : ℤ) ≤ (N₀ : ℤ) := by rw [haN₀]; exact hage
    exact_mod_cast this
  have hN₀le2N : N₀ ≤ 2 * N := by
    have : (N₀ : ℤ) ≤ 2 * N := by rw [haN₀]; exact min_le_right _ _
    exact_mod_cast this
  have hP'le : P' ≤ P := by
    have : (P' : ℤ) ≤ (P : ℤ) := by rw [hP'val]; linarith [hz2, hbma]
    exact_mod_cast this
  rw [haN₀.symm, hzval]
  exact vk_block_prefix_at hk hr hρ hP'le hY hNleN₀ hN₀le2N hN1 hjs2 hjsk htpos hD hW1 hW2a hW2b
    hW2c

/-! ## The per-scale prefix discharge (schedule witness) -/

/-- Exp-monotone (copy of `Window.vk_exp_mono_le`, private). -/
private lemma vk_exp_mono_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : Real.log A ≤ Real.log B) : A ≤ B := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hA, Real.exp_log hB] at this

set_option maxHeartbeats 1600000 in
-- The ~30 margin discharges (copied from `vk_window_scale`) exceed the default budget.
/-- **Prefix per-scale theorem** — prefix-of-window analogue of `vk_window_scale`.  Same schedule
witness `P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `js = m+2` and margins; concludes the prefix
bound `‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}` for `N < y ≤ 2N`.  Body identical to `vk_window_scale`
except the final consumer is `vk_window_prefix`. -/
theorem vk_window_scale_prefix {k r m N P Y : ℕ} {t ρ : ℝ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hqdef] at hP hDf
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmR11 : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm11
  have hmkR : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
  have humc : (0 : ℝ) ≤ (m : ℝ) - 11 := by linarith
  have hvmc : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ) - 8 := by linarith
  have hq0 : 0 ≤ q := by
    rw [hqdef, sub_nonneg, div_le_one hk1R]; linarith
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have : 0 ≤ ((m : ℝ) + 2) / ((k : ℝ) + 1) := by positivity
    linarith
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : 0 ≤ Real.log N := Real.log_nonneg hNR1
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlk0 : 0 ≤ Real.log (k : ℝ) := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  have hkl2nn : 0 ≤ ((k : ℝ) + 1) * Real.log 2 := by positivity
  have hj8 : 8 ≤ Real.log N := by linarith [hjf, hkl2nn, hlk0]
  have hP1 : 1 ≤ P := by
    rw [hP, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hNpos _
  have hPR1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg hPR1
  have hY1 : 1 ≤ Y := by
    rw [hY, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hPpos _
  have htpos : 0 < t :=
    lt_trans (show (0 : ℝ) < (N : ℝ) ^ (m - 1) by positivity) htlo
  have hlPlo : q * Real.log N ≤ Real.log P := vk_logP_ge hN1 hP
  have hlPub : Real.log P ≤ Real.log 2 + q * Real.log N := vk_logP_ub hN1 hq0 hP
  have hlYub : Real.log Y ≤ Real.log 2 + 1 / 2 * Real.log P := by
    have h := vk_logP_ub hP1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hY
    linarith [h]
  have hltub : Real.log t ≤ (m : ℝ) * Real.log N := by
    calc Real.log t ≤ Real.log ((N : ℝ) ^ m) := Real.log_le_log htpos hthi
      _ = (m : ℝ) * Real.log N := by rw [Real.log_pow]
  have hltlo : ((m : ℝ) - 1) * Real.log N ≤ Real.log t := by
    have h1 : Real.log ((N : ℝ) ^ (m - 1)) ≤ Real.log t :=
      Real.log_le_log (by positivity) htlo.le
    rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h1
    exact h1
  have h2kl2 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ Real.log N := by linarith [hjf, hlk0]
  have h13 : 3 * Real.log 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * Real.log N := by
    linarith only [hkl2nn, hlk0, hjf, mul_nonneg humc hj0]
  have h1mq : (1 - q) * Real.log N = ((m : ℝ) + 2) * Real.log N / ((k : ℝ) + 1) := by
    rw [hqdef]; field_simp; ring
  have h3l2q : 3 * Real.log 2 ≤ (1 - q) * Real.log N := by
    rw [h1mq, le_div_iff₀ hk1R]; linarith [h13]
  have hguardR : (4 : ℝ) * (P : ℝ) ≤ (N : ℝ) := by
    apply vk_exp_mono_le (by positivity) hNpos
    have h4P : Real.log (4 * (P : ℝ)) = 2 * Real.log 2 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hPpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4P]; linarith [hlPub, h3l2q]
  have h4PN : 4 * P ≤ N := by exact_mod_cast hguardR
  have hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ Real.log P := le_trans hDf hlPlo
  have hYP : Y ≤ P := by
    rw [hY]
    apply Nat.ceil_le.mpr
    calc (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (P : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hPR1 (by norm_num)
      _ = (P : ℝ) := Real.rpow_one _
  have hlogPY : Real.log ((P + Y : ℕ) : ℝ) ≤ 2 * Real.log 2 + q * Real.log N := by
    have hYR : (Y : ℝ) ≤ (P : ℝ) := by exact_mod_cast hYP
    calc Real.log ((P + Y : ℕ) : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
          apply Real.log_le_log (by push_cast; positivity)
          push_cast; linarith
      _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (ne_of_gt hPpos)
      _ ≤ 2 * Real.log 2 + q * Real.log N := by linarith [hlPub]
  have hW1m : Real.log t + ((k + 1 : ℕ) : ℝ) * Real.log ((P + Y : ℕ) : ℝ)
      ≤ (k : ℝ) * Real.log N := by
    have hexp : ((k : ℝ) + 1) * (2 * Real.log 2 + q * Real.log N)
        = 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [hqdef]; field_simp; ring
    have h2 : ((k : ℝ) + 1) * Real.log ((P + Y : ℕ) : ℝ)
        ≤ 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [← hexp]; exact mul_le_mul_of_nonneg_left hlogPY (by positivity)
    have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkcast]
    linarith only [h2, hltub, hlk0, hjf]
  have hW2cm : Real.log 8 + 2 * Real.log k + 1 / 2 * Real.log P ≤ Real.log N := by
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by linarith only [h3l2q, hl20]
    have hkl2 : 3 * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20
      exact_mod_cast (show 3 ≤ k by omega)
    rw [hl8]
    linarith [hjf, hlPub, hqj_le, hkl2, hlk0, hl20]
  have hW2bm : Real.log t + Real.log Y ≤ ((m + 2 + 1 : ℕ) : ℝ) * Real.log N := by
    have hc : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by linarith only [h3l2q, hl20]
    rw [hc]
    linarith only [h3l2q, hltub, hlYub, hlPub, hkl2nn, hlk0, hjf]
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hf : 9 / 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * ((k : ℝ) - (m : ℝ) - 1) := by
    linarith only [hmkR, hmR11, mul_nonneg humc hvmc]
  have hqj : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * (q * Real.log N) := by
    have hqeq : q * Real.log N = ((k : ℝ) - (m : ℝ) - 1) * Real.log N / ((k : ℝ) + 1) := by
      rw [hqdef]; field_simp; ring
    rw [hqeq, mul_div_assoc', le_div_iff₀ hk1R]
    linarith only [mul_le_mul_of_nonneg_right hf hj0]
  have hlPq : ((m : ℝ) + 2) * (q * Real.log N) ≤ ((m : ℝ) + 2) * Real.log P :=
    mul_le_mul_of_nonneg_left hlPlo (by linarith)
  have hl2π : Real.log (2 * π) ≤ 7 := by
    have hπ4 : π ≤ 4 := Real.pi_le_four
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * π by positivity)
    linarith
  have hl2lb : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hl4k : 0 ≤ Real.log (4 * (k : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  have hW2am : (-((m + 2 : ℕ) : ℝ) - ρ) * Real.log P - Real.log (4 * (k : ℝ))
      ≤ Real.log t - Real.log (2 * π) - ((m + 2 + 1 : ℕ) : ℝ) * Real.log (2 * (N : ℝ)) := by
    have hcjs : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    have hcjs1 : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hl2N : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hml2 : ((m : ℝ) + 9) * Real.log 2 ≤ ((k : ℝ) + 1) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20; linarith
    have hkey : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * Real.log P := le_trans hqj hlPq
    rw [hcjs, hcjs1, hl2N]
    linarith only [hml2, hl4k, hl2lb, hl2π, hlPq, hqj, hltlo, hlk0, hjf, mul_nonneg hρ0 hlP0]
  exact vk_window_prefix (js := m + 2) hk hr hρ hY hP1 h4PN hN1 (by omega) (by omega) htpos hD
    (vk_hW1_form htpos hP1 hN1 hW1m)
    (vk_hW2a_form (by omega) hP1 hN1 htpos hW2am)
    (vk_hW2b_form htpos hY1 hN1 hW2bm)
    (vk_hW2c_form (by omega) hP1 hN1 hY hW2cm)
    y hy1 hy2

/-! ## The mid-branch prefix window (schedule) -/

set_option maxHeartbeats 4000000 in
-- The ~55-hypothesis schedule bookkeeping exceeds the default heartbeat budget.
/-- **Mid-branch prefix window** — prefix-of-window analogue of `vk_window_mid`.  Same schedule
and routing predicates; concludes the prefix bound `‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·exp(−Θ·logN)` for
every `N < y ≤ 2N`.  `vk_window_mid` (below) is its `y = 2N` case; the schedule proof lives here,
through `vk_window_scale_prefix` threaded with `(y, hy1, hy2)`. -/
theorem vk_window_mid_prefix {t : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) := by
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log t := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ x : ℝ, x = Real.log N := ⟨_, rfl⟩
  rw [← hLdef] at hL100 hk hm hjhi
  rw [← hjdef] at hm hjhi hroute ⊢
  obtain ⟨ℓ, hℓdef⟩ : ∃ x : ℝ, x = Real.log L := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ, x = L ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hAdef] at hk
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
  have hAexp : A = Real.exp (ℓ * (1 / 4)) := by
    rw [hAdef, Real.rpow_def_of_pos hL0, hℓdef]
  have hA25 : Real.exp 25 ≤ A := by
    rw [hAexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hA26 : (26 : ℝ) ≤ A := by
    have : (26 : ℝ) ≤ Real.exp 25 := by linarith [Real.add_one_le_exp (25 : ℝ)]
    linarith
  have hA0 : (0 : ℝ) < A := by linarith
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
  have hlog4k2 : Real.log (4 * (k : ℝ) ^ 2) ≤ 2 + 56 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h4 : Real.log 4 ≤ 2 := by
      exact_mod_cast Salt.Tactic.log_le_nat_of_le_pow 2 (by norm_num) (by norm_num)
    push_cast; linarith [hlnk_ub]
  have hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) := by
      apply mul_nonneg hk0R.le
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
      nlinarith only [hkR_lo, hA26, (Nat.cast_nonneg _ : 0 ≤ ↑k), (Nat.cast_nonneg _ : 0 ≤ ↑k)]
    have h1 : (⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ : ℝ)
        < (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) + 1 := Nat.ceil_lt_add_one h0
    have h2 : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (k : ℝ) * (2 + 56 / 100 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog4k2 hk0R.le
    have h3 : (k : ℝ) * 100 ≤ (k : ℝ) * ℓ := mul_le_mul_of_nonneg_left hℓ100 hk0R.le
    linarith only [h3, h2, h1, hkR_lo, hA26]
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_ceil_iff]
    apply mul_pos hk0R
    apply Real.log_pos
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
    nlinarith only [hkR_lo, hA26, (Nat.cast_nonneg _ : 0 ≤ ↑k), (Nat.cast_nonneg _ : 0 ≤ ↑k)]
  have hr0R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
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
    nlinarith only [hl20, hj0, h1, Real.log_two_gt_d9]
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
  have hℓ2ge : (10000 : ℝ) ≤ ℓ ^ 2 := by nlinarith only [hℓ100]
  have hA2ge : (676 : ℝ) ≤ A ^ 2 := by nlinarith only [hA26]
  have hLj_ub : L / j ≤ A / 693 := by
    have hstep : L * 693 ≤ A * j := by
      have h1 : A * (693 * (A ^ 3 * ℓ ^ 2)) ≤ A * j := mul_le_mul_of_nonneg_left hjlo hA0.le
      have h2 : A * (693 * (A ^ 3 * ℓ ^ 2)) = 693 * L * ℓ ^ 2 := by rw [hL_A4]; ring
      rw [h2] at h1
      nlinarith only [hL0, hℓ2ge, hA2ge, h1, hL_A4, sq_nonneg A]
    rw [div_le_div_iff₀ hj0 (by norm_num)]
    linarith [hstep]
  have hmA : (m : ℝ) ≤ A / 693 + 1 := le_trans hm_ub.le (by linarith [hLj_ub])
  have hmk : m + 8 ≤ k := by
    have h1 : (m : ℝ) + 8 ≤ (k : ℝ) := by linarith only [hLj_ub, hm_ub, hLj10, hkR_lo]
    exact_mod_cast h1
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
  have hlnD_ub : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ 52 * A ^ 3 * ℓ ^ 2 :=
    vk_lnD_budget hkR_lo hkR_ub hr_ub hlnk_ub hlnk0 hr0R hk0R hl21 hA26 hℓ100 hA0 hℓ0
  have hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N := by
    rw [← hjdef]
    have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 654 / 1000 := by
      rw [div_le_iff₀ hk1R]
      linarith only [hLj_ub, hm_ub, hLj10, hkR_lo]
    have hβj : (346 / 1000) * j ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * j := by
      apply mul_le_mul_of_nonneg_right _ hj0.le
      linarith [hle]
    have hfloor : 52 * A ^ 3 * ℓ ^ 2 ≤ (346 / 1000) * j := by
      have h : (346 / 1000) * (693 * (A ^ 3 * ℓ ^ 2)) ≤ (346 / 1000) * j :=
        mul_le_mul_of_nonneg_left hjlo (by norm_num)
      linarith only [hjlo, hD0]
    linarith only [hlnD_ub, hfloor, hβj]
  have hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N := by
    rw [← hjdef]
    have hkℓ : 2 * ((k : ℝ) + 1) + 4 * (28 / 100) * ℓ + 8 ≤ (346 / 1000) * j := by
      have hbig : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := vk_Aℓ_cube hA26 hℓ100 hA0 hℓ0
      have hjge : 693 * (A * ℓ) ≤ j := le_trans (by linarith only [hbig]) hjlo
      nlinarith only [hℓ100, hA26, hbig, hjlo, hkR_ub]
    have h1 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ 2 * ((k : ℝ) + 1) := by nlinarith [hl21, hk0R]
    have h2 : 4 * Real.log k ≤ 4 * (28 / 100) * ℓ := by linarith [hlnk_ub]
    have hj346 : (346 / 1000) * j ≤ j := by linarith only [hkℓ, hLj_ub, hLj10, hkR_lo, hℓ100]
    linarith only [h1, h2, hkℓ, hj346]
  have hlPlo : (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N ≤ Real.log P :=
    vk_logP_ge hN1 hPdef
  have hlogN0 : (0 : ℝ) ≤ Real.log N := by rw [← hjdef]; exact hj0.le
  have hlP_half : j / 2 ≤ Real.log P := by
    have hβle : (1 : ℝ) / 2 ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
      have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hk1R]; linarith only [hLj_ub, hm_ub, hLj10, hkR_lo]
      linarith [hle]
    have hstep : (1 : ℝ) / 2 * Real.log N ≤ Real.log P :=
      le_trans (mul_le_mul_of_nonneg_right hβle hlogN0) hlPlo
    rw [hjdef]; linarith only [hstep]
  have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hr_ub2 : (16 * (k : ℝ) * r) ≤ 16 * (11 / 10 * A) * (6 / 10 * (11 / 10 * A) * ℓ) := by
    apply mul_le_mul (by linarith only [hkR_ub]) _ hr0R.le (by positivity)
    apply le_trans hr_ub; nlinarith only [hℓ100, hkR_ub]
  have h16kr : (0 : ℝ) < 16 * (k : ℝ) * r := mul_pos (mul_pos (by norm_num) hk0R) hr0R
  have hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ := by
    rw [hρdef, div_le_div_iff₀ (by positivity) h16kr]
    linarith only [h16kr, hr_ub2]
  have hΘlogN : vkTheta t * j ≤ ρ * Real.log P := by
    rw [hΘval]
    exact vk_theta_saving hA26 hℓ100 hj0 hρpos hρlo hlP_half
  have hbound := vk_window_scale_prefix (k := k) (r := r) (m := m) (N := N) (P := P) (Y := Y)
    (ρ := ρ) (t := t) hk19 hr hρdef hm11 hmk hN1 hPdef hYdef htlo hthi hDf hjf y hy1 hy2
  refine le_trans hbound ?_
  have hPρ : (P : ℝ) ^ (-ρ) = Real.exp (-(ρ * Real.log P)) := by
    have hPpos : (0 : ℝ) < (P : ℝ) := by
      rw [hPdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (by rw [Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hN0R _)
    rw [Real.rpow_def_of_pos hPpos]; congr 1; ring
  rw [hPρ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith [hΘlogN])

end VkPrefix

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
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) :=
  vk_window_mid_prefix ht0 hL100 hN2 hk hr hm hroute hjhi (2 * N) (by omega) le_rfl

end Salt.Vk
