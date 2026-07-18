/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Windows
import Salt.Vk.Core

/-!
# VMVT-VK rung R5b (transcendental half, plumbing) — the window assembly `vk_window_bound`

`vk_window_bound` is the spine of R5b: it assembles the per-block Weyl bound `vk_block_core`
(applied at every block `N₀ ∈ [N, 2N)` of the equal-length partition `c i = min (N+iP) (2N)`)
through the landed ladder `vk_ladder_bound` into the freeze's dyadic window bound

  `‖∑_{(N,2N]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}`.

It is *growth-of-parameters-agnostic*: it consumes the `vk_block_core` hypotheses only in their
per-scale **worst-case** forms over the block range `N₀ ∈ [N, 2N)` (`hD` is `N₀`-independent;
`hW1`, `W2b`, `W2c` are worst at `N₀ = N`; `W2a` is worst at `N₀ = 2N`), reducing the per-block
Diophantine system to five scale-level inequalities.  Deriving those five from the window-select
parameters (`j = log N`, `r₀ = ⌈L/j⌉`, `β = (r₀+1)/(k+1)`, `P = ⌈N^{1−β}⌉`, `Y = ⌈P^{1/2}⌉`,
`j* = r₀+2`) is the transcendental grind tracked in `docs/blueprints/flags.md`; the numeric
refuter `scripts/vk_minpow_check.py` certifies they hold with generous margins.
-/

namespace Salt.Vk

open Finset Real Salt.ExpSum
open scoped BigOperators

/-- **Per-block `vk_block_core` at an interior block `N₀ ∈ [N, 2N]`.**  Given the per-scale
worst-case hypotheses (`hW1` at `N`, `hW2a` at `2N`, `hW2b`/`hW2c` at `N`), monotonicity in `N₀`
recovers the block-specific `vk_block_core` hypotheses, so the per-block Weyl bound holds. -/
private lemma vk_block_at {k r P P' Y N N₀ : ℕ} {t ρ : ℝ} {js : ℕ}
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
  · -- hW1 at N₀ : t·((P+Y)/N₀)^{k+1} ≤ N₀⁻¹, from the cross-multiplied t·(P+Y)^{k+1} ≤ N^k ≤ N₀^k
    have hkey : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k :=
      le_trans hW1 (by gcongr)
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    calc t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k := hkey
      _ = ((N₀ : ℝ))⁻¹ * (N₀ : ℝ) ^ (k + 1) := by
          rw [pow_succ, mul_comm ((N₀ : ℝ) ^ k) (N₀ : ℝ), ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hN₀0), one_mul]
  · rw [Finset.mem_Icc]; exact ⟨hjs2, hjsk⟩
  · -- W2a at N₀
    have hpow : ((N₀ : ℝ)) ^ (js + 1) ≤ ((2 * N : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN₀0.le hN₀leR _
    calc (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
        ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := hW2a
      _ ≤ t / (2 * π * ((N₀ : ℝ)) ^ (js + 1)) := by gcongr
  · -- W2b at N₀
    have hpow : ((N : ℝ)) ^ (js + 1) ≤ ((N₀ : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN0pos.le hNleR _
    calc t * (Y : ℝ) / (2 * π * ((N₀ : ℝ)) ^ (js + 1))
        ≤ t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) := by gcongr
      _ ≤ 1 / 6 := hW2b
  · -- W2c at N₀
    calc 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := hW2c
      _ ≤ (N₀ : ℝ) := hNleR

/-- **R5b window bound — the `⌈N/P⌉`-block assembly (spine).**  For the window-select parameters at
scale `N`, with the guard `4P ≤ N` and the five per-scale worst-case `vk_block_core` hypotheses
(`hD` `N₀`-independent, `hW1`/`hW2b`/`hW2c` at `N`, `hW2a` at `2N`), the dyadic window `(N, 2N]`
of the ζ-phase Weyl sum obeys the freeze's `‖∑_{(N,2N]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}`.  Every block
`N₀ = min(N+iP)(2N) ∈ [N, 2N)` is discharged by `vk_block_at`; the ladder is `vk_ladder_bound`. -/
theorem vk_window_bound {k r P Y N : ℕ} {t ρ : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hP : 1 ≤ P) (h4P : 4 * P ≤ N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  apply vk_ladder_bound (fun n => eR (phi t n)) hP h4P
  intro i hi
  have hP0Z : (0 : ℤ) ≤ (P : ℤ) := by positivity
  have hiP0 : (0 : ℤ) ≤ (i : ℤ) * (P : ℤ) := by positivity
  have hN0Z : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hstep : ((i : ℤ) + 1) * (P : ℤ) = (i : ℤ) * (P : ℤ) + (P : ℤ) := by ring
  -- block endpoints and their basic order facts
  have hage : (N : ℤ) ≤ min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    le_min (by linarith) (by linarith)
  have hab : min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)
      ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) :=
    min_le_min (by linarith [hstep, hP0Z]) (le_refl _)
  have hale : min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ 2 * N := min_le_right _ _
  have hbma : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ (P : ℤ) := by
    omega
  set N₀ : ℕ := (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hN₀def
  set P' : ℕ := (min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hP'def
  have haN₀ : (N₀ : ℤ) = min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (le_trans hN0Z hage)
  have hP'val : (P' : ℤ) = min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (by linarith [hab])
  have hbval : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) = (N₀ : ℤ) + (P' : ℤ) := by
    rw [haN₀, hP'val]; ring
  -- transfer the ℤ-facts to the Nat parameters
  have hNleN₀ : N ≤ N₀ := by
    have : (N : ℤ) ≤ (N₀ : ℤ) := by rw [haN₀]; exact hage
    exact_mod_cast this
  have hN₀le2N : N₀ ≤ 2 * N := by
    have : (N₀ : ℤ) ≤ 2 * N := by rw [haN₀]; exact hale
    exact_mod_cast this
  have hP'le : P' ≤ P := by
    have : (P' : ℤ) ≤ (P : ℤ) := by rw [hP'val]; exact hbma
    exact_mod_cast this
  rw [haN₀.symm, hbval]
  exact vk_block_at hk hr hρ hP'le hY hNleN₀ hN₀le2N hN1 hjs2 hjsk htpos hD hW1 hW2a hW2b hW2c

/-! ## Transcendental discharge of the per-scale hypotheses (from clean log-margins)

Each `vk_block_core` hypothesis converts from a clean log-form margin (exactly what the refuter
`scripts/vk_minpow_check.py` verifies) to the exact rpow/pow/π form.  These conversions land the
Lean-painful *nonlinear* content (ceils, `rpow`, `π` bounds); the residual is the *linear-in-logs*
margin arithmetic from the window band `r₀ = ⌈L/j⌉ ∈ [11, k−8]`, `j ∈ (j_cut, L/10]`. -/

/-- **`log P ≥ q·log N`** — the ceil'd-power log floor.  With `P = ⌈N^q⌉`, `q ≥ 0`, `N ≥ 1`,
`P ≥ N^q` gives `log P ≥ q·log N`.  Reused by the `hD`/`hW1`/`hW2` margins. -/
lemma vk_logP_ge {N P : ℕ} {q : ℝ} (hN : 1 ≤ N) (hPdef : P = ⌈(N : ℝ) ^ q⌉₊) :
    q * Real.log N ≤ Real.log P := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hNq_pos : (0 : ℝ) < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos q
  have hPge : (N : ℝ) ^ q ≤ (P : ℝ) := by rw [hPdef]; exact Nat.le_ceil _
  calc q * Real.log N = Real.log ((N : ℝ) ^ q) := (Real.log_rpow hNpos q).symm
    _ ≤ Real.log P := Real.log_le_log hNq_pos hPge

/-- **`log P ≤ q·log N + log 2`** — the ceil'd-power log ceiling.  With `P = ⌈N^q⌉ < N^q + 1 ≤
2·N^q` (using `N^q ≥ 1`), `log P ≤ log 2 + q·log N`.  Dual to `vk_logP_ge`. -/
lemma vk_logP_ub {N P : ℕ} {q : ℝ} (hN : 1 ≤ N) (hq : 0 ≤ q) (hPdef : P = ⌈(N : ℝ) ^ q⌉₊) :
    Real.log P ≤ Real.log 2 + q * Real.log N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNq1 : (1 : ℝ) ≤ (N : ℝ) ^ q := Real.one_le_rpow hNR hq
  have hNq_pos : (0 : ℝ) < (N : ℝ) ^ q := by linarith
  have hPub : (P : ℝ) ≤ 2 * (N : ℝ) ^ q := by
    rw [hPdef]
    have h : (⌈(N : ℝ) ^ q⌉₊ : ℝ) < (N : ℝ) ^ q + 1 := Nat.ceil_lt_add_one hNq_pos.le
    linarith [hNq1]
  have hPge : (N : ℝ) ^ q ≤ (P : ℝ) := by rw [hPdef]; exact Nat.le_ceil _
  have hPpos : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le hNq_pos hPge
  calc Real.log P ≤ Real.log (2 * (N : ℝ) ^ q) := Real.log_le_log hPpos hPub
    _ = Real.log 2 + q * Real.log N := by rw [Real.log_mul (by norm_num) (ne_of_gt hNq_pos),
        Real.log_rpow hNpos]

/-- Exp-monotone: from `log A ≤ log B` (both positive) conclude `A ≤ B`. -/
private lemma vk_exp_mono_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : Real.log A ≤ Real.log B) : A ≤ B := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hA, Real.exp_log hB] at this

/-- **`hW2c` discharge** — `4k²Y ≤ N` from the clean log-margin `log 8 + 2 log k + ½ log P ≤ log N`.
`Y = ⌈P^{1/2}⌉ ≤ 2 P^{1/2}` (since `P^{1/2} ≥ 1`), so `4k²Y ≤ 8k²P^{1/2}`; the margin closes it. -/
lemma vk_hW2c_form {k P Y N : ℕ} (hk : 1 ≤ k) (hP : 1 ≤ P) (hN : 1 ≤ N)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hmargin : Real.log 8 + 2 * Real.log k + (1 / 2) * Real.log P ≤ Real.log N) :
    4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hsqrt1 : (1 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hPR (by norm_num)
  have hsqrtpos : (0 : ℝ) < (P : ℝ) ^ ((1 : ℝ) / 2) := by linarith
  have hY2 : (Y : ℝ) ≤ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hY]
    have h : (⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊ : ℝ) < (P : ℝ) ^ ((1 : ℝ) / 2) + 1 :=
      Nat.ceil_lt_add_one (le_of_lt hsqrtpos)
    linarith [hsqrt1]
  have hprodpos : (0 : ℝ) < 8 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hlogprod : Real.log (8 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2))
      = Real.log 8 + 2 * Real.log k + (1 / 2) * Real.log P := by
    rw [Real.log_mul (by positivity) (ne_of_gt hsqrtpos),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_rpow hPpos]
    push_cast; ring
  have hle : 8 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) :=
    vk_exp_mono_le hprodpos hNpos (by rw [hlogprod]; exact hmargin)
  calc 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ 4 * (k : ℝ) ^ 2 * (2 * (P : ℝ) ^ ((1 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left hY2 (by positivity)
    _ = 8 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ (N : ℝ) := hle

/-- **`hW2b` discharge** — `t·Y/(2π·N^{js+1}) ≤ 1/6` from the clean log-margin
`log t + log Y ≤ (js+1)·log N`.  First `t·Y ≤ N^{js+1}` (exp), then `π ≥ 3` gives
`N^{js+1} ≤ (1/6)(2π·N^{js+1})`. -/
lemma vk_hW2b_form {N Y js : ℕ} {t : ℝ} (htpos : 0 < t) (hY : 1 ≤ Y) (hN : 1 ≤ N)
    (hm : Real.log t + Real.log Y ≤ ((js + 1 : ℕ) : ℝ) * Real.log N) :
    t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6 := by
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hY
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hNjs : (0 : ℝ) < ((N : ℝ)) ^ (js + 1) := by positivity
  have hprodpos : (0 : ℝ) < t * (Y : ℝ) := by positivity
  have hlogtY : Real.log (t * (Y : ℝ)) = Real.log t + Real.log Y :=
    Real.log_mul (ne_of_gt htpos) (ne_of_gt hYpos)
  have hlogNjs : Real.log (((N : ℝ)) ^ (js + 1)) = ((js + 1 : ℕ) : ℝ) * Real.log N := by
    rw [Real.log_pow]
  have htY : t * (Y : ℝ) ≤ ((N : ℝ)) ^ (js + 1) :=
    vk_exp_mono_le hprodpos hNjs (by rw [hlogtY, hlogNjs]; exact hm)
  have hpi3 : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  rw [div_le_iff₀ (by positivity)]
  calc t * (Y : ℝ) ≤ ((N : ℝ)) ^ (js + 1) := htY
    _ ≤ 1 / 6 * (2 * π * ((N : ℝ)) ^ (js + 1)) := by
        nlinarith [mul_nonneg (by linarith [hpi3] : (0 : ℝ) ≤ π - 3) hNjs.le]

/-- **`hW1` discharge** — the cross-multiplied Taylor-window bound `t·(P+Y)^{k+1} ≤ N^k` from the
clean log-margin `log t + (k+1)·log(P+Y) ≤ k·log N`. -/
lemma vk_hW1_form {k P Y N : ℕ} {t : ℝ} (htpos : 0 < t) (hP : 1 ≤ P) (hN : 1 ≤ N)
    (hm : Real.log t + ((k + 1 : ℕ) : ℝ) * Real.log ((P + Y : ℕ) : ℝ) ≤ (k : ℝ) * Real.log N) :
    t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hPYpos : (0 : ℝ) < ((P + Y : ℕ) : ℝ) := by
    have : 1 ≤ P + Y := le_trans hP (Nat.le_add_right _ _)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hApos : (0 : ℝ) < t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) := by positivity
  have hBpos : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  apply vk_exp_mono_le hApos hBpos
  have hlogA : Real.log (t * (((P + Y : ℕ) : ℝ)) ^ (k + 1))
      = Real.log t + ((k + 1 : ℕ) : ℝ) * Real.log ((P + Y : ℕ) : ℝ) := by
    rw [Real.log_mul (ne_of_gt htpos) (by positivity), Real.log_pow]
  have hlogB : Real.log ((N : ℝ) ^ k) = (k : ℝ) * Real.log N := by
    rw [Real.log_pow]
  rw [hlogA, hlogB]; exact hm

/-- **`hW2a` discharge** — `P^{−js−ρ}/(4k) ≤ t/(2π·(2N)^{js+1})` from the expanded log-margin. -/
lemma vk_hW2a_form {k P N js : ℕ} {t ρ : ℝ} (hk : 1 ≤ k) (hP : 1 ≤ P) (hN : 1 ≤ N) (htpos : 0 < t)
    (hm : (-(js : ℝ) - ρ) * Real.log P - Real.log (4 * k)
        ≤ Real.log t - Real.log (2 * π) - ((js + 1 : ℕ) : ℝ) * Real.log (2 * N)) :
    (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k) ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hApos : (0 : ℝ) < (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k) := by positivity
  have hBpos : (0 : ℝ) < t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := by positivity
  apply vk_exp_mono_le hApos hBpos
  have hlogA : Real.log ((P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k))
      = (-(js : ℝ) - ρ) * Real.log P - Real.log (4 * k) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hPpos]
  have hlogB : Real.log (t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
      = Real.log t - Real.log (2 * π) - ((js + 1 : ℕ) : ℝ) * Real.log (2 * N) := by
    rw [Real.log_div (ne_of_gt htpos) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  rw [hlogA, hlogB]; exact hm

/-! ## The per-scale discharge at the amended window-select witness (WALL 1)

`vk_window_scale` instantiates the whole R5b system at the (VK-8-amended) witness
`β = (m+2)/(k+1)` — one notch above the freeze's `(r₀+1)/(k+1)`; the notch retires the hW1
integer-corner obstruction (#206) while keeping `j* = m+2` and the `t`-window semantics
`N^{m−1} < t ≤ N^m` (`m = ⌈L/j⌉`) unchanged.  The five margins all hold with explicit slack on
the band `m ∈ [11, k−8]`; the W2a corner is the quadratic
`(m+2)(k−m−1) − (9/2)(k+1) = 1 + (5/2)u + (17/2)v + uv ≥ 0` (`u = m−11`, `v = k−m−8`). -/

set_option maxHeartbeats 1600000 in
-- The five margin discharges thread ~40 shared log-atom facts through staged `nlinarith` calls;
-- the default budget times out in the W2a corner arithmetic.
/-- **WALL 1 per-scale theorem — the window-select discharge.**  At the amended witness
`P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `js = m+2` on the band `11 ≤ m`, `m+8 ≤ k`, with the
`hD` P-floor (in `(1−β)·log N` form) and the `j`-floor `2(k+1)log 2 + 4 log k + 8 ≤ log N`, every
`t` in the scale window `N^{m−1} < t ≤ N^m` obeys the freeze's dyadic window bound. -/
theorem vk_window_scale {k r m N P Y : ℕ} {t ρ : ℝ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  -- ## Setup: positivity and the basic cast facts (`q` opaque to avoid defeq storms)
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
  -- ## Log bounds for P, Y, t
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
  -- ## The guard 4P ≤ N
  have h2kl2 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ Real.log N := by linarith [hjf, hlk0]
  have h13 : 3 * Real.log 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * Real.log N := by
    nlinarith [h2kl2, mul_nonneg humc hj0, mul_nonneg hl20 hk1R.le]
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
  -- ## hD: the P-floor
  have hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ Real.log P := le_trans hDf hlPlo
  -- ## The W1 margin
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
    nlinarith [hltub, h2, hjf, hlk0]
  -- ## The W2c margin
  have hW2cm : Real.log 8 + 2 * Real.log k + 1 / 2 * Real.log P ≤ Real.log N := by
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    have hkl2 : 3 * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20
      exact_mod_cast (show 3 ≤ k by omega)
    rw [hl8]
    linarith [hjf, hlPub, hqj_le, hkl2, hlk0, hl20]
  -- ## The W2b margin
  have hW2bm : Real.log t + Real.log Y ≤ ((m + 2 + 1 : ℕ) : ℝ) * Real.log N := by
    have hc : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    rw [hc]
    nlinarith [hltub, hlYub, hlPub, hqj_le, hj8, hl21, hl20]
  -- ## The W2a margin (the corner: (m+2)(k−m−1) ≥ (9/2)(k+1) on the band)
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hf : 9 / 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * ((k : ℝ) - (m : ℝ) - 1) := by
    nlinarith [mul_nonneg humc hvmc]
  have hqj : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * (q * Real.log N) := by
    have hqeq : q * Real.log N = ((k : ℝ) - (m : ℝ) - 1) * Real.log N / ((k : ℝ) + 1) := by
      rw [hqdef]; field_simp; ring
    rw [hqeq, mul_div_assoc', le_div_iff₀ hk1R]
    nlinarith [mul_le_mul_of_nonneg_right hf hj0]
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
    nlinarith [hltlo, hkey, hl2π, hl4k, hjf, hml2, mul_nonneg hρ0 hlP0, hlk0, hl2lb]
  -- ## Assemble via `vk_window_bound` at `js = m + 2`
  exact vk_window_bound (js := m + 2) hk hr hρ hY hP1 h4PN hN1 (by omega) (by omega) htpos hD
    (vk_hW1_form htpos hP1 hN1 hW1m)
    (vk_hW2a_form (by omega) hP1 hN1 htpos hW2am)
    (vk_hW2b_form htpos hY1 hN1 hW2bm)
    (vk_hW2c_form (by omega) hP1 hN1 hY hW2cm)

end Salt.Vk
