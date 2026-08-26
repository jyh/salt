/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BridgeAdapt

/-!
# MRT port (item 15), node D5 — A.1's RHS tail below any fixed `δ`

Dispatched from the frozen D-wave executor brief
(`2026-08-25-item15-D-WAVE-EXECUTOR-BRIEF-FROZEN.md`, node D5).  Two
declarations:

* **D5** `mul_exp_neg_le_two_div` — the ONE link turning a LOWER bound on the quality
  `mrtM` into an UPPER bound on A.1's first error term `exp(−M)·M`.  Route:
  `1 + M + M²/2 ≤ exp M` (`Real.quadratic_le_exp_of_nonneg`) gives `M²/2 ≤ exp M`,
  hence `M/exp M ≤ 2/M`.  No monotonicity is used.
* **D6** `mrtA1_rhs_tail_le` — A.1's second and third RHS summands fall below any fixed
  `δ > 0` past a single floor.  The whole analytic content is `loglog_absorb`
  (`Salt/MR/BridgeAdapt.lean:494`) at `C = 1`, `ε = 1/2`, whose `1 ≤ log X` half is what
  keeps the squared `loglog` signed correctly.  Because A.1 already carries `h ≤ X`, ONE
  floor serves both summands.

⛔ **SCOPE.**  These close **named residuals** on the δ₀-split road.  They do NOT compose
to the door: GAP α (the major arc) and GAP A.1 (`MRTThmA1` has no producer) remain open
and are class D.

The ℕ-floor a socket's `U1floor` slot eats is `⌈h₀⌉₊`, the idiom already at
`MRTPort.lean:110`.
-/

namespace Salt.MR

theorem mul_exp_neg_le_two_div {M : ℝ} (hM : 0 < M) :
    Real.exp (-M) * M ≤ 2 / M := by
  have hq := Real.quadratic_le_exp_of_nonneg hM.le
  have hE : (0 : ℝ) < Real.exp M := Real.exp_pos M
  have hsq : M ^ 2 / 2 ≤ Real.exp M := by nlinarith
  rw [Real.exp_neg, inv_mul_eq_div, div_le_div_iff₀ hE hM]
  nlinarith

theorem mrtA1_rhs_tail_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h X : ℝ, h₀ ≤ h → h ≤ X →
      Real.log (Real.log h) ^ 2 / Real.log h ^ 2
          + 1 / Real.log X ^ ((1 : ℝ) / 50)
        ≤ δ
    := by
  obtain ⟨X₀, hX₀pos, hX₀⟩ :=
    loglog_absorb (C := (1 : ℝ)) (ε := (1 : ℝ) / 2) zero_le_one (by norm_num)
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  set T : ℝ := max 1 (2 / δ) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hTr : 2 / δ ≤ T := le_max_right _ _
  have hTp : (0 : ℝ) < T ^ (50 : ℕ) := pow_pos hT0 50
  have hTeq : (T ^ (50 : ℕ)) ^ ((1 : ℝ) / 50) = T := by
    have hcast : (T ^ (50 : ℕ)) ^ ((1 : ℝ) / 50)
        = T ^ (((50 : ℕ) : ℝ) * ((1 : ℝ) / 50)) := by
      rw [← Real.rpow_natCast T 50, ← Real.rpow_mul hT0.le]
    rw [hcast]
    norm_num
  refine ⟨max X₀ (Real.exp (T ^ (50 : ℕ) + T)),
    lt_of_lt_of_le hX₀pos (le_max_left _ _), ?_⟩
  intro h X hh hhX
  have hexp_le : Real.exp (T ^ (50 : ℕ) + T) ≤ h := le_trans (le_max_right _ _) hh
  have hhpos : (0 : ℝ) < h := lt_of_lt_of_le (Real.exp_pos _) hexp_le
  have hlogh : T ^ (50 : ℕ) + T ≤ Real.log h := by
    have hmono := Real.log_le_log (Real.exp_pos (T ^ (50 : ℕ) + T)) hexp_le
    rwa [Real.log_exp] at hmono
  obtain ⟨hlog1, habs⟩ := hX₀ h (le_trans (le_max_left _ _) hh)
  have hlogh0 : (0 : ℝ) < Real.log h := lt_of_lt_of_le zero_lt_one hlog1
  -- FIRST SUMMAND.  `1 ≤ log h` signs the `loglog`, so squaring the absorption is legal.
  have hhalfsq : (Real.log h ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = Real.log h := by
    have hcast : (Real.log h ^ ((1 : ℝ) / 2)) ^ (2 : ℕ)
        = Real.log h ^ (((1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (Real.log h ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hlogh0.le]
    rw [hcast]
    norm_num
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log h) := Real.log_nonneg hlog1
  have hll : Real.log (Real.log h) ≤ Real.log h ^ ((1 : ℝ) / 2) := by linarith
  have hmss := mul_self_le_mul_self hll0 hll
  have hsq : Real.log (Real.log h) ^ 2 ≤ Real.log h := by nlinarith [hmss, hhalfsq]
  have hTle : T ≤ Real.log h := by linarith
  have h2d : 2 / δ ≤ Real.log h := le_trans hTr hTle
  have hdl : 2 ≤ δ * Real.log h := by
    have hq : δ * (2 / δ) = 2 := by field_simp
    have hstep : δ * (2 / δ) ≤ δ * Real.log h := mul_le_mul_of_nonneg_left h2d hδ.le
    linarith
  have hden : (0 : ℝ) < Real.log h ^ 2 := pow_pos hlogh0 2
  have hA : Real.log (Real.log h) ^ 2 / Real.log h ^ 2 ≤ δ / 2 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith [hsq, mul_le_mul_of_nonneg_right hdl hlogh0.le]
  -- SECOND SUMMAND.  `h ≤ X` pushes the same floor up to `X`; one floor serves both.
  have hlogX : T ^ (50 : ℕ) ≤ Real.log X := by
    have hmono := Real.log_le_log hhpos hhX
    linarith
  have hstepX : (T ^ (50 : ℕ)) ^ ((1 : ℝ) / 50) ≤ Real.log X ^ ((1 : ℝ) / 50) :=
    Real.rpow_le_rpow hTp.le hlogX (by norm_num)
  rw [hTeq] at hstepX
  have hA2 : 2 / δ ≤ Real.log X ^ ((1 : ℝ) / 50) := le_trans hTr hstepX
  have hB : 1 / Real.log X ^ ((1 : ℝ) / 50) ≤ δ / 2 := by
    have hpos : (0 : ℝ) < 2 / δ := by positivity
    have hstep := one_div_le_one_div_of_le hpos hA2
    rwa [one_div_div] at hstep
  linarith

end Salt.MR
