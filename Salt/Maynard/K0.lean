/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Ratio

/-!
# N6.3 — concrete threshold `k₀` (blueprint N6.3)

`ratio_prize` (N6.2) shows the Maynard variational ratio `I_g²/J_g` is at
least `(log k)/64` for all `k ≥ 2`.  N6.3 packages the elementary
consequence: for any fixed target `M`, there is a threshold `k₀` past
which the ratio exceeds `M`.

Indeed `(log k)/64 ≥ M ⟺ log k ≥ 64·M ⟺ k ≥ exp(64·M)`, so it suffices to
take `k₀ := max 2 ⌈exp(64·M)⌉₊` (the `max` with the N6.2 threshold keeps
`ratio_prize` applicable, and `⌈exp(64·M)⌉₊` forces `log k ≥ 64·M`).  The
threshold is symbolic — `exp(64·M)` is never evaluated.
-/

namespace Salt.Maynard

/-- **N6.3 — concrete `k₀`.**  For any fixed target `M`, past a symbolic
threshold `k₀` (of `exp(64·M)`-scale) the Maynard variational ratio
`I_g²/J_g` (with `A = log k`, `T = k^{1/8}/log k` substituted into the
N6.1 closed forms) exceeds `M`.  Proved from `ratio_prize`
(`≥ (log k)/64`) plus `(log k)/64 ≥ M ⟺ k ≥ exp(64·M)`. -/
theorem exists_k0_ratio_gt (M : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (Real.log (1 + Real.log k * ((k:ℝ)^(1/8:ℝ)/Real.log k)) / Real.log k) ^ 2
        / (((k:ℝ)^(1/8:ℝ)/Real.log k) / (1 + Real.log k * ((k:ℝ)^(1/8:ℝ)/Real.log k)))
      ≥ M := by
  obtain ⟨k₁, hk₁⟩ := ratio_prize
  refine ⟨max k₁ ⌈Real.exp (64 * M)⌉₊, fun k hk => ?_⟩
  -- Split the two threshold roles.
  have hk_k₁ : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk_ceil : ⌈Real.exp (64 * M)⌉₊ ≤ k := le_trans (le_max_right _ _) hk
  -- From `ratio_prize`: the ratio is at least `(log k)/64`.
  have hprize := hk₁ k hk_k₁
  simp only at hprize
  -- `exp(64·M) ≤ k`, hence `k > 0` and `64·M ≤ log k`.
  have hexp_le : Real.exp (64 * M) ≤ (k : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hk_ceil
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexp_le
  have hlog_ge : 64 * M ≤ Real.log k := by
    rw [← Real.le_log_iff_exp_le hkpos] at hexp_le
    exact hexp_le
  have hMle : M ≤ Real.log k / 64 := by linarith
  -- Chain: ratio ≥ (log k)/64 ≥ M.
  exact le_trans hMle hprize

end Salt.Maynard
