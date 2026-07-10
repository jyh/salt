/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard

/-!
# Rung 4b — the level-of-distribution interface (`HasLevel`)

Design: `docs/blueprints/lod-interface-design.md`.  `HasLevel θ` is the
Bombieri–Vinogradov-shaped hypothesis: for every log-power saving `A` there is a
log-power *haircut* `B = B(A)` on the modulus range `x^θ/(log x)^B`.  The `∀A ∃B`
order is BV's exact shape — a fixed-`B` or `∀B` variant would be strictly
stronger than BV and unusable by the eventual BV instantiation.  `EH θ` is the
`B = 0` special case (`EH_hasLevel`), so anything proved from `HasLevel (1/2)`
specializes to the landed `EH (1/2)` results and becomes unconditional the day
BV is formalized.
-/

open Finset

/-- **The level-of-distribution hypothesis (BV shape).** For every `A > 0`
there is a haircut `B = B(A) ≥ 0` and constant `C` with the discrepancy over
moduli `≤ x^θ/(log x)^B` bounded by `C·x/(log x)^A`.  `EH θ = HasLevel θ` at
`B = 0`. -/
def HasLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (B C : ℝ), 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / (Real.log x) ^ B⌋₊, maxDiscrepancy x q)
      ≤ C * (x : ℝ) / (Real.log x) ^ A

/-- `EH θ → HasLevel θ`: the full-range EH bound is the `B = 0` haircut
(`(log x)^0 = 1`). -/
theorem EH_hasLevel {θ : ℝ} (hEH : EH θ) : HasLevel θ := by
  intro A hA
  obtain ⟨C, hC⟩ := hEH A hA
  refine ⟨0, C, le_refl 0, fun x hx => ?_⟩
  rw [Real.rpow_zero, div_one]
  exact hC x hx

/-- `HasLevel` is antitone in `θ` (smaller level ⟹ smaller modulus range;
same `B, C` witnesses work). -/
theorem HasLevel_antitone {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) (_hθ₁ : 0 ≤ θ₁)
    (hL : HasLevel θ₂) : HasLevel θ₁ := by
  intro A hA
  obtain ⟨B, C, hB0, hC⟩ := hL A hA
  refine ⟨B, C, hB0, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hxr : (1 : ℝ) ≤ (x : ℝ) := le_of_lt hx1
  have hden : (0 : ℝ) < (Real.log x) ^ B := Real.rpow_pos_of_pos (Real.log_pos hx1) B
  have hsub : Finset.Icc 1 ⌊(x : ℝ) ^ θ₁ / (Real.log x) ^ B⌋₊
      ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ₂ / (Real.log x) ^ B⌋₊ := by
    apply Finset.Icc_subset_Icc_right
    apply Nat.floor_le_floor
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hxr h)
      (le_of_lt (inv_pos.mpr hden))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => maxDiscrepancy_nonneg x q)).trans (hC x hx)
