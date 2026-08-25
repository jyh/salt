/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4BridgeCover
import Salt.MR.M4BridgeIntegral
import Salt.MR.M4Window

/-!
# `MRTPortRowLam` — THE SIEVE-FREE ROW DESCENT (node D8)

The unsieved twin of `M4Join.M4RowMeanSq` / `m4_blockMeanSq_of_rowMeanSq`: the same row
input with `M4BridgeCover.doorSievedCoeff M` replaced by the bare Liouville datum
`M4Window.lamCoeff`, descended all the way to the squared door integral.

⟦WHY THE SIEVE IS NOT NEEDED⟧ the only place the sieved route touches the coefficient is
the coverage slot `hcov` of `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le_ladder`, and
that slot is discharged by `M4BridgeIntegral.hcov_of_seamS0`, which is GENERIC in `c`: it
proves `c m = 0` by `absurd` on a membership that `mem_seamS0_of_block_window` already
supplies, so the hypothesis is vacuous and no support statement about `c` is ever read.
Hence the descent runs verbatim at `c := lamCoeff`.

⟦THE ONE GATE THAT IS NOT FREE⟧ the absorption step (`M4BridgeCover.door_weight_absorb`)
needs `0 ≤ MS H`, which the statement does not assume.  It is *derived*: `hreach` at `k = 0`
would read `R.x ≤ R.x / R.ω`, contradicting `2 ≤ R.x` and `2 ≤ R.ω` (`doorLadder _ _ 0 = x`),
so `0 < k`; and then `hrow` at `i = 0` bounds `MS H` below by a nonnegative integral.

⛔ **STALE WHEN WRITTEN, CORRECTED 2026-08-25.**  The line below was true at the moment the
executor wrote it and false within the hour: this module IS rooted — `Salt/MR/All.lean:393`
imports it and both declarations sit in the `#audit_axioms` tail (full rooted build 08/25,
`saltbuild EXIT=0`, ✓ 7096 / ✗ 0).  The original sentence is kept rather than deleted:

> This module is NOT rooted in any aggregate — it must be built targeted.

*The rooting was the maestro's own act, so this note was stale by that same hand — a claim
invalidated by the edit that consumed it.  Found by a completeness critic, not by me.*
-/

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **THE SIEVE-FREE ROW INPUT.**  `M4Join.M4RowMeanSq` (`M4Join.lean:311`) with
`doorSievedCoeff M` replaced by `lamCoeff` and the `M` binder dropped. -/
def M4RowMeanSqLam (R : ChowlaRegime) (k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorCoeffPhase lamCoeff α)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

theorem m4_doorSq_of_rowMeanSqLam {R : ChowlaRegime} {k : ℕ} {MS : ℕ → ℝ}
    (hreach : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω)
    (hpow : 2 ^ (k + 1) ≤ R.x)
    (hk3 : (k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹)
    (hrow : M4RowMeanSqLam R k MS) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum lamCoeff H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ 3 * (MS H * (H : ℝ) ^ 2)
              + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ)
                  / ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹
:= by
  intro H _ hlo hhi α harc
  have hH0 : 0 < H := by
    have := R.hHlo_floor
    omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹ :=
    door_norm_pos R.hx R.hω
  -- ⟦the ladder is nonempty: `hreach` at `k = 0` would say `x ≤ x / ω`⟧
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      have hr := hreach H hlo hhi
      rw [doorLadder_zero] at hr
      have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
      have h2 : 2 ≤ R.x := R.hx
      omega
    · exact hk
  -- ⟦the grade is a grade: the row input's left side is a nonnegative integral⟧
  have hMS0 : 0 ≤ MS H := by
    refine le_trans ?_ (hrow H hlo hhi α harc 0 hk0)
    have hX : (0 : ℝ) ≤ ((doorLadder R.x H (0 + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    refine mul_nonneg (by positivity) ?_
    exact intervalIntegral.integral_nonneg (by linarith) (fun y _ => by positivity)
  have hP : (0 : ℝ) ≤ (H : ℝ) ^ 2 * MS H := by positivity
  -- ⟦B-4 per block, with the coverage datum free at the seam⟧
  have hblk : ∀ i < k, ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ‖absWindowSum lamCoeff H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 * MS H := by
    intro i hik
    have hfit := doorLadder_fit R.x H i
    have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
            (doorLadder R.x H (i + 1) : ℝ) → lamCoeff m = 0 :=
      hcov_of_seamS0 lamCoeff (A := doorLadder R.x H (i + 1))
        (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
        (by omega)
    exact sum_Ioc_absWindowSum_sq_div_le_ladder lamCoeff
      (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) α
      (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov (hrow H hlo hhi α harc i hik)
  -- ⟦§6: compose over the ladder and normalise⟧
  have hbridge := m4_bridge_door_sq_le (x := R.x) (H := H) (ω := R.ω) (k := k)
    (c := lamCoeff) (α := α) (MS := MS H) R.hx R.hω hxH (hreach H hlo hhi) hpow hblk
  -- ⟦the `k ≤ 3Z` absorption⟧
  have habs := door_weight_absorb (k := k)
    (Z := ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) (P := (H : ℝ) ^ 2 * MS H)
    (G := 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ)) hZ0 hk3 hP
  have heq : 3 * ((H : ℝ) ^ 2 * MS H) = 3 * (MS H * (H : ℝ) ^ 2) := by ring
  rw [heq] at habs
  linarith

end Salt.MR
