/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorEpsRung2
import Salt.MR.BigXiArc
import Salt.Entropy.Chowla.HeadPinLeaves
import Mathlib

/-!
# ⟦TIER S — THE FLAT DOOR IS NOT VACUOUS: `0 ∈ Ξ_H` ON THE BUILT REGIMES⟧ (`FlatDoorNonVacuity`)

The `L²` door `MRTUniformityXiL2 R ρ` sums over the large-spectrum set `Ξ_H = bigXi R.eps H`, so
a door on a regime whose `Ξ_H` were EMPTY at every `H` would be a statement about an empty sum.
This file is the control that rules that reading out for the LANDED flat door: the regimes that
`flatDoorEpsFamilyW_holds` builds can be taken with `0 ∈ Ξ_H` at EVERY `H` at or above their
`Hlo`, which is every `H` the door quantifies over.

The route is three steps, all about landed objects and all UNCONDITIONAL:

* `crownNV_expSum_zero` — `S_H(0)` is the real Mertens sum `∑_{p ∈ P} 1/p` over the Chowla prime
  window;
* `crownNV_zero_mem_bigXi` — the pinned Mertens leaf `primeWindow_sum_inv_ge_bounded` through
  `mem_bigXi_iff`: above a floor `H₀`, in the leaf's own regime, `0 ∈ Ξ_H`;
* `crownNV_above_flat_floor` — once the design constant `A` clears that `H₀` and `(2/ε²)²`, every
  `H ≥ flatDesignBase A` is in the leaf's regime, because `A ≤ exp (exp (3.2·A)) ≤ H`;

and `crownNV_landedW_nonvacuous` pays the two floors out of the landed door's own `∀ A₀`.

⚠ WHAT THIS DOES NOT SAY.  The floor `H₀` is the Mertens leaf's and is NON-EFFECTIVE (an `∃`, not
a numeral).  Membership of `0` says the sum is non-empty; that the `ξ = 0` TERM of the door is
strictly positive is a separate fact (a parity floor at odd `H`) and is NOT proved here — it is
proved downstream, in `FlatDoorParityFloor`.  Nothing here bears on twin primes.

Inside `namespace Salt.MR` the bare name `primeWindow` is `Salt.MR.primeWindow (P : ℝ) (n : ℕ)`,
NOT the Chowla prime window; every occurrence below is QUALIFIED for that reason.
-/

noncomputable section

open Salt.Entropy.Chowla
open scoped BigOperators

namespace Salt.MR

/-- **⟦`S_H(0)` IS THE MERTENS SUM⟧** (`crownNV_expSum_zero`) — at frequency `0` every character
value is `1`, so the exponential sum over the Chowla prime window is the real sum `∑ 1/p`, cast
to `ℂ`. -/
theorem crownNV_expSum_zero (eps : ℚ) (H : ℕ) :
    expSum eps H 0 = ((∑ p ∈ Salt.Entropy.Chowla.primeWindow eps H, (1 / (p : ℝ)) : ℝ) : ℂ) := by
  have hsum : (∑ p ∈ Salt.Entropy.Chowla.primeWindow eps H, (1 / (p : ℝ)))
      = ∑ p : Salt.Entropy.Chowla.primeWindow eps H, (1 / ((p : ℕ) : ℝ)) :=
    (Finset.sum_coe_sort (Salt.Entropy.Chowla.primeWindow eps H) (fun p => (1 / (p : ℝ)))).symm
  rw [hsum]
  unfold expSum
  push_cast
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp

/-- **⟦NV-a, THE LEAF⟧** (`crownNV_zero_mem_bigXi`) — above a floor `H₀`, in the Mertens leaf's
own regime (`√H ≤ ε²·H/2` and `ε² ≤ 1/4`), the frequency `0` is in the large-spectrum set `Ξ_H`.
The floor is `primeWindow_sum_inv_ge_bounded`'s, raised to `2` so that `log H > 0`. -/
theorem crownNV_zero_mem_bigXi :
    ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ) [NeZero H], H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 → (eps : ℝ) ^ 2 ≤ 1 / 4 →
      (0 : ZMod H) ∈ bigXi eps H := by
  obtain ⟨c, _hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded
  refine ⟨max H₀ 2, ?_⟩
  intro eps H _ hH hreg heps
  have hH₀ : H₀ ≤ H := le_trans (le_max_left _ _) hH
  have hH2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hH
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hleaf := hD3 eps H hH₀ hreg (by linarith)
  rw [mem_bigXi_iff]
  simp only [ZMod.val_zero, Nat.cast_zero, neg_zero, zero_div]
  have hnn : (0 : ℝ) ≤ ∑ p ∈ Salt.Entropy.Chowla.primeWindow eps H, (1 / (p : ℝ)) :=
    Finset.sum_nonneg (fun p _ => by positivity)
  rw [crownNV_expSum_zero, Complex.norm_real, Real.norm_of_nonneg hnn]
  refine le_trans ?_ hleaf
  exact div_le_div_of_nonneg_right (by linarith) hlog.le

/-- **⟦THE FLOOR LEMMA⟧** (`crownNV_above_flat_floor`) — once the design constant `A` clears the
leaf's `H₀` and `(2/ε²)²`, every `H` at or above `flatDesignBase A` has `0 ∈ Ξ_H`.  The two
inputs are `A ≤ exp (exp (3.2·A)) ≤ flatDesignBase A ≤ H` (so `H₀ ≤ H`) and `2/ε² ≤ √H` (so the
leaf's regime hypothesis `√H ≤ ε²·H/2` holds). -/
theorem crownNV_above_flat_floor :
    ∃ H₀ : ℕ, ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ A : ℝ, 162 ≤ A → (H₀ : ℝ) ≤ A →
      (2 / (ε : ℝ) ^ 2) ^ 2 ≤ A →
      ∀ (H : ℕ) [NeZero H], flatDesignBase A ≤ H → (0 : ZMod H) ∈ bigXi ε H := by
  obtain ⟨H₀, hNV⟩ := crownNV_zero_mem_bigXi
  refine ⟨H₀, ?_⟩
  intro ε hε0 hε A hA162 hH₀A hTA H _ hH
  have hε0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεR : (ε : ℝ) ≤ 1 / 500 := by
    have h : ((ε : ℚ) : ℝ) ≤ ((1 / 500 : ℚ) : ℝ) := Rat.cast_le.mpr hε
    simpa using h
  have hsq : (ε : ℝ) ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := pow_le_pow_left₀ hε0R.le hεR 2
  have heps4 : (ε : ℝ) ^ 2 ≤ 1 / 4 := le_trans hsq (by norm_num)
  have hε2pos : (0 : ℝ) < (ε : ℝ) ^ 2 := by positivity
  -- `A ≤ flatDesignBase A ≤ H`
  have h1 := Real.add_one_le_exp (3.2 * A)
  have h2 := Real.add_one_le_exp (Real.exp (3.2 * A))
  have h3 : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    unfold flatDesignBase
    exact Nat.le_ceil _
  have hHR : ((flatDesignBase A : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hAH : A ≤ (H : ℝ) := by linarith
  have hH₀H : H₀ ≤ H := by
    have : (H₀ : ℝ) ≤ (H : ℝ) := le_trans hH₀A hAH
    exact_mod_cast this
  -- the leaf's regime hypothesis `√H ≤ ε²·H/2`
  have hT : (0 : ℝ) < 2 / (ε : ℝ) ^ 2 := by positivity
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hTs : 2 / (ε : ℝ) ^ 2 ≤ Real.sqrt (H : ℝ) :=
    (Real.le_sqrt' hT).mpr (le_trans hTA hAH)
  have hreg : Real.sqrt (H : ℝ) ≤ (ε : ℝ) ^ 2 * (H : ℝ) / 2 := by
    have hHss : (H : ℝ) = Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) :=
      (Real.mul_self_sqrt hH0).symm
    have hs0 : 0 ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
    have h2le : 2 ≤ (ε : ℝ) ^ 2 * Real.sqrt (H : ℝ) := by
      have := mul_le_mul_of_nonneg_left hTs hε2pos.le
      rwa [mul_div_cancel₀ _ hε2pos.ne'] at this
    have key : Real.sqrt (H : ℝ) * 2 ≤ Real.sqrt (H : ℝ) * ((ε : ℝ) ^ 2 * Real.sqrt (H : ℝ)) :=
      mul_le_mul_of_nonneg_left h2le hs0
    have hre : (ε : ℝ) ^ 2 * (H : ℝ) / 2
        = Real.sqrt (H : ℝ) * ((ε : ℝ) ^ 2 * Real.sqrt (H : ℝ)) / 2 := by
      conv_lhs => rw [hHss]
      ring
    rw [hre]
    linarith
  exact hNV ε H hH₀H hreg heps4

/-- **⟦LANDED W, NON-VACUOUS — UNCONDITIONAL⟧** (`crownNV_landedW_nonvacuous`) —
`FlatDoorEpsFamilyW`'s body VERBATIM plus ONE conjunct: the regime can be taken with `0 ∈ Ξ_H` at
EVERY `H` at or above its `Hlo`, so at every `H` the door quantifies over.  The two floors of
`crownNV_above_flat_floor` are paid out of the landed door's own `∀ A₀`, by asking it for
`max A₀ (max H₀ ((2/ε²)²))`.  NON-VACUOUS means `0 ∈ Ξ_H` and NO MORE: the door's sum is
non-empty.  That its `ξ = 0` term is `≥ 1/H²` at odd `H` is `FlatDoorParityFloor`, not this. -/
theorem crownNV_landedW_nonvacuous :
    ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ A₀ : ℝ,
      ∃ (δ₀ A : ℝ), 0 < δ₀ ∧
        (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) ≤ δ₀ ∧ δ₀ ≤ 500 * (ε : ℝ) / 837782 ∧
        162 ≤ A ∧ A₀ ≤ A ∧
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          MRTUniformityXiL2 R δ₀ ∧
          (∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
            ¬ logChowla2Fails R.eps R.x R.ω) ∧
          ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H := by
  obtain ⟨H₀, hfloor⟩ := crownNV_above_flat_floor
  intro ε hε0 hε A₀
  obtain ⟨δ₀, A, hδ₀, hlo, hhi, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor, hslot⟩ :=
    flatDoorEpsFamilyW_holds ε hε0 hε (max A₀ (max (H₀ : ℝ) ((2 / (ε : ℝ) ^ 2) ^ 2)))
  refine ⟨δ₀, A, hδ₀, hlo, hhi, hA162, le_trans (le_max_left _ _) hA₀A, R, hReps, hHlo, hdes,
    hdoor, hslot, ?_⟩
  intro H _ hH
  rw [hReps]
  refine hfloor ε hε0 hε A hA162 ?_ ?_ H (hHlo ▸ hH)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA₀A
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA₀A

end Salt.MR
