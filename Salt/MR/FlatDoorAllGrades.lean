/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorNonVacuity
import Mathlib

/-!
# ⟦TIER S — ROAD F, THE GRADE AXIS: THE FLAT DOOR AT EVERY GRADE (W-δ)⟧ (`FlatDoorAllGrades`)

Rung 2 (`FlatDoorEpsRung2`) proved the `L²` MRT door on the flat family at every
`ε ∈ (0, 1/500]`, at ONE grade per `ε` — the head's own threshold `δ₀`.  This file states and
proves the same door at EVERY grade `ρ > 0`:

* `FlatDoorAllGradesW` — the statement of record (W-δ);
* `flatDoorAllGradesW_holds : FlatDoorAllGradesW` — its proof.

THE ROUTE is one formal step on landed names.  Rung 2's `L`-charge design put the threshold
INSIDE the head form: `FlatHeadFormEpsW ε c Q` reads its threshold at exactly three conjuncts
(`0 < δ₀`, the pin `1/(838400·c) ≤ δ₀`, and the final arrow).  So a head at charge `c` is a head
at the same charge whose threshold is ANY `ρt` on the pin (`flatHeadFormEpsW_at_grade`), and a
charge `c` that pins both `ε` and the target grade `ρ` always exists (`crownWd_exists_charge`).
The landed head `flat_head_uniform_xceil_epsW` at that charge, the shrink, and the landed chain
`flat_chain_generic_epsW` give W-δ.  No landed statement moves and no landed file is edited.

TWO CONTROLS, each stated FROM `FlatDoorAllGradesW` so that it reads the statement and not the
proof: `crownWd_zero_level_landed` (at `ε := 1/500`, `ρ := 1/837782` W-δ is the landed door's
statement) and `crownWd_L1_on_flat` (the `L¹` door at every grade `δ`, through `ρ := δ²`).

NON-VACUITY lands as SEPARATE theorems and is NOT a conjunct of the statement:
`crownNV_Wdelta_nonvacuous` runs `FlatDoorNonVacuity`'s floor argument on W-δ, and
`crownNV_Wdelta_nonvacuous_holds` supplies the proof.

⚠ WHAT THIS DOES NOT SAY.  The quantifier shape is `∀ A₀ ∃ R` on the FLAT family — a regime
above every floor — and NOT the crown's `∃ H₀ ∀ R`; the crown still has no producer.  No rate is
exported: the charge `c` grows like `1/ρ` and the design constant pays `2·log c`.  Nothing here
bears on twin primes.
-/

noncomputable section

open Salt.Entropy.Chowla

namespace Salt.MR

/-- **⟦W-δ — THE FLAT DOOR AT EVERY GRADE⟧** (`FlatDoorAllGradesW`) — the `L²` door on the flat
family at EVERY grade `ρ > 0` and every `ε ∈ (0, 1/500]`, above every floor `A₀` on the design
constant.  Inhabited by `flatDoorAllGradesW_holds`. -/
def FlatDoorAllGradesW : Prop :=
  ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        MRTUniformityXiL2 R ρ

/-- **⟦THE CHARGE EXISTS⟧** (`crownWd_exists_charge`) — one `c ≥ 1` that pins both `ε`
(`1/(500·c) ≤ ε`) and the target grade `ρ` (`1/(838400·c) ≤ ρ`): the larger of the two
ceilings. -/
theorem crownWd_exists_charge (ε : ℚ) (hε0 : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ c : ℕ, 1 ≤ c ∧ (1 : ℚ) / (500 * (c : ℚ)) ≤ ε ∧ (1 : ℝ) / (838400 * (c : ℝ)) ≤ ρ := by
  have hεQ0 : (0 : ℚ) < 500 * ε := by linarith
  have hρ0 : (0 : ℝ) < 838400 * ρ := by linarith
  have hn1pos : 0 < ⌈(1 / (500 * ε) : ℚ)⌉₊ := Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
  refine ⟨max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * ρ) : ℝ)⌉₊, ?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
  · have hle : (1 : ℚ) / (500 * ε)
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * ρ) : ℝ)⌉₊ : ℕ) : ℚ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_left _ _)
    have hc1 : (1 : ℚ) ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * ρ) : ℝ)⌉₊ : ℕ) : ℚ) := by
      exact_mod_cast le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
    rw [div_le_iff₀ hεQ0] at hle
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have hle : (1 : ℝ) / (838400 * ρ)
        ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * ρ) : ℝ)⌉₊ : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
    have hc1 : (1 : ℝ) ≤ ((max ⌈(1 / (500 * ε) : ℚ)⌉₊ ⌈(1 / (838400 * ρ) : ℝ)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Nat.succ_le_of_lt hn1pos) (le_max_left _ _)
    rw [div_le_iff₀ hρ0] at hle
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- **⟦THE THRESHOLD SHRINK, ON THE FORM⟧** (`flatHeadFormEpsW_at_grade`) — the head form reads
its threshold `δ₀` at exactly three conjuncts (`0 < δ₀`, the pin, the final arrow), so any head
at the charge `c` is a head at the same charge whose threshold is ANY `ρt` on the pin, with the
door at `ρt` as its payload.  The old payload `Q` is dropped; the new final arrow is
`mrtUniformityXiL2_mono`. -/
theorem flatHeadFormEpsW_at_grade {ε : ℚ} {c : ℕ} {Q : ChowlaRegime → Prop}
    (h : FlatHeadFormEpsW ε c Q) {ρt : ℝ} (hρt : 0 < ρt)
    (hpin : (1 : ℝ) / (838400 * (c : ℝ)) ≤ ρt) :
    FlatHeadFormEpsW ε c (fun R => MRTUniformityXiL2 R ρt) := by
  unfold FlatHeadFormEpsW at h ⊢
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, -, hc1, hcε, -, hβ, hbody⟩ := h
  refine ⟨K, ρt, β, Hopq, hε, hK, hKb, hρt, hc1, hcε, hpin, hβ, ?_⟩
  intro A hA hbud hcA
  obtain ⟨Hcap, hHcap, hR⟩ := hbody A hA hbud hcA
  refine ⟨Hcap, hHcap, ?_⟩
  intro extraFloor U1floor g hg
  obtain ⟨R, hReps, hef, hU1, hRg, hRx, hcount, htow, hcap, -⟩ := hR extraFloor U1floor g hg
  exact ⟨R, hReps, hef, hU1, hRg, hRx, hcount, htow, hcap,
    fun ρ _ hle hd => mrtUniformityXiL2_mono hle hd⟩

/-- **⟦W-δ IS PROVED⟧** (`flatDoorAllGradesW_holds`) — from the landed rung-2 head at the charge
of `crownWd_exists_charge`, the shrink `flatHeadFormEpsW_at_grade`, and the landed rung-2 chain
`flat_chain_generic_epsW`. -/
theorem flatDoorAllGradesW_holds : FlatDoorAllGradesW := by
  intro ε hε0 hε ρ hρ A₀
  obtain ⟨c, hc1, hcε, hpin⟩ := crownWd_exists_charge ε hε0 ρ hρ
  have hhead : FlatHeadFormEpsW ε c (fun _ => True) :=
    flat_head_uniform_xceil_epsW ε hε0 hε hc1 hcε (fun _ => True) (fun _ _ _ _ => trivial)
  have hV := flat_chain_generic_epsW ε c (fun R => MRTUniformityXiL2 R ρ)
    (flatHeadFormEpsW_at_grade hhead hρ hpin) A₀
  obtain ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hA162, hA₀A, R, hReps, hHlo, -, hdes, -, hdoor⟩ := hV
  exact ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor⟩

/-- **⟦ZERO LEVEL 1⟧** (`crownWd_zero_level_landed`) — W-δ at `ε := 1/500`, `ρ := 1/837782` is
the landed flat door's statement.  Stated from `FlatDoorAllGradesW`, so it reads the STATEMENT
and not its proof. -/
theorem crownWd_zero_level_landed (hWd : FlatDoorAllGradesW) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / 500 ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 837782 ∧ MRTUniformityXiL2 R ρ := by
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor⟩ :=
    hWd (1 / 500) (by norm_num) le_rfl (1 / 837782) (by norm_num) A₀
  exact ⟨1 / 500, A, by norm_num, le_rfl, hA162, hA₀A, R, hReps, hHlo, hdes, 1 / 837782,
    by norm_num, le_rfl, hdoor⟩

/-- **⟦THE `L¹` DOOR AT EVERY GRADE, ON THE FLAT FAMILY⟧** (`crownWd_L1_on_flat`) — from W-δ at
`ρ := δ²` through `mrtUniformityXi_of_xiL2`: the crown's conclusion with `∃ H₀ ∀ R` replaced by
`∀ A₀ ∃ R (flat)`.  It is NOT the crown. -/
theorem crownWd_L1_on_flat (hWd : FlatDoorAllGradesW) (δ : ℝ) (hδ : 0 < δ) (ε : ℚ)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 500) (A₀ : ℝ) :
    ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧ MRTUniformityXi R δ := by
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor⟩ :=
    hWd ε hε0 hε (δ ^ 2) (by positivity) A₀
  refine ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, ?_⟩
  have h := mrtUniformityXi_of_xiL2 R (by positivity : (0 : ℝ) ≤ δ ^ 2) hdoor
  rwa [Real.sqrt_sq hδ.le] at h

/-- **⟦W-δ, NON-VACUOUS — FROM W-δ⟧** (`crownNV_Wdelta_nonvacuous`) — W-δ's body VERBATIM plus
ONE conjunct: the regime can be taken with `0 ∈ Ξ_H` at EVERY `H` at or above its `Hlo`.  The
floor argument of `crownNV_landedW_nonvacuous`, run on the statement W-δ. -/
theorem crownNV_Wdelta_nonvacuous (hWd : FlatDoorAllGradesW) :
    ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
      ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          MRTUniformityXiL2 R ρ ∧
          ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H := by
  obtain ⟨H₀, hfloor⟩ := crownNV_above_flat_floor
  intro ε hε0 hε ρ hρ A₀
  obtain ⟨A, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor⟩ :=
    hWd ε hε0 hε ρ hρ (max A₀ (max (H₀ : ℝ) ((2 / (ε : ℝ) ^ 2) ^ 2)))
  refine ⟨A, hA162, le_trans (le_max_left _ _) hA₀A, R, hReps, hHlo, hdes, hdoor, ?_⟩
  intro H _ hH
  rw [hReps]
  refine hfloor ε hε0 hε A hA162 ?_ ?_ H (hHlo ▸ hH)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA₀A
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA₀A

/-- **⟦W-δ, NON-VACUOUS — UNCONDITIONAL⟧** (`crownNV_Wdelta_nonvacuous_holds`) —
`crownNV_Wdelta_nonvacuous` with `flatDoorAllGradesW_holds` supplied, so no reader carries the
`hWd` binder as an open hypothesis. -/
theorem crownNV_Wdelta_nonvacuous_holds :
    ∀ (ε : ℚ), 0 < ε → ε ≤ 1 / 500 → ∀ ρ : ℝ, 0 < ρ → ∀ A₀ : ℝ,
      ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          MRTUniformityXiL2 R ρ ∧
          ∀ (H : ℕ) [NeZero H], R.Hlo ≤ H → (0 : ZMod H) ∈ bigXi R.eps H :=
  crownNV_Wdelta_nonvacuous flatDoorAllGradesW_holds

end Salt.MR
