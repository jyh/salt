/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HloExportMR
import Salt.Entropy.Chowla.TowerFlatExport

/-!
# THE FLAT SHAPE on the road — the carrier twins of `HloExportMR` (freeze F-5)

FLAT-REF's F-5 rules that the flat tower's width export is stated A-FREE, and
that the MR cone then changes exactly ONE SHAPE in the conjunct it carries:

```
(50 ≤ loglog H₋ → loglog H₊ ≤ loglog H₋ ^ (9/2))          -- landed
(50 ≤ loglog H₋ → loglog H₊ ≤ exp (loglog H₋ / 2))        -- flat
```

This file carries the FLAT shape across the ten road statements of
`Salt.MR.HloExportMR` as ADDITIVE TWINS.  Every twin's statement is its landed
original with that one conjunct re-shaped; nothing else moves — same `∃`-prefix,
same pins, same payload, same census, same suppliers.

⟦WHY THE PROOFS ARE ONE LINE⟧ `Salt.Entropy.Chowla.pow_nine_halves_le_exp_half`
says `λ^{9/2} ≤ e^{λ/2}` on the conjunct's own guard `50 ≤ λ`.  A CARRIER holds
the conjunct in the PAYLOAD of an `∃`, so the flat carrier is strictly WEAKER
than the landed one and follows by one monotone rewrite.  (The dual asymmetry is
what pays for the consumers: a CONSUMER holds it as a HYPOTHESIS, so the flat
consumer twin is strictly STRONGER and must be re-derived against the flat
λ-engine `flat_lambda_core`.)

⟦THE INTERIM ROOT, NAMED⟧ Today these twins are rooted, through their landed
originals, in the landed `9/2` producer (`TowerExport.tower_loglog_le_45`).  That
is deliberate and is the ONLY thing that moves when the flat regime builder
lands: the flat producer supplies exactly `loglog H₊ ≤ e^{loglog H₋/2}` (freeze
F-5, `Salt.Entropy.Chowla.towerFlat_width_export`), each `obtain` below re-points
at it, and the bridge step is deleted.  No statement in this file changes then —
that is the whole purpose of twinning at the flat shape now.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the road-form socket, cap-carrying, at the flat shape -/

/-- `m4_exit_socket_split_sq_arc_hloCap` (`HloExportMR.lean:68`) at the FLAT tower
conjunct. -/
theorem m4_exit_socket_split_sq_arc_hloCap_flat :
    ∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
            (∀ m, lamCoeff m = a m + e m) →
            (∀ H : ℕ, 0 ≤ Bsieve H) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ Bsieve H * (H : ℝ) ^ 2) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω)) ≤ Binsert) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hmain⟩ := m4_exit_socket_split_sq_arc_hloCap
  refine ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-! ## §2 — the closed loop, cap-carrying, at the flat shape -/

/-- `m4_doorL2_close_split_sq_hloCap` (`HloExportMR.lean:112`) at the FLAT tower
conjunct. -/
theorem m4_doorL2_close_split_sq_hloCap_flat :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hmain⟩ := m4_doorL2_close_split_sq_hloCap
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-! ## §3 — the second road's terminal register, at the flat shape -/

/-- `m4_second_road_L2_hloCap` (`HloExportMR.lean:188`) at the FLAT tower
conjunct.  The ELEVEN-ITEM CENSUS and the four named suppliers are the landed
ones, item for item. -/
theorem m4_second_road_L2_hloCap_flat :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, hmain⟩ := m4_second_road_L2_hloCap
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-! ## §4 — the road, pinned, at the flat shape -/

/-- `m4_exit_socket_split_sq_arc_hloCap_pinned` (`HloExportMR.lean:277`) at the
FLAT tower conjunct. -/
theorem m4_exit_socket_split_sq_arc_hloCap_pinned_flat :
    ∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
            (∀ m, lamCoeff m = a m + e m) →
            (∀ H : ℕ, 0 ≤ Bsieve H) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ Bsieve H * (H : ℝ) ^ 2) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                  ∂(logMeasure R.x R.ω)) ≤ Binsert) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_exit_socket_split_sq_arc_hloCap_pinned
  refine ⟨ε, K, δ₀, Hcap, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-- `m4_doorL2_close_split_sq_hloCap_pinned` (`HloExportMR.lean:320`) at the FLAT
tower conjunct. -/
theorem m4_doorL2_close_split_sq_hloCap_pinned_flat :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_pinned
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-- `m4_second_road_L2_hloCap_pinned` (`HloExportMR.lean:394`) at the FLAT tower
conjunct.  THE DELIVERABLE of this file: the surface the capstone compose reads
when it needs the constants AS NUMBERS, now carrying the flat width shape. -/
theorem m4_second_road_L2_hloCap_pinned_flat :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_second_road_L2_hloCap_pinned
  refine ⟨Cg, ε, K, δ₀, Hcap, hCg, hCgle, hε, hK, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-! ## §GK — the G-lever twins, at the flat shape -/

/-- `m4_doorL2_close_split_sq_hloCap_gk` (`HloExportMR.lean:500`) at the FLAT
tower conjunct. -/
theorem m4_doorL2_close_split_sq_hloCap_gk_flat (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-- `m4_second_road_L2_hloCap_gk` (`HloExportMR.lean:556`) at the FLAT tower
conjunct. -/
theorem m4_second_road_L2_hloCap_gk_flat (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, hmain⟩ := m4_second_road_L2_hloCap_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hε, hKb, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-- `m4_doorL2_close_split_sq_hloCap_pinned_gk` (`HloExportMR.lean:640`) at the
FLAT tower conjunct. -/
theorem m4_doorL2_close_split_sq_hloCap_pinned_gk_flat (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_doorL2_close_split_sq_hloCap_pinned_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

/-- `m4_second_road_L2_hloCap_pinned_gk` (`HloExportMR.lean:698`) at the FLAT
tower conjunct — the lever's copy of this file's deliverable. -/
theorem m4_second_road_L2_hloCap_pinned_gk_flat (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ : ℝ) (Hcap : ℕ),
      1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧ 0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hmain⟩ :=
    m4_second_road_L2_hloCap_pinned_gk K
  refine ⟨Cg, ε, Kb, δ₀, Hcap, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

end Salt.MR
