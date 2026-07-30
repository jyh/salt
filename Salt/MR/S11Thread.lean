/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4SecondRoad

/-!
# ⟦S0-THREAD⟧ — the tower conjunct, re-threaded to the road

`M4Exit.m4_exit_socket_split` delivers, alongside the regime's own data, the head's tower
endpoint law

  `50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^5`

(⟦THE NAMED AMENDMENT⟧, the 2026-07-29 anchor ruling).  `M4Close`'s exit discards it (`-` in
its `obtain`, "not consumed at this stage") and so does the second road; but the S11 compose
reads BOTH `λ₋ = loglog R.Hlo` and `λ₊ = loglog R.Hhi` — the door arm prices at `λ₊`, the
drift arm at `λ₋` — and the tower is the ONLY bridge between them.  Without it the spine has
no `λ₊` control at all.

This file re-threads the conjunct through the two forwarding stages, as ADDITIVE twins:

* `m4_door_contradiction_of_live_split_tower` — `M4Close.m4_door_contradiction_of_live_split`
  with the `-` named and the conjunct passed into the `∃ R` payload;
* `m4_second_road_tower` — `M4SecondRoad.m4_second_road` with the same conjunct in its own
  `∃ R` payload.

Both proofs are the landed proofs with one extra component carried; every other byte of the
register — the gate list, the conclusion `¬ logChowla2Fails R.eps R.x R.ω` — is verbatim.
No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **THE WAVE'S EXIT, SPLIT, WITH THE TOWER** (`m4_door_contradiction_of_live_split_tower`) —
`M4Close.m4_door_contradiction_of_live_split` with `M4Exit.m4_exit_socket_split`'s tower
conjunct FORWARDED instead of dropped.  Statement diff against the landed twin: one extra
conjunct in the `∃ R` payload, `50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^5`.  The
register (`M4DoorGates`, `0 ≤ Braw`, `M4GradeGateSplit`, `M4SievedDoorSq`) and the conclusion
are byte-identical. -/
theorem m4_door_contradiction_of_live_split_tower :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  -- ⟦THE NAMED AMENDMENT⟧, named here instead of discarded
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, hRtow, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, WITH THE TOWER⟧** (`m4_second_road_tower`).
`M4SecondRoad.m4_second_road` with the tower endpoint law carried in the `∃ R` payload.  The
ten-item gate census, the analytic slot ⟦item 11⟧ and the conclusion are byte-identical to the
landed road; the proof is the landed proof with the extra component passed through. -/
theorem m4_second_road_tower :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
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
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_tower
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
  intro δ RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate
    hdrift hgrade hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2 hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
  refine m4_sievedDoorSq_of_blk2 (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]

end Salt.MR

end
