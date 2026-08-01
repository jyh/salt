/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12ConstCompose
import Salt.Entropy.Chowla.TowerFlatExport

/-!
# THE FLAT SHAPE at the CAPSTONE — the §GK / §GK-PINNED twins (freeze F-5)

The two most downstream carriers of the tower conjunct on the second road:
`logChowla2_capstone_final_const'_graded_gk` (`S12ConstCompose.lean:1217`) and its
pinned twin (`:1460`), restated with

```
(50 ≤ loglog H₋ → loglog H₊ ≤ exp (loglog H₋ / 2))
```

in place of the `9/2` conjunct.  Nothing else moves: same `∃`-prefix (13 binders
and 11 — resp. 14 — pins), same `Mfl` wire, same census, same suppliers, same
residue.  The conjunct is carried OPAQUELY by both landed proofs (they destructure
it at `hRtow` and re-emit it untouched), so each twin is its landed original plus
one application of `Salt.Entropy.Chowla.pow_nine_halves_le_exp_half`.

⟦THE SWAP⟧ as in `Salt.MR.HloExportMRFlat`: today the root is the landed `9/2`
producer; when the flat regime builder lands, `Salt.Entropy.Chowla.
chowlaRegimeFlat_tower_conjunct` becomes the root, the `obtain` re-points, and the
bridge step is deleted.  NO STATEMENT IN THIS FILE MOVES.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

set_option maxHeartbeats 1000000 in
-- Same cause as the landed originals: the statement re-elaborates the full residue.
/-- `logChowla2_capstone_final_const'_graded_gk` (`S12ConstCompose.lean:1217`) at the
FLAT tower conjunct. -/
theorem logChowla2_capstone_final_const'_graded_gk_flat (K : ℕ) (hK : K ≤ 170000000)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates_gk K Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate'''_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (s13GK K M))
                                  (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl,
      hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk K hK Aexp hAexp
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl,
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain Cp hCp U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

set_option maxHeartbeats 1000000 in
-- Same cause as the landed original: the statement re-elaborates the full residue.
/-- `logChowla2_capstone_final_const'_graded_gk_pinned` (`S12ConstCompose.lean:1460`)
at the FLAT tower conjunct — the road's terminal carrier, flat. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_flat (K : ℕ) (hK : K ≤ 170000000)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
        ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
          ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap U1floor ∧
            ∀ (M : ℕ), Mfl ≤ M →
              ∃ C' : ℝ, 0 < C' ∧
                8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
                    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                  -- ⟦A⟧ THE SPINE ARITHMETIC
                  M4DoorGates_gk K Cg R M k δ₀ →
                  8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloor M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    GRowsZeroGate'''_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    calQK (Adoor M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                        ≤ 8 * (0 : ℝ) ^ 2
                          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                \ seamBall (((A + s : ℕ)) : ℝ) 0)
                              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                  (calP (Adoor M) (s13GK K M))
                                  (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                                  (mrAlpha (1 / 12)) 2,
                              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                              * (Real.log (((A + s : ℕ)) : ℝ))
                                  ^ (-theta293 + epsrf (A + s)))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl,
      hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned K hK Aexp hAexp
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl,
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain Cp hCp U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

end Salt.MR

end
