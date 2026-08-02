/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowSpineLinear

/-!
# ⟦LADDER-L G3 §1⟧ — `M4ArithRho` at the LINEAR anchor (`M4ArithRhoLinear`)

⟦COMPOSE-FLAT-2⟧ kernelized `flat_landed_ladder_break`: the road and the fuse read the door a
SECOND time, through the LADDER `calP (Adoor M) (s13GK K M)`.  This page carries the `_L` twin
family of `M4ArithRho`'s ⟦A4ρ⟧ exit at `AdoorL M = 2^36·M`, with the `G`-slot unchanged
(`3072·M`, resp. `s13GK K M`).

PURELY ADDITIVE: no landed declaration moves.  Every twin is a RESTATEMENT of the landed
theorem with the landed body replayed at the linear door's own suppliers
(`M4RowLinear`/`M4RowAssemblyLinear`/`M4RowSpineLinear`/`ArithPageLinear`).

⟦WHAT DOES NOT MOVE⟧ the entire `ρ` scale.  `RSanDoorRho`, `DoorArithFrameRho`'s five derived
lemmas, `gArmDoorRho`, `doorRhoOfDelta` and the ceiling `m4_arith_rs_ceiling_met_rho` are
door-FREE and are consumed verbatim; `DoorArithFrameRho_L` (`ArithPageLinear`) is the frame
the linear socket supplies, and it is the landed frame with the `jfloor`/`anchor` fields paid
off the LINEAR row floor's own `M` factor.

⟦THE SOCKET BASE⟧ the linear twins quantify over `ArithPageLinear.SocketBaseL` — the landed
`SocketBase` with the window-index floor at `doorRowFloorL M = 2^36·M²`.  That is a STRONGER
antecedent, so every landed consumer still applies (`socketBase_of_socketBaseL`).
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦GATE 4⟧ at the `ρ`-envelope, at the linear floor -/

/-- **⟦GATE 4, READ AT THE `ρ`-ENVELOPE, AT THE LINEAR DOOR⟧** (`m4_arith_gate4_rho_L`) —
`M4ArithRho.m4_arith_gate4_rho` at `j₀ := doorRowFloorL M`. -/
theorem m4_arith_gate4_rho_L (M : ℕ) (ρ : ℝ) :
    ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
  m4ChiRowGraded_an_L (fun _ _ _ => le_rfl)

/-! ## §2 — ⟦ITEM 11⟧ AT THE `ρ`-ENVELOPE, AT THE LINEAR DOOR -/

/-- **⟦A4ρ — THE ASSEMBLY, ARITHMETIC INCLUDED, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorArithRho_L`).  `M4ArithRho.m4_chiSummedFreeRow_of_doorArithRho`
(:617) at `AdoorL`: ⟦item 11⟧ of `m4_second_road_L` at the spliced grade
`m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)`.

THE COMPLETE HYPOTHESIS LIST — `hM`, `hframe`, `hrows`, `hband` are the linear assembly's own
four, and `harith` is the linear `ρ`-frame at every base the LINEAR socket reaches. -/
theorem m4_chiSummedFreeRow_of_doorArithRho_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K ρ : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_rho_L harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §3 — THE ARITHMETIC EXIT, AT THE LINEAR DOOR -/

/-- **⟦A4ρ — THE ARITHMETIC EXIT, AT THE LINEAR DOOR⟧** (`m4_arith_door_exit_rho_L`).
`M4ArithRho.m4_arith_door_exit_rho` (:793) at `AdoorL`.  ⟦ii⟧ moves to the LINEAR floor
`doorRowFloorL M`; ⟦iii⟧ is door-FREE and is the landed statement verbatim. -/
theorem m4_arith_door_exit_rho_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K ρ δ₀ : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H))
      ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
          m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
            ≤ δ₀ ^ 2) := by
  refine ⟨m4_chiSummedFreeRow_of_doorArithRho_L hM hframe hrows hband harith,
    m4_arith_gate4_rho_L M ρ, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met_rho hρ hρδ hL0 hlam

/-- **⟦A4ρ — THE ARITHMETIC EXIT AT THE CONSUMER'S `ρ`, AT THE LINEAR DOOR⟧**
(`m4_arith_door_exit_of_delta_L`).  `M4ArithRho.m4_arith_door_exit_of_delta` (:831) at
`AdoorL`: `ρ := doorRhoOfDelta δ₀`, ceiling hypothesis discharged by construction. -/
theorem m4_arith_door_exit_of_delta_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K δ₀ : ℝ}
    (hM : 1 ≤ M) (hδ₀ : 0 < δ₀)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
        (doorRhoOfDelta δ₀)) :
    M4ChiSummedFreeRow_L R M
        (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
      ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
          m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
            ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
              * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
            ≤ δ₀ ^ 2) :=
  m4_arith_door_exit_rho_L hM (doorRhoOfDelta_pos hδ₀.ne') (doorRhoOfDelta_spec δ₀) hHreg
    hframe hrows hband harith

/-! ## §GK — the `G`-lever twins

The linear `ρ`-page at `G := s13GK K M`.  ⟦THE BINDER SHADOW⟧ is the landed page's: the
statements already bind a REAL `K` (⟦C3⟧'s symbolic margined-floor constant), which is
alpha-renamed to `Kar` in the twins so the lever's `(K : ℕ)` can go first. -/

/-- `m4_arith_henv_rho_L` (`ArithPageLinear`), at the lever.  `a2DoorGrade_L_gk` is
`a2DoorGrade_L` under a levered name (its only ladder read is the K-invariant level 1). -/
theorem m4_arith_henv_rho_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  m4_arith_henv_rho_L harith

/-- `m4_chiSummedFreeRow_of_doorArithRho_L` (:60), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorArithRho_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {Kar ρ : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big_L_gk K
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk K hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_rho_L_gk K harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- `m4_arith_door_exit_rho_L` (:105), at the lever.  ⟦ii⟧ and ⟦iii⟧ are `G`-FREE. -/
theorem m4_arith_door_exit_rho_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {Kar ρ δ₀ : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H))
      ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
          m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
            ≤ δ₀ ^ 2) := by
  refine ⟨m4_chiSummedFreeRow_of_doorArithRho_L_gk K hM hframe hrows hband harith,
    m4_arith_gate4_rho_L M ρ, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met_rho hρ hρδ hL0 hlam

/-- `m4_arith_door_exit_of_delta_L` (:148), at the lever. -/
theorem m4_arith_door_exit_of_delta_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {Kar δ₀ : ℝ}
    (hM : 1 ≤ M) (hδ₀ : 0 < δ₀)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
        (doorRhoOfDelta δ₀)) :
    M4ChiSummedFreeRow_L_gk K R M
        (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
      ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
          m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
            ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
              * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
            ≤ δ₀ ^ 2) :=
  m4_arith_door_exit_rho_L_gk K hM (doorRhoOfDelta_pos hδ₀.ne') (doorRhoOfDelta_spec δ₀) hHreg
    hframe hrows hband harith

end Salt.MR

end
