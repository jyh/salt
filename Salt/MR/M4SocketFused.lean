/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithZero
import Salt.MR.M4ArithRho

/-!
# ⟦THE FUSED TERMINAL — BOTH REPAIRS AT ONCE⟧ (`M4SocketFused`)

Design provenance: **REF-SOCKET-2's ⟦AMENDMENT 1 — THE UNJOINED REPAIRS⟧** (flags,
2026-07-30).  The refuter's mandate-1 sweep confirmed the repaired socket but caught that the
three repairs had landed SIDE BY SIDE and were never composed:

* `M4ArithZero.m4_socket_discharged_bandfree_zero` carries the density repair (`Cp` free over
  the nonnegatives, `hbase : DoorRowZeroBase`) and the ⟦ALPHA-SURGERY⟧ base cap
  (`SocketBase`'s `A ≤ 2·R.x` field) — but still asks the **dead** `2/10⁴⁹ ≤ δ₀`;
* `M4ArithRho.m4_arith_door_exit_of_delta` closes that blocker (`0 < δ₀` alone, `ρ` set to
  `doorRhoOfDelta δ₀`) — but takes the `hrows` binder the ⟦SECOND HORN⟧ refuted.

This file is the JOIN.  It is a single theorem, `m4_socket_discharged_fused`, and it is
PURELY ADDITIVE: no landed declaration is touched, nothing is weakened, and the proof is the
refuter's own `ref2_fused_terminal` (scratch probe 1, first-attempt) ported verbatim — the ρ
exit fed by the density-free `hrows` SUPPLIER `M4RowsChiZero.m4_hrowsSlot_at_door_zero` and
the band SUPPLIER `M4SocketDischarge.m4_hband_at_door_slot`.

## ⟦WHAT THE STATEMENT COSTS THE ROAD⟧

The δ₀ side is `0 < δ₀` and nothing else.  The grade is `RSanDoorRho (doorRhoOfDelta δ₀)` and
the ceiling is met from `hδ₀` + `hHreg` alone: `doorRhoOfDelta` is built FROM `δ₀`, so the
clearing constant no longer has to beat an opaque existential numeral.  Carried binders, all
in the open: `hframe` (`DoorFuseFrame` at `Cp`), `hbase` (`DoorRowZeroBase`), `hcap` (the A3
capstone family at the door pin `S ≡ 0` — still the one un-instantiated analytic binder),
`hbandbase` (`DoorBandBase`, the eight per-base band gates), `harith` (`DoorArithFrameRho`).
`hrows`, `henv`, ⟦gate 4⟧, the ceiling and the `T₀`-band are GONE from the statement.

## ⟦THE S11 LAW — DO NOT ROUTE THROUGH THE TWO ρ-CAP SHORTCUTS⟧

`harith`'s `DoorArithFrameRho` still has to be met by the spine.  Its `anchor` and `jfloor`
fields MUST be met **directly** at the instantiated `M`.  They must NOT be routed through
`M4ArithRho.m4_arith_anchor_of_C1_rho` / `M4ArithRho.m4_arith_jfloor_of_anchor_rho`: those two
helpers ask `Real.log (1/ρ) ≤ 10¹¹`, which is an unproved claim about the opaque `δ₀`
(REF-SOCKET-2's `ref2_rho_cap_not_derivable`, witness `δ₀ = e^{−10¹¹}`).  The escape is clean
— they are shortcuts, not the only road: both fields are `M`-LOWERS, met at the chosen anchor
numeral with the quantifier order `δ₀ → ρ → Aexp/K/x₀ → U1floor → g → R → M`, the single joint
constraint `L ≤ 1.371·10⁸·λ` being spine-controlled.  The ceiling itself is genuinely δ₀-free;
⟦RHO-PAGE⟧'s headline stands.

## ⟦THE ANCHOR NUMERAL — `log₂M + 1 ≥ 14728`, WORKING POINT 20000⟧

REF-SOCKET-2's ⟦AMENDMENT 2⟧: the binding `GRowsZeroGate` field is `p2` (the `p²` rows,
`1.002·μ + 15 ≤ log 2 · Adoor M`), not `level1`; it is NECESSARY, not a sufficient-condition
artifact (`gRows_forces_Adoor` derives it from `gRows` at `Ccc = 0` alone, the other two
summands of `a2RowsSum_door_decomp` being nonnegative).  The ⟦C1⟧ anchor numeral `2484` FAILS
it by 5.93× at the register top.  The certified replacement: the exact minimum is
`log₂M + 1 ≥ 14728` (`ref2_p2_threshold`), and ALL SEVEN `M`-side conditions hold jointly at
`log₂M + 1 = 20000`, `λ = 10¹¹` (`ref2_joint_window`) — a window `[14728, 1.44·10¹¹]` seven
orders wide, its upper end the socket's own `M`-cap.  Both certificates are kernel facts of
the refuter's scratch probes; the M4ArithZero header carries the matching erratum.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦THE FUSED TERMINAL⟧** (`m4_socket_discharged_fused`) — `m4_second_road`'s three demands
(⟦item 11⟧ at the `ρ`-grade, ⟦gate 4⟧, the ceiling) at ONE hypothesis set carrying BOTH
repairs: the density constant `Cp` free over the nonnegatives with the six-field
`DoorRowZeroBase`, the ⟦ALPHA-SURGERY⟧ base cap inside `SocketBase`, the `T₀`-band discharged
to `DoorBandBase`, and the δ₀ side reduced to `0 < δ₀` with `ρ := doorRhoOfDelta δ₀`.
The fusion of `M4ArithZero.m4_socket_discharged_bandfree_zero` and
`M4ArithRho.m4_arith_door_exit_of_delta`; REF-SOCKET-2 ⟦AMENDMENT 1⟧. -/
theorem m4_socket_discharged_fused (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                            (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) (hbandslot hbandbase) harith

/-! ## §GK — the G-lever twin

The fused terminal at `G := s13GK K M` (`GLever`), `(K : ℕ)` first.

⟦THE ONE NEW HYPOTHESIS⟧ `hK : K ≤ 1.7·10⁸`.  It is not this file's: it rides in from
`M4RowsChiZero.m4_hrowsSlot_at_door_zero_gk`, whose own row family needs the `A_gate_logK`
leg of the levered `CalFrameK` inhabitant (`DoorFrame.calFrameK_satisfiable_door_gk`), and
that leg holds exactly on `K ≤ 1.7·10⁸` (J-REF).  Everything else on this page is the landed
composition with `_gk` names.

⚠ ⟦THE BINDER SHADOW⟧ the landed statement binds a REAL `K` — ⟦C3⟧'s margined-floor constant
inside `DoorArithFrameRho`.  It is ALPHA-RENAMED to `Kar` so the lever's `(K : ℕ)` can go
first, per THE KDESIGN.  `RSanDoorRho`, `doorRhoOfDelta`, `m4ChiRowGraded`, `doorRowFloor`,
`strataResidual` and `calH (H1door M)` are `G`-FREE (or LEVEL 1) and keep their landed names. -/

/-- `m4_socket_discharged_fused` (:79), at the lever. -/
theorem m4_socket_discharged_fused_gk (K : ℕ) (hK : K ≤ 170000000) (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                            (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_gk K R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_gk K hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) (hbandslot hbandbase) harith

end Salt.MR

-- #audit (temporary)

end
