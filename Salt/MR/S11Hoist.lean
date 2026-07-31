/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamErrWS

/-!
# ⟦S0-HOIST⟧ — the band constants born BEFORE the regime

The socket terminals (`M4SocketFused.m4_socket_discharged_fused` and its cap-wired
descendants) quantify the band's two constants AFTER the regime:

  `∀ Cp, ∀ R M C₁ M₀, 1 ≤ M → ∃ C' x₀, 0 < C' ∧ …`.

The S11 spine cannot consume that order.  `DoorBandBase`'s `x₀_le` field is a floor on the
socket's own base range, and the base range is fixed by `R.x`, which is fixed by the `g`-arm,
which the spine must choose BEFORE the regime exists — so `C'` and `x₀` have to be in hand
before `g`, i.e. before `R`.

⟦WHY THE HOIST IS GENUINE⟧  the two constants come from ONE supplier,
`M4T0DatumDischarge.m4_hT0band_at_door_discharged`, fired at

  `(P, Q) = (calP (Adoor M) (3072M) 1, calQK (Adoor M) (3072M) M 2)`

— `M`-dependent and nothing else.  `R`, `C₁`, `M₀` enter `M4SocketDischarge`'s band slot only
inside the CONCLUSION (through `SocketBase R M …` and `DoorBandBase … (C₁ (A+s)) (M₀ (A+s))`),
never in the choice of `C'`/`x₀`.  So the `∃` commutes past them, and this file states the
commuted twins:

* `m4_hband_at_door_slot_hoisted` — the band slot with `R C₁ M₀` inside;
* `m4_socket_discharged_fused_hoisted` — the fused terminal at prefix
  `∀ Cp, ∀ M, 1 ≤ M → ∃ C' x₀, 0 < C' ∧ ∀ R C₁ M₀, …`;
* `m4_socket_discharged_capwired_ws_hoisted` — the same for `RamErrWS`'s cap-wired terminal
  at the strict pair law (the ⟦E-binder⟧ form).

Each proof is the landed proof with the `intro` list re-ordered; not one hypothesis is
weakened or added, and the conclusions are byte-identical.  PURELY ADDITIVE: no landed
declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the band slot, hoisted -/

/-- **⟦THE `hband` SLOT, MET, HOISTED⟧** (`m4_hband_at_door_slot_hoisted`) —
`M4SocketDischarge.m4_hband_at_door_slot` with `R`, `C₁`, `M₀` moved INSIDE the `∃ C' x₀`.
The proof is the landed one with the `intro` moved; the supplier
(`m4_hT0band_at_door_discharged` at the door's own `(P, Q)`) never saw those three
arguments. -/
theorem m4_hband_at_door_slot_hoisted (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
            DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged hMmu Aexp hAexp
    (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ hgates H L q j A s hb χ
  have hq : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hgates H L q j A s hb
  have h16 : 16 ≤ A + s := by
    have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
    have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
    exact_mod_cast this
  exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
    hD.x₀_le h16 hD.qfit hcovP hcovQ hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-! ## §2 — the fused terminal, hoisted -/

/-- **⟦THE FUSED TERMINAL, HOISTED⟧** (`m4_socket_discharged_fused_hoisted`) —
`M4SocketFused.m4_socket_discharged_fused` with the band's `∃ C' x₀` pulled in front of
`R`, `C₁`, `M₀`.  Hypothesis list, conclusion and constants: byte-identical. -/
theorem m4_socket_discharged_fused_hoisted (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
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
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_hoisted hMmu Aexp hAexp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-! ## §3 — the cap-wired terminal at the strict pair law, hoisted -/

set_option maxHeartbeats 1000000 in
-- The statement re-elaborates the cap-wired terminal's full binder list (same cause as
-- `RamErrWS` §4 and `M4CapWire` §5).
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW, HOISTED⟧**
(`m4_socket_discharged_capwired_ws_hoisted`) — `RamErrWS.m4_socket_discharged_capwired_ws`
with the band's `∃ C' x₀` pulled in front of `R`, `C₁`, `M₀`.  The proof composes the hoisted
fused terminal with `M4CapWire.m4_hcap_at_door` and `RamErrWS.m4_capE_at_door` exactly as the
landed pair does; the six constants, the `hcapbase` bundle `DoorCapErrWS`, the pinned `t₁ ≡ 0`
and the three conjuncts are byte-identical. -/
theorem m4_socket_discharged_capwired_ws_hoisted (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                            VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
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
  obtain ⟨Ct, hCt, hfused⟩ := m4_socket_discharged_fused_hoisted hMmu Aexp hAexp
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hfused Cp hCp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm R C₁ M₀ ε cU bU (fun _ _ => (0 : ℝ)) K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase
    (hwire R M cU ε hc1 ?_) hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-! ## §4 — ⟦KNOT-1 ARITY SURGERY⟧ the hoisted terminal at the PER-BLOCK co-factor range -/

set_option maxHeartbeats 1000000 in
-- Same cause as §3.
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW, HOISTED, PER-BLOCK⟧**
(`m4_socket_discharged_capwired_ws_hoisted_perBlock`) — §3 over
`M4CapWire.m4_hcap_at_door_perBlock`.  The band's `∃ C' x₀` is hoisted exactly as in §3; the
ONE difference from the landed statement is the type of the `hcapWS` family's `Mr`
existential (`ℕ → ℕ`) and, with it, `DoorCapBasePerBlock` in place of `DoorCapBase`. -/
theorem m4_socket_discharged_capwired_ws_hoisted_perBlock (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                            (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
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
  obtain ⟨Ct, hCt, hfused⟩ := m4_socket_discharged_fused_hoisted hMmu Aexp hAexp
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door_perBlock
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hfused Cp hCp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm R C₁ M₀ ε cU bU (fun _ _ => (0 : ℝ)) K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase
    (hwire R M cU ε hc1 ?_) hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-! ## §5 — ⟦THE SPLIT-HOIST⟧ (R3, 2026-07-30): `x₀` TO THE TOP, `C'` LEFT AFTER `M`

⟦THE K4-CENSUS's MOVE 1, links 5–7⟧  §1–§4 hoist the band's `∃ C' x₀` past `R, C₁, M₀` as ONE
block; the block still sits AFTER `M`.  The census's byte-warrant (`LambdaChiMask` §7) is that
`x₀` is `Aexp`-only at its birth, so the block SPLITS: `x₀` joins the top constant group and
only `C'` — which reads the door's `M`-dependent window through `windowMassConst` — stays
after `M`.

  landed  `∃ Ct Cq cs T₀ Kq Ks, … ∀ Cp ∀ M, 1 ≤ M → ∃ C' x₀, 0 < C' ∧ ∀ R C₁ M₀ …`
  split   `∃ Ct Cq cs T₀ Kq Ks x₀, … ∀ Cp ∀ M, 1 ≤ M → ∃ C', 0 < C' ∧ ∀ R C₁ M₀ …`

That is exactly the prefix `S12Compose.logChowla2_capstone_final` needs: `x₀` is available
before the regime `R` is chosen (so the `g`-arm may read it), while `C'` — and with it the
band's grade fit — is chosen after `M`, which is chosen after `R`.  `∀ R` sits after `∃ C'`
in every one of these statements, so a capstone that has already fixed `R` may still fire
them.  Each proof is the corresponding §1–§4 proof with the `obtain`/`refine` order changed;
no hypothesis is added or weakened, and the conclusions are byte-identical. -/

/-- **⟦THE `hband` SLOT, SPLIT-HOISTED⟧** (`m4_hband_at_door_slot_split`) — §1 with `x₀`
moved in front of `M` and `C'` left behind it. -/
theorem m4_hband_at_door_slot_split (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ x₀ : ℕ, ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, hsplit⟩ := m4_hT0band_at_door_discharged_split hMmu Aexp hAexp
  refine ⟨x₀, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds M hM
  obtain ⟨C', hC'pos, hband⟩ := hsplit
    (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover M hM
  refine ⟨C', hC'pos, ?_⟩
  intro R C₁ M₀ hgates H L q j A s hb χ
  have hq : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hgates H L q j A s hb
  have h16 : 16 ≤ A + s := by
    have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
    have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
    exact_mod_cast this
  exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
    hD.x₀_le h16 hD.qfit hcovP hcovQ hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-- **⟦THE FUSED TERMINAL, SPLIT-HOISTED⟧** (`m4_socket_discharged_fused_split`) — §2 with
`x₀` in the top constant block. -/
theorem m4_socket_discharged_fused_split (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Ct : ℝ) (x₀ : ℕ), 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
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
  obtain ⟨x₀, hbandsplit⟩ := m4_hband_at_door_slot_split hMmu Aexp hAexp
  refine ⟨Ct, x₀, hCt, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

set_option maxHeartbeats 1000000 in
-- Same cause as §3/§4.
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW, SPLIT-HOISTED, PER-BLOCK⟧**
(`m4_socket_discharged_capwired_ws_hoisted_perBlock_split`) — §4 with `x₀` in the top
constant block.  This is the terminal `S12Compose.logChowla2_capstone_final` consumes. -/
theorem m4_socket_discharged_capwired_ws_hoisted_perBlock_split (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ (Ct Cq cs T₀ Kq Ks : ℝ) (x₀ : ℕ),
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                            (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
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
  obtain ⟨Ct, x₀, hCt, hfused⟩ := m4_socket_discharged_fused_split hMmu Aexp hAexp
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door_perBlock
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, x₀, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hterm⟩ := hfused Cp hCp M hM
  refine ⟨C', hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm R C₁ M₀ ε cU bU (fun _ _ => (0 : ℝ)) K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase
    (hwire R M cU ε hc1 ?_) hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-! ## §6 — ⟦THE SPLIT-HOIST, GRADED⟧ (R3, 2026-07-30): THE `M`-SLOPE OF `C'`, EXPOSED

⟦B5-HOIST, links 5–7⟧  §5 put `x₀` in the top constant block; `C'` still arrives opaque after
`M`, and `S13BandGate.grade` (`8·C' ≤ (log 2 · doorRowFloor M)^{5/2+1/1000}`) cannot be read
as an `M`-floor against an opaque `C'`.  `M4T0DatumDischarge` §8 carries the shape one level
lower — `C' ≤ C·4^A·windowMassConst P Q + 1`, `C` in the top block.  THE SEPARATION POINT is
§5's `m4_hband_at_door_slot_split`, the ONLY place `M` enters: it fires the window at
`(𝒫₁, 𝒬₂) = (calP (Adoor M) (3072M) 1, calQK (Adoor M) (3072M) M 2)`.

⟦THE ONE ANALYTIC STEP⟧ (`s11_windowMassConst_door_le`) — the ~40-line escape "the window's
mass is `M`-uniform" is FALSE: `log 𝒬₂ / log 𝒫₁ = 49152·M²` EXACTLY (`s11_log_calQK_door_two`
over `s11_log_calP_door_one`).  But the ABSORPTION works, because the mass constant reads that
ratio only through a logarithm and an exponent `c = 1 + 1/(𝒫₁−1) ≤ 1.05` (uniform, off
`𝒫₁ = 2^{Adoor M} ≥ 2^{36}`):

  `windowMassConst 𝒫₁ 𝒬₂ = exp(c·(log(49152M²) + 25)) ≤ exp 26.25 · 49152^{1.05} · M^{2.1}`.

`M^{2.1}` against the gate's `M^{2.501}` leaves `M^{0.401}` of headroom, so `grade` becomes an
ordinary `M`-floor (`S11HoistGrade.s11_grade_absorption`).  Links 5–7 carry the resulting
conjunct `C' ≤ Cb·M^{2.1}` with `Cb` in the top constant block; the bodies are byte-identical
to §5's and §5 is untouched. -/

/-- The door's `e₂` in terms of `Adoor M` (`calE_door_two` re-expressed). -/
theorem s11_calE_door_two (M : ℕ) :
    calE (Adoor M) (3072 * M) 2 = 12288 * M * Adoor M := by
  rw [calE_door_two, Adoor]; ring

/-- `log 𝒬₂ = 49152·M²·Adoor M·log 2` at the door family. -/
theorem s11_log_calQK_door_two (M : ℕ) :
    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      = 49152 * (M : ℝ) ^ 2 * ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  rw [calQK, s11_calE_door_two]; push_cast; rw [Real.log_pow]; push_cast; ring

/-- `log 𝒫₁ = Adoor M · log 2` at the door family (`calE_one`). -/
theorem s11_log_calP_door_one (M : ℕ) :
    Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  rw [calP, calE_one]; push_cast; rw [Real.log_pow]

/-- `𝒫₁ = 2^{Adoor M} ≥ 2^{36}`, in ℝ — the floor that pins the Euler exponent `c`. -/
theorem s11_calP_door_geR (M : ℕ) :
    (68719476736 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hP : calP (Adoor M) (3072 * M) 1 = 2 ^ Adoor M := by rw [calP, calE_one]
  have h36 : 36 ≤ Adoor M := le_trans (by norm_num) (Adoor_ge_old M)
  have hbig : (2 : ℕ) ^ 36 ≤ 2 ^ Adoor M := Nat.pow_le_pow_right (by norm_num) h36
  have : (68719476736 : ℕ) ≤ calP (Adoor M) (3072 * M) 1 := by rw [hP]; omega
  exact_mod_cast this

/-- **THE `c`-EXPONENT, CONTROLLED**: `c = 1 + 1/(𝒫₁ − 1) ≤ 1.05`, uniformly in `M`. -/
theorem s11_windowMass_c_le (M : ℕ) :
    (1 : ℝ) + 1 / (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1) ≤ 1.05 := by
  have hPR : (68719476736 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := s11_calP_door_geR M
  have hden : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1 := by linarith
  have : 1 / (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1) ≤ 1 / 68719476735 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith

/-- **⟦THE ABSORPTION CORE⟧** (`s11_windowMassConst_door_le`) — the door window's mass constant
is `M^{2.1}` up to an absolute factor: `windowMassConst 𝒫₁ 𝒬₂ ≤ exp 26.25 · 49152^{1.05} ·
M^{2.1}` for every `M ≥ 1`.  The ratio itself is EXACTLY `49152·M²` (no `M`-uniform bound
exists); what saves the gate is that the mass constant sees it through `log` and an exponent
`c ≤ 1.05`. -/
theorem s11_windowMassConst_door_le (M : ℕ) (hM : 1 ≤ M) :
    windowMassConst (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2)
      ≤ Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAdR : (1 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by exact_mod_cast one_le_Adoor M
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 1 + 1 / (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1) with hc
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    have hPR : (68719476736 : ℝ) ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) :=
      s11_calP_door_geR M
    have hden : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1 := by linarith
    have : (0 : ℝ) ≤ 1 / (((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) - 1) :=
      one_div_nonneg.mpr hden.le
    linarith
  have hcle : c ≤ 1.05 := s11_windowMass_c_le M
  have hratio : Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ))
      - Real.log (Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      = Real.log (49152 * (M : ℝ) ^ 2) := by
    rw [s11_log_calQK_door_two, s11_log_calP_door_one]
    rw [show (49152 : ℝ) * (M : ℝ) ^ 2 * ((Adoor M : ℕ) : ℝ) * Real.log 2
        = (49152 * (M : ℝ) ^ 2) * (((Adoor M : ℕ) : ℝ) * Real.log 2) by ring]
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  rw [windowMassConst, ← hc, hratio]
  have hR0 : (0 : ℝ) < 49152 * (M : ℝ) ^ 2 := by positivity
  have hsplit : Real.exp (c * (Real.log (49152 * (M : ℝ) ^ 2) + 25))
      = Real.exp (25 * c) * (49152 * (M : ℝ) ^ 2) ^ c := by
    rw [Real.rpow_def_of_pos hR0, ← Real.exp_add]
    congr 1; ring
  rw [hsplit]
  have h1 : Real.exp (25 * c) ≤ Real.exp 26.25 := Real.exp_le_exp.mpr (by linarith)
  have h2 : (49152 * (M : ℝ) ^ 2) ^ c ≤ (49152 * (M : ℝ) ^ 2) ^ (1.05 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith) hcle
  have h3 : (49152 * (M : ℝ) ^ 2) ^ (1.05 : ℝ)
      = (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (M : ℝ) 2, ← Real.rpow_mul (by linarith)]
    norm_num
  rw [h3] at h2
  have hpos : (0 : ℝ) < (49152 * (M : ℝ) ^ 2) ^ c := Real.rpow_pos_of_pos hR0 c
  calc Real.exp (25 * c) * (49152 * (M : ℝ) ^ 2) ^ c
      ≤ Real.exp 26.25 * (49152 * (M : ℝ) ^ 2) ^ c :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ ≤ Real.exp 26.25 * ((49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by ring

/-- `1 ≤ M^{2.1}` for `M ≥ 1` — the one-line step that lets the additive `+1` be absorbed. -/
theorem s11_one_le_rpow_M (M : ℕ) (hM : 1 ≤ M) : (1 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hMR (by norm_num : (0 : ℝ) ≤ 2.1)
  rwa [Real.one_rpow] at h

/-- **⟦THE `hband` SLOT, SPLIT-HOISTED + GRADED — THE SEPARATION POINT⟧**
(`m4_hband_at_door_slot_split_graded`) — §5's link 5 with the band constant's `M`-slope
EXPLICIT: `C' ≤ Cb·M^{2.1}`, `Cb := (C·4^{Aexp}·exp 26.25·49152^{1.05}) + 1` in the top
constant block beside `x₀`.  The body is §5's byte for byte. -/
theorem m4_hband_at_door_slot_split_graded (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (x₀ : ℕ) (Cb : ℝ), 0 < Cb ∧ ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := m4_hT0band_at_door_discharged_split_graded hMmu Aexp hAexp
  have h4A : (0 : ℝ) < (4 : ℝ) ^ Aexp := Real.rpow_pos_of_pos (by norm_num) Aexp
  have hEpos : (0 : ℝ) < Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) := by positivity
  refine ⟨x₀, C * (4 : ℝ) ^ Aexp * (Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ)) + 1,
    by positivity, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds M hM
  obtain ⟨C', hC'pos, hC'le, hband⟩ := hsplit
    (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover M hM
  refine ⟨C', hC'pos, ?_, ?_⟩
  · -- ⟦THE ABSORPTION⟧ the window's mass, priced in `M`
    have hmass := s11_windowMassConst_door_le M hM
    have hone := s11_one_le_rpow_M M hM
    have hstep : C * (4 : ℝ) ^ Aexp
        * windowMassConst (calP (Adoor M) (3072 * M) 1) (calQK (Adoor M) (3072 * M) M 2)
        ≤ C * (4 : ℝ) ^ Aexp
            * (Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ)) := by
      have hcoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ Aexp := by positivity
      exact mul_le_mul_of_nonneg_left hmass hcoef
    have hexp : (C * (4 : ℝ) ^ Aexp * (Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ)) + 1)
        * (M : ℝ) ^ (2.1 : ℝ)
        = C * (4 : ℝ) ^ Aexp
            * (Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ))
          + (M : ℝ) ^ (2.1 : ℝ) := by ring
    linarith
  · intro R C₁ M₀ hgates H L q j A s hb χ
    have hq : 0 < q := hb.2.2.2.1
    haveI : NeZero q := ⟨hq.ne'⟩
    have hD := hgates H L q j A s hb
    have h16 : 16 ≤ A + s := by
      have h400 : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := hD.X400
      have : (16 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by linarith
      exact_mod_cast this
    exact hband q χ M (A + s) (2 * (A + s)) rfl hD.X400 (by omega) le_rfl hD.C₁_one
      hD.x₀_le h16 hD.qfit hcovP hcovQ hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-- **⟦THE FUSED TERMINAL, SPLIT-HOISTED + GRADED⟧** (`m4_socket_discharged_fused_split_graded`)
— §5's link 6 with `Cb` in the top constant block and `C' ≤ Cb·M^{2.1}` carried. -/
theorem m4_socket_discharged_fused_split_graded (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ (Ct Cb : ℝ) (x₀ : ℕ), 0 < Ct ∧ 0 < Cb ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
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
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ := m4_hband_at_door_slot_split_graded hMmu Aexp hAexp
  refine ⟨Ct, Cb, x₀, hCt, hCb, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

set_option maxHeartbeats 1000000 in
-- Same cause as §3/§4/§5.
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW, SPLIT-HOISTED + GRADED, PER-BLOCK⟧**
(`m4_socket_discharged_capwired_ws_hoisted_perBlock_split_graded`) — §5's link 7 with `Cb` in
the top constant block.  This is the terminal a capstone twin consumes when it needs the band
gate's `grade` line to be an ordinary `M`-floor. -/
theorem m4_socket_discharged_capwired_ws_hoisted_perBlock_split_graded (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Ct Cq cs T₀ Kq Ks Cb : ℝ) (x₀ : ℕ),
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < Cb ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                            (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
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
  obtain ⟨Ct, Cb, x₀, hCt, hCb, hfused⟩ := m4_socket_discharged_fused_split_graded hMmu Aexp hAexp
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door_perBlock
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, Cb, x₀, hCt, hCq, hcs, hT₀, hKq, hKs, hCb, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hC'le, hterm⟩ := hfused Cp hCp M hM
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro R C₁ M₀ ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm R C₁ M₀ ε cU bU (fun _ _ => (0 : ℝ)) K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase
    (hwire R M cU ε hc1 ?_) hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

end Salt.MR

end
