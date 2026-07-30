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

end Salt.MR

end
