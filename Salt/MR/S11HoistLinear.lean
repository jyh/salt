/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ClosureRepairLinear

/-!
# ⟦LADDER-L G3 §7⟧ — `S11Hoist` at the LINEAR anchor (`S11HoistLinear`)

⟦COMPOSE-FLAT-2⟧'s ladder re-cut, at the S11 HOIST.  The `_L` twin family of the hoisted /
split / split-graded band slots and fused terminals, and of the window-mass absorption core,
all at `AdoorL M = 2^36·M`.

⟦THE ONE HYPOTHESIS THE RE-CUT ADDS⟧ `1 ≤ M`.  The landed `s11_calP_door_geR` is
UNCONDITIONAL because `Adoor 0 = 2^36`; at the linear anchor `AdoorL 0 = 0`, so the `2^36`
floor is `AdoorL_ge hM`.  That single hypothesis propagates to `s11_windowMass_c_le_L` and is
already present everywhere else.

`s11_calE_doorL_two`, `s11_log_calQK_doorL_two`, `s11_log_calP_doorL_one` are `DoorLinear`'s,
already landed; `s11_one_le_rpow_M` and `s11_wmc_le_of_ratio` are ladder-BLIND and reused.

PURELY ADDITIVE: no landed declaration moves.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- `S11Hoist.s11_calP_door_geR` (:501) at the linear anchor.  ⟦THE ADDED HYPOTHESIS⟧
`1 ≤ M`: `AdoorL 0 = 0`, so the `2^36` anchor floor is conditional. -/
theorem s11_calP_door_geR_L {M : ℕ} (hM : 1 ≤ M) :
    (68719476736 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hP : calP (AdoorL M) (3072 * M) 1 = 2 ^ AdoorL M := by rw [calP, calE_one]
  have h36 : 36 ≤ AdoorL M := le_trans (by norm_num) (AdoorL_ge_old hM)
  have hbig : (2 : ℕ) ^ 36 ≤ 2 ^ AdoorL M := Nat.pow_le_pow_right (by norm_num) h36
  have : (68719476736 : ℕ) ≤ calP (AdoorL M) (3072 * M) 1 := by rw [hP]; omega
  exact_mod_cast this

/-- **THE `c`-EXPONENT, CONTROLLED, AT THE LINEAR DOOR** (`s11_windowMass_c_le_L`). -/
theorem s11_windowMass_c_le_L {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) + 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) ≤ 1.05 := by
  have hPR : (68719476736 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
    s11_calP_door_geR_L hM
  have hden : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1 := by linarith
  have : 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) ≤ 1 / 68719476735 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  linarith

/-- **⟦THE ABSORPTION CORE, AT THE LINEAR DOOR⟧** (`s11_windowMassConst_door_le_L`) — the
linear door window's mass constant is `M^{2.1}` up to an absolute factor.  The ratio
`𝒬₂/𝒫₁`'s log is `49152·M²` at the linear anchor exactly as at the landed one (the anchor
cancels between the two levels), so the landed arithmetic replays verbatim. -/
theorem s11_windowMassConst_door_le_L (M : ℕ) (hM : 1 ≤ M) :
    windowMassConst (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2)
      ≤ Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAdR : (1 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by exact_mod_cast one_le_AdoorL hM
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 1 + 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) with hc
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    have hPR : (68719476736 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
      s11_calP_door_geR_L hM
    have hden : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1 := by linarith
    have : (0 : ℝ) ≤ 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) :=
      one_div_nonneg.mpr hden.le
    linarith
  have hcle : c ≤ 1.05 := s11_windowMass_c_le_L hM
  have hratio : Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ))
      - Real.log (Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      = Real.log (49152 * (M : ℝ) ^ 2) := by
    rw [s11_log_calQK_doorL_two, s11_log_calP_doorL_one]
    rw [show (49152 : ℝ) * (M : ℝ) ^ 2 * ((AdoorL M : ℕ) : ℝ) * Real.log 2
        = (49152 * (M : ℝ) ^ 2) * (((AdoorL M : ℕ) : ℝ) * Real.log 2) by ring]
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


/-- **⟦THE `hband` SLOT, MET, HOISTED⟧** (`m4_hband_at_door_slot_hoisted_L`) —
`M4SocketDischarge.m4_hband_at_door_slot` with `R`, `C₁`, `M₀` moved INSIDE the `∃ C' x₀`.
The proof is the landed one with the `intro` moved; the supplier
(`m4_hT0band_at_door_discharged_L` at the door's own `(P, Q)`) never saw those three
arguments. -/
theorem m4_hband_at_door_slot_hoisted_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged_L hMmu Aexp hAexp
    (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L M hM
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

/-- **⟦THE FUSED TERMINAL, HOISTED⟧** (`m4_socket_discharged_fused_hoisted_L`) —
`M4SocketFused.m4_socket_discharged_fused` with the band's `∃ C' x₀` pulled in front of
`R`, `C₁`, `M₀`.  Hypothesis list, conclusion and constants: byte-identical. -/
theorem m4_socket_discharged_fused_hoisted_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
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
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_hoisted_L hMmu Aexp hAexp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-- **⟦THE `hband` SLOT, SPLIT-HOISTED⟧** (`m4_hband_at_door_slot_split_L`) — §1 with `x₀`
moved in front of `M` and `C'` left behind it. -/
theorem m4_hband_at_door_slot_split_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ x₀ : ℕ, ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, hsplit⟩ := m4_hT0band_at_door_discharged_split_L hMmu Aexp hAexp
  refine ⟨x₀, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L M hM
  obtain ⟨C', hC'pos, hband⟩ := hsplit
    (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L M hM
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

/-- **⟦THE FUSED TERMINAL, SPLIT-HOISTED⟧** (`m4_socket_discharged_fused_split_L`) — §2 with
`x₀` in the top constant block. -/
theorem m4_socket_discharged_fused_split_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
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
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  obtain ⟨x₀, hbandsplit⟩ := m4_hband_at_door_slot_split_L hMmu Aexp hAexp
  refine ⟨Ct, x₀, hCt, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-- **⟦THE `hband` SLOT, SPLIT-HOISTED + GRADED — THE SEPARATION POINT⟧**
(`m4_hband_at_door_slot_split_graded_L`) — §5's link 5 with the band constant's `M`-slope
EXPLICIT: `C' ≤ Cb·M^{2.1}`, `Cb := (C·4^{Aexp}·exp 26.25·49152^{1.05}) + 1` in the top
constant block beside `x₀`.  The body is §5's byte for byte. -/
theorem m4_hband_at_door_slot_split_graded_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (x₀ : ℕ) (Cb : ℝ), 0 < Cb ∧ ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := m4_hT0band_at_door_discharged_split_graded_L hMmu Aexp hAexp
  have h4A : (0 : ℝ) < (4 : ℝ) ^ Aexp := Real.rpow_pos_of_pos (by norm_num) Aexp
  have hEpos : (0 : ℝ) < Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ) := by positivity
  refine ⟨x₀, C * (4 : ℝ) ^ Aexp * (Real.exp 26.25 * (49152 : ℝ) ^ (1.05 : ℝ)) + 1,
    by positivity, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L M hM
  obtain ⟨C', hC'pos, hC'le, hband⟩ := hsplit
    (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L M hM
  refine ⟨C', hC'pos, ?_, ?_⟩
  · -- ⟦THE ABSORPTION⟧ the window's mass, priced in `M`
    have hmass := s11_windowMassConst_door_le_L M hM
    have hone := s11_one_le_rpow_M M hM
    have hstep : C * (4 : ℝ) ^ Aexp
        * windowMassConst (calP (AdoorL M) (3072 * M) 1) (calQK (AdoorL M) (3072 * M) M 2)
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

/-- **⟦THE FUSED TERMINAL, SPLIT-HOISTED + GRADED⟧** (`m4_socket_discharged_fused_split_graded_L`)
— §5's link 6 with `Cb` in the top constant block and `C' ≤ Cb·M^{2.1}` carried. -/
theorem m4_socket_discharged_fused_split_graded_L (hMmu : MmuChiRate) (Aexp : ℝ)
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
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ := m4_hband_at_door_slot_split_graded_L hMmu Aexp hAexp
  refine ⟨Ct, Cb, x₀, hCt, hCb, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-! ## §GK — the `G`-lever twins, at the LINEAR door -/

/-- `s11_windowMassConst_door_le_L` (:523), at the lever.  The ratio `log 𝒬₂ / log 𝒫₁` is
EXACTLY `49152·2^K·M²`, so the lever's whole cost to the band constant is the absolute factor
`2^{1.05K}`; the `M`-slope stays `M^{2.1}`.

The proof is the landed one after ONE transport: `𝒫₁` is LEVEL 1
(`GLever.calP_gk_one_eq`), so the Euler exponent `c = 1 + 1/(𝒫₁−1)` and its cap
`s11_windowMass_c_le_L` are the landed objects verbatim; only the `𝒬₂` leg of the ratio moves. -/
theorem s11_windowMassConst_door_le_L_gk (K M : ℕ) (hM : 1 ≤ M) :
    windowMassConst (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 2)
      ≤ Real.exp 26.25 * ((49152 : ℝ) * 2 ^ K) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAdR : (1 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by exact_mod_cast one_le_AdoorL hM
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2K : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hR1 : (1 : ℝ) ≤ 49152 * 2 ^ K * (M : ℝ) ^ 2 := by nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hR0 : (0 : ℝ) < 49152 * 2 ^ K * (M : ℝ) ^ 2 := by linarith
  -- ⟦THE LEVEL-1 TRANSPORT⟧ `𝒫₁` does not move, so the whole `c`-side is the landed one
  rw [calP_gk_one_eq]
  set c : ℝ := 1 + 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) with hc
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    have hPR : (68719476736 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
      s11_calP_door_geR_L hM
    have hden : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1 := by linarith
    have : (0 : ℝ) ≤ 1 / (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) - 1) :=
      one_div_nonneg.mpr hden.le
    linarith
  have hcle : c ≤ 1.05 := s11_windowMass_c_le_L hM
  have hratio : Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ))
      - Real.log (Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      = Real.log (49152 * 2 ^ K * (M : ℝ) ^ 2) := by
    rw [s11_log_calQK_doorL_two_gk, s11_log_calP_doorL_one]
    rw [show (49152 : ℝ) * 2 ^ K * (M : ℝ) ^ 2 * ((AdoorL M : ℕ) : ℝ) * Real.log 2
        = (49152 * 2 ^ K * (M : ℝ) ^ 2) * (((AdoorL M : ℕ) : ℝ) * Real.log 2) by ring]
    rw [Real.log_mul (ne_of_gt hR0) (by positivity)]
    ring
  rw [windowMassConst, ← hc, hratio]
  have hsplit : Real.exp (c * (Real.log (49152 * 2 ^ K * (M : ℝ) ^ 2) + 25))
      = Real.exp (25 * c) * (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ c := by
    rw [Real.rpow_def_of_pos hR0, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  have h1 : Real.exp (25 * c) ≤ Real.exp 26.25 := Real.exp_le_exp.mpr (by linarith)
  have h2 : (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ c
      ≤ (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ (1.05 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR1 hcle
  have hM2 : ((M : ℝ) ^ 2) ^ (1.05 : ℝ) = (M : ℝ) ^ (2.1 : ℝ) := by
    rw [← Real.rpow_natCast (M : ℝ) 2, ← Real.rpow_mul (by linarith)]
    norm_num
  have h3 : (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ (1.05 : ℝ)
      = ((49152 : ℝ) * 2 ^ K) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
    rw [show (49152 : ℝ) * 2 ^ K * (M : ℝ) ^ 2 = ((49152 : ℝ) * 2 ^ K) * (M : ℝ) ^ 2 by ring,
      Real.mul_rpow (by positivity) (by positivity), hM2]
  rw [h3] at h2
  have hpos : (0 : ℝ) < (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ c := Real.rpow_pos_of_pos hR0 c
  calc Real.exp (25 * c) * (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ c
      ≤ Real.exp 26.25 * (49152 * 2 ^ K * (M : ℝ) ^ 2) ^ c :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ ≤ Real.exp 26.25 * (((49152 : ℝ) * 2 ^ K) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp 26.25 * ((49152 : ℝ) * 2 ^ K) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by ring

/-- **⟦THE `K`-FREE REPRICE⟧** (`s11_windowMassConst_door_prod_le_L_gk`) — the door's mass,
priced PER BLOCK:

  `windowMassConst 𝒫₁ 𝒬₁ · windowMassConst 𝒫₂ 𝒬₂ ≤ e^{52.5}·4^{1.05}·M^{2.1}`

against the single-covering-window `s11_windowMassConst_door_le_L_gk`, whose absolute factor
carries `2^{1.05K}`.  ⟦WHY `K` LEAVES⟧ the two per-block loglog gaps are `log M` and
`log(4M)` at EVERY base `G` — the lever's `G` cancels inside each block and survives only in
the CROSS ratio `log 𝒬₂/log 𝒫₁` the covering window reads.  The `M`-slope is unchanged at
`M^{2.1}`, so `S11HoistGrade`'s absorption is reused VERBATIM. -/
theorem s11_windowMassConst_door_prod_le_L_gk (K M : ℕ) (hM : 1 ≤ M) :
    windowMassConst (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 1)
        * windowMassConst (calP (AdoorL M) (s13GK K M) 2)
            (calQK (AdoorL M) (s13GK K M) M 2)
      ≤ Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hAd := one_le_AdoorL hM
  have hd1 : Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
      - Real.log (Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) = Real.log (M : ℝ) :=
    loglog_calQK_sub_calP (AdoorL M) (s13GK K M) M hAd hM
  have he2 : calE (AdoorL M) (s13GK K M) 2 = AdoorL M * s13GK K M * 4 := by
    simp [calE, Nat.factorial]
  have he2pos : 1 ≤ calE (AdoorL M) (s13GK K M) 2 := by
    rw [he2]; have := one_le_s13GK K hM; nlinarith [hAd]
  have he2R : (1 : ℝ) ≤ ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by exact_mod_cast he2pos
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd2 : Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ))
      - Real.log (Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
      = Real.log (4 * (M : ℝ)) := by
    have hP : Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)
        = ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) * Real.log 2 := by
      rw [calP]; push_cast; rw [Real.log_pow]
    have hQ : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
        = (4 * (M : ℝ)) * (((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) * Real.log 2) := by
      rw [calQK]; push_cast; rw [Real.log_pow]; push_cast; ring
    rw [hP, hQ, Real.log_mul (by positivity) (by positivity)]; ring
  have hP1ge : (68719476736 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    rw [calP_gk_one_eq]; exact s11_calP_door_geR_L hM
  have hP2ge : (68719476736 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by
    refine le_trans hP1ge ?_
    have : calP (AdoorL M) (s13GK K M) 1 ≤ calP (AdoorL M) (s13GK K M) 2 := by
      rw [calP, calP]
      exact Nat.pow_le_pow_right (by norm_num)
        (calE_mono (AdoorL M) (one_le_s13GK K hM) (by norm_num : (1 : ℕ) ≤ 2))
    exact_mod_cast this
  have hcaps : ∀ {P : ℕ}, (68719476736 : ℝ) ≤ ((P : ℕ) : ℝ) →
      (1 : ℝ) ≤ 1 + 1 / ((P : ℝ) - 1) ∧ (1 : ℝ) + 1 / ((P : ℝ) - 1) ≤ 1.05 := by
    intro P hP
    have hden : (0 : ℝ) < (P : ℝ) - 1 := by linarith
    have h1 : (0 : ℝ) ≤ 1 / ((P : ℝ) - 1) := one_div_nonneg.mpr hden.le
    have h2 : 1 / ((P : ℝ) - 1) ≤ 1 / 68719476735 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    exact ⟨by linarith, by linarith⟩
  obtain ⟨-, hc1b⟩ := hcaps hP1ge
  obtain ⟨-, hc2b⟩ := hcaps hP2ge
  have hb1 := s11_wmc_le_of_ratio (P := calP (AdoorL M) (s13GK K M) 1)
    (Q := calQK (AdoorL M) (s13GK K M) M 1) hMR hd1 hc1b
  have hb2 := s11_wmc_le_of_ratio (P := calP (AdoorL M) (s13GK K M) 2)
    (Q := calQK (AdoorL M) (s13GK K M) M 2) (by linarith : (1 : ℝ) ≤ 4 * (M : ℝ)) hd2 hc2b
  have hsplit4 : (4 * (M : ℝ)) ^ (1.05 : ℝ) = (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (1.05 : ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hMsum : (M : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (1.05 : ℝ) = (M : ℝ) ^ (2.1 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have he : Real.exp 26.25 * Real.exp 26.25 = Real.exp 52.5 := by
    rw [← Real.exp_add]; norm_num
  have h0b : (0 : ℝ) ≤ windowMassConst (calP (AdoorL M) (s13GK K M) 2)
      (calQK (AdoorL M) (s13GK K M) M 2) := (Real.exp_pos _).le
  have hR1 : (0 : ℝ) ≤ Real.exp 26.25 * (M : ℝ) ^ (1.05 : ℝ) := by positivity
  calc windowMassConst (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 1)
        * windowMassConst (calP (AdoorL M) (s13GK K M) 2) (calQK (AdoorL M) (s13GK K M) M 2)
      ≤ (Real.exp 26.25 * (M : ℝ) ^ (1.05 : ℝ))
          * (Real.exp 26.25 * (4 * (M : ℝ)) ^ (1.05 : ℝ)) := mul_le_mul hb1 hb2 h0b hR1
    _ = Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ) := by
        rw [hsplit4, ← he, ← hMsum]; ring

/-- `m4_hband_at_door_slot_hoisted_L` (:58), at the lever. -/
theorem m4_hband_at_door_slot_hoisted_L_gk (K : ℕ) (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) (M : ℕ) (hM : 1 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L_gk K M hM
  obtain ⟨C', x₀, hC'pos, hband⟩ := m4_hT0band_at_door_discharged_L_gk K hMmu Aexp hAexp
    (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L_gk K M hM
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

/-- `m4_socket_discharged_fused_hoisted_L` (:92), at the lever. -/
theorem m4_socket_discharged_fused_hoisted_L_gk (K : ℕ) (hK : K ≤ 170000000)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                            (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L_gk K R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_hoisted_L_gk K hMmu Aexp hAexp M hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-- `m4_hband_at_door_slot_split_L` (:307), at the lever. -/
theorem m4_hband_at_door_slot_split_L_gk (K : ℕ) (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ x₀ : ℕ, ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, hsplit⟩ := m4_hT0band_at_door_discharged_split_L_gk K hMmu Aexp hAexp
  refine ⟨x₀, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L_gk K M hM
  obtain ⟨C', hC'pos, hband⟩ := hsplit
    (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 2) hP4 hPQ
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L_gk K M hM
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

/-- `m4_socket_discharged_fused_split_L` (:341), at the lever. -/
theorem m4_socket_discharged_fused_split_L_gk (K : ℕ) (hK : K ≤ 170000000) (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Ct : ℝ) (x₀ : ℕ), 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                            (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L_gk K R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk K hK
  obtain ⟨x₀, hbandsplit⟩ := m4_hband_at_door_slot_split_L_gk K hMmu Aexp hAexp
  refine ⟨Ct, x₀, hCt, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

/-- `m4_hband_at_door_slot_split_graded_L` (:582), at the lever — ⟦THE SEPARATION POINT⟧.  The
`M`-slope is UNCHANGED (`M^{2.1}`).

⟦LEVEL2-PROD, 2026-07-31 — THE RE-WITNESS⟧ the `∃`-witness for `Cb` is now the PER-BLOCK
price `C·4^{Aexp}·(e^{52.5}·4^{1.05}) + 1` (`s11_windowMassConst_door_prod_le_L_gk`), which
carries NO `K` — in place of the covering-window price
`C·4^{Aexp}·(e^{26.25}·(49152·2^K)^{1.05}) + 1`, whose `2^{1.05K}` was the `G`-lever's
recoil.  **THE STATEMENT IS UNCHANGED**: `Cb` is existential, so every consumer below
(`S11HoistGrade`, `S12ConstCompose`'s `Mfl = s11GradeFloor Cb`) inherits the smaller witness
with no edit.  `s11_windowMassConst_door_le_L_gk` is untouched and still names the
covering-window price. -/
theorem m4_hband_at_door_slot_split_graded_L_gk (K : ℕ) (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ (x₀ : ℕ) (Cb : ℝ), 0 < Cb ∧ ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ :=
    m4_hT0band_at_door_discharged_split_graded_prod_L_gk K hMmu Aexp hAexp
  have h4A : (0 : ℝ) < (4 : ℝ) ^ Aexp := Real.rpow_pos_of_pos (by norm_num) Aexp
  have hEpos : (0 : ℝ) < Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) := by positivity
  refine ⟨x₀, C * (4 : ℝ) ^ Aexp * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1,
    by positivity, ?_⟩
  intro M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L_gk K M hM
  obtain ⟨hP4₁, hPQ₁⟩ := door_block_bounds_L_gk K M hM (j := 1) le_rfl
  obtain ⟨hP4₂, hPQ₂⟩ := door_block_bounds_L_gk K M hM (j := 2) (by norm_num)
  obtain ⟨C', hC'pos, hC'le, hband⟩ := hsplit
    (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 2)
    (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 1)
    (calP (AdoorL M) (s13GK K M) 2) (calQK (AdoorL M) (s13GK K M) M 2)
    hP4 hPQ hP4₁ hPQ₁ hP4₂ hPQ₂
  obtain ⟨hcovP, hcovQ⟩ := door_cover_L_gk K M hM
  have hcovB := door_block_cover_L_gk K M
  refine ⟨C', hC'pos, ?_, ?_⟩
  · -- ⟦THE ABSORPTION⟧ the per-block mass, priced in `M` — `K`-FREE
    have hmass := s11_windowMassConst_door_prod_le_L_gk K M hM
    have hone := s11_one_le_rpow_M M hM
    have hstep : C * (4 : ℝ) ^ Aexp
        * (windowMassConst (calP (AdoorL M) (s13GK K M) 1) (calQK (AdoorL M) (s13GK K M) M 1)
            * windowMassConst (calP (AdoorL M) (s13GK K M) 2)
                (calQK (AdoorL M) (s13GK K M) M 2))
        ≤ C * (4 : ℝ) ^ Aexp
            * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ)) := by
      have hcoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ Aexp := by positivity
      exact mul_le_mul_of_nonneg_left hmass hcoef
    have hexp : (C * (4 : ℝ) ^ Aexp * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
        * (M : ℝ) ^ (2.1 : ℝ)
        = C * (4 : ℝ) ^ Aexp * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) * (M : ℝ) ^ (2.1 : ℝ))
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
      hD.x₀_le h16 hD.qfit hcovP hcovQ hcovB hD.gHalf hD.gO1 hD.gWin hD.grade hD.err

/-- `m4_socket_discharged_fused_split_graded_L` (:634), at the lever. -/
theorem m4_socket_discharged_fused_split_graded_L_gk (K : ℕ) (hK : K ≤ 170000000)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (Ct Cb : ℝ) (x₀ : ℕ), 0 < Ct ∧ 0 < Cb ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (M : ℕ), 1 ≤ M →
        ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
          ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ)
            (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                            (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L_gk K R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk K hK
  obtain ⟨x₀, Cb, hCb, hbandsplit⟩ :=
    m4_hband_at_door_slot_split_graded_L_gk K hMmu Aexp hAexp
  refine ⟨Ct, Cb, x₀, hCt, hCb, ?_⟩
  intro Cp hCp M hM
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro R C₁ M₀ ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap)
    (hbandslot R C₁ M₀ hbandbase) harith

end Salt.MR

end
