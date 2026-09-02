/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16ProducersH
import Salt.MR.S16UniformLH
import Salt.MR.S16FlatTerminalLinearLH

/-!
# THE UNIFORM CAPSTONES AT SHIFT `h` — wave H3, block C

⟦WHAT THIS FILE SETTLES⟧  The `A`-uniform, windowed, doubly-priced capstone at the inflated arc
cap, and the conditional that sits on it.  Everything below block U's exit
(`S16UniformLH.m4_second_road_L2_H_gk_flatRoot_L_exit_uniform`) and block W's rider
(`S16BandLaneCBoundedLH_win`) is already landed; this file is the join.

**§1 — THE `Ct` CEILING ON THE `h` LANE.**  Wave P's fuse
(`S16ProducersH.m4_closure_fuse_zero'_const_nonneg_H_L_gk`) carries `0 < Ct` and no ceiling,
while the capstone's statement carries `Ct ≤ 2^23`.  The two names here are the landed
`h`-lane slot and fuse re-obtained off `NumeralCt.m4_hrowsSum_chi_door_zero'_L_gk_bounded`
(`Ct ≤ 6·e^14`) and closed with `six_exp_fourteen_le_two_pow_23`.  **Proof bodies verbatim** —
only the source of `Ct` moves.

**§2 — THE CAPSTONE.**  `S16Compose.flat_capstone_uniform_win_ceiling` at shift `h`.
⛔ **ONE GATE IS NOT A TRANSCRIPTION, AND IT IS THE REASON H2a WORD 5 EXISTS.**  At `h = 1`
gate 7 (`128·arcDen^3 ≤ H`) is discharged from `arcFloor36 = 10^138`, which clears the demand by
**1.14×** and therefore FAILS from `h = 2`.  The `h` lane reads `arc36_of_regime_h` instead,
routed off `loglogFloor50 = ⌈e^{e^50}⌉₊` — a tower against a demand of `10^157`.  So the
`arcFloor36` hypothesis that the `h = 1` proof extracts is **not extracted here**; the floor stays
in the `U1floor` join (the cap arithmetic `flatCap_join_floor` still reads it) and only
`loglogFloor50` is spent.

⭐ **THE TRIVIAL GRADE PAYS `h^7` AND NOTHING ELSE DOES.**  The road's ⟦G1⟧ slot demands
`(h·arcDen 12 H)^7 ≤ RStr H`, so `RStr := h^7·rStrWitness` (`rStrWitness_G1_h`).  The `h^7` is
invisible at gate 10a — `m4BclGraded_le_of_fits` bounds the graded block by `2·(m4Cmax H · Fan H)`,
in which `Ftr` does not appear — so the ceiling arithmetic is the landed one **byte for byte**.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `Ct` CEILING AT THE INFLATED SOCKET -/

set_option maxHeartbeats 1000000 in
-- the landed slot's own budget: the 40-line statement re-elaborates the seam integrals at
-- every socket base, here with one extra conjunct in the `∃`-prefix
set_option maxHeartbeats 1000000 in
/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE INFLATED SOCKET, PRICED⟧**
(`m4_hrowsSlot_at_door_zero'H_L_gk` with `Ct ≤ 2^23`) — `S16ProducersH:1190` re-obtained off
`NumeralCt.m4_hrowsSum_chi_door_zero'_L_gk_bounded`.  Body verbatim. -/
theorem m4_hrowsSlot_at_door_zero'H_L_gk_ceiling (h K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
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
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hCtb, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk_bounded K hK
  refine ⟨Ct, hCt, le_trans hCtb six_exp_fourteen_le_two_pow_23, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

set_option maxHeartbeats 1000000 in
-- the landed fuse's own budget: sixteen socket-framed hypotheses re-elaborate against the
-- re-cut prefix
/-- **⟦THE CONSTANT-POOL FUSE AT THE INFLATED SOCKET, PRICED⟧**
(`m4_closure_fuse_zero'_const_nonneg_H_L_gk` with `Ct ≤ 2^23`) — `S16ProducersH:1322` off §1.
Body verbatim. -/
theorem m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log h ≤ 7) (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRowH_L_gk h K R M
          (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) := by
  obtain ⟨Ct, hCt, hCtb, hslot⟩ := m4_hrowsSlot_at_door_zero'H_L_gk_ceiling h K hK
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk h K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRhoH ρ h H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPoolH_L_gk K hh hh7 hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)


/-! ## §2 — THE CAPSTONE, WINDOWED, WITH BOTH SOCKET CEILINGS, AT SHIFT `h` -/

set_option maxHeartbeats 1600000 in
-- Same cause as the landed capstone: the ~120-line residue re-elaborates against the re-cut
-- prefix, here at the inflated socket and with the cap threaded through every gate.
/-- **⟦THE `A`-UNIFORM CAPSTONE, WINDOWED AND PRICED, AT SHIFT `h`⟧**
(`flat_capstone_uniform_win_ceiling_h`) — `S16Compose:484` on block U's `A`-uniform road and
block W's windowed rider, carrying `Kc ≤ 2^539` and `Ct ≤ 2^23`, at `ε` pinned by
`1/(500·h)` and `δ₀` by `1/(838400·h²)`.  ⛔ Gate 7 is routed off `loglogFloor50`, NOT
`arcFloor36` — see the file header. -/
theorem flat_capstone_uniform_win_ceiling_h (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_win h Awin K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                          ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        (h : ℝ) * arcDen 12 H
                          < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    m4_second_road_L2_H_gk_flatRoot_L_exit_uniform h hh hh7 K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling h hh hh7 K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb, hCtb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor⟧ ⭐ at `h` only `loglogFloor50` is read: `arc36_of_regime_h` routes
  -- gate 7 off the tower floor, because `arcFloor36` clears `h = 1` by 1.14× and FAILS at `h ≥ 2`.
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
    m4_arith_gate4_rhoH_L h M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h hh hh7 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-! ## §3 — THE CONDITIONAL, WINDOWED, WITH BOTH SOCKET CEILINGS, AT SHIFT `h` -/

set_option maxHeartbeats 1000000 in
-- Same cause as the landed conditional: the residue re-elaborates against the prefix.
/-- **⟦THE `A`-UNIFORM CONDITIONAL, WINDOWED AND PRICED, AT SHIFT `h`⟧**
(`flat_conditional_uniform_win_ceiling_h`) — `S16Compose:723` on §2, with wave H2b's `h` fire
list (`S16FlatTerminalLinearLH` §5) substituted for the `h = 1` one.

⭐ **`S13BandGate'_L_gk` DISSOLVES RATHER THAN PORTING.**  At `h = 1` the band register is
assembled into that structure (whose field ⟦4⟧ is socket-quantified) and handed to
`doorBandBase_family'_L_gk`.  Wave P's `doorBandBase_family'H_L_gk` takes the four components
directly, so the `h` lane never builds the structure — one socket-framed object that the row
table would have priced as a port costs nothing at all.

📌 Slot 3 carries H2a word 6's `+ 28`: `s13_g2_jfloor_of_MSelect'_L_gk_h` wants
`4·log(263·h·max 1 (arcDen 12 H)) ≤ doorRowFloorL M`, and the shift is bought from
`s13_g2_jfloor_of_MSelect'_L_gk_shift28` over the `h`-free family. -/
theorem flat_conditional_uniform_win_ceiling_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (hK : K ≤ 170000000) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_win h Awin K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_LH_gk h K R M → ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hKcb, hCtb, hMflb,
    hβ, hcapU⟩ :=
    flat_capstone_uniform_win_ceiling_h h hh hh7 K hK Awin hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hKcb, hCtb, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `28` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift28 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 28) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h hh hh7 hj0raw)
    (s13_gate8_L_gk_h hh hh7 le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h hh hh7 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk K hh hh7 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH hh hh7 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk K hh hh7 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

/-! ## §4 — ⟦KWIDE⟧ THE WIDE-CEILING TWINS

Mechanical widening of the flat `hK` ceiling binder: it moves INSIDE the internal `∀ M` as
`K ≤ 170000000 * M`, so the raised lever `KlevF` can flow.  Statements and proofs are verbatim
apart from that antecedent and the `_kwide` re-pointing — exactly the `h = 1` lane's own
§Xw discipline.  The originals are untouched. -/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSlot_at_door_zero'H_L_gk_ceiling_kwide`) — §1's slot. -/
theorem m4_hrowsSlot_at_door_zero'H_L_gk_ceiling_kwide (h K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) →
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
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
        ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hCtb, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk_bounded_kwide K
  refine ⟨Ct, hCt, le_trans hCtb six_exp_fourteen_le_two_pow_23, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate
    hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hKw hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

set_option maxHeartbeats 1000000 in
/-- ⟦WIDE CEILING TWIN⟧ (`m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide`) — §1's fuse,
off the slot above. -/
theorem m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log h ≤ 7) (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) →
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
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
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRowH_L_gk h K R M
          (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) := by
  obtain ⟨Ct, hCt, hCtb, hslot⟩ := m4_hrowsSlot_at_door_zero'H_L_gk_ceiling_kwide h K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hKw hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk h K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRhoH ρ h H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPoolH_L_gk K hh hh7 hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)

set_option maxHeartbeats 1600000 in
-- Same cause as §2: the ~120-line residue re-elaborates against the re-cut prefix.
/-- ⟦WIDE CEILING TWIN⟧ (`flat_capstone_uniform_win_ceiling_kwide_h`) — §2 widened. -/
theorem flat_capstone_uniform_win_ceiling_kwide_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_win h Awin K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                          ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        (h : ℝ) * arcDen 12 H
                          < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    m4_second_road_L2_H_gk_flatRoot_L_exit_uniform h hh hh7 K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide h hh hh7 K
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb, hCtb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor⟧ ⭐ at `h` only `loglogFloor50` is read: `arc36_of_regime_h` routes
  -- gate 7 off the tower floor, because `arcFloor36` clears `h = 1` by 1.14× and FAILS at `h ≥ 2`.
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
    m4_arith_gate4_rhoH_L h M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h hh hh7 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

set_option maxHeartbeats 1000000 in
/-- ⟦WIDE CEILING TWIN⟧ (`flat_conditional_uniform_win_ceiling_kwide_h`) — §3 on the capstone
above, the widened antecedent carried through the `∀ M`. -/
theorem flat_conditional_uniform_win_ceiling_kwide_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_win h Awin K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧ Ct ≤ 2 ^ 23 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ, K ≤ 170000000 * M →
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_LH_gk h K R M → ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hKcb, hCtb, hMflb,
    hβ, hcapU⟩ :=
    flat_capstone_uniform_win_ceiling_kwide_h h hh hh7 K Awin hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hKcb, hCtb, hMflb, hβ, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapU A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hKw hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `28` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift28 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 28) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h hh hh7 hj0raw)
    (s13_gate8_L_gk_h hh hh7 le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h hh hh7 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk K hh hh7 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH hh hh7 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk K hh hh7 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

/-! ## §5 — ⟦KHOIST⟧ THE `K`-HOISTED ROAD, AND THE CAPSTONES ON IT

⭐ **THE `K`-HOIST IS A PURE RE-BRACKETING ON THE `h` LANE, AND ITS LEGALITY IS ONE READ.**
The `h` road's `Cg` comes from `parseval_insert_budget_door_bounded` and its `H₀` from
`nearRatTight_of_bigXiArcTight_H` — **neither mentions `K`**.  `K` enters only inside the
`∀ R` body, through `M4DoorGates_L_gk K`, `s13GK K M` and `M4ChiSummedFreeRowH_L_gk h K`.  So
`∀ K` moves inside the `∃ Cg`/`∃ H₀` prefix with the proof bodies verbatim and one extra
`intro K`.  This is the same legality condition block U's head hoist met, read one level down.
-/

/-- `S16UniformLH.flatRootCapH_arc_u`, re-proved (the landed lemma is `private`). -/
private lemma flatRootCapH_arc_k (d p b c f : ℕ) :
    max (max d (max (max p b) c)) f ≤ max d (max (max (max p f) b) c) := by
  omega

set_option maxHeartbeats 1000000 in
/-- ⟦`K`-HOISTED⟧ (`m4_doorL2_supply_H_L_gk_khoist`) — `S16FlatTerminalLinearH:1470` with `∀ K`
moved inside the `∃ Cg`/`∃ H₀` prefix.  Body verbatim plus one `intro K`. -/
theorem m4_doorL2_supply_H_L_gk_khoist (h : ℕ) (hh : 0 < h) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (K : ℕ) (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (Kc Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSqH_L_gk h K R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXiH h R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
              MRTUniformityXiL2H h R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  refine ⟨Cg, hCg, hCgle, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight_H bigXiArcTight_twelve heps hh
  refine ⟨H₀, ?_⟩
  intro K R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 hsock hXi hK0 hceil
  -- ⟦the arc supply at the TWISTED set, transported to the regime's own `ε`⟧
  have harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXiH h R.eps H,
      NearRatTight ((h : ℝ) * arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
    intro H _ hH ξ hξ
    rw [hReps] at hξ
    exact hH₀ H hH ξ hξ
  -- ⟦the door's own scales, off the regime — the lane's four lines⟧
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦THE FUSE⟧ the adapter's `hins`, fired at `Xi := bigXiH h R.eps H`.
  have hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXiH h R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)
        ≤ δ / 4 + 4 * 2 ^ k / (R.x : ℝ) := by
    intro H _ hlo hhi
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXiH h R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  -- ⟦the adapter⟧ N4c: arc + socket at the inflated cap + count + the fused insert budget.
  have hkey := sum_bigXiH_norm_windowExpSum_sq_le_parseval h R
    (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC)
    Braw Kc (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) hfloor harc hBraw0 (hsock m4_bandTransport)
    hXi hins
  -- ⟦the budget line⟧ and the `H`-uniform ceiling on the socket leg.
  intro H _ hlo hhi
  have hb := hkey H hlo hhi
  rw [l2_budget_line Kc (Braw H) δ (R.x : ℝ) k] at hb
  have hmono : 2 * Kc * Braw H ≤ 2 * Kc * Bceil :=
    mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
  linarith

set_option maxHeartbeats 1000000 in
/-- ⟦`K`-HOISTED⟧ (`m4_second_road_L2_H_gk_flatRoot_L_khoist`) — `S16FlatTerminalLinearH:1588`
likewise, off the mint above. -/
theorem m4_second_road_L2_H_gk_flatRoot_L_khoist (h : ℕ) (hh : 0 < h) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (K : ℕ) (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (δ Bceil Kc : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXiH h R.eps H).card : ℝ) ≤ Kc) →
            0 ≤ Kc →
            M4ChiSummedFreeRowH_L_gk h K R M RS →
              MRTUniformityXiL2H h R (2 * Kc * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hCgle, hmint⟩ := m4_doorL2_supply_H_L_gk_khoist h hh
  refine ⟨Cg, hCg, hCgle, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := hmint eps heps
  refine ⟨H₀, ?_⟩
  intro K R hReps hfloor δ Bceil Kc RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han
    hG1 hG2 harc3 hdgate hdrift hceil hXi hKc0 hrow
  have hh1 : 1 ≤ h := hh
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqNH_L_gk h K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_suppliedH_L_gk h K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummedH_L_gk h K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidualH h H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2H_L_gk h K hgates hBblk0 hblk2
  refine hH₀ K R hReps hfloor Braw Kc Bceil δ M k hgates hBraw0 ?_ hXi hKc0 hceil
  refine m4_sievedDoorSq_of_blk2H_L_gk h K (ℓ := blockLenH h)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLenH h H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh1 hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLenH_le h H q hH1
  · intro H q hlo hhi _ _
    exact blockLenH_narrow (R := R) hh1 hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLenH_drift (R := R) hh1 hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have hdr := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidualH h H :=
      strataResidualH_nonneg (one_le_hArcDen_of_regime hh1 hlo)
    have hB := hBcl0 H
    nlinarith [hdr]

set_option maxHeartbeats 1000000 in
/-- ⟦`K`-HOISTED⟧ (`m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_khoist`) — block U's exit
(`S16UniformLH:69`) on the register above, `∀ K` sitting just before the `∀ A`.  This is the
`h` twin of `S16ComposeV4.flat_road_uniform_ceiling_khoist`. -/
theorem m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_khoist (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ((h : ℝ) * arcDen 12 H) ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * ((h : ℝ) * arcDen 12 H) ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  (h : ℝ) * arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRowH_L_gk h K R M RS →
                  ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hreg⟩ := m4_second_road_L2_H_gk_flatRoot_L_khoist h hh
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    flat_head_uniform_h h hh hh7
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, ε, Kb, δ₀, β, max Hopq H₀, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact flatRootCapH_arc_k _ _ _ _ _, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hcount, hRtow, hRcap, hR⟩ := hhd H₀ U1floor g
  refine ⟨R, hReps, hRU1, hRg, hRtow, le_trans hRcap (by omega), ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have hdoor := hH₀ K R hReps hRextra δ Bceil Kb RS RSan RStr Braw M k j₀ hgates hM hRSan0
    hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  exact hR δ₀ hδ₀ le_rfl (mrtUniformityXiL2H_mono hdoor hbudget)

set_option maxHeartbeats 1600000 in
-- Same cause as §4: the residue re-elaborates under one more binder layer.
/-- **⟦THE CAPSTONE, WINDOWED, WIDE-CEILINGED, `K`-HOISTED, AT SHIFT `h`⟧**
(`flat_capstone_uniform_win_ceiling_kwide_khoist_h`) — §4 on the `K`-hoisted road.  Only `Ct`
moves with `K` (it is the constant-pool fuse's), so it — and it alone — sits under the `∀ K`;
the landed twin's `Cq, cs, T₀, Kq, Ks` prefix members are DROPPED exactly as at `h = 1`. -/
theorem flat_capstone_uniform_win_ceiling_kwide_khoist_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_winU h Awin) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
                          ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        (h : ℝ) * arcDen 12 H
                          < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRhoH (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) h H)
                          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_khoist h hh hh7
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ :=
    m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide h hh hh7 K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the absorbed floor⟧ ⭐ at `h` only `loglogFloor50` is read: `arc36_of_regime_h` routes
  -- gate 7 off the tower floor, because `arcFloor36` clears `h = 1` by 1.14× and FAILS at `h ≥ 2`.
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRowH_L_gk h K R M
      (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H) j H ≤ RSanDoorRhoH ρ h H :=
    m4_arith_gate4_rhoH_L h M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 * (108 / 5 * RSanDoorRhoH ρ h H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_deltaH hh hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGradedH_L h M (fun _ H => RSanDoorRhoH ρ h H)) (RSanDoorRhoH ρ h)
    (fun H => (h : ℝ) ^ 7 * rStrWitness H)
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
          (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRhoH_nonneg hρpos.le h H)
    (fun H => rStrWitness_mul_nonneg h H) ?_ hgate4 (fun H _ _ => rStrWitness_G1_h h H) ?_
    (arc36_of_regime_h hh hh7 hllfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) (H := H)
      (by have := RSanDoorRhoH_nonneg hρpos.le h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRhoH ρ h H))
      (by have := rStrWitness_mul_nonneg h H
          simpa using (by linarith : (0:ℝ) ≤ 2 * ((h : ℝ) ^ 7 * rStrWitness H)))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hSR1 : (1 : ℝ) ≤ strataResidualH h H := one_le_strataResidualH harc1
    have hSRsq : (1 : ℝ) ≤ strataResidualH h H ^ 2 := by nlinarith
    have hRSle : RSanDoorRhoH ρ h H ≤ rSanWitness H := by
      have h1 : RSanDoorRhoH ρ h H ≤ 1 := by
        unfold RSanDoorRhoH
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor_h h hh H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRhoH ρ h H)
      (Ftr := fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ (h : ℝ) * arcDen 12 H := one_le_hArcDen_of_regime hh hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRhoH ρ h H)
            (fun H => 2 * ((h : ℝ) ^ 7 * rStrWitness H)) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRhoH ρ h H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
            * (108 / 5 * RSanDoorRhoH ρ h H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidualH h H ^ 2
        * (108 / 5 * RSanDoorRhoH ρ h H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

set_option maxHeartbeats 1600000 in
/-- **⟦THE CONDITIONAL, WINDOWED, WIDE-CEILINGED, `K`-HOISTED, AT SHIFT `h`⟧**
(`flat_conditional_uniform_win_ceiling_kwide_khoist_h`) — §4's conditional under the capstone
above, verbatim. -/
theorem flat_conditional_uniform_win_ceiling_kwide_khoist_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (Awin : ℝ)
    (hband : S16BandLaneCBoundedLH_winU h Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧ 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ, K ≤ 170000000 * M →
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                S15CrossingBound_LH_gk h K R M → ¬ logChowlaFails h R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hMfl, hCgle, hεpin, hδpin, hKcb, hMflb,
    hβ, hcapU⟩ :=
    flat_capstone_uniform_win_ceiling_kwide_khoist_h h hh hh7 Awin hband
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15ArmH h δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15ArmH h δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hKw hsel
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15ArmH_demoted h δ₀ ρ R.Hhi R.ω) hRarm
  have hhω : (0 : ℝ) ≤ (h : ℝ) * (R.ω : ℝ) := by positivity
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 ((h : ℝ) * (R.ω : ℝ)) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hhω ?_ hhi) (s15ArmH_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family at the inflated socket, arm read at `h·ω`
  have harith := s15_doorArithFrameRho_L_familyH'' (C₁ := fun _ : ℕ => (1 : ℝ)) hh hsel.hM
    hρ0 hρ1 hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧ — the register and its bridges are SOCKET-BLIND
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦slot 3⟧ H2a word 6's OUTER step, over the `h`-free family, with the `28` in the gate
  have hj0raw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have hgate := s13_g2_jfloor_of_MSelect'_L_gk_shift28 K (by linarith) hS
    have hbase := s13_g2_jfloor_gen (R := R)
      (F := ((doorRowFloorL M : ℕ) : ℝ) - 28) le_rfl (by linarith)
    intro H hlo hhi
    linarith [hbase H hlo hhi]
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_of_MSelect'_L_gk_h hh hh7 hj0raw)
    (s13_gate8_L_gk_h hh hh7 le_rfl (by linarith) hsel.gRows)
    (s13_smallGradeFits_of_halfWindow_L_gk_h hh hh7 hρ0 hρ1 hfl hsel.half)
    (fun H L q j A s hb => doorBaseFrame_at_socket_LH hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorLH_gk K hh hh7 hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flatH hh hh7 hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flatH hh hh7 hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM
        (s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'H_L_gk K hh hh7 hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (s15ArmH_rho hRarm) harith hsel.x0M (fun _ => le_rfl) hgrade
      (fun H L q j A s hb =>
        s15_block_at_socketH_L_gk K hh hh7 hb (hHreg H hb.1 hb.2.1) hsel.blk))
    harith

end Salt.MR
