/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S11HoistLinear
import Salt.Entropy.Chowla.GoldbachEnergyKcH
import Salt.MR.S13BandCapLinear
import Salt.MR.FlatFloorBump
import Salt.MR.S12ConstCompose
import Salt.MR.S12FuseCompose

/-!
# THE FLAT TERMINAL AT THE LINEAR LADDER — the re-fire

⟦WHAT THIS FILE SETTLES⟧  `S16FlatTerminal.logChowla2_witnessed_scale_flat` reaches the flat
road's terminal but CARRIES the `S15` register `S15Sel''_gk` as a named debt: at the flat
design point the LANDED door `Adoor M = 2^36·(⌊log₂M⌋+1)` cannot satisfy it
(⟦COMPOSE-FLAT-2⟧'s `flat_landed_ladder_break`).  ⟦LADDER-L⟧ G1–G4 re-cut the whole ladder
at `AdoorL M = 2^36·M`; this page composes that re-cut into the terminal and DISCHARGES the
register from `FlatFloorBump.s15_sel''_L_gk_witness_flat_bumped` at the flat design modulus
`M = flatDoorM A`.

⟦THE CHAIN⟧ §2 the road at the flat root and the linear ladder (`m4_second_road_L2_gk_
flatRoot_L`) → §3 HOP 3 → §4 HOP 4 → §5 THE TERMINAL.  Every proof body is the landed one
with the door reads moved: `Adoor → AdoorL`, `doorRowFloor → doorRowFloorL`,
`s13BlockExp_gk → s13BlockExp_L_gk`, `H1door → H1doorL`, `SocketBase → SocketBaseL`,
`doorChiCoeff_gk → doorChiCoeff_L_gk`, and the register `S15Sel''_gk → S15Sel''_L_gk`.  The
`G`-slot never moves (`s13GK K M` throughout).

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE BAND-LANE RIDER AT THE LINEAR DOOR -/

/-- **⟦THE BAND-LANE `C` RIDER, AT THE LINEAR LADDER⟧** (`S16BandLaneCBoundedL`) —
`S16Budget.S16BandLaneCBounded` with its socket family and band base read at
`AdoorL M = 2^36·M`.  Exactly as at the landed door, everything but `log C ≤ 40` is a theorem
at this very witness (`S11HoistLinear.m4_hband_at_door_slot_split_graded_L_gk`); the conjunct
is the honest rider on `MlambdaChi_rate`'s opaque `C_mu`. -/
def S16BandLaneCBoundedL (K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 40 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-! ## §1 — THE CONSTANT-POOL FUSE AT `0 ≤ C_p`, AT THE LINEAR LADDER -/

/-- `S12ConstCompose.ftl_one_le_log_of_three_le`, re-proved (the landed lemma is `private`).
Ladder-BLIND. -/
private lemma ftl_one_le_log_of_three_le {Xd : ℕ} (h : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at this
  linarith

/-- `S12ConstCompose.doorFuseFrame_pool'_of_gates_const_pos_gk` at the linear ladder: the
`ε`-pool slot is paid by the THRESHOLD (`eps_pool_const_pos`) rather than by `ε ≤ 0`, which
is what lets the fuse run at a positive absorption exponent. -/
theorem doorFuseFrame_pool'_of_gates_const_pos_L_gk (K : ℕ) {M Xd j Hhi : ℕ}
    {Cs Ccc ε ρ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ constPool ρ Hhi)
    (hg : GRowsZeroGate'''_L_gk K M Xd Ccc (constPool ρ Hhi))
    (hρ : 0 < ρ)
    (hthr : 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
      ≤ (theta293 - ε) * Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hband4096 : (4096 : ℝ)
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 500) * constPool ρ Hhi) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs Ccc ε (constPool ρ Hhi) where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'''_L_gk K hM hXd hg
  eps_pool := eps_pool_const_pos (ftl_one_le_log_of_three_le hb.X_three) hρ hthr
  band_pool := band_pool_of_threshold
    (by have := ftl_one_le_log_of_three_le hb.X_three; linarith) hband4096

set_option maxHeartbeats 1000000 in
/-- `S12ConstCompose.m4_closure_fuse_zero'_const_nonneg_gk` at the linear ladder — the
constant-pool fuse the flat capstone fires, with `0 ≤ C_p` and the absorption exponent free. -/
theorem m4_closure_fuse_zero'_const_nonneg_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
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
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPool_L_gk K hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)

/-! ## §2 — THE ROAD AT THE FLAT ROOT, AT THE LINEAR LADDER

`HloExportMRFlatRoot`'s §1 (`m4_exit_socket_split_sq_arc_flatRoot`) is DOOR-FREE and is
reused verbatim; only §GK-2 and §GK-3 move. -/

/-- `HloExportMRFlatRoot.m4_doorL2_close_split_sq_gk_flatRoot` at the linear ladder. -/
theorem m4_doorL2_close_split_sq_gk_flatRoot_L (K : ℕ) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      Hcap ≤ max (flatDesignFloor A)
        (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          R.Hlo ≤ max Hcap U1floor ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq_L_gk K R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, A, β, Hcap, Hopq, hε, hKb, hδ₀, hεpin, hδpin, hβ, hA26, hA₀A,
    hAge, hCapLe, hexit⟩ := m4_exit_socket_split_sq_arc_flatRoot A₀ hA₀
  refine ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **⟦THE FLAT ROAD'S TERMINAL REGISTER, AT THE LINEAR LADDER⟧**
(`m4_second_road_L2_gk_flatRoot_L`) — `HloExportMRFlatRoot.m4_second_road_L2_gk_flatRoot`
with the ladder read at `AdoorL M = 2^36·M`.  This is the surface the linear flat compose
reads. -/
theorem m4_second_road_L2_gk_flatRoot_L (K : ℕ) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ A β : ℝ) (Hcap Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
            M4ChiSummedFreeRow_L_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hmain⟩ := m4_doorL2_close_split_sq_gk_flatRoot_L K A₀ hA₀
  refine ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
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
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
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

/-! ## §3 — THE CAPSTONE AT THE FLAT ROOT, AT THE LINEAR LADDER (HOP 3) -/

/-- `S11HoistGrade.s11_grade_absorption'` transported to the LINEAR row floor: the linear
floor is LARGER (`doorRowFloor M ≤ doorRowFloorL M`) and the grade exponent
`s13Aexp − 1/2 + 1/1000 = 2.501` is positive, so the landed absorption implies the linear
one.  ⟦THE TRANSPORT DIRECTION⟧ consumption transports UP: a stronger right side. -/
theorem s11_grade_absorption'_L (Cb : ℝ) (M : ℕ) (hM : s11GradeFloor Cb ≤ M) (C' : ℝ)
    (hC' : C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ)) :
    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hM1 : 1 ≤ M := le_trans (s11GradeFloor_one_le Cb) hM
  have hbase := s11_grade_absorption' Cb M hM C' hC'
  have hle : ((doorRowFloor M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    exact_mod_cast doorRowFloor_le_doorRowFloorL hM1
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Real.log 2 * ((doorRowFloor M : ℕ) : ℝ)
      ≤ Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hle hl2.le
  have hnn : (0 : ℝ) ≤ Real.log 2 * ((doorRowFloor M : ℕ) : ℝ) := by positivity
  have hexp : (0 : ℝ) ≤ s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000) := by
    rw [s13Aexp]; norm_num
  exact le_trans hbase (Real.rpow_le_rpow hnn hmul hexp)

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 3: the ~120-line residue re-elaborates against the re-cut
-- prefix, which here gains three items and five conjuncts.
/-- **⟦HOP 3, AT THE FLAT ROOT AND THE LINEAR LADDER⟧**
(`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L`) —
`S16FlatTerminal.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot` with its road
`obtain` re-pointed at §2's `m4_second_road_L2_gk_flatRoot_L` and every door read moved to
`AdoorL M = 2^36·M`.  The `G`-slot is unchanged.  The five constants `Cq cs T₀ Kq Ks` are the
LANDED ones (`m4_fuse_hcap_of_capWS_gk` is spent for its constants only; its payload is
discarded here exactly as in the landed HOP 3). -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBoundedL K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloorL M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    GRowsZeroGate'''_L_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
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
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hroad⟩ := m4_second_road_L2_gk_flatRoot_L K A₀ hA₀
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk K hK
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀,
    max Hcap (max arcFloor36 loglogFloor50),
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40,
    hβ, hA26, hA₀A, hAge, flatCap_join_floor hCapLe, ?_⟩
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
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
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
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
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

/-! ## §4 — THE HOP-4 SUPPLIERS AT THE LINEAR LADDER -/

/-- `M4AssemblyFrames.frames_logX_ge` at the linear frame — the arm alone, `anchor`-free. -/
theorem frames_logX_ge_L {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) : (10 : ℝ) ^ 10 ≤ Real.log X := by
  have hmu : (356600 : ℝ) ≤ Real.log (Real.log X) := hfr.loglogX_ge
  have hL1 : (1 : ℝ) < Real.log X := hfr.one_lt_logX
  have hstep : Real.exp (356600 : ℝ) ≤ Real.log X := by
    have := Real.exp_le_exp.mpr hmu
    rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log X)] at this
  have hq : (356600 : ℝ) ^ 2 / 4 ≤ Real.exp (356600 : ℝ) :=
    frames_quarter_sq_le_exp (by norm_num)
  have : (10 : ℝ) ^ 10 ≤ (356600 : ℝ) ^ 2 / 4 := by norm_num
  linarith

/-- `M4AssemblyFrames.doorBaseFrame_at_socket` at the linear socket and frame.  The landed
body reads NO `anchor` field — only the arm, the `H`-floor, the `ρ`-charge and the window
index — so it replays verbatim at `DoorArithFrameRho_L`. -/
theorem doorBaseFrame_at_socket_L {R : ChowlaRegime} {M H L q j A s : ℕ} {C₁ M₀ K ρ : ℝ}
    (hb : SocketBaseL R M H L q j A s)
    (hfr : DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) C₁ M₀ K ρ) :
    DoorBaseFrame (A + s) j := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hAs : 0 < A + s := by omega
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hLX : (10 : ℝ) ^ 10 ≤ Real.log (((A + s : ℕ)) : ℝ) := frames_logX_ge_L hfr
  have hLXn : (10000000000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    le_trans (by norm_num) hLX
  have hLX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the `H`-side scales⟧
  have hH1 : (1 : ℝ) < Real.log (H : ℝ) := hfr.one_lt_logH
  have hH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases lt_or_ge 0 (H : ℝ) with h | h
    · exact h
    · exfalso
      have hz : (H : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg H)
      rw [hz, Real.log_zero] at hH1; linarith
  have hlam : (50 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := hfr.Hfloor
  have hlr : (0 : ℝ) ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  -- ⟦the window index⟧
  have hjR : (1078 : ℝ) ≤ (j : ℝ) := by have := hfr.jfloor; linarith
  have hjN : 1078 ≤ j := by exact_mod_cast hjR
  have hLne : L ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at hjL
    omega
  have h2jH : 2 ^ j ≤ H :=
    le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 hLne)) hLH
  have h2jHR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2jH
  have h2jpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  -- ⟦the ARM, at its weakest reading: `log X_d ≥ e·log H`⟧
  have hstep : Real.log (Real.log (H : ℝ)) + 1 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have := hfr.armWeak; linarith
  have hEH : Real.log (H : ℝ) * Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hstep
    rwa [Real.exp_add, Real.exp_log hH0, Real.exp_log hLX0] at h1
  have hHX : 2.7 * Real.log (H : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have he27 : (2.7 : ℝ) < Real.exp 1 := exp_one_gt_27
    nlinarith [hEH, he27, hH0]
  have hllX : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 := by
    have := Real.add_one_le_exp (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
    rw [Real.exp_log hLX0] at this; linarith
  -- ⟦the shared lower bound on the annulus height `2·X_d/2^j`⟧
  have hXH : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      = (((A + s : ℕ)) : ℝ) / (H : ℝ) := by
    rw [Real.exp_sub, Real.exp_log hX0, Real.exp_log hHpos]
  have hdiv : (((A + s : ℕ)) : ℝ) / (H : ℝ)
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    have hd : (((A + s : ℕ)) : ℝ) / (H : ℝ)
        ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by gcongr
    have hpos : (0 : ℝ) ≤ (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by positivity
    linarith
  have hann : Real.exp (Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ))
      ≤ 2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by rw [hXH]; exact hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ⟦`X_exp`⟧
    have h := Real.exp_le_exp.mpr (by linarith : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    rwa [Real.exp_log hX0] at h
  · -- ⟦`X_three`⟧
    have h := frames_base_ge hAs hLX
    have h3 : (3 : ℝ) ≤ 1 + (10 : ℝ) ^ 10 := by norm_num
    linarith
  · -- ⟦`h_four`⟧
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hR : ((2 ^ 2 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h4
    simpa using hR
  · -- ⟦`h_window`⟧
    have hprod : (((A + s : ℕ)) : ℝ) * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-(1 / 5 : ℝ))
        = Real.exp (Real.log (((A + s : ℕ)) : ℝ)
            + Real.log (Real.log (((A + s : ℕ)) : ℝ)) * (-(1 / 5 : ℝ))) := by
      rw [Real.rpow_def_of_pos hLX0, Real.exp_add, Real.exp_log hX0]
    rw [hprod]
    calc ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := h2jHR
      _ = Real.exp (Real.log (H : ℝ)) := (Real.exp_log hHpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · -- ⟦`tann`⟧
    rw [TannGate]
    have hsq : Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by
      have hnn : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) / 60 := by positivity
      have hle : Real.log (((A + s : ℕ)) : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2 := by
        nlinarith [hLXn, hLX0]
      calc Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
          ≤ Real.sqrt ((Real.log (((A + s : ℕ)) : ℝ) / 60) ^ 2) := Real.sqrt_le_sqrt hle
        _ = Real.log (((A + s : ℕ)) : ℝ) / 60 := Real.sqrt_sq hnn
    rw [← Real.sqrt_eq_rpow]
    refine le_trans (Real.exp_le_exp.mpr ?_) hann
    linarith
  · -- ⟦`ceil5`⟧
    have he5 : Real.exp 5 ≤ 1000 := by
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hh : Real.exp 5 = (Real.exp 1) ^ (5 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      rw [hh]
      have hc : (Real.exp 1) ^ (5 : ℕ) ≤ (2.7182818286 : ℝ) ^ (5 : ℕ) :=
        pow_le_pow_left₀ hpos.le he.le 5
      have hn : (2.7182818286 : ℝ) ^ (5 : ℕ) ≤ 1000 := by norm_num
      linarith
    have hlog : Real.exp 5
        ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
      have h1 : Real.log (((A + s : ℕ)) : ℝ) - Real.log (H : ℝ)
          ≤ Real.log (2 * ((((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
        have h2 := Real.log_le_log (Real.exp_pos _) hann
        rwa [Real.log_exp] at h2
      linarith
    have := Real.log_le_log (Real.exp_pos 5) hlog
    rwa [Real.log_exp] at this

/-- **⟦THE BLOCK-SCALE FLOOR AT A SYMBOLIC EXPONENT⟧** — `S15Compose.s15_block_at_socket_gk`
reads the door only through the SYMBOL `s13BlockExp_gk K M`.  Stated at an arbitrary exponent
`E` it covers both cuts; the linear instance is `E := s13BlockExp_L_gk K M`. -/
theorem s15_block_at_socket_gen {R : ChowlaRegime} {M H L q j A s E : ℕ}
    (hb : SocketBase R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((E : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    2 ^ E ≤ A + s := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith [hHreg.2]
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hxs : ((4 ^ m : ℕ) : ℝ) ^ 2 ≤ 2 * arcDen 12 H * (A : ℝ) := s13_socketBase_xscale hb
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlhs0 : (0 : ℝ) < ((4 ^ m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hlhs0 hxs
  have hLid : Real.log (((4 ^ m : ℕ) : ℝ) ^ 2) = 4 * (m : ℝ) * Real.log 2 := by
    have h4 : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
    rw [h4, ← pow_mul, Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hRR : Real.log (2 * arcDen 12 H * (A : ℝ))
      = Real.log 2 + 12 * Real.log (Real.log (H : ℝ)) + Real.log (A : ℝ) := by
    rw [harcpow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hLid, hRR] at hlog
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hE : ((E : ℕ) : ℝ) * Real.log 2 ≤ Real.log (A : ℝ) := by
    nlinarith [hblk, hlog, hllH, hll0, hl2lo, hl2hi]
  have hpow : ((2 : ℝ)) ^ E ≤ (A : ℝ) := by
    have hlt : Real.log (((2 : ℝ)) ^ E) ≤ Real.log (A : ℝ) := by
      rw [Real.log_pow]; linarith
    exact (Real.log_le_log_iff (by positivity) hApos).mp hlt
  have hcast : ((2 ^ E : ℕ) : ℝ) ≤ (A : ℝ) := by push_cast; exact hpow
  have hnat : (2 : ℕ) ^ E ≤ A := by exact_mod_cast hcast
  omega

/-- `s15_block_at_socket_gk` at the LINEAR block exponent. -/
theorem s15_block_at_socket_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s)
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hblk : ((s13BlockExp_L_gk K M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    s13BlockFloor_L_gk K M ≤ A + s := by
  rw [s13BlockFloor_L_gk]
  exact s15_block_at_socket_gen hb hHreg hblk

/-- `S13BandBase.s13_band_baseFloor` at the LINEAR row floor. -/
theorem s13_band_baseFloor_L {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s) :
    Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hj : doorRowFloorL M ≤ j := hb.2.2.2.2.2.2.1
  have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  have hpow : (2 : ℕ) ^ doorRowFloorL M ≤ A + s := by
    have : (2 : ℕ) ^ doorRowFloorL M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hR : ((2 : ℝ)) ^ (doorRowFloorL M) ≤ (((A + s : ℕ)) : ℝ) := by
    have h : ((2 ^ doorRowFloorL M : ℕ) : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast hpow
    simpa using h
  have h0 : (0 : ℝ) < ((2 : ℝ)) ^ (doorRowFloorL M) := by positivity
  have := Real.log_le_log h0 hR
  rwa [Real.log_pow, mul_comm] at this

/-- **⟦THE BAND GATE AT THE LINEAR LADDER⟧** (`S13BandGate'_L_gk`) — `S13BandBase.
S13BandGate'_gk` with `x0_le`/`grade` at the LINEAR row floor and `block` at the LINEAR
block floor. -/
structure S13BandGate'_L_gk (K : ℕ) (R : ChowlaRegime) (M x₀ : ℕ) (C' : ℝ) (C₁ : ℕ → ℝ) :
    Prop where
  /-- ⟦1⟧ the opaque threshold at the LINEAR row floor. -/
  x0_le : x₀ ≤ 2 ^ doorRowFloorL M
  /-- ⟦2⟧ the band constant's normalisation. -/
  C1_one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n
  /-- ⟦3⟧ the grade fit at the LINEAR `M`-only floor. -/
  grade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- ⟦4⟧ ⟦F3⟧ the LINEAR block-scale floor at every socket base. -/
  block : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s

/-- `S15Compose.s15_bandGate''_of_grade_gk` at the linear ladder. -/
theorem s15_bandGate''_of_grade_L_gk (K : ℕ) {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime} {M : ℕ} {C' : ℝ} (hfl : loglogFloor50 ≤ R.Hlo)
    (hsel : S15Sel''_L_gk K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgrade : 8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
      ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))) :
    S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) where
  x0_le := hsel.x0M
  C1_one := fun _ => le_rfl
  grade := hgrade
  block := by
    intro H L q j A s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hsel.hM hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk

/-- `S13BandBase.doorBandBase_family'_gk` at the linear ladder. -/
theorem doorBandBase_family'_L_gk (K : ℕ) {R : ChowlaRegime} {M x₀ : ℕ} {C' Kar ρ : ℝ}
    {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC1hi : ∀ n : ℕ, C₁ n ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ R.Hhi ≤ (R.x : ℝ))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ)
    (hgate : S13BandGate'_L_gk K R M x₀ C' C₁) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hbL
  have hb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hbL
  have hfr := harith H L q j A s hbL
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hjfl : doorRowFloorL M ≤ j := hbL.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five_L_gk K hM (hgate.block H L q j A s hbL) hjfl
  have hreg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400 hM hb
      C₁_one := hgate.C1_one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · have hAj : 2 ^ j ≤ A := hbL.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloorL M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hgate.x0_le (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · refine s13_band_qfit hbL.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge_L_gk K hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one_L_gk K hM)
      (s13_band_log_calQK_two_ge_L_gk K hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · refine le_trans hgate.grade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor_L hbL) ?_
    rw [s13Aexp]; norm_num
  · exact s13_band_err_free hρ0 hρ1 (hgate.C1_one (A + s)) (hC1hi (A + s)) hHreg hg hb

/-- `S13FramesA.s13_doorGates_of_arm'_gk` at the linear ladder. -/
theorem s13_doorGates_of_arm'_L_gk (K : ℕ) {Cg δ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hMδ : 24 * Cg / δ ≤ (M : ℝ))
    (harm : s13GArm' δ R.Hhi R.ω ≤ R.x)
    (hblk : 4 * R.ω * s13BlockFloor_L_gk K M ≤ R.x) :
    M4DoorGates_L_gk K Cg R M (doorCount R.ω) δ := by
  have hω1 : 1 ≤ R.ω := by have := R.hω; omega
  have hcount : ((doorCount R.ω : ℕ) : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2 :=
    doorCount_le hω1
  have harm1 : 2 * R.ω * (R.Hhi + 2) ≤ R.x := by rw [s13GArm'] at harm; omega
  have harm2 : 8 * R.ω ≤ R.x := by rw [s13GArm'] at harm; omega
  refine ⟨hM, hδ, hMδ, s13_logOmega_ge R, ?_, hcount, ?_, ?_⟩
  · have h4 : 2 ^ (doorCount R.ω) ≤ 4 * R.ω :=
      two_pow_le_four_mul_of_count R.hω hcount
    have : 2 ^ (doorCount R.ω + 1) = 2 ^ (doorCount R.ω) * 2 := by rw [pow_succ]
    omega
  · intro H hlo hhi
    have hbig : 2 * (R.ω : ℝ) * ((H : ℝ) + 2) ≤ (R.x : ℝ) := by
      have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have h1 : ((2 * R.ω * (R.Hhi + 2) : ℕ) : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast harm1
      push_cast at h1
      nlinarith
    exact (doorCount_gates hω1 hbig).1
  · intro H hlo hhi i hik
    have hmid : s13BlockFloor_L_gk K M ≤ R.x / (4 * R.ω) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc s13BlockFloor_L_gk K M * (4 * R.ω) = 4 * R.ω * s13BlockFloor_L_gk K M := by ring
        _ ≤ R.x := hblk
    exact s13_sieveBlockGate_L_gk hM
      (le_trans hmid (doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)))

/-- `S13MSelect2.s13_doorGates_of_MSelect'_gk` at the linear ladder. -/
theorem s13_doorGates_of_MSelect'_L_gk (K : ℕ) {Cg δ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hS : MSelect'_L_gk K Cg δ Λ ρ R M)
    (harm : s13GArm' δ R.Hhi R.ω ≤ R.x) :
    M4DoorGates_L_gk K Cg R M (doorCount R.ω) δ :=
  s13_doorGates_of_arm'_L_gk K hM hδ hS.bfloor harm hS.blockCeil

/-! ## §5 — THE ROAD AT THE FLAT ROOT, PINNED, AT THE LINEAR LADDER (HOP 4) -/

/-- `S13FramesA.s13_g2_jfloor` at a SYMBOLIC row floor — the body reads `doorRowFloor M` only
as the right-hand symbol.  The linear instance is `F := doorRowFloorL M`. -/
theorem s13_g2_jfloor_gen {R : ChowlaRegime} {Λ F : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 4 * Real.log 263 + 48 * Λ ≤ F) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ F := by
  intro H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hmax : max 1 (arcDen 12 H) = arcDen 12 H := max_eq_right harc1
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hlogmul : Real.log (263 * arcDen 12 H) = Real.log 263 + Real.log (arcDen 12 H) :=
    Real.log_mul (by norm_num) (by linarith)
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  rw [hmax, hlogmul, hlogarc]
  linarith



/-- The level-1 `𝒬` read is `G`-BLIND: `calE A G 1 = A`, so the lever's `𝒬₁` and the plain
door's `𝒬₁` are the SAME natural number. -/
theorem calQK_L_one_gk_eq (K M : ℕ) :
    calQK (AdoorL M) (s13GK K M) M 1 = calQK (AdoorL M) (3072 * M) M 1 := by
  rw [calQK, calE_one, calQK, calE_one]

/-- `ArithPageLinear.gRowsZeroGate'''_L_of_budget` at the lever. -/
theorem gRowsZeroGate'''_L_gk_of_budget (K : ℕ) {M Xd Hhi : ℕ} {ρ : ℝ} (hM : 1 ≤ M)
    (hXd : 0 < Xd) (hρ : 0 < ρ)
    (hlvl : 26 + 14 * Real.log (Real.log (Hhi : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ)
    (hp2 : 27 + 14 * Real.log (Real.log (Hhi : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ)
    (hend : 26 + 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log ((Xd : ℕ) : ℝ)) :
    GRowsZeroGate'''_L_gk K M Xd 0 (constPool ρ Hhi) where
  level1 := s15_level1_L_of_budget hM hρ (by rwa [calQK_L_one_gk_eq] at hlvl)
  endpt := s15_endpt_at_constPool hXd hρ hend
  p2 := s15_p2_of_budget_gen hρ (calP_door_one_le_two_L_gk K hM) hp2
  dens := s15_dens_at_zero hρ.le

/-- `S15SelLinearWide.s15_gRows_const_at_socket_flat_doorL` at the lever — the flat
`gRows` consumer at the LINEAR ladder and the `G`-lever. -/
theorem s15_gRows_const_at_socket_flat_doorL_gk (K : ℕ) {R : ChowlaRegime}
    {M H L q j A s : ℕ} {ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBaseL R M H L q j A s) (hM : 1 ≤ M)
    (hρ0 : 0 < ρ) (_hρ1 : ρ ≤ 1)
    (htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2))
    (hrho : -Real.log ρ ≤ 100000000000000)
    (hlvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
        + (-Real.log ρ)
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    GRowsZeroGate'''_L_gk K M (A + s) 0 (constPool ρ R.Hhi) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le _hρ1
  have hQ0 : (0 : ℝ)
      ≤ Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) := by
    rw [calQK_L_one_gk_eq]; exact s15_loglogQ1_L_nonneg hM
  obtain ⟨-, hL50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have hp2 : 27 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ := by
    linarith [hlvl, hQ0, hL50, hlogρ]
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hAs : 0 < A + s := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hbb
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hllle : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ Real.log (((A + s : ℕ)) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hll := s12c_llX_ge hfl hbb
  have hcore := flat_lambda_core_17 hlam50
  have hendbud : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h1 : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
        ≤ 14 * Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := by linarith
    linarith [hcore, hll, hllle, hrho, h1]
  exact gRowsZeroGate'''_L_gk_of_budget K hM hAs hρ0 (by linarith) hp2 hendbud

/-- **⟦THE CROSSING BOUND AT THE LINEAR LADDER⟧** (`S15CrossingBound_L_gk`) —
`S15Compose.S15CrossingBound_gk` with the socket family, the door coefficient and the
`(𝒫, 𝒬, ℋ)` triple read at `AdoorL M = 2^36·M`. -/
def S15CrossingBound_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ 8 * (0 : ℝ) ^ 2
          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                \ seamBall (((A + s : ℕ)) : ℝ) 0)
              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                  (calP (AdoorL M) (s13GK K M))
                  (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                  (mrAlpha (1 / 12)) 2,
              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + (theta293 - 1 / 500)))

set_option maxHeartbeats 1000000 in
-- Same cause as the landed HOP 4: the residue re-elaborates against the prefix.
/-- **⟦HOP 4, AT THE FLAT ROOT AND THE LINEAR LADDER⟧**
(`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L`) —
`S16FlatTerminal.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot` on §3, with the
register `S15Sel''_L_gk` and the crossing bound `S15CrossingBound_L_gk` at the linear
ladder. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBoundedL K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
            S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀, Hcap, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A,
    hAge, hCapLe, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L K hK hband A₀ hA₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
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
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-! ## §5b — ⟦THE ARM CENSUS AND THE `Nat.ceil` OVERSHOOT⟧ ⟦added per REF-FLAT-SAT⟧

The pinned base `flatWitFloor ε β A Hopq` is a `max` over five arms.  At `A ≥ 162` and the
terminal's OWN exported pins (`1/500 ≤ ε ≤ 1/2`, `0 < β`, `budgetAFlat ε β ≤ A`), FOUR of
them collapse under `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊`: `arcFloor36 = 10^138`,
`loglogFloor50 = ⌈e^{e^{50}}⌉₊`, `4⌈1/ε⌉₊⁴ ≤ 2.5·10^{11}`, `flatBase A` and the HEIGHT-1
`budgetFloorFlat`.  So the base equals the design base as soon as the ONE remaining arm —
the road's Siegel-carrying `Hopq` — is inside it, and the terminal can price its width rider
against a KNOWN base.  The price is a factor `2`: `Nat.ceil` overshoots, so the base's
`loglog` is `≤ 3.2A + log 2`, NOT `≤ 3.2A`, and the road's width export `e^{λ₋/2}` therefore
lands at `2·e^{1.6A}` rather than at `e^{1.6A}`.  The register's `Λ` slot was widened to
match (`S15SelLinear`/`S15SelLinearWide`/`FlatFloorBump`, `898× → 449×`). -/

/-- `log 10 ≤ 3`. -/
private theorem flat_log_ten_le_three : Real.log 10 ≤ 3 := by
  have he : Real.exp 3 = (Real.exp 1) ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h10 : (10 : ℝ) ≤ Real.exp 3 := by rw [he]; nlinarith [h1, sq_nonneg (Real.exp 1)]
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 10) h10
  rwa [Real.log_exp] at this

private theorem flat_expA_ge_519 {A : ℝ} (hA : 162 ≤ A) : (519 : ℝ) ≤ Real.exp (3.2 * A) := by
  have := Real.add_one_le_exp (3.2 * A); linarith

private theorem flat_ten138_le : (10 : ℝ) ^ (138 : ℕ) ≤ Real.exp 414 := by
  have hl : Real.log ((10 : ℝ) ^ (138 : ℕ)) = 138 * Real.log 10 := by rw [Real.log_pow]; norm_num
  have h := Real.exp_le_exp.mpr
    (show Real.log ((10 : ℝ) ^ (138 : ℕ)) ≤ 414 by rw [hl]; linarith [flat_log_ten_le_three])
  rwa [Real.exp_log (by positivity)] at h

/-- ⟦ARM 1⟧ `arcFloor36 = 10^138 ≤ flatDesignBase A` at `A ≥ 162` (102 orders of room). -/
theorem flat_arm_arcFloor_le {A : ℝ} (hA : 162 ≤ A) : arcFloor36 ≤ flatDesignBase A := by
  have hlit : ((arcFloor36 : ℕ) : ℝ) = (10 : ℝ) ^ (138 : ℕ) := by
    rw [arcFloor36, Nat.cast_pow, Nat.cast_ofNat]
  have hR : ((arcFloor36 : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
    rw [hlit]
    exact le_trans flat_ten138_le (Real.exp_le_exp.mpr (by linarith [flat_expA_ge_519 hA]))
  have := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
  rw [flatDesignBase]; exact_mod_cast this

/-- ⟦ARM 2⟧ `loglogFloor50 ≤ flatDesignBase A` — `50 < 3.2·162 = 518.4`. -/
theorem flat_arm_loglogFloor_le {A : ℝ} (hA : 162 ≤ A) : loglogFloor50 ≤ flatDesignBase A := by
  rw [loglogFloor50, flatDesignBase]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))

theorem flat_designBase_ge_4e6 {A : ℝ} (hA : 162 ≤ A) : 4000000 ≤ flatDesignBase A :=
  le_trans (by norm_num [arcFloor36]) (flat_arm_arcFloor_le hA)

/-- ⟦ARM 3⟧ `flatBase A = ⌈e^{200·c + 10000}⌉₊ ≤ flatDesignBase A` at `A ≥ 162`. -/
theorem flat_arm_flatBase_le {A : ℝ} (hA : 162 ≤ A) : flatBase A ≤ flatDesignBase A := by
  rw [flatBase, flatDesignBase]
  refine Nat.ceil_le_ceil (Real.exp_le_exp.mpr ?_)
  have hApos : (0 : ℝ) < 2 * A := by linarith
  have hlA : Real.log (2 * A) ≤ 2 * A - 1 := Real.log_le_sub_one_of_pos hApos
  have hu : (0 : ℝ) ≤ A - 162 := by linarith
  have hsplit : Real.exp (3.2 * A) = Real.exp 518.4 * Real.exp (3.2 * (A - 162)) := by
    rw [← Real.exp_add]; ring_nf
  have hlin : (1 : ℝ) + 3.2 * (A - 162) ≤ Real.exp (3.2 * (A - 162)) := by
    have := Real.add_one_le_exp (3.2 * (A - 162)); linarith
  have hE2 : (100000 : ℝ) ≤ Real.exp 518.4 := by
    have he : Real.exp 12 = (Real.exp 1) ^ (12 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h12 : (100000 : ℝ) ≤ Real.exp 12 := by
      rw [he]
      calc (100000 : ℝ) ≤ (2.7 : ℝ) ^ (12 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (12 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 12
    exact le_trans h12 (Real.exp_le_exp.mpr (by norm_num))
  rw [flatC, hsplit]
  nlinarith [hlA, hlin, hu, hE2, Real.exp_pos (3.2 * (A - 162))]

/-- `flatDesignFloor A = flatDesignBase A` at `A ≥ 162`. -/
theorem flat_designFloor_eq_designBase {A : ℝ} (hA : 162 ≤ A) :
    flatDesignFloor A = flatDesignBase A := by
  rw [flatDesignFloor]
  have h1 := flat_designBase_ge_4e6 hA
  have h2 := flat_arm_flatBase_le hA
  omega

/-- ⟦ARM 4⟧ `4·⌈1/ε⌉₊⁴ ≤ flatDesignBase A` from the exported pin `1/500 ≤ ε`. -/
theorem flat_arm_eps_le {A : ℝ} {ε : ℚ} (hA : 162 ≤ A) (hε : 0 < ε) (hεpin : 1 / 500 ≤ ε) :
    4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ flatDesignBase A := by
  have hceil : ⌈(1 / ε : ℚ)⌉₊ ≤ 500 := by
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hε]
    push_cast
    nlinarith [hεpin, hε]
  have h1 : 4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ 4 * 500 ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hceil 4)
  exact le_trans h1 (le_trans (by norm_num [arcFloor36] : 4 * 500 ^ 4 ≤ arcFloor36)
    (flat_arm_arcFloor_le hA))

/-- ⟦ARM 5⟧ `budgetFloorFlat ε β A ≤ flatDesignBase A`, from the terminal's OWN exported
budget conjunct `budgetAFlat ε β ≤ A` plus `1/500 ≤ ε ≤ 1/2`.  The flat budget floor is
HEIGHT 1 (`⌈e^{max(4X, 2 log A + 2)}⌉₊`), so it is invisible against the design base. -/
theorem flat_arm_budget_le {A β : ℝ} {ε : ℚ} (hA : 162 ≤ A) (hβ : 0 < β)
    (hε : (1 : ℝ) / 500 ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2)
    (hbudA : budgetAFlat (ε : ℝ) β ≤ A) :
    budgetFloorFlat (ε : ℝ) β A ≤ flatDesignBase A := by
  set e : ℝ := (ε : ℝ) with hedef
  have hepos : (0 : ℝ) < e := by rw [hedef]; linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hden : (0 : ℝ) < e ^ 6 * β ^ 2 := by positivity
  have hbud' : 2304 * Real.log 4 ≤ A * (e ^ 6 * β ^ 2) := by
    rw [budgetAFlat, div_le_iff₀ hden] at hbudA
    linarith [hbudA]
  have he6 : e ^ 6 ≤ 1 / 64 := by
    have h := pow_le_pow_left₀ hepos.le hε2 6
    norm_num at h; linarith
  have hbsq : (1 : ℝ) / β ^ 2 ≤ A / 204352 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hbud', he6, hl2lo, hlog4, sq_nonneg β, hβ, pow_pos hepos 6]
  have hb1 : (1 : ℝ) / β ≤ 1 + A / 204352 := by
    have ht : (1 : ℝ) / β ≤ 1 + 1 / β ^ 2 := by
      have h : (1 : ℝ) / β ^ 2 = (1 / β) ^ 2 := by field_simp
      nlinarith [sq_nonneg (1 / β - 1), h]
    linarith [hbsq]
  have he6lo : (1 : ℝ) / 15625000000000000 ≤ e ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 500) hε 6
    norm_num at h; linarith
  have hepow : (1 : ℝ) / e ^ 6 ≤ 15625000000000000 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [he6lo]
  have hS : (1 : ℝ) / β ^ 2 + 1 / β + 1 ≤ A := by
    have : A / 204352 + (1 + A / 204352) + 1 ≤ A := by linarith
    linarith [hbsq, hb1]
  have hSpos : (0 : ℝ) ≤ 1 / β ^ 2 + 1 / β + 1 := by positivity
  have hT : (1 : ℝ) / e ^ 6 + 1 ≤ 15625000000000001 := by linarith
  have hTpos : (0 : ℝ) ≤ 1 / e ^ 6 + 1 := by positivity
  have hApos : (0 : ℝ) < A := by linarith
  have hbX : budgetXFlat e β ≤ 10 ^ 21 * A := by
    rw [budgetXFlat, budgetX]
    have hprod : (1 / β ^ 2 + 1 / β + 1) * (1 / e ^ 6 + 1) ≤ A * 15625000000000001 :=
      mul_le_mul hS hT hTpos hApos.le
    nlinarith [hprod, hl2hi, hlog4, hApos]
  have hexp : 10 ^ 21 * A * 4 ≤ Real.exp (3.2 * A) := by
    have hu : (0 : ℝ) ≤ A - 162 := by linarith
    have hsplit : Real.exp (3.2 * A) = Real.exp 518.4 * Real.exp (3.2 * (A - 162)) := by
      rw [← Real.exp_add]; ring_nf
    have hlin : (1 : ℝ) + 3.2 * (A - 162) ≤ Real.exp (3.2 * (A - 162)) := by
      have := Real.add_one_le_exp (3.2 * (A - 162)); linarith
    have hE : (10 : ℝ) ^ 25 ≤ Real.exp 518.4 := by
      have he60 : Real.exp 60 = (Real.exp 1) ^ (60 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h60 : (10 : ℝ) ^ 25 ≤ Real.exp 60 := by
        rw [he60]
        calc (10 : ℝ) ^ 25 ≤ (2.7 : ℝ) ^ (60 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (60 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 60
      exact le_trans h60 (Real.exp_le_exp.mpr (by norm_num))
    rw [hsplit]
    nlinarith [hE, hlin, hu, Real.exp_pos (3.2 * (A - 162))]
  have hmax : max (4 * budgetXFlat e β) (2 * Real.log A + 2) ≤ Real.exp (3.2 * A) := by
    refine max_le ?_ ?_
    · nlinarith [hbX, hexp]
    · have hlA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos hApos
      have : (2 : ℝ) * A ≤ Real.exp (3.2 * A) := by
        nlinarith [Real.add_one_le_exp (3.2 * A)]
      linarith
  rw [budgetFloorFlat, flatDesignBase]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr hmax)

set_option exponentiation.threshold 4000 in
/-- ⟦ARM 4 AT SHIFT `h`⟧ (`flat_arm_eps_le_h`) — `flat_arm_eps_le` from the `h` lane's pin
`1/(500·h) ≤ ε`.  `⌈1/ε⌉₊ ≤ 500·h`, so the arm is `4·(500·1096)^4 = 3.61·10^23` against
`arcFloor36 = 10^138` — 114 orders. -/
theorem flat_arm_eps_le_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {A : ℝ} {ε : ℚ}
    (hA : 162 ≤ A) (hε : 0 < ε) (hεpin : 1 / (500 * (h : ℚ)) ≤ ε) :
    4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ flatDesignBase A := by
  have hq0 : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have h1096 : h ≤ 1096 := Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have hceil : ⌈(1 / ε : ℚ)⌉₊ ≤ 500 * h := by
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hε]
    have hq : (1 : ℚ) / (500 * (h : ℚ)) ≤ ε := hεpin
    rw [div_le_iff₀ (by positivity)] at hq
    push_cast
    nlinarith [hq, hq0, hε]
  have hb : 500 * h ≤ 548000 := by omega
  have h1 : 4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4 ≤ 4 * 548000 ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_trans hceil hb) 4)
  exact le_trans h1 (le_trans (by norm_num [arcFloor36] : 4 * 548000 ^ 4 ≤ arcFloor36)
    (flat_arm_arcFloor_le hA))

set_option exponentiation.threshold 4000 in
/-- ⟦ARM 5 AT SHIFT `h`⟧ (`flat_arm_budget_le_h`) — `flat_arm_budget_le` from `1/(500·h) ≤ ε`.
The `ε^6` arms gain `h^6`: `1.5625·10^16 → 2.71·10^34` at `h ≤ 1096`, and the budget bound
`10^21·A → 4·10^39·A`.  ⭐ **The `hE` digit moves `10^25 → 10^43`, and `10^42` would NOT do**
— at `A = 162` the demand is `2.59·10^42`.  `10^43 ≤ 2.7^100 ≤ exp 100 ≤ exp 518.4`
(`log₁₀(2.7^100) = 43.136`, margin 1.37×).  The UPPER pin `ε ≤ 1/2` is untouched, so `he6` and
`hbsq` are the landed proof verbatim. -/
theorem flat_arm_budget_le_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {A β : ℝ} {ε : ℚ}
    (hA : 162 ≤ A) (hβ : 0 < β)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2)
    (hbudA : budgetAFlat (ε : ℝ) β ≤ A) :
    budgetFloorFlat (ε : ℝ) β A ≤ flatDesignBase A := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hx1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have h1096 : (h : ℝ) ≤ 1096 := by
    exact_mod_cast Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have h6b : (h : ℝ) ^ 6 ≤ (1096 : ℝ) ^ 6 := pow_le_pow_left₀ hx0.le h1096 6
  set e : ℝ := (ε : ℝ) with hedef
  have hepos : (0 : ℝ) < e := by
    rw [hedef]; exact lt_of_lt_of_le (by positivity) hε
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hden : (0 : ℝ) < e ^ 6 * β ^ 2 := by positivity
  have hbud' : 2304 * Real.log 4 ≤ A * (e ^ 6 * β ^ 2) := by
    rw [budgetAFlat, div_le_iff₀ hden] at hbudA
    linarith [hbudA]
  have he6 : e ^ 6 ≤ 1 / 64 := by
    have hp := pow_le_pow_left₀ hepos.le hε2 6
    norm_num at hp; linarith
  have hbsq : (1 : ℝ) / β ^ 2 ≤ A / 204352 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hbud', he6, hl2lo, hlog4, sq_nonneg β, hβ, pow_pos hepos 6]
  have hb1 : (1 : ℝ) / β ≤ 1 + A / 204352 := by
    have ht : (1 : ℝ) / β ≤ 1 + 1 / β ^ 2 := by
      have hq : (1 : ℝ) / β ^ 2 = (1 / β) ^ 2 := by field_simp
      nlinarith [sq_nonneg (1 / β - 1), hq]
    linarith [hbsq]
  -- ⟦THE ONE AXIS THAT MOVES⟧ the LOWER pin, and it moves by `h^6`
  have he6lo : (1 : ℝ) / (15625000000000000 * (h : ℝ) ^ 6) ≤ e ^ 6 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (500 * (h : ℝ))) hε 6
    have hid : ((1 : ℝ) / (500 * (h : ℝ))) ^ 6 = 1 / (15625000000000000 * (h : ℝ) ^ 6) := by
      field_simp; ring
    rw [hid] at hp; exact hp
  have hepow : (1 : ℝ) / e ^ 6 ≤ 27100000000000000000000000000000000 := by
    rw [div_le_iff₀ (by positivity)]
    have hstep : (1 : ℝ) ≤ 15625000000000000 * (h : ℝ) ^ 6 * e ^ 6 := by
      have hpos : (0 : ℝ) < 15625000000000000 * (h : ℝ) ^ 6 := by positivity
      have := mul_le_mul_of_nonneg_left he6lo hpos.le
      calc (1 : ℝ) = 15625000000000000 * (h : ℝ) ^ 6 * (1 / (15625000000000000 * (h : ℝ) ^ 6)) := by
            field_simp
        _ ≤ 15625000000000000 * (h : ℝ) ^ 6 * e ^ 6 := this
    have hnum : (15625000000000000 : ℝ) * (1096 : ℝ) ^ 6
        ≤ 27100000000000000000000000000000000 := by norm_num
    nlinarith [hstep, h6b, hnum, pow_pos hepos 6, hx1]
  have hS : (1 : ℝ) / β ^ 2 + 1 / β + 1 ≤ A := by
    have : A / 204352 + (1 + A / 204352) + 1 ≤ A := by linarith
    linarith [hbsq, hb1]
  have hSpos : (0 : ℝ) ≤ 1 / β ^ 2 + 1 / β + 1 := by positivity
  have hT : (1 : ℝ) / e ^ 6 + 1 ≤ 27100000000000000000000000000000001 := by linarith
  have hTpos : (0 : ℝ) ≤ 1 / e ^ 6 + 1 := by positivity
  have hApos : (0 : ℝ) < A := by linarith
  have hbX : budgetXFlat e β ≤ 4 * 10 ^ 39 * A := by
    rw [budgetXFlat, budgetX]
    have hprod : (1 / β ^ 2 + 1 / β + 1) * (1 / e ^ 6 + 1)
        ≤ A * 27100000000000000000000000000000001 :=
      mul_le_mul hS hT hTpos hApos.le
    nlinarith [hprod, hl2hi, hlog4, hApos]
  have hexp : 4 * 10 ^ 39 * A * 4 ≤ Real.exp (3.2 * A) := by
    have hu : (0 : ℝ) ≤ A - 162 := by linarith
    have hsplit : Real.exp (3.2 * A) = Real.exp 518.4 * Real.exp (3.2 * (A - 162)) := by
      rw [← Real.exp_add]; ring_nf
    have hlin : (1 : ℝ) + 3.2 * (A - 162) ≤ Real.exp (3.2 * (A - 162)) := by
      have := Real.add_one_le_exp (3.2 * (A - 162)); linarith
    have hE : (10 : ℝ) ^ 43 ≤ Real.exp 518.4 := by
      have he100 : Real.exp 100 = (Real.exp 1) ^ (100 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h100 : (10 : ℝ) ^ 43 ≤ Real.exp 100 := by
        rw [he100]
        calc (10 : ℝ) ^ 43 ≤ (2.7 : ℝ) ^ (100 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (100 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 100
      exact le_trans h100 (Real.exp_le_exp.mpr (by norm_num))
    rw [hsplit]
    nlinarith [hE, hlin, hu, Real.exp_pos (3.2 * (A - 162))]
  have hmax : max (4 * budgetXFlat e β) (2 * Real.log A + 2) ≤ Real.exp (3.2 * A) := by
    refine max_le ?_ ?_
    · nlinarith [hbX, hexp]
    · have hlA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos hApos
      have : (2 : ℝ) * A ≤ Real.exp (3.2 * A) := by
        nlinarith [Real.add_one_le_exp (3.2 * A)]
      linarith
  rw [budgetFloorFlat, flatDesignBase]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.mpr hmax)

/-- **⟦gate 7 AT THE INFLATED CAP, IN REGIME FORM⟧** (`arc36_of_regime_h`) — wave H2a word 5.
The exit's `harc3` (`S16FlatTerminalExitH:107`) demands `128·(h·arcDen 12 H)^3 ≤ H`, and the
landed `arcFloor36` route clears `h = 1` by only **1.14×**, so it FAILS from `h = 2`.  Routed off
`loglogFloor50 = ⌈e^{e^50}⌉₊` instead: that gives `H ≥ e^{e^50}`, against a demand of `10^157`.
**The room is a tower, not a factor** — which is why this is the floor the `h` lane must read. -/
theorem arc36_of_regime_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) {R : ChowlaRegime}
    (hfloor : loglogFloor50 ≤ R.Hlo) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have h1096 : (h : ℝ) ≤ 1096 := by
    exact_mod_cast Salt.Entropy.Chowla.h_le_1096_of_log_le_seven hh hh7
  have hcb : (h : ℝ) ^ 3 ≤ 1316532736 := by
    calc (h : ℝ) ^ 3 ≤ (1096 : ℝ) ^ 3 := pow_le_pow_left₀ hx0.le h1096 3
      _ = 1316532736 := by norm_num
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hfl : (10 : ℕ) ^ 157 ≤ loglogFloor50 := by
    have he3 : (10 : ℝ) ≤ Real.exp 3 := by
      have h3 : Real.exp 3 = (Real.exp 1) ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hp : (2.7 : ℝ) ^ (3 : ℕ) ≤ (Real.exp 1) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he1.le 3
      rw [h3]; nlinarith [hp]
    have he157 : (Real.exp 3) ^ (157 : ℕ) = Real.exp 471 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpow : ((10 : ℝ)) ^ (157 : ℕ) ≤ Real.exp 471 := by
      have hle : ((10 : ℝ)) ^ (157 : ℕ) ≤ (Real.exp 3) ^ (157 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he3 157
      rw [← he157]; exact hle
    have h471 : (471 : ℝ) ≤ Real.exp 50 := by
      have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      have hp : (2.7 : ℝ) ^ (50 : ℕ) ≤ (Real.exp 1) ^ (50 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he1.le 50
      have hn : (471 : ℝ) ≤ (2.7 : ℝ) ^ (50 : ℕ) := by norm_num
      rw [h50]; linarith
    have hmono : Real.exp 471 ≤ Real.exp (Real.exp 50) := Real.exp_le_exp.mpr h471
    have hceil : Real.exp (Real.exp 50) ≤ ((loglogFloor50 : ℕ) : ℝ) := by
      rw [loglogFloor50]; exact Nat.le_ceil _
    have hfin : ((10 : ℝ)) ^ (157 : ℕ) ≤ ((loglogFloor50 : ℕ) : ℝ) := by linarith
    exact_mod_cast hfin
  intro H hlo _
  exact arc36_of_floor_h hcb (le_trans hfl (le_trans hfloor hlo))

/-- **⟦THE `j₀` CORNER AT SHIFT `h`⟧** (`s13_g2_jfloor_of_MSelect'_L_gk_h`) — wave H2a word 6,
the OUTER step taking the `h`-free `∀H` family to the `h`-bearing one, exactly as the H2b/H2c
commission pins it (its §1 word 2 slot 3; the H2a draft had the composition inverted).  This is
the QUEUE's "unpriced `4·log h`" corner, priced: `4·log h ≤ 28` under `hh7`.

⚠️ **ONE DEVIATION FROM THE PINNED SHAPE, AND IT IS A SOUNDNESS REPAIR, NOT A CONVENIENCE.** The
pin states the hypothesis as `4·log(263·max 1 (arcDen 12 H)) ≤ F`; from that alone the
conclusion is **not derivable**, because `4·log(263·h·A) = 4·log(263·A) + 4·log h` and nothing
in the hypothesis supplies the `4·log h`.  The `28` is therefore carried where it must live —
in the hypothesis.  The consumer supplies it from `s13_g2_jfloor_gen` with its gate at
`4·log 263 + 48·Λ + 28 ≤ F`, which is the same one numeral, and the slack the pin itself names
(`F = doorRowFloorL M = 2^36·M²` against `4·log 263 + 48·Λ`) pays it many times over.
`F` is left generic; `F := ((doorRowFloorL M : ℕ) : ℝ)` is the pinned instance. -/
theorem s13_g2_jfloor_of_MSelect'_L_gk_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {R : ChowlaRegime} {F : ℝ}
    (h1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) + 28 ≤ F) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H)) ≤ F := by
  intro H hlo hhi
  have hx0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hmax : (1 : ℝ) ≤ max 1 (arcDen 12 H) := le_max_left _ _
  have hsplit : Real.log (263 * (h : ℝ) * max 1 (arcDen 12 H))
      = Real.log (263 * max 1 (arcDen 12 H)) + Real.log (h : ℝ) := by
    rw [show (263 : ℝ) * (h : ℝ) * max 1 (arcDen 12 H)
        = (263 * max 1 (arcDen 12 H)) * (h : ℝ) by ring,
      Real.log_mul (by positivity) (ne_of_gt hx0)]
  rw [hsplit]
  linarith [h1 H hlo hhi, hh7]

/-- **⟦THE ARM CENSUS AT SHIFT `h`⟧** (`flat_witFloor_eq_designBase_h`) —
`flat_witFloor_eq_designBase` on the two `h`-scaled arms.  The other three arms
(`flat_arm_arcFloor_le`, `flat_arm_loglogFloor_le`, `flat_designFloor_eq_designBase`) are
`ε`-free and `δ₀`-free, so they are the landed ones verbatim: **the shift touches exactly the
two arms that read the `ε` pin, and no others.** -/
theorem flat_witFloor_eq_designBase_h {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {A β : ℝ} {ε : ℚ} {Hopq : ℕ} (hA : 162 ≤ A) (hβ : 0 < β)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2) (hεq : 0 < ε)
    (hεqpin : 1 / (500 * (h : ℚ)) ≤ ε) (hbudA : budgetAFlat (ε : ℝ) β ≤ A)
    (hopq : Hopq ≤ flatDesignBase A) :
    flatWitFloor ε β A Hopq = flatDesignBase A := by
  have hbud := flat_arm_budget_le_h hh hh7 hA hβ hε hε2 hbudA
  have hepsarm := flat_arm_eps_le_h hh hh7 hA hεq hεqpin
  have harc := flat_arm_arcFloor_le hA
  have hll := flat_arm_loglogFloor_le hA
  have hdf := flat_designFloor_eq_designBase hA
  rw [flatWitFloor, hdf]
  omega

/-- **⟦THE ARM CENSUS, ASSEMBLED⟧** ⟦added per REF-FLAT-SAT⟧ — at `A ≥ 162` and the terminal's
own exported pins, the pinned base collapses to `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊` as soon
as the ONE opaque arm `Hopq` is inside it.  `Hopq` is the road's
`max (max H₀red H₀D3) H₀xi`, whose `H₀red`/`H₀D3` carry the SIEGEL-INEFFECTIVE `K_Chen`
(`⌈e^{64·K_Chen}⌉+1`, FORMALLY UNBOUNDED at `S16Budget:887`).  So `Hopq ≤ flatDesignBase A`
is the honest surviving form of the old width rider: one Siegel ask, the same genre as the
`x₀` window. -/
theorem flat_witFloor_eq_designBase {A β : ℝ} {ε : ℚ} {Hopq : ℕ} (hA : 162 ≤ A) (hβ : 0 < β)
    (hε : (1 : ℝ) / 500 ≤ (ε : ℝ)) (hε2 : (ε : ℝ) ≤ 1 / 2) (hεq : 0 < ε)
    (hεqpin : 1 / 500 ≤ ε) (hbudA : budgetAFlat (ε : ℝ) β ≤ A)
    (hopq : Hopq ≤ flatDesignBase A) :
    flatWitFloor ε β A Hopq = flatDesignBase A := by
  have hbud := flat_arm_budget_le hA hβ hε hε2 hbudA
  have hepsarm := flat_arm_eps_le hA hεq hεqpin
  have harc := flat_arm_arcFloor_le hA
  have hll := flat_arm_loglogFloor_le hA
  have hdf := flat_designFloor_eq_designBase hA
  rw [flatWitFloor, hdf]
  omega

/-- **⟦THE CEILING OVERSHOOT⟧** ⟦added per REF-FLAT-SAT⟧ — the pinned base's `loglog` is
`3.2·A` PLUS the `Nat.ceil` overshoot, which is bounded by `log 2` and NOT provably zero.
It is therefore NOT `≤ 3.2·A`, and every consumer that wanted the base AT its design law
must pay the resulting factor. -/
theorem flatDesignBase_loglog_le {A : ℝ} (hA : 162 ≤ A) :
    Real.log (Real.log ((flatDesignBase A : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
  have hceil : ((flatDesignBase A : ℕ) : ℝ) ≤ 2 * Real.exp (Real.exp (3.2 * A)) := by
    rw [flatDesignBase]
    have h1 : ((⌈Real.exp (Real.exp (3.2 * A))⌉₊ : ℕ) : ℝ)
        ≤ Real.exp (Real.exp (3.2 * A)) + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    have h2 : (1 : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by
      have := Real.add_one_le_exp (Real.exp (3.2 * A)); linarith [Real.exp_pos (3.2 * A)]
    linarith
  have hge : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hlogge : Real.exp (3.2 * A) ≤ Real.log ((flatDesignBase A : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hge
    rwa [Real.log_exp] at this
  have hE1 : (1 : ℝ) ≤ Real.exp (3.2 * A) := by
    have := Real.add_one_le_exp (3.2 * A); linarith
  have hposlog : (0 : ℝ) < Real.log ((flatDesignBase A : ℕ) : ℝ) := by linarith
  have hDpos : (0 : ℝ) < ((flatDesignBase A : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) hge
  have hlog : Real.log ((flatDesignBase A : ℕ) : ℝ) ≤ Real.log 2 + Real.exp (3.2 * A) := by
    have h := Real.log_le_log hDpos hceil
    rwa [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  calc Real.log (Real.log ((flatDesignBase A : ℕ) : ℝ))
      ≤ Real.log (2 * Real.exp (3.2 * A)) := by
        refine Real.log_le_log hposlog ?_
        linarith
    _ = 3.2 * A + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]; ring

/-- **⟦THE WIDTH RIDER, PRICED AT THE PINNED BASE⟧** ⟦added per REF-FLAT-SAT⟧ — the road's
own width certificate plus the arm census give the register's `Λ` line ONLY up to `2×`: the
literal ceiling `e^{3.2A/2}` is NOT reached, because the base's `loglog` carries the
`Nat.ceil` overshoot.  This is why the register's slot was widened. -/
theorem flat_L_width_priced {A : ℝ} {R : ChowlaRegime} (hA : 162 ≤ A)
    (hbase : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2)
    (hdes : 3.2 * A ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)))
    (htow : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) :
    Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) := by
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith
  have h := htow h50
  have hmono : Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)
      ≤ Real.exp ((3.2 * A + Real.log 2) / 2) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp ((3.2 * A + Real.log 2) / 2)
      = Real.exp (3.2 * A / 2) * Real.exp (Real.log 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hhalf : Real.exp (Real.log 2 / 2) ≤ 2 := by
    have h1 : Real.log 2 / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
  have hpos : (0 : ℝ) < Real.exp (3.2 * A / 2) := Real.exp_pos _
  calc Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) := h
    _ ≤ Real.exp ((3.2 * A + Real.log 2) / 2) := hmono
    _ = Real.exp (3.2 * A / 2) * Real.exp (Real.log 2 / 2) := hsplit
    _ ≤ Real.exp (3.2 * A / 2) * 2 := by nlinarith [hhalf, hpos]
    _ = 2 * Real.exp (3.2 * A / 2) := by ring

/-! ## §6 — ⟦THE FLAT TERMINAL AT THE LINEAR LADDER, WITH THE REGISTER SUPPLIED⟧ -/

/-- `flatWitFloor_design` read as the register's `hlo` line: the pinned base clears
`e^{3.2A}` in `log`, which is EXACTLY what `s15_sel''_L_gk_witness_flat_bumped` asks. -/
theorem flatWitFloor_log_ge {ε : ℚ} {β A : ℝ} {Hopq : ℕ} (hA : 162 ≤ A) :
    Real.exp (3.2 * A) ≤ Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ) := by
  have hdes := flatWitFloor_design ε β A Hopq
  have h0 : (0 : ℝ) ≤ Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ) :=
    log_natCast_nonneg' _
  have hy : (1 : ℝ) < Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge h0 (by norm_num : (0 : ℝ) < 50) (by linarith)
  have h := Real.exp_le_exp.mpr hdes
  rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ))] at h

set_option maxHeartbeats 1000000 in
/-- **⟦THE FLAT TERMINAL AT THE LINEAR LADDER⟧** (`logChowla2_witnessed_scale_flat_L`) —
`S16FlatTerminal.logChowla2_witnessed_scale_flat` re-fired at `AdoorL M = 2^36·M`, with the
`S15` register **SUPPLIED, NOT CARRIED**.

⟦WHAT LEFT THE DEBT LIST, REMOVED-BECAUSE-PROVEN⟧

* **`S15Sel''_gk 32000000 …` — THE REGISTER — IS GONE.**  On the landed ladder it is
  unsatisfiable at the flat design point (⟦COMPOSE-FLAT-2⟧'s `flat_landed_ladder_break`).
  Here the whole chain reads the LINEAR ladder, and
  `FlatFloorBump.s15_sel''_L_gk_witness_flat_bumped` produces `S15Sel''_L_gk` at the flat
  design modulus `M = flatDoorM A = ⌊e^{1.6A}/310301⌋`, whose two `M`-floor demands
  ⟦LADDER-L G4⟧ kernelized (`A ≥ 162`).
* the register's `hlo` line — `e^{3.2A} ≤ log H₋` — is discharged by `flatWitFloor_log_ge`:
  the base is pinned at the road's OWN cap, whose design law IS that inequality.
* `heps` — `1/2^9 ≤ ε` — is `1/500 ≤ ε` (`1/512 < 1/500`), already in the prefix.
* `hKle` — `32000000 ≤ 1.7·10⁸·flatDoorM A` — is the door's own wide `K`-ceiling.

⟦THE COMPLETE SURVIVING HYPOTHESIS LIST⟧  the theorem's own arguments are
`hband : S16BandLaneCBoundedL 32000000` (the band-lane `C`, at the linear ladder) and the
design floor `A₀ ≥ 162`.  The inner implication asks for, in order:

1. `Kc ≤ 2^539` — ⟦REPAIRS-LANE⟧'s wide socket ceiling.  ⟦amended per REF-FLAT-HONEST⟧ true
   at the CLOSED FORM `ConstantsExposed.KExpr` (`12·10^161 = 2^538.42`); the chain's own `Kc`
   is `bigXi_bounded`'s opaque `∃ C, 0 < C ∧ …`, which exports POSITIVITY ONLY — the
   identification with the closed form is prose, not kernel;
2. `Ct ≤ 2^23` — the wide constant-pool ceiling.  ⟦amended per REF-FLAT-HONEST⟧ true at the
   closed form `6·e^{14} = 2^{22.78}` (`s16_audit_Ct_ceiling`); the chain's own `Ct` is
   `m4_hrowsSlot_at_door_zero'_L_gk`'s opaque `∃ Ct, 0 < Ct` — again positivity only;
3. `(x₀ : ℝ) ≤ e^{e^{3.2A}/10}` — ⟦THE `x0` WINDOW⟧, the register's second-tightest line
   (⟦LINEAR-PAGE⟧ measured `1.24×` of margin at the design point): a REAL design constraint
   on the opaque Siegel threshold, carried.  `x₀` too is an opaque `∃` of the band lane;
4. `Hopq ≤ flatDesignBase A` — ⟦THE SIEGEL-HONEST SURVIVING FORM OF THE OLD WIDTH DEMAND⟧.
   ⟦amended per REF-FLAT-HONEST + REF-FLAT-SAT⟧ the earlier rider `loglog H₊ ≤ e^{1.6A}` was
   UN-DISCHARGEABLE from this theorem's own exports (the proof obtained the road's width
   certificate and discarded it) and, once restored, was still short by the `Nat.ceil`
   overshoot of the pinned base.  Both are repaired: the width certificate is now EXPORTED,
   the register's `Λ` slot was widened to `2·e^{1.6A}` (`898× → 449×` on the four
   `Λ`-spending lines), and §5b's ARM CENSUS shows every closed-form arm of `flatWitFloor`
   sits under `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊`.  What remains is exactly ONE arm:
   `Hopq` (`HloExportFlat`: `max (max H₀red H₀D3) H₀xi`, whose `H₀red = H₀D3 = max (96^8)
   (⌈e^{64·K_Chen}⌉+1)` carries the SIEGEL-INEFFECTIVE `K_Chen`, recorded FORMALLY UNBOUNDED
   at `S16Budget:887`).  So this rider is a quantitative bound on a Siegel-ineffective
   constant — the SAME GENRE as rider 3's `x₀` window, not a free lunch — and the width
   demand itself is now REMOVED-BECAUSE-PROVEN (exported as a fact, conjunct 6 below);
5. `S15CrossingBound_L_gk 32000000 R (flatDoorM A)` — the crossing bound at the linear
   ladder, CARRIED.  Its landed supplier `S16Budget.s15_crossing_supplied_wide_gk` spends
   `cs`/`T₀`/`Kq`/`Ks`, ⟦RULING 9⟧'s cofactor debt and the base-scale cap through the
   `S13CapGrid`/`S13FramesB` cap lane, which this wave does not re-cut.

⟦WHAT IS EXPORTED ABOUT THE DESIGN CONSTANT⟧ `0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat ε β ≤ A`
— `A` is SYMBOLIC, above the caller's `A₀`, and the head's own budget demand rides the
prefix.  Plus the ARM CENSUS itself: `Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq =
flatDesignBase A`, so a caller who discharges the Siegel arm KNOWS the base.

⟦THE REGIME'S EXPORTED CONJUNCT LIST⟧ ⟦amended per REF-FLAT-HONEST + REF-FLAT-SAT⟧
`R.eps = ε`, `R.Hlo = flatWitFloor ε β A Hopq`, `g R.Hhi R.ω ≤ R.x`, THE WIDTH CERTIFICATE
`50 ≤ loglog H₋ → loglog H₊ ≤ e^{loglog H₋/2}` (restored — the earlier cut destructured and
discarded it, and `ChowlaRegime` itself carries no upper bound on `Hhi` in terms of `Hlo`),
`3.2A ≤ loglog H₋` (redundant given conjunct 2 and `flatWitFloor_design`, kept as a
convenience), THE PRICED WIDTH `loglog H₊ ≤ 2·e^{1.6A}` (a FACT, not a demand), then the
inner implication — whose only surviving hypothesis is the crossing bound. -/
theorem logChowla2_witnessed_scale_flat_L (hband : S16BandLaneCBoundedL 32000000)
    (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
      -- amended per REF-FLAT-SAT: THE ARM CENSUS, exported
      (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
      (Kc ≤ 2 ^ 539 → Ct ≤ 2 ^ 23 →
        (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
        -- amended per REF-FLAT-SAT: the Siegel-honest surviving form of the width demand
        Hopq ≤ flatDesignBase A →
        ∀ g : ℕ → ℕ → ℕ, ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
          -- amended per REF-FLAT-HONEST: the road's WIDTH CERTIFICATE, restored to the
          -- export (it was destructured and discarded; §7 cannot compose without it)
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          -- amended per REF-FLAT-SAT: the width demand, REMOVED-BECAUSE-PROVEN at `2×`
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (S15CrossingBound_L_gk 32000000 R (flatDoorM A) →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, hbody⟩ :=
    logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L 32000000 (by norm_num) hband
      A₀ hA₀
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1` (the census needs `ε ≤ 1/2`)
  obtain ⟨R0, hR0eps, -, -, -, -⟩ :=
    hbody (flatWitFloor ε β A Hopq) (fun _ _ => 0) (flatCap_le_flatWitFloor hCapLe)
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεpin
    rw [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
    exact h
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge,
    fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hKb hCtb hx0win hopq g
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  -- ⟦THE WIDTH DEMAND, DISCHARGED⟧ arm census + the `Nat.ceil` overshoot + the road's law
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRtow, hdes, hwin, ?_⟩  -- amended per REF-FLAT-HONEST/SAT
  intro hcross
  -- ⟦THE REGISTER, SUPPLIED⟧ at the flat design modulus
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have hKle : (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
    calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
      _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped (c := 1) hA26 32000000 hKle (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKb
    hCt hCtb hCgle hMflb hx0win (by simpa using heps) hlo hwin
  exact hfire (flatDoorM A) hsel hcross

/-! ## §7 — THE INHABITATION AND NON-VACUITY CERTIFICATES AT THE FLAT LINEAR POINT -/

/-- **⟦THE WIDTH RIDER, PRICED — THE WIDTH-LAW ROUTE⟧** ⟦amended per REF-FLAT-HONEST⟧ — §6's
now-exported width certificate (`htow`, verbatim the shape §6 hands out) plus a base sitting
AT its design law give the register's `hhi` line.  What rider 4 of §6 asks along THIS route
is therefore a CEILING on `flatWitFloor`'s opaque arm — the road's `Hopq`, whose `H₀red`/
`H₀D3` are built from the SIEGEL-INEFFECTIVE `K_Chen` (`⌈e^{64·K_Chen}⌉+1`, recorded FORMALLY
UNBOUNDED at `S16Budget:887`).  So this IS an analytic ask, of the same genre as the `x₀`
window of rider 3: it says `K_Chen` is not astronomically large.  The route is also the
LOSSY one — it demands the base at its design law EXACTLY, and ⟦REF-FLAT-SAT⟧ showed that
demand is not met: `flatDesignBase A = ⌈e^{e^{3.2A}}⌉₊`'s `Nat.ceil` overshoots, so the
pinned base only satisfies `loglog H₋ ≤ 3.2A + log 2` (`flatDesignBase_loglog_le`), never
`≤ 3.2A`.  §6 therefore prices the rider through `flat_L_width_priced` (at `2×`) instead;
this lemma is kept as the statement of what the tight route would have needed, and
`flat_L_width_of_flat_arm` below prices the same rider off the flat tower's own
no-overshoot law with no equality demand at all. -/
theorem flat_L_width_of_base_at_design {A : ℝ} {R : ChowlaRegime} (hA : 162 ≤ A)
    (htow : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2))
    (hbase_lo : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hbase_hi : Real.log (Real.log (R.Hlo : ℝ)) ≤ 3.2 * A) :
    Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ Real.exp (3.2 * A / 2) := by
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by linarith
  have h := htow h50
  have hmono : Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ≤ Real.exp (3.2 * A / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  exact le_trans h hmono

/-- **⟦THE SHARP WIDTH BRICK, AT THE DESIGN POINT⟧** ⟦amended per REF-FLAT-HONEST⟧ —
`TowerFlat.towerFlat_width_le`'s no-overshoot law `(λ₊ + c) ≤ (21/20)·4^A·(λ₋ + c)` evaluated
at the design base `λ₋ = 3.2A` already sits under the rider's ceiling `e^{1.6A}`: the flat
arm's `4^A = e^{1.3863A}` loses to `e^{1.6A}` by the fixed exponent gap `0.2137·A`, which at
`A ≥ 162` swallows the linear factor `(21/20)(c + 3.2A) ≤ 5.46A`. -/
theorem flat_arm_width_sharp {A : ℝ} (hA : 162 ≤ A) :
    (21 / 20 : ℝ) * ((4 : ℝ) ^ A * (flatC A + 3.2 * A)) ≤ flatC A + Real.exp (3.2 * A / 2) := by
  obtain ⟨hC0, hCle⟩ := flatC_bracket (A := A) (by linarith)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : (4 : ℝ) ^ A = Real.exp (Real.log 4 * A) := Real.rpow_def_of_pos (by norm_num) _
  have h4le : (4 : ℝ) ^ A ≤ Real.exp (1.3863 * A) := by
    rw [h4]; exact Real.exp_le_exp.mpr (by nlinarith [hl4, hl2, hA])
  have hy : (7 : ℝ) ≤ 0.2137 * A / 2 := by linarith
  have hlin : 19 * (0.2137 * A / 2) ≤ Real.exp (0.2137 * A / 2) := flat_exp_ge_lin hy
  have hsq : Real.exp (0.2137 * A / 2) * Real.exp (0.2137 * A / 2) = Real.exp (0.2137 * A) := by
    rw [← Real.exp_add]; congr 1; ring
  have hgap : (21 / 20 : ℝ) * (flatC A + 3.2 * A) ≤ Real.exp (0.2137 * A) := by
    nlinarith [hlin, hCle, hA, hsq, (Real.exp_pos (0.2137 * A / 2)).le]
  have hsplit : Real.exp (1.3863 * A) * Real.exp (0.2137 * A) = Real.exp (3.2 * A / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : (0 : ℝ) ≤ flatC A + 3.2 * A := by linarith
  have hstep : (21 / 20 : ℝ) * ((4 : ℝ) ^ A * (flatC A + 3.2 * A))
      ≤ Real.exp (1.3863 * A) * Real.exp (0.2137 * A) := by
    have h1 : (4 : ℝ) ^ A * (flatC A + 3.2 * A) ≤ Real.exp (1.3863 * A) * (flatC A + 3.2 * A) :=
      mul_le_mul_of_nonneg_right h4le hpos
    nlinarith [hgap, (Real.exp_pos (1.3863 * A)).le, h1]
  rw [hsplit] at hstep; linarith

/-- **⟦THE SHARP WIDTH BRICK, WITH THE BASE FREE⟧** ⟦amended per REF-FLAT-HONEST⟧ — the same
no-overshoot law with NO equality demand on the base: any `λ₋` in `[0, e^{A/10}]` still lands
`(21/20)·4^A·(c + λ₋)` under `c + e^{1.6A}`.  At `A = 162` the ceiling `e^{16.2} ≈ 1.1·10^7`
is `20 000×` the design law's `3.2A = 518.4` (`flat_arm_tolerance_contains_design`), so the
design point sits strictly INSIDE the window rather than on its edge — this is what the
width-law route (`flat_L_width_of_base_at_design`, which demands `λ₋ = 3.2A` exactly) was
paying for and did not need to. -/
theorem flat_arm_width_sharp_tolerant {A lam : ℝ} (hA : 162 ≤ A) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ Real.exp (A / 10)) :
    (21 / 20 : ℝ) * ((4 : ℝ) ^ A * (flatC A + lam)) ≤ flatC A + Real.exp (3.2 * A / 2) := by
  obtain ⟨hC0, hCle⟩ := flatC_bracket (A := A) (by linarith)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : (4 : ℝ) ^ A = Real.exp (Real.log 4 * A) := Real.rpow_def_of_pos (by norm_num) _
  have h4le : (4 : ℝ) ^ A ≤ Real.exp (1.3863 * A) := by
    rw [h4]; exact Real.exp_le_exp.mpr (by nlinarith [hl4, hl2, hA])
  have h20 : (7 : ℝ) ≤ A / 20 := by linarith
  have hlin20 : 19 * (A / 20) ≤ Real.exp (A / 20) := flat_exp_ge_lin h20
  have hsq20 : Real.exp (A / 20) * Real.exp (A / 20) = Real.exp (A / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2A : 2 * A ≤ Real.exp (A / 10) := by
    have hnn : (0 : ℝ) ≤ 19 * (A / 20) := by linarith
    have hmm := mul_le_mul hlin20 hlin20 hnn (Real.exp_pos (A / 20)).le
    rw [hsq20] at hmm
    nlinarith [hmm, hA]
  have hsum : flatC A + lam ≤ 2 * Real.exp (A / 10) := by linarith
  have h1137 : (7 : ℝ) ≤ 0.1137 * A := by linarith
  have hlin1137 : 19 * (0.1137 * A) ≤ Real.exp (0.1137 * A) := flat_exp_ge_lin h1137
  have hc21 : (21 / 20 : ℝ) * 2 ≤ Real.exp (0.1137 * A) := by linarith
  have hE : (0 : ℝ) < Real.exp (1.3863 * A) := Real.exp_pos _
  have hE2 : (0 : ℝ) < Real.exp (A / 10) := Real.exp_pos _
  have hpos0 : (0 : ℝ) ≤ flatC A + lam := by linarith
  have hsplit : Real.exp (1.3863 * A) * (Real.exp (A / 10) * Real.exp (0.1137 * A))
      = Real.exp (3.2 * A / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hstep1 : (4 : ℝ) ^ A * (flatC A + lam)
      ≤ Real.exp (1.3863 * A) * (2 * Real.exp (A / 10)) :=
    le_trans (mul_le_mul_of_nonneg_right h4le hpos0) (mul_le_mul_of_nonneg_left hsum hE.le)
  have hmul := mul_le_mul_of_nonneg_left hc21 (mul_nonneg hE.le hE2.le)
  calc (21 / 20 : ℝ) * ((4 : ℝ) ^ A * (flatC A + lam))
      ≤ (21 / 20 : ℝ) * (Real.exp (1.3863 * A) * (2 * Real.exp (A / 10))) :=
        mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    _ = Real.exp (1.3863 * A) * Real.exp (A / 10) * ((21 / 20 : ℝ) * 2) := by ring
    _ ≤ Real.exp (1.3863 * A) * Real.exp (A / 10) * Real.exp (0.1137 * A) := hmul
    _ = Real.exp (1.3863 * A) * (Real.exp (A / 10) * Real.exp (0.1137 * A)) := by ring
    _ = Real.exp (3.2 * A / 2) := hsplit
    _ ≤ flatC A + Real.exp (3.2 * A / 2) := by linarith

/-- **⟦THE TOLERANCE CONTAINS THE DESIGN POINT⟧** ⟦amended per REF-FLAT-HONEST⟧ — `3.2A` is
below `e^{A/10}` at every `A ≥ 162`, so `flat_arm_width_sharp_tolerant` covers the pinned
base and a wide neighbourhood above it. -/
theorem flat_arm_tolerance_contains_design {A : ℝ} (hA : 162 ≤ A) :
    3.2 * A ≤ Real.exp (A / 10) := by
  have h20 : (7 : ℝ) ≤ A / 20 := by linarith
  have hlin20 : 19 * (A / 20) ≤ Real.exp (A / 20) := flat_exp_ge_lin h20
  have hsq20 : Real.exp (A / 20) * Real.exp (A / 20) = Real.exp (A / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnn : (0 : ℝ) ≤ 19 * (A / 20) := by linarith
  have hmm := mul_le_mul hlin20 hlin20 hnn (Real.exp_pos (A / 20)).le
  rw [hsq20] at hmm
  nlinarith [hmm, hA]

/-- **⟦THE WIDTH RIDER, PRICED — THE FLAT-ARM ROUTE⟧** ⟦amended per REF-FLAT-HONEST⟧ — rider 4
of §6 off the flat tower's OWN no-overshoot law (`towerFlat_width_le`'s conclusion, carried
here as `hwid`), with the base only required to lie in the tolerance window
`[0, e^{A/10}]` — no equality demand.  This is the brick §7 should have been priced on. -/
theorem flat_L_width_of_flat_arm {A : ℝ} {R : ChowlaRegime} (hA : 162 ≤ A)
    (hbase0 : 0 ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hbase : Real.log (Real.log (R.Hlo : ℝ)) ≤ Real.exp (A / 10))
    (hwid : flatC A + Real.log (Real.log (R.Hhi : ℝ))
      ≤ (21 / 20 : ℝ) * ((4 : ℝ) ^ A * (flatC A + Real.log (Real.log (R.Hlo : ℝ))))) :
    Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ Real.exp (3.2 * A / 2) := by
  have h := flat_arm_width_sharp_tolerant hA hbase0 hbase
  linarith

/-- **⟦THE BASE IS ABOVE EVERY REGISTER FLOOR⟧** — the pinned flat base clears the `50`-floor
the whole `S13`/`S15` layer reads, by `3.2·162 = 518.4`.  Non-vacuity of the pin, in one
line. -/
theorem flatWitFloor_loglog_ge_fifty {ε : ℚ} {β A : ℝ} {Hopq : ℕ} (hA : 162 ≤ A) :
    (50 : ℝ) ≤ Real.log (Real.log ((flatWitFloor ε β A Hopq : ℕ) : ℝ)) := by
  have := flatWitFloor_design ε β A Hopq
  linarith

/-- **⟦THE FLAT DESIGN MODULUS IS A GENUINE MODULUS AT THE BUMPED FLOOR⟧** — `flatDoorM A ≥ 1`
at `A ≥ 162`, so the door's parameter is real and the wide `K`-ceiling `1.7·10⁸·flatDoorM A`
sits above the pinned `K = 3.2·10⁷`. -/
theorem flatDoorM_pos_at_162 {A : ℝ} (hA : 162 ≤ A) :
    1 ≤ flatDoorM A ∧ (32000000 : ℕ) ≤ 170000000 * flatDoorM A := by
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA)
  refine ⟨hM1, ?_⟩
  calc (32000000 : ℕ) ≤ 170000000 * 1 := by norm_num
    _ ≤ 170000000 * flatDoorM A := Nat.mul_le_mul_left _ hM1

/-- **⟦THE INHABITATION AT THE FLAT LINEAR POINT⟧** — a flat regime EXISTS at the terminal's
pinned base, at any design constant above the bumped floor.  `S16FlatTerminal.
flatWitFloor_regime_exists` at `A ≥ 162`. -/
theorem flat_L_regime_exists {ε : ℚ} (heps : 0 < ε) (heps1 : ε ≤ 1 / 2) (β A : ℝ)
    (hA : 162 ≤ A) (Hopq : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = ε ∧ R.A = A ∧ flatWitFloor ε β A Hopq ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) :=
  flatWitFloor_regime_exists heps heps1 β A (flat162_ge_26 hA) Hopq g

/-- **⟦THE JOINT POINT AT THE BUMPED FLOOR⟧** — ⟦COMPOSE-FLAT-2⟧'s seven simultaneous
conjuncts (the flat floor, the Fannes ceiling, the width law's own demand, the linear
`anchor`/`gRows` pair, the `half` window and the height-1 budget floor) hold at every
`A ≥ 162`, since they hold uniformly at `A ≥ 26`.  So the design floor the two `M`-bumps
force costs the joint point nothing. -/
theorem flat_linear_joint_point_at_162 {A : ℝ} (hA : 162 ≤ A) :
    26 ≤ A := flat162_ge_26 hA

/-! ## §8 — THE CROSSING LANE'S FIRST HOP AT THE LINEAR LADDER

The crossing bound `S15CrossingBound_L_gk` is CARRIED by §6.  Its landed supplier
`S16Budget.s15_crossing_supplied_wide_gk` is a two-stage object: the WIRE
(`S12FuseCompose.m4_fuse_hcap_of_capWS_gk`, which turns a per-block cap family into the
crossing integral) and the CAP GATE (`s16_capGate_supply_wide_gk` →
`S13FramesB.doorCapBundle_at_workingPoint_perBlock_gk` → the `S13CapGrid`/`S13CapFloor`/
`S13CapRbd` lane).  The WIRE is re-cut here — ⟦LADDER-L G3⟧ already landed
`M4CapWireLinear.m4_hcap_at_door_perBlock_L_gk` and `M4RowLinear.G2Scaffold.m4_capE_at_door_
L_gk`, so the hop costs one `obtain`.  THE CAP GATE IS THE NAMED RESIDUE: `S13CapGatePerBlock_L_gk`,
`s13CapGrid_all_L_gk` and `doorCapBundle_at_workingPoint_perBlock_L_gk` do not exist, and
that lane (~4.6k landed lines) is where `cs`/`T₀`/`Kq`/`Ks`, ⟦RULING 9⟧'s cofactor debt and
the base-scale cap are spent.

⚠ ⟦ONE HONEST CAVEAT⟧ the wire's `E`-discharge reads `M4RowLinear.G2Scaffold`, the NAMESPACED
restatement ⟦LADDER-L G2⟧ marked deletable-once-its-lane-lands.  `m4_fuse_hcap_of_capWS_L_gk`
is the only declaration on this page that touches it; when that lane lands, the two names
(`DoorCapErrWS_L_gk`, `m4_capE_at_door_L_gk`) move to `Salt.MR` and the prefix drops. -/

set_option maxHeartbeats 1000000 in
/-- `S12FuseCompose.m4_fuse_hcap_of_capWS_gk` at the linear ladder. -/
theorem m4_fuse_hcap_of_capWS_L_gk (K : ℕ) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door_perBlock_L_gk K
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro R M cU ε hc1 hcapWS
  refine hwire R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK` ceiling binders on the `L`-chain: the ceiling moves
INSIDE the internal `∀ M` as `≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_closure_fuse_zero'_const_nonneg_L_gk_kwide`) —
`m4_closure_fuse_zero'_const_nonneg_L_gk`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem m4_closure_fuse_zero'_const_nonneg_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (Kc ρ : ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → 0 < ρ → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
            ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          GRowsZeroGate'''_L_gk K M (A + s) Cp (constPool ρ R.Hhi)) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266 + (-Real.log ρ)
            ≤ (theta293 - ε (A + s)) * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293) ≤ constPool ρ R.Hhi) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
            * constPool ρ R.Hhi) →
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
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kc ρ) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk_kwide K
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε Kc ρ cU bU t₁ hM hKw hρ hb1 hc1 hbf hgP1 hgRows hthr _heps293
    hband4096 hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk K (Cs := fun _ => Ct)
    (Ccc := fun _ => Cp) (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := fun _ => constPool ρ R.Hhi)
    (RSbig := fun _ H => RSanDoorRho ρ H) hM ?_
    (hslot Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband
    (fun _ => constPool_nonneg hρ.le) (m4_arith_henv_constPool_L_gk K hρ.le harith)
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_const_pos_L_gk K (hbf H L q j A s hb)
    (hgP1 H L q j A s hb) (hgRows H L q j A s hb) hρ (hthr H L q j A s hb) hM hXd
    (hband4096 H L q j A s hb)


/-- ⟦WIDE CEILING TWIN⟧ (`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L_kwide`) —
`logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L_kwide (K : ℕ)
    (hband : S16BandLaneCBoundedL K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
                    4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                  (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                    m4SmallGradeFits (doorRowFloorL M)
                      (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                      (fun H => 2 * rStrWitness H) H) →
                  -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    GRowsZeroGate'''_L_gk K M (A + s) Cp
                      (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                        + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                      ≤ (theta293 - epsrf (A + s))
                          * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                      ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                      * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                  -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                      Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                          ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                      ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                  -- ⟦B4 RAW⟧ the crossing bound, carried
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                      5 ≤ Real.log (Real.log (2 * T)) →
                      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
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
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                    DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKc, hδ₀, hεpin, hδpin, hβ,
    hA26, hA₀A, hAge, hCapLe, hroad⟩ := m4_second_road_L2_gk_flatRoot_L K A₀ hA₀
  obtain ⟨Ct, hCt, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_kwide K
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, -⟩ := m4_fuse_hcap_of_capWS_gk K
  obtain ⟨x₀, Cband, hCband0, hCband40, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀,
    max Hcap (max arcFloor36 loglogFloor50),
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, s11_grade_floor_hoistCb_prod_le Cband hCband0 hCband40,
    hβ, hA26, hA₀A, hAge, flatCap_join_floor hCapLe, ?_⟩
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
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
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
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
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


/-- ⟦WIDE CEILING TWIN⟧ (`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L_kwide`) —
`logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L`
with the flat ceiling moved inside the `∀ M` as `K ≤ 170000000 * M`.
Statement and proof otherwise verbatim, off the `_kwide` upstream. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L_kwide (K : ℕ)
    (hband : S16BandLaneCBoundedL K) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (x₀ Hcap Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ budgetAFlat (ε : ℝ) β ≤ A ∧
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
            K ≤ 170000000 * M →
            S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, A, β, x₀, Hcap, Hopq, Mfl, hCg, hε, hKc,
    hδ₀, hCt, hCq, hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A,
    hAge, hCapLe, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L_kwide K hband A₀ hA₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hcap, Hopq, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, hβ, hA26, hA₀A, hAge, hCapLe, ?_⟩
  intro U1floor g hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω)
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRtow, ?_⟩
  intro M hsel hKw
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
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

end Salt.MR

end
