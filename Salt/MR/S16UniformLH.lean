/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalExitH
import Salt.MR.S16Uniform
import Salt.MR.S16ComposeV4
import Salt.Entropy.Chowla.HloExportFlatH

/-!
# THE UNIFORM LANE AT SHIFT `h` — wave H3, blocks U and W

⟦WHAT THIS FILE SETTLES⟧  Two things the `h` lane needs before its uniform capstones can be
ported, and nothing else.

**BLOCK U — the `A`-uniform road.**  `S16FlatTerminalExitH`'s exit is `A₀`-pinned because the
head it calls is.  `HloExportFlatH.flat_head_uniform_h` removed that pin with one `intro`; §1
here re-brackets the exit onto it.  ⭐ **At `h` this is ONE theorem, not three:** at `h = 1` the
lane needs `flat_socket_uniform` and `flat_doorL2_uniform` between the head and the road, but the
`h` door-form register `m4_second_road_L2_H_gk_flatRoot_L` (S16FlatTerminalLinearH:1588) **has no
`A` in its statement at all**, so the two intermediate hoists have nothing to hoist.

**BLOCK W — the windowed band rider at the inflated socket.**  §2.  This is the row where wave
H2b's price cut does NOT repeat, and the reason is worth stating: `S16BandLaneCBoundedL` has **no
producer anywhere**, so H2b re-quantified it for free; the WINDOWED riders
`S16BandLaneCBoundedL_win`/`_winU` are **theorems** (`s16_bandLaneWinL_holds`,
`s16_bandLaneWinL_holdsU`), so their `h` twins need a producer PORT.
⭐ **The port is class A, and a projection census says why.**  The mint
`S11HoistLinear.m4_hband_at_door_slot_split_graded_L_gk` touches its socket in exactly two ways —
it projects **conjunct 4** (`0 < q`, which `SocketBaseLH` does not move) and passes `hb` straight
to its own antecedent.  Across `S11HoistLinear`'s 59 socket occurrences there are **zero**
projections of conjunct 5 and **zero** of conjunct 11, the only two `SocketBaseLH h` relaxes.  So
every proof body below is the landed one **verbatim**: only the statements are re-quantified.

⛔ **NEITHER RIDER GAINS OR LOSES CONDITIONALITY HERE.**  The windowed rider is discharged at `h`
exactly as at `h = 1`, at the same `Awin := max 162 ((log Cband + 20)/0.64)`, and the `ε`/`δ₀`
pins ride out at `1/(500·h)` and `1/(838400·h²)` unchanged.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — BLOCK U: THE `A`-UNIFORM ROAD AT SHIFT `h` -/

/-- `S16FlatTerminalExitH.flatRootCapH_arc`, re-proved (the landed lemma is `private`). -/
private lemma flatRootCapH_arc_u (d p b c f : ℕ) :
    max (max d (max (max p b) c)) f ≤ max d (max (max (max p f) b) c) := by
  omega

set_option maxHeartbeats 1000000 in
-- Same cause as the landed exit: the road's own hypothesis list re-elaborates, here under a
-- prefix that has lost `A` and gained a `∀`.
/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER AT SHIFT `h`, `A`-UNIFORM⟧**
(`m4_second_road_L2_H_gk_flatRoot_L_exit_uniform`) — `S16FlatTerminalExitH:87` with the caller's
`A₀` replaced by a `∀ A` inside the `∃`-prefix, off `flat_head_uniform_h`.

⭐ **`Hopq` LEAVES THE `∀ A` AND `Hcap` STAYS INSIDE** — the same split the `h = 1` lane makes,
and for the same reason: `Hopq = max (max H₀red H₀D3) H₀xi` is `A`-free, while the cap is the
design floor at `A`.  H2a word 1(d)'s `Kb ≤ 2^539` rides out unchanged. -/
theorem m4_second_road_L2_H_gk_flatRoot_L_exit_uniform (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / (500 * (h : ℚ)) ≤ ε ∧
      1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
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
  obtain ⟨Cg, hCg, hCgle, hreg⟩ := m4_second_road_L2_H_gk_flatRoot_L h hh K
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    flat_head_uniform_h h hh hh7
  obtain ⟨H₀, hH₀⟩ := hreg ε hε
  refine ⟨Cg, ε, Kb, δ₀, β, max Hopq H₀, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact flatRootCapH_arc_u _ _ _ _ _, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hRextra, hRU1, hRg, hcount, hRtow, hRcap, hR⟩ := hhd H₀ U1floor g
  refine ⟨R, hReps, hRU1, hRg, hRtow, le_trans hRcap (by omega), ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have hdoor := hH₀ R hReps hRextra δ Bceil Kb RS RSan RStr Braw M k j₀ hgates hM hRSan0
    hRStr0 hBraw0 han hG1 hG2 harc3 hdgate hdrift hceil hcount hKb.le hrow
  exact hR δ₀ hδ₀ le_rfl (mrtUniformityXiL2H_mono hdoor hbudget)

/-! ## §2 — BLOCK W: THE WINDOWED BAND RIDER AT THE INFLATED SOCKET -/

/-- **⟦THE WINDOWED BAND RIDER, AT THE INFLATED SOCKET⟧** (`S16BandLaneCBoundedLH_win`) —
`S16Uniform.S16BandLaneCBoundedL_win` with both socket quantifiers at `SocketBaseLH h`. -/
def S16BandLaneCBoundedLH_win (h : ℕ) (Awin : ℝ) (K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 0.64 * Awin - 20 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-- **⟦THE WINDOWED BAND RIDER, WITNESS-UNIFORM, AT THE INFLATED SOCKET⟧**
(`S16BandLaneCBoundedLH_winU`) — `S16ComposeV4.S16BandLaneCBoundedL_winU` likewise. -/
def S16BandLaneCBoundedLH_winU (h : ℕ) (Awin : ℝ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 0.64 * Awin - 20 ∧ ∀ (K M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-- ⭐ **THE `h = 1` TWIN LAWS** — the anti-drift gate for both defs.  Both socket occurrences
sit in HYPOTHESIS position, so a drifted def would still elaborate at every consumer and no
build could see it; these are the only instruments that look. -/
theorem s16BandLaneCBoundedLH_win_one_iff (Awin : ℝ) (K : ℕ) :
    S16BandLaneCBoundedLH_win 1 Awin K ↔ S16BandLaneCBoundedL_win Awin K := by
  unfold S16BandLaneCBoundedLH_win S16BandLaneCBoundedL_win
  simp only [socketBaseLH_one_iff]

theorem s16BandLaneCBoundedLH_winU_one_iff (Awin : ℝ) :
    S16BandLaneCBoundedLH_winU 1 Awin ↔ S16BandLaneCBoundedL_winU Awin := by
  unfold S16BandLaneCBoundedLH_winU S16BandLaneCBoundedL_winU
  simp only [socketBaseLH_one_iff]

set_option maxHeartbeats 1000000 in
-- The landed mint's own budget: the band body re-elaborates at every socket base.
/-- **⟦THE BAND MINT AT THE INFLATED SOCKET⟧** (`m4_hband_at_door_slot_split_graded_LH_gk`) —
`S11HoistLinear:736` with both socket quantifiers at `SocketBaseLH h`.  **The proof body is the
landed one verbatim**: it projects conjunct 4 (`0 < q`) and passes `hb` to its own antecedent,
and `SocketBaseLH` moves neither. -/
theorem m4_hband_at_door_slot_split_graded_LH_gk (h : ℕ) (_hh : 0 < h) (K : ℕ)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (x₀ : ℕ) (Cb : ℝ), 0 < Cb ∧ ∀ (M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
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

set_option maxHeartbeats 1000000 in
-- Same cause as the landed `_uniform` mint.
/-- **⟦THE BAND MINT AT THE INFLATED SOCKET, WITNESS-UNIFORM⟧**
(`m4_hband_at_door_slot_split_graded_LH_gk_uniform`) — `S11HoistLinear:861` with both socket
quantifiers at `SocketBaseLH h`; body verbatim, for the same reason as the `K`-fixed twin. -/
theorem m4_hband_at_door_slot_split_graded_LH_gk_uniform (h : ℕ) (_hh : 0 < h)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ (x₀ : ℕ) (Cb : ℝ), 0 < Cb ∧ ∀ (K M : ℕ), 1 ≤ M →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ Cb * (M : ℝ) ^ (2.1 : ℝ) ∧
        ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
          ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q,
                (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                  ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                  ≤ t0BandB (((A + s : ℕ)) : ℝ)
                      (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ :=
    m4_hT0band_at_door_discharged_split_graded_prod_L_gk_uniform hMmu Aexp hAexp
  have h4A : (0 : ℝ) < (4 : ℝ) ^ Aexp := Real.rpow_pos_of_pos (by norm_num) Aexp
  have hEpos : (0 : ℝ) < Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) := by positivity
  refine ⟨x₀, C * (4 : ℝ) ^ Aexp * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1,
    by positivity, ?_⟩
  intro K M hM
  obtain ⟨hP4, hPQ⟩ := door_window_bounds_L_gk K M hM
  obtain ⟨hP4₁, hPQ₁⟩ := door_block_bounds_L_gk K M hM (j := 1) le_rfl
  obtain ⟨hP4₂, hPQ₂⟩ := door_block_bounds_L_gk K M hM (j := 2) (by norm_num)
  obtain ⟨C', hC'pos, hC'le, hband⟩ := hsplit K
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

/-! ## §3 — BLOCK W's PRIZE: THE WINDOWED RIDER IS A THEOREM AT SHIFT `h` TOO -/

/-- ⭐ **⟦THE WINDOWED RIDER IS A THEOREM AT `h`⟧** (`s16_bandLaneWinLH_holds`) —
`S16Uniform.s16_bandLaneWinL_holds` on the inflated mint.  **This is the row where wave H2b's
price cut does not repeat, and it repays the difference:** `S16BandLaneCBoundedL` has no producer
anywhere, so H2b's re-quantification of it was free and left an open rider; the WINDOWED rider is
discharged, so the `h` lane gets a DISCHARGED rider here rather than a re-stated debt.

The window is satisfied by construction at `Awin := max 162 ((log Cband + 20)/0.64)`, exactly as
at `h = 1`, because `Cband = Cb/E` and the mint's constant carries no `A`. -/
theorem s16_bandLaneWinLH_holds (h : ℕ) (hh : 0 < h) (K : ℕ) :
    ∃ Awin : ℝ, 162 ≤ Awin ∧ S16BandLaneCBoundedLH_win h Awin K := by
  obtain ⟨x₀, Cb, hCb0, hsplit⟩ :=
    m4_hband_at_door_slot_split_graded_LH_gk h hh K mmuChiRate_holds_gated s13Aexp
      (by rw [s13Aexp]; norm_num)
  set E : ℝ := (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (s13Aexp) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0 : ℝ) < (4 : ℝ) ^ (1.05 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cband : ℝ := Cb / E with hCbanddef
  have hCband0 : (0 : ℝ) < Cband := div_pos hCb0 hE0
  refine ⟨max 162 ((Real.log Cband + 20) / 0.64), le_max_left _ _,
    x₀, Cband, hCband0, ?_, ?_⟩
  · -- ⟦THE WINDOW, BY CONSTRUCTION⟧
    have h := le_max_right (162 : ℝ) ((Real.log Cband + 20) / 0.64)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.64)] at h
    linarith
  · intro M hM
    obtain ⟨C', hC'0, hC'le, hbody⟩ := hsplit M hM
    refine ⟨C', hC'0, ?_, hbody⟩
    have hid : Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) = Cb := by
      rw [hCbanddef, hEdef]; field_simp
    have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    rw [hid]
    nlinarith [hC'le, hMpow]

/-- ⭐ **⟦THE WINDOWED RIDER IS A THEOREM AT `h`, WITNESS-UNIFORM⟧**
(`s16_bandLaneWinLH_holdsU`) — `S16ComposeV4.s16_bandLaneWinL_holdsU` on the inflated uniform
mint; one `x₀` and one `Cband` serving every lever, at every shift `h`. -/
theorem s16_bandLaneWinLH_holdsU (h : ℕ) (hh : 0 < h) :
    ∃ Awin : ℝ, 162 ≤ Awin ∧ S16BandLaneCBoundedLH_winU h Awin := by
  obtain ⟨x₀, Cb, hCb0, hsplit⟩ :=
    m4_hband_at_door_slot_split_graded_LH_gk_uniform h hh mmuChiRate_holds_gated s13Aexp
      (by rw [s13Aexp]; norm_num)
  set E : ℝ := (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (s13Aexp) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0 : ℝ) < (4 : ℝ) ^ (1.05 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cband : ℝ := Cb / E with hCbanddef
  have hCband0 : (0 : ℝ) < Cband := div_pos hCb0 hE0
  refine ⟨max 162 ((Real.log Cband + 20) / 0.64), le_max_left _ _,
    x₀, Cband, hCband0, ?_, ?_⟩
  · -- ⟦THE WINDOW, BY CONSTRUCTION⟧
    have h := le_max_right (162 : ℝ) ((Real.log Cband + 20) / 0.64)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.64)] at h
    linarith
  · intro K M hM
    obtain ⟨C', hC'0, hC'le, hbody⟩ := hsplit K M hM
    refine ⟨C', hC'0, ?_, hbody⟩
    have hid : Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) = Cb := by
      rw [hCbanddef, hEdef]; field_simp
    have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    rw [hid]
    nlinarith [hC'le, hMpow]

end Salt.MR
