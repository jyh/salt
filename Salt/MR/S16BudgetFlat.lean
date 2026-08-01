/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16Budget
import Salt.MR.FlatConsumers

/-!
# THE FLAT SHAPE at the TOP OF THE ROAD — HOP 3 and HOP 4 (freeze F-5)

The two terminal `S16Budget` surfaces at the flat tower conjunct:

* **HOP 3** `logChowla2_capstone_final_const'_graded_gk_pinned_Mfl` (`:1429`) — a
  pure CARRIER.  Its flat twin is the landed statement with the conjunct
  re-shaped, proved by one `pow_nine_halves_le_exp_half`.
* **HOP 4** `logChowla2_conditional_sharp2_atK_gk_pinned_Mfl` (`:1654`) — the
  first surface on this road that CONSUMES the conjunct (`htow := hRtow hlam50`,
  `:1700`) and spends it on four socket suppliers.  Its flat twin is the landed
  proof with those four swapped for the flat consumers of
  `Salt.MR.FlatConsumers` — `s15_gRows_const_at_socket_gk_flat`,
  `s12c_eps_threshold_at_socket_flat`, `s15_heps293_at_socket_flat`,
  `s15_hband4096_at_socket_flat` — every one of which closes against the flat
  λ-engine `flat_lambda_core` at the SAME numerals as the landed proof.

⚠ ⟦THE FRONTIER — WHERE THE FLAT ROAD STOPS AT THIS WAVE⟧  HOP 5
(`logChowla2_conditional_sharp2_nonvacuous_gk'_Mfl`, `:1758`) reads the conjunct
NUMERICALLY through `S15Witness.s15w2_tower_bound`: at the witness floor's window
`λ₋ ≤ 277.2589` the `9/2` law gives `λ₊ ≤ 9.87·10¹⁰`, while the flat law gives
`λ₊ ≤ e^{138.63} ≈ 2·10⁶⁰`.  The `2^355` register discharge (`24·Cg/δ₀ ≤ 2^355`)
and the whole `S15Witness` numeral table are calibrated against the former.
Re-cutting them is the REGISTER/DOOR cone (FLAT-REF §2: S3's `Adoor M := 2^36·M`
linear re-cut, then the cap+frame face re-priced against `e^{λ₋/2}` at its uniform
`400×` margin), NOT this one.  HOP 5 and everything above it therefore has NO
flat twin in this wave, and that is the named frontier.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

set_option maxHeartbeats 1000000 in
-- Same cause as the landed original: the residue re-elaborates against the re-cut prefix.
/-- **⟦HOP 3, FLAT⟧** — `logChowla2_capstone_final_const'_graded_gk_pinned_Mfl`
(`S16Budget.lean:1429`) at the FLAT tower conjunct.  Pure carry. -/
theorem logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flat (K : ℕ)
    (hK : K ≤ 170000000) (hband : S16BandLaneCBounded K) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ Ct Cq cs T₀ Kq Ks : ℝ) (x₀ Hcap Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧
        0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
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
                    DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                  (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
                    DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                      (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                    ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hKc, hδ₀, hCt, hCq,
      hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl K hK hband
  refine ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hKc, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, ?_⟩
  intro Cp hCp U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hRcap, hR⟩ := hmain Cp hCp U1floor g
  exact ⟨R, hReps, hU1, hRg,
    fun h50 => le_trans (hRtow h50) (pow_nine_halves_le_exp_half h50), hRcap, hR⟩

set_option maxHeartbeats 1000000 in
-- Same cause as the landed original: the residue re-elaborates against the prefix.
/-- **⟦HOP 4, FLAT⟧** — `logChowla2_conditional_sharp2_atK_gk_pinned_Mfl`
(`S16Budget.lean:1654`) at the FLAT tower conjunct.  THE DELIVERABLE: the first
surface on the road whose flat twin is genuine new content rather than a
weakening — the landed proof with its four socket suppliers taken from
`Salt.MR.FlatConsumers`, at unchanged numerals. -/
theorem logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flat (K : ℕ) (hK : K ≤ 170000000)
    (hband : S16BandLaneCBounded K) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ 2 ^ 355 ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
        ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          ∀ M : ℕ, S15Sel''_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
            S15CrossingBound_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, Ct, Cq, cs, T₀, Kq, Ks, x₀, Hcap, Mfl, hCg, hε, hKc, hδ₀, hCt, hCq,
    hcs, hT₀, hKq, hKs, hMfl, hCgle, hεpin, hδpin, hMflb, hmain⟩ :=
    logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flat K hK hband
  refine ⟨ε, Cg, Kc, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hKc, hδ₀, hCt, hMfl,
    hCgle, hεpin, hδpin, hMflb, ?_⟩
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
  -- ⟦THE BASE PIN⟧ `R.Hlo = U1floor`
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
  -- ⟦the two scale floors⟧
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  -- ⟦the arm, both halves⟧
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
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the RESTORED anchor
  have harith := s15_doorArithFrameRho_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_of_halfWindow_gk K hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register, at the RESTORED `x0_le`⟧
  have hgate : S13BandGate'_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor le_rfl (s13_g2_jfloor_of_MSelect'_gk K hsel.hM (by linarith) hS))
    (s15_gate8_gk K le_rfl (s13_gate8_of_MSelect'_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gk K hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_gk_flat K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl hb hlam50 htow hsel.rho le_rfl)
    (fun H L q j A s hb => s15_heps293_at_socket_flat hfl hb hρ0 hlam50 htow hsel.rho)
    (fun H L q j A s hb => s15_hband4096_at_socket_flat hfl hb hρ0 hlam50 htow hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_gk K hsel.hM (hgate.block H L q j A s hb) hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

end Salt.MR

end
