/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

import Salt.MR.DoorReceipt
import Salt.MR.FlatDoorStandoff
import Salt.MR.V7SiegelFree
import Salt.TwinBar.SevenEighthsStandoff
import Salt.MR.FlatDesignBound

/-!
# The flat door's Ξ_H receipt under a Siegel standoff (O13)

`mrtUniformityXi_holds_flat`, the Ξ_H-restricted `L¹` door on the flat family (a row added to RESULTS
on 2026-10-24), reaches `Salt.SW.siegel_theorem` through six declarations of
`Salt/MR/DoorReceipt.lean` that had no standoff twin, the head included, measured by the pruned map
probe the same day: `mrtUniformityXiL2_holds_flat`, `mrtDoorReceipt_v7_form`, `flat_chain_generic`
and its two arms `flat_v7_generic` and `flat_kswin_generic`. Their reaching children already have
twins (`s16_bandLaneWinL_holdsU_of_standoff` and the `kswin` crossing in
`Salt/MR/V7SiegelFree.lean`). Each declaration below is its landed statement under the three leading
binders `{cS} (hcS) (hSieg)`, its landed proof verbatim with each reaching child replaced by its
twin, emitted inside a replay of the scope that was active at the landed declaration. The text was
generated from the landed sources by script. No landed proof is edited; the ledger
`Salt/MR/All.lean` gains the import and the audit block.

## What this does and does not say

* Each conclusion is the landed statement token for token (`#assert_conclusion_is`), under the open
  hypothesis `NoSiegelZerosAt cS`, or under the repository's restatement `DirichletSevenEighths`,
  which is a HYPOTHESIS here.
* The certificate below is about the PROOF TERM: each closure contains none of `siegel_theorem`,
  `siegel_L_one_exceptional` and `L1_lower_siegel`, while the landed head's closure contains
  `siegel_theorem` (the positive control). `#print axioms` cannot see this.
* The door is one produced regime per floor, as in the landed row. Nothing here makes a constant
  explicit, and nothing here bears on twin primes.
-/

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `flat_v7_generic` (`Salt/MR/DoorReceipt.lean:825`): its statement under the three standoff
binders, its proof verbatim with `s16_bandLaneWinL_holdsU` replaced by their twins. -/
theorem flat_v7_generic_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (P : ChowlaRegime → Prop)
    (h : ∀ Awin : ℝ, S16BandLaneCBoundedL_winU Awin → FlatKswinForm P Awin)
    (A₀ : ℝ) :
    V7RatedForm P A₀ := by
  unfold V7RatedForm
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated
  obtain ⟨Awin, -, hband⟩ := (s16_bandLaneWinL_holdsU_of_standoff hcS hSieg)
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    h Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrict_zero ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / 500 ≤ R.eps := by rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / 500 ≤ (R.eps : ℝ) := by
    rw [hReps]
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `flat_kswin_generic` (`Salt/MR/DoorReceipt.lean:731`): its statement under the three standoff
binders, its proof verbatim with `s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin` replaced by their twins. -/
theorem flat_kswin_generic_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatConditionalForm P Awin) :
    FlatKswinForm P Awin := by
  unfold FlatKswinForm
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    h
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := (s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin_of_standoff hcS hSieg)
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε2q
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num)
    (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `flat_chain_generic` (`Salt/MR/DoorReceipt.lean:1022`): its statement under the three standoff
binders, its proof verbatim with `flat_v7_generic` · `flat_kswin_generic` replaced by their twins. -/
theorem flat_chain_generic_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (P : ChowlaRegime → Prop) (h : FlatHeadForm P) (A₀ : ℝ) :
    V7RatedForm P A₀ :=
  (flat_v7_generic_of_standoff hcS hSieg) P (fun Awin hband => (flat_kswin_generic_of_standoff hcS hSieg) P Awin
    (flat_conditional_generic P Awin
      (flat_capstone_generic P (flat_road_generic P (flat_doorL2_generic P
        (flat_socket_generic P h))) Awin hband))) A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `mrtDoorReceipt_v7_form` (`Salt/MR/DoorReceipt.lean:1046`): its statement under the three standoff
binders, its proof verbatim with `flat_chain_generic` replaced by their twins. -/
theorem mrtDoorReceipt_v7_form_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) : V7RatedForm MRTDoorReceipt A₀ :=
  (flat_chain_generic_of_standoff hcS hSieg) _ flat_door_head_xceil A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `mrtUniformityXiL2_holds_flat` (`Salt/MR/DoorReceipt.lean:1056`): its statement under the three standoff
binders, its proof verbatim with `mrtDoorReceipt_v7_form` replaced by their twins. -/
theorem mrtUniformityXiL2_holds_flat_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / 500 ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 837782 ∧ MRTUniformityXiL2 R ρ := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hεpin, -, -, -, hA162, hA₀A, R, hReps, hHlo, -, hdes, -, hdoor⟩ :=
    (mrtDoorReceipt_v7_form_of_standoff hcS hSieg) A₀
  exact ⟨ε, A, hε, hεpin, hA162, hA₀A, R, hReps, hHlo, hdes, hdoor⟩
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private uniformCap_arc uniformCap_shuffle from Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
set_option exponentiation.threshold 4000
/-- **⟦STANDOFF TWIN⟧** `mrtUniformityXi_holds_flat` (`Salt/MR/DoorReceipt.lean:1119`): its statement under the three standoff
binders, its proof verbatim with `mrtUniformityXiL2_holds_flat` replaced by their twins. -/
theorem mrtUniformityXi_holds_flat_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / 500 ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (1 / 837782) ∧ MRTUniformityXi R δ := by
  obtain ⟨ε, A, hε, hεpin, hA162, hA₀A, R, hReps, hHlo, hdes, ρ, hρ0, hρle, hdoor⟩ :=
    (mrtUniformityXiL2_holds_flat_of_standoff hcS hSieg) A₀
  exact ⟨ε, A, hε, hεpin, hA162, hA₀A, R, hReps, hHlo, hdes, Real.sqrt ρ,
    Real.sqrt_pos.mpr hρ0, Real.sqrt_le_sqrt hρle, mrtUniformityXi_of_xiL2 R hρ0.le hdoor⟩
/-- `mrtUniformityXi_holds_flat` from the 7/8 statement, without Siegel's theorem. -/
theorem mrtUniformityXi_holds_flat_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / 500 ≤ ε ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (1 / 837782) ∧ MRTUniformityXi R δ :=
  mrtUniformityXi_holds_flat_of_standoff (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.MR.mrtUniformityXi_holds_flat Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.mrtUniformityXiL2_holds_flat_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.mrtUniformityXiL2_holds_flat_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.mrtUniformityXiL2_holds_flat_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.mrtDoorReceipt_v7_form_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.mrtDoorReceipt_v7_form_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.mrtDoorReceipt_v7_form_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_chain_generic_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_chain_generic_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_chain_generic_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_v7_generic_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_v7_generic_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_v7_generic_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_kswin_generic_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_kswin_generic_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_kswin_generic_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.mrtUniformityXi_holds_flat_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.MR.mrtUniformityXi_holds_flat_of_standoff 3
  Salt.MR.mrtUniformityXi_holds_flat
#assert_conclusion_is Salt.MR.mrtUniformityXiL2_holds_flat_of_standoff 3
  Salt.MR.mrtUniformityXiL2_holds_flat
#assert_conclusion_is Salt.MR.mrtDoorReceipt_v7_form_of_standoff 3 Salt.MR.mrtDoorReceipt_v7_form
#assert_conclusion_is Salt.MR.flat_chain_generic_of_standoff 3 Salt.MR.flat_chain_generic
#assert_conclusion_is Salt.MR.flat_v7_generic_of_standoff 3 Salt.MR.flat_v7_generic
#assert_conclusion_is Salt.MR.flat_kswin_generic_of_standoff 3 Salt.MR.flat_kswin_generic
#assert_conclusion_is Salt.MR.mrtUniformityXi_holds_flat_of_sevenEighths 1
  Salt.MR.mrtUniformityXi_holds_flat

end
end Salt.MR
