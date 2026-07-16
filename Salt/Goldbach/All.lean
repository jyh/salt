/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Base
import Salt.Goldbach.WeightWindow
import Salt.Goldbach.Residue
import Salt.Goldbach.Density
import Salt.Goldbach.A1
import Salt.Goldbach.A1W
import Salt.Goldbach.A2W
import Salt.Goldbach.Switch
import Salt.Goldbach.SwitchBV
import Salt.Goldbach.Band
import Salt.Goldbach.Count
import Salt.Goldbach.WindowSW
import Salt.Goldbach.PiUpper
import Salt.Goldbach.BandIdent
import Salt.Goldbach.CountFinal
import Salt.Goldbach.SW2
import Salt.Goldbach.PDiag
import Salt.Goldbach.Op
import Salt.Goldbach.Omega
import Salt.Goldbach.Op2
import Salt.Goldbach.Price
import Salt.Goldbach.PriceClose
import Salt.Tactic.AuditAxioms

/-!
# The Goldbach rung (`chen_goldbach`) — aggregate import

Sprint Q1 (full in-sprint, JYH-ratified 29a9a68): Chen's second theorem —
every sufficiently large even `N` is `p + P₂`. Design:
`docs/exploration/q1-design.md` (frozen statement D0, waves W0–W4,
post-gate corrections). The reuse contract (D1): the 2A backbone imports
unchanged; wave files are new siblings under `Salt/Goldbach/`. This
aggregator is HOUSE-OWNED: executors never edit it; each wave landing is
wired here at its ceremony.
-/

-- Build-time axiom audit: a stray axiom in the Goldbach rung fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.Goldbach.window_two_thirds_lt
  Salt.Goldbach.card_window_dvd_le Salt.Goldbach.stripSum_le
  Salt.Goldbach.exists_crt_finset Salt.Goldbach.goldbach_residue_witness
  Salt.Goldbach.crtClassG_modEq_left Salt.Goldbach.crtClassG_modEq_right
  Salt.Goldbach.crtClassG_coprime Salt.Goldbach.crt_class_coprimeG
  Salt.Goldbach.goldPs_squarefree Salt.Goldbach.goldPs_primeFactors
  Salt.Goldbach.goldPs_coprime_N Salt.Goldbach.coprime_of_dvd_goldPs
  Salt.Goldbach.goldPs_odd Salt.Goldbach.goldPs_primeFactors_facts
  Salt.Goldbach.coprime_mod_of_coprime Salt.Goldbach.crtClass_coprime_gold
  Salt.Goldbach.card_primesInWindow_dvd_le
  Salt.Goldbach.punctured_correction_le
  Salt.Goldbach.window_prod_upper_punctured
  Salt.Goldbach.exp_correction_le Salt.Goldbach.exp_correction_le_op
  Salt.Goldbach.window_prod_upper_punctured_folded
  Salt.Goldbach.goldPs_nu_eq Salt.Goldbach.goldPs_hnu
  Salt.Goldbach.gold_A1_lower Salt.Goldbach.gold_A1_lower_B
  Salt.Goldbach.goldBVSum Salt.Goldbach.W_goldA1_ge
  Salt.Goldbach.gold_A1_lower_W Salt.Goldbach.gold_A1_lower_B_W
  Salt.Goldbach.goldRosserRemainderW_le_split Salt.Goldbach.goldBVSum_W
  Salt.Goldbach.gold_A2_per_prime_W
  Salt.Goldbach.goldRosserRemainderW2_le_split
  Salt.Goldbach.goldA2_hBVagg_W Salt.Goldbach.goldA2W_rem_eq
  Salt.Goldbach.goldApSumW_eq_psiAP
  Salt.Goldbach.goldTripleSum_eq_card Salt.Goldbach.gold_switch_upper_B
  Salt.Goldbach.gold_block_switch_upper_B_W
  Salt.Goldbach.gold_mainA3_of_hBVswitch
  Salt.Goldbach.goldSwitchSieveW_W_eq
  Salt.Goldbach.goldBlockSwitchSieveW_maxDepth_eq
  Salt.Goldbach.goldSwitchSieve_multSum_eq_apCount
  Salt.Goldbach.goldSwitchSieve_rem_split
  Salt.Goldbach.gold_hBVswitch_of_generalBV Salt.Goldbach.gold_memClassG
  Salt.Goldbach.goldBlockMultSumW_eq_apCount
  Salt.Goldbach.goldBlockSwitchSieveW_rem_split
  Salt.Goldbach.gold_hBVblocksW_of_generalBV
  Salt.Goldbach.gold_nonunit_forces_fst_dvd Salt.Goldbach.gold_hCE_at_op
  Salt.Goldbach.norm_goldSemiprimeBlockInd_le_one
  Salt.Goldbach.gold_switch_coprime_N
  Salt.Goldbach.gold_dvd_sub_of_resG Salt.Goldbach.gold_diag_residue_crumb
  Salt.Goldbach.goldCard_le_pairSum Salt.Goldbach.goldTripleSum_le_pairSum
  Salt.Goldbach.goldBlockBox_windowed_pair_card
  Salt.Goldbach.goldBlockBox_windowDisc_eq_res
  Salt.Goldbach.goldBlockBox_windowDisc_eq_res_annulus
  Salt.Goldbach.goldWindowDisc_le_annulus_sum
  Salt.Goldbach.goldBlockBoxHonestDisc_eq_carrier
  Salt.Goldbach.goldBoxHonestDisc_le_annulus_sum
  Salt.Goldbach.goldPerPair_pi_upper
  Salt.Goldbach.goldLowRect_eq Salt.Goldbach.goldSymRect_eq
  Salt.Goldbach.goldLowRect_windowDisc_eq
  Salt.Goldbach.goldSymRect_windowDisc_eq
  Salt.Goldbach.goldBandCard_split Salt.Goldbach.goldSymCard_two_mul
  Salt.Goldbach.goldBandDiagCount_le Salt.Goldbach.goldBandDiscW_eq_three
  Salt.Goldbach.goldBandLowDisc_le_annulus_sum
  Salt.Goldbach.goldBandSymRectDisc_le_annulus_sum
  Salt.Goldbach.goldBandLowDisc_eq_carrier
  Salt.Goldbach.goldTripleSum_le_cbar_final
  Salt.Goldbach.goldCount_bound_uniformK
  Salt.Goldbach.gold_hBlockW_of_window_prices Salt.Goldbach.gold_hNum_at_opW
  Salt.Goldbach.gold_PloW_sym_of_box_disc
  Salt.Goldbach.gold_PloW_low_of_box_disc
  Salt.Goldbach.gold_bandDiscW_le_three_pieces_diag
  Salt.Goldbach.goldBlockHonestDiscW_eq_sum_pieces
  Salt.Goldbach.goldBlockBoxHonestDisc_split_m
  Salt.Goldbach.goldBlockResCountM_eq_sum_pieces
  Salt.Goldbach.gold_hBVblocksW_discharge'
  Salt.Goldbach.gold_diagAggW_le_honest Salt.Goldbach.gold_PloW_honest
  Salt.Goldbach.goldDiagPairSet_card_le
  Salt.Goldbach.sum_goldDiagTotal_le_goldDiagPairSet
  Salt.Goldbach.gold_op_Zpow9 Salt.Goldbach.gold_op_residue
  Salt.Goldbach.gold_a12_hBV_A1 Salt.Goldbach.gold_a12_hA1
  Salt.Goldbach.gold_op_count_rows Salt.Goldbach.gold_op_hCE
  Salt.Goldbach.gold_opQ_squarefree Salt.Goldbach.gold_opQ_even
  Salt.Goldbach.gold_opQ_coprime_P
  Salt.Goldbach.goldOmegaPrimeSum_decomp Salt.Goldbach.goldA2W_hcoef
  Salt.Goldbach.gold_a12_hBV_A2 Salt.Goldbach.gold_a12_hA2
  Salt.Goldbach.gold_op_Yhalf Salt.Goldbach.gold_factors_ge_z_of_sift
  Salt.Goldbach.goldOpP_pfull
  Salt.Goldbach.gold_hcount_seam
  Salt.Goldbach.gold_crtClassG_coprime_of_mem
  Salt.Goldbach.gold_box_price_engine
  Salt.Goldbach.gold_hNum_close_of_tower Salt.Goldbach.gold_tower_budget
  Salt.Goldbach.gold_mainA3_at_op
