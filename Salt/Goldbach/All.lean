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
