/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.RosserChain
import Salt.Chen.Tail
import Salt.Chen.LinearSieve
import Salt.Chen.Buchstab
import Salt.Chen.TnInduction
import Salt.Chen.Lemma11
import Salt.Chen.Peeling
import Salt.Chen.StepBound
import Salt.Chen.StepBound2
import Salt.Chen.Hyp4
import Salt.Chen.AbelStep
import Salt.Chen.SharpStep
import Salt.Chen.DecayMass
import Salt.Chen.WindowedStep
import Salt.Chen.TwinA1
import Salt.Chen.TwinA2
import Salt.Chen.BVSum
import Salt.Chen.TauNumeric
import Salt.Chen.SharpTau
import Salt.Chen.GeneralBV
import Salt.Chen.BetaSW
import Salt.Chen.ConductorDescent
import Salt.Chen.BilinearDescent
import Salt.Chen.TripleCount
import Salt.Chen.EnergyClose
import Salt.Chen.EnergyShellDvd
import Salt.Chen.DyadicDvd
import Salt.Chen.TotientHelpers
import Salt.Chen.DivisorBound
import Salt.Chen.MertensPNT
import Salt.Chen.WRatioSharp
import Salt.Chen.WeightedCount
import Salt.Chen.CbarCert
import Salt.Chen.AbelPass
import Salt.Chen.AbelPass2
import Salt.Chen.CountClose
import Salt.Chen.CountFinal
import Salt.Chen.WindowBV
import Salt.Chen.WindowBVDescent
import Salt.Chen.WindowSW
import Salt.Chen.WindowClose
import Salt.Chen.WindowErrFold
import Salt.Chen.WindowSmallChi
import Salt.Chen.PieceDecomp
import Salt.Chen.BandSplit
import Salt.Chen.BandClose
import Salt.Chen.BandIdent
import Salt.Chen.ErrFold
import Salt.Chen.PerEEngine
import Salt.Chen.PerEEngine2
import Salt.Chen.AlphaSide
import Salt.Chen.AlphaClose
import Salt.Chen.WeightTrivia
import Salt.Chen.SharpFuncbound
import Salt.Chen.FlatFuncbound
import Salt.Chen.ChainValues
import Salt.Chen.TauSharp
import Salt.Chen.ValueCascade
import Salt.Chen.PLCascade
import Salt.Chen.MassLedger
import Salt.Chen.MassLedgerA1
import Salt.Chen.MassCert
import Salt.Chen.MassCert2
import Salt.Chen.LogToolkit
import Salt.Chen.SuperSolution
import Salt.Chen.SuperProfile
import Salt.Chen.SuperProfileDef
import Salt.Chen.SuperPanelsO
import Salt.Chen.SuperPanelsE
import Salt.Chen.SuperClose
import Salt.Chen.FchainPoint
import Salt.Chen.A2Weighted
import Salt.Chen.WindowMembership
import Salt.Chen.RazorClose
import Salt.Chen.GlueNormalized
import Salt.Chen.GlueBV
import Salt.Chen.WLower
import Salt.Chen.SubBlocked
import Salt.Chen.TransposedBV
import Salt.Chen.MediumFloor
import Salt.Chen.SqrtDFold
import Salt.Chen.GlueFinal
import Salt.Chen.Headline
import Salt.Chen.SharpH
import Salt.Chen.SharpH2
import Salt.Chen.SharpF
import Salt.Chen.H4Cond
import Salt.Chen.SharpClose
import Salt.Chen.FseqAntitone
import Salt.Chen.TwinSharp
import Salt.Chen.WindowedStepP
import Salt.Chen.WindowedStepC
import Salt.Chen.Assembly
import Salt.Chen.SwitchSieve
import Salt.Chen.SwitchBV
import Salt.Chen.SwitchDyadic
import Salt.Chen.SwitchPricing
import Salt.Chen.SwitchStrip
import Salt.Chen.SwitchBlocks
import Salt.Chen.TwinA1W
import Salt.Chen.SwitchW
import Salt.Chen.SwitchW2
import Salt.Chen.HeadlineW
import Salt.Chen.PDiag
import Salt.Chen.HeadlineW2
import Salt.Chen.PriceOne
import Salt.Chen.PriceTwo
import Salt.Chen.PriceThree
import Salt.Chen.PriceClose
import Salt.Chen.ChenHeadline
import Salt.Chen.ChenFinal
import Salt.Chen.ChenFinal2
import Salt.Chen.ChenRows1
import Salt.Chen.ChenRows2
import Salt.Chen.Headline3
import Salt.Chen.MiddleK
import Salt.Chen.AssembleA3
import Salt.Chen.AggCE
import Salt.Chen.AggDiag
import Salt.Chen.AggSum
import Salt.Chen.AssembleA3b
import Salt.Chen.TheHeadline
import Salt.Chen.PackA
import Salt.Chen.PackB
import Salt.Chen.CountAtOp
import Salt.Chen.A2Window
import Salt.Chen.CountAtOp2
import Salt.Chen.CountAtOp3
import Salt.Chen.Headline4
import Salt.Chen.FinA3
import Salt.Chen.FinLed
import Salt.Chen.FinA3b
import Salt.Chen.CountW
import Salt.Chen.TwinA2W
import Salt.Chen.BlockPricing
import Salt.Chen.PairBijection
import Salt.Chen.SwitchConstant
import Salt.Tactic.AuditAxioms

/-!
# The Chen rung (`chen`) — aggregate import

Design: `docs/blueprints/chen.md`. Target: **`chen_of_siegelWalfisz`**
(`p + 2 = P₂` infinitely often, modulo the SW gate) — the same gate the
SW arc is discharging, so the day it lands both bounded gaps AND Chen
become unconditional. Route: Tao 254A Supp. 5 (native twin form) with
the BJS explicit linear sieve (arXiv:2207.09452v6) as the constants
backbone; margin `M = 2log3 − log6 − c̄ ≈ 0.0424` at assembly
normalization (catch #20), governed by the frozen C0 budget ledger
(catches #21–#24).

## Landed (wave 1)

`RosserChain` (C1a, FULL): `fseq` (the BJS (15)–(17) Rosser-chain
system, total with documented junk-zero windows; the improper tails
realized as finite `intervalIntegral`s via `fseq_eq_zero_of_ge`),
`Fchain`/`fchain` at the **catch-#24-corrected parities** (F = 1 +
odd sum, f = 1 − EVEN sum; regression witness
`Fchain_add_fchain_one_ne_two` documents that the printed parity would
force F + f ≡ 2), first values `fseq_one_window`/`fseq_two_window`
(= BJS (19)), and the full integrability package (`fseq_props`
coupled induction → `fseq_measurable`/`fseq_bounded`/
`fseq_intervalIntegrable`/`fseq_shift_intervalIntegrable`).

`SwitchConstant` (C4a, FLOOR): `cbar` (the switch integral), `cbar_pos`,
and **`two_log_three_sub_log_six_sub_cbar_pos`** — the literal budget
line C5 consumes (`2log3 − log6 = log(3/2) ≥ 2/5 > 0.363084`). The
tight `cbar_lt : cbar < 0.363084` (gap 2.7e−7) is DEFERRED: mathlib has
no `Li₂`/polylog and no `norm_num` log extension, so neither the exact
dilog route nor a ≳220-panel tangent majorant is in scope — and C3d's
Lean-shape count bound may come from explicit prime sums rather than
the smooth integral, in which case `cbar_lt` is never consumed. See the
module docstring and `docs/blueprints/flags.md`.
-/

-- Build-time axiom audit: a stray axiom in the `chen` carriers fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.Chen.cbar_pos
  Salt.Chen.two_log_three_sub_log_six_sub_cbar_pos
  Salt.Chen.fseq_one_window Salt.Chen.fseq_two_window
  Salt.Chen.fseq_nonneg Salt.Chen.fseq_eq_zero_of_ge
  Salt.Chen.fseq_intervalIntegrable Salt.Chen.fseq_shift_intervalIntegrable
  Salt.Chen.Fchain_add_fchain Salt.Chen.Fchain_add_fchain_one_ne_two
  Salt.Chen.fseq_le Salt.Chen.fseq_tail_sum_le Salt.Chen.fseq_tail_le
  Salt.Chen.fchain_close Salt.Chen.Fchain_close
  Salt.Chen.TruncSieve.isUpperMoebius Salt.Chen.TruncSieve.isLowerMoebius
  Salt.Chen.rosserCond_one Salt.Chen.rosserCond_dvd_closed
  Salt.Chen.rosserCond_add_prime
  Salt.Chen.rosserSieve_isUpperMoebius Salt.Chen.rosserSieve_isLowerMoebius
  Salt.Chen.linear_sieve_upper Salt.Chen.linear_sieve_lower
  Salt.Chen.linear_sieve_upper_chain Salt.Chen.linear_sieve_lower_chain
  Salt.Chen.rosserCond_upper_lt Salt.Chen.rosserCond_lower_lt
  Salt.Chen.mainSum_moebius_eq_W Salt.Chen.mainSum_lam_defect
  Salt.Chen.linear_sieve_upper_rosser Salt.Chen.linear_sieve_lower_rosser
  Salt.Chen.buchstab_defect Salt.Chen.buchstab_upper Salt.Chen.buchstab_lower
  Salt.Chen.T_nonneg Salt.Chen.hbar_le_hBJS
  Salt.Chen.hmain_upper Salt.Chen.hmain_lower
  Salt.Chen.linear_sieve_upper_rosser_assembled
  Salt.Chen.linear_sieve_lower_rosser_assembled
  Salt.Chen.prod_telescope Salt.Chen.T_one_upper Salt.Chen.T_two_one_zero
  Salt.Chen.hlevel_one_upper Salt.Chen.tau_sum_le_of_recursion
  Salt.Chen.hTbound_upper_of_levels Salt.Chen.hTbound_lower_of_levels
  Salt.Chen.linear_sieve_upper_rosser_assembled_final
  Salt.Chen.linear_sieve_lower_rosser_assembled_final
  Salt.Chen.T_peel Salt.Chen.isViolPrefix_peel_iff Salt.Chen.W_sieveBelow
  Salt.Chen.T_le_of_peel_step
  Salt.Chen.hlevel_upper_of_step Salt.Chen.hlevel_lower_of_step
  Salt.Chen.hmain_upper_of_step Salt.Chen.hmain_lower_of_step
  Salt.Chen.hBJS_funcbound Salt.Chen.hbase_of
  Salt.Chen.tauSum_odd_le Salt.Chen.tauSum_even_le
  Salt.Chen.bjs_theorem6_upper Salt.Chen.bjs_theorem6_lower
  Salt.Chen.bjs_theorem6_upper_sifted Salt.Chen.bjs_theorem6_lower_sifted
  Salt.Chen.T_le_of_peel_step' Salt.Chen.hbase'_of
  Salt.Chen.bjs_theorem6_upper' Salt.Chen.bjs_theorem6_lower'
  Salt.Chen.bjs_theorem6_upper_sifted' Salt.Chen.bjs_theorem6_lower_sifted'
  Salt.Chen.neg_log_nu_le Salt.Chen.vratio_prod_le Salt.Chen.vratio_window_le
  Salt.Chen.h4_base Salt.Chen.w0R_threshold Salt.Chen.thresh_mono
  Salt.Chen.telescope_ge Salt.Chen.stepHyp_lhs_eq
  Salt.Chen.telescope_window_upper Salt.Chen.telescope_window_lower
  Salt.Chen.ledger_collect Salt.Chen.stepHyp_of_comparisons
  Salt.Chen.Vbelow_le_ratio Salt.Chen.prime_support_mass_le
  Salt.Chen.hf_of_window Salt.Chen.hh_reduced
  Salt.Chen.hBJS_antitone Salt.Chen.prime_tail_mass_le
  Salt.Chen.decay_mass_le Salt.Chen.hh_of_window
  Salt.Chen.stepHyp_pointwise
  Salt.Chen.T_vanish Salt.Chen.stepHypW_holds Salt.Chen.T_le_of_peel_step_w
  Salt.Chen.bjs_theorem6_windowed_upper Salt.Chen.bjs_theorem6_windowed_lower
  Salt.Chen.one_le_Fchain Salt.Chen.twin_A2_per_prime
  Salt.Chen.A2grid_le_envelope Salt.Chen.twin_A2_upper
  Salt.Chen.nuChen_eq_inv_totient Salt.Chen.twinA1_rem_eq
  Salt.Chen.twinA1_abs_rem_le Salt.Chen.twinA1_hnu Salt.Chen.twinA1_hguard
  Salt.Chen.twin_A1_lower
  Salt.Chen.rosserRemainder_le_split Salt.Chen.convSum_le
  Salt.Chen.sum_inv_totient_le_Winv Salt.Chen.twinA1_hBV
  Salt.Chen.tauChen_one Salt.Chen.tauChen_rec
  Salt.Chen.hτrec_zero_impossible Salt.Chen.tauSum_odd_ge
  Salt.Chen.fseq_geom_uniform Salt.Chen.ch_const_geom_ge
  Salt.Chen.tauDecSum_odd_ge
  Salt.Chen.apDiscBilin_orthogonality Salt.Chen.norm_apDiscBilin_le
  Salt.Chen.bilinTwist_energy_le Salt.Chen.general_BV_weak
  Salt.Chen.thetaAP_SW Salt.Chen.prime_indicator_SW
  Salt.Chen.prime_indicator_coprime_SW
  Salt.Chen.bilinTwist_eq_sum_class Salt.Chen.bilinTwist_le_of_classDisc
  Salt.Chen.hβSW_of_prime_indicator Salt.Chen.general_BV_closed
  Salt.Chen.bilinTwist_coprimeRestrict_primitive Salt.Chen.perd_energy_le
  Salt.Chen.regroup_bilin Salt.Chen.swapPhi_generic
  Salt.Chen.bilinear_hLargeDisc
  Salt.Chen.prime_count_Ioc_le Salt.Chen.triple_count_le
  Salt.Chen.chen_switch_const_lt
  Salt.Chen.smallConductor_energy_le Salt.Chen.hMainEnergy_discharge
  Salt.Chen.bilinTwist_sub_primitive_eq
  Salt.Chen.bilinTwist_efold Salt.Chen.hErrSum_reorg
  Salt.Chen.hErrSum_discharge
  Salt.Chen.efold_density_fold Salt.Chen.hErrSum_final
  Salt.Chen.hLargeDisc_of_perE Salt.Chen.general_BV_final
  Salt.Chen.EfoldTerm_split Salt.Chen.blockPrimeInd_dilated_eq_zero
  Salt.Chen.EfoldTermBeta_eq_zero Salt.Chen.sum_inv_Icc_le_log
  Salt.Chen.hErrSum_final' Salt.Chen.hLargeDisc_of_perE'
  Salt.Chen.general_BV_final' Salt.Chen.hPerE_reduces_to_alpha
  Salt.Chen.sum_totient_div_sqrt_le Salt.Chen.efold_large_fibered
  Salt.Chen.efold_large_reduce Salt.Chen.efold_large_discharge
  Salt.Chen.general_BV_alpha_final
  Salt.Chen.EfoldTermAlpha_eq_prim Salt.Chen.efold_alpha_reduce_dense
  Salt.Chen.efold_small_le Salt.Chen.efold_large_fourterm
  Salt.Chen.efold_alpha_le Salt.Chen.efold_small_discharge
  Salt.Chen.general_BV_alpha_discharged
  Salt.Chen.razor_reduction Salt.Chen.triplePrimeSum_le
  Salt.Chen.chen_positivity Salt.Chen.chen_survivor
  Salt.Chen.chen_of_hypotheses
  Salt.Chen.switch_hnu Salt.Chen.switch_hguard
  Salt.Chen.switch_upper_B Salt.Chen.triplePrimeSum_le_sifted
  Salt.Chen.mainA3_of_hBVswitch
  Salt.Chen.switch_dvd_coprime_two Salt.Chen.switchSieve_multSum_eq_apCount
  Salt.Chen.norm_semiprimeBlockInd_le_one Salt.Chen.switchSieve_rem_split
  Salt.Chen.switchSieve_abs_rem_le Salt.Chen.switchSieve_rosserRemainder_split_le
  Salt.Chen.hBVswitch_of_generalBV
  Salt.Chen.switchHonestDisc_eq_sum_box Salt.Chen.boxHonestDisc_zero_of_windowDisjoint
  Salt.Chen.abs_switchHonestDisc_le_sum_relevant Salt.Chen.hHD_of_generalBV_inputs
  Salt.Chen.abs_boxHonestDisc_le_boxCount Salt.Chen.card_relevantBoxes_le
  Salt.Chen.hHD_of_uniform_price Salt.Chen.norm_boxAlpha_le_one
  Salt.Chen.box_price_of_apDiscBilin
  Salt.Chen.blockBox_pair_card Salt.Chen.blockBox_apDiscBilin_eq
  Salt.Chen.norm_blockBox_apDiscBilin_eq
  Salt.Chen.blockSwitchSieve_rem_split Salt.Chen.blockRem_rosserRemainder_split_le
  Salt.Chen.sum_blockRem_split_le Salt.Chen.norm_blockPieceAlpha_le_one
  Salt.Chen.hHDblocks_of_perBlock Salt.Chen.hBVblocks_of_generalBV
  Salt.Chen.tripleSum_eq_sum_blockTripleSum Salt.Chen.blockSwitchSieve_W_eq
  Salt.Chen.block_switch_upper_B Salt.Chen.triplePrimeSum_le_sum_blocks
  Salt.Chen.norm_blockAlpha_le_one Salt.Chen.mainA3_of_block_remainders
  Salt.Chen.switchSieveW_W_eq Salt.Chen.blockSwitchSieveW_W_eq
  Salt.Chen.blockSwitchSieveW_maxDepth_eq
  Salt.Chen.triplePrimeSumW_le_sifted Salt.Chen.switchSieveW_siftedSum_eq_sum_blocks
  Salt.Chen.block_switch_upper_B_W Salt.Chen.mainA3_of_block_remainders_W
  Salt.Chen.crtClassW_coprime Salt.Chen.memClassW_iff
  Salt.Chen.blockMultSumW_eq_apCount Salt.Chen.blockUnitM_add_blockNonUnitM
  Salt.Chen.blockSwitchSieveW_rem_split Salt.Chen.blockSwitchSieveW_abs_rem_le
  Salt.Chen.blockRemW_rosserRemainder_split_le Salt.Chen.sum_blockRemW_split_le
  Salt.Chen.hBVblocksW_of_generalBV
  Salt.Chen.blockBox_windowDisc_eq_res
  Salt.Chen.apDiscBilin_sum_alpha Salt.Chen.apDiscBilin_split_threshold
  Salt.Chen.apDiscBilin_singleton_collapse Salt.Chen.norm_restrictAlpha_le_one
  Salt.Chen.productInWindow_of_corners
  Salt.Chen.tail_parts_bound Salt.Chen.hBJS_funcbound_sharp
  Salt.Chen.fchain_lower_of_evenSum_le Salt.Chen.Fchain_upper_of_oddSum_le
  Salt.Chen.fseq_two_le_sq Salt.Chen.fchain_two_lower
  Salt.Chen.fchain_trunc_close Salt.Chen.chen_ledger_line
  Salt.Chen.chen_weight_le_indicator Salt.Chen.chen_weight_struct
  Salt.Chen.stripSum_le Salt.Chen.window_two_thirds_lt
  Salt.Chen.switch_loss_le
  Salt.Chen.chSharp_lt_one Salt.Chen.sharp_h_contract
  Salt.Chen.chSharp_h_contract Salt.Chen.tauSharp_nonneg
  Salt.Chen.tauSharp_hτrec Salt.Chen.tauSharp_sum_le
  Salt.Chen.tauSharp_sum_odd_le Salt.Chen.tauSharp_sum_even_le
  Salt.Chen.Csharp_frozen Salt.Chen.stepHyp_sharp_of_comparisons
  Salt.Chen.bjs_theorem6_sharp_upper Salt.Chen.bjs_theorem6_sharp_lower
  Salt.Chen.fseq_next_le_of_shift_majorant Salt.Chen.integral_M3
  Salt.Chen.fseq2_shift_le_M3 Salt.Chen.M3_intble
  Salt.Chen.fseq_three_tail_le Salt.Chen.fseq_three_flat_le
  Salt.Chen.stepHypWP_const Salt.Chen.T_le_of_peel_step_wp
  Salt.Chen.hlevel_wp_upper Salt.Chen.hlevel_wp_lower
  Salt.Chen.bjs_theorem6_windowed_p_upper Salt.Chen.bjs_theorem6_windowed_p_lower
  Salt.Chen.bjs_theorem6_windowed_upper_via_p Salt.Chen.bjs_theorem6_windowed_lower_via_p
  Salt.Chen.bjs_theorem6_windowed_sharp_upper Salt.Chen.bjs_theorem6_windowed_sharp_lower
  Salt.Chen.stepHypWPC_of_wp Salt.Chen.stepHypWPC_const
  Salt.Chen.T_le_of_peel_step_wpc
  Salt.Chen.hlevel_wpc_upper Salt.Chen.hlevel_wpc_lower
  Salt.Chen.bjs_theorem6_windowed_c_upper Salt.Chen.bjs_theorem6_windowed_c_lower
  Salt.Chen.chSharpB_lt_one Salt.Chen.tauSharpB_hτrec
  Salt.Chen.tauSharpB_sum_le Salt.Chen.tauSharpB_sum_odd_le
  Salt.Chen.tauSharpB_sum_even_le Salt.Chen.CsharpB_frozen
  Salt.Chen.bjs_theorem6_windowed_cB_upper Salt.Chen.bjs_theorem6_windowed_cB_lower
  Salt.Chen.massE_nonneg Salt.Chen.fseq_odd_eq_massE
  Salt.Chen.Fchain_mass_ledger Salt.Chen.Fchain_le_A2_of_massSum
  Salt.Chen.massE_le_crude
  Salt.Chen.twin_A1_lower_B Salt.Chen.twin_A2_per_prime_B
  Salt.Chen.antitone_integral_lower Salt.Chen.fseq_one_antitoneOn_Ici
  Salt.Chen.fseq_antitoneOn_odd Salt.Chen.fseq_antitoneOn_even
  Salt.Chen.hBJS_shift_le Salt.Chen.upset_mass_le
  Salt.Chen.hh_antitone_majorize Salt.Chen.hh_sharp_ge2_of_pushforward
  Salt.Chen.layer_cake_pushforward Salt.Chen.hpush_core
  Salt.Chen.hh_sharp_ge2 Salt.Chen.upset_mass_window_le
  Salt.Chen.hh_sharp_flat Salt.Chen.hh_sharp_of_window
  Salt.Chen.abel_pushforward Salt.Chen.hf_cell_ge2
  Salt.Chen.hBJS_flat_lb Salt.Chen.vlow_le_of_guard Salt.Chen.h4_cond_of_base
  Salt.Chen.hf_sharp_flat Salt.Chen.hf_sharp_of_window
  Salt.Chen.stepHyp_sharpB_pointwise Salt.Chen.stepHypWPC_sharpB
  Salt.Chen.bjs_theorem6_sharpB_final_upper Salt.Chen.bjs_theorem6_sharpB_final_lower
  Salt.Chen.massO_nonneg Salt.Chen.fseq_even_eq_masses
  Salt.Chen.evenSum_le_of_massSums Salt.Chen.fchain_ge_A1_of_massSums
  Salt.Chen.massO_le_crude
  Salt.Chen.log_two_le Salt.Chen.le_log_two Salt.Chen.log_three_le
  Salt.Chen.le_log_three Salt.Chen.log_half_le_tangent Salt.Chen.log_half_ge_chord
  Salt.Chen.panel_le Salt.Chen.panel_ge Salt.Chen.integral_quad
  Salt.Chen.even_step Salt.Chen.odd_step Salt.Chen.Xe_recursion
  Salt.Chen.superSol_dominates Salt.Chen.massE_sum_eq Salt.Chen.massO_sum_eq
  Salt.Chen.massSum_le_A2_of_superSolution Salt.Chen.massOSum_le_A1_of_superSolution
  Salt.Chen.hSE_reduce Salt.Chen.hSO_reduce
  Salt.Chen.Ebar_panel_eq Salt.Chen.Obar_panel_eq
  Salt.Chen.Ebar_tail_eq Salt.Chen.Obar_tail_eq
  Salt.Chen.Ebar_nonneg Salt.Chen.Obar_nonneg
  Salt.Chen.Ebar_intervalIntegrable Salt.Chen.Obar_intervalIntegrable
  Salt.Chen.Ebar_integral_le Salt.Chen.Obar_integral_le
  Salt.Chen.W_twinA1_ge
  Salt.Chen.medium_support_floor_high Salt.Chen.medium_support_floor_low
  Salt.Chen.medium_support_floor_sym Salt.Chen.carrier_eq_zero_below_floor
  Salt.Chen.apDiscBilinCutoff_eq_of_under Salt.Chen.hdiv_direct
  Salt.Chen.dyadicBoundary_card_le_three Salt.Chen.box_disc_three_way
  Salt.Chen.medium_survivor_price Salt.Chen.hHD_of_box_disc
  Salt.Chen.Plo_sym_of_box_disc Salt.Chen.Plo_low_of_box_disc
  Salt.Chen.hNum_at_op
  Salt.Chen.medium_box_price_at_op Salt.Chen.bridge_scale
  Salt.Chen.kfloor_of_live_box Salt.Chen.box_hprice_at_2pow_lo
  Salt.Chen.box_price_at_op Salt.Chen.hCE_at_op
  Salt.Chen.hdiag_slot_at_op Salt.Chen.crumb_le_rpow_at_op Salt.Chen.opPdiag_compat
  Salt.Chen.hSum_at_op Salt.Chen.boxPriceKerr_worst_le Salt.Chen.kerr_ratio_term_le
  Salt.Chen.low_price_at_op Salt.Chen.sym_price_at_op Salt.Chen.op_floors
  Salt.Chen.boxPriceKerrY_worst_le Salt.Chen.symPriceK_worst_le
  Salt.Chen.lowPriceK_worst_le Salt.Chen.hRCE_at_op Salt.Chen.ratio_le_of_floor
  Salt.Chen.twinA1SieveW_W_eq Salt.Chen.hWy_at_op Salt.Chen.XW_pos_at_op
  Salt.Chen.hcount_at_op Salt.Chen.hcount_massBridge Salt.Chen.hcount_op_geometry
  Salt.Chen.box_price_indep Salt.Chen.tripleSum_le_16x_at_op
  Salt.Chen.low_price_indep Salt.Chen.sym_price_indep
  Salt.Chen.hcertA1_at_op Salt.Chen.hcertA3_at_op Salt.Chen.hcount_seam
  Salt.Chen.two_le_maxDepth_A1 Salt.Chen.XW_lower_at_op
  Salt.Chen.chen_headline_of_ops Salt.Chen.chen_headline_of_A3_ledger
  Salt.Chen.hA1_bundle Salt.Chen.hA2_bundle
  Salt.Chen.hcount_slot_closed Salt.Chen.hcount_star_at_op
  Salt.Chen.count_bound_uniformK Salt.Chen.corr_le_at_op
  Salt.Chen.hcount_Lval_rows Salt.Chen.Ifun_op_le Salt.Chen.S1set_mertens
  Salt.Chen.slack_collapse Salt.Chen.ESW_main_fold
  Salt.Chen.A2grid_window_le Salt.Chen.A2grid_window_additive
  Salt.Chen.razor_window_cost Salt.Chen.logRatio_A2_window_mem
  Salt.Chen.nonunit_forces_fst_dvd Salt.Chen.nuChen_sum_dvd_le
  Salt.Chen.middle_k_price Salt.Chen.middle_medium_box_price_at_y
  Salt.Chen.band_habs_row Salt.Chen.middle_k_M_le_two_y
  Salt.Chen.box_rows_at_op Salt.Chen.low_rows_at_op Salt.Chen.sym_rows_at_op
  Salt.Chen.band_price_rows_at_op Salt.Chen.blockAlphaSym_eq_blockAlphaLow_of_le
  Salt.Chen.middle_k_band_floor
  Salt.Chen.d0_window_of_XM_band Salt.Chen.medium_box_price_at_op_band
  Salt.Chen.sym_box_hprice_at_2pow_band Salt.Chen.low_box_hprice_at_2pow_band
  Salt.Chen.band_kfloor_of_live
  Salt.Chen.boundary_XM_raw Salt.Chen.boundary_log_bounds Salt.Chen.xm_sqrt_bounds
  Salt.Chen.blockAlphaLow_eq_zero_of_pieceN_le Salt.Chen.blockAlphaSym_eq_zero_of_pieceM_le
  Salt.Chen.box_carrier_eq_zero_above_cap Salt.Chen.y_lt_two_pow_succ_of_carrier
  Salt.Chen.hDsq_piece_of_kfloor Salt.Chen.hDsmall_at_op
  Salt.Chen.tower_budget Salt.Chen.hNum_close_of_tower
  Salt.Chen.box_hprice_at_2pow Salt.Chen.sym_box_hprice_at_2pow
  Salt.Chen.low_box_hprice_at_2pow Salt.Chen.maxBlock_eq_zero_of_eps_self
  Salt.Chen.crtClassW_coprime_of_mem
  Salt.Chen.d0_window_nonempty_lo Salt.Chen.medium_box_price_at_op_lo
  Salt.Chen.sym_box_price_at_op Salt.Chen.low_box_price_at_op
  Salt.Chen.cutoffEfoldTerm_eq_zero_of_gt
  Salt.Chen.PloW_honest Salt.Chen.hBVblocksW_discharge' Salt.Chen.diagAggW_le_honest
  Salt.Chen.rough_divisor_crumb Salt.Chen.nuChen_sum_divisors_le
  Salt.Chen.catch68_hSum_hNum_infeasible Salt.Chen.catch68_price_rows_nonneg
  Salt.Chen.hBVblocksW_discharge Salt.Chen.hNum_at_opW Salt.Chen.PloW_discharge
  Salt.Chen.blockBoxW_windowDisc_eq Salt.Chen.bandDiscW_le_three_pieces
  Salt.Chen.hBlockW_of_window_prices Salt.Chen.hrW_discharge
  Salt.Chen.twin_A1_lower_B_W Salt.Chen.twinA1_hBV_W Salt.Chen.twinA1W_rem_eq
  Salt.Chen.A1primeSumW_bridge Salt.Chen.crt_class_coprime
  Salt.Chen.tripleSum_le_cbar_final_W Salt.Chen.tripleSumW_equidist
  Salt.Chen.twin_A2_per_prime_W Salt.Chen.twinA2W_hcoef Salt.Chen.twinA2_hBVagg_W
  Salt.Chen.omegaPrimeSumW_decomp Salt.Chen.twinA2W_rem_eq
  Salt.Chen.chen_of_hypotheses_W Salt.Chen.chen_positivity_W Salt.Chen.chen_survivor_W
  Salt.Chen.factors_ge_z_of_sift_W Salt.Chen.razor_reduction_W Salt.Chen.stripPrimeSum_le_W
  Salt.Chen.aCount_ge_one_of_W Salt.Chen.residue_witness
  Salt.Chen.catch65_slot_torn Salt.Chen.catch65_no_H_at_odd_P
  Salt.Chen.catch64_op_boundary_infeasible Salt.Chen.catch64_D0_window_empty
  Salt.Chen.hyx_at_op Salt.Chen.sievePrimorial_dvd Salt.Chen.hDsq_row
  Salt.Chen.hfloor_row Salt.Chen.habs_row Salt.Chen.logRatio_A3_mem_range
  Salt.Chen.two_sqrt_primes_not_both_dvd Salt.Chen.efold_beta_le_single
  Salt.Chen.card_conductor_not_dvd_le Salt.Chen.general_BV_cutoff_sqrtD
  Salt.Chen.d0_window_nonempty
  Salt.Chen.medium_survivor_price_sqrtD Salt.Chen.hNum_at_op_sqrtD
  Salt.Chen.apDiscBilinCutoff_transpose Salt.Chen.medium_smallconductor_prime_side
  Salt.Chen.medium_band_price Salt.Chen.subblocked_box_price_reduced
  Salt.Chen.apDiscBilinCutoff_sum_alpha Salt.Chen.apDiscBilinCutoff_eq_zero_of_over
  Salt.Chen.subblocked_box_price
  Salt.Chen.cutoff_BV_at_op Salt.Chen.hCE_discharge Salt.Chen.diag_nu_crumb
  Salt.Chen.hmA1_normalized Salt.Chen.hmA2_normalized
  Salt.Chen.hmA3_normalized Salt.Chen.errorBundle_le
  Salt.Chen.normalized_package
  Salt.Chen.razor_scalar_margin Salt.Chen.razor_of_normalized
  Salt.Chen.hledger_at_certs
  Salt.Chen.logRatio_A1_mem Salt.Chen.logRatio_A3_mem
  Salt.Chen.Fchain_switch_le Salt.Chen.A2grid_sharp_le
  Salt.Chen.massSum_le_A2_sharp
  Salt.Chen.hSO_holds Salt.Chen.hSE_holds
  Salt.Chen.massSum_le_A2_final Salt.Chen.massOSum_le_A1_final
  Salt.Chen.Fchain_A2_final Salt.Chen.fchain_A1_final
  Salt.Chen.energy_shell_dvd Salt.Chen.bilinTwist_energy_le_dvd
  Salt.Chen.cbar_lt
  Salt.Chen.prime_sum_abel_antitone Salt.Chen.prime_sum_abel_monotone
  Salt.Chen.applicationA Salt.Chen.Ifun_closed_form Salt.Chen.Ifun_hasDerivAt
  Salt.Chen.Ifun_deriv_nonpos Salt.Chen.applicationB
  Salt.Chen.Ifun_integral_eq_cbar Salt.Chen.weightedPairSum_fibered
  Salt.Chen.tripleSum_le_weighted_pairSum' Salt.Chen.weightedPairSum'_le_cbar
  Salt.Chen.tripleSum_le_cbar_final
  Salt.Chen.apDiscBilinCutoff_orthogonality Salt.Chen.norm_apDiscBilinCutoff_le
  Salt.Chen.cutoffTwist_energy_le Salt.Chen.energy_shell_cutoff
  Salt.Chen.norm_blockAlphaLow_le_one Salt.Chen.lowRect_eq_apDiscBilinCutoff
  Salt.Chen.norm_blockAlphaSym_le_one Salt.Chen.symRect_eq_apDiscBilinCutoff
  Salt.Chen.Plo_discharge_priced
  Salt.Chen.symCard_two_mul Salt.Chen.bandCard_split
  Salt.Chen.bandDisc_eq_three Salt.Chen.bandDisc_le_three_pieces
  Salt.Chen.Plo_discharge
  Salt.Chen.sum_symm_ordered_split Salt.Chen.bandDiagCount_le
  Salt.Chen.blockHonestDisc_eq_sum_pieces Salt.Chen.abs_blockHonestDisc_le_sum_pieces
  Salt.Chen.card_pieces Salt.Chen.hBlock_of_window_prices
  Salt.Chen.cutoffTwist_le_sum_interval_twists Salt.Chen.interval_prime_twist_SW
  Salt.Chen.hSmallCut_discharge Salt.Chen.hsmall_pere_discharge
  Salt.Chen.general_BV_cutoff_unconditional
  Salt.Chen.hMainEnergy_cutoff_discharge Salt.Chen.cutoffEfoldTerm_reorg
  Salt.Chen.cutoffEfold_alpha_le Salt.Chen.hErrSum_cutoff_of_thresholds
  Salt.Chen.general_BV_cutoff_closed
  Salt.Chen.cutoffTwist_coprimeRestrict_primitive Salt.Chen.regroup_cutoff
  Salt.Chen.cutoff_hLargeDisc Salt.Chen.general_BV_cutoff_final
  Salt.Chen.hHD_of_generalBV_window
  Salt.Chen.smallconductor_window_perd Salt.Chen.smallconductor_window_sum
  Salt.Chen.blockBox_windowDisc_eq Salt.Chen.blockBox_windowed_pair_card
  Salt.Chen.block_energy_le_cutoff Salt.Chen.dyadic_large_reduction_cutoff
  Salt.Chen.dyadic_energy_le_cutoff Salt.Chen.dyadic_energy_le_cutoff_dvd
  Salt.Chen.S2set_subset_primesInWindow Salt.Chen.S1set_subset_insert
  Salt.Chen.tail187_integral_le
  Salt.Chen.per_pair_weighted_le Salt.Chen.tripleSum_le_weighted_pairSum
  Salt.Chen.cbar_inner_integral Salt.Chen.cbar_eq_double_integral
  Salt.Chen.W_switch_factor Salt.Chen.window_prod_lower Salt.Chen.window_prod_upper
  Salt.Chen.W_ratio_upper Salt.Chen.W_ratio_lower
  Salt.Chen.sum_inv_prime_window_ge Salt.Chen.twinWindow_mass_eq
  Salt.Chen.lambda_mass_lower Salt.Chen.lambda_mass_upper
  Salt.Chen.card_divisors_subpoly Salt.Chen.card_divisors_cube_root
  Salt.Chen.hdiv_discharge
  Salt.Chen.totient_ratio_le_log Salt.Chen.totient_lcm_mul_totient_gcd
  Salt.Chen.card_divisors_le_two_sqrt Salt.Chen.prod_ratio_le_card_succ
  Salt.Chen.block_energy_le_dvd Salt.Chen.dyadic_large_reduction_dvd
  Salt.Chen.geom_shell_sum_le_dvd Salt.Chen.dyadic_energy_le_dvd
  Salt.BV.bilinear_LS_shell_dvd Salt.BV.cs_over_finset_chi
  Salt.Chen.fseq2_upper_of_log_lower Salt.Chen.tail_integral_le
  Salt.Chen.budE_le Salt.Chen.budO_le
  Salt.Chen.cflatI_tight Salt.Chen.cflatI_lower
  Salt.Chen.massE_two_tight Salt.Chen.massE_two_lower Salt.Chen.Cphi2_tight
  Salt.Chen.fseq_odd_le_massE_div Salt.Chen.fseq_even_le_massO_div
  Salt.Chen.fseq_even_continuousOn Salt.Chen.massTail_eq_phiMoment
  Salt.Chen.massE_eq_flat_phiMoment Salt.Chen.Cphi1_le Salt.Chen.Cphi2_le
  Salt.Chen.fseq_odd_continuousOn Salt.Chen.massE_recursion
  Salt.Chen.cflatI_le_half Salt.Chen.massE_flat_split
  Salt.Chen.massE_two_le Salt.Chen.massE_two_le_half
  Salt.Chen.massSum_reindex Salt.Chen.massEvenSum_tail_le
  Salt.Chen.massSum_le_head_add_geomtail
  Salt.Chen.hBJS_window_min Salt.Chen.hBJS_funcbound_flat
  Salt.Chen.flat_h_contract
  Salt.Chen.geom_decay_pointwise Salt.Chen.geom_tail_ratio
  Salt.Chen.geom_tail_majorant Salt.Chen.fseq_le_leftEndpoint
  Salt.Chen.fseq_next_le_const Salt.Chen.evenSum_reindex
  Salt.Chen.fseq_evensum_tail_le Salt.Chen.evenSum_le_head_add_geomtail
  Salt.Chen.fseq_even_le_crude Salt.Chen.fseq_evensum_tail_crude
  Salt.Chen.fseq_two_le_const_demo
