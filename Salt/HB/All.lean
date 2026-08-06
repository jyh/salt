/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.QuadCharSum
import Salt.HB.TwistChain
import Salt.HB.TwistChainC
import Salt.HB.Transfer
import Salt.HB.PairSieve
import Salt.HB.PairInstance
import Salt.HB.PairSieveMixed
import Salt.HB.TransferFull
import Salt.HB.StarStep
import Salt.HB.StarWindow
import Salt.HB.MixedCount
import Salt.HB.SignChain
import Salt.HB.SignLiouville
import Salt.HB.SignRate
import Salt.HB.L2cCore
import Salt.HB.L2cEL
import Salt.HB.L2cELT1
import Salt.HB.L2cELT2
import Salt.HB.L2cELT3
import Salt.HB.L2cELT3F
import Salt.HB.L2cELTsw
import Salt.HB.L2cELJunk
import Salt.HB.L2cEven
import Salt.HB.L2cER
import Salt.HB.L2cERT1
import Salt.HB.L2cERT2
import Salt.HB.L2cERT3
import Salt.HB.L2cERTsw
import Salt.HB.L2cMaster
import Salt.HB.L2cMop
import Salt.HB.L2cGlue
import Salt.HB.L2cEngineRoute
import Salt.HB.L2cMasterUncond
import Salt.HB.RosserDim4
import Salt.HB.RosserDim4FL
import Salt.HB.RosserDim4Instance
import Salt.HB.PretenseSumProof
import Salt.HB.TwistedMertens
import Salt.HB.Lemma3Uncond
import Salt.HB.Lemma7L
import Salt.HB.Lemma7EF
import Salt.HB.Lemma7F
import Salt.HB.Lemma7Prod
import Salt.HB.Lemma7
import Salt.Tactic.AuditAxioms

/-!
# The Heath-Brown track (`HB`) — aggregate import

HB-ENGINE: the formalization of Heath-Brown, *Prime twins and
Siegel zeros* (Proc. LMS (3) 47 (1983) 193–224) — infinitely many
Siegel zeros imply infinitely many prime twins. The campaign map
(seven work packages, re-frozen against the source PDF) lives in
`docs/exploration/s3-hb3-design.md`; the WP2 L-function nodes land
in `Salt/SW/`; the Kloosterman/Weil inputs are banked in
`Salt/Weil/` (HB-FOUND).
-/

open Salt.Tactic in
#audit_axioms Salt.HB.S2_sub_S3_honestWindow
  Salt.HB.hstar_window
  Salt.HB.hb_lemma2
  Salt.HB.S2_sub_S1_le
  Salt.HB.boundingSum_ge_phi_log_sq
  Salt.HB.pairSieveMixed_lemma8
  Salt.HB.pairSieve_lemma8
  Salt.HB.hb_lemma8
  Salt.HB.hbPairSieve
  Salt.HB.card_apResidues
  Salt.HB.hbPairSieve_rem_abs_le
  Salt.HB.hbPairSieve_errSum_le
  Salt.HB.hb_lemma8'_unconditional
  Salt.HB.card_mixResidues
  Salt.HB.rhoK_prime
  Salt.HB.mixPairSieve_rem_abs_le
  Salt.HB.mixPairSieve_errSum_le
  Salt.HB.boundingSum_ge_log_sq_of_twinDensity
  Salt.HB.LamStar_nonneg
  Salt.HB.vonMangoldt_le_LamTilde
  Salt.HB.LamTilde_eq_fChi_conv
  Salt.HB.LamStar_eq_fStar_conv
  Salt.HB.eq_nPlus_mul_nMinus
  Salt.HB.coprime_nPlus_nMinus
  Salt.HB.LamTilde_sub_vonMangoldt_le
  Salt.HB.LamTilde_eq_sum_nPlus
  Salt.HB.S1_le_S2
  Salt.HB.S2_sub_S1_le
  Salt.HB.overshoot_sum_nonneg
  Salt.HB.twin_termwise_le
  Salt.HB.overshootLog_eq_zero_of_nMinus_ne_one
  Salt.HB.overshootPP_eq_zero_of_not_isPrimePow
  Salt.HB.coprimeSupport_window
  Salt.HB.quadraticChar_sum_two_forms_bound
  Salt.HB.quadraticChar_sum_mul_shift
  Salt.HB.quadraticChar_sum_two_forms_trivial
  Salt.HB.legendre_sum_mul_shift
  Salt.HB.legendre_sum_two_forms_bound
  Salt.HB.legendre_sum_two_forms_trivial
  Salt.HB.S1_le_S2Gen
  Salt.HB.S2Gen_sub_S1_eq
  Salt.HB.LamTildeGen_lamR_eq_vonMangoldt
  Salt.HB.S2Gen_lamR_eq_S1
  Salt.HB.overshootExactGen_lamR
  Salt.HB.PretenseSumGen_lamR_eq_zero
  Salt.HB.neutrality_rate
  Salt.HB.EL_T1_bound
  Salt.HB.EL_T2_bound
  Salt.HB.EL_T3F_bound
  Salt.HB.EL_Tsw_bound
  Salt.HB.EL_cJunk_bound
  Salt.HB.ER_wJunk_bound
  Salt.HB.EL_corners_bound
  Salt.HB.EL_evenCorner_bound
  Salt.HB.ER_squarefull_junk
  Salt.HB.ER_T1'_bound_mixed
  Salt.HB.ER_T2'_bound
  Salt.HB.ER_T3'_bound
  Salt.HB.ER_Tsw'_bound_of_count
  Salt.HB.hb_l2c_master_of_count
  Salt.HB.engineRoute_card_right
  Salt.HB.ER_Tsw'_bound_unconditional
  Salt.HB.cPairSum_bound_unconditional
  Salt.HB.EL_uncov_bound_unconditional
  Salt.HB.hb_l2c_master_unconditional
  Salt.HB.chi_log_le_level
  Salt.HB.chi_le_rpow_level
  Salt.HB.Gdens_le_four
  Salt.HB.log_Wratio_le_ladder_dim4
  Salt.HB.M_bound_gen
  Salt.HB.hMert_dim4
  Salt.HB.brun_lower_dim4
  Salt.HB.brun_upper_dim4
  Salt.HB.flB_level_bound
  Salt.HB.fl_defect_le
  Salt.HB.fl_defect_le_upper
  Salt.HB.flConst_quarter_le
  Salt.HB.fl_dim4_lower
  Salt.HB.fl_dim4_upper
  Salt.HB.firstFailure_decomposition
  Salt.HB.exists_firstFailure
  Salt.HB.failSet_unique
  Salt.HB.failSet_le_rpow
  Salt.HB.failSet_forced_count
  Salt.HB.failSet_moebius
  Salt.HB.firstFailure_decomposition_signed
  Salt.HB.perDelta_transfer
  Salt.HB.transfer_of_decomposition
  Salt.HB.hb_perDelta_transfer
  Salt.HB.nuG_isMultiplicative
  Salt.HB.hbSieve
  Salt.HB.hbP_squarefree
  Salt.HB.hbP_chi
  Salt.HB.hb_sandwich_lower
  Salt.HB.hb_sandwich_upper
  Salt.HB.moebSum_nu_eq_W
  Salt.HB.mainSum_chi_eq_W_sub_correction
  Salt.HB.hb_levelRatio_eq
  Salt.HB.hb_fl_lower
  Salt.HB.hb_fl_upper
  Salt.HB.hb_transfer
  Salt.HB.hbSieve_fl_sandwich
  Salt.HB.two_mul_pretenseSum_le_vmPairW
  Salt.HB.two_mul_pretenseSum_le_mertens
  Salt.HB.two_mul_pretenseSum_le_vmPairS
  Salt.HB.inv_le_rpow_mul_rpow_neg
  Salt.HB.pole_cancel_le
  Salt.HB.hb_rate_at_optimal_a
  Salt.HB.hb_rate_optimal
  Salt.HB.one_sub_ceiling_le_dist_one
  Salt.HB.nearOne_multTotal_le
  Salt.HB.nearOne_invSq_sum_le
  Salt.HB.pretenseSum_nonneg
  Salt.HB.pretenseSum_le
  Salt.HB.pretenseSum_le_series
  Salt.HB.pretenseSum_le_hb_rate
  Salt.HB.pretenseSum_le_hb_rate_rpow
  Salt.HB.pretenseSum_le_quarter_rate
  Salt.HB.hb_lemma2_of_pretenseSum_le
  Salt.HB.hb_lemma2_at_hb_rate
  Salt.HB.logDeriv_LFunction_eq_LSeries
  Salt.HB.neg_re_logDeriv_LFunction_eq_tsum
  Salt.HB.neg_re_logDeriv_zeta_eq_tsum
  Salt.HB.neg_re_logDeriv_LFunction_le
  Salt.HB.vmPairS_le_pole
  Salt.HB.norm_inv_sub_inv
  Salt.HB.dist_one_lower_of_floor
  Salt.HB.per_zero_inv_diff_le
  Salt.HB.neg_re_logDeriv_differenced
  Salt.HB.invSq_sum_split_le
  Salt.HB.hbCoreRate_at_operating_point
  Salt.HB.hbCoreRate_at_hb_optimum
  Salt.HB.vmPairS_le_hb_core
  Salt.HB.pretenseSum_le_differenced
  Salt.HB.hb_lemma3_final
  Salt.HB.hb_lemma3_unconditional
  Salt.HB.wLog_nonneg Salt.HB.wLog'_nonpos Salt.HB.hasDerivAt_wLog
  Salt.HB.sum_Icc_zero_eq_psiChiR Salt.HB.abel_logChiSum Salt.HB.mainTerm_ibp
  Salt.HB.logChiSum_add_mainTerm_norm_le
  Salt.HB.psiDefect_norm_le_of_ef
  Salt.HB.rpow_c_add_one Salt.HB.efShiftError_le_efShiftBound
  Salt.HB.re_le_repulsionCeiling_of_ne Salt.HB.exists_repulsion_ceiling_of_ne
  Salt.HB.re_le_of_zeroFree_of_ne Salt.HB.psiDefect_norm_le_rangeA
  Salt.HB.two_le_efT0 Salt.HB.efH_pos Salt.HB.psiDefect_norm_le_envelope
  Salt.HB.continuousOn_efEnvelope Salt.HB.efShiftB_nonneg Salt.HB.efShiftBound_nonneg
  Salt.HB.efEnvelope_nonneg Salt.HB.logChiSum_composite_of_ceiling
  Salt.HB.logChiSum_add Salt.HB.intervalIntegrable_rpow_div_log
  Salt.HB.integrableOn_rpow_div_log Salt.HB.logChiSum_tendsto_of_envelope
  Salt.HB.integrableOn_expNeg_div_Ioi Salt.HB.integrableOn_expNeg_mul_log_Ioi_zero
  Salt.HB.hasDerivAt_expNeg_mul_log Salt.HB.expIntegral_ibp Salt.HB.expIntegral_eq_sub
  Salt.HB.abs_integral_expNeg_mul_log_Ioc_le Salt.HB.expIntegral_sub_log_gamma_abs_le
  Salt.HB.integral_rpow_div_log_Ioi_eq_expIntegral Salt.HB.hb_F_tail_integral
  Salt.HB.chi_eq_ofReal_chiRe Salt.HB.chiRe_eq_two_mul_ind_sub Salt.HB.logChiSum_re_eq
  Salt.HB.chiOne_prime_logWeighted_le Salt.HB.rankin_floor_le
  Salt.HB.two_mul_pretenseSum_le_at_window Salt.HB.hb_chiOne_kill_at_window
  Salt.HB.hb_logF_at_split_point
  Salt.HB.chiReTB_abs_le_one Salt.HB.log_hbEulerProd Salt.HB.hbEulerProd_pos
  Salt.HB.hbLogF_eq_of_tendsto Salt.HB.tendsto_hbEulerProd_hbF
  Salt.HB.abs_neg_log_one_sub_sub_self_le Salt.HB.hbEulerLog_sub_primeSum_termwise
  Salt.HB.sum_two_div_sq_windowPrimes_le Salt.HB.ppDefect_nonneg
  Salt.HB.logChiSum_re_eq_sum Salt.HB.logChiSum_re_sub_primeSum_le
  Salt.HB.exp_two_mul_log Salt.HB.sq_eq_exp_mul_one_add Salt.HB.abs_one_add_mul_sub_one_le
  Salt.HB.primeProdBelow_pos Salt.HB.abs_log_log_floor_sub_le Salt.HB.hb_mertens_third_real
  Salt.HB.one_lt_log_three Salt.HB.log_le_two_mul_log_floor
  Salt.HB.sum_recip_windowPrimes_eq Salt.HB.sum_recip_largePrimeFactors_le
  Salt.HB.hb_coprime_segment Salt.HB.hb_hseg
  Salt.HB.hb_hcorr_finite Salt.HB.hb_hcorr_at_limit
  Salt.HB.sum_ppCoef_eq Salt.HB.sum_ppCoef_nat_eq Salt.HB.psi_sub_theta_nonneg
  Salt.HB.abs_wLog'_mul_psi_sub_theta_le Salt.HB.ppDefect_le Salt.HB.ppDefect_le'
  Salt.HB.hb_hcorr_closed Salt.HB.hb_hseg_closed
  Salt.HB.hb_L2_core Salt.HB.hb_L2_at_split_point
