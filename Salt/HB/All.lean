/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.QuadCharSum
import Salt.HB.RealPrimitive
import Salt.HB.RealPrimStructure
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
import Salt.HB.Lemma7Kappa
import Salt.HB.HSigmaComp
import Salt.HB.CharTrio
import Salt.HB.MOne
import Salt.Tactic.AuditAxioms
import Salt.HB.Lemma10
import Salt.HB.Lemma10Chain
import Salt.HB.EstermannRoad
import Salt.HB.Lemma3Floor
import Salt.HB.SieveWire
import Salt.HB.DoorBridge
import Salt.HB.CrownChain
import Salt.HB.CrownAssembly
import Salt.HB.CrownTheorem1

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
  Salt.HB.efShiftB_le_scale_sharp Salt.HB.efEnvelope_le_ledger_sharp
  Salt.HB.ledger_const_le_of_window Salt.HB.efEnvelope_zfr_eventually_le_sharp
  Salt.HB.integral_inv_mul_log_sq Salt.HB.tail_le_of_pointwise
  Salt.HB.logChiSum_tendsto_zfr_hundred
  Salt.HB.zeroMult_eq_one_of_window Salt.HB.zeroMult_eq_one_of_gap
  Salt.HB.zeroMult_eq_one_of_eta
  Salt.HB.hbG_prime Salt.HB.hbG_prime_dvd Salt.HB.hbG_le_four Salt.HB.one_sub_hbG_div_eq
  Salt.HB.mem_Pz Salt.HB.primeProdBelow_eq
  Salt.HB.hbSfac_le_one Salt.HB.one_sub_four_div_sq_le_hbSfac Salt.HB.hbSfac_pos
  Salt.HB.abs_log_hbSfac_le Salt.HB.tsum_tail_inv_sq_le Salt.HB.three_le_of_primesGt2
  Salt.HB.summable_eight_div_sq Salt.HB.abs_log_twinFactor_le Salt.HB.hbSfac_log_summable
  Salt.HB.hbWfac_pos Salt.HB.abs_log_hbWfac_le Salt.HB.hbWfac_log_summable
  Salt.HB.hbWfac_multipliable Salt.HB.hb_hsing
  Salt.HB.hb_rear_factor Salt.HB.hb_rear_factor_two Salt.HB.gt2Primes_eq_filter
  Salt.HB.hb_rear_prod_identity Salt.HB.hbCalpha_eq Salt.HB.alpha_primeFactors_prod_eq
  Salt.HB.qFactors_low_prod_eq Salt.HB.hbS1_eq Salt.HB.hbKappaTail_split
  Salt.HB.one_sub_sum_le_prod_one_sub Salt.HB.abs_prod_one_sub_two_div_sub_one_le
  Salt.HB.hb_hrear Salt.HB.hb_L2_at_split_point_concrete
  Salt.HB.chiRe_eq_one_or_neg_one_or_zero Salt.HB.chiRe_eq_zero_iff_map_eq_zero
  Salt.HB.chiRe_eq_zero_iff_not_coprime Salt.HB.chiRe_prime_eq_zero_iff_dvd
  Salt.HB.hb_hchi01 Salt.HB.hb_hchi0
  Salt.HB.hbL1_eq Salt.HB.prod_one_sub_chiRe_div_Pz_pos Salt.HB.hbL1_pos
  Salt.HB.Pz_eq_union_windowPrimes Salt.HB.Pz_disjoint_windowPrimes
  Salt.HB.hbEulerProdBelow_split Salt.HB.tendsto_hbEulerProdBelow_hbL1
  Salt.HB.hbL1_eq_of_tendsto Salt.HB.hbL1_split_indep
  Salt.HB.hb_L2_at_split_point_char Salt.HB.hb_L2_at_split_point_charTrio
  Salt.HB.quadraticChar_sum_two_forms_eq Salt.HB.quadraticChar_sum_two_forms_bound_one
  Salt.HB.legendre_sum_two_forms_bound_one
  Salt.HB.chi4_sum_two_forms_le_gcd Salt.HB.chi8_sum_two_forms_le_gcd
  Salt.HB.chi8'_sum_two_forms_le_gcd
  Salt.HB.sum_range_nsmul_of_periodic Salt.HB.sum_range_eq_nsmul_of_dvd_of_periodic
  Salt.HB.sum_range_natCast_eq_sum_univ Salt.HB.sum_two_forms_range_eq_univ
  Salt.HB.gcd_val_castHom Salt.HB.HasTwoFormGcdBound.mul
  Salt.HB.hasTwoFormGcdBound_of_modulus_one
  Salt.HB.hasTwoFormGcdBound_chi4 Salt.HB.hasTwoFormGcdBound_chi8
  Salt.HB.hasTwoFormGcdBound_chi8'
  Salt.HB.jacobiChar_prime Salt.HB.hasTwoFormGcdBound_jacobiChar_prime
  Salt.HB.hasTwoFormGcdBound_jacobiChar Salt.HB.sum_two_forms_le_gcd_of_split
  Salt.HB.sum_class_eq_zero_of_isPrimitive
  -- node WEIL-TRIO-W4-a (Salt/HB/RealPrimStructure.lean): the real primitive structure theorem
  Salt.HB.isQuadratic_of_int Salt.HB.int_apply_unit
  Salt.HB.chineseRemainder_apply Salt.HB.crtIn₁ Salt.HB.crtIn₂
  Salt.HB.crtFactor₁ Salt.HB.crtFactor₂ Salt.HB.crtFactor_apply
  Salt.HB.crtFactor₁_unique Salt.HB.crtFactor₂_unique
  Salt.HB.crtFactor₁_isPrimitive Salt.HB.crtFactor₂_isPrimitive
  Salt.HB.not_isPrimitive_of_odd_prime_pow Salt.HB.eq_quadraticChar_of_isPrimitive
  Salt.HB.not_isPrimitive_two Salt.HB.exists_odd_sq_sub_dvd Salt.HB.not_isPrimitive_two_pow
  Salt.HB.isPrimitive_two_pow_of_not_factorsThrough
  Salt.HB.isPrimitive_chi4 Salt.HB.isPrimitive_chi8 Salt.HB.isPrimitive_chi8'
  Salt.HB.eq_chi4_of_isPrimitive Salt.HB.eq_chi8_or_chi8'_of_isPrimitive
  Salt.HB.squarefree_and_eq_jacobiChar_of_isPrimitive
  Salt.HB.exists_split_of_isPrimitive Salt.HB.exists_split_of_isPrimitive_enumerated
  Salt.HB.structure_of_isPrimitive Salt.HB.sum_two_forms_le_gcd_of_isPrimitive
  -- node HSIGMA-COMP (Salt/HB/HSigmaComp.lean): the repulsion floor composed into
  -- `hb_L1_one_sided`'s `hσ'r` — the `hσ'r` obligation ONLY (see the file's scope fence)
  Salt.HB.sqrt_quad_of_threshold Salt.HB.repulsion_floor_gives_hsigma
  Salt.HB.hb_L1_one_sided_at_repulsion_floor Salt.HB.hsigma_largeness_satisfiable
  -- node N7 WAVE A (Salt/HB/Lemma10.lean): HB Lemma 10's rung (7.5) — the trivial
  -- bound on `S_m`, stated EXACTLY (‖S_m‖ ≤ #I, no `≪`, no `E`) per gate ruling R-A1,
  -- with the `E + 1` passage as its own lemma so the slack is priced in the open
  Salt.N7.norm_lem10ExpSum_le_card Salt.N7.lem10ExpSum_attains_card
  Salt.N7.card_le_of_mem_Ioc
  -- the divisor bookkeeping (gap row 4's open half): d(k)·d(k₀)·d(k₁) ≤ d(k)³
  Salt.N7.card_divisors_le_of_dvd Salt.N7.divisor_triple_le_cube
  Salt.N7.divisor_triple_attains_cube
  -- node N7 WAVE A cont. (Salt/HB/Lemma10Chain.lean): HB (7.6)–(7.8) — the Abel transfer
  -- with the phase variation as a hypothesis (R-A3), the completion by additive characters
  -- mod `k` with Estermann spent once (the 2-adic factor carried literally as `√(2^{v₂ k})`,
  -- collapsed at the road modulus by the consumer), the dyadic `m`-sum; numerals 8 / 16
  -- from the written ledger, unmoved.  Lemma 10 itself (the p.223 assembly at
  -- `K = 2 + k^{1/4}`) is NOT here — it is the next wave, and the file header says so.
  Salt.N7.invMod Salt.N7.hbPhase Salt.N7.hbPhase' Salt.N7.klPhaseSum Salt.N7.lem10Coeff
  Salt.N7.e_add_intCast Salt.N7.norm_e_sub_le Salt.N7.sum_Ioc_succ_top_int
  Salt.N7.sum_Ico_succ_top_int Salt.N7.sum_Ioc_abel_int_ico Salt.N7.sum_Ico_eq_sum_Ioc_pred
  Salt.N7.sum_Ioc_abel_int Salt.N7.lem10ExpSum_eq_sum_coeff Salt.N7.lem10_abel_transfer
  Salt.N7.var_const Salt.N7.var_inv Salt.N7.lem10ExpSum_kl_mul
  Salt.N7.stdAddChar_intCast_eq_e Salt.N7.isUnit_intCast_iff Salt.N7.klPhaseSum_eq_kloosterman
  Salt.N7.sum_zmod_val_eq_sum_range Salt.N7.sum_range_mul_mod Salt.N7.sum_Ico_reflect
  Salt.N7.gcd_natAbs_eq_of_dvd_sub Salt.N7.sqrt_gcd_mul_le Salt.N7.dist₁_shift_lower
  Salt.N7.sum_sqrt_gcd_min_le Salt.N7.klPhaseSum_bound Salt.N7.lem10_dyadic_bound
  Salt.N7.e_neg_eq_conj Salt.N7.norm_lem10ExpSum_neg
  -- node ESTERMANN-2ADIC (Salt/HB/EstermannRoad.lean): the road-modulus close — HB (7.1)
  -- with NO 2-adic factor, the `q`-side valuation hypothesis discharged from primitivity.
  -- The Weil-side rows D1′–D4 audit in `Salt/Weil/All.lean`.
  Salt.HB.factorization_two_le_three_of_isPrimitive
  Salt.HB.norm_kloosterman_estermann_road_of_isPrimitive
  -- ⛔ NEGATIVE CONTROL — NOT A BOUND, and it must not be read as one. This row proves the
  -- D1′ inequality `φ(2^e) ≤ d(2^e)·√(2^e)` FAILS at `e = 9`; its content is the failure of
  -- a bound, so it can never be composed into an estimate. It is here so the `≤ 8` carried
  -- by every row above reads as the limit of the method rather than unexamined slack.
  Salt.HB.two_pow_totient_exceeds_estermann_at_nine
  -- node N3 JOIN (Salt/HB/Lemma3Floor.lean): HB Lemma 3 at the repulsion floor — the
  -- FLOOR antecedent of `hb_lemma3_unconditional_absorbed` discharged from a
  -- `repulsionCeiling` hypothesis, the mirror of HSIGMA-COMP at `B = 2b·log Q/L`.  The
  -- `Sinv` antecedent is deliberately still carried (priced by `invSq_sum_split_le`), and
  -- `hceil` is consumed, not proved.  A join is not the engine.
  Salt.HB.repulsion_floor_gives_lemma3_binders
  Salt.HB.hb_lemma3_at_repulsion_floor
  -- node N5 WIRING (Salt/HB/SieveWire.lean): the star step's honest window built as an
  -- `HBSieveData` (the real character of a quadratic χ via `Salt.MR.e4a_toR`), HB's `P`
  -- identified with the complex χ's fibre, the two `S⁽³⁾`s identified (`rfl`), and the
  -- dim-4 sandwich instantiated there.  A wire, not an estimate; the window the reduction
  -- chain is stated on is N8's decision, not this file's.
  Salt.HB.chiReChar Salt.HB.chiReChar_apply Salt.HB.chiReChar_prime
  Salt.HB.hbSiftSet_chiReChar Salt.HB.hbData Salt.HB.hbData_P Salt.HB.hbData_S3_eq
  Salt.HB.hbData_fl_sandwich
  -- node N11 (Salt/HB/DoorBridge.lean): the DOOR half of the fulcrum — from HB's own
  -- carrier `S1 (Ioc x (2x))` to TPC via the landed survivor extraction on `p1PrimeSum`,
  -- the proper-prime-power tail split off and bounded (crude by design).  The `S1` LOWER
  -- bound (Theorem 1, N9) is NOT here; a positive `S1 − ppTail` at arbitrarily large `x`
  -- is the HYPOTHESIS of these rows, never their claim.
  Salt.HB.twinPrimeConjecture_of_frequently_pos Salt.HB.twinWindow_two_mul_add_two
  Salt.HB.ppTail_le Salt.HB.S1_Ioc_le_p1PrimeSum_add_ppTail
  Salt.HB.twin_of_ppTail_lt_S1 Salt.HB.twinPrimeConjecture_of_frequently_S1

/-! ## node N8 — THE §2 ASSEMBLY, EXECUTED (freeze v2 2026-09-03; landed 2026-09-04; `h2c/crown-n8`)

Two modules, one per executor: `Salt/HB/CrownChain.lean` (the reduction `S⁽⁰⁾ → S⁽³⁾` on the
crown window `l2cWindow`, the swap `S⁽⁰⁾ → S⁽¹⁾`, HB Lemma 4 with the pretense sum SYMBOLIC and
the divisor constant bound BEFORE `z x`, HB Lemma 3 at the pretense-sum level at the repulsion
floor on the `(L1)` packet at `Lp := 2L`) and `Salt/HB/CrownAssembly.lean` (the wire `hbDataN8`
with the vacuous `(l, P) = 1` filter, HB Lemma 6 with literal constants, HB Lemma 5 as the
INTERFACE `Lemma5Eval` that Wave C-2 fills, the p.200 assembly both signs, the `κS₁ = W` wire).
All 27 theorems are proved, sorry-free, with no statement changed from the freeze and no new
axiom (the wave: two Opus executors, one per file, 2026-09-04).  N8 assembles nothing:
`hEngine` stays a binder until N7 (Waves A/B/C), N8, N4's composition wave, the `z` witness,
N9, N10 and N12 land (N11 is closed).

**ONE NAME PER COMMAND, deliberately.**  `#audit_axioms` aborts at its FIRST offender
(`throwError` inside the `for`), so a single 35-name command on this branch would resolve
exactly one name and hide a typo in the other 34 behind the same red.  As 35 commands the
branch emits 27 errors (`sorryAx`) and 8 ✓ (the defs, the structure, the `rfl` row), every
name resolved; at the wave's landing it read 35 ✓.  Executors never edit these rows.
-/

section N8
open Salt.Tactic
#audit_axioms Salt.HB.l2cWindow_subset_honestWindow
#audit_axioms Salt.HB.S1_l2cWindow_le_S1_Ioc
#audit_axioms Salt.HB.S1_Ioc_sub_S1_l2cWindow_le
#audit_axioms Salt.HB.S2_sub_S3_window_of_tau
#audit_axioms Salt.HB.S2_sub_S3_l2cWindow
#audit_axioms Salt.HB.lemma4Err
#audit_axioms Salt.HB.hb_lemma4_l2cWindow
#audit_axioms Salt.HB.pretenseSum_at_repulsion_floor

#audit_axioms Salt.HB.l2cWindow_coprime_hbP
#audit_axioms Salt.HB.hbDataN8
#audit_axioms Salt.HB.hbDataN8_P
#audit_axioms Salt.HB.hbDataN8_S3_eq
#audit_axioms Salt.HB.hbDataN8_sandwich
#audit_axioms Salt.HB.IsAdditiveOn
#audit_axioms Salt.HB.deltaSum_nuG_eq
#audit_axioms Salt.HB.deltaSum_nuG_nonneg
#audit_axioms Salt.HB.lamSum_nuG_sub_W_bounds
#audit_axioms Salt.HB.deltaSum_nuG_mul_additive
#audit_axioms Salt.HB.deltaSum_nuG_mul_additive_le
#audit_axioms Salt.HB.deltaSum_nuG_mul_sq_additive_le
#audit_axioms Salt.HB.moebSum_nuG_mul_additive
#audit_axioms Salt.HB.moebSum_nuG_mul_additive_le
#audit_axioms Salt.HB.moebSum_nuG_mul_sq_additive_le
#audit_axioms Salt.HB.failSet_log_le
#audit_axioms Salt.HB.hb_transfer_additive
#audit_axioms Salt.HB.hb_transfer_sq_additive
#audit_axioms Salt.HB.Lemma5Eval
#audit_axioms Salt.HB.hbG_div_eq_nuG
#audit_axioms Salt.HB.n8ErrSum
#audit_axioms Salt.HB.mertens2C
#audit_axioms Salt.HB.n8ErrSum_le
#audit_axioms Salt.HB.n8C6
#audit_axioms Salt.HB.hb_p200_upper
#audit_axioms Salt.HB.hb_p200_lower
#audit_axioms Salt.HB.hbS1_eq_W
end N8

/-! ## N9 — HB Theorem 1 and the door hand-over (`Salt/HB/CrownTheorem1.lean`), STATEMENTS ONLY

The crown's N9 freeze (2026-09-04): HB 1983 Theorem 1 at the twin instance (`hb_theorem1`),
the zero side of N4's `(L1)`/N8's L3 packet made consumable (§3 there), N4's `(L2)` composition
(§4), the assembly (§5), and the door hand-over to the crown FAMILY `HeathBrownDichotomyPoly k`
(§6) — every theorem left unproved BY DESIGN until the wave landed.  v2 (2026-09-04, on the
refuter verdict): 68 rows — 42 theorems + 26 defs/structures; the expected reading before the
wave was 51 red (the 42 theorems + the 9 defs downstream of `dh_repulsion_tall_at`'s placeholder:
`dhC n9Ell n9EllAt n9Floor hbZ0 hbZ hbS N9Regime n9Cq`) + 17 ✓.  THE WAVE LANDED 2026-09-04
(four executors, 42/42, zero flags): the reading is 68 ✓.  The first row is the one
theorem appended to a landed file (`Salt/SW/TBalTall.lean`, the helm's ruling).  ONE NAME PER
COMMAND, as for N8 (the audit aborts at its first offender).  Executors never edit these rows.
-/

section N9
open Salt.Tactic
#audit_axioms Salt.HB.dhB
#audit_axioms Salt.HB.dhK
#audit_axioms Salt.SW.dh_repulsion_tall_of_floor
#audit_axioms Salt.HB.dh_repulsion_tall_at
#audit_axioms Salt.HB.dhC
#audit_axioms Salt.HB.dh_spec
#audit_axioms Salt.HB.invSqC
#audit_axioms Salt.HB.invSqC_spec
#audit_axioms Salt.HB.merC
#audit_axioms Salt.HB.merC_spec
#audit_axioms Salt.HB.segC
#audit_axioms Salt.HB.segC_spec
#audit_axioms Salt.HB.n9Ell
#audit_axioms Salt.HB.n9EllAt
#audit_axioms Salt.HB.n9EllAt_two
#audit_axioms Salt.HB.n9Floor
#audit_axioms Salt.HB.n9Cs
#audit_axioms Salt.HB.hbZ0A
#audit_axioms Salt.HB.hbZ0
#audit_axioms Salt.HB.hbZ
#audit_axioms Salt.HB.hbS
#audit_axioms Salt.HB.hbLL
#audit_axioms Salt.HB.hbKappaN9
#audit_axioms Salt.HB.n9E0
#audit_axioms Salt.HB.N9Regime
#audit_axioms Salt.HB.N7Exit
#audit_axioms Salt.HB.n9K
#audit_axioms Salt.HB.hbZ_bounds
#audit_axioms Salt.HB.hbZ_packet
#audit_axioms Salt.HB.re_le_beta0_of_ne
#audit_axioms Salt.HB.dh_repulsion_tall_real
#audit_axioms Salt.HB.dh_ceiling_box
#audit_axioms Salt.HB.dh_floor_ball
#audit_axioms Salt.HB.sinv_ball
#audit_axioms Salt.HB.hb_zero_data
#audit_axioms Salt.HB.hb_L1_lower_at_hb_point
#audit_axioms Salt.HB.neg_re_logDeriv_LFunction_ge
#audit_axioms Salt.HB.neg_re_logDeriv_differenced_mult_ge
#audit_axioms Salt.HB.hb_L1_upper_at_hb_point
#audit_axioms Salt.HB.pretenseSum_at_hb_point
#audit_axioms Salt.HB.chiOne_kill_at_hb_point
#audit_axioms Salt.HB.real_zeros_below_zfrCeil
#audit_axioms Salt.HB.logChiSum_tail_at_window
#audit_axioms Salt.HB.hbEulerLog_tendsto
#audit_axioms Salt.HB.hcorr_at_split
#audit_axioms Salt.HB.n9K2
#audit_axioms Salt.HB.hb_L2_at_hb_point
#audit_axioms Salt.HB.card_divisors_le_rpow_explicit
#audit_axioms Salt.HB.hb_lemma4_at_hb_point
#audit_axioms Salt.HB.n9K3
#audit_axioms Salt.HB.hb_S3_at_hb_point
#audit_axioms Salt.HB.hb_theorem1
#audit_axioms Salt.HB.hb_theorem1_lower
#audit_axioms Salt.HB.FulcrumQualityPoly
#audit_axioms Salt.HB.NoSiegelZerosPoly
#audit_axioms Salt.HB.HeathBrownDichotomyPoly
#audit_axioms Salt.HB.fulcrumQualityPoly_one_iff
#audit_axioms Salt.HB.noSiegelZerosPoly_one_iff
#audit_axioms Salt.HB.heathBrownDichotomyPoly_one_iff
#audit_axioms Salt.HB.three_le_of_ne_one
#audit_axioms Salt.HB.noSiegelZerosPoly_mono
#audit_axioms Salt.HB.not_fulcrumPoly_implies_noSiegelZerosPoly
#audit_axioms Salt.HB.fulcrum_dichotomy_poly
#audit_axioms Salt.HB.beta0_max_of_zero
#audit_axioms Salt.HB.n9Cq
#audit_axioms Salt.HB.crown_handover
#audit_axioms Salt.HB.hEngine_poly_of_N7
#audit_axioms Salt.HB.heathBrownDichotomyPoly_of_N7
end N9
