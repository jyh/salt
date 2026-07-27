/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Dist
import Salt.MR.DoorDischarge
import Salt.MR.L2MVT
import Salt.MR.NonPret
import Salt.MR.TuranKubilius
import Salt.MR.ZetaLowerAllT
import Salt.MR.ZetaPowLower
import Salt.MR.PrimeSigmaShift
import Salt.MR.HalaszCore
import Salt.MR.PrimeTail
import Salt.MR.OneLinePowGrowth
import Salt.MR.ShiuMoment
import Salt.MR.MVHilbert
import Salt.MR.NonPretClose
import Salt.MR.DistHalasz
import Salt.MR.Decomp
import Salt.MR.MVCore
import Salt.MR.TypicalDensity
import Salt.MR.HalaszLambda
import Salt.MR.HalaszKernel
import Salt.MR.HalaszSeam
import Salt.MR.HalaszRep
import Salt.MR.MVCore2
import Salt.MR.PretentiousTriangle
import Salt.MR.HalaszContour
import Salt.MR.ParsevalSL
import Salt.MR.PerronSharp
import Salt.MR.HalaszRepAsm
import Salt.MR.HalaszFactor
import Salt.MR.DistSplit
import Salt.MR.PerronTrunc
import Salt.MR.ParsevalAsm
import Salt.MR.PropA3Core
import Salt.MR.PerronZones
import Salt.MR.MomentsA2
import Salt.MR.RamareDpoly
import Salt.MR.LargeValues
import Salt.MR.RamareWindows
import Salt.MR.HalaszPrimes
import Salt.MR.HalaszIntegers
import Salt.MR.VanDerCorput
import Salt.MR.MidBand
import Salt.MR.LargeValueCount
import Salt.MR.MultShiu
import Salt.MR.HalaszPrimesCore
import Salt.MR.HalaszIdentity
import Salt.MR.HalaszHead
import Salt.MR.DistWindow
import Salt.MR.Prop1Assembly
import Salt.MR.RampSliver
import Salt.MR.ShortIntervalPsi
import Salt.MR.HExit
import Salt.MR.HeadGrade
import Salt.MR.GrandComp
import Salt.MR.AnnHead
import Salt.MR.Lemma14Bridge
import Salt.MR.Lemma14Taylor
import Salt.MR.Lemma14Vtail
import Salt.MR.Lemma14
import Salt.MR.ChiFloor
import Salt.MR.PerronLimit
import Salt.MR.SeamSplit
import Salt.MR.ChiEuler
import Salt.MR.ChiFloorLow
import Salt.MR.SeamBallWeighted
import Salt.MR.HalaszDirect
import Salt.MR.ChiLLower
import Salt.MR.PerronMeanSq
import Salt.MR.VdCSocket
import Salt.MR.RamareErr
import Salt.MR.USetThin
import Salt.MR.RamareMR
import Salt.MR.SevenEighths
import Salt.MR.Renormalise
import Salt.MR.JFactor
import Salt.MR.BallSup
import Salt.MR.SmallStones
import Salt.MR.Prop21Uniform
import Salt.MR.LambdaMass
import Salt.MR.WindowBridge
import Salt.MR.PretSupply
import Salt.MR.CenterCore
import Salt.MR.BridgeAdapt
import Salt.MR.CenterSupply
import Salt.MR.RHSGrade
import Salt.MR.CompactMin
import Salt.MR.WidthGrade
import Salt.MR.TruncFactor
import Salt.MR.GradeConst
import Salt.MR.SupClose
import Salt.MR.FarClose
import Salt.MR.SeamGate
import Salt.MR.FarStar
import Salt.MR.JointPlumb
import Salt.MR.SupStation
import Salt.MR.USetThinTS
import Salt.MR.USetPins
import Salt.MR.USetThinTL
import Salt.MR.RHSGradeC
import Salt.MR.RamRAdapter
import Salt.MR.RamWeight
import Salt.MR.CofactorDist
import Salt.MR.GradeWindowC
import Salt.MR.CofactorBall
import Salt.MR.CofactorGrade
import Salt.MR.CofactorSupply
import Salt.MR.USetBalance
import Salt.MR.USetPrice
import Salt.MR.SeamTerminal
import Salt.MR.FarArm
import Salt.MR.USetResiduals
import Salt.MR.CofactorLocal
import Salt.MR.Transfer34
import Salt.MR.SeamGraded
import Salt.MR.PinFamily
import Salt.MR.USetGradedThin
import Salt.MR.PinFamily2
import Salt.MR.SupplyGeneric
import Salt.MR.USetGradedBalance
import Salt.MR.USetGradedPrice
import Salt.MR.CaseASocket
import Salt.MR.GradedCapstone
import Salt.MR.TLegPreamble
import Salt.MR.TLegE1
import Salt.MR.MultShiuBridge
import Salt.MR.TLegCover
import Salt.MR.TLegKill
import Salt.MR.TLegExit
import Salt.MR.SeamCalibration
import Salt.MR.SeamLemma14
import Salt.MR.FloorProvenance
import Salt.MR.KernelCarry
import Salt.MR.TypicalPrice
import Salt.MR.SeamCalibrationK
import Salt.MR.TypicalPriceK
import Salt.MR.SeamNumber
import Salt.MR.SupF
import Salt.MR.JointHead
import Salt.Tactic.AuditAxioms

/-!
# The Matomäki–Radziwiłł gate track (`MR`) — aggregate import + axiom audit

The MR-gate campaign (freeze: `docs/exploration/mr-freeze.md`) opens the road
from the landed power zero-free region (`Salt.Vk.zeta_zero_free_region_pow`,
θ = 3/4 < 1) toward unconditional log-Chowla-2, by discharging the pretentious
non-pretentiousness hypothesis (1.6) of Tao 1509.05422 and the MRT door.

Wave 1 (route-shared, ungated stones), in the freeze's dispatch order; status
per stone after the MR-W1 executor wave (residual detail: the MR-W1 section of
`docs/blueprints/flags.md`):
* S10a `DoorDischarge` — LANDED: `regime_W_headroom_of_floor`, the
  `(log X)^{1/125}` arm.
* S1  `Dist`          — CORE LANDED: `pretDistSq` + Liouville split + principal
  Mertens evaluation + Euler `k≥2` tail.  Residual: the twisted
  `Re log L(1+1/logx+it,χ)` identity (needs an Euler-log-of-`L` bridge).
* S2  `ZetaPowLower`  — LANDED (MR-W2): Block A + keystones + Block B
  (`near_norm_logDeriv_Zc_le` the normalized scaled-Landau zero count,
  `zeta_near_bound_core`/`zeta_near_logDeriv_bound` the pow-region
  discharge at honest `C_L = 400`, `zeta_near_bridge` the FTC bridge) →
  `zeta_pow_lower`, `c' = e^{-400}/(32·10⁹)`-grade, shape `L^{3/4}ℓ⁴`.
* S3  `ZetaLowerAllT` — LANDED + CLOSED (MR-W2): compact-mid fill + `Zc`
  small-`t` patch + head `zeta_lower_all_t_of_pow`; the closer
  `zeta_lower_all_t` discharges `hpow` with S2 — the all-`t` uniform
  bound `c''/((log(|t|+3))^{3/4}(loglog(|t|+16))⁴) ≤ ‖ζ(1+d'+it)‖`.
* S6a `L2MVT`         — PARTIAL: `dpoly` L² expansion + diagonal split; the
  `(T+N)` close needs a Montgomery–Vaughan Hilbert-inequality stone (absent
  from mathlib/corpus).
* S6b `TuranKubilius` — LANDED: `turan_kubilius` (asymptotic form, `C = 4`)
  + the moment/counting helper set.
* S5  `NonPret`       — CASH-OUT LANDED (MR-W3): `lambda_nonpret_of_bridge`, the
  RANGE/QUALITY SPLIT (heights `|t| ≤ Q·x`, coefficient EXACTLY `1/4`) composing
  the λ-Euler bridge hypothesis with `zeta_lower_all_t` + the height absorption
  `loglog_height_le`.  Honest o(1) shape RECORDED: the freeze's `−C(Q)` carries a
  `−4·logloglog(|t|+16)` correction (the load-bearing `(loglog)⁴` region factor).
  Bridge down-payment: `log_norm_zeta_eq_re_tsum`
  (`log‖ζ(s)‖ = ∑'_p Re(−log(1−p^{−s}))`, `Re s > 1`).  The former single residual —
  the `σ = 1` oscillating prime truncation `∑_{p≤x} cos(t·log p)/p` vs the full
  log-Euler sum — CLOSED 2026-07-19 via `euler_osc_bridge_unconditional`
  (`PrimeTail.lean`), making `lambda_nonpret` (`NonPretClose.lean`) UNCONDITIONAL.
-/

open Salt.Tactic in
#audit_axioms Salt.MR.pretDistSq_principal
  Salt.MR.pretDistSq_liouville_split
  Salt.MR.pretDistSq_principal_eval
  Salt.MR.prime_power_tail_le
  Salt.MR.regime_W_headroom_of_floor
  Salt.MR.continuous_dpoly
  Salt.MR.sq_norm_dpoly_eq
  Salt.MR.dirichlet_poly_l2_expand
  Salt.MR.dirichlet_poly_l2_diagonal
  Salt.MR.card_Icc_filter_dvd
  Salt.MR.omega_eq_sum
  Salt.MR.first_moment
  Salt.MR.first_moment_le
  Salt.MR.first_moment_ge
  Salt.MR.second_moment_le
  Salt.MR.variance_bound
  Salt.MR.loglog_gap
  Salt.MR.turan_kubilius
  Salt.MR.zeta_lower_compact_mid
  Salt.MR.zeta_lower_small_t
  Salt.MR.zeta_lower_all_t_of_pow
  Salt.MR.zeta_lower_all_t
  Salt.MR.zeta_pow_anchor
  Salt.MR.pow_region_width
  Salt.MR.zeta_dirichlet_re_le
  Salt.MR.hasDerivAt_log_norm_zeta
  Salt.MR.zeta_horiz_lower
  Salt.MR.zeta_pow_lower_far
  Salt.MR.near_norm_logDeriv_Zc_le
  Salt.MR.zeta_near_logDeriv_bound
  Salt.MR.zeta_near_bridge
  Salt.MR.zeta_pow_lower
  Salt.MR.costwist_re
  Salt.MR.loglog_height_le
  Salt.MR.lambda_nonpret_of_bridge
  Salt.MR.log_norm_zeta_eq_re_tsum
  Salt.MR.mertens_first_upper
  Salt.MR.sigma_shift
  Salt.MR.euler_osc_truncation
  Salt.MR.euler_osc_bridge
  Salt.MR.log_euler_osc_zeta
  Salt.MR.euler_osc_bridge_le
  Salt.MR.halasz_cosh_ineq
  Salt.MR.halasz_cosh_ineq_complex
  Salt.MR.offdiag_int_bound
  Salt.MR.prime_tail_shift
  Salt.MR.log_euler_osc_zeta_unconditional
  Salt.MR.euler_osc_bridge_unconditional
  Salt.MR.one_line_pow_growth
  Salt.MR.shiu_moment_sq
  Salt.MR.l2_duality
  Salt.MR.dirichlet_poly_l2_mvt
  Salt.MR.lambda_nonpret
  Salt.MR.dist_one_floor_pow
  Salt.MR.Mrange_one_floor
  Salt.MR.ramare_weight_sum
  Salt.MR.ramare_decomp
  Salt.MR.mvHilbertUniform_of_l2
  Salt.MR.sep_inv_sq_sum_le
  Salt.MR.typical_density_le
  Salt.MR.lambdaLin_norm_le
  Salt.MR.lambdaLin_convolution
  Salt.MR.ellLin_lseries_deriv
  Salt.MR.hat_desmooth
  Salt.MR.hat_contour_rep
  Salt.MR.hat_mellin_bound
  Salt.MR.prop21_desmooth_reduction
  Salt.MR.lambdaLin_window_bound
  Salt.MR.fgJ_factorization
  Salt.MR.s2_tail_ledger
  Salt.MR.shifted_dirichlet_ftc
  Salt.MR.line_integral_tsum_swap
  Salt.MR.mvHilbertUniform_holds
  Salt.MR.dirichlet_poly_l2_mvt_final
  Salt.MR.pretentious_pointwise_triangle
  Salt.MR.pretDist_triangle
  Salt.MR.dist_mul_half
  Salt.MR.grade_EM
  Salt.MR.ball_mvt
  Salt.MR.log_diff_ge
  Salt.MR.halasz_ball_decay
  Salt.MR.cos_int_pair
  Salt.MR.dirichlet_plancherel
  Salt.MR.sv_average_identity
  Salt.MR.lpoly_mean_sq_bound
  Salt.MR.sv_smooth_kernel_bound
  Salt.MR.sharp_kernel_factor
  Salt.MR.ellLin_split
  Salt.MR.prop21_contour_leg
  Salt.MR.prop21_analog
  Salt.MR.largeSeries_ftc_double_beta
  Salt.MR.dist_split_A4
  Salt.MR.dist_split_fgJ
  Salt.MR.dist_recenter
  Salt.MR.perron_trunc
  Salt.MR.perron_trunc_trivial
  Salt.MR.perron_trunc_min
  Salt.MR.Aperron_representation
  Salt.MR.dist_split_A4_frozen
  Salt.MR.T1_pointwise_decay
  Salt.MR.log_ratio_ge
  Salt.MR.harmonic_zone_bound
  Salt.MR.perron_sum_error_collapsed
  Salt.MR.moment_core_bound
  Salt.MR.lemma12_meansq_conditional
  Salt.MR.lemma13_moment
  Salt.MR.ramare_decomp_pm
  Salt.MR.spoly_ramare_eq16
  Salt.MR.wellspaced_l2
  Salt.MR.wellspaced_card_le
  Salt.MR.spoly_ram_decomp
  Salt.MR.lemma12_meansq_of_windowErr
  Salt.MR.window_card_le
  Salt.MR.primes_dual_iff
  Salt.MR.zeta_near_strip_growth
  Salt.MR.primePoly_wellspaced_l2
  Salt.MR.exp_sum_decay
  Salt.MR.dualPoly_diagonal
  Salt.MR.wellspaced_harmonic_double
  Salt.MR.halasz_integers_of_vanDerCorput
  Salt.MR.norm_socketSum_eq_eR
  Salt.MR.socketBlock_kusmin
  Salt.MR.socketBlock_strip
  Salt.MR.halasz_integers_log_split
  Salt.MR.halasz_socket_large
  Salt.MR.zeta_block_secondDeriv
  Salt.MR.halasz_socket_midHigh
  Salt.MR.halasz_socket
  Salt.MR.halasz_integers
  Salt.MR.dpoly_pow
  Salt.MR.large_value_count_pre
  Salt.MR.kconv_l1_le
  Salt.MR.clean_dyadic_sub_main
  Salt.MR.ramErr_window_decomp
  Salt.MR.ramCopTail_moment
  Salt.MR.kconv_sup_le_window
  Salt.MR.kconv_l2_le_window
  Salt.MR.lemma12_meansq
  Salt.MR.ramP2corr_moment
  Salt.MR.large_value_count
  Salt.MR.abel_master
  Salt.MR.lambda_partial_alpha
  Salt.MR.lambda_tail_shift
  Salt.MR.rough_prime_tail
  Salt.MR.hall_tenenbaum_core
  Salt.MR.ht_valuation_partition
  Salt.MR.euler_exp_bound
  Salt.MR.euler_exp_bound_shifted
  Salt.MR.hall_tenenbaum_euler
  Salt.MR.smooth_rough_split
  Salt.MR.rect_zero_free
  Salt.MR.pole_row_sum
  Salt.MR.mult_shiu_MS_A
  Salt.MR.mult_shiu_MS_B
  Salt.MR.mult_shiu_MS_EXIT
  Salt.MR.ms_b_rough_factor
  Salt.MR.pole_residue_term
  Salt.MR.shifted_edge_price
  Salt.MR.lemma12_meansq_pretty
  Salt.MR.window_dominates
  Salt.MR.prime_power_discard
  Salt.MR.contour_A13_A14_head_wired
  Salt.MR.primeWindow_contour_rep
  Salt.MR.lambda_window_rep
  Salt.MR.rep_truncated
  Salt.MR.norm_logDeriv_zeta_cline_le
  Salt.MR.smoothPart_ellLin_eq_restrictBelow
  Salt.MR.seam_centering
  Salt.MR.seam_double_ftc
  Salt.MR.seam_alpha_collapse
  Salt.MR.four_factor_hat_rep
  Salt.MR.prop21RHS_hat_rep
  Salt.MR.prop21RHS_hat_rep_aligned
  Salt.MR.seam_realignment
  Salt.MR.seam_realignment_hat
  Salt.MR.hat_contour_rep_mismatch
  Salt.MR.four_factor_hat_rep_shifted
  Salt.MR.joint_support_untruncation
  Salt.MR.aligned_collapse_assembled
  Salt.MR.endpoint_reconciliation_full
  Salt.MR.prop21_unconditional
  Salt.MR.k4_plan_le_diag_sharp
  Salt.MR.contour_A13_A14_head_sharp
  Salt.MR.hhead_supplier_fgJ
  Salt.MR.T1_decay_fgJ
  Salt.MR.seamCoeff_trivial_dist_eq
  Salt.MR.T1_decay_trivial
  Salt.MR.hhead_supplier_trivial
  Salt.MR.dist_window_restrict
  Salt.MR.out_of_window_mass_le
  Salt.MR.dist_split_A4_N2
  Salt.MR.dist_split_A4_N2_windowed
  Salt.MR.upper_tail_le
  Salt.MR.dist_split_A4_N2_final
  Salt.MR.expEM_le_of_floor_corrected
  Salt.MR.T1_pointwise_decay_corrected
  Salt.MR.T1_decay_corrected_fgJ
  Salt.MR.prop_A3'_assembly
  Salt.MR.rampSliverMass_eq_zero_of_gap
  Salt.MR.ramp_sliver_bound
  Salt.MR.shortInterval_vonMangoldt_le
  Salt.MR.rampSliverMass_bound_unconditional
  Salt.MR.prop21_contour_leg_unwindowed
  Salt.MR.prop21_unconditional_final
  Salt.MR.prop21_unconditional_clean
  Salt.MR.T1_head_wire
  Salt.MR.norm_windowSum_le_mass
  Salt.MR.prop21RHS_le_head
  Salt.MR.kernel_L1_mass
  Salt.MR.kernel_mass_ledger
  Salt.MR.sigma_cutoff
  Salt.MR.dual_core
  Salt.MR.dual_assembly
  Salt.MR.pole_double_row
  Salt.MR.error_double_row
  Salt.MR.halasz_primes_primal_raw
  Salt.MR.absorb_arith
  Salt.MR.halasz_primes_pow
  Salt.MR.ellLin_euler_product
  Salt.MR.euler_log_bound
  Salt.MR.smooth_ratio_bound
  Salt.MR.dist_identification
  Salt.MR.head_pin_bound
  Salt.MR.joint_cs_factoring
  Salt.MR.sigma_wiring
  Salt.MR.joint_grade_assembly
  Salt.MR.hRHS_discharged_joint
  Salt.MR.T1_head_supplied_joint
  Salt.MR.T1_decay_conditional_final
  Salt.MR.kernel_L1_mass_sharp
  Salt.MR.lorentz_compare
  Salt.MR.mixed_weight_cs
  Salt.MR.prime_sum_sigma
  Salt.MR.dist_identification_sigma
  Salt.MR.head_sigma_bound
  Salt.MR.scale_floor
  Salt.MR.scale_floor_Mrange
  Salt.MR.sigma_cutoff_pretentious
  Salt.MR.scale_floor_Mrange_seam
  Salt.MR.offdiag_window_eval
  Salt.MR.widthA_plancherel
  Salt.MR.offdiag_widthA_eval
  Salt.MR.band_second_moment
  Salt.MR.head_split_ledger
  Salt.MR.kernel_tail_mass
  Salt.MR.tail_band_sum
  Salt.MR.offdiag_widthA_sharp
  Salt.MR.hband_discharge
  Salt.MR.offdiag_widthA_final
  Salt.MR.head_second_moment_grade
  Salt.MR.crossKer_head_tail_grade
  Salt.MR.kernel_head_mass
  Salt.MR.head_integral_discharged
  Salt.MR.crossKer_grade_final
  Salt.MR.low_leg_shift
  Salt.MR.sqNorm_cs_band
  Salt.MR.head_sharp_socket
  Salt.MR.crossKer_grade_sharp
  Salt.MR.offdiag_widthA_sharp_low
  Salt.MR.offdiag_widthA_final_low
  Salt.MR.head_second_moment_grade_low
  Salt.MR.crossKer_grade_decayed
  Salt.MR.window_mass_eval
  Salt.MR.window_sup_decay
  Salt.MR.window_sup_decay_sq
  Salt.MR.sigma_cutoff_seam
  Salt.MR.annHead_le_measure_sup
  Salt.MR.annHead_grade
  Salt.MR.annHead_le_socket
  Salt.MR.T1_decay_annular
  Salt.MR.prop_A3_T1_row_annular
  Salt.MR.T1_decay_annular_tailed
  Salt.MR.moment_core_bound_shifted
  Salt.MR.prop_A3_T1_row_moment
  Salt.MR.Aperron_short_interval
  Salt.MR.Aperron_short_interval_collapsed
  Salt.MR.dyadic_tail_proper
  Salt.MR.taylor2_bound
  Salt.MR.uSlab_taylor_main
  Salt.MR.uSlab_taylor_main_sq
  Salt.MR.xTentT_eq
  Salt.MR.tailT_mean_sq_bound
  Salt.MR.vtail_mean_sq_bound
  Salt.MR.lemma14_contour
  Salt.MR.lemma14_contour_grouped
  Salt.MR.lemma14_shortInterval_of_perron
  Salt.MR.annHead_le_socket_T
  Salt.MR.annHead_le_socket_polyT
  Salt.MR.pretDistSq_pow_le
  Salt.MR.pretDist_pow_le
  Salt.MR.pretDistSq_chiPrin_ge
  Salt.MR.chi_floor_of_order
  Salt.MR.chi_floor_orderOf
  Salt.MR.chi_floor_orderOf_twisted
  Salt.MR.zone_sum_collapsed_wide
  Salt.MR.Aperron_short_interval_collapsed_wide
  Salt.MR.lemma14_shortInterval_concrete
  Salt.MR.Aperron_error_le_of_T
  Salt.MR.Aperron_tendsto
  Salt.MR.perron_gap_tendsto
  Salt.MR.prop_A3_T1_row_annular_le
  Salt.MR.prop_A3_T1_row_moment_le
  Salt.MR.annulus_ball_far_split
  Salt.MR.spoly_abel_sup
  Salt.MR.ball_leg_of_sup
  Salt.MR.seam_TU_split
  Salt.MR.far_leg_collapse
  Salt.MR.prop_A3_T1_row_split
  Salt.MR.prop_A3_T1_row_split_crude
  Salt.MR.log_norm_L_eq_re_tsum
  Salt.MR.chi_peel_sum_bound
  Salt.MR.chi_euler_osc_bridge_unconditional
  Salt.MR.chi_dist_bridge
  Salt.MR.chi_floor_low_of_Llower
  Salt.MR.chi_floor_low_principal
  Salt.MR.chi_floor_all_principal
  Salt.MR.chi_floor_all_principal_twisted
  Salt.MR.chi_floor_all_of_Llower
  Salt.MR.chi_floor_all_of_Llower_twisted
  Salt.MR.ball_leg_of_sup_weighted
  Salt.MR.prop_A3_T1_row_split_weighted
  Salt.MR.sigma_cutoff_pretentious_gen
  Salt.MR.sigma_cutoff_pretentious_half
  Salt.MR.chi_Llower_trivial
  Salt.MR.chi_floor_all_unconditional
  Salt.MR.chi_Llower_341
  Salt.MR.chi_floor_all_nonreal
  Salt.MR.chi_floor_all_nonreal_twisted
  Salt.MR.zone_min_sum_split
  Salt.MR.socket_hZ
  Salt.MR.halasz_integers_unconditional
  Salt.MR.seam_sum_identity
  Salt.MR.ramWindowErr_moment_sharp
  Salt.MR.ramWindowErr_moment_grade
  Salt.MR.lemma12_meansq_sharp
  Salt.MR.lemma12_meansq_sharp_blockSupport
  Salt.MR.seam_sum_identity_mr
  Salt.MR.lemma12_meansq_on_subset
  Salt.MR.lemma12_meansq_on_subset_blockSupport
  Salt.MR.wellspaced_discretize
  Salt.MR.Uset_thin
  Salt.MR.spoly_ramare_split_mr
  Salt.MR.lemma12_meansq_mr
  Salt.MR.seven_eighths_bound
  Salt.MR.seven_eighths_bound_loglog
  Salt.MR.seven_eighths_bound_primes
  Salt.MR.hall_tenenbaum_core_two
  Salt.MR.euler_exp_bound_two
  Salt.MR.ht_tail_ratio
  Salt.MR.renormalise
  Salt.MR.renormalise_shifted
  Salt.MR.prod_one_sub_blockAvoid
  Salt.MR.alt_sum_blockAvoid_dirichlet
  Salt.MR.norm_exp_half_sub_le
  Salt.MR.block_factor_le_one
  Salt.MR.jfactor_alt_sum_le
  Salt.MR.jfactor_alt_sum_le_euler
  Salt.MR.center_to_ball_transfer
  Salt.MR.exp_budget_le
  Salt.MR.transfer_at_scale
  Salt.MR.spolyA_datum_split
  Salt.MR.ball_sup_of_center
  Salt.MR.halasz_direct_ball_window_free
  Salt.MR.mertensM_ge_neg_seventeen
  Salt.MR.sixteenth_loglog_le_SPartial_div_eight
  Salt.MR.hMball_of_A4_cap
  Salt.MR.ramP2mass_le
  Salt.MR.lemma12_meansq_mr_final
  Salt.MR.prop21_unconditional_uniform
  Salt.MR.prop21_uniform_at_scale
  Salt.MR.prop21_unconditional_uniform_absC
  Salt.MR.prop21_uniform_at_scale_absC
  Salt.MR.vonMangoldt_window_damped_min
  Salt.MR.vonMangoldt_window_shifted_min
  Salt.MR.lambdaLin_window_damped_min
  Salt.MR.lambdaLin_window_shifted_min
  Salt.MR.window_mass_product
  Salt.MR.window_bridge_shifted
  Salt.MR.window_bridge
  Salt.MR.smooth_euler_product
  Salt.MR.head_dist_floor_gen
  Salt.MR.supF_pret_pointwise
  Salt.MR.supF_pret_majorant_sigma
  Salt.MR.joint_sigma_integral
  Salt.MR.window_sup_decay_center
  Salt.MR.halasz_direct_center
  Salt.MR.halasz_direct_center_gen
  Salt.MR.ball_center_dichotomy
  Salt.MR.ball_leg_empty_of_le
  Salt.MR.ball_leg_of_center_small
  Salt.MR.crossKer_sigma_bound
  Salt.MR.bridge_adapter
  Salt.MR.sigma_wiring_of_crossKer
  Salt.MR.loglog_absorb
  Salt.MR.loglog_absorb_pow
  Salt.MR.seamCoeff_twist_combine
  Salt.MR.pretDistSq_twist_slot
  Salt.MR.center_halasz_supply
  Salt.MR.ball_sup_supplied
  Salt.MR.center_dist_floor
  Salt.MR.crossKer_sharp_sigma_bound
  Salt.MR.rhs_grade_at_scale
  Salt.MR.hRHS_discharged
  Salt.MR.center_halasz_of_grade
  Salt.MR.lemma12_meansq_mr_blockSupport
  Salt.MR.lemma12_meansq_mr_consume
  Salt.MR.gapMaj_meansq_le
  Salt.MR.gapMaj_meansq_sqrt
  Salt.MR.lemma14_shortInterval_meansq
  Salt.MR.lemma14_shortInterval_meansq_concrete
  Salt.MR.T1_decay_annular_polyT
  Salt.MR.T1_decay_annular_tailed_polyT
  Salt.MR.prop_A3_T1_row_annular_polyT
  Salt.MR.prop_A3_T1_row_moment_polyT
  Salt.MR.window_sup_decay_gen
  Salt.MR.halasz_direct_gen
  Salt.MR.halasz_direct_ball
  Salt.MR.halasz_direct_ball_window
  Salt.MR.pretDistSq_continuous_freq
  Salt.MR.exists_min_dist_on_Icc
  Salt.MR.exists_min_dist_abs
  Salt.MR.pretDistSq_freq_lipschitz
  Salt.MR.dist_one_shift_le_of_two_caps
  Salt.MR.overhang_no_undercut
  Salt.MR.compact_min_package
  Salt.MR.band_second_moment_width
  Salt.MR.head_second_moment_grade_width
  Salt.MR.head_second_moment_grade_low_width
  Salt.MR.tail_lorentz_core
  Salt.MR.tail_lorentz_grade
  Salt.MR.band_weight_le_lorentz
  Salt.MR.crossKer_grade_width
  Salt.MR.line_moment_grade_width
  Salt.MR.line_moment_grade_low_width
  Salt.MR.crossKer_width_sigma_bound
  Salt.MR.width_pin_gates
  Salt.MR.crossKer_width_sigma_pin
  Salt.MR.crossKerFar_nonneg
  Salt.MR.measurableSet_farRegion
  Salt.MR.measurableSet_farAbs
  Salt.MR.joint_inner_factor_trunc
  Salt.MR.joint_cs_factoring_trunc
  Salt.MR.kernel_far_mass
  Salt.MR.crossKerFar_le_tail
  Salt.MR.far_tail_absorb
  Salt.MR.crossKerFar_pin_le
  Salt.MR.center_dist_floor_trunc
  Salt.MR.center_dist_floor_compact
  Salt.MR.exists_shortIntervalDatum
  Salt.MR.hband_discharge_param
  Salt.MR.crossKer_width_sigma_bound_param
  Salt.MR.crossKer_width_sigma_bound_uniform
  Salt.MR.pin_width_gates
  Salt.MR.width_pin_bracket_le
  Salt.MR.crossKer_width_pin_const
  Salt.MR.beta_integral_pin_const
  Salt.MR.rhs_grade_at_scale_const
  Salt.MR.rhsAgradeConst_le
  Salt.MR.hRHS_discharged_const
  Salt.MR.center_halasz_of_grade_const
  Salt.MR.joint_supF_pin_at
  Salt.MR.center_dist_floor_recentred
  Salt.MR.joint_supF_pin_trunc
  Salt.MR.joint_cs_trunc_pin
  Salt.MR.rhs_grade_at_scale_trunc
  Salt.MR.far_supF_bound
  Salt.MR.far_kernel_bound
  Salt.MR.far_kernel_bound_T
  Salt.MR.far_window_mass_le
  Salt.MR.far_price_floor
  Salt.MR.far_term_priced
  Salt.MR.rhs_grade_at_scale_closed
  Salt.MR.hRHS_socket_of_far
  Salt.MR.ball_sup_closed
  Salt.MR.seamAnn_inter_seamBall_center_le
  Salt.MR.ball_center_dichotomy_two_sided
  Salt.MR.seamGateR_nonneg
  Salt.MR.log_pow_four_le_of_le_two_mul
  Salt.MR.seam_gate_of_nonempty
  Salt.MR.seam_gate_of_nonempty_nat
  Salt.MR.exists_min_gate
  Salt.MR.seam_gate_package
  Salt.MR.seam_sup_binder_of_inter_empty
  Salt.MR.ball_leg_of_inter_empty
  Salt.MR.rhs_grade_at_scale_seam_gate
  Salt.MR.Tstar_mono
  Salt.MR.far_kernel_bound_star
  Salt.MR.far_kfar_star_le
  Salt.MR.hfar_star
  Salt.MR.seam_gate_star_of_nonempty
  Salt.MR.exists_min_gate_star
  Salt.MR.seam_gate_star_package
  Salt.MR.rhs_grade_at_scale_closed_star
  Salt.MR.hRHS_socket_star
  Salt.MR.ball_sup_closed_star
  Salt.MR.intervalIntegrable_beta_leg
  Salt.MR.intervalIntegrable_alpha_leg
  Salt.MR.intervalIntegrable_beta_leg'
  Salt.MR.intervalIntegrable_alpha_leg'
  Salt.MR.jointIntegrableAt_of_gates
  Salt.MR.jointIntegrableAt_discharged
  Salt.MR.jointIntegrableAt_pin
  Salt.MR.jointIntegrableAt_of_zero
  Salt.MR.jointIntegrableAt_pin_free
  Salt.MR.center_halasz_supply_uniform
  Salt.MR.ball_sup_supplied_uniform
  Salt.MR.ball_sup_closed_star_uniform
  Salt.MR.seam_ball_leg_station
  Salt.MR.seamGateRstar_le_self
  Salt.MR.seam_ball_leg_station_M
  Salt.MR.prop_A3_T1_row_station
  Salt.MR.ramR_eq_spoly
  Salt.MR.wellSpaced_neg_image
  Salt.MR.ramR_sq_sum_le
  Salt.MR.norm_ramMain_sq_le_of_small
  Salt.MR.TS_branch_meansq
  Salt.MR.dyadicPairs_card_le_exp
  Salt.MR.Uset_thin_alpha
  Salt.MR.thin_sqrt_kill
  Salt.MR.Uset_thin_sqrt_kill
  Salt.MR.uset_TS_branch
  Salt.MR.uset_TS_branch_meanvalue
  Salt.MR.ramRcoeff_mass_le
  Salt.MR.loglog_le_rpow
  Salt.MR.QJ_sq_subpoly
  Salt.MR.QJ_succ_sq_le_rpow
  Salt.MR.pin_Pii
  Salt.MR.pin_Pii_nat
  Salt.MR.pin_P83_le_Q83_of_gate
  Salt.MR.two_le_H83
  Salt.MR.kappa30_of_TannGate
  Salt.MR.TannGate_of_row_height
  Salt.MR.TannGate_fails_polylog_deg
  Salt.MR.balance_exit
  Salt.MR.exit_margin
  Salt.MR.exit_beats_c0
  Salt.MR.halved_fails
  Salt.MR.balance_exit_B4
  Salt.MR.loglog_absorb_B4
  Salt.MR.ramQ_eq_spoly
  Salt.MR.ramQ_eq_dpoly
  Salt.MR.ramQ_eq_halaszSum
  Salt.MR.ramQ_large_count
  Salt.MR.ramQ_large_count_Tfree
  Salt.MR.ramQbase_le_pow_ten
  Salt.MR.tL_sumsq_ramQ
  Salt.MR.ramQblock_inv_sum_le
  Salt.MR.tL_kill
  Salt.MR.tL_ramQ_sumsq_killed
  Salt.MR.tL_main_sumsq
  Salt.MR.rhsFbound_eq_rhsFboundC
  Salt.MR.rhsSigmaG_eq_rhsSigmaGC
  Salt.MR.rhsFboundC_eq_exp_mul
  Salt.MR.joint_supF_pinC
  Salt.MR.beta_integral_pin_constC
  Salt.MR.ramRrange_subset_Icc_sharp
  Salt.MR.norm_ramRcoeff_le_one
  Salt.MR.norm_ramRcoeff_cterm_le
  Salt.MR.ramR_split_top
  Salt.MR.ramRtop_card_le_two
  Salt.MR.norm_ramRtop_le
  Salt.MR.ramR_abel_sup
  Salt.MR.ramR_abel_window_floor
  Salt.MR.inv_blockOmega_succ_eq_integral
  Salt.MR.blockOmega_mul_coprime
  Salt.MR.blockOmega_pow_mul_coprime
  Salt.MR.gxDatum_norm_le_one
  Salt.MR.ellLin_gxDatum
  Salt.MR.ramR_eq_integral_damp
  Salt.MR.ramR_norm_le_of_damp_le
  Salt.MR.ramRdamp_eq_spoly
  Salt.MR.ramRdamp_ellLin
  Salt.MR.sum_blockWindowPrimes_le
  Salt.MR.gxDatum_pretDistSq_ge
  Salt.MR.gxDatum_pretDistSq_ge_one
  Salt.MR.gxDatum_pretDistSq_costwist
  Salt.MR.blockWindow_mertens_pin
  Salt.MR.theta293_self_consistent
  Salt.MR.exit_margin_293
  Salt.MR.exit_margin_293_sharp
  Salt.MR.exit_beats_c0_293
  Salt.MR.loglog_absorb_293
  Salt.MR.pin_P83_le_Q83_293
  Salt.MR.dist_one_shift_le_of_two_caps_asym
  Salt.MR.pocket_collision_abstract
  Salt.MR.pocket_collision
  Salt.MR.pocket_collision_pin
  Salt.MR.collisionGate_of_five
  Salt.MR.pocket_collision_window
  Salt.MR.pocket_far_from_ball
  Salt.MR.pocket_ball_shrink
  Salt.MR.intervalIntegrable_beta_legC
  Salt.MR.intervalIntegrable_alpha_legC
  Salt.MR.jointIntegrableAt_iff_C
  Salt.MR.jointIntegrableAtC_of_gates
  Salt.MR.jointIntegrableAtC_pin_free
  Salt.MR.joint_supF_pin_atC
  Salt.MR.joint_supF_pin_windowC
  Salt.MR.joint_cs_trunc_pinC
  Salt.MR.rhsAgradeConstC_le
  Salt.MR.rhs_grade_at_scale_windowC
  Salt.MR.center_halasz_supply_B_uniform
  Salt.MR.center_halasz_supply_B
  Salt.MR.center_trivial_bound
  Salt.MR.damped_partial_trivial
  Salt.MR.spolyA_window_split
  Salt.MR.far_transfer_sup
  Salt.MR.spolyA_ramRcoeff_eq_integral
  Salt.MR.spolyA_ramRcoeff_le_of_damp
  Salt.MR.damped_partial_transfer
  Salt.MR.caseB_window_geometry
  Salt.MR.caseB_ramR_of_collided
  Salt.MR.caseB_ramR_bound
  Salt.MR.collisionGate_discharged
  Salt.MR.center_halasz_supply_A
  Salt.MR.caseA_rhs_socket
  Salt.MR.caseA_partial_supply
  Salt.MR.caseA_damped_partial
  Salt.MR.caseA_ramR_of_supplied
  Salt.MR.caseA_ramR_bound
  Salt.MR.caseA_grade_numeral
  Salt.MR.caseA_ramR_bound_293
  Salt.MR.pretDistSq_tail_le
  Salt.MR.caseA_floor_slot
  Salt.MR.gxDatum_trivial_window
  Salt.MR.caseA_partial_supply_slice
  Salt.MR.cofactorRbd_nonneg
  Salt.MR.pocket_transport
  Salt.MR.cofactor_Rbd
  Salt.MR.descent_tail_le
  Salt.MR.cofactorMfl_nonneg_of_descent
  Salt.MR.cofactorMfl_grade_293
  Salt.MR.caseAS_293
  Salt.MR.cofactor_Rbd_293
  Salt.MR.tL_supply_discharged
  Salt.MR.sum_TS_add_TL
  Salt.MR.uset_integral_to_branches
  Salt.MR.TS_feed_of_thin
  Salt.MR.sum_inv_sq_Icc_le
  Salt.MR.TL_feed_of_supply
  Salt.MR.block_sum_bound
  Salt.MR.hU_exit_of_branches
  Salt.MR.tL_block_weight
  Salt.MR.hU_supplied
  Salt.MR.hU_balance
  Salt.MR.hU_balance_beats_door
  Salt.MR.hU_discharged
  Salt.MR.KS_priced
  Salt.MR.KS_supplied
  Salt.MR.cofactorRbd_le_of_worst
  Salt.MR.Rbd_uniform
  Salt.MR.ramI_card_le_pin
  Salt.MR.floor_pin
  Salt.MR.balance_priced_main
  Salt.MR.rem_priced
  Salt.MR.hU_fully_priced
  Salt.MR.priced_exit_beats_door
  Salt.MR.seam_window_datum_zero
  Salt.MR.seam_Dmax_bridge
  Salt.MR.seam_terminal_row
  Salt.MR.seam_terminal_dichotomy
  Salt.MR.dyadic_SPartial_charge
  Salt.MR.farArm_charge_le
  Salt.MR.cap_fails_floor
  Salt.MR.Mrange_floor_of_center_floor_radius
  Salt.MR.Mrange_floor_of_center_floor
  Salt.MR.far_arm_row
  Salt.MR.far_arm_row_tailed
  Salt.MR.far_arm_row_polyT
  Salt.MR.seam_row_of_inter_empty
  Salt.MR.seam_row_both_arms
  Salt.MR.seam_row_three_arms
  Salt.MR.caseAS_arm_priced
  Salt.MR.farMain_priced
  Salt.MR.Rbd_grade_priced
  Salt.MR.farErr_TannGate_floor
  Salt.MR.Rbd_TannGate_floor
  Salt.MR.Rbd_grade_refuted
  Salt.MR.Rbd_and_Cq_gates_collide
  Salt.MR.farErr_le_of_ambient_gate
  Salt.MR.Rbd_grade_priced_of_ambient
  Salt.MR.ambient_cap_below_TannGate_floor
  Salt.MR.E_priced
  Salt.MR.E_priced_row_scale
  Salt.MR.EP2_gate_of_row
  Salt.MR.P2_route_64_over_Psq_insufficient
  Salt.MR.gate_Cq_CR
  Salt.MR.gate_KS_live_delta
  Salt.MR.gate_absorb_8640
  Salt.MR.numeral_gates_discharged
  Salt.MR.Tstar_window_mono
  Salt.MR.contour_gate_local_iff
  Salt.MR.pocket_transport_local
  Salt.MR.cofactor_Rbd_local
  Salt.MR.tL_supply_discharged_local
  Salt.MR.log_Tstar_self
  Salt.MR.farErr_local_le
  Salt.MR.farErr_local_of_gate
  Salt.MR.farErr_local_window_ge
  Salt.MR.thirtysecond_cap_to_SPartial
  Salt.MR.thirtysecond_loglog_le_SPartial_div_32
  Salt.MR.thirtysecond_cap_to_SPartial_293_descent
  Salt.MR.budget_le_quarter
  Salt.MR.exp_budget_le_34
  Salt.MR.transfer_at_scale_34
  Salt.MR.far_transfer_sup_34
  Salt.MR.far_transfer_sup_34_of_pocket_cap
  Salt.MR.farErr34_le_of_ambient_gate
  Salt.MR.Rbd34_grade_priced
  Salt.MR.Rbd34_grade_priced_of_ambient
  Salt.MR.farErr34_at_TannGate_floor
  Salt.MR.TsetG_unique
  Salt.MR.TsetG_disjoint
  Salt.MR.TsetG_UsetG_disjoint
  Salt.MR.exists_TsetG_or_mem_UsetG
  Salt.MR.measurableSet_UsetG
  Salt.MR.measurableSet_TsetG
  Salt.MR.measurableSet_seamTtotG
  Salt.MR.sdiff_biUnion_TsetG
  Salt.MR.seam_T_additivityG
  Salt.MR.seam_TU_splitG
  Salt.MR.prop_A3_T1_row_split_weightedG
  Salt.MR.prop_A3_T1_row_split_weightedG_crude
  Salt.MR.pin2_basic
  Salt.MR.log_le_rpow_fifth
  Salt.MR.log_Tstar2_self
  Salt.MR.far_window_mass_le2
  Salt.MR.far_kernel_bound_T2
  Salt.MR.far_kernel_bound_star2
  Salt.MR.far_kfar_star2_le
  Salt.MR.hfar_star2
  Salt.MR.far_supF_bound2
  Salt.MR.joint_supF_pin_at2
  Salt.MR.prop21_uniform_at_scale_pin2
  Salt.MR.cofactor_Rbd34_assembled
  Salt.MR.width_pin_gates_pin2
  Salt.MR.width_pin_gate_bandwidth_fails_pin2
  Salt.MR.two_mul_pow_four_le_ypin2
  Salt.MR.E_slot_pin2_le
  Salt.MR.E_slot_pin2_closes
  Salt.MR.three_twentieths_gap
  Salt.MR.farErr34_local_closes
  Salt.MR.ramI_nonempty
  Salt.MR.ramQbase_le_of_mem_ramI
  Salt.MR.not_blockSmallG_witness
  Salt.MR.ramI_nonempty_of_not_blockSmallG
  Salt.MR.not_blockSmallG_witness_of_mem_UsetG
  Salt.MR.ramQ_graded_count
  Salt.MR.usetG_thin
  Salt.MR.usetG_thin_Q
  Salt.MR.gradeV_sq_le_rpow
  Salt.MR.usetG_thin_pin
  Salt.MR.pow_four_le_ypin2
  Salt.MR.width_pin_gates_pin2_old_A
  Salt.MR.width_pin_gates_pin2_at_pin
  Salt.MR.Tstar2_mono
  Salt.MR.seamGateRstar2_nonneg
  Salt.MR.seam_gate_star2_of_nonempty
  Salt.MR.exists_min_gate_star2
  Salt.MR.seam_gate_star2_package
  Salt.MR.joint_supF_pin_trunc2
  Salt.MR.joint_cs_trunc_pin2
  Salt.MR.crossKer_width_pin_const2
  Salt.MR.beta_integral_pin_const2
  Salt.MR.rhs_grade_at_scale_trunc2
  Salt.MR.rhs_grade_at_scale_closed_star2
  Salt.MR.hRHS_socket_star2
  Salt.MR.caseAS2_nonneg
  Salt.MR.caseAS2_absorbs_E_slot
  Salt.MR.caseAS2_absorbs_E_slot_closes
  Salt.MR.center_halasz_supply_Y
  Salt.MR.ball_sup_supplied_Y
  Salt.MR.ball_sup_closed_star2
  Salt.MR.usetG_integral_to_branches
  Salt.MR.gradedPins_nondegenerate
  Salt.MR.usetG_thin_bundle
  Salt.MR.usetG_thin_sqrt_kill
  Salt.MR.usetG_TS_branch
  Salt.MR.usetG_TS_branch_meanvalue
  Salt.MR.TSG_feed_of_thin
  Salt.MR.TLG_feed_of_supply_local
  Salt.MR.hUG_exit_of_branches
  Salt.MR.hUG_supplied
  Salt.MR.hUG_balance
  Salt.MR.hUG_balance_beats_door
  Salt.MR.hUG_discharged
  Salt.MR.pin2Gate_le_ballQuarterThreshold
  Salt.MR.Tstar2_window_mono
  Salt.MR.pocket_transport_pin2
  Salt.MR.damped_partial_transfer_34
  Salt.MR.cofactor_Rbd34_local
  Salt.MR.tL_supply_discharged34_local
  Salt.MR.caseAS2_arm_priced
  Salt.MR.farErr34_le
  Salt.MR.farSupS34_le
  Salt.MR.cofactorRbd34loc_le_of_worst
  Salt.MR.Rbd34loc_uniform
  Salt.MR.Rbd34loc_grade_priced
  Salt.MR.Rbd34loc_grade_closes
  Salt.MR.thinBundleG_at_pin
  Salt.MR.thinBundleG_at_pin_Q
  Salt.MR.hUG34_supplied
  Salt.MR.hUG34_fully_priced
  Salt.MR.center_halasz_supply_YA
  Salt.MR.joint_supF_pin_at2C
  Salt.MR.joint_supF_pin_window2C
  Salt.MR.joint_cs_trunc_pin2C
  Salt.MR.jointIntegrableAtC_pin2_free
  Salt.MR.beta_integral_pin_const2C
  Salt.MR.rhs_grade_at_scale_window2C
  Salt.MR.caseA_rhs_socket2
  Salt.MR.caseA_partial_supply2
  Salt.MR.caseA_slice2
  Salt.MR.caseASocket2_discharged
  Salt.MR.hUG34_unconditional
  Salt.MR.hUG34_unconditional_beats_door
  Salt.MR.blockSmallG_of_mem_TsetG
  Salt.MR.ramQ_le_of_blockSmallG
  Salt.MR.ramQ_sq_le_of_blockSmallG
  Salt.MR.exists_mem_ramI_ramQ_le_of_mem_TsetG
  Salt.MR.measurableSet_annulus_TsetG
  Salt.MR.annulus_TsetG_subset_Icc
  Salt.MR.lemma12_on_TsetG
  Salt.MR.lemma12_on_TsetG_blockSupport
  Salt.MR.cofactor_mvt_of_subset
  Salt.MR.cofactor_mvt_sharp
  Salt.MR.ramRrange_mass_le
  Salt.MR.cofactor_mvt_mass_of_subset
  Salt.MR.cofactor_mvt_sharp_exit
  Salt.MR.exists_sharp_length
  Salt.MR.cofactor_mvt_sharp_exit_visible
  Salt.MR.cofactor_mvt_dyadic_lossy
  Salt.MR.sum_exp_neg_graded
  Salt.MR.sum_exp_neg_graded_rate
  Salt.MR.sum_exp_neg_graded_card
  Salt.MR.sum_exp_growth
  Salt.MR.sum_exp_growth_top
  Salt.MR.norm_ramMain_sq_le_of_mem_TsetG
  Salt.MR.integral_ramMain_sq_le_of_subset_TsetG
  Salt.MR.ramRbot_one_le_of_mem_ramI
  Salt.MR.sum_integral_ramMain_sq_le_of_subset_TsetG
  Salt.MR.E1_bound
  Salt.MR.exp_block_bottom_le_rpow
  Salt.MR.rpow_growth_le_rpow_bottom
  Salt.MR.E1_pin
  Salt.MR.spoly_of_support_le
  Salt.MR.spoly_mul
  Salt.MR.ramQ_eq_spoly_bounded
  Salt.MR.multShiuCoeff_support_low
  Salt.MR.multShiuCoeff_support_high
  Salt.MR.ramQ_pow_mul_ramR_eq_spoly
  Salt.MR.af_mul_oneAf_apply
  Salt.MR.norm_af_mul_le
  Salt.MR.norm_multShiuCoeff_le
  Salt.MR.blockPrimeAf_pow_bound
  Salt.MR.maj_le_factorial_blockDiv
  Salt.MR.coeff_bound_factorial_blockDiv
  Salt.MR.multShiu_moment
  Salt.MR.ramQblock_subset_dyadic_block
  Salt.MR.ramRrange_ceil_bot_le
  Salt.MR.multShiu_moment_pinned
  Salt.MR.not_blockSmallG_pred_of_mem_TsetG
  Salt.MR.TsetG_level_ge_two_witness
  Salt.MR.ramI_pred_nonempty_of_mem_TsetG
  Salt.MR.TsetGr_subset_TsetG
  Salt.MR.ramQ_violation_of_mem_TsetGr
  Salt.MR.measurableSet_TsetGr
  Salt.MR.TsetG_subset_biUnion_TsetGr
  Salt.MR.setIntegral_le_finset_sum_of_cover
  Salt.MR.integral_TsetG_le_sum_TsetGr
  Salt.MR.integral_TsetG_le_card_mul
  Salt.MR.one_le_normalized_of_mem_TsetGr
  Salt.MR.one_le_normalized_pow
  Salt.MR.one_le_ramQ_pow_mul_exp
  Salt.MR.cell_integral_normalized
  Salt.MR.measurableSet_annulus_TsetGr
  Salt.MR.annulus_TsetGr_subset_Icc
  Salt.MR.cell_integral_normalized_annulus
  Salt.MR.ellPin_mul_block_le
  Salt.MR.exp_ellPin_alpha_le
  Salt.MR.exp_ellPin_cancel
  Salt.MR.ellPin_window_bottom_ge
  Salt.MR.factorial_sq_le_exp
  Salt.MR.ell_log_ell_le
  Salt.MR.factorial_sq_le_pin
  Salt.MR.mrAlpha_diff
  Salt.MR.mrAlpha_decay_le
  Salt.MR.mrAlpha_pred_lt
  Salt.MR.CellGates.loglogQ_le_of_gate2
  Salt.MR.CellGates.logQ_le_rpow_of_gate2
  Salt.MR.gate2_absorb
  Salt.MR.cell_geometry_collapse
  Salt.MR.ramQ_pow_mul_ramR_eq_spoly_mix
  Salt.MR.norm_mixCoeff_le
  Salt.MR.coeff_bound_mix
  Salt.MR.mix_moment
  Salt.MR.cell_ramR_normalized
  Salt.MR.cell_bound_raw
  Salt.MR.cell_bound_pinned
  Salt.MR.level_kill_exponent
  Salt.MR.level_kill_exp
  Salt.MR.level_kill_collected
  Salt.MR.level_kill_collected_P1
  Salt.MR.mrAlpha_mono
  Salt.MR.mrAlpha_pos
  Salt.MR.mrAlpha_le_quarter
  Salt.MR.alpha_gates_from_eta
  Salt.MR.ramI_bottom_deficit
  Salt.MR.ramI_top_le
  Salt.MR.ramI_pos_of_mem
  Salt.MR.ramI_card_two_mul
  Salt.MR.level_kill_budget
  Salt.MR.cell_price_uniform
  Salt.MR.level_geometry_collapse
  Salt.MR.integral_ramMain_le_exp_mul_ramR
  Salt.MR.Ej_bound
  Salt.MR.sum_Ej_collected
  Salt.MR.TLeg_bound
  Salt.MR.TLeg_feeds_capstone
  Salt.MR.calE_one
  Salt.MR.calE_mono
  Salt.MR.calE_step
  Salt.MR.calQ_mono
  Salt.MR.log_calP
  Salt.MR.log_calQ
  Salt.MR.le_rpow_half_of_sq_le
  Salt.MR.levelGates_calibrated
  Salt.MR.calFrame_satisfiable
  Salt.MR.calibrated_block_nonempty
  Salt.MR.ladder_below_station
  Salt.MR.seam_row_calibrated
  Salt.MR.seamAnn_integral_split
  Salt.MR.spoly_eq_dpolyA_filter
  Salt.MR.seamS0_range
  Salt.MR.seamS0_pos
  Salt.MR.seam_midrange_bound
  Salt.MR.seam_split_four
  Salt.MR.seam_midrange_of_tall_row
  Salt.MR.seam_Msup
  Salt.MR.lemma14_contour_of_Msup_at
  Salt.MR.lemma14_contour_seam_supplied
  Salt.MR.lemma14_contour_seam_supplied_single
  Salt.MR.lemma14_contour_seam_supplied_calibrated
  Salt.MR.seam_row_calibrated_station
  Salt.MR.dist_one_floor_uniform
  Salt.MR.seam_floor_of_cap_pointwise
  Salt.MR.Mrange_seam_floor_of_cap
  Salt.MR.cap_gate_satisfiable
  Salt.MR.Mrange_seam_floor_column
  Salt.MR.T1_decay_column_cap_supplied
  Salt.MR.Mrange_seam_floor_A10
  Salt.MR.dampA_normSq
  Salt.MR.vSeg_eq_damp_endpoints
  Salt.MR.uKernel_norm_le
  Salt.MR.uKernel_wdiff_norm_le
  Salt.MR.vtail_meansq_damped
  Salt.MR.vtail_meansq_kernel
  Salt.MR.vtail_meansq_kernel_neg
  Salt.MR.lemma14_contour_kernel
  Salt.MR.lemma14_shortInterval_meansq_kernel
  Salt.MR.coprime_bandProd_of_blockOmega_zero
  Salt.MR.blockfree_sum_le
  Salt.MR.ramP2mass_win_le
  Salt.MR.lemma12Rows_priced
  Salt.MR.lemma12Rows_priced_ratio
  Salt.MR.sum_lemma12Rows_priced
  Salt.MR.sum_lemma12Rows_priced_calibrated
  Salt.MR.log_calP_div_log_calQ
  Salt.MR.sum_calibrated_ratio_eq
  Salt.MR.calibrated_ratio_not_MR_shape
  Salt.MR.calibrated_sum_ratio_ge_half
  Salt.MR.log_calP_div_log_calQK
  Salt.MR.calQK_mono
  Salt.MR.calP_le_calQK
  Salt.MR.calibrated_block_nonemptyK
  Salt.MR.ladder_below_stationK
  Salt.MR.levelGates_calibratedK
  Salt.MR.calFrameK_satisfiable
  Salt.MR.sum_ratioK_le
  Salt.MR.eq28_clears_of_M
  Salt.MR.sum_ratioK_pinned_clears
  Salt.MR.ramP2mass_direct
  Salt.MR.seam_row_calibratedK
  Salt.MR.sum_lemma12Rows_priced_calibratedK
  Salt.MR.lemma12Rows_pricedK
  Salt.MR.lemma12Rows_priced_ratioK
  Salt.MR.sum_lemma12Rows_pricedK
  Salt.MR.sum_lemma12Rows_priced_calibratedK2
  Salt.MR.seam_row_number
  Salt.MR.sum_ratioK_le_basel
  Salt.MR.eq28_clears_of_M_basel
  Salt.MR.farErr34_local_closes_of_gate
