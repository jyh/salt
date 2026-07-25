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
