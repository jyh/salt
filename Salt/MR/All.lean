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
import Salt.MR.Sec9Glue
import Salt.MR.DoorFloor
import Salt.MR.SiegelArm
import Salt.MR.SiegelBand
import Salt.MR.BigXiArc
import Salt.MR.RegimeHead
import Salt.MR.LandauL1
import Salt.MR.LandauDescent
import Salt.MR.LandauOdd
import Salt.MR.ThmA2Open
import Salt.MR.Sawtooth
import Salt.MR.ParsevalSingle
import Salt.MR.MWindowBridge
import Salt.MR.CapFreeArm
import Salt.MR.CapFreeArm3
import Salt.MR.SPartCore
import Salt.MR.ThmA2Spine
import Salt.MR.T0Band
import Salt.MR.SeamRowWindowed
import Salt.MR.SPartStation
import Salt.MR.ThmA2
import Salt.MR.ThmA2Rows
import Salt.MR.StationHoist
import Salt.MR.MWindowExtend
import Salt.MR.Eq26Bridge
import Salt.MR.DoorFloor1500
import Salt.MR.DoorFrame
import Salt.MR.DoorFrameH1
import Salt.MR.SieveGlue
import Salt.MR.MinorArcVaughan
import Salt.MR.Eq26Compose
import Salt.MR.MinorArcCore
import Salt.MR.MinorArcExit
import Salt.MR.ExitClose
import Salt.MR.M4Window
import Salt.MR.M4Chars
import Salt.MR.M4Residue
import Salt.MR.M4Dyadic
import Salt.MR.SupF
import Salt.MR.JointHead
import Salt.MR.M4Abel
import Salt.MR.VkTwistClose
import Salt.MR.VkTwistLadder
import Salt.MR.CapFreeAssembly
import Salt.MR.M4ErrRewire
import Salt.MR.FrameWitness
import Salt.MR.T0BandCapFree
import Salt.MR.M4Quality
import Salt.MR.M4MeanSq
import Salt.MR.M4Sieve
import Salt.MR.M4Door
import Salt.MR.M4Exit
import Salt.MR.M4Close
import Salt.MR.M4BridgePhase
import Salt.MR.M4BridgeCover
import Salt.MR.M4BridgeResidue
import Salt.MR.M4BridgeIntegral
import Salt.MR.M4BridgeDilate
import Salt.MR.M4Seam
import Salt.MR.M4Join
import Salt.MR.M4ClassPrice
import Salt.MR.CofactorSupplier
import Salt.MR.CaseAWide
import Salt.MR.M4WaveClosed
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
  Salt.MR.gJ_prime_pow
  Salt.MR.gJ_mul
  Salt.MR.gJ_eq_prod
  Salt.MR.prod_one_sub_gJ
  Salt.MR.lemma5_middle
  Salt.MR.lemma5
  Salt.MR.lemma5_MR_middle
  Salt.MR.lemma5_MR
  Salt.MR.lemma5_budget
  Salt.MR.lemma5_budget_pinned
  Salt.MR.door_h_le_hTwo
  Salt.MR.sec9_split
  Salt.MR.sec9_count_identity
  Salt.MR.sec9_four_term
  Salt.MR.card_not_memS_le_sum
  Salt.MR.sec9_eq28
  Salt.MR.sec9_eq28_exit
  Salt.MR.rpow_neg_anti
  Salt.MR.H0door_pos
  Salt.MR.exp_le_H0door
  Salt.MR.H0door_anti
  Salt.MR.doorGrade_pos
  Salt.MR.doorGrade_anti
  Salt.MR.log_ge_of_H0door_le
  Salt.MR.doorGrade_le_of_H0door_le
  Salt.MR.le_log_of_H0door_le
  Salt.MR.log_scale_threshold
  Salt.MR.regime_hthr_of_scale
  Salt.MR.regime_W_headroom_of_H0door
  Salt.MR.budget_head_at_H0door
  Salt.MR.budget_head_grade_closed
  Salt.MR.budget_head_grade_closed_g
  Salt.MR.LFunction_band_lower
  Salt.MR.eulerFactor_prod_lower
  Salt.MR.LFunction_band_lower_principal
  Salt.MR.chi_Llower_band
  Salt.MR.chi_floor_all_complete
  Salt.MR.chi_floor_all_complete_twisted
  Salt.MR.zeta_upper_band
  Salt.MR.LFunctionTrivChar_norm_le
  Salt.MR.norm_deriv_LFunction_ball_le
  Salt.MR.LFunction_lower_of_L1
  Salt.MR.chi_Llower_real_far
  Salt.MR.chi_Llower_real_of_L1
  Salt.MR.chi_floor_real_of_L1
  Salt.MR.exists_L1_lower
  Salt.MR.nearRat_mono
  Salt.MR.nearRat_neg
  Salt.MR.exists_dirichlet_approx
  Salt.MR.nearRat_of_pos
  Salt.MR.exists_large_den_of_not_nearRat
  Salt.MR.one_le_arcDen
  Salt.MR.arcRadius_pos
  Salt.MR.arcDen_mono
  Salt.MR.arcRadius_mono
  Salt.MR.exists_large_den_of_minor
  Salt.MR.mem_bigXi_iff
  Salt.MR.norm_expSum_le_sum
  Salt.MR.not_mem_bigXi_of_norm_lt
  Salt.MR.threshold_le_sum_inv_of_mem
  Salt.MR.primeWindow_bounds
  Salt.MR.inv_p_le_of_mem
  Salt.MR.le_inv_p_of_mem
  Salt.MR.norm_expSum_le_card
  Salt.MR.bigXiArc_of_minorArc
  Salt.MR.nearRat_arc_zero
  Salt.MR.bigXiArc_mono
  Salt.MR.farErr34_local_closes_of_gate
  Salt.MR.regimeEnlargeX_x
  Salt.MR.regimeEnlargeX_omega
  Salt.MR.regimeEnlargeX_eps
  Salt.MR.regimeEnlargeX_Hlo
  Salt.MR.regimeEnlargeX_Hhi
  Salt.MR.s5_spec
  Salt.MR.s5_spec_of_le
  Salt.MR.anchor_le_gJoin
  Salt.MR.s5x0_le_gJoin
  Salt.MR.carm_le_gJoin
  Salt.MR.mrThreshold_le_gJoin
  Salt.MR.omega_le_gJoin
  Salt.MR.gJoin_pos
  Salt.MR.chowlaRegime_exists_param_head
  Salt.MR.chowlaRegime_exists_param_of_head
  Salt.MR.chowlaRegime_exists_param_head_gJoin
  Salt.MR.s5x0_le_of_gJoin
  Salt.MR.s5_at_regime
  Salt.MR.mrThreshold_le_x
  Salt.MR.heps_arm_of_epsFloor
  Salt.MR.regime_head_W_headroom
  Salt.MR.L1LowerEffective_half_iff
  Salt.MR.log_le_two_mul_sqrt
  Salt.MR.logq_absorbed
  Salt.MR.door_L1_absorbed
  Salt.MR.door_L1_absorbed_subexp
  Salt.MR.debit_le_affine_log
  Salt.MR.door_L1_debit_absorbed
  Salt.MR.chi_floor_real_uniform
  Salt.MR.chi_floor_real_door
  Salt.MR.dhA_sqrt_weighted_floor
  Salt.MR.arcDen_nonneg
  Salt.MR.nearRat_of_nearRatTight
  Salt.MR.nearRatTight_imp_nearRat
  Salt.MR.nearRatTight_mono
  Salt.MR.nearRatTight_neg
  Salt.MR.nearRatTight_zero
  Salt.MR.exists_large_den_of_not_nearRatTight
  Salt.MR.exists_large_den_of_minorTight
  Salt.MR.bigXiArcTight_of_minorArcTight
  Salt.MR.bigXiArc_of_bigXiArcTight
  Salt.MR.minorArcBound_of_minorArcBoundTight
  Salt.MR.nearRatTight_arc_zero
  Salt.MR.bigXiArcTight_mono
  Salt.MR.gJR_ofReal
  Salt.MR.lemma5R
  Salt.MR.lemma5_budget_diff
  Salt.MR.one_le_log_of_exp_le
  Salt.MR.hTwo_pos
  Salt.MR.hTwo_le_self
  Salt.MR.hTwo_eq_mul_rpow_neg
  Salt.MR.eq26
  Salt.MR.eq26_pinned
  Salt.MR.gJR_one
  Salt.MR.gJR_mul
  Salt.MR.blockOmega_pow_eq_zero_iff
  Salt.MR.gJR_prime_pow
  Salt.MR.gJR_abs_le_one
  Salt.MR.Lemma4Datum.gJR_mul
  Salt.MR.window_defect_bound
  Salt.MR.shortSum_eq26_window
  Salt.MR.sec9_R_eq_zero_of_card
  Salt.MR.log_scale_threshold_1500
  Salt.MR.regime_hthr_of_scale_1500
  Salt.MR.regime_W_headroom_of_floor_1500
  Salt.MR.regime_W_headroom_of_H0door_1500
  Salt.MR.regime_head_W_headroom_1500
  Salt.MR.W_second_arm
  Salt.MR.W_second_arm_of_scale
  Salt.MR.door_L1_absorbed_w
  Salt.MR.door_L1_absorbed_12
  Salt.MR.door_L1_debit_absorbed_w
  Salt.MR.door_L1_debit_absorbed_12
  Salt.MR.chi_floor_real_door_w
  Salt.MR.chi_floor_real_door_12
  Salt.MR.Adoor_ge
  Salt.MR.one_le_Adoor
  Salt.MR.Adoor_cast
  Salt.MR.calE_door_two
  Salt.MR.log_four_M_door
  Salt.MR.log_calE_door_two
  Salt.MR.calFrameK_satisfiable_door
  Salt.MR.levelGates_calibrated_door
  Salt.MR.eq28_door_clears
  Salt.MR.log_calQK_door_one
  Salt.MR.Adoor_eq_four_mul
  Salt.MR.calP_door_one_ge
  Salt.MR.calP_door_one_rpow_quarter
  Salt.MR.one_le_log_calQK_door_one
  Salt.MR.H1door_two
  Salt.MR.H1door_cube
  Salt.MR.H1door_pin
  Salt.MR.calFrameK_satisfiable_doorH1
  Salt.MR.levelGates_calibrated_doorH1
  Salt.MR.mrAlpha_door_one
  Salt.MR.H1door_level1_identity
  Salt.MR.H1door_level1_certificate
  Salt.MR.level1_term_door_decays
  Salt.MR.sec9_eq28_const
  Salt.MR.eq28_clears_of_M_const
  Salt.MR.sec9_eq28_exit_const
  Salt.MR.card_blockfree_le
  Salt.MR.hreg_of_small_h
  Salt.MR.hbig_of_floor
  Salt.MR.herr_of_mertens
  Salt.MR.two_le_calP
  Salt.MR.herr_of_floor
  Salt.MR.hsieve_of_engine
  Salt.MR.memS_calFamily
  Salt.MR.memS_congr
  Salt.MR.card_notMemS_pin
  Salt.MR.sec9_eq28_exit_calFamily
  Salt.MR.eK_eq_eR
  Salt.MR.norm_one_sub_eR
  Salt.MR.eR_add_intCast
  Salt.MR.eR_mul_natCast
  Salt.MR.dist₁_eq_sub_zero
  Salt.MR.abs_sin_pi_mul_add_intCast
  Salt.MR.two_mul_dist₁_le_abs_sin
  Salt.MR.inv_le_dist₁_intCast_div
  Salt.MR.vaughan_expSum
  Salt.MR.norm_moebius_le
  Salt.MR.norm_typeICoeff_le
  Salt.MR.norm_typeIIData_le
  Salt.MR.geom_phase_card_bound
  Salt.MR.geom_phase_dist_bound
  Salt.MR.minTerm_le_left
  Salt.MR.minTerm_le_inv
  Salt.MR.minTerm_nonneg
  Salt.MR.minTerm_mono_left
  Salt.MR.geom_phase_bound
  Salt.MR.one_add_log_le_two_mul_log
  Salt.MR.sum_range_inv_succ_le
  Salt.MR.minsum_residue_count
  Salt.MR.minsum_block_core
  Salt.MR.minsum_block
  Salt.MR.minsum_shift
  Salt.MR.four_mul_ge_of_mem_blockExc_zero
  Salt.MR.minsum_d_dependent
  Salt.MR.shortSum_measurable'
  Salt.MR.shortSum_sub_const_sq_intervalIntegrable
  Salt.MR.rpow_inv20_sq
  Salt.MR.one_div_rpow_absorb
  Salt.MR.meansq_shift_of_pointwise
  Salt.MR.thm3_of_step1_and_eq26
  Salt.MR.thm3_meansq_pinned
  Salt.MR.hTwo_meets_kernel_binder
  Salt.MR.eq26_carrier_hrange
  Salt.MR.thm3_meansq_of_kernel
  Salt.MR.chebyshev_exceptional_set
  Salt.MR.thm3_chebyshev_exceptional
  Salt.MR.thm3_pair_exceptional
  Salt.MR.thm3_pair_nonvacuous
  Salt.MR.calFrameK_satisfiable_scaled
  Salt.MR.Ah_mul_le
  Salt.MR.Ah_one_sided
  Salt.MR.Ah_containment
  Salt.MR.calFrameK_satisfiable_Ah
  Salt.MR.levelGates_calibrated_Ah
  Salt.MR.log_nat_nonneg
  Salt.MR.log_nat_mono
  Salt.MR.log_nat_monotone
  Salt.MR.dist₁_neg_zero
  Salt.MR.inner_range_eq
  Salt.MR.eR_phase_reindex
  Salt.MR.partial_phase_bound
  Salt.MR.inner_phase_bound
  Salt.MR.sum_Ioc_abel
  Salt.MR.norm_sum_Ioc_weighted_le
  Salt.MR.inner_log_phase_bound
  Salt.MR.typeI_one_bound
  Salt.MR.typeI_two_bound
  Salt.MR.typeI_bound
  Salt.MR.typeIIData_eq_zero_of_le
  Salt.MR.typeII_inner_vanishes
  Salt.MR.typeII_block_eq_zero
  Salt.MR.dpair_range_eq
  Salt.MR.typeIIBlockBd_nonneg
  Salt.MR.typeII_block_bound
  Salt.MR.norm_lambda_head_le
  Salt.MR.lambda_head_add_tail
  Salt.MR.typeII_dyadic_bound
  Salt.MR.vinogradov_lambda
  Salt.MR.vinogradov_lambda_dyadic
  Salt.MR.vinogradov_lambda_sq
  Salt.MR.sqrt_add_le_sqrt_add_sqrt
  Salt.MR.norm_sum_Ioc_weighted_le_antitone
  Salt.MR.expSum_eq_indicator
  Salt.MR.sum_lambda_not_prime_le
  Salt.MR.norm_thetaPhase_sub_lambdaPhase
  Salt.MR.prime_sum_to_lambda
  Salt.MR.approx_reduced
  Salt.MR.approx_c_form
  Salt.MR.expSum_abel
  Salt.MR.typeII_dyadic_trunc
  Salt.MR.typeIIBlockBd_le_crude
  Salt.MR.typeII_dyadic_sum_le
  Salt.MR.vinoBd_mono
  Salt.MR.lambdaPhase_le
  Salt.MR.expSum_le_vinoBd
  Salt.MR.two_le_winBot
  Salt.MR.winBot_le_winTop
  Salt.MR.one_le_vaughanW
  Salt.MR.vaughanW_sq_le
  Salt.MR.winTop_le_pow
  Salt.MR.primeWindow_sub
  Salt.MR.mem_primeWindow_of_mem
  Salt.MR.exists_q_expSum_le
  Salt.MR.minorArcBoundTight_of_exitClose
  Salt.MR.minorArcBoundTight_twelve_of_close
  Salt.MR.bigXiArcTight_twelve_of_close
  Salt.MR.sqrt_le_of_sq_le
  Salt.MR.mul_three_le
  Salt.MR.pow24_le_exp
  Salt.MR.exit_collect
  Salt.MR.exitBd_lt_of_arms
  Salt.MR.exitClose_twelve
  Salt.MR.minorArcBoundTight_twelve
  Salt.MR.bigXiArcTight_twelve
  Salt.MR.norm_one_sub_le_of_one_le_re
  Salt.MR.norm_eulerProd_lower
  Salt.MR.eulerCorr_prod_lower_real
  Salt.MR.eulerCorr_one_lower
  Salt.MR.primitiveCharacter_ne_one
  Salt.MR.primitiveCharacter_quadratic
  Salt.MR.primitiveCharacter_conductor_le
  Salt.MR.norm_LFunction_one_eq_re
  Salt.MR.L1LowerEffective_descend
  Salt.MR.primitiveCharacter_neg_one
  Salt.MR.primitiveCharacter_odd_iff
  Salt.MR.L1LowerEffectiveOdd_descend
  Salt.MR.rootNumber_norm_eq_one
  Salt.MR.mod_ne_one_of_odd
  Salt.MR.odd_inv
  Salt.MR.LFunction_apply_zero_eq_completed_odd
  Salt.MR.LFunction_apply_one_eq_completed_odd
  Salt.MR.LFunction_apply_zero_odd_fe
  Salt.MR.norm_LFunction_apply_one_odd
  Salt.MR.inv_eq_self_of_sq_eq_one
  Salt.MR.LFunction_apply_zero_ne_zero_odd
  Salt.MR.norm_LFunction_one_eq_re'
  Salt.MR.rpow_three_halves
  Salt.MR.L1_lower_odd_of_L0_floor
  Salt.MR.LFunction_apply_zero_eq_sum_of_sawtooth
  Salt.MR.val_cases_of_sq_eq_one
  Salt.MR.exists_int_sum_val_mul
  Salt.MR.L0_floor_of_sawtooth
  Salt.MR.L1_lower_odd_primitive_of_sawtooth
  Salt.MR.primitiveCharacter_ne_one'
  Salt.MR.primitiveCharacter_odd
  Salt.MR.primitiveCharacter_sq_eq_one
  Salt.MR.LFunction_apply_one_descent
  Salt.MR.descent_prod_eq_real
  Salt.MR.L1_lower_odd_of_sawtooth
  Salt.MR.l1LowerOddEffective_of_l1LowerEffective
  Salt.MR.l1LowerOddEffective_of_sawtooth
  Salt.MR.l1LowerOddEffective_one_of_sawtooth
  Salt.MR.exp_add_exp_sub_two_cos_le
  Salt.MR.a3_prefactor_band_le_two
  Salt.MR.a3_prefactor_max_le_three
  Salt.MR.a3_logQ_third_mono
  Salt.MR.a3_logQ_term_mono
  Salt.MR.a3_head_le_third_grade
  Salt.MR.parseval_a3_join
  Salt.MR.far_of_mem_closedBall
  Salt.MR.closedBall_subset_far
  Salt.MR.ball_inf_floor_of_mem_far
  Salt.MR.abs_sum_mul_le_of_bounded
  Salt.MR.abs_sum_shift_mul_le_of_bounded
  Salt.MR.tendsto_tsum_div_rpow
  Salt.MR.exp_pow_im
  Salt.MR.sin_pi_mul_pos
  Salt.MR.one_sub_cos_two_pi_mul
  Salt.MR.one_sub_exp_eq
  Salt.MR.norm_one_sub_exp
  Salt.MR.exp_ne_one
  Salt.MR.abs_sum_sin_le
  Salt.MR.tendsto_sum_sin_div_nat
  Salt.MR.sinZeta_apply_one
  Salt.MR.hurwitzZetaOdd_apply_zero
  Salt.MR.coe_unitAddCircle_ne_zero
  Salt.MR.hurwitzZeta_apply_zero
  Salt.MR.sawtoothOdd
  Salt.MR.L1_lower_odd
  Salt.MR.l1LowerOddEffective_pi
  Salt.MR.l1LowerOddEffective_one
  Salt.MR.vtail_single_mean_sq_bound
  Salt.MR.vtail_single_meansq_damped
  Salt.MR.vtail_single_meansq_kernel
  Salt.MR.vtail_single_meansq_kernel_neg
  Salt.MR.contour_single_h_kernel
  Salt.MR.perron_gap_single_le_gapMaj
  Salt.MR.parseval_single_h
  Salt.MR.pretFloorShape_def
  Salt.MR.pretFloorShape_le_of_le
  Salt.MR.dist_floor_far_sep
  Salt.MR.dist_floor_far_range
  Salt.MR.M_win_bddBelow
  Salt.MR.M_win_window_nonempty
  Salt.MR.M_win_le
  Salt.MR.M_win_approx
  Salt.MR.M_win_anti
  Salt.MR.M_window_bridge
  Salt.MR.M_window_bridge_inf
  Salt.MR.M_window_bridge_seam
  Salt.MR.M_rangeCap_at_self
  Salt.MR.M_rangeCap_window_nonempty
  Salt.MR.M_rangeCap_le_M_range
  Salt.MR.Mrange_cap_one_floor
  Salt.MR.Mrange_one_floor_2X
  Salt.MR.log_sq_le_self
  Salt.MR.contour_height_le_two_mul
  Salt.MR.pretDistSq_ellLin_eq
  Salt.MR.capFreeFloor_of_row_floor
  Salt.MR.no_pocket_of_floor
  Salt.MR.box_gate_le_X
  Salt.MR.pocketSocket_of_row
  Salt.MR.pocketSocket_of_floor
  Salt.MR.ball_leg_vacuous_at_zero
  Salt.MR.cofactor_Rbd34_local_nocap
  Salt.MR.tL_supply_discharged34_local_nocap
  Salt.MR.hUG34_supplied_nocap
  Salt.MR.hUG34_fully_priced_nocap
  Salt.MR.hUG34_unconditional_nocap
  Salt.MR.hUG34_unconditional_beats_door_nocap
  Salt.MR.seam_row_calibratedK_nocap
  Salt.MR.seam_row_number_nocap
  Salt.MR.seam_row_number_capfree
  Salt.MR.capFreeFloor_of_capFreeFloor3
  Salt.MR.capFreeFloor3_of_row_floor
  Salt.MR.no_pocket_of_floor3
  Salt.MR.box_gate_le_3X
  Salt.MR.pocketSocket_of_floor3
  Salt.MR.cofactor_Rbd34_local_nocap3
  Salt.MR.tL_supply_discharged34_local_nocap3
  Salt.MR.hUG34_supplied_nocap3
  Salt.MR.hUG34_fully_priced_nocap3
  Salt.MR.hUG34_unconditional_nocap3
  Salt.MR.seam_row_calibratedK_nocap3
  Salt.MR.seam_row_number_nocap3
  Salt.MR.seam_row_number_capfree3
  Salt.MR.A2Frame3.box_at
  Salt.MR.A2Frame3.ksGate_at
  Salt.MR.restrictAbove_one_prime
  Salt.MR.ellLinInv_congr_primes
  Salt.MR.ellLin_congr_primes
  Salt.MR.smoothPart_one_eq_sPart
  Salt.MR.sPart_factorization
  Salt.MR.sPart_factorization_smoothPart
  Salt.MR.sPart_apply
  Salt.MR.sPart_prime_pow
  Salt.MR.sPart_apply_prime
  Salt.MR.sPart_prime_pow_norm_le
  Salt.MR.sPart_isMultiplicative
  Salt.MR.sPart_eq_zero_of_not_squarefull
  Salt.MR.squarefull_of_sPart_ne_zero
  Salt.MR.sum_Icc_divisorsAntidiagonal
  Salt.MR.filter_mul_le_eq_Icc_div
  Salt.MR.sum_hyperbola_eq_nested
  Salt.MR.conv_partial_sum_dissect
  Salt.MR.conv_partial_sum_dissect_range
  Salt.MR.pretDistSq_scale_gap
  Salt.MR.mertens_gap_le
  Salt.MR.pretDistSq_scale_gap_dilate
  Salt.MR.norm_ellLinInv_le_one
  Salt.MR.norm_sPart_le_card_divisors
  Salt.MR.card_divisors_mul_le_real
  Salt.MR.sum_tau_weight_le
  Salt.MR.sum_tau_le
  Salt.MR.sum_tau_sq_le
  Salt.MR.sum_tau_cube_le
  Salt.MR.rpow_neg_three_halves
  Salt.MR.rpow_neg_two
  Salt.MR.step_three_halves
  Salt.MR.step_two
  Salt.MR.sum_Icc_eq_sum_range_of_zero
  Salt.MR.sum_range_three_halves_le
  Salt.MR.sum_range_two_le
  Salt.MR.sum_Icc_three_halves_le
  Salt.MR.sum_Icc_two_le
  Salt.MR.prime_of_mem_factorization_support
  Salt.MR.one_le_sqPartOf
  Salt.MR.one_le_cubePartOf
  Salt.MR.sqPartOf_sq_mul_cubePartOf_cube
  Salt.MR.sqPartOf_le
  Salt.MR.cubePartOf_le
  Salt.MR.rpow_sq_cube_le
  Salt.MR.sPart_dirichlet_bound_three_quarters
  Salt.MR.sPart_dirichlet_bound
  Salt.MR.sPart_tail_bound
  Salt.MR.cm_pow
  Salt.MR.cm_isMultiplicative
  Salt.MR.alt_sum_shift
  Salt.MR.sPart_cm_prime_pow
  Salt.MR.sPart_cm_prime_pow_norm_le_one
  Salt.MR.sPart_factorization_prod
  Salt.MR.sPart_cm_norm_le_one
  Salt.MR.sPart_cm_factorization_even
  Salt.MR.sPart_cm_square_support
  Salt.MR.rpow_sq_neg_three_quarters
  Salt.MR.sPart_cm_dirichlet_bound
  Salt.MR.seamCoeff_one_eq_one
  Salt.MR.seamCoeff_isMultiplicative
  Salt.MR.norm_seamCoeff_trivial_le
  Salt.MR.sPart_seamCoeff_factorization
  Salt.MR.sPart_seamCoeff_dirichlet_bound
  Salt.MR.sPart_seamCoeff_tail_bound
  Salt.MR.seam_coef_contract_forces_vanishing
  Salt.MR.seam_coef_contract_absurd
  Salt.MR.far_tail_crude
  Salt.MR.seam_Msup_family
  Salt.MR.thm_a2_spine
  Salt.MR.bandSupS_seamRad
  Salt.MR.bandLterm_pos
  Salt.MR.bandTail_nonneg
  Salt.MR.bandSupS_nonneg
  Salt.MR.ballErr_le_radius
  Salt.MR.band_sup_of_center
  Salt.MR.band_sup_supplied_Y
  Salt.MR.band_integral_of_sup
  Salt.MR.t0_band_supply
  Salt.MR.seamCoefW_of_global
  Salt.MR.seamCoefWLevels_of_global
  Salt.MR.winCut_supp
  Salt.MR.winCut_supp_real
  Salt.MR.norm_winCut_le
  Salt.MR.winCut_of_mem
  Salt.MR.seamCoefW_winCut
  Salt.MR.seam_coef_contract_windowed_sat
  Salt.MR.spoly_ramare_split_mr_windowed
  Salt.MR.ramErr_decomp_mr_windowed
  Salt.MR.ramErr_moment_split_mr_windowed
  Salt.MR.lemma12_meansq_mr_windowed
  Salt.MR.lemma12_meansq_mr_blockSupport_windowed
  Salt.MR.lemma12_meansq_mr_consume_windowed
  Salt.MR.second_window_le_first_row
  Salt.MR.ellLin_seamCoeff
  Salt.MR.eIu_natCast_mul
  Salt.MR.center_halasz_supply_wide
  Salt.MR.dilGap_div
  Salt.MR.pretDistSq_floor_dilate
  Salt.MR.dilated_scale_grade
  Salt.MR.hCenter_dissected
  Salt.MR.seam_ball_leg_station_M_gen
  Salt.MR.bandLterm_seamT0_le
  Salt.MR.t0BandB_grade
  Salt.MR.egap_small
  Salt.MR.thm_a2'_of_rows
  Salt.MR.calFrameK_doorH1_at
  Salt.MR.a2_row_cap_of_not_capFreeFloor
  Salt.MR.A2Frame.box_at
  Salt.MR.A2Frame.ksGate_at
  Salt.MR.a2Rows_of_capfree
  Salt.MR.a2Rows_of_cap
  Salt.MR.thm_a2'
  Salt.MR.a2_station_supply_pointwise
  Salt.MR.a2Frame_satisfiable_partial
  Salt.MR.a2Rows_of_capfree3
  Salt.MR.a2Frame3_satisfiable_partial
  Salt.MR.witKk_cut
  Salt.MR.witMt_window
  Salt.MR.witness_window_geometry
  Salt.MR.ramRbot_le_scale
  Salt.MR.witMs_range
  Salt.MR.witM0_le
  Salt.MR.witM0_two_le
  Salt.MR.witMs_le_four_mul
  Salt.MR.ramI_self
  Salt.MR.ramQbase_at_pin
  Salt.MR.ramI_self_index_ge
  Salt.MR.h_ceiling_gate
  Salt.MR.c4_at_height
  Salt.MR.tlBlockGates34_at_witness
  Salt.MR.blocks_at_witness
  Salt.MR.thinBundleG_mono_T
  Salt.MR.thin_at_witness
  Salt.MR.ksGate_at_witness
  Salt.MR.calibration_at_witness
  Salt.MR.Tstar2_le_self
  Salt.MR.Tstar2_box_at_witness
  Salt.MR.witEP2_nonneg
  Salt.MR.err_at_witness
  Salt.MR.a2Frame3_witness
  Salt.MR.row_ladder_at_witness
  Salt.MR.seam_ball_leg_station_M_hoisted
  Salt.MR.hStation_of_hoisted
  Salt.MR.dist_floor_far_sep_at
  Salt.MR.dist_floor_far_reach
  Salt.MR.M_window_bridge_reach
  Salt.MR.M_window_bridge_seam_reach
  Salt.MR.M_window_bridge_seam_2X
  Salt.MR.M_window_bridge_seam_3X
  Salt.MR.hM0_at_centre
  Salt.MR.pretFloorShape_quarter_at_pow
  Salt.MR.pretFloorShape_quarter_sq
  Salt.MR.Tstar_two_mul_le_quarter
  Salt.MR.seamGateRstar_le_two_mul
  Salt.MR.norm_lamCoeff_le_one
  Salt.MR.windowExpSum_eq_offWindowSum
  Salt.MR.Ioc_eq_map_rebase
  Salt.MR.offWindowSum_eq_rebase
  Salt.MR.norm_offWindowSum
  Salt.MR.norm_windowExpSum_le
  Salt.MR.windowExpSum_eq_rebase
  Salt.MR.norm_windowExpSum_eq_absWindowSum
  Salt.MR.norm_absWindowSum_le
  Salt.MR.nearRatTight_of_bigXiArcTight
  Salt.MR.mrtUniformityXi_of_absWindowBound
  Salt.MR.mrtUniformityXi_of_absWindowBound_twelve
  Salt.MR.sum_Ioc_abel_complex
  Salt.MR.sum_Ioc_abel_complex_const
  Salt.MR.norm_sum_Ioc_abel_le
  Salt.MR.norm_sum_Ioc_weighted_le_drift
  Salt.MR.norm_eR_succ_sub
  Salt.MR.norm_phase_sum_Ioc_ibp
  Salt.MR.norm_phase_sum_Ioc_drift
  Salt.MR.norm_phase_sum_Ioc_drift_sup
  Salt.MR.abs_mul_window_le_of_arcDen
  Salt.MR.norm_phase_sum_arcDen_drift
  Salt.MR.norm_phase_sum_arcDen_drift_sup
  Salt.MR.conj_chi_eq_inv
  Salt.MR.conj_chi_eq_invChar
  Salt.MR.chi_inv_eq_conj_chi
  Salt.MR.norm_chi_of_isUnit
  Salt.MR.totient_cast_ne_zero
  Salt.MR.totient_cast_pos
  Salt.MR.sum_conj_chi_mul_chi
  Salt.MR.sum_chi_mul_conj_chi
  Salt.MR.indicator_eq_inv_totient_sum
  Salt.MR.weight_indicator_eq_inv_totient_sum
  Salt.MR.lam_indicator_eq_lamChi_sum
  Salt.MR.lam_modEq_indicator_eq_lamChi_sum
  Salt.MR.sum_weight_residue_eq
  Salt.MR.sum_lam_residue_eq
  Salt.MR.norm_sum_lam_residue_le
  Salt.MR.isUnit_natCast_of_coprime
  Salt.MR.sum_lam_modEq_residue_eq
  Salt.MR.norm_sum_lam_modEq_residue_le
  Salt.MR.liouvilleC
  Salt.MR.liouvilleC_mul
  Salt.MR.liouvilleC_prime
  Salt.MR.liouvilleC_norm
  Salt.MR.liouvilleC_norm_le_one
  Salt.MR.primeFactors_lt_of_lt
  Salt.MR.blockPrimeDivs_eq_empty_of_small
  Salt.MR.blockPrimeDivs_dilate
  Salt.MR.blockOmega_dilate
  Salt.MR.blockOmega_dilate_of_lt
  Salt.MR.memS_dilate
  Salt.MR.memS_dilate_of_lt
  Salt.MR.memS_dilate_of_lt_bot
  Salt.MR.indicator_mul_dilate
  Salt.MR.indicator_mul_dilate_liouville
  Salt.MR.sum_memS_dilate
  Salt.MR.gcd_dvd_of_modEq
  Salt.MR.coprime_reduced_of_gcd
  Salt.MR.modEq_dilate_iff
  Salt.MR.sum_reindex_dilate
  Salt.MR.residue_split_dilate
  Salt.MR.residue_split_dilate_liouville
  Salt.MR.calP_door_one_eq
  Salt.MR.two_pow_le_calP_door_one
  Salt.MR.lt_calP_door_one
  Salt.MR.d_lt_calP_door_one
  Salt.MR.logH_pow_twelve_lt
  Salt.MR.door_dilation_gate
  Salt.MR.calP_door_mono
  Salt.MR.memS_dilate_door
  Salt.MR.residue_split_dilate_door

open Salt.Tactic in
#audit_axioms Salt.MR.chi_Llower_band_single
  Salt.MR.chi_Llower_band_uniform
  Salt.MR.chi_floor_band_uniform
  Salt.MR.chi_floor_band_uniform_twisted
  Salt.MR.capfree_threshold
  Salt.MR.capfree_threshold_lt
  Salt.MR.band_gate_threshold
  Salt.MR.band_gate_threshold_cfb
  Salt.MR.quality_gate_threshold
  Salt.MR.siegelBandB_spec
  Salt.MR.modulus_bound_mono

open Salt.Tactic in
#audit_axioms Salt.MR.vk_height_facts
  Salt.MR.log_vkProfile
  Salt.MR.chi_Llower_341_of_ub
  Salt.MR.chi_Llower_341_height
  Salt.MR.chi_Llower_341_vk
  Salt.MR.one_le_vkEulerCorr
  Salt.MR.vkEulerCorr_pos
  Salt.MR.norm_LFunction_le_vkEulerCorr
  Salt.MR.vkProfile_const_mul
  Salt.MR.vkTwistUB_of_primitive
  Salt.MR.vkDebitConst_nonneg
  Salt.MR.vkMidDebit_nonneg
  Salt.MR.vkDebitConst_vkEulerCorr
  Salt.MR.vk_debit_le
  Salt.MR.chi_floor_vk_pointwise
  Salt.MR.vk_capfree_threshold
  Salt.MR.capFreeFloor3_lamChi_vk
  Salt.MR.capFreeFloor_lamChi_vk
  Salt.MR.vk_twist_block_le
  Salt.MR.vk_twist_head_le
  Salt.MR.char_sum_fourier_le
  Salt.MR.vk_twist_head_abs_le
  Salt.MR.vk_char_head_le
  Salt.MR.one_le_vkTwistConst
  Salt.MR.vkTwistConst_mono
  Salt.MR.vkProfile_mono
  Salt.MR.vk_LFunction_bridge_le_primitive
  Salt.MR.vkTwistUB_holds
  Salt.MR.capFreeFloor3_lamChi_unconditional

open Salt.Tactic in
#audit_axioms Salt.MR.cff_scale_facts
  Salt.MR.cff_box_loglog
  Salt.MR.cff_box_logloglog
  Salt.MR.primeDivSum_le_modulus
  Salt.MR.chi_floor_real_bulk
  Salt.MR.chi_floor_band_arm
  Salt.MR.capFreeFloor3_all_chi
  Salt.MR.capFreeFloor_all_chi
  Salt.MR.cffK_nonneg
  Salt.MR.cffK_spec
  Salt.MR.lamChi_eq_liouChi_prime
  Salt.MR.pretDistSq_liouChi_eq
  Salt.MR.norm_liouChi_le_one
  Salt.MR.capFreeFloor3_liouChi_of_lamChi
  Salt.MR.capFreeFloor3_liouChi_all

-- M4-4 (`M4Dyadic`) — the c.o.v., the trivial cut, and THE OUTER DYADIC COVER
open Salt.Tactic in
#audit_axioms Salt.MR.dyadScale_le_self
  Salt.MR.two_mul_dyadScale_succ
  Salt.MR.dyadIdx_le
  Salt.MR.dyadCount_le
  Salt.MR.dyadCount_logPow_le
  Salt.MR.dyadCount_logPow_le_numeral
  Salt.MR.pow_ten_le_two_pow_dyadIdx
  Salt.MR.dyadScale_dyadIdx_le
  Salt.MR.dyadPart_window
  Salt.MR.sum_dyadPart
  Salt.MR.sum_dyadCover
  Salt.MR.exists_dyadPart_mem
  Salt.MR.exists_dyadScale_cover
  Salt.MR.dyadScale_floor_of_cover
  Salt.MR.sqrt_le_of_depth
  Salt.MR.two_mul_pow_ten_le_sqrt
  Salt.MR.sqrt_le_dyadScale
  Salt.MR.exp_one_le_of_sqrt_le
  Salt.MR.three_le_of_sqrt_le
  Salt.MR.log_dyadScale
  Salt.MR.log_sub_log_le_log_of_floor
  Salt.MR.loglog_sub_log_two_le
  Salt.MR.h_ceiling_transfer
  Salt.MR.five_le_loglog_transfer
  Salt.MR.image_div_window_dilate
  Salt.MR.sum_window_dilate
  Salt.MR.meanSq_scale_invariant
  Salt.MR.meanSq_shortSum_scale
  Salt.MR.sum_div_le_of_window
  Salt.MR.le_sum_div_of_window
  Salt.MR.sum_div_dyadPart_le
  Salt.MR.le_sum_div_dyadPart
  Salt.MR.norm_absWindowSum_le_thresh
  Salt.MR.norm_absWindowSum_le_trivThresh
  Salt.MR.integral_logMeasure_le_of_le
  Salt.MR.integral_logMeasure_absWindowSum_le_thresh
  Salt.MR.card_shortWindow_le
  Salt.MR.norm_shortSum_le
  Salt.MR.sum_range_le_mul
  Salt.MR.sum_range_le_mul_sup'
  Salt.MR.dyadCover_total_le
  Salt.MR.dyadCover_total_le_sup'
  Salt.MR.dyadCover_total_le_logPow

-- CFB (`T0BandCapFree`) — THE CAP-FREE `T₀`-BAND: the per-frequency sup, the crude fold,
-- the band-strength floor (coefficient `7/30`), the two thresholds, and the `hT0band` exit
open Salt.Tactic in
#audit_axioms Salt.MR.cfb_sup_of_center
  Salt.MR.band_integral_of_sup_crude
  Salt.MR.cfb_band_loglog
  Salt.MR.cfb_band_logloglog
  Salt.MR.chi_floor_band_strength
  Salt.MR.chi_floor_band_nonreal
  Salt.MR.band_floor_M0
  Salt.MR.band_floor_M0_liouChi
  Salt.MR.cfb_gate_decay
  Salt.MR.cfb_floor_clears_gate
  Salt.MR.cfb_ballerr_le
  Salt.MR.cfbC₁_sq
  Salt.MR.cfbC₁_nonneg
  Salt.MR.cfb_exit_summand_le
  Salt.MR.cfb_t0band_supply
  Salt.MR.cfb_seam_floor_of_band
  Salt.MR.cfb_t0band_supply_chi

-- M4-6 (`M4Quality`) — THE QUALITY SUPPLY: the demand `(5e/2)·log W` (constant in `X`), its
-- exceedance at the `T₀`-band `M₀` (`cfbM0`, coefficient `7/30`) and at the bounded band
-- (`siegelBandB`, coefficient `1` — the C3 upgrade), the `W`-monotonicity glue, and the
-- SINGLE regime constant `m4QualityB` / joint threshold `m4JointThr` the spine's `g` clears
open Salt.Tactic in
#audit_axioms Salt.MR.m4Demand_door
  Salt.MR.one_le_m4W
  Salt.MR.m4Demand_nonneg
  Salt.MR.m4_exit_decay_of_quality
  Salt.MR.cfbM0_antitone_K
  Salt.MR.m4_quality_of_band
  Salt.MR.m4_log_le_div_eighty
  Salt.MR.m4_quality_of_band_hhi
  Salt.MR.m4_quality_band_coeff_one
  Salt.MR.m4_quality_band_coeff_one_liouChi
  Salt.MR.m4_quality_band_door
  Salt.MR.m4W_mono
  Salt.MR.m4_modulus_le
  Salt.MR.m4_modulus_nat_le
  Salt.MR.m4Wnat_mono
  Salt.MR.m4_quality_band_window
  Salt.MR.cfbK_nonneg
  Salt.MR.cfbK_spec
  Salt.MR.m4VKdebit_spec
  Salt.MR.cfbK_le_m4QualityB
  Salt.MR.siegelBandB_le_m4QualityB
  Salt.MR.cffK_le_m4QualityB
  Salt.MR.m4VKdebit_le_m4QualityB
  Salt.MR.m4QualityB_nonneg
  Salt.MR.m4JointThr_anchor
  Salt.MR.m4JointThr_qual
  Salt.MR.m4JointThr_band
  Salt.MR.m4JointThr_cff
  Salt.MR.m4_quality_of_joint
  Salt.MR.m4_band_of_joint
  Salt.MR.m4_capfree_of_joint

-- M4-5 (`M4MeanSq`) — THE ASSEMBLY CAPSTONE: `thm_a2'_of_rows` instantiated at the M4 datum
-- (`liouChi χ`), entered through `a2Rows_of_capfree3` with the frame from `a2Frame3_witness`,
-- the row ladder from `row_ladder_at_witness` and the floor from `capFreeFloor3_liouChi_all`;
-- the `X_d = X`, `N = 2X` joint pin; the `T₀`-band from `cfb_t0band_supply_chi` at the M4
-- datum plus the live-range transport into the `hT0band` slot (⚠ the A2-5 seam — the file's
-- header records why the band is a slot and not an inlined supplier); and the trivial-cut
-- dichotomy the dyadic consumer takes
open Salt.Tactic in
#audit_axioms Salt.MR.dpolyA_congr
  Salt.MR.mem_seamS0
  Salt.MR.m4BandDatum_supp
  Salt.MR.m4BandDatum_eq
  Salt.MR.dpolyA_seamS0_bandDatum
  Salt.MR.exp_exp_one_gt_three
  Salt.MR.exp_one_le_exp_exp_one
  Salt.MR.coef_widen_of_window
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_t0band_at_datum
  Salt.MR.m4_t0band_of_live
  Salt.MR.m4_trivial_branch
  Salt.MR.m4_meansq_or_trivial

-- M4-1 (`M4Sieve`) — THE `1_𝒮` INSERT: the insert identity at a general 1-bounded datum, the
-- short-window double count (the Fubini exchange the door needs), the half-open endpoint of
-- the sieve engine's window, the M-gate at the Basel collector, and the two exits (the
-- priced block and the door-shaped `logMeasure`-L¹ insert)
open Salt.Tactic in
#audit_axioms Salt.MR.memSCoeff_mul
  Salt.MR.norm_memSCoeff_le_one
  Salt.MR.ratioSumK_nonneg
  Salt.MR.card_notMemS_eq_sum
  Salt.MR.sum_memS_split
  Salt.MR.norm_sum_notMemS_le
  Salt.MR.norm_sum_memS_insert
  Salt.MR.norm_absWindowSum_memS_insert
  Salt.MR.norm_shortSum_memS_insert
  Salt.MR.norm_absWindowSum_memS_insert_liouville
  Salt.MR.norm_absWindowSum_memS_insert_liouChi
  Salt.MR.sum_window_double_count
  Salt.MR.sum_notMemSCount_le
  Salt.MR.sum_notMemSCount_weighted_le
  Salt.MR.door_window_not_one_block
  Salt.MR.integral_logMeasure_le_add
  Salt.MR.integral_logMeasure_le_of_weighted
  Salt.MR.card_notMemS_of_subset_Icc
  Salt.MR.notMemS_window_count_le
  Salt.MR.sieve_mass_le_basel
  Salt.MR.sieve_mass_le_quarter
  Salt.MR.sieve_mass_le_eighth
  Salt.MR.m4_sieve_block_mass
  Salt.MR.m4_sieve_insert
  Salt.MR.m4_sieve_insert_liouville
  Salt.MR.m4_sieve_insert_liouChi

-- M4-8 (`M4Door`) — THE DOOR GLUE: the `logMeasure` mass page (the singleton mass, the
-- `1/n ≍ 1/X′` block comparison, the `±1` endpoint band of width `2/H`, `Z ≥ log ω − 1` and
-- the sharp `∫ ≤ B/Z` normalisation); the H-offset dyadic `doorLadder` whose sieve-block fit
-- is UNCONDITIONAL (⟦THE OVERHANG FINDING⟧: exactly-dyadic blocks are unfittable, `b+H ≤ 2a`
-- forces `H ≤ 0`); the cover-summed sieve mass `m4_door_sieve_mass` — the seam M4-1's
-- vacuity finding named, with HS-6's half-open endpoint composed as the geometric
-- `4·2^k·H/x`; the `log ω` absorption into `M` (`k ≤ 3Z`, the gate `8C/δ ↦ 24C/δ`); and the
-- exit `m4_door_glue` with the inhabitation witness `doorCount_gates`
open Salt.Tactic in
#audit_axioms Salt.MR.logMeasure_singleton_toReal
  Salt.MR.door_norm_pos
  Salt.MR.door_norm_ge
  Salt.MR.door_norm_one_le
  Salt.MR.integral_logMeasure_le_div
  Salt.MR.sum_div_Ioc_le
  Salt.MR.le_sum_div_Ioc
  Salt.MR.card_shortWindow_ge
  Salt.MR.card_shortWindow_abs_sub_le_one
  Salt.MR.card_shortWindow_band
  Salt.MR.doorLadder_fit
  Salt.MR.doorLadder_floor
  Salt.MR.doorLadder_step_le
  Salt.MR.doorLadder_block_subset
  Salt.MR.doorLadder_upper
  Salt.MR.doorLadder_lower
  Salt.MR.doorLadder_inv_le
  Salt.MR.sum_range_two_pow_shift_le
  Salt.MR.natDiv_gt
  Salt.MR.doorLadder_reaches
  Salt.MR.doorCount_le
  Salt.MR.two_mul_le_two_pow_doorCount
  Salt.MR.sum_Ioc_ladder_split
  Salt.MR.door_cover_sum_le
  Salt.MR.m4_door_sieve_mass
  Salt.MR.door_count_le_three_mul_norm
  Salt.MR.door_mass_normalised_le
  Salt.MR.m4_door_glue
  Salt.MR.m4_door_glue_liouville
  Salt.MR.m4_door_glue_liouChi
  Salt.MR.doorCount_gates

-- M4-9 (`M4Exit`) — THE THREE-STEP EXIT into `MRTUniformityXi`: the pin `δ := doorGrade R.Hlo`
-- (positivity off `hHlo_floor`, the antitone-in-`H` transfer serving the whole window range),
-- the in-statement `C_MRT` gate `C_MRT·loglog H ≤ (log H)^{3/2}` with its scale discharge and
-- its floor `H0scale`, the `∀ξ`-outside-preserving weakening, and the socket whose ONE open
-- binder is M4-7's `hbd`
open Salt.Tactic in
#audit_axioms Salt.MR.lamCoeff_eq_liouvilleC
  Salt.MR.absWindowSum_lamCoeff_eq
  Salt.MR.integral_absWindowSum_lamCoeff_eq
  Salt.MR.two_le_regime_Hlo
  Salt.MR.log_pos_of_regime_le
  Salt.MR.doorGrade_regime_pos
  Salt.MR.doorGrade_le_regime_floor
  Salt.MR.doorGrade_regime_pin
  Salt.MR.mrtDeliveredGrade
  Salt.MR.mrtGate
  Salt.MR.mrtGate_of_sq_le
  Salt.MR.H0scale
  Salt.MR.H0scale_pos
  Salt.MR.sq_le_log_of_H0scale_le
  Salt.MR.mrtGate_transfer
  Salt.MR.mrtDeliveredGrade_le_doorGrade
  Salt.MR.mrtDeliveredGrade_le_pin
  Salt.MR.absWindowBound_le_pin
  Salt.MR.m4_exit_of_hbd
  Salt.MR.m4_exit_collision
  Salt.MR.m4_exit_socket
  Salt.MR.m4_exit_socket_False

-- M4-7 (`M4Close`) — THE ARITHMETIC CLOSE and THE WAVE'S EXIT: the `L²→L¹` step on the door's
-- (probability) measure with the `Z`-normalisation cancelled exactly, the five raw mean-square
-- summands priced against the quality demand's `W^{−5/2}` saving, the trivial-bound MARGIN
-- (`(log H)^{−15}` under `C(log H)^{−11/4}loglog H`, floor discharged off `hHlo_floor`), the
-- ⟦A2-5⟧ band transport named and landed, the M4-7 socket with its inhabitation witness, and
-- `m4_hbd_of_live` plugged into M4-9 to give `m4_door_contradiction_of_live`
open Salt.Tactic in
#audit_axioms Salt.MR.sum_harmonic_cauchy_schwarz
  Salt.MR.integral_logMeasure_le_sqrt
  Salt.MR.integral_logMeasure_le_sqrt_of_sq
  Salt.MR.m4RawMS
  Salt.MR.m4Saving
  Salt.MR.arcDen_twelve_eq_m4W
  Salt.MR.m4Saving_eq
  Salt.MR.sqrt_m4Saving
  Salt.MR.m4_quality_summand_le
  Salt.MR.m4_rawMS_le
  Salt.MR.m4_rawMS_le_saving
  Salt.MR.exp_one_le_log_regime_Hlo
  Salt.MR.exp_one_le_log_of_regime_le
  Salt.MR.sqrt_m4Saving_le_delivered
  Salt.MR.M4LiveAgree
  Salt.MR.M4BandTransport
  Salt.MR.m4_bandTransport
  Salt.MR.M4SievedDoorSq
  Salt.MR.m4_sievedDoorSq_trivial
  Salt.MR.M4DoorGates
  Salt.MR.M4GradeGate
  Salt.MR.m4_gradeGate_of_pricing
  Salt.MR.m4_hbd_of_live
  Salt.MR.m4_door_contradiction_of_live
  Salt.MR.m4_door_False_of_live
  Salt.MR.sum_liou_residue_eq
  Salt.MR.sum_liou_modEq_residue_eq
  Salt.MR.norm_sum_liou_modEq_residue_le
  Salt.MR.card_dirichletCharacter_eq_totient
  Salt.MR.inv_totient_sum_le

-- M4-B2 (`M4BridgePhase`) — ⟦BRIDGE #2⟧: the phase-convention bridge (`absWindowSum`'s inline
-- `exp(2πiα·)` ↔ `Salt.ExpSum.eR`, both directions, the `2π` inside the character), the
-- partial-sum family `S(K) = absWindowSum a K n β` with its length-indexed sup and the
-- reconciliation with `M4Abel`'s endpoint-indexed `sup'`, the drift composition at a
-- tight-major frequency (`1 + 2π·arcDen 12 H/q` over the sub-window sup at the rational),
-- and the uniformity hook: `M4SievedDoorSqSup` discharges `M4Close.M4SievedDoorSq` at the
-- `q`-GRADED drift cost `(1 + 2π·arcDen 12 H/q)²` read against the socket's own `q²` (the
-- two `q`'s are the SAME `NearRatTight` witness), with `qgraded_drift_price_le` the closing
-- arithmetic `(q + 2πA)² ≤ (1+2π)²A²` and `m4_sievedDoorSq_of_sup_uniform` the `q`-free
-- reading, plus the sup socket's own inhabitation witness
open Salt.Tactic in
#audit_axioms Salt.MR.exp_phase_eq_eR
  Salt.MR.eR_eq_exp_phase
  Salt.MR.eR_mul_split
  Salt.MR.absWindowSum_eq_eR_sum
  Salt.MR.phaseCoeff
  Salt.MR.sum_Ioc_phaseCoeff_eq
  Salt.MR.sum_Ioc_phaseCoeff_eq_sub
  Salt.MR.absWindowSum_eq_phaseCoeff_sum
  Salt.MR.subWindowSup
  Salt.MR.le_subWindowSup
  Salt.MR.norm_absWindowSum_le_subWindowSup
  Salt.MR.subWindowSup_nonneg
  Salt.MR.subWindowSup_le
  Salt.MR.subWindowSup_le_of_norm_le_one
  Salt.MR.abel_sup'_eq_subWindowSup
  Salt.MR.absWindowSum_add_eq_phase_sum
  Salt.MR.norm_absWindowSum_le_drift
  Salt.MR.norm_absWindowSum_le_drift_tight
  Salt.MR.norm_absWindowSum_le_ratPartial
  Salt.MR.integral_logMeasure_mono
  Salt.MR.integral_logMeasure_const_mul
  Salt.MR.M4SievedDoorSqSup
  Salt.MR.qgraded_drift_price_le
  Salt.MR.m4_sievedDoorSq_of_sup
  Salt.MR.m4_sievedDoorSq_of_sup_uniform
  Salt.MR.m4_sievedDoorSqSup_trivial

-- M4-B5 (`M4BridgeCover`) — ⟦BRIDGE #5⟧: the harmonic-weighted cover assembly, the M4 door
-- road's final composition layer.  The block weight exchange (`1/n ≍ 1/X_{i+1}` on a
-- `doorLadder` block, both directions — the ladder is dyadic within a factor 2 by its own
-- fit), the ladder sum at a FREE endpoint numerator (M4-8's `door_cover_sum_le` is its
-- `E := H` instance), the `log ω` absorption spent ONCE (`door_weight_absorb` is
-- `M4Door.door_mass_normalised_le` re-instantiated — the grade factor 3, NOT a second
-- `M`-gate rescale), and the exit `m4_cover_assembly`, which discharges
-- `M4Close.M4SievedDoorSq` from the per-block mean square `M4BlockMeanSq` with its
-- inhabitation witness.  THE JOIN is landed: `m4_door_contradiction_of_blockMeanSq` moves the
-- wave's open obligation off the covering side entirely, onto bridges 1–4
open Salt.Tactic in
#audit_axioms Salt.MR.doorLadder_pos
  Salt.MR.doorLadder_top_le_two_mul
  Salt.MR.block_weight_exchange
  Salt.MR.block_weight_exchange_tight
  Salt.MR.door_cover_weighted_le
  Salt.MR.door_weight_absorb
  Salt.MR.integral_door_cover_le
  Salt.MR.integral_door_cover_le_clean
  Salt.MR.doorSievedCoeff
  Salt.MR.norm_doorSievedCoeff_le_one
  Salt.MR.regime_window_headroom
  Salt.MR.M4BlockMeanSq
  Salt.MR.m4_cover_assembly
  Salt.MR.m4_blockMeanSq_trivial
  Salt.MR.m4_gradeGate_of_block_pricing
  Salt.MR.m4_door_contradiction_of_blockMeanSq
  Salt.MR.m4_door_False_of_blockMeanSq

-- ⟦BRIDGE 1⟧ (`M4BridgeResidue`) — THE RESIDUE-CLASS SPLIT OF THE WINDOW SUM: the window
-- partition mod `q` (`Finset.sum_fiberwise_of_maps_to` at `m ↦ m % q`, re-spelled into the
-- corpus's `Nat.ModEq` test) with its cardinality audit `∑_{r<q} #class = H`, the phase split
-- `e(αm) = e((a₀/q)m)e(θm)` and THE CONSTANCY of the rational part on each class, THE SPLIT
-- `absWindowSum a H n (a₀/q+θ) = ∑_{r<q} ratPhase·classPhaseSum` at a general coefficient
-- sequence with its unimodular-coefficient norm corollary and arc-facing form (the `(a₀,q)`
-- witnesses and the drift datum `|θ| ≤ Q/(qH)` handed to ⟦BRIDGE 2⟧), the lossless-at-trivial
-- check, and THE HOOK into `M4Close` §6: the character decomposition fires on each coprime
-- class, `1/φ(q)` cancelled by `inv_totient_sum_le`, with the `K`-uniform partial-sum family
-- Abel summation differences
open Salt.Tactic in
#audit_axioms Salt.MR.residueClassOn
  Salt.MR.windowClass
  Salt.MR.mem_residueClassOn
  Salt.MR.mem_windowClass
  Salt.MR.windowClass_subset
  Salt.MR.sum_window_residue_partition
  Salt.MR.sum_card_windowClass
  Salt.MR.ratPhase
  Salt.MR.classPhaseSum
  Salt.MR.norm_ratPhase
  Salt.MR.exp_phase_split
  Salt.MR.exp_eq_ratPhase_of_modEq
  Salt.MR.absWindowSum_residue_split
  Salt.MR.norm_absWindowSum_residue_split_le
  Salt.MR.norm_absWindowSum_residue_split_le_of_eq
  Salt.MR.norm_absWindowSum_le_class_sum_of_nearRatTight
  Salt.MR.norm_absWindowSum_split_coprime_add
  Salt.MR.norm_classPhaseSum_le_card
  Salt.MR.sum_norm_classPhaseSum_le
  Salt.MR.sum_residueClassOn_liou_eq
  Salt.MR.sum_windowClass_liou_eq
  Salt.MR.norm_sum_residueClassOn_liou_le
  Salt.MR.norm_sum_residueClassOn_liou_le_of_uniform
  Salt.MR.norm_sum_windowClass_liou_le_of_uniform
  Salt.MR.windowClass_partial
  Salt.MR.norm_sum_residueClassOn_Ioc_liou_le_of_uniform
  Salt.MR.norm_absWindowSum_le_liou_class_bound_of_nearRatTight

-- THE BRIDGE WAVE, B-4 (`M4BridgeIntegral`) — THE SUM→INTEGRAL BRIDGE: the constancy of
-- `shortSum a s₀ · H` on the unit cells `[n, n+1)` (the `Ico`-cell ↔ `Ioc`-window pairing,
-- EXACT — no `±1` inside the window), the interval-integrability of the mean-square
-- integrand (bounded + measurable, `Lemma14`'s own route at the single-`shortSum` shape),
-- the bridge identity `∑_{Ico A B} = ∫_A^B` via interval additivity, the honest endpoint
-- ledger off the ladder, and THE MEASURE EXCHANGE: `logMeasure`'s `1/n` against `thm_a2'`'s
-- `1/X` cancel exactly at the block bottom, so a door-ladder block costs `H²·MS` with NO
-- boundary loss (`doorLadder_fit` supplies the fit unconditionally); composed over the
-- cover into `M4Close.M4SievedDoorSq`'s own shape
open Salt.Tactic in
#audit_axioms Salt.MR.shortSum_filter_eq_inter_Ioc
  Salt.MR.shortSum_eq_inter_Ioc
  Salt.MR.mem_unit_cell
  Salt.MR.shortSum_const_unit
  Salt.MR.doorCoeffPhase
  Salt.MR.absWindowSum_eq_shortSum
  Salt.MR.norm_shortSum_nat_sq_le_one
  Salt.MR.shortSum_sq_intervalIntegrable
  Salt.MR.integral_unit_shortSum_sq
  Salt.MR.sum_Ico_shortSum_sq_eq_integral
  Salt.MR.integral_shortSum_sq_mono
  Salt.MR.Ioc_eq_Ico_succ
  Salt.MR.meanSq_nonneg
  Salt.MR.sum_Ioc_shortSum_sq_le_meanSq
  Salt.MR.sum_Ico_le_core_add_boundary
  Salt.MR.sum_Ioc_shortSum_sq_le_meanSq_boundary
  Salt.MR.sum_Ioc_absWindowSum_sq_div_le
  Salt.MR.sum_Ioc_absWindowSum_sq_div_le_ladder
  Salt.MR.m4_bridge_door_sq_le
  Salt.MR.mem_seamS0_of_block_window
  Salt.MR.hcov_of_seamS0
  Salt.MR.m4_bridge_door_gates_witness

-- THE BRIDGE WAVE, B-3 (`M4BridgeDilate`) — ⟦BRIDGE 3⟧: THE `d₀`-DILATION TRANSPORT INTO THE
-- DOOR WINDOW: the honest ℕ-division endpoint bookkeeping (`dilLen = H/d₀ ± 1`, both signs
-- derived, plus `dilLen ≤ H` by the `k ↦ d₀k` injection), the EXACT membership correspondence
-- (`Nat.div_lt_iff_lt_mul`/`Nat.le_div_iff_mul_le` — no `±1` in the window, only in the
-- length), the class-window transport `classWindowSum = absWindowSum (dilCoeff …) (dilLen …)
-- (n/d₀) (d₀α)` at the dilated frequency, the λ-factorisation at NO coprimality with the
-- `1_𝒮` transfer at the STRICT door gate (`memS_dilate_door`), the trivial branch as a case
-- split at `trivThresh` (pointwise and `logMeasure`-`L¹`), the dilated frequency's honest arc
-- bookkeeping (cap `Q(H+d₀)/H`, denominator dropping to `q/(d₀,q)`; `arcDen 12 (dilLen …)` is
-- BELOW that cap), the composed per-class exit with the reduced class coprime, and ⟦SEAM A⟧:
-- ⟦BRIDGE 1⟧'s `classPhaseSum` is this file's `classWindowSum` on the nose, so B-1's
-- non-coprime half discharges wholesale against the dilated window's length
open Salt.Tactic in
#audit_axioms Salt.MR.dilLen
  Salt.MR.div_add_div_le_add_div
  Salt.MR.add_div_le_div_add_div_succ
  Salt.MR.le_dilLen
  Salt.MR.dilLen_le
  Salt.MR.Ioc_dilate_eq
  Salt.MR.Ioc_dilate_maps
  Salt.MR.dilLen_le_window
  Salt.MR.dilLen_le_real
  Salt.MR.le_dilLen_real
  Salt.MR.d_mul_dilLen_le
  Salt.MR.image_div_class_window
  Salt.MR.exp_phase_dilate
  Salt.MR.classCoeff
  Salt.MR.dilCoeff
  Salt.MR.classWindowSum
  Salt.MR.norm_classCoeff_le_one
  Salt.MR.norm_dilCoeff_le_one
  Salt.MR.classWindowSum_eq_absWindowSum
  Salt.MR.classWindowSum_dilate
  Salt.MR.door_gate_blocks
  Salt.MR.dilCoeff_memS_door
  Salt.MR.absWindowSum_dilCoeff_memS_door
  Salt.MR.norm_absWindowSum_dilCoeff_memS_door
  Salt.MR.norm_absWindowSum_dilLen_le
  Salt.MR.norm_classWindowSum_le_thresh
  Salt.MR.norm_classWindowSum_le_trivThresh
  Salt.MR.integral_logMeasure_classWindowSum_le_thresh
  Salt.MR.classWindow_trivial_or_long
  Salt.MR.nearRatTight_dilate
  Salt.MR.arcDen_dilLen_le
  Salt.MR.arcDen_le_dilate_cap
  Salt.MR.nearRatTight_dilate_door
  Salt.MR.m4_class_dilate_exit
  Salt.MR.m4_class_dilate_coprime
  Salt.MR.classWindowSum_eq_classPhaseSum
  Salt.MR.classPhaseSum_dilate
  Salt.MR.norm_classPhaseSum_le_thresh
  Salt.MR.norm_absWindowSum_split_dilate_trivial

-- A2-5 SEAM (`M4Seam`) — THE `hT0band` SLOT DISCHARGED AT THE ROW: the datum-free re-cut of
-- the cap-free band supply (`hDatum` is used exactly once upstream, at an already-abstract cut
-- point, so the crude fold + plug arithmetic re-state at the PER-FREQUENCY SUP of `a` itself);
-- THE DILATION RE-INDEX, exact at both ends (`k ≤ m/P` NAT at the top, `X/P < k` REAL at the
-- bottom, `P ∤ k` ↔ `P ∣ n ∧ P² ∤ n` for multiplicity) and its two factorizations — `spolyA`
-- (what the sup wants) and `dpolyA` at `seamS0` (the slot's own integrand, the one new lemma:
-- no `dpolyA` re-index existed); the sup transfer with BOTH `m/P²` debits counted exactly;
-- and THE FINDING `m4_row_cf_block_eq_zero` — the row's window binder read at the cofactor
-- `m = 1` (where `ellLin _ 1 = 1`) forces `cf P = 0`, so the dilation's main term vanishes and
-- the seam closes on the single numeric gate `M₀ ≤ 4e·log P`.  `m4_hT0band_of_dilated_sup` is
-- the general supplier (dilated sup as a named binder); `m4_hT0band_at_row` is the row's own
-- instance — no `M4LiveAgree`, no `hDatum`, no `t₀`
open Salt.Tactic in
#audit_axioms Salt.MR.cfb_t0band_supply_of_sup
  Salt.MR.dvd_of_one_le_blockOmega_self
  Salt.MR.norm_natCast_cpow_it
  Salt.MR.norm_sum_div_cpow_le_card
  Salt.MR.card_filter_dvd_Icc
  Salt.MR.Icc_filter_pexact_image
  Salt.MR.seamS0_filter_pexact_image
  Salt.MR.injOn_mul_left
  Salt.MR.spolyA_dilate_eq
  Salt.MR.dpolyA_seamS0_dilate
  Salt.MR.norm_spolyA_dilate_le
  Salt.MR.m4_row_cf_block_eq_zero
  Salt.MR.m4_row_supp_sq
  Salt.MR.m4_hT0band_of_dilated_sup
  Salt.MR.m4_hT0band_at_row
  Salt.MR.m4_hT0band_at_row_pins

-- THE M4 WAVE'S CLOSE (`M4Join`) — `m4_wave_exit`: the end-to-end M4/S9 chain at ⟦THE
-- REGISTER⟧ (the door gates, the row grade's positivity, `2 ≤ C`, THE PRICING `6·MS ≤
-- m4Saving`, the door's own two grades, and the row input `M4RowMeanSq`) — nothing else.
-- ⟦THE WALL⟧ (§1): the §3′ repair of `hcoefPin`/`hcoefBand` is sound but does NOT dissolve
-- the capstone binder defect, because the WINDOW binder `hwinPin` forces `cf P = 0` on its
-- own at `m = 1` (`m4_row_cf_block_eq_zero` never reads `hcoefPin`); `m4_capstone_row_supp_sq`
-- draws the `P²ℕ` consequence AT THE REPAIRED (window-restricted) coefficient binder, so the
-- narrowing loses nothing and gains nothing here.  ⟦THE SUP-ROUTE COVER⟧ (§2): B-5's
-- documented ~20-line repackage, landed — `M4BlockMeanSqSup` ⟹ `M4SievedDoorSqSup` at the
-- same factor `3`, plus its anti-vacuity witness.  ⟦THE BLOCK EXCHANGE⟧ (§3): B-4's harmonic
-- currency into B-5's flat socket at the ladder's factor `2`, loss-free at the endpoints.
-- ⟦THE GRADE⟧ (§4): `3 × 2 = 6`, every constant symbolic
open Salt.Tactic in
#audit_axioms Salt.MR.m4_capstone_window_forces_cf_zero
  Salt.MR.m4_capstone_row_supp_sq
  Salt.MR.m4_cover_assembly_sup
  Salt.MR.m4_blockMeanSqSup_trivial
  Salt.MR.sum_Ioc_le_two_mul_of_harmonic
  Salt.MR.m4_blockMeanSq_of_rowMeanSq
  Salt.MR.m4_blockGrade_nonneg
  Salt.MR.m4_wave_gradeGate
  Salt.MR.m4_wave_exit
  Salt.MR.m4_wave_False
  Salt.MR.m4_wave_exit_sup

-- ⟦PART C — THE CLASS PRICING⟧ (`M4ClassPrice`) — the second of the two design questions
-- behind `M4Join`'s residue, landed at DEPTH 1 (no induction: one dilation already reaches a
-- coprime class, and the dilated frequency needs no second split).  §1 the phase removal (at
-- the rational `b/q` the phase is constant on each class, so the carriers are the BARE class
-- sums); §2 the sieved class sum IS `residueClassOn` of the sieved window, so `M4Close` §6's
-- character expansion fires with the `1/φ(q)` cancelled exactly; §3 `m4_class_price`, the
-- two-case lemma (`d₀ = 1` → the expansion; `d₀ > 1` → ONE dilation, an EQUALITY, then the
-- expansion at the provably coprime reduced pair); §4 the assembly — `q` classes squared,
-- the `q²` landing in `M4BridgePhase.M4SievedDoorSqSup`'s `q`-graded slot at THE SAME `q` as
-- the drift witness, with `M4BlockMeanSqSupQ`/`m4_cover_assembly_supQ` the `q`-graded twins
-- of `M4Join`'s pair; §5 the endpoint drop (K3(iii)) — the dilated block misses the TIGHT
-- `doorLadder_fit` by ≤ 3 units and the drop costs `3·H²/X`; §6 the two grade repairs —
-- ⟦U3⟧ `m4_gradeGate_direct` (the gate WITHOUT spending the `15 − 11/4` exponent gap; the
-- Prop socket unedited) and ⟦U1⟧ `m4_decay_summand_eq` (summand 1 priced from `cfbM0`
-- DIRECTLY, as an EQUALITY, retaining the honest `(log X)^{1/15 − 7/(30e)}` decay — never
-- through `m4_quality_summand_le`, whose `g1` is unsatisfiable); §7 ⟦U2⟧ THE ORDER PIN —
-- `M4RowMeanSqUnphased`, the re-cut row, pinned to `M4Join.M4RowMeanSq`'s body at the
-- removed phase, plus `m4_sievedDoorSq_of_classPrice`, steps 3–5 of the final compose
open Salt.Tactic in
#audit_axioms Salt.MR.absWindowSum_zero
  Salt.MR.classPhaseSum_zero
  Salt.MR.absWindowSum_classCoeff_zero
  Salt.MR.norm_absWindowSum_rat_le_class_sums
  Salt.MR.absWindowSum_classCoeff_rat
  Salt.MR.norm_absWindowSum_classCoeff_rat
  Salt.MR.sievedWindow
  Salt.MR.mem_sievedWindow
  Salt.MR.sum_windowClass_indicator
  Salt.MR.sum_windowClass_memSCoeff
  Salt.MR.norm_sum_windowClass_memS_le_of_uniform
  Salt.MR.norm_sum_windowClass_memS_dilate
  Salt.MR.m4_class_price
  Salt.MR.norm_absWindowSum_rat_le_class_count
  Salt.MR.subWindowSup_le_class_count
  Salt.MR.subWindowSup_sq_le_class_count
  Salt.MR.M4BlockMeanSqSupQ
  Salt.MR.m4_cover_assembly_supQ
  Salt.MR.m4_blockMeanSqSupQ_of_classPrice
  Salt.MR.three_mul_div_le
  Salt.MR.dilBlock_fit_slack
  Salt.MR.dilBlock_fitted
  Salt.MR.sum_Ioc_drop_top
  Salt.MR.sum_Ioc_absWindowSum_sq_div_le_dropped
  Salt.MR.m4_gradeGate_direct
  Salt.MR.m4_gradeGate_direct_of_sq
  Salt.MR.m4_decay_exponent_neg
  Salt.MR.m4DecayGrade
  Salt.MR.m4_decay_summand_eq
  Salt.MR.m4DecayGrade_factor_le_one
  Salt.MR.M4RowMeanSqUnphased
  Salt.MR.doorCoeffPhase_zero
  Salt.MR.m4_rowMeanSqUnphased_eq_phased_zero
  Salt.MR.m4_sievedDoorSq_of_classPrice

-- ⟦THE ERR REWIRE⟧ (`M4ErrRewire` + the FrameWitness/M4MeanSq re-route, W-EXECUTOR of the
-- M4 closing wave).  ⟦THE WALL⟧ was: `A2Frame3.err`'s only supplier read the JOINT-SUPPORT
-- window law `hwin`, which `M4Seam.m4_row_cf_block_eq_zero` refutes at any `P`-exact datum.
-- THE STONE (§1): `ramP2massMR_direct` — `SeamCalibrationK.ramP2mass_direct`'s sharp
-- `16·log₂(2X)/(X·P)` grade at MR's OWN domain `ramP2domMR`, where the window lives in the
-- index set (`mem_ramP2domMR_window`) and the `by_cases hmem` becomes a fibre-emptiness
-- split; the coefficient sequence is UNCONSTRAINED.  THE ROW (§2): `E_priced_mr` /
-- `E_priced_mr_row_scale` through `SeamRowWindowed.ramErr_moment_split_mr_windowed` —
-- `hwin` gone, `hcoef` relativized to `SeamCoefW`, prefactor `4` in place of `3`, both MR
-- seam windows inside `seam_rows_grade`'s `520`.  THE FIT (`err_grade_fit`):
-- `4·520 = 2080 ≤ 2160 = 3·720` on the seam half, and `4·E′ ≤ 3·E` on the `EP2` half —
-- which is `witEP2`'s `4/3` inflation, carried silently at its four sites.  THE
-- INHABITATION (§3): the door's sieved, phased `λχ̄` meets the surviving binder set at EVERY
-- cofactor including `m = 1` and `P ∣ m` (complete multiplicativity; the sieve indicator and
-- the phase absorbed into the cofactor slot at the dilated frequency `αP`)
open Salt.Tactic in
#audit_axioms Salt.MR.mem_ramP2domMR_window
  Salt.MR.ramP2domMR_fiber_card_le_omega
  Salt.MR.ramP2coeffMR_norm_div_le
  Salt.MR.ramP2coeffMR_sum_div_le
  Salt.MR.ramP2massMR_direct
  Salt.MR.E_priced_mr
  Salt.MR.E_priced_mr_row_scale
  Salt.MR.err_grade_fit
  Salt.MR.liouChi_mul
  Salt.MR.doorDatum_factorizes
  Salt.MR.doorDatum_seamCoefW
  Salt.MR.doorDatum_inhabits_err_binders
  Salt.MR.witEP2_eval
  Salt.MR.witEP2_gate
  Salt.MR.err_at_witness_mr
  Salt.MR.a2Frame3_witness
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_meansq_or_trivial

-- ⟦THE SOCKET CUT⟧ (`CapFreeArm3` §4′ + the `ThmA2Rows`/`FrameWitness`/`M4MeanSq` re-cut,
-- SOCKET-CUT executor, 2026-07-28).  ROW-GENERICITY's verdict: the cap-free row reads
-- exactly ONE structural fact about its co-factor datum, and it is confined to
-- `cofactor_Rbd34_local_nocap3` (the CASE-A/B pocket machinery, refutably false at a generic
-- `1`-bounded `b`).  THE CUT: name that fact —
--   `CofactorSocket H N Xd P Q Tann Rrad t₁ R̄ b :=
--      ∀ j ∈ I, ∀ |t| ≤ Tann, Rrad ≤ |t − t₁| → ‖ramR H N Xd P Q j b t‖ ≤ R̄`
-- — carry it, and free the datum.  `cofactor_Rbd34_local_nocap3` is UNCHANGED and becomes
-- the canonical inhabitant (`cofactorSocket_of_ellLin`); `cofactorSocket_of_pieces` is the
-- inclusion–exclusion consumer (`ramR_sum_fin`: `ramR` is linear in its co-factor slot), the
-- 4-piece door supplier's entry point.  WHAT LEFT the row's statements: `g`, `hg`,
-- `CapFreeFloor3`, `PocketSocket3`, `CaseASocket2`, the `3X` contour box,
-- `ShortIntervalDatum` and the whole `kmin`/`Ymax` ladder — replaced by the socket plus the
-- single grade `R̄ ≤ gradeCR2 C_b·(log X)^{−ρ₂₉₃}` that `balance_priced_main` consumes.  The
-- `𝒰`-leg's datum is now the SAME free `b` the `𝒯`-leg's factorization binder already
-- carried (`a(pm) = b m · c p`), which is exactly how the door's sieved datum factorizes, so
-- no row gains a parameter.  CONCLUSIONS machine-diffed byte-identical at every re-cut node
-- (`a2Rows_of_capfree3`, both capstones, the whole `hUG34`/`seam_row` chain); the only moved
-- conclusion is `A2Frame3.err` itself — the `b`-slot being freed.  `m4_meansq_per_chi_gen`'s
-- STATEMENT does not move at all: the socket is discharged inside it (`M4MeanSq` §3‴)
open Salt.Tactic in
#audit_axioms Salt.MR.CofactorSocket
  Salt.MR.CofactorSocket.mono
  Salt.MR.ramR_sum_fin
  Salt.MR.cofactorSocket_of_pieces
  Salt.MR.cofactorSocket_of_ellLin
  Salt.MR.m4_rbar_nonneg
  Salt.MR.m4_cofactorSocket_at_witness
  Salt.MR.tL_supply_discharged34_local_nocap3
  Salt.MR.hUG34_supplied_nocap3
  Salt.MR.hUG34_fully_priced_nocap3
  Salt.MR.hUG34_unconditional_nocap3
  Salt.MR.seam_row_calibratedK_nocap3
  Salt.MR.seam_row_number_nocap3
  Salt.MR.seam_row_number_capfree3
  Salt.MR.a2Rows_of_capfree3
  Salt.MR.a2Frame3_satisfiable_partial
  Salt.MR.err_at_witness
  Salt.MR.err_at_witness_mr
  Salt.MR.a2Frame3_witness
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_meansq_or_trivial

-- ⟦THE SUPPLIER⟧ (`CofactorSupplier`, 2026-07-28) — the socket's inhabitant at the DOOR's own
-- co-factor datum `1_𝒮(P·m)·λ(m)χ̄(m)`, which is not `ellLin`-shaped and so cannot use
-- `cofactorSocket_of_ellLin`.  Three moves, all additive: (1) the shifted sieve indicator
-- factorizes through `gJ`'s complete multiplicativity, splitting the datum into `2^J` signed
-- completely multiplicative pieces `λχ̄·g_𝒥` with unimodular coefficients, and `ramR`'s
-- linearity adds their sockets (`cofactorSocket_door_of_pieces`); (2) each piece's prime datum
-- is `gxDatum` at `x = 0`, so the floor transfers at FACTOR 1 and the debit is the blocks'
-- Mertens mass — which for the DOOR's calibrated ladder is the `X`-FREE `log(j²M) + 25`
-- (`blockWindow_calibrated_debit`: the §8.3 grading is NOT needed, and in fact FAILS at the
-- lower endpoint, `𝒫_j` being `X`-free); (3) the whole CASE-A/B pocket machinery re-cut at the
-- damped general datum `b·x^ω` (`cofactor_Rbd34_local_nocap3_gen`), whose CASE-A exit constant
-- `S` is FREE.  §8 then BRIDGES that socket to Route III (`hCenter_dissected` at the damped
-- datum, paying the full `cSq = 20736` — the damped datum is coprime- but never completely
-- multiplicative), and `caseA_floor_of_capFreeFloor3` supplies the floor at the DILATED scales
-- the dissection walks.  The residue is ONE page: the landed `ellLin` CASE-A supply
-- (`caseA_slice2`) re-cut from its dyadic window to the dissection's WIDE window — i.e.
-- `center_halasz_supply_wide`'s window at the `y₂` pin.  `CaseASocketGen` is stated here
-- exactly as `USetGradedPrice` states `CaseASocket2` (law #253)
open Salt.Tactic in
#audit_axioms Salt.MR.pieceDatum
  Salt.MR.doorCofactor0
  Salt.MR.pieceDatum_mul
  Salt.MR.prod_one_sub_gJ_expand
  Salt.MR.doorCofactor0_split
  Salt.MR.ramR_sum_finset
  Salt.MR.cofactorSocket_of_pieces_finset
  Salt.MR.cofactorSocket_door_of_pieces
  Salt.MR.pieceDatum_insert_prime
  Salt.MR.pretDistSq_pieceDatum_ge
  Salt.MR.capFreeFloor3_margin_all_chi
  Salt.MR.capFreeFloor3_pieceDatum
  Salt.MR.dampDatum
  Salt.MR.pretDistSq_dampDatum_eq
  Salt.MR.PocketSocket3Gen
  Salt.MR.pocketSocket3Gen_of_floor3
  Salt.MR.box_gate_le_3X_gen
  Salt.MR.CaseASocketGen
  Salt.MR.cofactorRbdGen
  Salt.MR.caseA_damped_partial_gen
  Salt.MR.damped_partial_transfer_34_gen
  Salt.MR.cofactor_Rbd34_local_nocap3_gen
  Salt.MR.cofactorSocket_of_gen
  Salt.MR.cofactorSocket_door
  Salt.MR.blockWindow_calibrated_debit
  Salt.MR.blockWindow_calibrated_debit_sum
  Salt.MR.dampDatum_isMultiplicative
  Salt.MR.ellLin_dampDatum
  Salt.MR.caseA_dissect_gen
  Salt.MR.caseASocketGen_of_inner
  Salt.MR.caseA_floor_of_capFreeFloor3

-- ⟦THE WIDE PAGE⟧ (`CaseAWide`, 2026-07-28) — the M4 wave's LAST supply flight.  `CofactorSupplier`
-- §8 leaves the supply chain ONE open page, named byte-precisely: `caseASocketGen_of_inner`'s
-- `hInner` binder, i.e. the landed `ellLin` CASE-A supply (`CaseASocket.caseA_slice2`) re-cut from
-- its DYADIC window to the WIDE window Route III's dissection walks (`⌊k/d⌋`, `d ≤ D`).  The stack
-- is `caseA_slice2`'s three layers with the bottom one swapped for
-- `SPartStation.center_halasz_supply_wide`; the two named obstacles were (1) THE SEVENTH PRIVATE
-- CLONE — `centerErrorGradeWide` and its numerals are `private` in `SPartStation`, re-derived here
-- under `_wd` (~145 ln, the house's transplant convention); and (2) THE X₀ HOIST — the wide supply's
-- `∃X₀` sits UNDER the datum, while the consumer binds the damping parameter `x` over the CONTINUUM
-- `[0,1]`, so a finite-max hoist is unavailable.  The route taken is BOUNDS-UNIFORM: the landed
-- witness `max (max (XA+1) XB) (e^8)` is built from two already-datum-hoisted sources and mentions
-- neither `g` nor `t₀`, so the body transplants byte-for-byte and only the `intro` line moves —
-- exactly `StationHoist.seam_ball_leg_station_M_hoisted` and `CaseASocket` §0.  The exit constant
-- `caseASwide` carries the wide window's TWO scales (the far arm reads the bottom, the grade page
-- the anchor) and collapses to the landed `caseAS2` on a dyadic window.  §7's two `_tb` twins
-- restrict `cofactorSocket_of_gen`/`cofactorSocket_door`'s CASE-A binder to the annulus `|t| ≤ T_ann`
-- — the only place the landed proofs read it, and the only place the `3X`-box floor discharge can
-- supply it.  `m4_supplier_complete` is the door's `CofactorSocket` with NO remaining socket
open Salt.Tactic in
#audit_axioms Salt.MR.center_halasz_supply_wideA
  Salt.MR.caseASwide
  Salt.MR.caseASwide_eq_caseAS2
  Salt.MR.caseASwide_nonneg
  Salt.MR.caseA_partial_supply_wide
  Salt.MR.caseA_slice_wide
  Salt.MR.caseA_wide_floor
  Salt.MR.caseA_inner_wide
  Salt.MR.caseASocketGen_mono
  Salt.MR.caseASocketGen_wide
  Salt.MR.caseASocketGen_discharged_door
  Salt.MR.cofactorSocket_of_gen_tb
  Salt.MR.cofactorSocket_door_tb
  Salt.MR.m4_supplier_complete

-- ⟦THE FINAL COMPOSE⟧ (`M4WaveClosed`, 2026-07-28) — the M4 wave's LAST flight:
-- `m4_wave_closed`, the M4/S9 chain end to end at ⟦THE FINAL REGISTER⟧.  The compose's one
-- substantive re-cut is §2: `M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice` assembles the
-- `q`-graded block predicate from a POINTWISE class price (a bound at every door index of
-- the block), which no mean-square supplier can deliver — at the strength the pricing needs
-- (`B H ≈ H·(log H)^{−15}`) it asserts cancellation in EVERY short interval, strictly beyond
-- the MRT method, whose output is a mean square over the block.  §2 lands the same assembly
-- at the same output grade with the input re-cut to a BLOCK MEAN SQUARE
-- (`M4ClassBlockMeanSq`): the split's `q` is paid once inside the square by Chebyshev
-- (`sq_sum_le_card_mul_sum_sq`), and the resulting `q²` lands in exactly the `q`-graded slot
-- `M4ClassPrice` §4 opened.  §3 takes the character expansion INSIDE the mean square —
-- `‖class‖ ≤ (1/φ(q))∑_χ‖twisted‖` pointwise, then square-of-average ≤ average-of-squares,
-- then the `n`-sum and the χ-average commute and `M4Close.inv_totient_sum_le` cancels the
-- `1/φ(q)` EXACTLY: loss-free, for the classes coprime to `q`.  §4 prices the capstone's
-- five raw summands with ⟦U1⟧'s decay-retaining first gate.  §5 is the close
-- (`m4_wave_closed`, `m4_wave_closed_False`, `m4_wave_closed_of_chi`).  §6 brings the χ
-- datum down to the capstone's own currency (`M4ChiRowMeanSq` → the FIXED-length block
-- bound, via B-4's ladder lemma at frequency `0` and `M4Join`'s exchange), leaving THREE
-- named residues and nothing else: ⟦R1⟧ `M4ChiMaximalStep` (the sub-window sup against the
-- fixed length — a maximal inequality, `(log H)²` by the dyadic route, absorbed by the
-- exponent gap; the trivial route's factor `H` is fatal), ⟦R2⟧ the non-coprime classes
-- (one loss-free dilation, then a `d₀`-to-one re-indexing of the block — `M4Join`'s ⟦THE
-- CLASS PRICING⟧ in mean-square form), ⟦R3⟧ `M4ChiRowMeanSq` itself, which
-- `M4MeanSq.m4_meansq_per_chi_gen` cannot yet supply: it pins its co-factor slot to
-- `ellLin (liouChi χ)` (the b-slot cut — both `a2Rows_of_capfree3` and `a2Frame3_witness`
-- are already `b`-generic, and `CaseAWide.m4_supplier_complete` is already stated at the
-- door's own `doorCofactor0`) and demands `blockOmega P P`-support of the row datum.
-- `m4_wave_closed_of_row` is the close at that currency — the S11 spine's consumption list
open Salt.Tactic in
#audit_axioms Salt.MR.classSup
  Salt.MR.le_classSup
  Salt.MR.classSup_nonneg
  Salt.MR.classSup_le
  Salt.MR.norm_sum_windowClass_le_of_norm_le_one
  Salt.MR.classSup_le_of_norm_le_one
  Salt.MR.subWindowSup_le_sum_classSup
  Salt.MR.M4ClassBlockMeanSq
  Salt.MR.m4_classBlockMeanSq_trivial
  Salt.MR.m4_blockMeanSqSupQ_of_classMeanSq
  Salt.MR.m4_sievedDoorSq_of_classMeanSq
  Salt.MR.sq_inv_totient_sum_le_sum_sq
  Salt.MR.doorSievedWindow
  Salt.MR.doorChiSup
  Salt.MR.le_doorChiSup
  Salt.MR.doorChiSup_nonneg
  Salt.MR.M4ChiBlockMeanSq
  Salt.MR.classSup_le_inv_totient_sum_doorChiSup
  Salt.MR.m4_classMeanSq_of_chiMeanSq
  Salt.MR.m4_rawMS_priced_decay
  Salt.MR.m4DecayGrade_le_debit
  Salt.MR.m4_wave_closed
  Salt.MR.m4_wave_closed_False
  Salt.MR.m4_wave_closed_of_chi
  Salt.MR.doorChiCoeff
  Salt.MR.absWindowSum_doorChiCoeff_zero
  Salt.MR.M4ChiRowMeanSq
  Salt.MR.m4_chiBlock_fixed_of_chiRow
  Salt.MR.M4ChiMaximalStep
  Salt.MR.m4_chiBlockMeanSq_of_row
  Salt.MR.m4_wave_closed_of_row
