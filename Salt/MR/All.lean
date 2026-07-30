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
import Salt.MR.RamareP2End
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
import Salt.MR.M4BridgeBlock
import Salt.MR.M4BridgeResidue
import Salt.MR.M4BridgeIntegral
import Salt.MR.M4BridgeDilate
import Salt.MR.M4Seam
import Salt.MR.M4Join
import Salt.MR.M4ClassPrice
import Salt.MR.CofactorSupplier
import Salt.MR.CaseAWide
import Salt.MR.M4WaveClosed
import Salt.MR.M4NonCoprime
import Salt.MR.M4Maximal
import Salt.MR.M4RowSupply
import Salt.MR.M4P2MR
import Salt.MR.M4RowMR
import Salt.MR.M4Band
import Salt.MR.M4Puncture
import Salt.MR.M4DoorRow
import Salt.MR.M4T0Datum
import Salt.MR.M4DoorClose
import Salt.MR.FarL2
import Salt.MR.FarL2Dyadic
import Salt.MR.A2Wall
import Salt.MR.M4T0Discharge
import Salt.MR.M4CoprimeSupply
import Salt.MR.M4Collapse
import Salt.MR.M4BaseNarrow
import Salt.MR.M4Spine
import Salt.MR.CapFreeSharp
import Salt.MR.VkMidSharp
import Salt.MR.M4ChiSummed
import Salt.MR.M4Gauss
import Salt.MR.M4SecondRoad
import Salt.MR.VkTwistRegionProbe
import Salt.MR.VkTwistStrip
import Salt.MR.VkTwistRegion
import Salt.MR.VkTwistRegionReal
import Salt.MR.MVHilbertFinset
import Salt.MR.CharFold
import Salt.MR.HybridMVT
import Salt.MR.LambdaRateTwisted
import Salt.MR.HybridLargeValues
import Salt.MR.HybridMoments
import Salt.MR.USetChi
import Salt.MR.USetChiTS
import Salt.MR.USetGChiCount
import Salt.MR.HalaszPrimesChi
import Salt.MR.TwistedEdge
import Salt.MR.MobiusChiRate
import Salt.MR.HalaszIntegersChiClose
import Salt.MR.MobiusChiRamare
import Salt.MR.LFunctionInvShallow
import Salt.MR.MobiusChiRateClose
import Salt.MR.ZetaInvShallow
import Salt.MR.PortAssembly
import Salt.MR.PortClose
import Salt.MR.PortNonVacuous
import Salt.MR.ThmA2ChiSummed
import Salt.MR.M4ChiSocketWire
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
  Salt.MR.Adoor_ge_old
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
  Salt.MR.door_dilation_gate'
  Salt.MR.door_dilation_gate_calP
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
-- `doorLadder_fit` by ≤ 3 units and the drop costs `3·H²/X`; §5b the SLACK-`4` SIBLING —
-- ⟦R2⟧'s re-indexed block reads its window at the UNIFORM length `⌊H/d₀⌋ + 1` over
-- `(⌊A/d₀⌋ − 1, ⌊B/d₀⌋]`, so the two uniform endpoints cost one unit each and the drop peels
-- `4` (`sum_Ioc_drop_top_four`, `sum_Ioc_absWindowSum_sq_div_le_dropped_four`; only the
-- endpoint constant moves `3 → 4`), with `sum_Ioc_absWindowSum_sq_div_le_slack4` THE ⟦R2⟧
-- JOIN — the block bound stated at `M4NonCoprime.M4CoprimeBlockMeanSq`'s own hypotheses
-- (`0 < A`, `B + H ≤ 2A + 4`, scale pinned at the block bottom) with BOTH endpoint regimes
-- discharged inside, the short block `B < A + 4` being covered by the drop's own `4·H²/A`;
-- §6 the two grade repairs —
-- ⟦U3⟧ `m4_gradeGate_direct` (the gate WITHOUT spending the `15 − 11/4` exponent gap; the
-- Prop socket unedited) and ⟦U1⟧ `m4_decay_summand_eq` (summand 1 priced from `cfbM0`
-- DIRECTLY, as an EQUALITY, retaining the honest `(log X)^{1/45 − 7/(30e)}` decay — never
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
  Salt.MR.slack4_fitted
  Salt.MR.sum_Ioc_drop_top_four
  Salt.MR.sum_Ioc_absWindowSum_sq_div_le_dropped_four
  Salt.MR.sum_Ioc_absWindowSum_sq_div_le_slack4
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

-- ⟦R2 — THE NON-COPRIME CLASSES⟧ (`M4NonCoprime`, 2026-07-28) — the second of the final
-- register's three residues, closed.  `M4WaveClosed` §3 reduces `M4ClassBlockMeanSq` only at
-- the classes COPRIME to `q` (the character expansion needs `(r,q) = 1`); this file closes
-- the other half and hands back the FULL predicate.  The transport is `M4ClassPrice` §3's
-- dilation EQUALITY at the residual frequency `0`, taken pointwise in the door index and
-- then applied to the BLOCK by the same map `n ↦ ⌊n/d₀⌋` — which is `d₀`-to-one, its fibre
-- being exactly `[d₀n', d₀n' + d₀)` (`card_fibre_div_le`, from `Nat.div_add_mod`; no ± slack
-- is guessed).  The image of the half-open block is a CLOSED interval (the bottom index IS
-- hit), so the re-indexed block is `(⌊A/d₀⌋ − 1, ⌊B/d₀⌋]` and it is not a `doorLadder`
-- block — `M4Join`'s ⟦THE CLASS PRICING⟧ obstruction in its surviving, mean-square form.
-- The interface `M4CoprimeBlockMeanSq` is therefore interval-general AND length-general,
-- with the fit at `M4ClassPrice` §5's endpoint slack (`4`: §5's own `3`, plus one unit for
-- the uniform endpoints `⌊H/d₀⌋ + 1` and `⌊A/d₀⌋ − 1`; `dilBlock_reindex_fit`), which is
-- what `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` + `sum_Ioc_drop_top` supply.
-- ⟦THE d₀-LEDGER⟧ (`d0_ledger`): the fibre factor `d₀` is paid EXACTLY by the dilated
-- block's bottom (`d₀·(⌊A/d₀⌋ − 1) ≤ d₀·⌊A/d₀⌋ ≤ A`), and the window shrink `H ↦ ⌊H/d₀⌋+1`
-- is BANKED UNSPENT — sharply `d₀·(B·H'²·A') ≤ B·H²·A·(1 + d₀/H)²/d₀²` (`d0_ledger_sharp`),
-- a factor `≥ 16/9` of headroom already at `d₀ = 2`.  So the composed grade is IDENTICAL to
-- the coprime half's and the `q²` slot `M4ClassPrice` §4 opened is untouched.  TWO gates
-- added: the dilation's own, `M`-RELATIVE since the register-scope wave
-- (`arcDen 12 H < calP (Adoor M) (3072M) 1 = 2^{Adoor M}`, `M4Residue.door_dilation_gate'`,
-- paid by every consumer of the dilation), and `2·arcDen 12 H ≤ H`, an `H`-only class-(a)
-- threshold (which makes the re-index non-degenerate:
-- `2d₀ ≤ 2q ≤ H < A`, hence `⌊A/d₀⌋ ≥ 2` — and which `MinorArcExit` already DERIVES from
-- the mere existence of a large Dirichlet denominator).  Anti-vacuity:
-- `m4_coprimeBlockMeanSq_trivial` at grade `5`.
open Salt.Tactic in
#audit_axioms Salt.MR.card_fibre_div_le
  Salt.MR.sum_Ioc_comp_div_le
  Salt.MR.two_mul_div_le
  Salt.MR.div_mem_reindexed
  Salt.MR.dilBlock_reindex_fit
  Salt.MR.d0_ledger
  Salt.MR.d0_ledger_sharp
  Salt.MR.classSup_mono_len
  Salt.MR.classSup_le_dilate
  Salt.MR.M4CoprimeBlockMeanSq
  Salt.MR.m4_coprimeBlockMeanSq_trivial
  Salt.MR.m4_nonCoprime_classMeanSq

-- ⟦R1 — THE MAXIMAL STEP⟧ (`M4Maximal`, 2026-07-28; ⟦LEVER 1′⟧ re-cut 2026-07-29) — the
-- first of the final register's three residues, executed by THE DYADIC (Rademacher–Menshov)
-- ROUTE at the price `m4Cmax = 54/5 = 10.8` — a CONSTANT, not the `3(log₂H+1)` the uniform
-- Chebyshev charged, not the `(log H)²` the budget allowed, and never the fatal `H + 1` of
-- `sup² ≤ ∑_{K≤H}`.  ⟦THE STATEMENT FINDING⟧: `M4WaveClosed`'s
-- `M4ChiMaximalStep` — the sup priced against the SAME block's fixed-length-`H` sums — is
-- not the shape that can be proved and is false for general data (an alternating datum has
-- `S(n,H) = 0` at even `H` while `S(n,1) = ±1`: the right side vanishes, the left is the
-- block length).  It is the ⟦F1⟧ genre again, and per iron rule 1 the statement is left
-- standing; this file lands the provable route beside it.  The dyadic pieces of `(n, n+K]`
-- sit at SHIFTED bases `n + P_j K` with `P_j K = 2^{j+1}⌊K/2^{j+1}⌋` a multiple of
-- `2^{j+1}` — the ALIGNMENT is the content: at scale `j` only `⌊H/2^{j+1}⌋+1` offsets can
-- occur, so summing over offsets (never maximising) costs `∑_j (⌊H/2^{j+1}⌋+1)(2^j)² ≤ 3H²`
-- (`dyadic_count_weight_le`, two geometric series against `2^{log₂H} ≤ H`).  ⟦LEVER 1′⟧ (the
-- second-road freeze v2, wave ②) replaces the uniform Chebyshev over the `≤ log₂H+1` pieces
-- — which contributed the single log — by GEOMETRIC-WEIGHT Cauchy–Schwarz at `c = 3/2`,
-- packaged in the sqrt-free ENGEL/Sedrakyan form `Finset.sq_sum_div_le_sum_sq_div`.  The
-- weight sum `∑_{j≤L}(3/2)^j = 3(3/2)^L − 2` and the `(2/3)^j`-weighted count multiply to
-- `6H·2^L + (24/5)·4^L ≤ (54/5)H²` (`dyadic_count_weight_geom_le`) — the two mixed products
-- `(3/2)^L(4/3)^L = 2^L` and `(3/2)^L(8/3)^L = 4^L` are exact, which is why every ratio is
-- rational and every geometric series closes under `norm_num`.  `c = 3/2` is ~1% off the
-- true optimum (25/16 gives 10.9076) and materially easier bookkeeping.  The lever is FREE
-- on the supply side: no datum, no gate, no new hypothesis at the door — the weights live
-- entirely inside the maximal step's own Cauchy–Schwarz.  The input is therefore the row
-- mean square at the DYADIC lengths `2^j ≤ H` and the SHIFTED scales `X_{i+1}+s`, `s ≤ H`
-- (`M4ChiDyadicRowMeanSq`) — the capstone's own currency with both pins (`X_d = X`,
-- `N = 2X_d`) intact at every instance.  ⟦THE OVERHANG, HONESTLY⟧: the shift is EXACT
-- (`Finset.map_add_right_Ioc` — no cell created, none discarded), and the bridge's two fits
-- at `X := A+s` read `le_rfl` and `(B+s)+2^j ≤ 2(A+s)`, which is `M4Door.doorLadder_fit`'s
-- `B + H ≤ 2A` with `2^j ≤ H`: the shift appears on both sides and pays for itself, and the
-- harmonic→flat exchange keeps the ladder's own factor `2` because `B + s ≤ B + H ≤ 2A`.
-- ⟦THE LENGTH-GRADED RE-CUT⟧ (WALL 2's repair, in place): the row grade is
-- `MS : ℕ → ℕ → ℝ`, read `MS j H` — the grade at dyadic length `2^j` — because the door's
-- capstone cannot be STATED below `j = M·Adoor M` (`M4DoorRow.door_length_gate_iff`) and at
-- `j = 0` the row quantity IS the block density, `≍ 1`.  The assembly absorbs the grading at
-- a NAMED floor `j₀` (never `2^18` inlined — the `M`-dependence is the point): the weighted
-- full count `(54/5)H²` charges the analytic envelope `MSan` on `j₀ ≤ j`, while the weighted
-- small head `(9/2)H(3/2)^{log₂H}(4/3)^{j₀} + (9/5)(3/2)^{log₂H}(8/3)^{j₀}`
-- (`dyadic_count_weight_geom_small_le` — TWO summands, because the term bound's `H·2^{j-1}`
-- half is top-heavy at ratio `2/(3/2) = 4/3` and its `4^j` half at `4/(3/2) = 8/3`) charges
-- the trivial envelope `MStr` on `j < j₀`.  Composed grade
-- `Bcl H = m4BclGraded j₀ (2·MSan) (2·MStr) H
--        = (108/5)·MSan H
--          + (9·(3/2)^{log₂H}(4/3)^{j₀}/H + (18/5)(3/2)^{log₂H}(8/3)^{j₀}/H²)·MStr H`
-- — the second summand's two pieces are `≍ H^{-0.415}` and `≍ H^{-1.415}` (since
-- `(3/2)^{log₂H} = H^{0.58496}`), so at fixed `M` the small lengths decay.  ⟦THE FLOOR, HALVED⟧
-- `log₂(4/3) = 0.41504` and `log₂(8/3) = 1.41504` are EXACTLY the two `H`-exponents, so both
-- pieces impose the same demand `H ≳ 2^{j₀}` where the uniform route demanded `4^{j₀}`: the
-- window floor's exponent halves, and `U1floor` with it.  THE THRESHOLD, symbolic
-- (`m4SmallGradeFits`, `m4SmallGradeFits_of_threshold`): the weighted head against `D` under
-- `H²·MSan H` for any envelope `MStr H ≤ D`, under which the split costs at most a factor 2
-- (`m4BclGraded_le_of_fits`, STATEMENT unmoved).  ⟦A1, THE SHAPE RULE⟧ `m4BclGraded` and
-- `m4Cmax` keep their names and signatures and are re-cut IN PLACE — that alone keeps every
-- register restatement site byte-identical, because they consume only `m4BclGraded_nonneg`.
-- ⟦A2, THE PRICE AT THE NARROW BASE⟧ the free-base copies transfer the head from the free
-- length `L` to `H` through `H ≤ arcDen·L`, and the `(8/3)^{j₀}` piece is normalised by `H²`
-- — so ⟦G1⟧ must strengthen from `arcDen 12 H ≤ MStr H` to `arcDen 12 H ^ 2 ≤ MStr H` (the
-- honest exponent is `log₂(8/3) = 1.415`, rounded up to the integer square), and ⟦G2⟧ from
-- `12·MSan H + 24 ≤ 4^{j₀}` to `44·MSan H + 87 ≤ (4/3)^{j₀}`.  MStr is WITNESSED data, so
-- both are free to supply; they move at six register sites and nowhere else.
-- The close is `m4_wave_closed_of_dyadicRow`,
-- `m4_wave_closed_of_chi`'s analytic slot filled with ⟦R1⟧ discharged and only ⟦R2⟧/⟦R3⟧
-- outstanding; its conclusion `¬ logChowla2Fails` is unmoved by the re-cut, and only the
-- register's grade items move (two envelopes + two envelope gates + the bound floor `j₀`;
-- the drift and non-coprime lines read `m4BclGraded`).  Anti-vacuity:
-- `m4_chiShiftBlock_trivial` at grade `1`, now at EVERY length.
open Salt.Tactic in
#audit_axioms Salt.MR.sum_sievedWindow_add
  Salt.MR.dyadic_prefix_shift
  Salt.MR.norm_sum_sievedWindow_le_dyadic
  Salt.MR.norm_sum_sievedWindow_sq_le_dyadic
  Salt.MR.doorChiSup_sq_le_dyadic
  Salt.MR.sum_Ioc_shift
  Salt.MR.dyadic_count_weight_term_le
  Salt.MR.dyadic_count_weight_term_nonneg
  Salt.MR.dyadic_count_weight_le
  Salt.MR.dyadic_count_weight_small_le
  Salt.MR.geom_weight_sum
  Salt.MR.geom_weight_sum_pos
  Salt.MR.geom_weight_sum_le
  Salt.MR.inv_geom_weight
  Salt.MR.geom_term_eq
  Salt.MR.dyadic_count_weight_geom_le
  Salt.MR.dyadic_count_weight_geom_small_le
  Salt.MR.m4Cmax
  Salt.MR.m4Cmax_nonneg
  Salt.MR.m4BclGraded
  Salt.MR.m4BclGraded_nonneg
  Salt.MR.m4SmallGradeFits
  Salt.MR.m4SmallGradeFits_of_threshold
  Salt.MR.m4BclGraded_le_of_fits
  Salt.MR.M4ChiShiftBlockMeanSq
  Salt.MR.m4_chiShiftBlock_trivial
  Salt.MR.m4_chiBlockMeanSq_of_shiftBlock
  Salt.MR.M4ChiDyadicRowMeanSq
  Salt.MR.m4_chiShiftBlock_of_dyadicRow
  Salt.MR.m4_chiBlockMeanSq_of_dyadicRow
  Salt.MR.m4_wave_closed_of_dyadicRow

-- ⟦THE R3 WAVE⟧ (`M4RowSupply` + the in-place repairs, 2026-07-28) — R3d's level-indexed
-- band coefficient `bfam` through the capfree3 chain; R3c's ε-graded `EP₂` budget
-- (`12·EP₂ ≤ (log X)^{−θ₂₉₃+ε}`, `rem_priced`); W1's carried `b`-slot (the capstone reads
-- NO `liouChi` at all now — the socket, its grade and the datum all ride the statement);
-- R3a's PRICED coprime tail (`ramCopTail_moment` in place of `_moment_zero`; `homega` gone
-- from the capstones, `M_tail` in its place); R3b's relaxed regularity gate
-- (`100·log Q ≤ log W` in place of `log Q ≤ √log W ∧ 100 ≤ √log W` — a strict weakening,
-- bridged by `densGate_of_sqrt`).  `M4RowSupply` is the row-side supply and records the
-- POINT-vs-BAND wall that R3's tail pricing leaves open.
open Salt.Tactic in
#audit_axioms Salt.MR.densGate_of_sqrt
  Salt.MR.densSieve_tail_le
  Salt.MR.typical_density_le
  Salt.MR.blockfree_sum_le
  Salt.MR.rem_priced
  Salt.MR.E_priced_mr
  Salt.MR.err_at_witness_mr
  Salt.MR.a2Frame3_witness
  Salt.MR.TLeg_bound
  Salt.MR.TLeg_feeds_capstone
  Salt.MR.sum_lemma12Rows_priced_calibratedK2
  Salt.MR.seam_row_number_capfree3
  Salt.MR.a2Rows_of_capfree3
  Salt.MR.thm_a2'
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_meansq_or_trivial
  Salt.MR.m4_tail_gate_at_pins
  Salt.MR.m4_tail_mass_at_band
  Salt.MR.m4_tail_mass_nonneg
  Salt.MR.m4_tail_grade_at_pins


-- ⟦THE BAND RE-CUT⟧ (`FrameWitness` §2′/§3′ + `M4MeanSq` §4 + `M4Band` + `M4RowSupply` §4 +
-- the `CofactorSupplier`/`CaseAWide` shift decoupling; BAND-WAVE executor, 2026-07-28).  THE
-- WALL (flags `1bab8e3`): the capstone's Ramaré block was a POINT `ramI (H83 X θ₂₉₃) P P` —
-- TLGATES-SCOPE's "easiest witness; a genuine band also works" — and the door datum calls it,
-- because at a point the block-free mass is ≍ 1/X_d and the coprime tail's charge
-- (2X+20N)·M_tail is O(1), which no ε-window absorbs.  THE REPAIR, mathematically forced:
-- re-cut the witness chain at the BAND [P, Q] with **Q PINNED at ⌊Q₈₃ X⌋₊** — the unique
-- corner where C4's h-ceiling charge is the minimal 30·log X/loglog X (vanishing on the
-- loglog scale) while the tail grade log P/log Q is the minimal loglog X·(log X)^{−θ₂₉₃}.
-- WHAT MOVED: (1) the singleton collapse `ramQbase_at_pin` → the SANDWICH
-- `P ≤ ramQbase H P j ≤ Q` (`ramQbase_ge_bot`/`ramQbase_le_top`), which routes each
-- `TLBlockGates34` conjunct to its endpoint — C2/C6 UP from P (C6 monotone in the base, at
-- `0 ≤ cq`), C3/C4/C5 DOWN from Q; (2) the h-ceiling to its band form
-- `log h + 30(log X/loglog X) ≤ log X`; (3) the twelve `ramI … P P` slots of the frame,
-- the row ladder, the socket and the err supply to `ramI … P Q` — every one of which was
-- already (P,Q)-general downstream, so NO conclusion moved anywhere in the chain; (4) the
-- sieve SHIFT inside `doorCofactor0` decoupled from the band bottom (fresh `Ps`, the band
-- reads it at `Ps := 1` via `doorCofactor0_at_one`).  WHAT THE BAND BUYS: `M4Band`'s pair
-- law — the UPWARD mirror of `M4Residue`'s dilation — gives `SeamCoefW X_d P Q` at the
-- door's un-phased sieved datum with NO coprimality and NO m = 1 exception (a single band
-- prime meets no door block, so both sides vanish), its gate being the K-calibration's own
-- `𝒬K_j < P₈₃ X θ₂₉₃ ≤ P`; and `M4RowSupply` §4 closes the Perron budget
-- `12·EP₂ ≤ (log X)^{−θ₂₉₃+ε}` at P = ⌈P₈₃⌉₊, Q = ⌊Q₈₃⌋₊ under THE ONE NEW NAMED THRESHOLD
-- `2688·C·loglog X ≤ (log X)^ε`.  ⚠ THE ROUNDING FINDING: the EXACT grade log P₈₃/log Q₈₃ is
-- unattainable at any admissible ℕ-band (P ≥ P₈₃ and Q ≤ Q₈₃ move the ratio only UP), so the
-- brief's 1344 becomes 2688 — `m4_tail_grade_rounded` prices the two roundings at one factor
-- of e each.  ⚠ THE UN-PHASED PIN: `M4ErrRewire`'s doorDatum/doorCofactor are genuinely
-- point-only (e(αpm) does not factor at varying p) and are NOT generalized
open Salt.Tactic in
#audit_axioms Salt.MR.ramQbase_ge_bot
  Salt.MR.ramQbase_le_top
  Salt.MR.ramI_index_ge
  Salt.MR.log_le_of_le_Q83
  Salt.MR.h_ceiling_gate_band
  Salt.MR.c4_at_height_band
  Salt.MR.tlBlockGates34_at_witness
  Salt.MR.blocks_at_witness
  Salt.MR.thin_at_witness
  Salt.MR.Tstar2_box_at_witness
  Salt.MR.err_at_witness_mr
  Salt.MR.a2Frame3_witness
  Salt.MR.row_ladder_at_witness
  Salt.MR.doorCofactor0_at_one
  Salt.MR.cofactorSocket_door_of_pieces
  Salt.MR.cofactorSocket_door_tb
  Salt.MR.m4_supplier_complete
  Salt.MR.m4_cofactorSocket_at_witness
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_meansq_or_trivial
  Salt.MR.blockPrimeDivs_eq_empty_of_large
  Salt.MR.blockOmega_shift_up
  Salt.MR.memS_shift_up
  Salt.MR.indicator_mul_shift_up
  Salt.MR.memSCoeff_seamCoefW_band
  Salt.MR.doorChiCoeff_seamCoefW_band
  Salt.MR.door_band_gate
  Salt.MR.door_band_gate_of_log
  Salt.MR.m4_tail_grade_rounded
  Salt.MR.m4_ep2_budget_at_band
  Salt.MR.m4_tail_supply_at_band

-- ⟦W2-DOOR⟧ (`M4DoorRow`, 2026-07-28).  The night sequence's step 2 — the band-re-cut
-- capstone `m4_meansq_per_chi_gen` instantiated at `M4Maximal.M4ChiDyadicRowMeanSq`'s
-- per-(χ, block, shift, dyadic length) family — does NOT close, and the two obstructions are
-- structural.  WHAT LANDS: the half-open window cut `winCutH` forced by the capstone's own
-- support pins (`hsupp0` at `(n:ℝ) ≤ X_d` vs `hasupp` on `[X_d, 2X_d]` straddle the block
-- bottom; `winCut_endpoint` shows the CLOSED cut of `SeamRowWindowed` cannot meet `hsupp0`),
-- with both cuts invisible to the row's own short sum (`seamS0` filters `X_d < m` strictly);
-- the three S8 slots `ha1`/`hsupp0`/`hasupp` at the door datum; the co-factor socket at
-- `Ps := 1` (`cofactorSocket_doorChiCoeff`, `m4_supplier_complete`'s conclusion re-read at
-- `doorChiCoeff` through `doorCofactor0_at_one`); the Ramaré-band pair law with its gate
-- discharged from the capstone's own `hQXd`/`hPlow` (`doorChiCoeff_seamCoefW_at_door`); and
-- the coprime-tail triple at the door's cut datum inside the K6 existential
-- (`m4_door_tail_supply`).  ⚠ WALL 1 — THE K-BLOCK WINDOW LAW: `band_window_ratio_lock`
-- proves that the capstone's `hcoefBand`/`hwinBand` pair (inherited verbatim from
-- `ThmA2Rows.a2Rows_of_capfree3`'s `hcoef`/`hwin`, ThmA2Rows:914–918) locks any two block
-- primes at which the datum is LIVE into a factor 2 of each other, while
-- `door_block_one_wide` shows the door's level-1 K-block spans `2^{(M−1)·Adoor M}` (a factor
-- 4 already at M ≥ 2) and the sieve `𝒮` puts live points at block primes throughout it.  This
-- is `M4Join` §1's ⟦THE WALL⟧ alive on the K-BLOCK chain: the closing wave deleted `hwinPin`
-- from the Ramaré-band pin chain but left `hwinBand` standing.  ✔ WALL 2 — THE UNIFORM-IN-j
-- GRADE, **REPAIRED** (WALL2-REGRADE, same day): `door_length_gate` solves the capstone's
-- window gate `𝒬K_1 ≤ h` at `h = 2^j` into `M·Adoor M ≤ j` — and `door_length_gate_iff`
-- shows the converse, so `doorRowFloor M = M·Adoor M` is EXACTLY the capstone's statement
-- boundary, not a chosen cut.  Every `j < 2^18` is outside it
-- (`door_length_gate_fails_of_small`), and at `j = 0` the row quantity IS the block density
-- of live sieved residues (≍ 1/loglog H), against a consumer budget of `(log H)^{−30}`.  The
-- dyadic assembly never needed uniformity, and `M4Maximal` now says so: the row grade is
-- length-graded (`MS j H`) and the split assembly charges the trivial envelope only on
-- `j < j₀`, where the weighted count is `2H·4^{j₀}` — LINEAR in `H`.  `door_smallGrade_fits`
-- states the door's threshold in bytes: `2·4^{M·Adoor M}·D ≤ H·MSan H` for any density
-- envelope `D`, one inequality in `H` at fixed `M`.  WALL 1 remains a statement change
-- upstream of this file
open Salt.Tactic in
#audit_axioms Salt.MR.winCutH
  Salt.MR.winCutH_supp0
  Salt.MR.winCut_endpoint
  Salt.MR.shortSum_winCutH_seamS0
  Salt.MR.shortSum_winCut_seamS0
  Salt.MR.doorRow_ha1
  Salt.MR.doorRow_hsupp0
  Salt.MR.doorRow_hasupp
  Salt.MR.doorCofactor0_door_eq
  Salt.MR.cofactorSocket_doorChiCoeff
  Salt.MR.doorChiCoeff_seamCoefW_at_door
  Salt.MR.m4_door_tail_supply
  Salt.MR.band_window_ratio_lock
  Salt.MR.door_block_one_wide
  Salt.MR.door_length_gate
  Salt.MR.door_length_gate_fails_of_small
  Salt.MR.doorRowFloor
  Salt.MR.door_length_gate_iff
  Salt.MR.door_smallGrade_fits

-- ⟦THE ENDPOINT STRADDLE⟧ (`M4Band` §4, ENDPOINT executor, 2026-07-28).  `M4DoorRow` §1's
-- SMALL finding closed on the DATUM side.  THE CLASH: the capstone's two support pins meet at
-- the block bottom — `hsupp0` demands `a n = 0` for `(n:ℝ) ≤ X = X_d` while `hasupp` allows
-- support on `[X_d, 2X_d]` — so the door datum must be cut HALF-OPEN (`winCutH`), while
-- `M4Band` §2's pair law is stated at the CLOSED `winCut`, whose `SeamCoefW` antecedent
-- `X_d ≤ p·m` INCLUDES the endpoint (`winCut_endpoint`).  THE ROUTE TAKEN (the task's (ii),
-- made conditional and TIGHT — (i) is unavailable to an executor because `SeamCoefW` is the
-- capstone's own binder in `M4MeanSq`, and (iii) is refuted: `seamS0`'s strict filter governs
-- the CONCLUSION, not the `hcoefPin` binder, which quantifies over every admissible `(p, m)`).
-- `memSCoeff_seamCoefW_band_gen` re-cuts §2's law at an ABSTRACT cut — agreement with the
-- sieved datum on the CLOSED window is all the proof ever used — and
-- `memSCoeff_seamCoefW_band_H` reads it at a HALF-OPEN cut (agreement strictly above `X_d`,
-- vanishing AT `X_d`) under ONE new binder `hend : 1_𝒮·λχ̄ (X_d) = 0`, with the door forms
-- `doorChiCoeff_seamCoefW_band_H` and `doorChiCoeff_seamCoefW_at_door_H` (gate discharged from
-- the capstone's own `hQXd`/`hPlow`, the half-open sibling of `doorChiCoeff_seamCoefW_at_door`).
-- ⚠ THE BINDER IS FORCED, NOT A CONVENIENCE: `seamCoefW_endpoint_forced` shows any cut with
-- `a X_d = 0` satisfying the CLOSED antecedent must kill the pair's right-hand side at every
-- band factorization of `X_d`, and `memSCoeff_endpoint_zero_of_seamCoefW` turns that (through
-- §1's shift-up identity, `b m·cf p = 1_𝒮·λχ̄(p·m) = 1_𝒮·λχ̄(X_d)`) into the CONVERSE of
-- `hend` whenever `X_d = p·m` at a band prime.  So the endpoint is a genuine arithmetic cost
-- at the door's own `X_d = doorLadder R.x H (i+1) + s` (no power-of-2 escape), payable by
-- `memSCoeff_eq_zero_of_not_memS` (`X_d ∉ 𝒮`) or by choosing a band whose primes miss `X_d`.
-- ⚠ THE CUT IS LEFT ABSTRACT because `winCutH` is defined DOWNSTREAM in `M4DoorRow`; the
-- instance is that file's one-liner
-- `… _ hgate (fun n h₁ h₂ => winCutH_of_mem _ h₁ h₂) (winCutH_supp0 _ le_rfl) hend`
-- (kernel-checked in scratch against `M4DoorRow`, both the band and the at-door forms)
open Salt.Tactic in
#audit_axioms Salt.MR.memSCoeff_seamCoefW_band_gen
  Salt.MR.memSCoeff_seamCoefW_band_H
  Salt.MR.doorChiCoeff_seamCoefW_band_H
  Salt.MR.doorChiCoeff_seamCoefW_at_door_H
  Salt.MR.memSCoeff_eq_zero_of_not_memS
  Salt.MR.seamCoefW_endpoint_forced
  Salt.MR.memSCoeff_endpoint_zero_of_seamCoefW

-- ⟦T0BAND-DATUM⟧ (`M4T0Datum`, 2026-07-28).  THE `hT0band` SLOT AT THE DOOR'S SIEVED
-- χ-TWISTED UN-PHASED DATUM — the last analytic item `M4DoorRow`'s ⟦THE `T₀`-BAND, NAMED⟧
-- recorded as open, closed on the SUPPLIER GENRE's third performance (after `CofactorSupplier`
-- the socket and `CaseAWide` the wide centre), at the SAME four-piece split.  THE CUT COMMUTES
-- WITH THE SPLIT (`winCutH_sum_finset`): `winCutH` is multiplication by a `0/1` indicator, so
-- `doorCofactor0_split` at the shift `Ps := 1` rides through the half-open cut with the same
-- unimodular coefficients and the pieces cut by the same window (`winCutH_doorChiCoeff_split`,
-- `door_powerset_card` = 4).  `spolyA` is LINEAR in its coefficient slot (`spolyA_sum_finset`,
-- the twin of `ramR_sum_finset`), so the door's polynomial sup is the pieces' at `4×`
-- (`norm_spolyA_of_pieces`).  THE HALF-OPEN COST IS ZERO ON THE LIVE RANGE: `cfb_sup_of_center`
-- asks agreement on all of `n > X`, the cut gives it only on `(X_d, 2X_d]`, and `m ≤ N ≤ 2X_d`
-- supplies the difference from the WINDOW PIN instead of a datum hypothesis
-- (`spolyA_winCutH_split`, `cfb_sup_of_center_cut`, factor `2`).  PER PIECE: Route III
-- (`hCenter_dissected`, `cSq = 20736`) at the UNDAMPED piece directly — `pieceDatum` is
-- completely multiplicative (`pieceDatum_isMultiplicative`) and `1`-bounded, and
-- `caseA_dissect_gen` is NOT specialisable at `x = 1` because its consumer binds `x` over
-- `[0,1]` and carries a `cofactorMfl` floor the band has not (`piece_center_of_inner`); the
-- inner sums ride `center_halasz_supply_wideA`, whose ⟦HOIST⟧ gives ONE threshold for all four
-- pieces at every band frequency, with the dilated window entered by
-- `seam_ball_leg_station_M_gen`'s own gate `D·(X_w+1) ≤ X−1` (`piece_center_of_wide`).
-- EXITS: `m4_t0datum_sup` (the `hsup` binder at the grade `8·S₀ = 4` pieces × the cut's `2`),
-- `m4_hT0band_at_door` (the slot, `cfb_t0band_supply_of_sup` composed) and
-- `m4_hT0band_at_door_of_wide` (the same from the wide supply's own binders — the kernel
-- witness that §5's `X−1 < k` window and §7's `X_d ≤ k` window are the same window under
-- `(X_d : ℝ) = X`).  ⟦THE U1 PRICING HOOK⟧ `cfbM0_add_debit`: the mask debit does not change
-- the SHAPE of `M₀` (`cfbM0 K q X − D = cfbM0 (K+D) q X`), so `band_floor_M0_pieceDatum` (band
-- strength `7/30`, NOT the box's `1/16`, less the mask at FACTOR 1) is still `cfbM0`-shaped and
-- `m4_rawMS_priced_decay`'s route stays reachable; at the door's own ladder the debit is
-- `X`-FREE and equals `2·(log(4M)+25)` (`band_floor_M0_doorPiece`, `two_le_calE_door`).
-- CARRIED SYMBOLIC, all of it: the grade gate `hSle`/`hgrade`, `hErr`, the four `Y`-gates, the
-- piece `hRHS`, the dissection gates and the floor threshold.  No numeral is chosen here.
-- ⚠ ⟦THE PRICING RESIDUE, NAMED⟧ (module header): §5's `hRHS` is carried at a FREE `B`, and the
-- corpus's landed pricer `dilated_scale_grade` — datum-generic, so it DOES apply at the piece —
-- asks its floor on `|v| ≤ Rad ≥ |t₁| + Tstar(k, log k)`, and `Tstar k L = L⁴·k^{1/(4 log L)}` at
-- `k ≍ X` is `X^{o(1)}`, incomparably wider than the band's `|v| ≤ 2·seamT0 X + 1`.  So the two
-- floors available at the piece sit on DIFFERENT ranges: band strength `7/30` on the band
-- (§8), box strength `1/32` on `|v| ≤ 3X` (`capFreeFloor3_pieceDatum`, the range that covers
-- `Tstar`).  The dissection is FORCED (the door datum is completely multiplicative, NOT
-- squarefree-linearised), so a consumer pricing through `dilated_scale_grade` gets `M₀` at BOX
-- strength — and `T0BandCapFree`'s own header records `1/32` as `6×` short of the exit's decay
-- gate `(103/1500)e`, i.e. the `(log X)^{1/30}` inside `cfbC₁` is not paid back.  Two escapes,
-- both design-tier and both outside this file: a band-radius pricing page on the wide scale
-- window, or a crude-fold re-cut.  `B` is left FREE so either plugs in unchanged
open Salt.Tactic in
#audit_axioms Salt.MR.winCutH_sum_finset
  Salt.MR.winCutH_doorChiCoeff_split
  Salt.MR.door_powerset_card
  Salt.MR.spolyA_sum_finset
  Salt.MR.norm_spolyA_of_pieces
  Salt.MR.spolyA_winCutH_split
  Salt.MR.cfb_sup_of_center_cut
  Salt.MR.pieceDatum_isMultiplicative
  Salt.MR.piece_center_of_inner
  Salt.MR.piece_center_of_wide
  Salt.MR.m4_t0datum_sup
  Salt.MR.m4_hT0band_at_door
  Salt.MR.m4_hT0band_at_door_of_wide
  Salt.MR.cfbM0_add_debit
  Salt.MR.band_floor_M0_pieceDatum
  Salt.MR.two_le_calE_door
  Salt.MR.band_floor_M0_doorPiece

-- ⟦WALL 1 — hwinBand DELETED⟧ (`M4P2MR` + `M4RowMR` + `M4Puncture` + the row wave; WALL1
-- executor, 2026-07-28).  `M4DoorRow` §6's kernel witness (`band_window_ratio_lock` +
-- `door_block_one_wide`) said the capstone's `hwinBand` locks any two LIVE block primes into
-- a factor 2 while the door's level-1 K-block spans `2^{(M−1)·2^18}` — so the binder was
-- UNINHABITABLE at the door datum.  THE REPAIR, by the `hwinPin` playbook (`M4MeanSq` §3″):
-- delete the window law and pay for the rows through MR's own cofactor range, where the
-- window lives in the INDEX SET (`RamareMR.ramHonMR`).  WHAT MOVED: (1) `M4ErrRewire` §1 —
-- the `p²` stone `ramP2massMR_direct` — RELOCATED verbatim into `M4P2MR`, which is upstream
-- of `CapFreeArm3` (`M4ErrRewire`'s cone passes through `M4Sieve`, hence `CapFreeArm3`);
-- (2) `M4RowMR` names Lemma 12's FOUR windowed rows (`lemma12RowsMR`), lands the on-subset
-- MR row (`lemma12_meansq_on_subset_mr_windowed`: `SeamCoefW` in, `hwin` out, `hasupp` in)
-- and prices them through `TypicalPriceK`'s three-stage wire — `second_window_le_first_row`
-- collapses the second seam window onto twice the first, the first LOSES a factor `e`, and
-- the net exit is `960·(T/X_d+1)·(…)` where the landed row is `480·(…)`; (3) `TLegE1`/
-- `TLegExit` are ROW-GENERIC (`E1_bound_gen`, `E1_pin_gen`, `Ej_bound_gen`, `TLeg_bound_gen`,
-- `TLeg_feeds_capstone_gen`): the leg reads Lemma 12's rows only as an opaque additive term
-- plus the per-level Lemma-12 conclusion, and the LANDED names are re-derived from the
-- generic ones with statements byte-identical; (4) `CapFreeArm3`'s three chain statements
-- re-cut (`hcoef` ON-WINDOW, `hwin` deleted, `hasupp` added at §9, the row `lemma12RowsMR`,
-- the prefactor `960`); (5) `ThmA2Rows.a2Rows_of_capfree3` consumes the on-window `hcoef`
-- with `hwin` gone, weighed by `a2_term3_weigh_mr` — `960·3 = 2880 ≤ 5760`, so ⟦AMENDMENT G⟧'s
-- `×4` cover pays and NO interface numeral moves; (6) `M4MeanSq.m4_meansq_per_chi_gen` and
-- `m4_meansq_or_trivial` lose `hwinBand` outright and the widening `hcoefBandW` with it —
-- both conclusions BYTE-IDENTICAL, both theorems strictly STRONGER.  `coef_widen_of_window`
-- keeps no consumer and stays as a documented dead stone (the historical-instance
-- convention).  THE DATUM SIDE: `M4Puncture` supplies the per-block pair law the re-cut
-- `hcoefBand` now wants at the door — at a block-`j` prime `1_𝒮(p·m) = 1_{𝒮∖j}(m)`
-- (`RamWeight.blockOmega_mul_coprime`, the IN-BLOCK case; NOT `M4Band` §1's shift-up), whose
-- one new arithmetic stone is the block separation `𝒬K_1 = 2^{M·A} < 2^{4AG} = 𝒫_2`
-- (`door_block_separation`, free at `G = 3072M`), carried at the HALF-OPEN cut with
-- `M4Band` §4's forced endpoint binder `hend`
open Salt.Tactic in
#audit_axioms Salt.MR.ramP2massMR_direct
  Salt.MR.lemma12RowsMR
  Salt.MR.lemma12_meansq_on_subset_mr_windowed
  Salt.MR.lemma12_on_TsetG_mr_windowed
  Salt.MR.lemma12RowsMR_pricedK
  Salt.MR.lemma12RowsMR_priced_ratioK
  Salt.MR.sum_lemma12RowsMR_pricedK
  Salt.MR.sum_lemma12RowsMR_priced_calibratedK2
  Salt.MR.E1_bound_gen
  Salt.MR.E1_pin_gen
  Salt.MR.Ej_bound_gen
  Salt.MR.TLeg_bound_gen
  Salt.MR.TLeg_feeds_capstone_gen
  Salt.MR.seam_row_calibratedK_nocap3
  Salt.MR.seam_row_number_nocap3
  Salt.MR.seam_row_number_capfree3
  Salt.MR.a2Rows_of_capfree3
  Salt.MR.thm_a2'
  Salt.MR.m4_meansq_per_chi_gen
  Salt.MR.m4_meansq_or_trivial
  Salt.MR.MemSPunct
  Salt.MR.memSPunctCoeff
  Salt.MR.blockOmega_prime_in
  Salt.MR.blockOmega_prime_out
  Salt.MR.memS_mul_prime_punct
  Salt.MR.indicator_mul_punct
  Salt.MR.calQK_one_lt_calP_two
  Salt.MR.door_block_separation
  Salt.MR.door_block_sep_at
  Salt.MR.memSCoeff_seamCoefW_punct_gen
  Salt.MR.memSCoeff_seamCoefW_punct_H
  Salt.MR.doorChiCoeff_seamCoefW_punct_H
  Salt.MR.norm_doorPunctCoeff_le_one

-- ⟦POLY-LOG FLOOR + ℓ²-MASS FAR KERNEL⟧ (`FarL2`, 2026-07-28).  THE PRICING-SCOPE R1 PAGE.
-- ⟦THE FLOOR HALF, CLOSED⟧ `polylog_floor_M0`: the χ-floor at coefficient **`1/4`** on EVERY
-- poly-log height `|v| ≤ (log X)^A`, `A ≥ 1` — against `band_floor_M0`'s `7/30` on the
-- `seamT0`-band and `chi_floor_vk_pointwise`'s `1/16` on the `3X` box.  The whole content is
-- `plog_vk_debit`: on the box `vk_debit_le` reads `loglog|2v| ≤ log2 + loglog X` and pays
-- `(3/16)·loglog X` (the `1/4 → 1/16` collapse); at poly-log height `plog_drift_loglog` /
-- `plog_inner_log` read `loglog|2v| ≤ log(3A) + logloglog X`, DOUBLY logarithmic, so the
-- `loglog X` coefficient stays `1 − 3/4 = 1/4`.  Three arms exactly as `band_floor_M0`
-- (`plog_floor_real` at `k=2`, `chi_floor_band_arm` at `|v| ≤ 1/2`, `plog_floor_nonreal`
-- through the VK branch `chi_Llower_341_vk` above `exp(exp 100)` and `chi_Llower_341_height`
-- AT that absolute height below); NO socket remains (`vkTwistUB_holds`, its two named debits
-- absorbed by the `q`-slot via `plog_vk_qdebit`).  ⟦THE MASTER CHECK⟧ `plog_floor_clears_gate`:
-- the threshold constant is **`16`** (margin `1/4 − (103/1500)e = 0.0633527… ≥ 1/16`), against
-- `cfb_floor_clears_gate`'s `22` at `7/30`; the box's `1/16 = 0.0625 < 0.18665` does not clear
-- the gate at all.  TRANSPORTS `polylog_floor_M0_liouChi` / `polylog_floor_M0_pieceDatum`
-- (`plogM0_add_debit`, the `band_floor_M0_pieceDatum` pattern).  FREE WINS: `band_floor_M0_vk`
-- (w2 — the `T₀`-band floor lifted `7/30 → 1/4`, an instance at `A := 3`) and `box_floor_M0`
-- (w1 — the plain `M₀ ≤ 𝔻²` box form at `1/16`, `capFreeFloor3_margin_all_chi`'s arms with the
-- strict `CapFreeFloor3` wrapper removed, NO margin spent).
-- ⟦THE BOX FLOOR AT THE PIECE⟧ (§12, 2026-07-28 — the re-cut's supply side).  `box_floor_M0`
-- transported to the masked piece by the `polylog_floor_M0_pieceDatum` pattern VERBATIM one
-- coefficient down: `box_floor_M0_liouChi` (the `pretDistSq_liouChi_eq` equality, free) and
-- `box_floor_M0_pieceDatum` (`pretDistSq_pieceDatum_ge` at factor `1`, the debit absorbed by
-- `boxM0_add_debit`), on the WHOLE box `|v| ≤ 3X` with no threshold.  ⟦THE ONE LEMMA THE RE-CUT
-- `T₀`-SUPPLIER CONSUMES⟧ `box_floor_clears_gate_45`: floor + mask + gate in one implication,
-- `700·((5/4)ℓ + (3/4)log q + q + (K+D)) ≤ L ⟹ (1009/45000)·e·L ≤ 𝔻²(λχ̄·g_𝒥, n^{iv}; X)` —
-- `A2Wall.a2wall_gate_45`'s coefficient (`1/45 − 1009/45000 = −1/5000`, EXACT) paid at box
-- strength with margin `1/16 − (1009/45000)e = 0.00155008…`.  Stated in `FarL2`, not `A2Wall`,
-- because the import runs `FarL2 → A2Wall`; the two-line clearance arithmetic
-- (`a2wall_box_clears_45`) is therefore re-run inline there.
-- ⟦THE FAR HALF: THE N-TERM REFUTATION⟧ (P2, a DESIGN FINDING, not a landing).  The scope's
-- route "dyadic Cauchy–Schwarz in `τ` + `dirichlet_poly_l2_mvt_final` against the kernel's
-- `1/(c²+τ²)` weight" does NOT reach a poly-log `H`.  The landed mean value is
-- `∫_{−R}^{R}‖dpoly N a‖² ≤ (2R + 20N)·∑‖aₙ‖²`, so the `τ`-dyadic sum gives `2A/H + N·A/H²`
-- with `A` the ℓ² mass (NO `k`-power — that half of the scope is right) but `N = ⌈k/y⌉₊ ≍ k/L⁴`
-- the window LENGTH.  Pricing the second term against the crown's `k·(log X)^{−1/(32e)}` forces
-- `H ≳ √k·L^{−3.24}`, WORSE than the standing `Tstar = L⁴·k^{1/(4 log L)}`.  The `20N` is the
-- Montgomery–Vaughan constant at the UNIFORM spacing `δ = 1/N` (`mvHilbertUniform_holds`); the
-- sharp `δₙ ≍ 1/n` is not supplied.  THE REPAIR (arithmetic verified, NOT in Lean): split the
-- window dyadically FIRST (`J ≍ L/log 2` blocks), mean-value per block, recombine by
-- Cauchy–Schwarz (cost one factor `J`); the `N`-term becomes `J·∑_j M_j A_j ≍ L·L³ = L⁴` and
-- the pricing forces only `H ≳ 19·L^{2.76}/log L` — POLY-LOG, the scope's target.
-- ⟦LANDED FOR THAT ROUTE⟧ `windowSum_eq_dpoly` (the window polynomial IS an `L2MVT.dpoly` at
-- `winL2Coeff`), `winL2Mass` + `winL2Coeff_l2_eq` + `windowSum_l2_mvt` (the mean value AT the
-- window, unconditional), and `crossKerFar_le_weighted_l2` — the far cross-integral bounded by
-- `((X+h)^{c+1}/h)·(winL2Tail(c₀−β) + winL2Tail(c₀+β))` with NO window mass of any kind, by
-- branch-2 + AM–GM + `farL2_recentre`, on two named integrability sockets.
#audit_axioms Salt.MR.plog_drift_loglog
  Salt.MR.plog_drift_logloglog
  Salt.MR.plog_floor_real
  Salt.MR.plog_vk_debit
  Salt.MR.plog_floor_nonreal
  Salt.MR.plogM0
  Salt.MR.plogM0_add_debit
  Salt.MR.polylog_floor_M0
  Salt.MR.plog_floor_clears_gate
  Salt.MR.polylog_floor_M0_liouChi
  Salt.MR.polylog_floor_M0_pieceDatum
  Salt.MR.band_floor_M0_vk
  Salt.MR.boxM0
  Salt.MR.box_floor_M0
  Salt.MR.boxM0_add_debit
  Salt.MR.box_floor_M0_liouChi
  Salt.MR.box_floor_M0_pieceDatum
  Salt.MR.box_floor_clears_gate_45
  Salt.MR.winL2Coeff
  Salt.MR.windowSum_eq_dpoly
  Salt.MR.winL2Mass
  Salt.MR.winL2Coeff_l2_eq
  Salt.MR.windowSum_l2_mvt
  Salt.MR.winL2Tail
  Salt.MR.crossKerFar_le_weighted_l2

-- ⟦THE N-TERM REPAIR⟧ (`FarL2Dyadic`, 2026-07-28).  THE LAST PRICING PAGE, in Lean.
-- ⟦THE DYADIC-IN-`n` MEAN VALUE⟧ `dpoly_block_l2_mvt`: for ANY cut `P : ℕ → ℕ` with `P 0 = 0`
-- and `P` monotone, `∫_{−R}^{R}‖dpoly (P J) a‖² ≤ J·∑_{j<J}(2R + 20·P(j+1))·A_j` — the block
-- split (`dpoly_eq_sum_blocks`, `Finset.sum_Ioc_consecutive` telescoping), Cauchy–Schwarz over
-- the blocks (`sq_sum_le_card_mul_sum_sq`, the ONE factor `J`), the landed
-- `dirichlet_poly_l2_mvt_final` per block.  ⟦THE N-TERM IS GONE⟧: `20·N·A` (window LENGTH ×
-- total mass) is replaced by `20·J·Π`, `Π = ∑_j P(j+1)·A_j` the BLOCK PRICE.  The constant is
-- the block TOP, not its length — Montgomery–Vaughan's `δ = 1/N` is read at the largest
-- frequency present, which is why the dyadic cut is the right one.
-- ⟦THE `τ`-LAYER CAKE⟧ `far_weight_le_of_linear_growth`: for EVERY nonnegative continuous `φ`
-- with `∫_{−R}^{R}φ ≤ 2RA + B`, `∫_{|τ|>H} φ/τ² ≤ 8A/H + (4/3)B/H²` — dyadic shells
-- `H·2^i < |τ| ≤ H·2^{i+1}`, `MeasureTheory.integral_iUnion`, two geometric series.  Fully
-- general; ONE named socket (the tail's own integrability, the same one
-- `crossKerFar_le_weighted_l2` already carries).
-- ⟦THE PRICED TAIL⟧ `windowSum_l2_block_mvt` + `winL2Tail_dyadic_le`:
-- `winL2Tail g X y σ H ≤ farL2Grade = 8·J·A/H + (80/3)·J·Π/H²`, `A = winL2Mass` (no `k`-power),
-- `Π = winL2Price`.  ⟦THE GATE⟧ `farL2_grade_clears_gate` at `farL2Threshold Ca Cp ε =
-- 16·Ca/ε + √(54·Cp/ε)`.  ⟦THE COMPOSED FAR BOUND⟧ `crossKerFar_polylog` (§6, per-line) and
-- `crossKerFar_polylog_uniform` (§7, `α,β`-uniform at the worst line `c₀ − η`, via the three
-- antitonicity stones `winL2Mass_antitone` / `winL2Price_antitone` / `farL2Grade_antitone`).
-- ⟦THE TWINS, NOW NON-VACUOUS⟧ `joint_cs_trunc_polylog` (`GradeWindowC.joint_cs_trunc_pinC` at
-- `T := H` with `hKfar` DISCHARGED — `FarStar.far_kernel_bound_star` lives only at `Tstar`) and
-- `dilated_scale_grade_polylog` (`SPartStation.dilated_scale_grade` with `Tstar` swapped out:
-- the gate is `|t₁| + H ≤ Rad`, the floor transport by `pretDistSq_floor_dilate` is verbatim,
-- and the far arm rides at `farKfarPolylog` — `farKfarStar`'s replacement with NO ℓ¹ window
-- mass, hence no `k^{1/(4 log L)}` in the KERNEL binder).
-- ⚠ ⟦THE LOW-LINE REFUTATION⟧ (DESIGN arithmetic, NOT kernel-checked; no theorem asserts it).
-- The repair's verified arithmetic is read at `σ ≍ 1`, where `Π ≍ ∑(log n)²/n ≍ L³` is
-- poly-log.  The chain does NOT read `σ = 1`: `hKfar` is uniform over `β ∈ [0, η]`, so the
-- price is read at the LOWEST line `c₀ − η`, where the exponent `2σ − 1 = 1 − (2η − 2/L) < 1`
-- and `Π ≍ L²·k^{2(η−1/L)}/(2η−2/L)` — the SQUARE of `FarStar` §3's ℓ¹ excess.  The `1/H²`
-- takes the square root back out, so the honest threshold is `H ≳ k^{η−1/L}·L^{3/2}√(log L)`:
-- a `k`-power, a factor `≍ e·L^{5/2}` BELOW `Tstar = L⁴k^{η}` but of the SAME grade — NOT
-- poly-log.  The `k`-power is intrinsic to the low line (AM–GM squares it; a `τ`-Cauchy–Schwarz
-- buys back only the square root, landing in the same place).  ⟦WHAT IS UNCONDITIONALLY WON⟧
-- the `N`-term is gone, the `A`-term is mass-free and convergent at every line of the band, and
-- the far arm is stated at a FREE height with `Tstar` nowhere in it.
-- ⟦THE RESIDUE⟧ the datum-level ℓ² estimates `winL2Mass`/`winL2Price` at the piece datum (the
-- `LambdaMass.vonMangoldt_window_damped_min` genre at exponent `2σ` and `2σ−1`) are NOT landed
-- here, so STEP 5 (`m4_hRHS_priced` / `m4_t0band_supplier_complete`) is NOT reached.
#audit_axioms Salt.MR.blockCoeff
  Salt.MR.dpoly_block_eq
  Salt.MR.dpoly_eq_sum_blocks
  Salt.MR.dpolyBlockMass
  Salt.MR.blockCoeff_l2_eq
  Salt.MR.dpoly_block_l2_mvt
  Salt.MR.far_weight_le_of_linear_growth
  Salt.MR.sum_dpolyBlockMass_eq
  Salt.MR.winL2Price
  Salt.MR.continuous_windowSum_sq
  Salt.MR.windowSum_l2_block_mvt
  Salt.MR.farL2Grade
  Salt.MR.winL2Tail_dyadic_le
  Salt.MR.farL2Threshold
  Salt.MR.farL2_grade_clears_gate
  Salt.MR.crossKerFar_polylog
  Salt.MR.winL2Coeff_norm_antitone
  Salt.MR.winL2Mass_antitone
  Salt.MR.winL2Price_antitone
  Salt.MR.farL2Grade_antitone
  Salt.MR.crossKerFar_polylog_uniform
  Salt.MR.joint_cs_trunc_polylog
  Salt.MR.farKfarPolylog
  Salt.MR.dilated_scale_grade_polylog

-- ⟦A2WALL⟧ — the seam re-cut window kernel-verified: floor n ≥ 44 (γ=1/16, δ=1/5000),
-- ceiling m < 97.65 (the ball radius vs ρ₂₉₃ — the freeze's 48 was an abandoned pin);
-- the working pin (n,m) = (45,46) inhabited at 2.12× margin; δ-relaxation FREE (𝒰-leg only).
open Salt.Tactic in
#audit_axioms Salt.MR.a2wall_gate_general
  Salt.MR.a2wall_gate_45
  Salt.MR.a2wall_box_clears_45
  Salt.MR.a2wall_box_floor_clears_gate_45
  Salt.MR.a2wall_exponent_neg_45
  Salt.MR.a2wall_critical_n
  Salt.MR.a2wall_floor_44
  Salt.MR.a2wall_floor_43_fails
  Salt.MR.a2wall_floor_48_at_500
  Salt.MR.a2wall_floor_47_fails_at_500
  Salt.MR.a2wall_floor32_89
  Salt.MR.a2wall_floor32_88_fails
  Salt.MR.a2wall_box_fails_gate_15
  Salt.MR.a2wall_ballrad_forced
  Salt.MR.a2wall_ballrad_pin_exponent
  Salt.MR.a2wall_ceiling_97
  Salt.MR.a2wall_ceiling_98_fails
  Salt.MR.a2wall_ballrad_46_clears
  Salt.MR.a2wall_window_45_46

-- ⟦W2-DOOR-CARRIED⟧ (`M4DoorClose`, 2026-07-28).  THE STRUCTURAL CLOSE OF THE M4 WAVE, with
-- the `hT0band` slot CARRIED.  `M4DoorRow` landed the door row's supply and named two walls;
-- the counter-wave demolished both (`hwinBand` DELETED, the length-graded re-cut), and
-- `M4T0Datum` reduced the T₀-band to a pricing residue on a morning ruling — so every OTHER
-- binder of `M4MeanSq.m4_meansq_per_chi_gen` is now inhabitable at the door datum, and this
-- file inhabits them.  ⟦THE FINAL CARRIED REGISTER⟧, three classes (module header):
-- (A) ANALYTIC-CARRIED, exactly TWO arms — the T₀-band integral at
-- `m4_hT0band_at_door`'s own conclusion shape (the RAW slot, so the morning route plugs by
-- `exact` at either granularity) and the coprime supply `M4CoprimeBlockMeanSq` at its
-- interval/length-general shape (⟦R2⟧'s deviation: `m4_nonCoprime_classMeanSq` consumes
-- exactly that, no adapter); (B) REGIME — the scale page at the BLOCK scale `X_d`, the band
-- gates with `(P, Q)` chosen PER INSTANCE, the ε-window, the tail threshold
-- `2688·Ctail·loglog X` stated where the opaque mass constant is bound, the socket's ~25
-- gates verbatim from `m4_supplier_complete` at `Ps := 1`/`J := 2`/`Tann := X`/`t₁ := 0`/
-- `Rrad := seamRad X`, the `hend` ENDPOINT gate per instance (discharge condition `X_d ∉ 𝒮`,
-- `memSCoeff_eq_zero_of_not_memS`; the converse `memSCoeff_endpoint_zero_of_seamCoefW` is why
-- it is forced), and the `g`-arm/`U1floor` shapes of the outer register; (C) WITNESSED —
-- `ha1`/`hcf1`/`hsupp0`/`hasupp`, `hb1`/`hbf1` at the PUNCTURED family `memSPunctCoeff … 2 j`,
-- the whole coprime-tail page (`Mtail` and `EP2` COMPUTED from `m4_door_tail_supply`, not
-- carried), `hsockR`, `hcoefBand` (`doorChiCoeff_seamCoefW_punct_H`), `hcoefPin`
-- (`doorChiCoeff_seamCoefW_at_door_H`), the per-piece cap-free floor
-- (`capFreeFloor3_pieceDatum`, so only the Mertens mask debit is a numeral), and the two pins.
-- ⟦THE LENGTH FLOOR IS FREE⟧ `doorRowFloor M ≤ j` DERIVES both `4 ≤ h` and the capstone's own
-- window gate `𝒬K_1 ≤ h` (`door_length_gate_iff`'s converse) — the graded split's partition
-- costs the supplier nothing above the floor, and `doorRow_trivial_grade` shows the grade
-- below it is the absolute `4` (`‖(1/h)·shortSum‖ ≤ (h+1)/h ≤ 2` at every `j`, `j = 0`
-- included).  ⟦THE K6 DISCIPLINE⟧ FOUR suppliers hoisted ONCE outside the instance quantifier
-- (`m4_meansq_per_chi_gen`'s seven constants, `m4_supplier_complete`'s `Xsk`,
-- `capFreeFloor3_pieceDatum`'s `Kcf`, `m4_door_tail_supply`'s `Ctail`), their gates INSIDE.
-- THE EXIT: `m4_wave_structurally_closed` — (the register) → `¬ logChowla2Fails R.eps R.x R.ω`,
-- end to end, at the door's own floor `j₀ = doorRowFloor M = M·Adoor M`.
open Salt.Tactic in
#audit_axioms Salt.MR.DoorRowCarried
  Salt.MR.doorRow_trivial_grade
  Salt.MR.m4_door_meansq_carried
  Salt.MR.m4_dyadicRow_carried
  Salt.MR.m4_wave_structurally_closed

-- ⟦T0-DISCHARGE⟧ (`M4T0Discharge`, 2026-07-28).  THE FIRST CARRIED ANALYTIC ARM, CLOSED.
-- `m4_wave_structurally_closed` carried TWO analytic arms; this file discharges the `T₀`-band
-- conjunct of `DoorRowCarried` — the RAW slot `∫_{−seamT0 X}^{seamT0 X} ‖dpolyA (winCutH X_d
-- (doorChiCoeff χ M)) (seamS0 (2X_d) X) t‖² ≤ t0BandB X C₁′ M₀` — at an EXPLICIT pinned pair
-- `(C₁′, M₀) = (cfbC₁ X (t0dC1 Cb), t0dM0 X)`, `t0dM0 X = (1009/45000)·e·loglog X`.
-- ⟦WHY IT CLOSES NOW⟧ `M4T0Datum`'s ⟦PRICING RESIDUE⟧ was a STRENGTH shortfall, never a RANGE
-- one: `dilated_scale_grade`'s `hM₀` reads the CONTOUR-BOX range `|v| ≤ Rad ⊇ |t₁| + Tstar`, and
-- the box floor `1/16` was `2.99×` short of the OLD gate `(103/1500)e` (`a2wall_box_fails_gate_15`)
-- but CLEARS the re-cut gate `(1009/45000)e = 0.060950…` with margin `0.00155008…`.  So the
-- ORIGINAL `Tstar`-reach pricer works verbatim and the whole route is composition:
-- `box_floor_M0_pieceDatum` → `dilated_scale_grade` (`t₀ = 0`, `t₁ = t`, `Rad = 3X`, `Xd = X_w`)
-- → `piece_center_of_wide`'s `hRHS` at `B := t0dB X Cb` → `m4_hT0band_at_door_of_wide` → the slot.
-- ⟦THE THREE NUMERALS⟧ `t0dM0` (the gate value: the SMALLEST `M₀` making the exit's first
-- summand decay, at `(log X)^{−1/5000}`); `t0dB` (the per-piece grade —
-- `e^{−M₀/(2e)} = (log X)^{−1009/90000}` by `t0d_decay_eq`, and the far arm's own `1/(32e) =
-- 0.011494…` DOMINATES `1009/90000 = 0.011211…` by `t0d_far_exp_le`, the SECOND place the
-- re-cut's margin is spent); `t0dC1 = 4·cSq·(C(c,Cb) + 2·farCStar + 5)`, `X`-free and `q`-free.
-- ⟦THE DILATION PRICE IS ABSOLUTE⟧ `t0d_dilGap_le`: at `√X ≤ X_w ≤ X` the Mertens gap is `≤ 4`
-- with NO `X`-dependence, so it is paid inside the floor's constant (`boxM0_add_debit`) — the
-- `700`-threshold is read at `Kbox + (Dmask + 4)`.
-- ⟦THE PINNED PAIR PAYS⟧ `t0d_envelope_decay`:
-- `(cfbC₁ X C₁)²·e^{−M₀⋆/e} ≤ (C₁+1)²·(log X)^{−1/5000}` — `a2wall_gate_45` at the discharged
-- pair, i.e. the crude fold's `√(seamT0 X)` is paid back with `1/5000` to spare.
-- ⟦THE REGISTER UPDATE⟧ `DoorRowCarriedT0` = `DoorRowCarried` with the two existential slots
-- `C₁′`/`M₀` GONE (pinned) and the `T₀` INTEGRAL replaced by `DoorRowT0Gates` (eight `X`-side
-- gates: the hoisted threshold, the dilation frame, the `700`-threshold, the `Tstar` reach
-- `seamT0 X + Tstar(2X, log 2X) ≤ 3X`, the dissection depth's decay).  `doorRowCarried_of_t0free`
-- is the bridge (98 conjuncts, one replaced); `m4_wave_closed_T0_discharged` is the exit —
-- **(the coprime-supply arm) + (regime) → ¬ logChowla2Fails R.eps R.x R.ω**, ONE analytic arm
-- left in the register.
open Salt.Tactic in
#audit_axioms Salt.MR.t0dM0
  Salt.MR.t0dB
  Salt.MR.t0dC1
  Salt.MR.t0d_decay_eq
  Salt.MR.t0d_far_exp_le
  Salt.MR.t0d_far_le
  Salt.MR.t0d_P_le
  Salt.MR.t0d_err_le
  Salt.MR.t0d_dilGap_le
  Salt.MR.one_le_t0dC1
  Salt.MR.t0d_piece_hRHS
  Salt.MR.m4_t0band_discharged
  Salt.MR.t0d_envelope_decay
  Salt.MR.DoorRowT0Gates
  Salt.MR.DoorRowCarriedT0
  Salt.MR.doorRowCarried_of_t0free
  Salt.MR.m4_wave_closed_T0_discharged

-- ⟦THE COPRIME-SUPPLY ARM, SUPPLIED⟧ (`M4CoprimeSupply` + `M4NonCoprime` §6, 2026-07-28) —
-- the second of `M4DoorClose`'s two carried analytic arms, discharged from the free row
-- datum.  ⟦COPRIME-SCOPE⟧'s finding first: `M4CoprimeBlockMeanSq` as carried is OVER-GENERAL
-- — its grade's small-length summand is off by `H/L` for ANY route, unconditionally — so
-- iron rule 1 keeps it standing and `M4CoprimeBlockMeanSqN` lands BESIDE it with ONE
-- hypothesis added, ⟦THE NARROWING⟧ `H ≤ arcDen 12 H · L`.  The narrowing is FREE at both
-- consumption sites (`m4_nonCoprime_classMeanSq_N`, whose hypothesis list, conclusion and
-- grade are byte-identical to `m4_nonCoprime_classMeanSq`'s): at `L = H` it is
-- `1 ≤ arcDen 12 H` (`one_le_arcDen_of_regime`), and at `L = ⌊H/d₀⌋+1` it is `H ≤ d₀·L`
-- against `d₀ ≤ q ≤ arcDen 12 H`.  The supply is `M4Maximal`'s dyadic maximal step re-run at
-- a FREE block `(A, B]` and a FREE length `L`: §1 the χ-reduction (a verbatim mirror — every
-- χ-layer stone is base- and length-generic, the `1/φ(q)` cancels exactly); §2 the free
-- shifted bridge, where the interface's slack-`4` fit forces
-- `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` in place of the ladder's tight bridge
-- (⟦THE hcov REPAIR⟧: that lemma's coverage hypothesis was asked for on `(A, B]` but READ
-- only on `(A, B−4]`, so it is now stated there — zero proof change, no consumer existed);
-- §3 the free maximal step.  ⟦THE LEDGER⟧ the free block's four units of slack: the analytic
-- half (`j₀ ≤ j`) lands ON THE NOSE against the grade's first summand (`Λ_L ≤ Λ_H` and
-- nothing else); the trivial half (`j < j₀`) is charged at the ABSOLUTE grade `1` — no row
-- datum is read below the floor at all, so the register owes ONE envelope gate, not two —
-- and takes (at ⟦LEVER 1′⟧) the head's `(4/3)^{j₀}` summand together with the slack residue
-- (the fit's `+4` and the drop's `4·(2^j)²/A`, both `A`-free, together
-- `(54/5)·(2·Fan H + 8)·L²`), while the head's `(8/3)^{j₀}` summand — normalised by `H²`
-- against a free length only `≥ H/arcDen` — is what forces ⟦G1⟧ up to `arcDen²`.  TWO
-- new class-(a) gates, both `H`-only and consumer-choosable: ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`
-- (the trivial envelope against the arc denominator SQUARED — a threshold, not a saving; the
-- honest exponent is `log₂(8/3) = 1.415`, rounded up to the integer square) and ⟦G2⟧
-- `44·MSan H + 87 ≤ (4/3)^{j₀}` (the slack residue against the floor's own constant; at the door
-- `j₀ = M·Adoor M ≥ 2^18`, so this is a formality — but `j₀` is a PARAMETER here, never a
-- numeral).  ONE regime fact carried: `8·arcDen 12 H ≤ H`, `M4NonCoprime`'s own `harc` with
-- `2 → 8`, which turns ⟦THE NARROWING⟧ into `8 ≤ L` and hence (on a non-empty block) into
-- `L ≤ 2A` and `B ≤ 2A` — without it the block `A = 1`, `L = 4`, `B = 2` is legal and
-- carries no such comparison.  THE EXIT `m4_coprimeN_supplied` emits
-- `m4BclGraded j₀ (2·MSan) (2·MStr)` **verbatim**: no register line moves.  Anti-vacuity at
-- every layer (`m4_coprimeBlockMeanSqN_trivial` and `m4_coprimeChiBlockMeanSqN_trivial` at
-- grade `5`, `m4_chiFreeShiftBlock_trivial` at grade `1`).
open Salt.Tactic in
#audit_axioms Salt.MR.M4CoprimeBlockMeanSqN
  Salt.MR.m4_coprimeBlockMeanSqN_of_full
  Salt.MR.m4_coprimeBlockMeanSqN_trivial
  Salt.MR.one_le_arcDen_of_regime
  Salt.MR.m4_nonCoprime_classMeanSq_N
  Salt.MR.norm_sum_doorSievedWindow_le
  Salt.MR.doorChiSup_le_len
  Salt.MR.M4CoprimeChiBlockMeanSqN
  Salt.MR.m4_coprimeChiBlockMeanSqN_trivial
  Salt.MR.m4_coprimeMeanSqN_of_chiMeanSqN
  Salt.MR.M4ChiFreeRowMeanSq
  Salt.MR.M4ChiFreeShiftBlockMeanSq
  Salt.MR.m4_chiFreeShiftBlock_trivial
  Salt.MR.m4_chiFreeShiftBlock_of_freeRow
  Salt.MR.m4_coprimeChiN_of_freeShiftBlock
  Salt.MR.m4_coprimeN_supplied

-- ⟦THE SWAP⟧ (`M4Collapse`, 2026-07-28) — the M4 wave's SECOND carried analytic arm,
-- discharged, and the exit re-composed around it.  `m4_wave_closed_T0_discharged` consumes
-- `M4CoprimeBlockMeanSq` (the interface ⟦COPRIME-SCOPE⟧ proved unsuppliable) INSIDE its own
-- proof, and the narrowed twin does not imply the full one — so the swap is not a patch but
-- an ADDITIVE re-run of the two compositions off the same three landed stones
-- (`m4_wave_closed_of_dyadicRow`, `m4_dyadicRow_carried`, `doorRowCarried_of_t0free`), with
-- `m4_nonCoprime_classMeanSq_N ∘ m4_coprimeN_supplied` at `j₀ := doorRowFloor M` in place of
-- `m4_nonCoprime_classMeanSq` at the raw arm.  Both landed exits stand untouched; nothing
-- upstream moves.  ⟦THE DIFF⟧ against `m4_wave_closed_T0_discharged`, machine-checked: ONE
-- line replaced (the coprime arm → `M4ChiFreeRowMeanSq R M MS`, the free-base row datum at
-- the register's OWN grade — no new envelope), THREE added (⟦G1⟧, ⟦G2⟧, ⟦the regime fact⟧,
-- all three `H`-only class-(a) thresholds, all three verbatim `m4_coprimeN_supplied`'s), and
-- every other byte identical INCLUDING the conclusion `¬ logChowla2Fails R.eps R.x R.ω`.
-- The landed `2·arcDen 12 H ≤ H` is KEPT although `8·arcDen 12 H ≤ H` subsumes it, so that
-- the diff is exactly one replacement plus three additions.  ⟦THE WALL, named⟧ the row datum
-- is CARRIED and not derived from the register: `M4ChiFreeRowMeanSq` is quantified over a
-- FREE base (`∀ A : ℕ, 0 < A → ∀ s ≤ L`), while the register supplies the ladder bases
-- `doorLadder R.x H (i+1) + s` and — under ⟦W5⟧'s ruled `∀d` extension — the dilated ones
-- `⌊doorLadder R.x H (i+1)/d⌋ − 1 + s`, `s ≤ ⌊H/d⌋+1`.  No register discharges a free base:
-- at `A ≍ 2^j` the row mean square is `≍ 1` against a grade that is a saving, and the
-- capstone is silent there (`h ≤ X(log X)^{−1/5}` fails at `X ≍ h`).  It is ⟦COPRIME-SCOPE⟧'s
-- genre one level down — narrowed there in the LENGTH, still free here in the BASE — and the
-- repair (a base-narrowed twin of the row interface, threaded through `M4CoprimeSupply`
-- §2/§3/§1, where each step consumes at the SAME `A` it concludes at) is a statement design.
-- THE EXIT: **(the free-base row datum) + (regime) → ¬ logChowla2Fails R.eps R.x R.ω**, with
-- the collision twin beside it; `M4Collapse`'s header enumerates the whole register in the
-- two classes — that list IS the S11 spine's consumption contract.
open Salt.Tactic in
#audit_axioms Salt.MR.m4_wave_closed_coprime_discharged
  Salt.MR.doorLadder_pow_lower
  Salt.MR.m4_wave_closed_coprime_discharged_False

-- ⟦BASE-NARROW — THE COLLAPSE⟧ (`M4BaseNarrow`, 2026-07-28) — ⟦THE WALL⟧ down, and the M4/S9
-- road at its TERMINAL FORM: `m4_wave_collapsed` carries **regime gates and witnessed data
-- ONLY — zero analytic arms**.  ⟦THE WALL⟧ was the QUANTIFIER, never the arithmetic:
-- `M4ChiFreeRowMeanSq` is stated over a FREE base and a register supplies its datum at a
-- LIST of bases, and a floor cannot turn a list into a half-line.  So the load-bearing
-- currency here is `M4RowDatumAt` — the row mean square at ONE `(H, L, χ, A)`, quantified
-- over the dyadic lengths `j ≤ log₂L` and the shifts `s ≤ L` and nothing else — and
-- `M4CoprimeSupply` §2/§3/§1 are re-run at it (`m4_freeShiftBlock_at`, `m4_chiBlock_at`,
-- `m4_classBlock_at`, composed as `m4_coprimeBlock_at`): each step consumes its input at the
-- SAME `A` it concludes at, so the base rides through and the ledger does not move — the
-- grade emitted is `m4BclGraded (doorRowFloor M) (2·MSan) (2·MStr)` VERBATIM, and the base
-- narrowing is then not a hypothesis of the chain at all but the side condition a consumer
-- checks.  ⟦W5, TAKEN ADDITIVELY⟧ the per-instance register's ARM-1 line gains the ruled
-- `∀ d, 0 < d → (d:ℝ) ≤ arcDen 12 H` quantifier, the base dilated to
-- `⌊doorLadder R.x H (i+1)/d⌋ − 1 + s` and the shift range to `s ≤ ⌊H/d⌋ + 1`; everything
-- else (the `j`-range, every conjunct of `DoorRowCarriedT0`, the grade slot `MS j H`) is the
-- landed line's.  The `d = 1` instance REPRODUCES it — `⌊X/1⌋ − 1 + (s+1) = X + s` — so
-- `M4ChiDyadicRowMeanSq` and the coprime branch's row datum both come off the same line, and
-- `M4DoorClose`/`M4T0Discharge` are NOT touched: `m4_rowDatum_dilated` re-composes off
-- `m4_door_meansq_carried` and `doorRowCarried_of_t0free` directly, so both landed exits
-- stand byte-identical.  ⟦THE TWO SITES⟧ `m4_classBlockMeanSq_of_rowDatum` re-runs
-- `m4_nonCoprime_classMeanSq_N` with the per-base supply at `(L = H, A = X_{i+1})` and at
-- `(L = ⌊H/d₀⌋+1, A = ⌊X_{i+1}/d₀⌋−1)` — `d0_ledger` closes the dilated branch on the nose,
-- the `q²` slot stays open, the drift line does not move.  ⟦THE ℕ-FLOOR BOOKKEEPING⟧
-- `2 ≤ ⌊X_{i+1}/d⌋` from `2·arcDen 12 H ≤ H < X_{i+1}` (the dilated base is positive);
-- `⌊H/d⌋ + 1 ≤ H` at `2 ≤ d` (the dilated `j`-range sits inside the register's).  ⟦THE
-- BUNDLED TWIN, FOR THE RECORD⟧ `M4ChiFreeRowMeanSqN` (the ruled `Φ H · L ≤ A` narrowing) and
-- `M4CoprimeBlockMeanSqNN` land beside the currency with the chain at them
-- (`m4_coprimeNN_supplied`), and `narrow_dilate` is the floor's own dilation law
-- (`Φ·H + (Φ+2)·d ≤ A → Φ·(⌊H/d⌋+1) ≤ ⌊A/d⌋−1`, one unit to spare) that discharges the
-- narrowing at the dilated site.  THE EXIT: **(regime) + (witnessed) → ¬ logChowla2Fails
-- R.eps R.x R.ω**, with the collision twin beside it; the diff against
-- `m4_wave_closed_coprime_discharged` is exactly TWO lines (the register's `∀d`, and the
-- analytic row line GONE).  `M4BaseNarrow`'s header enumerates ⟦THE FINAL REGISTER⟧ in the
-- two classes — that list IS the S11 spine's consumption contract, and class (c) is empty.
-- ⟦THE REGISTER-SCOPE WAVE⟧ (2026-07-29) re-cuts two of its lines against `M4Spine`'s
-- ⟦WALL C⟧, conclusions byte-identical: ⟦gate 12⟧ is now the `M`-relative dilation cap
-- `arcDen 12 H < calP (Adoor M) (3072M) 1` (`M4Residue.door_dilation_gate'`, threaded through
-- `M4BridgeDilate`/`M4ClassPrice`/`M4NonCoprime`/`M4BaseNarrow`/`M4DoorClose`/`M4Collapse` as
-- a hypothesis WEAKENING at every site), and `Qm` moves from the leading parameter into the
-- witnessed group beside `M`, `k` — legitimate because the three `Qm`-taking suppliers are
-- Skolemised (`capFreeFloor3_liouChi_all → Kfl`, `capFreeFloor3_pieceDatum → Kcf`,
-- `doorRowCarried_of_t0free → Kbox, X₀w`, all now `ℕ → ℝ`), which lets
-- `m4_modulusCap_discharged` close ⟦gate 9⟧ at `Qm := ⌈arcDen 12 R.Hhi⌉₊`.  The five re-cut
-- statements: `m4_meansq_per_chi_gen`, `m4_door_meansq_carried`, `m4_dyadicRow_carried`,
-- `m4_rowDatum_dilated`, `m4_wave_collapsed` (+ its `False` twin); every OTHER consumer keeps
-- its statement byte-identical by reading the choice functions at its own leading `Qm`.
-- ⟦WALLS A AND B STAND⟧ — the wave makes the register honest and `Hhi`-safe; it does not
-- unblock the spine.
open Salt.Tactic in
#audit_axioms Salt.MR.M4RowDatumAt
  Salt.MR.m4_freeShiftBlock_at
  Salt.MR.m4_chiBlock_at
  Salt.MR.m4_classBlock_at
  Salt.MR.m4_coprimeBlock_at
  Salt.MR.m4_classBlockMeanSq_of_rowDatum
  Salt.MR.M4ChiFreeRowMeanSqN
  Salt.MR.m4_rowDatumAt_of_freeRowN
  Salt.MR.M4CoprimeBlockMeanSqNN
  Salt.MR.m4_coprimeNN_supplied
  Salt.MR.narrow_dilate
  Salt.MR.m4_rowDatum_dilated
  Salt.MR.arcDen_le_arcDen_Hhi
  Salt.MR.m4_modulusCap_discharged
  Salt.MR.m4_wave_collapsed
  Salt.MR.m4_wave_collapsed_False

-- ⟦THE S11 SPINE — THE THREE WALLS⟧ (`M4Spine`, 2026-07-28).  The spine's job was to FIRE
-- `m4_wave_collapsed`: instantiate `(C, U1floor, g)`, then `(δ, Braw, MS, MSan, MStr, M, k)`
-- at the exit's regime, discharge the eighteen gates, land `m4_door_closed` unconditional.
-- **It does not fire, and the obstruction is the register itself.**  ⟦WALL A — THE BUDGET
-- COLLISION⟧ the arithmetic gates are JOINTLY INCONSISTENT: ⟦gate 8⟧ pins `δ` at the
-- DECAYING MRT grade (`δ ≲ C/(log H)²`), `M4DoorGates.hMδ` (`24·Cg/δ ≤ M`) then forces
-- `M ≳ (log H)²/C` and so `j₀ = doorRowFloor M ≥ 2^18·M`, while ⟦gate 6⟧'s small-length
-- summand `(9/2)(3/2)^{log₂H}(4/3)^{j₀}/H` of `m4BclGraded` (⟦LEVER 1′⟧'s weighted head at
-- `(3/2)^{log₂H} ≥ 1`) — with `MStr H` pinned from BELOW by ⟦G1⟧ — under ⟦gate 7⟧'s cap gives
-- `(4/3)^{j₀} ≤ C²·H`, i.e. `j₀·log(4/3) ≤ 2C + log H` and so (at `log(4/3) ≥ 1/4`)
-- `j₀ ≤ 8C + 4·log H`.  Multiplying:
-- **`589824·(log H)² ≤ 2C² + (log H)·C`** (`m4_spine_budget_necessary` — the geometric
-- weights cost the collision exactly a factor `4`, and `589824 ≫ 3` is all the wall needs:
-- ⟦WALL A⟧ SURVIVES the lever, which is itself the measure of how far its repair must go),
-- which at every
-- regime's `log H ≥ 15` forces `log H ≤ C` (`m4_budget_forces_C`) — impossible, since `C` is
-- fixed BEFORE `R` and `R.Hhi` is unbounded above, and outright contradictory against the
-- exit's own floor `H0scale C ≤ R.Hlo` (`C² ≤ log H`, `m4_budget_collision`).  So
-- `m4_wave_collapsed` is TRUE but VACUOUS; the repair is a statement ruling (an `M`-free
-- small-length term, or a per-`H` door grade `δ H` decoupling `M` from the top of the window
-- range).  ⟦WALL B — THE ENDPOINT⟧ `DoorRowCarriedT0`'s `hend : doorChiCoeff χ M X_d = 0` is
-- carried PER INSTANCE and the register quantifies `∀ s ≤ ⌊H/d⌋+1`, so at `d = 1` it demands
-- the sieved χ-twisted datum vanish on a FULL interval of `H+2` consecutive integers at every
-- ladder block bottom (`m4_register_forces_endpoint_interval`) — its only discharge route is
-- `X_d ∉ 𝒮`, and `𝒮` is the Ramaré sieve, which keeps almost every integer.  `M4DoorClose`'s
-- ⟦ENDPOINT CONVENTION⟧ ("a consumer discharges it by choosing `s`") points at a freedom
-- `M4Maximal.M4ChiDyadicRowMeanSq`'s own `∀ s` had already spent.  ⟦WALL C⟧ ⟦gates 9/12⟧ were
-- `H`-UPPER bounds (`arcDen 12 H ≤ Qm`, `log H ≤ 2^{21845}`) against a regime whose `Hhi` the
-- exit never bounds above — and are REPAIRED by the register-scope wave (2026-07-29): gate 12
-- is `M`-relative (`M4Residue.door_dilation_gate'`, the cap is the door's own `P₁`), and gate
-- 9 is discharged by the Skolem reorder — `Qm` moved into the witnessed group beside `M`, `k`
-- (`Kfl`, `Kcf`, `Kbox`, `X₀w` are now choice functions `ℕ → ℝ`), then closed at
-- `Qm := ⌈arcDen 12 R.Hhi⌉₊` (`M4BaseNarrow.m4_modulusCap_discharged`).  ⟦WALLS A AND B
-- STAND⟧ — the register is honest and `Hhi`-safe, and still unfulfillable; the same wave
-- banks the refutation of the C2(ii) repair (`m4_spine_budget_collision_perH_at_Hlo`: a
-- per-`H` door grade `δ H` collides at `H := R.Hlo`, where both `H`-side hypotheses are free
-- from `hHlo_floor` and the exit's own `H0scale C ≤ R.Hlo`).  ⟦WHAT LANDS⟧ the two reusable
-- stones the attempt produced: the brief's ⟦S-4⟧ arc page (`8·(log H)^{12} ≤ H` past `10^36`,
-- the discharge of ⟦gates 13/14⟧ in ANY repaired register) and the delivered grade against a
-- clean `1/(log H)²`.
open Salt.Tactic in
#audit_axioms Salt.MR.m4ArcFloor
  Salt.MR.arcDen_twelve_eq_pow
  Salt.MR.eight_arcDen_le_of_arcFloor
  Salt.MR.two_arcDen_le_of_arcFloor
  Salt.MR.mrtDeliveredGrade_le_inv_sq
  Salt.MR.m4_spine_budget_necessary
  Salt.MR.m4_budget_forces_C
  Salt.MR.m4_budget_collision
  Salt.MR.m4_spine_budget_collision
  Salt.MR.m4_spine_budget_collision_at_Hlo
  Salt.MR.m4_spine_budget_collision_perH_at_Hlo
  Salt.MR.doorRowCarriedT0_endpoint
  Salt.MR.m4_register_forces_endpoint_interval

/-! ## ⟦THE ENDPOINT WALL⟧ — the STRICT pair law and the FUSED `p²` row (2026-07-29)

Flags: ⟦ENDPOINT-ROW-SCOPE⟧ (the fusion design), ⟦BUDGET-SPLIT-SCOPE⟧ (context),
⟦ENDPOINT-REF⟧ (the BINDING v2 amendments).

**THE WALL.**  The whole MR chain read its factorization at the CLOSED window antecedent
`X_d ≤ p·m` (`SeamRowWindowed.SeamCoefW`), while the door's own cut is HALF-OPEN
(`M4DoorRow.winCutH` — the capstone's `hsupp0` kills the datum AT `X_d`, `hasupp` allows
support on `[X_d, 2X_d]`).  The straddle forced a genuine arithmetic obligation on the datum
(`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` shows it is FORCED, not a convenience).

**THE REPAIR — a FUSION, not a fifth row.**  A fifth Cauchy–Schwarz row would make the
prefactor `5` and `5·520 = 2600 > 2160 = 3·720`, breaking `A2Frame3.err`'s standing
right-hand side (and no `moment_split5` exists).  Instead:

* `SeamCoefWS` is `SeamCoefW` with the STRICT antecedent `X_d < p·m`
  (`seamCoefWS_of_seamCoefW` — additive, iron rule 1), and the band/puncture pair laws at it
  take `haH` ALONE: `ha0` and `hend` both DROP, the `m = 0` case dying by absurdity;
* the released endpoint cofactors are FUSED into the `p²` row, whose inner filter is enlarged
  to `p ∣ m ∨ p·m = X` (`RamareP2End`'s `ramP2domEndMR`/`ramP2corrEndMR`/`ramP2coeffEndMR`,
  NEW siblings — the landed `ramP2*MR` defs are byte-untouched, `SmallStones`:385-460 reads
  them).  The split stays at FOUR rows; `moment_split4` and `M4ErrRewire.err_grade_fit`'s
  `4·520 ≤ 2160` are untouched.

**THE PRICE.**  `M4P2MR.ramP2massEndMR_direct`: the max half is FREE (the fibre injection
into `primeFactors` never used `p ∣ m`), the `Σ` half gains `2·ω(X)/X` through the endpoint
singletons (`p·m = X` determines `m`, and `p ∣ X`), whence

  `Σ_{n≤N} ‖ramP2coeffEndMR n‖²/n² ≤ 16·log₂(2X)/(X·P) + 4·(log₂(2X))²/X²`.

The excess `M_end := 4·(log₂(2X_d))²/X_d²` (`M4ErrRewire.endMass`) is paid TWICE, once per
side, and NEITHER payment moves an interface numeral:

* the SEAM side carries it as a separate `hEP2` summand (the ⟦R3a⟧ `Mtail` pattern) through
  five sites — `err_at_witness_mr_end`, `a2Frame3_witness_end`, `m4_ep2_budget_at_band_end`,
  `m4_tail_supply_at_band_end`, `m4_door_tail_supply_end`.  `witEP2` and its `896`/`10752`
  numerals are byte-untouched; the ε-ledger goes `673 → 673 + 2688 = 3361 ≤ 4320`, still
  inside `habs`'s own half, and the `2688·L²/X` crumb is covered by the A-class stone
  `3(log X)³ ≤ X` derived INLINE from the existing `hL : 256 ≤ log X` (`e^{u/5} ≥ u/5`,
  five-fold) — NO new named threshold;
* the ROW side absorbs it inside `M4RowMR.four_rows_le_end`'s own slack (⟦AMENDMENT 1⟧): the
  landed regrouping spends `8` of `12` on the `B2` slot, an exact `1.5×` unspent factor, and
  `4L²/X_d² ≤ (1/2)·16L/(X_d·P)` ⟺ **`log₂(2X_d)·P ≤ 2·X_d`**, which `logb_two_mul_P_le`
  derives from the row's EXISTING binders `hP`/`hPQ`/`hreg`/`hbig` (`P ≤ e^{√u}`,
  `L ≤ (3/2)u`, `(3/2)u·e^{√u} ≤ 2e^u`).  So `lemma12RowsMR_pricedK_end`'s right-hand side is
  the landed one BYTE FOR BYTE, and `_priced_ratioK`/`_calibratedK2`/`seam_row_number_*`/
  `a2Rows_of_capfree3_end` thread with unchanged brackets — `ThmA2.a2RowsSum`, `a2Mrow`,
  `a2_term3_weigh_mr` and `thm_a2'_of_rows` NEVER MOVE, and both register grading conjuncts
  stay byte-identical.  `a2Rows_of_capfree3_end` is a NEW theorem beside the landed one, not
  a restatement of it.
-/
open Salt.Tactic in
#audit_axioms Salt.MR.SeamCoefWS
  Salt.MR.seamCoefWS_of_seamCoefW
  Salt.MR.memSCoeff_seamCoefWS_band_gen
  Salt.MR.memSCoeff_seamCoefWS_band_H
  Salt.MR.doorChiCoeff_seamCoefWS_band_H
  Salt.MR.doorChiCoeff_seamCoefWS_at_door_H
  Salt.MR.memSCoeff_seamCoefWS_punct_gen
  Salt.MR.memSCoeff_seamCoefWS_punct_H
  Salt.MR.doorChiCoeff_seamCoefWS_punct_H

open Salt.Tactic in
#audit_axioms Salt.MR.ramP2domEndMR
  Salt.MR.ramP2corrEndMR
  Salt.MR.ramP2coeffEndMR
  Salt.MR.ramP2corrEndMR_eq_spoly
  Salt.MR.ramP2corrEndMR_moment
  Salt.MR.mem_ramP2domEndMR_window
  Salt.MR.mem_ramP2domEndMR_prime
  Salt.MR.ramP2domEndMR_fiber_card_le_omega
  Salt.MR.ramP2coeffEndMR_norm_div_le
  Salt.MR.ramP2domEndMR_sum_le
  Salt.MR.ramP2coeffEndMR_sum_div_le
  Salt.MR.ramP2massEndMR_direct

open Salt.Tactic in
#audit_axioms Salt.MR.spoly_ramare_split_mr_windowed_end
  Salt.MR.ramErr_decomp_mr_windowed_end
  Salt.MR.ramErr_moment_split_mr_windowed_end
  Salt.MR.lemma12_meansq_mr_windowed_end
  Salt.MR.lemma12_meansq_mr_blockSupport_windowed_end
  Salt.MR.lemma12_meansq_mr_consume_windowed_end

open Salt.Tactic in
#audit_axioms Salt.MR.endMass
  Salt.MR.endMass_nonneg
  Salt.MR.E_priced_mr_end
  Salt.MR.E_priced_mr_row_scale_end
  Salt.MR.err_at_witness_mr_end
  Salt.MR.a2Frame3_witness_end
  Salt.MR.m4_ep2_budget_at_band_end
  Salt.MR.m4_tail_supply_at_band_end
  Salt.MR.m4_door_tail_supply_end

open Salt.Tactic in
#audit_axioms Salt.MR.lemma12RowsMR_end
  Salt.MR.lemma12_meansq_on_subset_mr_windowed_end
  Salt.MR.lemma12_on_TsetG_mr_windowed_end
  Salt.MR.lemma12RowsMR_pricedK_end
  Salt.MR.lemma12RowsMR_priced_ratioK_end
  Salt.MR.sum_lemma12RowsMR_pricedK_end
  Salt.MR.sum_lemma12RowsMR_priced_calibratedK2_end

open Salt.Tactic in
#audit_axioms Salt.MR.seam_row_calibratedK_nocap3_end
  Salt.MR.seam_row_number_nocap3_end
  Salt.MR.seam_row_number_capfree3_end
  Salt.MR.a2Rows_of_capfree3_end

-- ⟦F4⟧ (`CapFreeSharp`, 2026-07-29) — THE SHARP `p | q` DEFICIT.  `primeDivSum_le_modulus`'s
-- crude `q` (ω(q) ≤ q+1, each 1/p ≤ 1/2) replaced by the in-kernel sharp Mertens-2
-- (`Salt.Mertens.mertens_second_sharp_real`) at `t = q`: `loglog q + M + 12/log q`.  Every
-- statement is a SIBLING — the landed `capFreeFloor3`-family is byte-untouched; the `_sharp`
-- forms carry the same conclusions under a threshold whose `(1/4)·q` summand is
-- `(1/4)·mertensCap q`.  At the door's range `q ≤ (log H)^12` this turns an EXPONENTIAL
-- demand `8·exp(12·loglog H)` on `loglog X` into `8·log(12·loglog H) + O(1)`.
-- (`vkMidDebit q` is carried symbolically here; ⟦VT-7⟧ below replaces it.)
open Salt.Tactic in
#audit_axioms Salt.MR.primeDivSum_le_loglog
  Salt.MR.primeDivSum_max_le_mertensCap
  Salt.MR.mertensCap_nonneg
  Salt.MR.primeDivSum_le_mertensCap
  Salt.MR.mertensCap_le_of_le
  Salt.MR.chi_floor_real_bulk_sharp
  Salt.MR.capFreeFloor3_all_chi_sharp
  Salt.MR.capFreeFloor_all_chi_sharp
  Salt.MR.cffKSharp_nonneg
  Salt.MR.cffKSharp_spec
  Salt.MR.capFreeFloor3_liouChi_all_sharp
  Salt.MR.capFreeFloor3_margin_all_chi_sharp
  Salt.MR.capFreeFloor3_pieceDatum_sharp

-- ⟦VT-7⟧ (`VkMidSharp`, 2026-07-29) — THE `e^{e^100}` BLOCK, KILLED.  The mid frequency branch
-- (`VkTwistClose.chi_Llower_341_height`) priced its growth slot by
-- `ChiLLower.LFunction_norm_le_level`, LINEAR in `‖s‖`, so at the socket's floor
-- `T₀ = exp(exp 100)` it paid
-- `(1/4)·log(3(3+2T₀)q²(1+log q)) ≈ (1/4)·e^100` — an `X`-free `32·vkMidDebit q ≈ 2.15·10^44`
-- demand on `loglog X`.  `norm_LFunction_le_logBound` supplies the classical LOG-shaped bound
-- `‖L(s,ψ)‖ ≤ 7/2 + log 2 + log q + log(|Im s| + 2)` on `1 < Re s ≤ 2` instead — truncation at
-- `N = ⌈q(|t|+2)⌉` through the landed `Salt.SW.norm_LFunction_sub_partial_le`, with the level-`q`
-- character-sum bound `M = q` (`norm_char_partial_sum_le`) whose `q` cancels against `N`'s.
-- The block becomes `32·vkMidDebitSharp q ≈ 905`, and the threshold's `q`-coefficient drops from
-- `28·log q` to `12·log q` (the old `q²` sat OUTSIDE the outer log, the new `log q` INSIDE it).
-- SIBLING-ADDITIVE: `vkMidDebit`, `chi_Llower_341_height`, `chi_floor_vk_pointwise` and the whole
-- ⟦F4⟧ `_sharp` family are byte-untouched; the `_vt` family below is the SINGLE combined
-- threshold carrying BOTH repairs, conclusions byte-identical to the landed originals.
open Salt.Tactic in
#audit_axioms Salt.MR.norm_char_partial_sum_le
  Salt.MR.norm_LFunction_le_logBound
  Salt.MR.chi_Llower_341_height_sharp
  Salt.MR.vkMidDebitSharp_nonneg
  Salt.MR.chi_floor_vk_pointwise_sharp
  Salt.MR.capFreeFloor3_lamChi_vk_sharp
  Salt.MR.capFreeFloor3_lamChi_unconditional_sharp
  Salt.MR.capFreeFloor3_all_chi_vt
  Salt.MR.capFreeFloor_all_chi_vt
  Salt.MR.cffKVt_nonneg
  Salt.MR.cffKVt_spec
  Salt.MR.capFreeFloor3_liouChi_all_vt
  Salt.MR.capFreeFloor3_margin_all_chi_vt
  Salt.MR.capFreeFloor3_pieceDatum_vt

-- ⟦WAVE ① — THE SPLIT TWINS⟧ (2026-07-29, second-road freeze v2 RATIFIED;
-- `docs/exploration/second-road-freeze-0729.md`).  The M4/S9 road re-cut against the budget
-- head's OWN constant `δ₀`.  `log_chowla_two_budget_head_g` binds `δ₀` in its `∃`-prefix,
-- BEFORE `∀ extraFloor U1floor g`, and then opens `∀ δ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ
-- → ¬ logChowla2Fails`.  The landed road fires that quantifier at the DECAYING grade
-- `doorGrade R.Hlo` and pays for the descent (the pin, the `C_MRT` gate, `mrtDeliveredGrade ≤
-- doorGrade`); the split road fires it at `δ := δ₀` itself (`le_rfl`), which is legal exactly
-- because `δ₀` precedes the regime — so the decaying-grade machinery is BYPASSED, not
-- repaired.  SIBLING-ADDITIVE: every landed statement above is byte-untouched; the family's
-- contract is `M4Exit` §7.  ⟦NATURALLY RETIRED — no twins⟧ the whole mrtGate/H0scale block
-- (`mrtDeliveredGrade`, `mrtGate`, `H0scale`, `mrtGate_transfer`,
-- `mrtDeliveredGrade_le_doorGrade`, `absWindowBound_le_pin`), the `H0door δ₀` extraFloor
-- demand and `doorGrade_regime_pin` (at `δ := δ₀` the pin is `le_rfl` — THE byte the split
-- exists to remove), `m4Saving`'s `sqrt_m4Saving_le_delivered` margin, and
-- `m4_gradeGate_direct_of_sq`.  ⟦THE `_False` FAMILY IS RETIRED⟧ by JYH ruling — the five
-- collision forms stay landed and get NO twins; the S11 spine consumes the `¬`-form, which is
-- what every `_split` twin delivers.  ⟦THE C-BINDER RULE⟧ the `∀ (C : ℝ), 0 ≤ C →` (or
-- `2 ≤ C`) binder exists ONLY to feed `mrtGate`/`H0scale` and is ABSENT from every twin;
-- preserving it would re-import the decaying grade.  Binder-list law: the original's, minus
-- `C`, with every grade hypothesis re-stated at `δ₀` (`Cg` — the door glue's constant, not
-- `C_MRT` — is kept).  ⟦UNTOUCHABLE⟧ `M4DoorGates` and its `hMδ : 24·Cg/δ ≤ M` are consumed
-- unchanged; post-split `hMδ` reads at a constant-scale `δ` (the freeze's "defused at the
-- constant"), by design.  ⟦THE RATIFIED TARGET REGISTER⟧ is D-1 option (b),
-- `m4_wave_exit_sup_split`: its item 6′ (`M4BlockMeanSqSup`) is `q`-free and the `q`-free
-- dock's whole cover side is landed, so the class machinery lives in the supply chain and
-- never in the register; its drift-price line (item 4′) is carried at the LANDED SHAPE and is
-- wave ④'s to re-cut into the composed blocked-drift × stratified-Gauss × χ-summed form.
-- `m4_wave_exit_split` (plain α), `m4_wave_closed_split`/`_of_chi_split` (the class road,
-- which hard-wires `q²` in its drift conjunct — the reason D-1 chose the sup shape) and
-- `m4_wave_closed_of_dyadicRow_split` (the row-level host, adopting its own graded shape
-- `m4BclGraded j₀ (2·MSan) (2·MStr)` verbatim, ⟦R1⟧ still EXECUTED) stand beside it.
-- `m4_gradeGate_direct_split` is the CRITICAL-PATH step: the budget-line discharge every
-- register above the block level routes through
open Salt.Tactic in
#audit_axioms Salt.MR.m4_exit_of_hbd_split
  Salt.MR.m4_exit_socket_split
  Salt.MR.M4GradeGateSplit
  Salt.MR.m4_gradeGate_of_pricing_split
  Salt.MR.m4_hbd_of_live_split
  Salt.MR.m4_door_contradiction_of_live_split
  Salt.MR.m4_gradeGate_of_block_pricing_split
  Salt.MR.m4_door_contradiction_of_blockMeanSq_split
  Salt.MR.m4_gradeGate_direct_split
  Salt.MR.m4_wave_gradeGate_split
  Salt.MR.m4_wave_exit_split
  Salt.MR.m4_wave_exit_sup_split
  Salt.MR.m4_wave_closed_split
  Salt.MR.m4_wave_closed_of_chi_split
  Salt.MR.m4_wave_closed_of_dyadicRow_split

-- ⟦WAVE ③ — F3, THE BLOCKED DRIFT⟧ (2026-07-29, second-road freeze v2; `M4BridgeBlock`).
-- `M4BridgePhase`'s drift line (`norm_absWindowSum_le_drift`, `:291`) prices the phase
-- `e(αn)` over the WHOLE window and pays `(1 + 2π·arcDen 12 H/q)²` into the socket — factor
-- `F3` of ⟦DRIFT-SCOPE⟧'s four-factor wall.  Blocked at the drift's own length
-- `ℓ ≈ q·H/arcDen 12 H` the per-block drift is the ABSOLUTE `1 + 2π`, and the block count
-- `N = numBlocks H ℓ` enters once through Cauchy–Schwarz over blocks; composed with a
-- per-block supply normalised at `ℓ²` the two `N`s and the `ℓ²` reassemble `(N·ℓ)² ≤ 4H²`
-- (`numBlocks_mul_le`), so the blocking is loss-free up to the absolute factor `4` and the
-- assembled price is `4·(1+2π)²·Bblk H` — NO `arcDen`, NO `q`.  ⟦THE ③×④ INTERFACE⟧ the
-- socket wave ④ consumes is `M4SievedDoorSqBlk R M ℓ Bblk`:
-- `∫ ∑_{m<N} (subWindowSup a ℓ (n + m·ℓ) (b/q))² dμ ≤ Bblk H · N · ℓ²`, under the binders
-- `1 ≤ ℓ H q`, `ℓ H q ≤ H`, `H ≤ arcDen 12 H · ℓ H q`; `m4_sievedDoorSq_of_blk` exits at
-- `M4Close.M4SievedDoorSq`.  ⟦THE `q`-DEPENDENCE OF `ℓ` IS FORCED — co-design finding⟧ the
-- brief's two binders are jointly unsatisfiable for a `q`-UNIFORM `ℓ`: `NearRatTight` may
-- hand out `q = 1`, where the drift binder `arcDen·ℓ ≤ q·H` and the count binder
-- `H ≤ arcDen·ℓ` force `arcDen 12 H · ℓ = H` exactly.  Hence `ℓ : ℕ → ℕ → ℕ` and the
-- theorem-level obligation `arcDen 12 H · ℓ H q ≤ q·H` (④ owns the witness; the legal
-- interval `H/arcDen ≤ ℓ H q ≤ q·H/arcDen` is nonempty for every `q ≥ 1`).  ⟦K-FREE⟧ the
-- sup over sub-window lengths stays inside `subWindowSup` at cap `ℓ`; no statement carries a
-- `K`, and the partial last block is absorbed by the block-sup (`subWindowSup_mono_length`)
-- — `M4BridgeIntegral`'s overhang ledger is NOT needed and NOT cited.  ⟦F3 STANDALONE IS
-- WORTHLESS⟧ (D1-SCOPE, law): this file supplies one factor of a composition ④ owns.
-- SIBLING-ADDITIVE: one new file, no landed statement touched.
open Salt.Tactic in
#audit_axioms Salt.MR.numBlocks
  Salt.MR.le_numBlocks_mul
  Salt.MR.numBlocks_mul_le
  Salt.MR.mul_le_of_lt_numBlocks
  Salt.MR.blockCut
  Salt.MR.blockCut_eq_of_lt
  Salt.MR.blockCut_numBlocks
  Salt.MR.blockCut_mono
  Salt.MR.blockCut_succ_sub_le
  Salt.MR.sum_Ioc_chunk
  Salt.MR.subWindowSup_mono_length
  Salt.MR.abs_mul_window_le_of_arcDen_block
  Salt.MR.norm_block_phase_sum_le
  Salt.MR.norm_absWindowSum_le_drift_blocked
  Salt.MR.norm_absWindowSum_sq_le_drift_blocked
  Salt.MR.blockSupSq
  Salt.MR.blockSupSq_nonneg
  Salt.MR.blockSupSq_le_of_norm_le_one
  Salt.MR.M4SievedDoorSqBlk
  Salt.MR.m4_sievedDoorSq_of_blk
  Salt.MR.m4_sievedDoorSqBlk_trivial
  Salt.MR.M4BlockMeanSqBlk
  Salt.MR.m4_cover_assembly_blk
  Salt.MR.m4_blockMeanSqBlk_trivial
  Salt.MR.blockBase_mem_doorLadder_block
  Salt.MR.blockBase_le_two_mul

-- ⟦WAVE ④ — THE COMPOSED SUPPLY CHAIN AND THE SECOND ROAD'S REGISTER⟧ (2026-07-29,
-- second-road freeze v2 D-2/D-3/D-1(b); `M4ChiSummed`, `M4Gauss`, `M4SecondRoad`).
--
-- ⟦S-1 THE SOCKET⟧ `M4ChiSummedFreeRow R M RS` is ⟦REF-SHAPE A-C1⟧'s replacement for the
-- freeze-v1 socket that had NO instances at any stratum `d ≥ 2`: a FREE base `A` and shift
-- `s ≤ L`, CAP-GENERAL `∀ L ≤ H`, WINDOW-DYADIC `2^j`, EVERY modulus `0 < q ≤ arcDen 12 H`,
-- `RS` `q`-FREE, and the SUM over `χ : DirichletCharacter ℂ q` of the row mean squares
-- `chiFreeRowSq` of `doorChiCoeff χ M` at the `seamS0` windows.  Anti-vacuity at
-- `RS j H := 4·arcDen 12 H` (`doorRow_trivial_grade`'s absolute `4` times `φ(q) ≤ q ≤ arcDen`)
-- — `q`-free, as the socket demands.  ⟦WHY `Σ_χ`⟧ a per-χ socket re-imports a factor `φ(q)`
-- at the Gauss step; the χ-SUM is what makes the composition `O(1)`.
--
-- ⟦R-P5 / THE KMT PORT'S x-SCALE LADDER — wave P-1, 2026-07-29⟧ all three predicates of the
-- chain now quantify their base under THREE ANTECEDENTS: `2^j ≤ A` (`L ≤ A` at the block
-- form), `√H ≤ A`, and `R.x ≤ 16·R.ω·arcDen 12 H·A`.  The port's supply ladder needs
-- `loglog A ≳ 285`, unreachable at the `H`-scale without breaking the ruled `2³⁶` gate-8
-- sandwich; the socket's bases ARE door-ladder rungs, so the socket CARRIES that fact.  They
-- only WEAKEN the socket — every anti-vacuity witness discharges the new binders trivially,
-- `m4_second_road`'s ⟦item 11⟧ line gains NOTHING (the antecedents live in the socket's own
-- `∀`-prefix), the register gains no conjunct and no gate, and the port adds ZERO `H`-demand.
-- Supply side: `doorLadder_ge_x_div_four_omega` (`M4Collapse.doorLadder_pow_lower` composed
-- with `two_pow_le_four_mul_of_count`, i.e. `M4DoorGates.hcount`'s `2^k ≤ 4ω`) plus the
-- regime's wave-II headroom `8·H₊·log²H₊ ≤ ⌊x/ω⌋` — NO new regime field, NO `g`-arm movement.
-- `M4Gauss`'s stratified consumer swaps its crude base floor `32·arcDen ≤ A` for `2H ≤ A` and
-- `R.x ≤ 8·R.ω·A` and re-derives all three at the DILATED base `⌊A/d⌋ − 1` by the `hcapnar`
-- pattern (`capL_le_dilated_base`, `le_mul_div_add`) — the ONE `arcDen` cushion on the
-- x-antecedent is the honest price of that dilation, already recorded at `M4BaseNarrow`'s
-- header, and costs nothing at `loglog` since `R.x` is the consumer's own via the `g`-arm.
-- The one shape change: the fallback bridge to the per-χ family is now POINTWISE
-- (`chiFreeRowSq_le_of_chiSummed`), since the landed un-antecedented predicate
-- `M4ChiFreeRowMeanSq` cannot carry base antecedents.  Nothing consumes it.
--
-- ⟦S-2 THE MIRRORS⟧ the landed free-base chain re-run POINTWISE-IN-χ then summed:
-- `chiFreeShift_pointwise` (⟦W3⟧ at a per-χ constant) → `m4_chiSummedShiftBlock_of_freeRow`
-- → `m4_chiSummedBlockN_of_shiftBlock` (⟦W4⟧'s dyadic assembly at the summed integrand) →
-- `m4_chiSummedN_supplied`.  Every step IS genuinely pointwise-in-χ — no cross-χ coupling
-- anywhere (the freeze's spot-check answered).  ⟦THE φ(q) LEDGER⟧ the two ABSOLUTE-grade
-- charges (the drop residue `8·(2^j)²` and the trivial half `A·(2^j)²` at `j < j₀`) read no
-- row datum, so under `∑_χ` they cost `φ(q) ≤ arcDen 12 H`; both are carried at `arcDen`
-- (never at `q`, so the predicates stay `q`-free), which raises ⟦G1⟧ from `arcDen²` to
-- `arcDen⁷` — a threshold on the WITNESSED envelope `RStr`, not a saving.
--
-- ⟦S-3 THE STRATIFIED GAUSS CONSUMER⟧ `sum_normSq_chiGaussSum`: `∑_χ ‖τ_b(χ)‖² = φ(q)²`
-- EXACTLY, at EVERY `b : ℤ` (no coprimality on `b`, no primitivity, no `√q` — the double sum
-- with the unit-indicator collapse).  `norm_sq_coprime_window_le`: the coprime part of the
-- window at `b/q`, squared, is under `∑_χ (doorChiSup χ)²` at PREFACTOR `1` — the `φ(q)²`
-- cancels the expansion's `1/φ(q)²`.  **This is where ⟦F2⟧'s `q²` dies.**
-- `stratum_sq_le_chiSummed`: one stratum `d = gcd(r,q)`, re-indexed (`sum_fibre_eq_coprime`)
-- and dilated ONE step (`class_rat_dilate`, the landed `classWindowSum_dilate` +
-- `absWindowSum_dilCoeff_memS_door`), priced against its OWN cap `capL L d` — the
-- TRUNCATION-READY shape wave ⑤'s `D₀` cut needs.  `subWindowSup_sq_le_strata` recombines by
-- the WEIGHTED Cauchy–Schwarz at `1/d`, which spends `M4NonCoprime.d0_ledger_sharp`'s banked
-- `1/d²`; the residual is `(∑_{d ∣ q} 1/d)² ≤ (1 + log arcDen 12 H)²` (`sum_inv_divisors_le`,
-- the harmonic bound) — `H`-only, `loglog`-scale, and the ONLY `q`-trace on the whole road.
-- `m4_freeBlockSup_of_chiSummed` is the block form.
--
-- ⟦S-4 THE REGISTER⟧ ⟦THE q = 1 PINCH — a co-design finding that KILLS the landed socket's
-- consumer⟧ wave ③'s four `hℓ` obligations are JOINTLY UNSATISFIABLE: at `q = 1` the count
-- binder `H ≤ arcDen·ℓ` and the drift binder `arcDen·ℓ ≤ q·H` force `arcDen 12 H · ℓ = H`
-- exactly, which no natural number does for generic `H` — the `q`-dependence of `ℓ` buys
-- nothing at that corner.  ⟦THE REPAIR⟧ the count binder is a NARROWING handed TO the supply,
-- so weakening it to `H ≤ arcDen²·ℓ` (the whole S-2/S-3 chain is stated there) opens the
-- admissible interval `[H/arcDen², H/arcDen]` — ratio `arcDen ≥ e^{12}` — and the witness
-- `blockLen H q := max 1 (H / (⌊arcDen 12 H⌋₊ + 1))` is then even `q`-UNIFORM.
-- `M4SievedDoorSqBlk2`/`m4_sievedDoorSq_of_blk2`/`m4_cover_assembly_blk2` are `M4BridgeBlock`
-- §3/§4 re-cut at the weakened binder (the socket never USES the count binder — it only
-- hands it on), everything else consumed verbatim.  `m4_second_road` is the terminal
-- register: `M4DoorGates` unchanged (`hMδ` included), the analytic slot is the S-1 socket,
-- the drift line is the COMPOSED `96(1+2π)²·(1 + log arcDen)²·m4BclGraded j₀ (2RSan) (2RStr)`
-- — no `arcDen` power, no `q`, no `q²` — and the conclusion `¬ logChowla2Fails R.eps R.x R.ω`
-- is BYTE-IDENTICAL to the landed one.  ⟦THE GATE CENSUS⟧ eleven items, each witnessed,
-- consumer data, or regime-absorbable (one-sided, `H`-only): the window floor
-- `128·arcDen³ ≤ H`, ⟦G1⟧ `arcDen⁷ ≤ RStr`, ⟦G2⟧ `44·RSan + 87·arcDen ≤ (4/3)^{j₀}`, and the
-- `M`-RELATIVE dilation gate `arcDen < calP (Adoor M) (3072M) 1`.  ⟦F5 / WALL C CLEAR⟧ there
-- is NO `H`-upper and NO `X`-upper anywhere in the register, and the retired numeral
-- `log H ≤ 2^{21845}` is never demanded — every dilation routes through the `M`-relative
-- gate.  ⟦NOT RE-CUT IN PLACE⟧ `M4Join.m4_wave_exit_sup_split` is left BYTE-UNCHANGED: it
-- sits below `M4ClassPrice` in the import graph, six levels under the supply chain, so the
-- composed conjunct cannot be stated there.
open Salt.Tactic in
#audit_axioms Salt.MR.chiFreeRowSq
  Salt.MR.chiFreeRowSq_le_four
  Salt.MR.M4ChiSummedFreeRow
  Salt.MR.m4_chiSummedFreeRow_trivial
  Salt.MR.chiFreeRowSq_le_of_chiSummed
  Salt.MR.chiFreeShift_pointwise
  Salt.MR.M4ChiSummedFreeShiftBlock
  Salt.MR.m4_chiSummedShiftBlock_trivial
  Salt.MR.m4_chiSummedShiftBlock_of_freeRow
  Salt.MR.M4ChiSummedBlockMeanSqN
  Salt.MR.m4_chiSummedBlockN_trivial
  Salt.MR.m4_chiSummedBlockN_of_shiftBlock
  Salt.MR.m4_chiSummedN_supplied
  Salt.MR.chiGaussSum
  Salt.MR.sum_normSq_chiGaussSum
  Salt.MR.coprime_window_expansion
  Salt.MR.norm_sq_inv_totient_gauss_le
  Salt.MR.norm_sq_coprime_window_le
  Salt.MR.sum_fibre_eq_coprime
  Salt.MR.ratPhase_dilate
  Salt.MR.class_rat_dilate
  Salt.MR.stratum_sq_le_chiSummed
  Salt.MR.capL
  Salt.MR.capL_ledger
  Salt.MR.strataTerm
  Salt.MR.subWindowSup_sq_le_strata
  Salt.MR.sum_inv_divisors_le
  Salt.MR.strataResidual
  Salt.MR.capL_le_dilated_base
  Salt.MR.le_mul_div_add
  Salt.MR.m4_freeBlockSup_of_chiSummed
  Salt.MR.four_le_arcDen_of_regime
  Salt.MR.blockLen
  Salt.MR.blockLen_drift
  Salt.MR.blockLen_narrow
  Salt.MR.blockLen_arc_floor
  Salt.MR.M4SievedDoorSqBlk2
  Salt.MR.m4_sievedDoorSq_of_blk2
  Salt.MR.M4BlockMeanSqBlk2
  Salt.MR.m4_cover_assembly_blk2
  Salt.MR.two_pow_le_four_mul_of_count
  Salt.MR.doorLadder_ge_x_div_four_omega
  Salt.MR.m4_blockMeanSqBlk2_of_chiSummed
  Salt.MR.m4_second_road

-- ⟦WAVE ⑤ — THE D₀-TRUNCATION TEST (REFUTED) AND THE PRICING AUDIT⟧ (2026-07-29,
-- second-road freeze v2 D-6 / ⟦REF-SAND A-6⟧ / ⟦D0-TEST SITE A⟧; `M4Gauss`, `M4SecondRoad`).
--
-- ⟦THE TEST⟧ wave ⑤'s first item was the `D₀`-truncation: take the strata `d > D₀` by the
-- landed GATE-FREE trivial bound and collapse ⟦gate 8⟧ from `arcDen 12 H` to an ABSOLUTE
-- `D₀ = 2/√Bblk ≈ 1.4·10⁵¹`, dissolving the door-anchor sandwich with no `DoorFrame` re-pin.
-- ⟦THE VERDICT: REFUTED — structurally, not arithmetically.⟧  At one stratum `d ∣ q` over a
-- block `(A,B]` with `B−A ≤ A`, the analytic side gives `∑ₙ strataTerm_d ≤ Bcl·(L+d)²·A/d²`
-- and the trivial side `∑ₙ (L/d+1)² ≈ L²A/d²`: **the `1/d²` scaling is IDENTICAL**, because
-- the χ-summed supply is read at the stratum's OWN dilated cap `capL L d ≈ L/d` and its own
-- re-indexed block `⌊A/d⌋`.  The trivial branch is worse by `1/Bcl` at EVERY `d`; there is no
-- `d` at which it becomes competitive.  ⟦WHY⟧ the `1/d²` is `M4NonCoprime.d0_ledger_sharp`,
-- and `M4Gauss` §5 SPENDS it: the weighted Cauchy–Schwarz at `1/d` is what converts the
-- strata recombination's cost from `τ(q)²` (a positive power of `log H` — fatal by the
-- residual law) into the loglog-scale `(1 + log arcDen)²`.  **The weighted recombination and
-- the `D₀`-truncation are mutually exclusive: each needs the same ledger.**  Wave ④'s
-- per-stratum granularity is preserved exactly as ⟦D0-TEST⟧ steered and is NOT the binding
-- constraint.  ⟦WHAT `D₀` IS STILL WORTH⟧ only the divisor tail `∑_{d∣q,d>D₀} 1/d ≤ q/(2D₀²)`
-- (complementary divisors, τ-free), forcing `log₂ D₀ ≈ 6·log₂ log H + 169` — HALF ⟦gate 8⟧'s
-- own exponent, i.e. ONE anchor bit (⟦SANDWICH-REF⟧: ×1.96 per bit); Wigert's τ-bound would
-- buy 5–6 bits, not the 16 that `2^18 → 2^34` needs — and in every case `D₀` carries `arcDen`
-- so ⟦gate 8⟧ does not become `H`-free.  ⟦D0-TEST⟧'s banked "DISSOLVED ×3.9e4, log₂D₀ ∝
-- ln lnln Hhi" does not reproduce.  **⟦gate 8⟧ STANDS; the anchor ask returns to JYH.**
--
-- ⟦WHAT LANDED⟧ (1) the gate moved to `d`: `class_rat_dilate`/`stratum_sq_le_chiSummed` now
-- read `(gcd r q : ℝ) ≤ W` / `(d : ℝ) ≤ W` instead of `(q : ℝ) ≤ W` — ⟦D0-TEST⟧'s structural
-- fact (`q`, `W` are pure intermediates of the door side; nothing occurs in the conclusion),
-- a strictly weaker hypothesis every landed caller supplies, and the interface any future
-- truncation needs; (2) `truncBudget`/`truncD` — the `(Cg,δ₀)`-ONLY ceiling (no `H`, no `q`,
-- no `X`, no `M`) with `truncD_admissible`, the SITE-A per-stratum admissibility
-- `(L/d+1)² ≤ truncBudget δ₀·L²` proved with honest ±1 arithmetic (the `2` in the numerator
-- buys one half for the quotient and one for the `+1`; length-invariant, so the same `D₀`
-- serves `H`, `ℓ` and `H/d`), and `stratum_sq_le_chiSummed_at_truncD`, the zero-byte
-- instantiation of the door gate at `D₀`; (3) ⟦THE PRICING AUDIT⟧ `rStrWitness`/`rSanWitness`
-- witness gates 3/5 (`max 1 (·)` is what makes the OFF-RANGE `∀ H, 0 ≤ ·` hold),
-- `g2_of_j0_floor` discharges ⟦G2⟧ from `j₀ ≳ 22 + 48·loglog H` via `log(4/3) ≥ 1/4` — ⟦G2⟧
-- is an `H`-UPPER in disguise but slacker than ⟦gate 8⟧ by `0.415·M ≈ 8·10⁶¹`, so it is
-- non-binding while ⟦gate 8⟧ stands; and `m4_second_road_rs_ceiling` composes ⟦item 9⟧ with
-- ⟦item 10⟧ into **the number the port gate quotes**:
-- `96(1+2π)²·(1+log arcDen)²·(108/5)·RSan H ≤ δ₀²`, i.e. `RSan H ≲ 2.5·10⁻¹⁰⁵/(loglog H)²`
-- at `δ₀ = 2e-49` — a CONSTANT times `(loglog H)^{-2}`, inside ⟦D1-SCOPE⟧'s residual law and
-- far weaker than KMT's own `(log H)^{-1/200}`.  ⟦F5 RE-GREP⟧ clean: `R.x` occurs in the
-- register only as the `X`-LOWER `g R.Hhi R.ω ≤ R.x`; no `X`-upper anywhere.
open Salt.Tactic in
#audit_axioms Salt.MR.truncBudget
  Salt.MR.truncBudget_pos
  Salt.MR.truncD
  Salt.MR.truncD_ge
  Salt.MR.truncD_admissible
  Salt.MR.stratum_sq_le_chiSummed_at_truncD
  Salt.MR.rStrWitness
  Salt.MR.rStrWitness_nonneg
  Salt.MR.rStrWitness_G1
  Salt.MR.rSanWitness
  Salt.MR.rSanWitness_nonneg
  Salt.MR.rSanWitness_envelope
  Salt.MR.g2_of_j0_floor
  Salt.MR.m4_second_road_rs_ceiling

-- ⟦THE B-PROBE (P-0′) — THE KMT PORT'S GO/NO-GO⟧ (2026-07-29, port freeze v2 wave P-0′;
-- `VkTwistRegionProbe`).  KR-1 asked whether ζ's VK-width growth→region bridge
-- (`Salt.Vk.zeta_zero_free_region_pow_of_growth`, width `c/((log t)^{3/4}(loglog t)³)`) runs for
-- `L(s,χ)`, whose Borel–Carathéodory leg was feared to be anchored at ζ's POLE.  ⟦VERDICT: GO.⟧
-- The fear was a misdiagnosis: ζ's `Zc = (s−1)ζ` normalization exists to make the base ENTIRE
-- for `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` (paying a `Re(1/(s−1))` correction in every
-- leg), NOT to exploit the pole.  `L(·,χ)` for `χ ≠ 1` is already entire, so the `Zc` apparatus
-- and both corrections VANISH; the disc's reference floor is the twisted Möbius series
-- (`norm_LFunction_inv_cline_le`: `‖L(σ+it,χ)⁻¹‖ ≤ 1 + 1/(σ−1)`, mirror of the landed
-- `Salt.SW.norm_zeta_inv_cline_le`), and ζ's pole survives only in the 3-4-1's FIRST factor
-- `ζ(σ)³` at real `σ`, which is character-free.  The chain's `8` becomes `3`, and the assembly
-- needs NO height hypothesis (ζ needed `1 ≤ |Im ρ|` only for the two corrections).
--
-- ⟦KR-2 RECONCILED⟧ `LFunction_zero_free_width_law` isolates the law:
-- **width `= Θ/(14(8Θ + 700·log(20M/Θ)))`** — the strip HALF-WIDTH over a log of the
-- growth-to-width ratio.  So the twisted Fourier completion's `q^{3/2}(1+log q)` (inside `M`)
-- reaches the width only through `log`, i.e. as an additive `(3/2)log q`; the `3/4` exponent
-- comes from `Θ` alone.  `LFunction_zero_free_region_vk_shape` instantiates at `Θ = vkTheta 3γ`
-- and `M = Cq·(log 3γ)^{3/4}(loglog 3γ)⁴`, giving ζ's shape with a constant linear in the
-- `q`-scale grade `A` (`log(20000 Cq) ≤ A·loglog Im ρ`): at `q ≤ (log H)^12`, `A ≈ 18`,
-- `c ≈ 1/(2.3·10⁹)` against ζ's own `1/10⁹`.
--
-- ⟦CONDITIONAL BY DESIGN⟧ the strip growth (stone A) is a HYPOTHESIS throughout (`hgrowth`,
-- `hgrowth2` — for `χ` and for `χ²`, both mod `q`).  Open to stone B proper: the `χ² = 1` arm,
-- the height floor (here ζ's own `1100 ≤ loglog Im ρ`), the Siegel/carve-out fold.
open Salt.Tactic in
#audit_axioms Salt.MR.norm_LFunction_inv_cline_le
  Salt.MR.LFunction_ratio_bound
  Salt.MR.LFunction_keep_one_disc
  Salt.MR.LFunction_drop_all_disc
  Salt.MR.LFunction_zero_free_of_disc
  Salt.MR.LFunction_region_of_uniform_growth
  Salt.MR.LFunction_zero_free_width_law
  Salt.MR.LFunction_zero_free_region_vk_shape

-- ⟦WAVE P-2 — THE HYBRID LARGE SIEVE FOR CHARACTERS (KMT Lemma 6.2)⟧ (2026-07-29, port
-- freeze v2 wave P-2; `MVHilbertFinset` / `CharFold` / `HybridMVT`).  Four stages, all
-- ADDITIVE (the landed `L2MVT` / `MVHilbert` / `MVCore2` / `LS.CharLS` untouched):
--
-- ⟦S1 THE AP GAP⟧ `log_gap_ge_of_modEq`: distinct `m, n ∈ [1,N]` with `m ≡ n [MOD q]` have
-- `q/N ≤ |log m − log n|` — the `q`-fold sharpening of `log_gap_ge`, sharp (`n − m = q`
-- attained), NO coprimality needed.  ⟦S2 THE FINSET RE-CUT⟧ the landed MVT assembly
-- generalized from `Icc 1 N` to an arbitrary `s : Finset ℕ` with a *parameter* separation
-- `δ`: `dpolyS_l2_mvt_final : ∫_{-T}^{T}‖∑_{n∈s} aₙ n^{it}‖² ≤ (2T + 2π/δ)·∑_{n∈s}‖aₙ‖²`.
-- The Montgomery–Vaughan core is CONSUMED VERBATIM — `MVHilbertUniform` was already stated
-- at an arbitrary `Finset ℕ` with arbitrary real frequencies, so `mvHilbertUniform_holds`
-- (MVCore2) applies unchanged; `offdiag_term_hilbert` likewise (index-set agnostic).
-- ⟦R-P3's MANDATE⟧ the re-cut is not cosmetic: running the MVT on `Icc 1 N` and only then
-- splitting by class pays `φ(q)·2πN` — a factor `q` above the target.  The `1/q` is bought
-- by the per-class separation and is NOT droppable (unlike the `φ(q)/q`, whose loss costs
-- only a logloglog).  ⟦S3 THE ALL-χ FOLD⟧ `char_plancherel` extracts `CharLS`'s
-- proof-internal Plancherel chain (lines 88–178) as a standalone lemma over an arbitrary
-- `S : ZMod q → ℂ`: `∑_{χ mod q}‖∑_b χ(b)S(b)‖² = φ(q)·∑_{b unit}‖S b‖²` — ALL `φ(q)`
-- characters, principal and imprimitive included (no primitivity filter: that belongs to
-- the Gauss-sum argument, not here).  Plus the reindex bridge `dpolyChi_eq_class_sum`
-- (χ(n) = 0 at non-units handles coprimality for free) and the integrability plumbing
-- (`sum_chi_meanSq_fold`: the symmetric-window integral passes through both finite sums).
--
-- ⟦S4 THE ASSEMBLY⟧ `hybrid_char_mvt` — for `s ⊆ Icc 1 N`:
--   `∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n∈s} aₙ·χ(n)·n^{it}‖² dt`
--     `≤ (2·φ(q)·T + 7·φ(q)·N/q) · ∑_{n∈s, (n,q)=1} ‖aₙ‖²`.
-- ⟦THE CONSTANT IS 7, NOT 13⟧ the refuter priced the off-diagonal at `4π ≤ 13` from
-- `δ = q/(2N)`; S1 is sharp at `δ = q/N`, so the off-diagonal pays `2π ≤ 7` — the sharp
-- form, for free.  The `2` on the diagonal is exact (the two half-ranges of `[-T,T]`).
-- The RHS mass is the SHARP coprime-filtered one (`hybrid_char_mvt_full` weakens it to all
-- of `s` when a caller wants the crude form; needs `0 ≤ T`).  ⟦CATCH #B DISCHARGED⟧ the
-- statement is at `n^{+it}` (KMT's convention); `dpolyS_meanSq_reflect` shows the mean
-- square over the symmetric window is `t ↦ −t` invariant, so the corpus's `P(1−it)`
-- callers cost nothing.
open Salt.Tactic in
#audit_axioms Salt.MR.log_gap_ge_of_modEq
  Salt.MR.dpolyS_l2_expand
  Salt.MR.dpolyS_l2_diagonal
  Salt.MR.offdiag_eq_hilbertS
  Salt.MR.norm_hilbertLogSumS_le
  Salt.MR.dpolyS_l2_mvt
  Salt.MR.dpolyS_l2_mvt_final
  Salt.MR.dpolyS_meanSq_reflect
  Salt.MR.char_plancherel
  Salt.MR.dpolyChi_eq_class_sum
  Salt.MR.sum_chi_meanSq_pointwise
  Salt.MR.sum_chi_meanSq_fold
  Salt.MR.classSet_meanSq_le
  Salt.MR.sum_unitClass_mass
  Salt.MR.hybrid_char_mvt
  Salt.MR.hybrid_char_mvt_full

-- ⟦O3 — THE TWISTED μ→λ BRIDGE⟧ (2026-07-29, KMT port wave P-1; `LambdaRateTwisted`).
--
-- The χ,t-twisted version of the landed `Salt.TwinBar.LambdaRate` chain, i.e. obligation O3
-- of the port freeze (`docs/exploration/port-freeze-0729.md` §3): "the χ,t-twisted bridge,
-- mechanical — complete multiplicativity distributes over the convolution".  It is now
-- landed, and the "mechanical" reading held.
--
-- ⟦THE GENERAL LAW, NEW⟧ mathlib has `pmul`, `pmul_apply`, `pmul_comm/assoc`,
-- `IsMultiplicative.pmul` — but NO law relating `pmul` to the Dirichlet convolution `*`, and
-- no `IsCompletelyMultiplicative` predicate at all.  So the law is stated here:
-- `mul_apply_mul_twist` / `pmul_mul_of_twist` — `(f ∗ g)·h = (f·h) ∗ (g·h)` for any `h`
-- multiplicative on nonzero pairs, a `Finset` rearrangement over `divisorsAntidiagonal`.
--
-- ⟦THE DATUM⟧ `chiBarTwist χ t n := conj (χ n) · exp (i·t·log n)` — χ BARRED, per the corpus
-- (`ChiFloor.lean`'s `lamChi χ n = lam n · conj (χ n)`); KMT writes `χ(n)` unbarred.  The name
-- is `chiBarTwist` and not `chiTwist` because `Salt.MR.chiTwist` is already taken by
-- `ChiEuler.lean`'s UNBARRED g-side datum.  The twist is in `exp` form, term-for-term
-- `NonPret.costwist`, so `chiBarTwist χ t n = conj (χ n) * costwist t n` holds by `rfl`; the
-- sign is `n^{+it}` and every statement is `∀ t`, so KMT's `n^{-it}` is `chiBarTwist χ (-t)`.
--
-- ⟦THE TRANSFER⟧ `liouville_twist_eq_sum_divisorsAntidiagonal` (the identity `λ = 1_sq ∗ μ`
-- twisted), then `MlambdaChi_eq_sum_MmuChi` — the twisted `M_λχ̄(y) = ∑_{d ≤ √y} χ̄(d²)d^{2it}
-- M_μχ̄(⌊y/d²⌋)`.  The five arithmetic helpers of the landed fold (`sum_inv_sq_Ioc_le`,
-- `log_natSqrt_ge`, `le_sqrt_sqrt_of_pow4_le`, `eventually_pow4_le`, `sum_inv_sq_Icc_le`) are
-- CHARACTER-BLIND and are cited, not re-proved; only `Mmu_abs_le` needed a twin
-- (`norm_MmuChi_le`, `‖·‖` over ℂ instead of `|·|` over ℝ).
--
-- ⟦THE HYPOTHESIS SLOT, HONESTLY NOT LANDED⟧ `MmuChiRate` is the twisted twin of
-- `Salt.TwinBar.MmuRate`: a `y(log y)^{-A}` saving on `‖MmuChi χ t y‖`, with `C` and `x₀`
-- chosen BEFORE `q`, `χ`, `t` (uniform in the conductor range and in the height).  It is
-- exactly obligations **O4** (the `MobiusRateClose` re-run at `L(s,χ)`) + **O5** (the t-aspect
-- = the χ-VK/Landau–Page region, THE SAME STONE as P-6's stone B) and is NOT landed.
-- `LambdaChiSummatory_of_MmuChiRate` is the deliverable, conditional on it.
--
-- ⟦THE ONE PRICE, SPENT EXPLICITLY⟧ the μ-rate is invoked at `⌊y/d²⌋`, where only
-- `log⌊y/d²⌋ ≥ (log y)/4` is available, so the conductor gate moves by ONE exponent:
-- hypothesis at `q ≤ (log y)^{12}` (the freeze's number), deliverable at `q ≤ (log y)^{11}`.
-- The gate is on the MODULUS `q`, not `conductor χ`; since `conductor χ ≤ q` that demands
-- LESS of O4/O5 than the freeze's own line.
--
-- ⟦THE STALE COMMENT STRUCK⟧ `Salt/TwinBar/LambdaRate.lean`'s header and `MmuRate` docstring
-- both claimed that landing `MmuRate` from `siegelWalfisz_psiTot` "is the remaining
-- obstruction".  It is not: `Salt.SW.mmuRate_holds` (`Salt/SW/MobiusRateClose.lean`) LANDED,
-- and `Salt/TwinBar/WallUnconditional.lean` composes it.  Docstrings only; no declaration,
-- statement or proof in that file moved.
open Salt.Tactic in
#audit_axioms Salt.MR.mul_apply_mul_twist
  Salt.MR.pmul_mul_of_twist
  Salt.MR.chiBarTwist
  Salt.MR.chiBarTwist_mul
  Salt.MR.norm_chiBarTwist_le_one
  Salt.MR.liouville_twist_eq_sum_divisorsAntidiagonal
  Salt.MR.MmuChi
  Salt.MR.MlambdaChi
  Salt.MR.MmuChi_one_zero
  Salt.MR.MlambdaChi_one_zero
  Salt.MR.liouville_twist_eq_sum_moebius_twist
  Salt.MR.MmuChi_inner
  Salt.MR.MlambdaChi_eq_sum_MmuChi
  Salt.MR.norm_MmuChi_le
  Salt.MR.MmuChiRate
  Salt.MR.LambdaChiSummatory
  Salt.MR.MlambdaChi_rate
  Salt.MR.LambdaChiSummatory_of_MmuChiRate

-- ⟦WAVE P-3 — THE DISCRETE HYBRID LARGE SIEVE + THE HYBRID LARGE-VALUE COUNT (KMT Lemmas
-- 6.3, 6.5)⟧ (2026-07-29, port freeze v2 wave P-3; `HybridLargeValues`).  ADDITIVE: the
-- landed `LargeValues` / `LargeValueCount` are untouched and are *reused*, not retyped.
--
-- ⟦THE (χ,t)-SET⟧ `FibreWellSpaced ℰ` — for `ℰ : Finset (DirichletCharacter ℂ q × ℝ)`, two
-- members sharing the SAME character have ordinates `1`-separated; ordinates attached to
-- different characters are UNCONSTRAINED (READER-A's ambiguity, resolved to the same-χ
-- reading: it is what the fibrewise Gallagher argument needs and it is the weaker
-- hypothesis).  `exists_charFibre` packages the fibre decomposition existentially, so that
-- no *statement* in the file mentions a decidable-equality instance on characters (there is
-- none; `Classical` is used inside the construction only).
--
-- ⟦D1 — LEMMA 6.3⟧ `hybrid_wellspaced_l2` (pair form) / `hybrid_wellspaced_l2_family`
-- (fibre-family form, the engine).  For `s ⊆ Icc 1 N`:
--   `∑_{(χ,t)∈ℰ} ‖∑_{n∈s} aₙ·χ(n)·n^{it}‖²`
--     `≤ 84·(φ(q)·(T+1) + φ(q)·N/q)·log(2N)·∑_{n∈s,(n,q)=1}‖aₙ‖²`.
-- ⟦THE ORDER IS THE POINT (R-P3)⟧ the proof is the corpus's own written-out Gallagher
-- template (`wellspaced_l2`) with the mean-value input swapped to P-2's `hybrid_char_mvt`,
-- and the character sum taken AFTER the per-fibre Gallagher step
-- (`dpolyChi_fibre_gallagher`): summing the `q = 1` result over `χ` would pay `φ(q)·N` and
-- lose the `1/q` on the N-term.  New plumbing: the χ-twisted derivative
-- (`hasDerivAt_dpolyChi` / `deriv_dpolyChi` / `contDiff_dpolyChi` — the frequency `log n`
-- folds into the coefficient exactly as untwisted, the character value riding as a
-- constant) and the derivative moment `hybrid_char_mvt_deriv` (the same hybrid MVT at
-- `dtwist a`, paying `(log N)²`, which the AM–GM at `L = log(2N)` collapses to one
-- `log(2N)`).
-- ⟦THE `T+1`, STATED HONESTLY⟧ Gallagher's unit windows at ordinates in `[−T,T]` live in
-- `[−(T+½),T+½]`, so the diagonal is `2φ(q)(T+½) = 2φ(q)T + φ(q)`.  The stray `φ(q)` is NOT
-- absorbable into `φ(q)N/q` (that term can be the smaller of the two at large `q`), so it
-- is carried in the statement; at `T ≥ 1` a caller reads `T+1 ≤ 2T`.  Constant `84` = the
-- template's (28 suffices); `log(2N)` = the template's scale, not `log(3N)`.
--
-- ⟦D2 — LEMMA 6.5⟧ `hybrid_large_value_count`: for `c` supported on primes in `[P,2P]` with
-- `‖c_m‖ ≤ 1/m` (CATCH #A — the corpus's σ=1 convention, `c_p = a_p/p` PRE-FOLDED; KMT's
-- σ=0 statement reads through that dictionary) and `ℰ` per-fibre well-spaced with
-- `V⁻¹ ≤ ‖∑_{P≤p≤2P} c_p χ(p) p^{it}‖`:
--   `|ℰ| ≤ 1680·(qT)^{2 log V/log P}·V²·exp(2·(log qT/log P)·loglog qT)`.
-- ⟦THE k!-CORE IS CHARACTER-FREE, VERBATIM⟧ `dpolyChi q (Icc 1 N) c χ = dpoly N (c·χ)`
-- (`dpolyChi_Icc`, `rfl`), and complete multiplicativity distributes over the k-fold
-- convolution: `kconv_coeffChiTwist : kconv N (c·χ) k n = (kconv N c k n)·χ(n)`.  So the whole
-- landed combinatorial block (`kconv_supp_lower`, `kconv_primeFactors_card_le`,
-- `kconv_sup_le`, `kconv_sup_le_window`, `kconv_l2_le_window`, `csum_window_le`) is
-- consumed UNCHANGED — the twist only multiplies each coefficient by a factor of modulus
-- ≤ 1.  The two transcendental legs `pow_V_le` and `pack_exp_le` are pure real analysis and
-- are likewise reused unchanged, evaluated at the argument `qT` (the `T → qT` rewrite).
-- ⟦THE CONSTANT⟧ `1680 = 2·840`: the `2` is the bracket domination
-- `φ(q)(T+1) + φ(q)(2P)^k/q ≤ 2·(qT + (2P)^k)`, valid at `T ≥ 1` (from `φ(q) ≤ q`).
-- ⟦GATES⟧ the landed original's shapes at `qT` where forced: `3 ≤ P`, `1 ≤ T`, `1 < qT`,
-- `P ≤ qT`, `1 ≤ V`, `log qT/log P ≥ 30`, `loglog qT ≥ 5`.  The product-form bound (vs
-- KMT's sum-form) is the freeze's ACCEPTED weakening.  ⟦CATCH #B⟧ statements are at
-- `dpolyChi`'s `n^{+it}`; a caller holding `|P_χ(1−it)| ≥ V⁻¹` applies these at the negated
-- ordinate set, which is `FibreWellSpaced`, inside `[−T,T]`, and of the same cardinality
-- (mean-square form: `dpolyS_meanSq_reflect`).  Consumer: P-6's 𝒰-leg lift.
open Salt.Tactic in
#audit_axioms Salt.MR.exists_charFibre
  Salt.MR.hasDerivAt_dpolyChi
  Salt.MR.deriv_dpolyChi
  Salt.MR.contDiff_dpolyChi
  Salt.MR.continuous_deriv_dpolyChi
  Salt.MR.sum_dtwist_sq_le_subset
  Salt.MR.hybrid_char_mvt_deriv
  Salt.MR.hybrid_l2_arith
  Salt.MR.dpolyChi_fibre_gallagher
  Salt.MR.hybrid_wellspaced_l2_family
  Salt.MR.hybrid_wellspaced_l2
  Salt.MR.dpolyChi_Icc
  Salt.MR.norm_coeffChiTwist_le
  Salt.MR.kconv_coeffChiTwist
  Salt.MR.norm_dpolyChi_pow
  Salt.MR.card_mul_pow_le_hybrid
  Salt.MR.hybrid_large_value_count_combined
  Salt.MR.hybrid_large_value_count

-- ⟦WAVE P-4 — THE χ-SUMMED MOMENTS (KMT LEMMAS 6.6 + 6.7)⟧ (2026-07-29, KMT port;
-- `HybridMoments`).  Freeze `docs/exploration/port-freeze-0729.md` wave P-4; spec =
-- READER-A's 6.6/6.7 mappings (flags ⟦THE KMT DEEP READ⟧).  The whole wave is ONE idea:
-- the landed `q = 1` machinery is CHARACTER-BLIND, so it lifts to the χ-twisted datum for
-- free, and only the MEAN-VALUE ENGINE is swapped — `moment_core_bound` → wave P-2's
-- `hybrid_char_mvt`.
--
-- ⟦THE SHARED BRIDGE⟧ `hybrid_char_spoly_mvt` — P-2's hybrid MVT is at `σ = 0`
-- (`dpolyChi`), the corpus is at `σ = 1` (`spoly`); the landed `spoly_eq_dpoly`
-- (`MomentsA2:59`) converts at the cost of `aₙ ↦ aₙ/n`, `t ↦ −t`, and the symmetric window
-- makes the sign free (`integral_comp_neg`).  Deliverable:
--   `∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n≤N} χ̄(n)aₙ/n^{1+it}‖² ≤ (2φ(q)T + 7φ(q)N/q)·∑‖aₙ‖²/n²`
-- — the drop-in `σ = 1` replacement for `moment_core_bound`'s `(2T + 20N)`.  Summing the
-- `q = 1` grade over φ(q) characters instead would pay `φ(q)·20N`: the `1/q` is R-P3's
-- non-droppable saving, and this is where the port actually spends it.
--
-- ⟦THE BARRED-χ CONVENTION (N1)⟧ every statement is at `χ̄ = conj ∘ χ` (`chiBarCoeff`),
-- matching the corpus (`lamChi`/`liouChi`/`chiBarTwist`) and P-6's 𝒰-lift.  `hybrid_char_mvt`
-- is at unbarred χ; the bridge is `sum_chiBar_reindex` — `conj (χ a) = χ⁻¹ a`
-- (`MulChar.star_apply'`) and inversion is an involution of the character group, so a sum
-- over ALL φ(q) characters is invariant under barring.  Cost: zero.
--
-- ⟦D1 = LEMMA 6.6, the `Q^ℓ·A` moment⟧ `multShiuChi_moment`:
--   `∑_{χ mod q} ∫_{-T}^{T} ‖Q_j(χ̄,1+it)^ℓ·R_v(χ̄,1+it)‖² dt`
--     `≤ (2φ(q)T + 7φ(q)(2Y₁)^ℓ Mr/q)·(ℓ!²·C/(Y₁^ℓ X₀))`.
-- The landed `multShiu_moment`'s two MULT-SHIU seam stones are consumed VERBATIM (both are
-- character-blind): the window `multShiuCoeff_support_low/_high` and the count
-- `coeff_bound_factorial_blockDiv` (`‖aₙ‖ ≤ ℓ!·blockDiv Y₁ n`); the mass page is the landed
-- dyadic Shiu sum `blockDiv_sq_div_sq_sum_le` over `shiu_moment_sq`, whose `g` byte-matches
-- KMT's (READER-A §7).  ⟦THE ONE NEW ALGEBRAIC FACT⟧ twisting commutes with the ℓ-fold
-- Dirichlet convolution — `multShiuCoeff_chiBar`, via wave P-1's `pmul_mul_of_twist`
-- (`LambdaRateTwisted:153`) instantiated at `chiBarAf` and iterated (`pmul_pow_of_chiBarAf`).
-- ⟦THE `(ℓ+1)!²` ROUTE⟧ the corpus's count page is SHARPER than the paper's: the ℓ-fold
-- ordered block-prime count is `≤ ℓ!` and the co-factor enters through the 1-bounded
-- divisor-sum majorant `oneAf`, not as an `(ℓ+1)`-st factor — so `ℓ!²` is delivered and
-- `multShiuChi_moment_KMT` restates it at the paper's `(ℓ+1)!²` (pure domination).
-- ⟦THE `chiBarAf` GUARD⟧ the twist is NOT an `ArithmeticFunction` as written: at `q = 1`,
-- `(0 : ZMod 1) = 1` so `χ(0) = 1 ≠ 0`.  `chiBarAf` carries the `if n = 0` guard; every
-- use is on the nonzero branch, which is exactly `pmul_mul_of_twist`'s hypothesis shape.
-- ⟦THE DISCRETE (17)-FORM⟧ `spoly_chiBar_plancherel_at_zero` — at a single height the χ-sum
-- is an EQUALITY (`char_plancherel`), not a bound; `multShiuChi_moment_T1` is the `T = 1` row.
--
-- ⟦D2 = LEMMA 6.7, the Ramaré decomposition χ-summed⟧ `lemma12_meansq_all_chi`.  KMT's own
-- proof note is "almost identical to [32, Lemma 12] … estimates the error terms by Lemma 6.2
-- instead of the MVT", and [32, Lemma 12] IS the landed `lemma12_meansq`
-- (`RamareWindows:671`).  The entire eq-(16) identity chain (`spoly_ramare_eq16` →
-- `spoly_ramare_split` → `clean_term_dyadic` → `ramErr_window_decomp`) is an identity of
-- finite sums under ONE hypothesis, `a_{pm} = b_m c_p` on the coprime block — and the twisted
-- triple satisfies it because `χ̄(pm) = χ̄(p)χ̄(m)` (`chiBar_hcoef`).  So the identity work is
-- FREE and only the three error rows are re-priced:
--   • the sieve remainder (`ramCopTail`) — hybrid MVT, mass SYMBOLIC (P-7's discharge);
--   • the `p²`-correction (`ramP2corr`) — hybrid MVT, via `ramP2coeff_chiBar` (the fibre
--     recombination `χ̄(m)χ̄(p) = χ̄(n)`) and `ramP2corr_eq_spoly`'s un-inflated `[1,N]` cap;
--   • the grid/window error (`ramWindowErr`) — the χ-UNIFORM SUP, φ(q)-fold.
-- ⟦THE ONE STATED DEVIATION⟧ the brief asked for the hybrid MVT on both error terms; the
-- window row's frequencies run to `QN`, not `N`, so ANY mean-value theorem inflates the
-- frequency cap — the trap the landed q=1 proof avoids by `ramWindowErr_sup_le`.  That sup
-- is also χ-uniform (`windowMassChi_le`: twisting only shrinks the ℓ¹-mass), so the χ-sum
-- costs exactly φ(q) — the same φ(q) the hybrid MVT's diagonal would cost, and strictly less
-- than its off-diagonal.  ⟦THE GRID⟧ N6 held: `ramI = ⌊H log P⌋..⌊H log Q⌋` is already KMT's
-- `H·log p` grid, not base-2 dyadic — used as landed.  The `∑_χ∑_j` is exchanged to `∑_j∑_χ`
-- so each `j`-block presents exactly the object D1 prices.  Consumers: P-6's 𝒰-leg lift,
-- P-7's assembly.
open Salt.Tactic in
#audit_axioms Salt.MR.chiBarCoeff
  Salt.MR.norm_conj_chi_le_one
  Salt.MR.norm_chiBarCoeff_le
  Salt.MR.norm_chiBarCoeff_le_one
  Salt.MR.sum_chiBar_reindex
  Salt.MR.chiBarCoeff_eq_inv
  Salt.MR.spoly_chiBarCoeff_eq_dpolyChi
  Salt.MR.hybrid_char_spoly_mvt
  Salt.MR.chiBarAf
  Salt.MR.chiBarAf_one
  Salt.MR.chiBarAf_mul
  Salt.MR.pmul_pow_of_chiBarAf
  Salt.MR.ramQaf_chiBar
  Salt.MR.ramRaf_chiBar
  Salt.MR.multShiuCoeff_chiBar
  Salt.MR.ramQ_pow_mul_ramR_chiBar_eq_spoly
  Salt.MR.multShiuChi_moment
  Salt.MR.multShiuChi_moment_KMT
  Salt.MR.spoly_chiBar_plancherel_at_zero
  Salt.MR.multShiuChi_moment_T1
  Salt.MR.card_dirichletChar
  Salt.MR.sum_const_dirichletChar
  Salt.MR.conj_chi_natCast_mul
  Salt.MR.chiBar_hcoef
  Salt.MR.windowMassChi_le
  Salt.MR.ramP2coeff_chiBar
  Salt.MR.ramP2corr_chiBar_eq_spoly
  Salt.MR.ramCopTail_chiBar_eq_spoly
  Salt.MR.ramErr_meanSq_all_chi
  Salt.MR.lemma12_meansq_all_chi

-- ⟦WAVE P-6-CORE — THE χ-VK ZERO-FREE REGION, UNCONDITIONAL⟧ (2026-07-29, port freeze v2 wave
-- P-6-core; `VkTwistStrip` / `VkTwistRegion` / `VkTwistRegionReal`).  ⟦SPECTRUM-SCOPE⟧ named ONE
-- missing analytic stone for the KMT port — the VK-WIDTH zero-free region for `L(s,χ)` — and the
-- B-probe supplied the bridge conditionally on a strip growth.  This wave discharges the
-- hypothesis and lands the region.
--
-- ⟦STONE A — THE TWISTED STRIP GROWTH⟧ `vk_char_strip_growth` / `vk_char_box_growth`: for
-- nonprincipal `χ mod q`, `|T| ≥ exp(exp 100)` and `1 − vkTheta|T| ≤ σ ≤ 2`,
-- `‖L(σ+iT,χ)‖ ≤ vkStripConst q·(1 + log|T|)` — and the BOX form on
-- `Re z ∈ [1 − vkTheta 3γ, 2]`, `Im z ∈ [γ−1, 3γ]` at the floor `exp(exp 100) ≤ γ − 1`, which is
-- exactly the probe's `hgrowth` shape.  Route: the landed general-σ twisted per-block bound
-- (`Salt.Vk.vk_dirichlet_block_twist_all`, `≤ 1348`, no upper σ-gate) over a dyadic ladder of
-- `≤ 3(1+log t)` blocks — NO Abel fold, because the block bound already holds at the actual `σ`;
-- then the elementary Fourier completion (`char_sum_fourier_le`, one factor `q`) and the
-- truncation at `N = ⌈T²⌉` through `Salt.SW.norm_LFunction_sub_partial_le` at the CRUDE level
-- bound `M = q` (`norm_char_partial_sum_le`), whose tail is `≤ 4q` since `N^{−σ} ≤ 1/|T|`.
-- ⟦TWO DEVIATIONS, BOTH FAVOURABLE⟧ (1) `vkStripConst q = 5000·q` is LINEAR in `q`, not the
-- freeze's `q^{3/2}(1+log q)`: Pólya–Vinogradov (primitive-only, `√q(1+log q)`) is unnecessary at
-- truncation length `t²`, so no imprimitivity adapter and no `√q`.  (2) The growth is
-- `Cq·(1+log|t|)`, not `Cq·(log)^{3/4}(loglog)⁴`: the sharper profile is a NEAR-1-LINE phenomenon
-- (the geometric `M^{−Θ/2}` decay needs `σ ≥ 1 − Θ/2`, i.e. half the strip), and ζ's own strip
-- shape is likewise `K·log t` (`Salt.Vk.zeta_growth_pow`).  The width law sees `M` only through
-- `log M`, so keeping the FULL strip instead of halving `Θ` is worth ≈`2×` in the final constant.
--
-- ⟦STONE B — THE REGION⟧ `LFunction_zero_free_region_vk`: for `χ ≠ 1`, `χ² ≠ 1`, every zero with
-- `|Im ρ| ≥ exp(exp 100) + 1` obeys
-- `Re ρ ≤ 1 − (1/(10⁸(A+7)))·1/((log|Im ρ|)^{3/4}(loglog|Im ρ|)³)` under the `q`-scale gate
-- `log(20000·vkStripConst q) ≤ A·loglog|Im ρ|` (i.e. `log(10⁸) + log q ≤ A·loglog|Im ρ|` — benign
-- at `q ≤ (log H)^12`).  ⟦KR-2 BENIGN, TWICE⟧ the level cost is additive inside a logarithm AND
-- linear in `q`.  ⟦THE HEIGHT FLOOR RE-TUNED (probe gap-4)⟧ the coarser growth needs only
-- `2 log ℓ₃ ≤ ℓ₃`, so the floor drops from the probe's `1100 ≤ loglog|Im ρ|` to `100` — which the
-- landed `exp(exp 100)` block already supplies: the port adds ZERO height demand.
-- ⟦THE NEGATIVE HALF (probe gap-3)⟧ `LFunction_inv_conj`: `L(χ⁻¹, conj s) = conj(L(χ,s))` for any
-- `χ ≠ 1` — the general-character twin of `Salt.SW.LFunction_conj` (real-only), same identity-
-- theorem route with `conj(χ n) = χ⁻¹ n` (`MulChar.star_apply'`).  `χ⁻¹` has the same level, so
-- the same gate and constant serve.
--
-- ⟦THE `χ² = 1` ARM (probe gap-2)⟧ `LFunction_real_zero_free_region_vk`: the SAME width and the
-- SAME constant for a REAL non-principal `χ`, at the gate
-- `log(20000·(vkStripConst q + 8104)) ≤ A·loglog|Im ρ|`.  The third 3-4-1 leg is the PRINCIPAL
-- character, whose L has ζ's pole, so the probe's drop-all is replaced by ζ's own landed
-- `Salt.Vk.zeta_drop_all_disc` (spheres via `Salt.Vk.Zc_ratio_sphere_bound`, gate `1 ≤ |2γ|` free)
-- plus TWO numerals: the finite-Euler debit `neg_re_logDeriv_trivChar_le_zeta`
-- (`Re(−L′/L(s,χ₀)) ≤ Re(−ζ′/ζ(s)) + log q`, the `Re s > 1` core of
-- `Salt.SW.neg_re_logDeriv_trivChar_complex_le` with its CLASSICAL ζ-leg — `1080 log(|γ|+2)`,
-- which is `≫ (log γ)^{3/4}(loglog γ)³` and would destroy the VK width — left open), and the pole
-- correction `Re(1/(s₂−1)) ≤ 1/16` (the probe's "vacuous at VK width": `σ−1` is tiny against
-- `|γ| ≥ 2`, so `Salt.SW.zero_free_region_real`'s conjugate-zero apparatus is NOT needed).  The
-- chain is the probe's with `8 ⟹ 8 + log q` — the predicted `Lq = 8 + log q + 700·Pinv·W` shape —
-- and the debit rides inside the same gate, so the constant is unchanged.  ζ's growth is
-- re-derived with EXPLICIT constants (`zeta_strip_growth_explicit`, `‖ζ‖ ≤ 8104·log t`) so no
-- existential leaks from `Salt.Vk.zeta_growth_pow`.
-- ⟦NOT BUILT (P-7's, per the brief)⟧ the `∃ H₀` Siegel fold: zeros with `Im ρ = 0` are excluded by
-- the height floor exactly as `Salt.SW.zero_free_region_all`'s `(χ² ≠ 1 ∨ Im ρ ≠ 0)` carve-out
-- excludes them.  The consumer's dispatch: complex zeros of real `χ` ⟹ this wave; the exceptional
-- real zero ⟹ `Salt.SW.siegel_zero_free_exceptional` (KMT's `1_{χ∈{χ₀,ξ₁}}` row); heights below
-- the floor ⟹ the classical explicit `Salt.SW.zero_free_region_all'`.
--
-- ⟦STONE C NOT ATTEMPTED — the honest finding⟧ `halasz_primes_chi` (the χ-twin of
-- `halasz_primes_pow`) needs more than a retype: the REUSE BOUNDARY inside
-- `HalaszPrimesCore` is at the representation layer only (`primeWindow_contour_rep`,
-- `rep_truncated` are generic in the coefficients `a : ℕ → ℂ` — genuinely reusable), while REP
-- (`lambda_window_rep`), ZFREE-RECT, EDGE (`shifted_edge_price_strip`), RES and `per_pair_contour`
-- are written directly at `vonMangoldt`/`riemannZeta`/`Zc` and must be re-proved.  TWO design
-- questions the next wave must answer FIRST: (i) the EDGE price's moderate-height leg is ζ's
-- NON-EXPLICIT compact bound (`logDeriv_Zc_compact_bound`, `∃ δ₀ C₀`) — legitimate for the fixed
-- function ζ, but for `χ mod q` with `q` growing in `H` the constant would depend on `q`
-- non-effectively, so the χ-twin needs either a `q`-explicit L′/L strip bound or the classical
-- explicit region `zero_free_region_all'` carrying the low/moderate heights; (ii) the pole row
-- (RES) VANISHES for `χ ≠ 1` as the brief says, but the principal/exceptional rows must then be
-- carried by KMT's `1_{χ∈{χ₀,ξ₁}}` bookkeeping, which is an assembly decision, not a port.
open Salt.Tactic in
#audit_axioms Salt.MR.vk_twist_strip_sum_le
  Salt.MR.vk_twist_strip_abs_le
  Salt.MR.vk_char_strip_head_le
  Salt.MR.vkStripConst
  Salt.MR.one_le_vkStripConst
  Salt.MR.vkTheta_le_thousandth
  Salt.MR.vk_char_strip_growth
  Salt.MR.vk_char_box_growth
  Salt.MR.LFunction_zero_free_region_vk_pos
  Salt.MR.LFunction_inv_conj
  Salt.MR.LFunction_inv_conj_zero
  Salt.MR.LFunction_zero_free_region_vk
  Salt.MR.zeta_strip_growth_explicit
  Salt.MR.zeta_box_growth_explicit
  Salt.MR.neg_re_logDeriv_trivChar_le_zeta
  Salt.MR.LFunction_real_zero_free_of_disc
  Salt.MR.LFunction_real_region_of_growth
  Salt.MR.LFunction_real_zero_free_region_vk_pos
  Salt.MR.LFunction_real_zero_free_region_vk

-- ⟦WAVE P-6-E — THE 𝒰-LEG χ-LIFT (the index-set retype)⟧ (2026-07-29, port freeze v2 wave P-6
-- stone E; `USetChi` / `USetChiTS`).  ⟦SPECTRUM-SCOPE⟧'s stone E: the (t : ℝ)-indexed spectrum
-- machinery of the 𝒰-leg (`USetThin` / `USetThinTL` / `USetThinTS` / `USetBalance`) retyped to
-- (DirichletCharacter ℂ q × ℝ)-indexed, consuming P-2/P-3/P-4's supply floor.  The datum is
-- character-blind, so the proofs are near-verbatim; what is NOT verbatim is recorded below.
--
-- ⟦THE REFLECTION IS A PAIR INVOLUTION (CATCH #B ∘ N1)⟧ `reflectPair` / `reflectChi`: the
-- σ = 1 → σ = 0 bridge `spoly N (χ̄ a) t = dpolyChi q _ (a/n) χ⁻¹ (−t)`
-- (`HybridMoments.spoly_chiBarCoeff_eq_dpolyChi`) negates the ordinate AND conjugates the
-- character, so the q = 1 files' "negated ordinate set" becomes the involution (χ,t) ↦ (χ⁻¹,−t).
-- Built with `Finset.map` on an `Equiv` (not `Finset.image`), so NO `DecidableEq` on characters
-- enters any statement — the discipline `HybridLargeValues.exists_charFibre` set.  Card,
-- `FibreWellSpaced` and `[−T,T]` are all preserved.  Every statement declares its side: the
-- `ramQ`/`ramR`/`ramMain`/`primeBlockPoly` carriers are σ = 1; only the four `_eq_dpolyChi`
-- bridges and the two socket consumptions cross over.  `ramQ_chiBar_eq_halaszSum` is sign-FREE
-- (the σ = 1 convention already carries `p^{−it}`).
--
-- ⟦THE BLOCK OBJECTS ARE THE LANDED ONES AT TWISTED DATA⟧ no new block carrier is minted: the
-- retype is `ramQ H P Q j (chiBarCoeff q χ c)` etc., and the content is that the twist passes
-- through the masks (`blockSrc_chiBar`, `ramQsrc_chiBar`, `ramRcoeff_chiBar`) and through the
-- `1/n` of the σ = 1 convention (`chiBarCoeff_div`).  `UsetChi` is likewise the LANDED
-- `Decomp.Uset` of the twisted datum, fibre by fibre — which is what makes the whole
-- witness/ratio-2-chain/pigeonhole page of `USetThin` reusable at pairs.
--
-- ⟦REUSED VERBATIM, NO RETYPE (character-free)⟧ `dyadicPairs` + `card_dyadicPairs_le` +
-- `dyadicPairs_card_le_exp` (the Q_J² union factor is a t-free AND χ-free family),
-- `ratioChain` + `primeBlockPoly_chain_split` + `exists_piece_large`, `largeblock_bound_mono`
-- (rescaled by `hybridblock_bound_mono`), `tL_kill`, `thin_sqrt_kill`, `ramQbase` and its
-- geometry, `ramQblock_inv_sum_le` (the prime-window gain), `ramQbase_le_pow_ten`,
-- `norm_ramMain_sq_le_of_small`, `meansq_on_subset_of_decomp`, `wellspaced_discretize`,
-- `block_sum_bound` (at `Cq := 3C/2`, see the constant debit).
--
-- ⟦THE HEIGHT IS qT, AND THAT IS THE ONLY PLACE THE CHARACTER COUNT ENTERS⟧
-- `hybrid_large_value_count` counts PAIRS at height `q·T`, so `UsetChi_thin` carries NO φ(q)
-- union factor — the crude `|ℰ| ≤ φ(q)·max_χ|𝒯_χ|` route is not taken.  Every count/kill gate is
-- the landed shape read at `Real.log ((q:ℝ)*T)`: `1 < qT`, `P ≤ qT`, `30 ≤ log qT/log base`,
-- `5 ≤ loglog qT`, `log qT ≤ L`.  LAW #253: the X₀ law (`hκ30`) and the kill gate
-- `420·L·L^{3/4}(log L)^5 ≤ c·W²` stay in-statement, verbatim, at every rung.
--
-- ⟦THE ONE CONSTANT DEBIT⟧ Lemma 6.5's hybrid constant is `1680 = 2·840` (the fold's bracket
-- domination), so the landed `tL_kill` — stated at `840` — gives `|𝒯_L|·decay·(log qT)² ≤ 2`, not
-- `≤ 1`.  The 𝒯_L bracket therefore collapses to `3·base` (not `2·base`), the killed Q-side exits
-- at `3C` (not `2C`), and `tLChi_main_sumsq` at `81·C·Rbd²·(H/j)²` (not `54`).  `81 = 3·27`
-- against `54 = 2·27`; `USetBalance.block_sum_bound` absorbs it verbatim at `Cq := 3C/2`.
--
-- ⟦THE 𝒯_S RAZOR AND ITS CHARACTER DEBIT — THE MARGIN, COMPUTED⟧ the hybrid height splits as
-- `(qT)^{2α} = q^{2α}·T^{2α}`, so the razor's ENTIRE character cost is the single factor
-- `q^{2α} ≤ √q`, and `thin_sqrt_kill` is reused verbatim with `W := q^{2α}·W`
-- (`UsetChi_thin_sqrt_kill`).  `charDebit_le_rpow`: at the port's modulus gate
-- `q ≤ (log H)^12 ≤ (log X)^12` and `2α ≤ 1/2`, `q^{2α} ≤ √q ≤ (log X)^6 ≤ X^ε` whenever
-- `6·loglog X ≤ ε·log X` (`logpow_le_rpow_of_gate`, in-statement — nothing absorbed), and at
-- `ε = 1/1000` — HALF the landed `2η ≥ 1/500` (`USetPins.c0_le_exit_exponent`) — the gate holds
-- already at `log X ≥ e^40 ≈ 2.4·10^17` (`logpow_gate_of_exp_floor`, via `log L ≤ √L` and
-- `√L ≥ e^20 ≥ 6000`).  The same file's own X₀ law forces `log X ≥ 30^{3/ρ} ≈ 10^385`, where the
-- debit needs `6·loglog X ≈ 5.3·10^3` against `ε·log X ≈ 10^382`: **the razor tolerates the
-- φ(q)-genre debit with ≈ 378 orders of magnitude of margin**, and pays it out of at most half the
-- η it already had (`UsetChi_thin_sqrt_kill_absorbed`, exit `X^{1−2η+ε}` with `ε ≤ η`).
--
-- ⟦TWO NAMED HYPOTHESIS SLOTS (P-7 connects them)⟧
-- (1) `HalaszPrimesChi C c q T` — the χ-twisted MR Lemma 11, wave P-6-CORE's stone C, which that
-- wave reports NOT ATTEMPTED (the REUSE BOUNDARY finding).  Shape: `halasz_primes_pow` with the
-- pair index, `FibreWellSpaced` spacing, the χ̄-twisted integrand and the VK decay denominator
-- read at `qT`.  Reading it at `qT` rather than `T` makes the slot the WEAKER hypothesis (a larger
-- denominator is a weaker decay), so a sharper landed `halasz_primes_chi` discharges it.
-- ⟦THE SLOT-WAVE AMENDMENT (2026-07-30) — the quantifier order⟧ the slot was first stated with a
-- UNIFORM floor, `HalaszPrimesChi C c T₀ := ∀ q, 0 < q → ∀ T ≥ T₀, …`, and in that shape it is NOT
-- dischargeable: `PortClose.halaszPrimesChi_holds_gated` proves the same conclusion behind four
-- `q`-vs-`T` gates whose floors GROW with `q`, and no single `T₀` bridges a `q`-dependent floor.
-- It is now POINTWISE — `q` and `T` are parameters, the floor rides at the consumer — and the
-- three `𝒯_L` rungs below were re-run at the moved instantiation point (proofs verbatim; `0 < q`
-- and `T₀ ≤ T` drop out of `tLChi_sumsq_ramQ` / `tLChi_ramQ_sumsq_killed` / `tLChi_main_sumsq`).
-- Nothing is lost: the old form IS `∀ q, 0 < q → ∀ T ≥ T₀, HalaszPrimesChi C c q T`, and every
-- consumer spends the socket at ONE `(q, T)`.  `PortClose.halaszPrimesChi_pointwise_of_gates` then
-- DISCHARGES it, and the 𝒰-exit is socket-free (`usetChi_window_meansq_gated`).
-- (2) **`HalaszIntegersChi Cint` — the χ-twisted MR Lemma 9 (Halász for integers).  A FINDING:
-- this stone is on NEITHER the freeze's stone list (A–E) NOR in P-3/P-4's supply floor.**  The 𝒯_S
-- branch cannot run at the landed hybrid MEAN-VALUE grade: `hybrid_wellspaced_l2` carries a
-- `φ(q)(T+1)` row, and at the §8.3 pins `T ≍ X` while the co-factor length is `M ≍ X e^{−j/H}`, so
-- that row exceeds the q = 1 exit (`5128 ε² M (1+log 2T)`) by the factor `e^{j/H} ≍ p` — precisely
-- the factor the whole apparatus exists to save.  The trivial-grade row is landed anyway
-- (`ramRChi_sq_sum_mvt`, MR Step 0's majorant above `T ≍ X`), which is what makes the gap visible
-- rather than assumed.
--
-- ⟦THE BALANCE TWIN⟧ `fibrePack` (the inverse of `exists_charFibre`, built with
-- `Finset.disjiUnion`/`Finset.map` — again instance-free), the exhaustive branch-split IDENTITY at
-- pairs (`sum_TSChi_add_TLChi`, `tLsetChi_eq_filter_not`), and `usetChi_integral_to_branches`: the
-- χ-summed twin of `USetBalance.uset_integral_to_branches`, with the eq-(16) Cauchy–Schwarz and
-- the parity-halving discretisation applied PER CHARACTER and the per-(χ,j) witness sets packed
-- into the one pair set the branch bounds speak about.  The error row is taken χ-SUMMED — exactly
-- what `HybridMoments.lemma12_meansq_all_chi` supplies.  The §8.3 parameter page (`USetPins`:
-- H83/P83/Q83/J/θ) is consumed as landed and the lift stays parameter-generic; the cascade
-- re-pins are P-7's.
open Salt.Tactic in
#audit_axioms Salt.MR.reflectPair
  Salt.MR.reflectChi
  Salt.MR.mem_reflectChi
  Salt.MR.card_reflectChi
  Salt.MR.sum_reflectChi
  Salt.MR.fibreWellSpaced_reflectChi
  Salt.MR.reflectChi_subset_Icc
  Salt.MR.fibreWellSpaced_of_subset
  Salt.MR.chiBarCoeff_div
  Salt.MR.blockSrc_chiBar
  Salt.MR.primeBlockPoly_chiBar_eq_dpolyChi
  Salt.MR.ramQsrc_chiBar
  Salt.MR.ramQ_chiBar_eq_spoly
  Salt.MR.ramQ_chiBar_eq_dpolyChi
  Salt.MR.ramQ_chiBar_eq_halaszSum
  Salt.MR.hybridblock_bound_mono
  Salt.MR.hybridblock_count
  Salt.MR.UsetChi
  Salt.MR.mem_UsetChi
  Salt.MR.UsetChi_thin
  Salt.MR.tLsetChi
  Salt.MR.tLsetChi_subset
  Salt.MR.mem_tLsetChi
  Salt.MR.tLsetChi_fibreWellSpaced
  Salt.MR.ramQChi_large_count
  Salt.MR.ramQChi_large_count_Tfree
  Salt.MR.HalaszPrimesChi
  Salt.MR.tLChi_sumsq_ramQ
  Salt.MR.tLChi_ramQ_sumsq_killed
  Salt.MR.tLChi_main_sumsq
  Salt.MR.ramRcoeff_chiBar
  Salt.MR.ramR_chiBar_eq_spoly
  Salt.MR.ramR_chiBar_eq_dpolyChi
  Salt.MR.ramRcoeff_chiBar_mass_le
  Salt.MR.HalaszIntegersChi
  Salt.MR.ramRChi_sq_sum_le
  Salt.MR.ramRChi_sq_sum_mvt
  Salt.MR.thinBundleChi
  Salt.MR.thinBundleChi_nonneg
  Salt.MR.UsetChi_thin_alpha
  Salt.MR.UsetChi_thin_sqrt_kill
  Salt.MR.logpow_le_rpow_of_gate
  Salt.MR.logpow_gate_of_exp_floor
  Salt.MR.charDebit_le_rpow
  Salt.MR.UsetChi_thin_sqrt_kill_absorbed
  Salt.MR.TsetSmallChi
  Salt.MR.mem_TsetSmallChi
  Salt.MR.TsetSmallChi_subset
  Salt.MR.TSChi_branch_meansq
  Salt.MR.usetChi_TS_branch_meanvalue
  Salt.MR.tLsetChi_eq_filter_not
  Salt.MR.sum_TSChi_add_TLChi
  Salt.MR.fibrePack
  Salt.MR.mem_fibrePack
  Salt.MR.sum_fibrePack
  Salt.MR.fibreWellSpaced_fibrePack
  Salt.MR.usetChi_integral_to_branches

open Salt.Tactic in
#audit_axioms Salt.MR.norm_chi_vonMangoldt_twist_le
  Salt.MR.lambda_window_rep_chi
  Salt.MR.halasz_primes_chi
  Salt.MR.halasz_primes_chi_principal
  Salt.MR.halasz_primes_chi_hybridHeight
  Salt.MR.halasz_primes_chi_fibres
  Salt.MR.loglog_ge_hundred
  Salt.MR.logDn_mono
  Salt.MR.twisted_rect_zero_free_split
  Salt.MR.TwistedWindowPrice

-- ⟦O4 + O5 — THE χ-TWISTED MÖBIUS RATE: the spine, the region discharge, the residue⟧
-- (2026-07-29, KMT port wave P-5; `MobiusChiRate`).
--
-- The port's centerpiece, taken as far as the analytic boundary and STOPPED there on purpose.
--
-- ⟦D1 — THE SLOT AUDIT⟧ Wave P-1's `MmuChiRate` quantified `∀ t : ℝ` UNBOUNDED, and that is
-- FALSE, not merely undischargeable: by Kronecker density on `{log p}` one can choose `t`
-- (depending on `y`, which the quantifier order permits) with `p^{it} ≈ −1` for every `p ≤ y`,
-- making every squarefree term `≈ +1` and the sum `≍ (6/π²)y`.  The RULED in-place amendment
-- re-gates the slot at `|t| ≤ y`, and the fold's λ-side deliverable at `|t| ≤ ⌊√y⌋` (the
-- transfer `|t| ≤ ⌊√y⌋ ≤ ⌊y/d²⌋` is exactly `Nat.sqrt_le`, already proved inside
-- `MlambdaChi_rate` as `hts`).  So the fold now spends ONE of the twelve conductor exponents
-- AND HALF THE HEIGHT RANGE — both prices stated in `LambdaRateTwisted`'s header.
--
-- ⟦WHY `|t| ≤ y` IS THE HONEST CEILING⟧ The twist is a PURE SHIFT:
-- `∑ μ(n)χ̄(n)n^{it}n^{-s} = 1/L(s−it, χ⁻¹)` (`LSeries_muChiTw_eq_LFunction_inv`).  So the
-- truncated Perron contour reads the L-function at heights up to `|t| + T`, and the saving is
-- `exp(−(log y)·w(|t|+T))` for the zero-free WIDTH `w`.  At the CLASSICAL width `c₀/log(qH)`
-- that buys only `|t| ≤ exp((log y)^{1−δ})`; at the landed χ-VK width it buys any fixed power
-- of `y`.  This is the precise sense in which stone B was the campaign's isolated risk.
--
-- ⟦THE SPINE, LANDED⟧ `exp_phase_eq_cpow` + `chiBarTwist_eq_inv_mul_cpow` (the corpus's
-- barred exp-form twist IS `χ⁻¹(n)·n^{it}`; `MulChar.star_apply'`), the Dirichlet-series
-- identity above, the smoothed twisted Riesz mean `Mmu1Chi` with its Perron representation in
-- both `LSeries` and `1/L` form (`mmu1Chi_eq_integral_LSeries`, `mmu1Chi_eq_integral` — the
-- kernel machinery `kernel_sum_swap`/`riesz_tsum_eq`/`kernel_identity`/`integral_term_eq` is
-- COEFFICIENT-AGNOSTIC and is cited, not re-proved), and the `c`-line inverse bound at the
-- shifted height (`norm_muChiTw_LSeries_cline_le` — the B-probe's
-- `norm_LFunction_inv_cline_le` is uniform in the height, so the shift is free, and the tail
-- constant is `1 + log x` exactly as in the `q = 1` route: no `log⁷` tail friction).
--
-- ⟦THE REGION DISCHARGE, LANDED — the STONE-C RULING (i) pattern at both VK arms⟧
-- `LFunction_no_zero_in_box` / `LFunction_no_zero_in_shifted_box`: no zero of `L(·,χ)` in the
-- shallow box `Re ≥ 1 − boxWidth/2`, `|Im| ≤ H`.  Three-way height split: above the landed
-- floor the χ-VK region at BOTH arms (`LFunction_zero_free_region_vk` for `χ² ≠ 1`,
-- `LFunction_real_zero_free_region_vk` for `χ² = 1`), width transported DOWN to the box's top
-- height by `vkBoxWidth_le_of_le`; below the floor the classical explicit
-- `Salt.SW.zero_free_region_all'`, whose denominator is `≤ log q + exp 100 + 1` there
-- (`log_le_of_below_floor`); on the real axis the ξ₁ carve-out as a NAMED hypothesis (the
-- Siegel `∃H₀` fold is wave P-7's and is deliberately not folded here).
-- TWO findings worth banking: (a) the two VK arms' gates COLLAPSE to one `q`-only condition,
-- `log(20000(vkStripConst q + 8104)) ≤ 100·A`, because `log log|γ| ≥ 100` everywhere above the
-- floor; (b) the abscissa must sit at HALF the region width (`boxWidth_pos` is what makes the
-- box a contradiction) — at the full width the region bound and the box hypothesis are
-- consistent and nothing follows.
--
-- ⟦THE RESIDUE, STATED⟧ `LFunctionInvShallowVk` — the `L(·,χ)` analogue of the landed
-- `Salt.SW.zeta_inv_shallow`, moved from the classical width to the VK width.  It is the ONLY
-- open analytic input: `hzf` is landed above, `hbox` IS this Prop, and the contour shift +
-- budget + de-smoothing are line-for-line mirrors of `MobiusRateClose` (`MmuChiRate_residue`
-- records the exact remaining implication).  The file's §6 banks the route (the
-- Borel–Carathéodory factorization of `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled`, already
-- called by the B-probe, plus a Jensen zero count on the ball — the one missing input), the
-- DEAD END (anchor + Cauchy transport closes only for width `≲ 1/(q⁵(log γ)⁸)`, and the `q⁵`
-- alone destroys the saving at `q ≤ (log y)^12`), and the o(1) BUDGET: the delivered form is
-- `∀ A`, i.e. `c = ∞`-genre against the gate's `c ≥ 1.449`, so the budget clears with the
-- whole 0.29 of `o(1)` unspent — and the edge losses may be any fixed polynomial in `log q`
-- and `log H`, since the quasi-power saving `exp(−c(log x)^{1/4}/(log log x)⁴)` absorbs them.

open Salt.Tactic in
#audit_axioms Salt.MR.exp_phase_eq_cpow
  Salt.MR.chiBarTwist_eq_inv_mul_cpow
  Salt.MR.muChiTw
  Salt.MR.norm_muChiTw_le_one
  Salt.MR.MmuChi_eq_sum_muChiTw
  Salt.MR.LSeries_muChiTw_eq_LFunction_inv
  Salt.MR.Mmu1Chi
  Salt.MR.muChiTw_summable_dom
  Salt.MR.mmu1Chi_eq_integral_LSeries
  Salt.MR.mmu1Chi_eq_integral
  Salt.MR.norm_LFunction_inv_shifted_cline_le
  Salt.MR.norm_muChiTw_LSeries_cline_le
  Salt.MR.vkBoxWidth
  Salt.MR.clBoxWidth
  Salt.MR.boxWidth
  Salt.MR.boxWidth_pos
  Salt.MR.vkBoxWidth_le_of_le
  Salt.MR.log_le_of_below_floor
  Salt.MR.LFunction_no_zero_in_box
  Salt.MR.LFunction_no_zero_in_shifted_box
  Salt.MR.vkShallowWidth
  Salt.MR.vkShallowWidth_pos
  Salt.MR.LFunctionInvShallowVk
  Salt.MR.MmuChiRate_residue

-- ⟦THE HalaszIntegersChi DISCHARGE — ROUTE C, the φ-graded row⟧ (2026-07-29, KMT port wave
-- P-5; `HalaszIntegersChiClose`).
--
-- Wave P-6-E left `HalaszIntegersChi` as an honest NEW gap (the 𝒯_S branch's per-χ Halász row
-- for twisted integer sums).  The adjudication, first:
--
-- ⟦WHAT THE SLOT IS⟧ a DISCRETE MEAN-VALUE (Halász–Montgomery large-values) row over PAIRS,
-- for an ARBITRARY `a : ℕ → ℂ` — no multiplicativity, no support, no bound.  That single fact
-- kills both routes the freeze named:
-- * ROUTE A (the all-χ pretentious floors → `halasz_ball_decay`) is a CATEGORY MISMATCH: the
--   floors bound `pretDistSq (lamChi χ) (costwist v) X` from below and `halasz_ball_decay`
--   turns that into a DECAY statement for the summatory function of ONE multiplicative datum;
--   it cannot bound a mean square of an arbitrary Dirichlet polynomial over an ordinate set,
--   and the slot's `a` is the non-multiplicative Ramaré mask `ramRcoeff/m`.  This independently
--   re-derives REF-P-SHAPE's own R-P2 note ("the floor→Halász two-step is an INPUT to the
--   (χ,t) decomposition, never the row bound").  The `ellLin` pairing was checked and is
--   IRRELEVANT here — not a repairable type mismatch, the wrong genre of statement.
-- * ROUTE B (the χ-twisted μ-rate through O3's bridge) is a NON-ROUTE: `MmuChiRate` /
--   `LambdaChiSummatory` are rates for ONE datum at ONE height, and the slot quantifies over
--   all `a`, so no fixed-datum rate can enter.  No fake conditional was shipped.
--
-- ⟦THE DEMANDED GRADE, ARITHMETIC⟧ the slot is consumed ONLY at `ramRChi_sq_sum_le` →
-- `TSChi_branch_meansq` → `usetChi_TS_branch_meanvalue`, and only through `(M + |ℰ|√T) ≤ 2M`
-- (the razor clears `|ℰ|√T ≤ M`).  The `q = 1` twin `uset_TS_branch_meanvalue` exits at
-- `5128·ε²·M·(1+log 2T)·mass` with `ε = (log X)^{−100}`, so the demand is
-- `5128·(log X)^{−200}·M·(1+log 2T)·mass`.  The landed mean-value row
-- (`ramRChi_sq_sum_mvt`) carries `T` where the demand carries `M`, and at the §8.3 pins
-- `T/M ≍ e^{j/H} ≍ p` — the P-6-E gap report is CONFIRMED as a power-genre loss.
--
-- ⟦ROUTE C, TAKEN — UNCONDITIONAL⟧ `dpolyChi q (Icc 1 M) a χ = dpoly M (a·χ)` (`rfl`) and
-- `‖χ(n)‖ ≤ 1`, so the LANDED `q = 1` Lemma 9 (`halasz_integers_unconditional_const`,
-- constant 2564) applies on EVERY character fibre (`FibreWellSpaced` IS fibrewise
-- `WellSpaced`).  Summing over the `φ(q)` characters costs `φ(q)` on the LENGTH term and
-- NOTHING on the count term (`∑_χ |𝒯_χ| = |ℰ|` is an identity).  Exit:
-- `halaszIntegersChiPhi_holds : HalaszIntegersChiPhi 2564`.
--
-- ⟦THE DEBIT REPAID AT THE BRANCH⟧ `φ(q) ≤ q ≤ (log X)^12`, so re-pinning the branch level at
-- `ε_Q := (log X)^{−106}` gives `φ(q)·ε_Q² ≤ (log X)^{12−212} = (log X)^{−200}` —
-- `usetChi_TS_branch_exit_repinned` is then BYTE-FOR-BYTE the `q = 1` demand.  Price: `𝒯_L`
-- sees `V = (log X)^{106}` instead of `(log X)^{100}`, and its kill is a quasi-power
-- (`USetThinTL`, θ < 1/8) that beats any polylog.  Stated honestly: at MR's own level the
-- φ-graded exit is `(log X)^{−188}`, TWELVE POWERS SHORT — the re-pinning closes exactly those
-- twelve (`106·2 − 12 = 200`).
--
-- ⟦THE RESIDUE (STOP, reported)⟧ the LITERAL `φ(q)`-free `HalaszIntegersChi` is NOT proved and
-- cannot be obtained fibrewise (`∑_χ M = φ(q)M` is an identity, not slack).  The `φ`-free row
-- is the genuine HYBRID Halász–Montgomery estimate; its missing input is the off-diagonal Gram
-- entries `∑_{n≤M} χ(n)χ̄′(n)n^{i(t−t′)}` at `χ ≠ χ′` (Polyá–Vinogradov / hybrid large sieve).
-- TWO design notes: (a) that is a NEW stone, not a port composition; (b) the classical form of
-- that estimate carries `√(qT)`, not `√T`, in the count term — **the slot's literal statement
-- may itself need a `√q` amendment** (Fable/human tier; untouched here).  No consumer needs
-- it: every consumption factors through `usetChi_TS_branch_meanvalue`, whose demand the
-- re-pinned φ-graded exit meets exactly.

open Salt.Tactic in
#audit_axioms Salt.MR.card_chars_totient_real
  Salt.MR.halaszIntegersChi_fibre
  Salt.MR.halaszIntegersChi_phi
  Salt.MR.HalaszIntegersChiPhi
  Salt.MR.halaszIntegersChiPhi_holds
  Salt.MR.ramRChi_sq_sum_phi
  Salt.MR.TSChi_branch_meansq_phi
  Salt.MR.usetChi_TS_branch_meanvalue_phi
  Salt.MR.totient_le_logpow
  Salt.MR.phi_debit_level_repin
  Salt.MR.usetChi_TS_branch_exit_repinned
  Salt.MR.mvt_row_carries_T
  Salt.MR.phi_row_carries_M

-- ⟦O6 — THE g_r PERTURBATION (the Ramaré-weighted twisted datum)⟧ (2026-07-29, KMT port wave
-- P-5; `MobiusChiRamare`).
--
-- The freeze's O6: transfer the χ,t-twisted Möbius rate from the PLAIN datum to the
-- Ramaré-DAMPED one `μ(m)·r^{ω(m;P,Q)}`, and then to the WEIGHTED one `μ(m)/(ω(m;P,Q)+1)`.
--
-- ⟦THE CARRIER, VERIFIED (not assumed)⟧ `μ·g_r = μ ∗ w_r` with `w_r` the EXPLICIT closed form
-- `w_r n = (1−r)^{ω(n;P,Q)}` on window-smooth `n ≠ 0`, `0` otherwise (`ramTailWeight`; the
-- `n ≠ 0` guard is real, `primeFactors 0 = ∅` makes `0` vacuously smooth).  The closed form is
-- checked in TWO auditable halves, both proved: `ramTailWeight_prime_pow` (the coefficient is
-- `(1−r)` for EVERY `k ≥ 1` at a window prime and `0` off the window — literally the
-- coefficients of `(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)∑_{k≥1}p^{−ks}`) and
-- `ramTailWeight_eq_zeta_mul_muGr` (both sides multiplicative, matched at prime powers).
-- Free by-product: `ramTailWeight_eq_sum_divisors` (`w_r n = ∑_{d∣n} μ(d)r^{ω(d;P,Q)}`), the
-- alternative Möbius-transform carrier.  KEY POSITIVITY `ramTailWeight_nonneg` needs only
-- `r ≤ 1`, and `ramTailWeight_le_zero_param` makes `r = 0` the WORST CASE — which is what makes
-- every mass/tail hypothesis `r`-free and the `∫₀¹ dr` composition free.
--
-- ⟦THE FOLD⟧ `MmuGrChi_eq_sum` (UNCONDITIONAL): `∑_{m≤y} μ(m)g_r(m)χ̄(m)m^{it} = ∑_{b≤y}
-- w_r(b)χ̄(b)b^{it}·M_{μχ̄}(⌊y/b⌋)`, through the new `MmuChi_inner_dvd` (the general-divisor
-- twin of the landed `MmuChi_inner`).
--
-- ⟦THE HONEST LOSS — where O6 can fail, and it is NOT hidden⟧ the small range `b ≤ √y` costs
-- the ℓ¹(1/n) MASS, and at `r = 0` the mass is `∏_{P≤p≤Q}(1−1/p)^{−1}`, whose log is the
-- LANDED `blockWindow_mertens_const` (`CofactorDist.lean:139`) — i.e. `≍ log Q/log P`, exactly
-- the freeze's O6 shape.  The large range `b > √y` has only the crude `‖M_{μχ̄}(z)‖ ≤ z`, so it
-- costs `y·∑_{b>√y} w_r(b)/b`, and THAT is carried as a NAMED in-statement hypothesis pinned at
-- `(log y)^{−A}`.  Rankin gives it when `log Q ≪ (log y)^{1−δ}` and NOT when `log Q ≍ log y`;
-- the consumer pays it where it knows `P,Q`.  The mass stays inside `log Q/log P`; the tail is
-- the undischarged row, by design and stated as such.
--
-- ⟦PRICES⟧ conductor `(log y)^12 → (log y)^11` (the `MlambdaChi_rate` pattern, `log y ≥ 4^12`);
-- height `|t| ≤ y → |t| ≤ ⌊√y⌋` sharply (`Nat.sqrt y ≤ y/b` for `b ≤ √y`); the log-scale factor
-- `4^A` from the landed `Salt.TwinBar.log_natSqrt_ge`.  `C'` and `x₀` are INDEPENDENT of
-- `r, P, Q, q, χ, t` — which is precisely why item 5 (`MmuRamChi_rate`, the `∫₀¹ dr`
-- composition through the landed `integral_cpow_unit` + `ramR_norm_le_of_damp_le` pattern) is
-- free.  DEVIATION: `mul_apply_mul_twist` is CITED, not instantiated — the carriers here are
-- `ArithmeticFunction ℝ` (so `w_r ≥ 0` is first-class) while the twist is ℂ-valued, so
-- `muGr_twist_eq_sum_divisorsAntidiagonal` calls `chiBarTwist_mul` directly (the same analytic
-- content, ~15 lines of bookkeeping, documented in place).

open Salt.Tactic in
#audit_axioms Salt.MR.muGr
  Salt.MR.muGr_isMultiplicative
  Salt.MR.WindowSmooth
  Salt.MR.ramTailWeight
  Salt.MR.ramTailWeight_apply_of
  Salt.MR.ramTailWeight_eq_zero_of_not_smooth
  Salt.MR.ramTailWeight_nonneg
  Salt.MR.ramTailWeight_support
  Salt.MR.ramTailWeight_zero_param
  Salt.MR.ramTailWeight_le_zero_param
  Salt.MR.ramTailWeight_isMultiplicative
  Salt.MR.ramTailWeight_prime_pow
  Salt.MR.ramTailWeight_eq_zeta_mul_muGr
  Salt.MR.ramTailWeight_eq_sum_divisors
  Salt.MR.mu_mul_ramTailWeight
  Salt.MR.muGr_eq_sum_divisorsAntidiagonal
  Salt.MR.MmuGrChi
  Salt.MR.muGr_twist_eq_sum_divisorsAntidiagonal
  Salt.MR.MmuChi_inner_dvd
  Salt.MR.MmuGrChi_eq_sum
  Salt.MR.norm_MmuGrChi_le_split
  Salt.MR.MmuGrChi_rate
  Salt.MR.MmuRamChi
  Salt.MR.MmuRamChi_eq_integral
  Salt.MR.norm_MmuRamChi_le_of_uniform
  Salt.MR.MmuRamChi_rate

-- ⟦D1 + D2 — THE TWISTED EDGE and the ψ-twisted window price⟧
-- (2026-07-29, KMT port wave P-6-EDGE; `TwistedEdge`).
--
-- Stone C's pinned STOP closed.  `twisted_edge_price_strip` bounds `‖L′/L(x+iγ, ψ)‖` on the whole
-- near-1-line strip `|x − 1| ≤ (c_vk/2)/D₄(5T+1)` at every contour height `|γ| ≤ 5T`, by
-- `CE·D₅(5T+1)` — one `loglog` above the split's `D₄` depth, exactly as ζ's `D₄` price sits above
-- its `D₃` depth (`shifted_edge_price_strip`).  `twisted_window_price_gated_holds` then discharges
-- the residue interface.
--
-- ⟦THE THREE STRUCTURAL SAVINGS (all from the B-probe's finding)⟧
-- (a) `near_norm_logDeriv_entire_le` is `near_norm_logDeriv_Zc_le` with the base function FREE:
-- `L(·,ψ)` is entire for `ψ ≠ 1`, so the whole `Zc = (·−1)ζ` normalization and every `1/(z−1)`
-- correction VANISH, and the disc's reference floor is the probe's twisted Möbius bound
-- (`norm_LFunction_inv_cline_le` through `LFunction_ratio_bound`), not the pole's neighbourhood.
-- (b) ONE disc engine serves both height regimes (`twisted_disc_engine`, scale `Θ`, growth ceiling
-- `M`, output `(140/Θ)·log(20M/Θ) + (log(20M/Θ)/log(7/6))/w`): above stone C's exact floor
-- `exp(exp 100) + 1` it is fed stone A's box growth made TWO-SIDED (`vk_char_box_growth_abs` — the
-- strip bound already reads `|T|`, so ζ's conjugation leg is not needed, and no second region
-- hypothesis for `ψ⁻¹` is incurred); below the floor it is fed the EFFECTIVE crude ceiling
-- `LFunction_crude_growth` (`‖L(z,ψ)‖ ≤ 1 + q(1+3‖z‖)` on `Re z ≥ 1/2`, from the `N = 1`
-- truncation `Salt.SW.norm_LFunction_sub_partial_le` at the level bound `q`).  **ζ's below-floor
-- leg uses the NON-EFFECTIVE `logDeriv_Zc_compact_bound`; the twisted side does not** — its
-- moderate-height constant `twistedEdgeLowConst` is a closed form.
-- (c) RES/POLE-ROW have no twin: the shifted rectangle carries no interior pole, so
-- `pole_residue_term` is replaced by plain Cauchy–Goursat and the main term `windowKernel P 1 u`
-- disappears from the price.  The LEFT edge also loses ζ's `1/w` pole charge.
--
-- ⟦THE ONE HONEST NEW GATE (the deviation from stone C's pin, recorded)⟧
-- The price constant is absolute only under `8·log(40000·vkStripConst q) ≤ loglog(5T+1)`, i.e.
-- `log q ≲ loglog(5T+1)/8`.  This is EXACTLY ζ's own absorption: ζ hides `log(20000·K)` inside its
-- height floor `exp(exp(8 log(20000 K) + 1100))` because `K` is absolute; with `K` replaced by the
-- `q`-dependent `vkStripConst q = 5000 q` the same absorption becomes a `q`-vs-`T` gate, and it is
-- NOT absorbable into a constant — the depth `D₄` and the price `D₅` differ by exactly one
-- `loglog`, which is the entire budget `log q` must fit into.  It is the gate stone C's §4
-- docstring already predicted for the region's `A`-absorption (`log q ≤ K·loglog(q(5T+1))`,
-- `K ≈ 19`; at the port's parameters `12·loglog H ≤ K·loglog X`), so the edge consumes the SAME
-- one, and `twisted_gate_of_height` exhibits it as one extra `T`-floor per modulus.
-- **Consequence: `TwistedWindowPrice` as literally pinned (constants outermost, no `q`-dependence,
-- `hreg` the only hypothesis) is NOT dischargeable; `TwistedWindowPriceGated` — its body plus this
-- single gate — is, and is what P-7 should consume.**
--
-- ⟦WHAT IS CITED, NOT RE-PROVED⟧ `lambda_window_rep_chi` (REP-χ), `primeWindow_contour_rep` and
-- `rep_truncated` (generic in the coefficient), `sum_vonMangoldt_cline_bound`,
-- `truncKernel_const_le`, `norm_windowKernel_le`, `windowMellin_differentiableAt` — all
-- character-blind (`‖ψ(n)‖ ≤ 1`), exactly as stone C's finding said.
--
-- ⟦RESIDUE FOR P-7⟧ D3 (the `(χ,t)`-pair twin of `dual_core`: the fibre-split `44π·P` pole row via
-- `pole_row_sum` on `FibreWellSpaced` fibres, every cross-character row into the `error_double_row`
-- slot, plus the `p ∣ q` Euler debit on the diagonal fibres) is NOT attempted here.
open Salt.Tactic in
#audit_axioms Salt.MR.near_norm_logDeriv_entire_le
  Salt.MR.vk_char_box_growth_abs
  Salt.MR.LFunction_crude_growth
  Salt.MR.twisted_disc_engine
  Salt.MR.twisted_zfree_of_margin
  Salt.MR.twisted_edge_disc_core
  Salt.MR.twistedEdgeLowConst
  Salt.MR.twistedEdgeLowConst_pos
  Salt.MR.twisted_edge_moderate
  Salt.MR.twisted_edge_price_strip
  Salt.MR.twisted_dirichlet_cline
  Salt.MR.norm_logDeriv_LFunction_cline_le
  Salt.MR.logDeriv_LFunction_shift_differentiableOn
  Salt.MR.TwistedWindowPriceGated
  Salt.MR.twisted_gate_of_height
  Salt.MR.twisted_window_price_gated_holds

-- ⟦THE SHALLOW SLOT — DISCHARGED at the CORRECTED width⟧ (2026-07-29, KMT port closing wave;
-- `LFunctionInvShallow`).  P-5's last named analytic stone, with two findings.
--
-- ⟦FINDING 1 — THE JENSEN COUNT IS UNNECESSARY⟧ P-5's §6 named "a Jensen zero count
-- `∑ m ≲ log 4M₀` on the ball" as the one missing input.  It is missing because it is not
-- needed: the Landau/Borel–Carathéodory ball can be taken ENTIRELY INSIDE the zero-free region
-- (radius `η + W` about `(1+W)+it`, `η = boxWidth/2`), and then
-- `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled`'s zero set is EMPTY, so the product factor and
-- its count vanish.  `norm_LFunction_inv_shallow_of_ball` (§1) is the whole analytic core: one
-- mean-value transport of `log‖L‖` along `[1−W, 1+W] + it` against `‖logDeriv h‖ ≤
-- (120/λ)log(4M₀)`, anchored at the LANDED `LFunction_near_one_lower` (`‖L((1+W)+it,χ)‖ ≥ W/32`,
-- every χ, no region).  The stone was substantially cheaper than feared.
--
-- ⟦FINDING 2 — `LFunctionInvShallowVk` AS STATED IS NOT PROVABLE (two independent lines)⟧
-- (a) THE WIDTH.  The transport distance is `2W` and the BC cost is `(120/λ)log(4M₀)` per unit
-- length with `λ ≍ η`, so the loss is `O(1)` iff `W ≲ η/log(4M₀)`, and
-- `log(4M₀) ≍ log q + log log H` (the growth `vkStripConst q(1+log H)` gives `log q`; the
-- reference `W` gives `log log H`).  `vkShallowWidth c₄ q H` is a CONSTANT multiple of `η`, so
-- the requirement becomes `c₄·(log q + log log H) ≤ C′` — FALSE for every `c₄ > 0`.  The repair
-- is one extra `(log q+1)` and one extra `log log H`: `vkShallowWidthSharp` — and it is the SAME
-- price the landed `q = 1` twin `zeta_pow_lower` pays (its `ℓ⁴ = ℓ³·ℓ`, "3 (region) + 1 (the
-- `w = η/ℓ` cut)").
-- (b) THE CARVE-OUT.  The stated ξ₁ hypothesis `ρ.re < 1 − vkShallowWidth c₄ q H` has NO
-- margin: a real zero at `1 − W − ε` satisfies it for every `ε > 0` while `‖1/L((1−W)+i0)‖ ≥
-- c/ε`.  §5 states it at the region-scale `vkShallowWidth (10⁻⁶) q H` (which dominates
-- `boxWidth`, `boxWidth_le_carve`), and `carve_of_half` shows P-7's own `Re < 1/2` Siegel fold
-- covers that — so the amendment costs the consumer nothing on this side either.
--
-- ⟦WHAT LANDS⟧ `lFunctionInvShallowVkSharp_holds` : `LFunctionInvShallowVkSharp` — the slot
-- VERBATIM except for those two changes, `m = 2`, `K = 22528/c₄`.  Growth on two arms matching
-- §5's region split (`vk_char_strip_growth` above the VK floor, `LFunction_norm_le_level` below
-- it, where `‖z‖ ≤ e^{e^100}+4` is a constant); the region via `LFunction_no_zero_in_box` at box
-- height `H+1`; `boxWidth_shallow_lower` pins the min-of-three arms from below (the classical
-- arm's `exp 100` is paid by `log(H+1)^{3/4} ≥ exp 75`); `log_budget_bound` is the honest
-- `log(4M₀)` accounting; `exists_shallowConst` supplies the `c₄`-gate witness (`c·log(1/c) → 0`
-- with an explicit `x²/16`).
--
-- ⟦THE BUDGET SURVIVES⟧ at the consumer's parameters (`q ≤ (log x)^12`, `log H ≤ 2 log x`) the
-- corrected width gives the saving `exp(−c(log x)^{1/4}/(log log x)⁶)` in place of
-- `exp(−c(log x)^{1/4}/(log log x)⁴)` — still a quasi-power, still `o((log x)^{−A})` for EVERY
-- fixed `A`, so the `∀A` form and the whole 0.29 of the `o(1)` budget stand; only the finite
-- crossover moves (`10^{77} → 10^{90}`-genre), and `MmuChiRate`'s `∃x₀` absorbs it.
--
-- ⟦RESIDUE⟧ `MmuChiRate_residue_sharp`: the ξ₁/Siegel fold (P-7's, unchanged) plus the
-- mechanical `Salt.SW.MobiusRateClose` mirror read at `vkShallowWidthSharp`.  Still open and
-- named: the `χ₀`/`q = 1` row (the pole forces the `Zc`-normalized twin of §1 plus a compact
-- patch at `s = 1`; the slot's own statement excludes `χ = 1`, so this is P-5's gap unchanged).
open Salt.Tactic in
#audit_axioms Salt.MR.norm_LFunction_inv_shallow_of_ball
  Salt.MR.LFunction_ne_zero_of_shallow_ball
  Salt.MR.shallowGrowth
  Salt.MR.one_le_shallowGrowth
  Salt.MR.norm_LFunction_le_shallowGrowth
  Salt.MR.vkShallowWidthSharp
  Salt.MR.vkShallowWidthSharp_le
  Salt.MR.shallowA
  Salt.MR.one_le_shallowA
  Salt.MR.shallowA_gate
  Salt.MR.shallowA_lb
  Salt.MR.shallowA_ub
  Salt.MR.boxWidth_shallow_lower
  Salt.MR.log_budget_bound
  Salt.MR.boxWidth_le_carve
  Salt.MR.norm_LFunction_inv_shallow_sharp
  Salt.MR.sq_div_sixteen_log_le
  Salt.MR.exists_shallowConst
  Salt.MR.LFunctionInvShallowVkSharp
  Salt.MR.lFunctionInvShallowVkSharp_holds
  Salt.MR.carve_of_half
  Salt.MR.MmuChiRate_residue_sharp

-- ## `Salt/MR/MobiusChiRateClose.lean` — ⟦THE MIRROR⟧ the χ-twisted Möbius rate
--
-- The closing wave of the KMT port's centerpiece: `Salt.SW.MobiusRateClose` re-run at `L(s,χ)`.
-- §1 `mmu1Chi_contour_shift` — the residue-free twisted contour shift, PARAMETRIZED by an
-- analytic carrier `g` agreeing with `s ↦ (L(s − it, χ⁻¹))⁻¹` on the `c`-line (so the same
-- theorem serves the non-principal row, where the carrier IS that inverse, and the principal
-- row, where it is the pole-normalized continuation).  The `c`-line constant is the landed
-- height-uniform `norm_LFunction_inv_shifted_cline_le`, so the ζ route's `log⁷` tail friction
-- never appears.  §2 `mmu1Chi_rate_of_pinned` — the budget at the PINNED parameters
-- (`L = log x`, `s = L^{1/10}`, `T = e^s`, `c = 1 + 1/L`, `H = 2x`, `σ₀ = 1 − pinW c₅ H`), with
-- `pinW c₅ H = c₅/((log H)^{3/4}(log log H)⁶)`: the `⁶ = 4 + 2` is `vkShallowWidthSharp`'s own
-- `⁴` plus the conductor gate spent ONCE (`logq_le_thirteen`: `q ≤ (log x)^{12}` gives
-- `(log q + 1)² ≤ 169(log log H)²`), which is what makes every constant UNIFORM in `q, χ, t`.
-- §3 `mmuChiRate_of_smoothed` — the ℂ-valued two-point Riesz de-smoothing (`‖·‖` for `|·|`; the
-- twisted datum is not real), stated with a free side condition `P q χ` so the two rows share it.
--
-- ⟦D1⟧ `mmuChiRate_nonprincipal` — the `χ ≠ 1` row of `MmuChiRate` at the ⟦D1⟧-amended gates,
-- CONDITIONAL ONLY on the ξ₁/Siegel carve-out in the strong `Re < 1/2` form (P-7's fold).  The
-- edge bound is the landed `lFunctionInvShallowVkSharp_holds` at `H = 2x`; the zero-freeness is
-- the landed `LFunction_no_zero_in_shifted_box`; the two width comparisons (`pinW_le_sharp`,
-- `pinW_le_boxWidth_half`) are the only new arithmetic, and the HALF in the second is
-- `boxWidth_pos`'s own price.
--
-- ⟦D2⟧ `mmuChiRatePrincipal_of_zetaShallow` — the `χ₀` row from ONE analytic `Prop`.  The route
-- is the Euler product, not inclusion–exclusion: `L(s,1) = P_q(s)·ζ(s)` (mathlib's
-- `LFunctionTrivChar_eq_mul_riemannZeta`) makes the carrier
-- `g s = mmuG(s − it)·(P_q(s − it))⁻¹` with `Salt.SW.mmuG` the landed continuation of `1/ζ`
-- through the pole, and the Euler factor is FREE: `‖P_q(s)⁻¹‖ ≤ 4^{ω(q)} ≤ q² ≤ (log H)^{24}`
-- on `Re ≥ 3/4` (`norm_eulerFac_inv_le`, `two_pow_omega_le`).  **The finding worth banking: the
-- divisor/inclusion–exclusion route is STRICTLY WORSE — the Dirichlet inverse of `μ·χ₀` over the
-- divisors of `rad q` is `n ↦ [n ∣ q^∞]`, i.e. a sum over ALL `q`-smooth-supported `n ≤ y`, not
-- over `d ∣ rad q`.**
--
-- ⟦THE RESIDUE⟧ `ZetaInvShallowVk` — the ζ twin of `lFunctionInvShallowVkSharp_holds` at the
-- SAME sharp width read at `q = 1`.  Its first conjunct (the box is ζ-zero-free) is a
-- composition of landed material (`Salt.Vk.zeta_zero_free_region_pow` above the floor, the
-- classical region below); its SECOND conjunct — `‖mmuG(σ+iτ)‖ ≤ K(log H)^m` on the shallow box
-- — is the one open stone.  Why the corpus does not already have it: `Salt.SW.zeta_inv_shallow`
-- is at the CLASSICAL width `c₄/log⁹(|t|+2)`, worth only `|t| ≤ exp((log y)^{1−δ})` of height,
-- and the landed `zeta_pow_lower` / `zeta_lower_all_t` are at VK width but only on `Re ≥ 1` —
-- a lower bound to the RIGHT of the 1-line, and the Cauchy/MVT transport to `Re = 1 − w` costs
-- a full power of `log H` in the width, which kills the saving at `|t| ≍ y`.  The route is §1 of
-- `LFunctionInvShallow` at the `Zc` normalization (`Zc` entire, `Zc 1 = 1`, and the RATIO
-- `‖c−1‖/‖s−1‖ ≥ 1/2` kills the pole factor), growth from `Salt.Vk.zeta_growth_pow`, floor from
-- the landed `Salt.MR.zeta_pow_lower_far` (`‖ζ((1+d')+iτ)‖ ≥ d'/32`, the exact ζ analogue of
-- `LFunction_near_one_lower`); below the VK floor everything is a CONSTANT (no `q`, so no
-- Pólya–Vinogradov arm).  `Salt.MR.zeta_near_bound_core` is the closest landed relative and is
-- `private`, hence not reusable across modules as written.
--
-- The deliverables: `mmuChiRate_of_carve_and_zetaShallow : MmuChiRate` and
-- `lambdaChiSummatory_of_carve_and_zetaShallow : LambdaChiSummatory A`, both from exactly the
-- two named inputs (the ξ₁ fold + `ZetaInvShallowVk`).
--
-- ⟦THE RESIDUE, DISCHARGED⟧ `Salt/MR/ZetaInvShallow.lean` — `zetaInvShallowVk_holds`.  The ζ
-- twin is LANDED, so the χ₀ row is unconditional (`mmuChiRatePrincipal_holds`) and the mirror's
-- deliverables now read from ONE input: `mmuChiRate_of_carve` / `lambdaChiSummatory_of_carve`
-- take only the ξ₁/Siegel carve-out.  What the discharge actually cost, recorded because the
-- accounting is the finding:
--
-- 1. the first conjunct is a COMPOSITION, as predicted: `zeta_zero_free_region_pow` above the
--    power region's floor `T₀` (its width is antitone in the height, so the value read at `H+1`
--    serves the whole box) and the classical `Salt.SW.zeta_zero_free_region` below it, where
--    `c₃/log(T₀+2)` is a CONSTANT — folded into the single scale constant
--    `cR = min 1 (min c_pow (c₃/(2 log(T₀+2))))`;
-- 2. the near-pole corner needed NO new analysis.  Split the heights at the CONSTANT
--    `T₁ = T₀+t₀+4`: for `|τ| ≤ T₁` the landed `Salt.SW.zeta_inv_shallow` applies verbatim (its
--    classical width `c₄'/log⁹(|τ|+2)` and its value `C log⁷(|τ|+2)` are both constants there,
--    and its own `Zc_patch_lower` already owns the pole; at `s = 1`, `mmuG 1 = 0`).  So the
--    `private zeta_near_bound_core` did NOT have to be re-proved — that was the one banked
--    worry, and it evaporates once the height split is made at a constant rather than at `H`;
-- 3. the pole cancels exactly as banked, and the mechanism is worth naming: the Landau core
--    only ever sees the RATIO `‖Zc z/Zc c‖`, and on the ball `‖z−1‖ ≤ ‖c−1‖ + 1/8 ≤ 2‖c−1‖`
--    because `‖c−1‖ ≥ |τ| ≥ 2`.  Hence `M₀ ≤ 64·Kg·log(H+1)/W` — the `|τ| ≍ H` factor is GONE,
--    and `log(4M₀) ≍ loglog H` (`zeta_budget_log_bound`), which is what the sharp width's
--    fourth `loglog` divides out.  Had the ceiling entered as `sup‖Zc‖/floor` instead, the
--    budget would have carried `log H` and demanded width `≪ L^{-7/4}` — the route would die;
-- 4. the ball scale is `λ = cR/(10⁵ L^{3/4} ℓ³)`, a fixed fraction of the region's own width
--    shape, and the FOUR constraints (reach `2W ≤ 23λ/20`, the growth strip `7λ/4 ≤ vkTheta(H+1)`,
--    the region depth `3λ/2 < cR/(16 L^{3/4}ℓ³)`, the classical leg) are each one `min` arm.
--    The `c₄·log(1/c₄)` gate is `exists_zetaShallowGate` over the landed `sq_div_sixteen_log_le`.
--
-- Realized shape: `m = 5`, `K = 256/c₄ + C·log⁷(T₁+2)`, via `L^{3/4}ℓ⁴ ≤ L⁵` (`ℓ ≤ L`) — the
-- exponent is design-grade slack, only the WIDTH shape is load-bearing downstream.

open Salt.Tactic in
#audit_axioms Salt.MR.mmu1Chi_contour_shift
  Salt.MR.pinT
  Salt.MR.pinW
  Salt.MR.mmu1Chi_rate_of_pinned
  Salt.MR.pin_scale_facts
  Salt.MR.logq_le_thirteen
  Salt.MR.pinW_le_sharp
  Salt.MR.pinW_le_boxWidth_half
  Salt.MR.TsumChi
  Salt.MR.x_mul_Mmu1Chi
  Salt.MR.MmuChi_split
  Salt.MR.TsumChi_split
  Salt.MR.desmooth_identity_chi
  Salt.MR.remainder_bound_chi
  Salt.MR.mmuChiRate_of_smoothed
  Salt.MR.XiCarveWidth
  Salt.MR.xiCarveWidth_of_half
  Salt.MR.mmuChiRate_nonprincipal
  Salt.MR.MmuChiRatePrincipal
  Salt.MR.mmuChiRate_of_rows
  Salt.MR.mmuChiRate_of_carve_and_principal
  Salt.MR.lambdaChiSummatory_of_carve_and_principal
  Salt.MR.eulerFac
  Salt.MR.eulerFac_differentiable
  Salt.MR.norm_one_sub_prime_cpow_ge
  Salt.MR.one_le_pow_mul_norm_eulerFac
  Salt.MR.eulerFac_ne_zero
  Salt.MR.two_pow_omega_le
  Salt.MR.norm_eulerFac_inv_le
  Salt.MR.ZetaInvShallowVk
  Salt.MR.pinW_le_quarter
  Salt.MR.mmuChiRatePrincipal_of_zetaShallow
  Salt.MR.mmuChiRate_of_carve_and_zetaShallow
  Salt.MR.lambdaChiSummatory_of_carve_and_zetaShallow
  Salt.MR.vkShallowWidthSharp_one
  Salt.MR.exists_zetaShallowGate
  Salt.MR.zeta_shallow_scales
  Salt.MR.zeta_budget_log_bound
  Salt.MR.mmuG_eq_zeta_inv'
  Salt.MR.norm_mmuG_neg_im
  Salt.MR.norm_Zc_lower_of_shallow_ball
  Salt.MR.norm_Zc_ratio_le_of_shallow_ball
  Salt.MR.norm_mmuG_shallow_far
  Salt.MR.norm_mmuG_shallow_near
  Salt.MR.zeta_no_zero_in_shallow_box
  Salt.MR.zetaInvShallowVk_holds
  Salt.MR.mmuChiRatePrincipal_holds
  Salt.MR.mmuChiRate_of_carve
  Salt.MR.lambdaChiSummatory_of_carve

-- ## `Salt/MR/PortAssembly.lean` — ⟦WAVE P-7: THE ASSEMBLY⟧ the `(χ,t)`-pair dual + the Siegel fold
--
-- ⟦A1 — STONE C's RESIDUE DISCHARGED⟧ `halaszPrimesChiGated_of_price` :
-- `USetChi.HalaszPrimesChi`'s conclusion with the diagonal term `P`, NOT `φ(q)·P`.  THE FINDING
-- that makes the `φ(q)` disappear: `halasz_primes_chi_fibres` pays it because on the PRIMAL side
-- each fibre's bound reads the FULL coefficient mass, so `φ(q)` fibres multiply the diagonal; on
-- the DUAL side (`dual_core_pair`) the pole row is charged against the FIBRE's own mass
-- (`pole_double_row_fibre` = `pole_row_sum` once per `FibreWellSpaced` fibre) and the fibre masses
-- ADD UP.  "The `44π·P` paid once per fibre" is therefore a statement about WHICH SIDE of the
-- duality the pole row is priced on — not about slack.  Cross-character pairs carry
-- `ψ = χ_r·χ̄_{r'} ≠ 1`, where `L(·,ψ)` is entire and `TwistedWindowPriceGated` supplies the EDGE
-- price with no pole; they go into `error_double_row_gen`'s slot.
--
-- ⟦THE DIAGONAL FIBRES' EULER DEBIT⟧ on a diagonal pair `ψ = χ·χ⁻¹ = 1` is the PRINCIPAL character
-- mod `q`, not the trivial character of modulus 1, so the diagonal window sum is
-- `∑_{(n,q)=1}Λ(n)n^{iu}w(n)` and comparing with `per_pair_contour`'s untwisted sum costs the
-- `p ∣ q` mass.  `norm_principal_sub_untwisted_le` prices it at `(log₂⌊3P⌋+1)·log q` by the DIVISOR
-- route (`vonMangoldt_sum` on the divisors of `q^K`, `K = log₂⌊3P⌋+1`: every non-unit `n ≤ N` with
-- `Λ(n) ≠ 0` is `p^k` with `p ∣ q`, `2^k ≤ N`, hence divides `q^K`).  The
-- `neg_re_logDeriv_trivChar_le_zeta` route prices the Euler PRODUCT on `Re s > 1` — a different
-- object; the window sum needs this finite-sum form.  The debit is absorbed with a full `√P` to
-- spare (`natLog2_floor_le_sqrt` + `√P ≤ P·exp(−c log P/D₄)`).
--
-- ⟦THE GATES (never absorbed — the law)⟧ `HalaszPrimesChiGated` = the socket's conclusion plus
-- (1) the twisted edge's `q`-scale gate and (2) the region at `c_vk`.  Both are `q`-dependent, so
-- neither fits the socket's uniform `T₀`: that is the honest shape of the port's pair row.  Two new
-- absorptions: `D4_5T1_le_D4` (`K₄`) and `D5_5T1_le` (`K₅`, the extra `loglog` priced by
-- `log u ≤ 4u^{1/4}`); `c = min(c_vk/(2K₄), c₀/(2Cκ), 1/10)`.
--
-- ⟦A2 — THE SIEGEL FOLD, AND THE ADJUDICATION THAT SHAPES IT⟧ **the STRONG carve-out
-- `∀ real zero, Re ρ < 1/2` — carried by `mmuChiRate_of_carve`, `lambdaChiSummatory_of_carve`,
-- `carve_of_half` and `twisted_rect_zero_free_split`'s `hcarve` — IS NOT A SIEGEL STATEMENT AND
-- CANNOT BE FOLDED INTO AN `∃H₀`**: it says `L(s,χ)` has no real zero in `[1/2,1)`, a fragment of
-- GRH (Chowla's conjecture at real `χ`), and no threshold in `H` and no `q`-range weakens it (one
-- hypothetical real zero at `β = 0.9` for one fixed small `q` refutes it for every `H₀`).  What IS
-- foldable — and what every consumer actually needs — is the WIDTH form: `carve_of_half`
-- immediately drops `Re < 1/2` to `Re ρ ≤ 1 − vkShallowWidth(10⁻⁶) q H`, and the region uses
-- `1 − 10⁻⁸/D₄(5T+1)`; both are `≍ (log H)^{−3/4−o(1)}`, and at `q ≤ (log H)^{12}` Siegel at
-- `ε = 1/16` beats them (`16 = 12/(3/4)`; an effective Page bound gives `q^{−1/2}`, i.e.
-- `(log H)^{−6}`, losing by `(log H)^{5.25}` — which is exactly why the arc's `12` forces Siegel).
-- `siegel_real_carve` is that fold: `∃K > 0` INEFFECTIVE (the port's ONE ineffective constant) with
-- `q^{1/16}·W ≤ K ⟹` no real zero of `L(·,χ)` reaches `1 − W`.  Real characters go through the
-- landed ε-quantified `Salt.SW.siegel_theorem` on the primitive character; NON-real characters need
-- NO Siegel (`zero_free_region_all'`, carve-out satisfied by the left disjunct, at the cost
-- `log 2q ≤ 32q^{1/16}`).
--
-- ⟦A2's DELIVERABLE⟧ `twisted_rect_zero_free_siegel` — stone C's split with `hcarve` REPLACED by
-- one `q`-vs-`T` Siegel gate.  The re-derivation is cheap and legitimate because the landed split
-- applies `hcarve` to exactly ONE zero (the `ρ` it is handed) and `zero_free_region_all'` is itself
-- per-`ρ`: for `Im ρ ≠ 0` the right disjunct is free, and the only carved corner is the REAL zero,
-- which §7 kills.  Above the height floor the VK arms take no carve-out at all.
--
-- ⟦§9 — THE COMPOSITION⟧ `halasz_primes_chi_pair_of_gates`: the pair socket with the region
-- discharged, in front of FOUR gates (edge `q`-scale; the region's `A`-absorption at
-- `A := 1 + log(20000(Cq+8104))/100`; the below-floor comparison `Kq`; the Siegel gate `Ks`) and
-- nothing else.  It takes the edge price at the LITERAL width `1/10⁸` —
-- `twisted_edge_price_strip` proves exactly that (TwistedEdge.lean:895) and
-- `twisted_window_price_gated_holds` passes the same constant through, but both hide it behind
-- `∃ c_vk`, so the kernel cannot see that it matches the region's own `1/10⁸`.
--
-- ⟦NOT BUILT (the honest STOP)⟧ A3 (the 𝒰-exit compose) and A4 (`M4ChiSummedFreeRow`): the socket
-- discharge is one composition further on, and the rate chain's `hxi` is still stated at
-- `Re < 1/2`.  Owed, both Fable-tier statement changes: (i) restate `hxi` at the width (what
-- `mmuChiRate_nonprincipal` already consumes via `carve_of_half`); (ii) expose `c_vk = 1/10⁸` in
-- the edge's `∃`.
open Salt.Tactic in
#audit_axioms Salt.MR.sum_vonMangoldt_nonunit_le
  Salt.MR.window_lambda_support
  Salt.MR.summable_window_lambda_chi
  Salt.MR.norm_principal_sub_untwisted_le
  Salt.MR.error_double_row_gen
  Salt.MR.wellSpaced_fibre
  Salt.MR.pole_double_row_fibre
  Salt.MR.pair_phase_conj
  Salt.MR.dual_core_pair
  Salt.MR.conj_pairMatrix
  Salt.MR.primal_of_dual_pair
  Salt.MR.loglog5_le
  Salt.MR.K₄
  Salt.MR.D4_5T1_le_D4
  Salt.MR.K₅
  Salt.MR.D5_5T1_le
  Salt.MR.natLog2_floor_le_sqrt
  Salt.MR.HalaszPrimesChiGated
  Salt.MR.absorb_exp_term
  Salt.MR.halaszPrimesChiGated_of_price
  Salt.MR.siegel_real_carve
  Salt.MR.twisted_rect_zero_free_siegel
  Salt.MR.halasz_primes_chi_pair_of_gates

-- ## `Salt/MR/PortClose.lean` — ⟦WAVE CLOSE⟧ the two ruled exposures, fired
--
-- ⟦R-1 — THE RATE CHAIN'S `hxi`, RESTATED AND DISCHARGED⟧ P-7 ruled the STRONG carve-out
-- (`Re ρ < 1/2` at every real zero) unfoldable — it is a GRH fragment — and the WIDTH form
-- foldable.  The restatement is in the landed files (`MobiusChiRateClose.XiCarveWidth` + the
-- five wrappers + `ZetaInvShallow`'s two); `xiCarveWidth_of_half` records that the old shape
-- still implies the new one, so nothing provable was lost.  `xiCarveWidth_of_siegel` then
-- DISCHARGES it: at `q ≤ (log H)^{12}` the gate `q^{1/16}·vkShallowWidth(10⁻⁶) q H ≤ K`
-- collapses to `10⁻⁶/((log q+1)(loglog H)³) ≤ K` because `q^{1/16} ≤ (log H)^{3/4}` cancels
-- the width's own leading factor — `16 = 12/(3/4)` — and only `loglog H ≥ 1/K` is asked of
-- `H`.  **THE ADJUDICATION: the Siegel gate does NOT ride as a hypothesis.**  The threshold
-- `H₀ = max(exp(exp 100)+3, exp(exp(1/K)))` is ineffective (Siegel's `K` is), and it folds
-- into the `∃ x₀` that `MmuChiRate` already carries.  So `mmuChiRate_holds_gated : MmuChiRate`
-- and `lambdaChiSummatory_holds_gated` are UNCONDITIONAL: the port's centerpiece — the
-- χ-twisted, `t`-uniform Möbius rate at `q ≤ (log y)^{12}`, `|t| ≤ y` — is in the kernel, with
-- `C` and the `(log y)^{−A}` decay effective and only the threshold ineffective.
--
-- ⟦R-2 — `c_vk = 1/10⁸`, EXPOSED⟧ `twisted_edge_price_strip` gained the conjunct
-- `c_vk = 1/10^8` (the value its own `refine` supplies) and `twisted_window_price_gated_holds`
-- is now stated AT that literal, with `exp(exp 100) ≤ T₀` in place of `3 ≤ T₀` (the second
-- exposure, same genre: a value the proof had, hidden by a weaker `∃` body).  So §9 fires:
-- `halaszPrimesChi_holds_gated` is `USetChi.HalaszPrimesChi`'s conclusion, UNCONDITIONAL,
-- behind FOUR `q`-vs-`T` gates (edge `q`-scale; the region's `A`-absorption; the below-floor
-- comparison `Kq`; the Siegel gate `Ks`) and nothing else.
--
-- ⟦A3 — THE 𝒰-EXIT COMPOSE⟧ `usetChi_window_meansq_of_socket`: the lifted ladder's two
-- branches joined through `usetChi_integral_to_branches` — the `𝒯_S` branch at the re-pinned
-- level `ε_Q = (log X)^{−106}` (UNCONDITIONAL: `halaszIntegersChiPhi_holds` + the `φ(q)` debit
-- repaid) and the `𝒯_L` branch at the same level, where the pair socket is spent.
-- **THE SOCKET ENTERED NAMED, AND THAT WAS A FINDING**: `HalaszPrimesChi C c T₀` fixed `T₀`
-- BEFORE quantifying `∀ q`, while each of §2's four gates asks `T ≥ T₁(q)` with `T₁`
-- increasing in `q` — so the gated row could not discharge the slot AS THEN STATED, though
-- every consumer instantiates it at a single `(q,T)`.
--
-- ⟦THE SLOT WAVE (2026-07-30) — THE REPAIR, MADE⟧ the slot is now POINTWISE in `(q, T)`
-- (`USetChi.lean`), the three `𝒯_L` rungs were re-run at the moved instantiation point, and
-- this file's §2/§4 close the composition: `halaszPrimesChi_pointwise_of_gates` discharges the
-- restated socket from `halaszPrimesChi_holds_gated` — **the four gates BECOME the per-`(q,T)`
-- floor the slot no longer carries** (G4's ineffective `Ks` rides as the `∃` it already was) —
-- and `usetChi_window_meansq_gated` is A3 with `hslot` GONE.  The honest residue is now: the
-- 𝒰-package (`f`, `Pseq/Qseq`, `δ`, `J/Jb`, `V`, `α/η/ε`, the budget, `hUA`), the per-`j` block
-- gates on `ramI H P Q`, the ambient height/scale gates, the pointwise co-factor bound `Rbd`,
-- the Lemma-12 error row `E`, and the floor `T₀ ≤ T` + G1–G4.  Four log scales stay apart:
-- `log(5T+1)` (gates), `log(qT)` (decay, count, kill), `L ≥ log(qT)`, `log X` (the 𝒯_S level).
--
-- ⟦A4 — NOT REACHED, and the blocker is kernel-stated⟧ `M4ChiSummedFreeRow`'s datum is a
-- `y`-aspect short-sum window mean square (`chiFreeRowSq`), the ladder's is a `t`-aspect
-- ordinate mean square; the bridge is the door row, whose χ-lift meets `M4DoorRow`'s TWO
-- WALLS (`band_window_ratio_lock`, `door_length_gate_fails_of_small` / `door_length_gate_iff`)
-- — obstructions stated as theorems, not prose.  The socket's only landed inhabitant is the
-- trivial grade `4·arcDen 12 H` (`m4_chiSummedFreeRow_trivial`), which cannot meet
-- `m4_second_road_rs_ceiling`'s `δ₀²` budget.  So A4 remains a design block, not a
-- composition.
open Salt.Tactic in
#audit_axioms Salt.MR.xiCarveWidth_of_siegel
  Salt.MR.mmuChiRate_holds_gated
  Salt.MR.lambdaChiSummatory_holds_gated
  Salt.MR.halaszPrimesChi_holds_gated
  Salt.MR.halaszPrimesChi_pointwise_of_gates
  Salt.MR.usetChi_window_meansq_of_socket
  Salt.MR.usetChi_window_meansq_gated

-- ⟦ii-2, THE PROBE (2026-07-30)⟧ `USetGChiCount` — the PAIR Lemma-8 at the GRADED threshold,
-- first stone of the ⟦THE THRESHOLD WALL⟧ repair (C2-SCOPE; freeze v2.3): the graded
-- uniformisation of the landed raw pair count `ramQChi_large_count`, mirroring
-- `ramQ_graded_count` at `q = 1` with the pair genre (`FibreWellSpaced`, `chiBarCoeff`, the
-- height `qT`, the hybrid constant `1680`).  The exact-`α` collapse survives the χ-lift
-- untouched: the height-power exponent is exactly `2α`, with no pigeonhole factor.
open Salt.Tactic in
#audit_axioms Salt.MR.ramQChi_graded_count
