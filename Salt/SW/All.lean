/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Defs
import Salt.SW.Kernel
import Salt.SW.Psi1Identity
import Salt.SW.ZeroCount
import Salt.SW.Growth
import Salt.SW.PartialFractions
import Salt.SW.BCBound
import Salt.SW.MaxModulus
import Salt.SW.EulerBridge
import Salt.SW.ThreeFourOne
import Salt.SW.ZetaPole
import Salt.SW.ZeroFree
import Salt.SW.ZetaPartialFractions
import Salt.SW.LandauPage
import Salt.SW.ZeroFreeReal
import Salt.SW.Page
import Salt.SW.FourFold
import Salt.SW.Siegel
import Salt.SW.Estermann
import Salt.SW.EstermannInterface
import Salt.SW.SiegelFinal
import Salt.SW.SiegelClose
import Salt.SW.ContourShift
import Salt.SW.ShiftAssembly
import Salt.SW.ShiftVariants
import Salt.SW.ZetaZeroFree
import Salt.SW.ShiftTrivChar
import Salt.SW.Psi1Transfer
import Salt.SW.CharDispatch
import Salt.SW.Fold
import Salt.SW.Gate
import Salt.SW.BoxCount
import Salt.SW.BoxFold
import Salt.SW.ZetaLogBound
import Salt.SW.BoxCompose
import Salt.SW.ZetaLowerShallow
import Salt.SW.ZetaInvShallow
import Salt.SW.MobiusRate
import Salt.SW.MobiusRateClose
import Salt.SW.ZeroCountNearOne
import Salt.SW.DHDetector
import Salt.SW.StripConvergence
import Salt.SW.GrahamWeights
import Salt.SW.DHRepulsion
import Salt.SW.DHContour
import Salt.SW.DHBalance
import Salt.SW.DHClose
import Salt.SW.DHMain
import Salt.SW.MoebiusDiv
import Salt.SW.MoebiusRateSharp
import Salt.SW.MoebiusLog
import Salt.SW.GrahamL2
import Salt.SW.CoprimeBV
import Salt.SW.DHMollified
import Salt.SW.DHFinal
import Salt.SW.DHTrunc
import Salt.SW.DHBal
import Salt.SW.DHBal2
import Salt.SW.SelWeight
import Salt.SW.SelAlgebra
import Salt.SW.SelOpt
import Salt.SW.DHExtract
import Salt.SW.Hyperbola
import Salt.SW.ZetaEM
import Salt.SW.DHCore
import Salt.SW.DHClose2
import Salt.SW.EulerEff
import Salt.SW.EulerLink
import Salt.SW.DHExtractW
import Salt.SW.Crush
import Salt.SW.CrushC
import Salt.SW.CrushE
import Salt.SW.CrushH
import Salt.SW.TBalClose
import Salt.SW.DHExtractRho
import Salt.SW.TBalFinal
import Salt.SW.TBalCompose
import Salt.SW.TBalR7
import Salt.Tactic.AuditAxioms

/-!
# The SW rung (`sw`) — aggregate import

Design: `docs/blueprints/sw.md`. THE project's remaining gate: discharge
`Salt.BV.SiegelWalfisz` (`Salt/BV/Defs.lean`), turning
`Salt.BV.bounded_gaps_of_siegelWalfisz` into UNCONDITIONAL bounded prime gaps.
The route is the Fable Riesz amendment (smooth `ψ₁` carrier, absolutely
convergent Mellin kernel) with error-#14's orthogonality-first de-smoothing.
Wired into `Salt.lean` from the first commit; extended as waves S1–S6 land.

## Landed (wave S0 — the Riesz carriers)

`Defs`:
* the carriers `psi1Chi` (ℂ character Riesz mean) and `psi1AP` (real AP Riesz
  carrier), conventions matching `Salt.LS.psiAP`, plus the floor bridge `psiAPr`;
* `psi1Chi_eq_sum_psi1AP` — the character expansion of the Riesz carrier;
* `psi1_fold` — the orthogonality fold `∑_χ χ̄(a)·ψ₁(x,χ) = φ(q)·ψ₁(x;q,a)` (the
  ψ₁-analog of the landed `Salt.BV.MaxReduction` identity; the algebraic half of
  S6's "orthogonality FIRST" order);
* `psi1AP_nonneg` and the first-difference sandwich `psi1AP_sandwich`
  (`psi1AP_sub_lower` / `psi1AP_sub_upper`) — the monotonicity hypothesis S6's
  de-smoothing consumes;
* `neg_logDeriv_LSeries_eq_LSeries_twist` — the `−L'/L = LSeries (χ·Λ)` identity
  on `Re s > 1` (re-export of mathlib's `LSeries_twist_vonMangoldt_eq`), the
  Dirichlet-series input S1 feeds through the Mellin/Perron identity.

## Gate reference

The frozen target is `Salt.BV.SiegelWalfisz` (unchanged since the BV rung). No
weakening to bounded `C` is permitted (Iron Rule 1): the effective-only route
reaches `C < 2` and is not the theorem. The `∃ K` top-level shape absorbs
Siegel's intrinsic ineffective constant.
-/

-- Build-time axiom audit (T5 adoption): a stray axiom in the SW track fails
-- `lake build` here, not only at out-of-band lint time.
open Salt.Tactic in
#audit_axioms Salt.SW.norm_shifted_detector_mollified_le
  Salt.SW.dhDetectorShift_regroup
  Salt.SW.innerG_eq_coprime_sum
  Salt.SW.sum_coprime_eq_moebius_multiples
  Salt.SW.grahamW_eq_sum_grahamGc
  Salt.SW.graham_diagonalisation
  Salt.SW.abs_grahamGc_le
  Salt.SW.abs_sum_grahamTheta_div_le_inv_log
  Salt.SW.abs_sum_moebius_div_mul_log_le
  Salt.SW.abs_mwWeighted_le_div_log
  Salt.SW.mwWeighted_tendsto_zero
  Salt.SW.abs_sum_grahamTheta_div_le_one
  Salt.SW.abs_mwWeighted_le_one
  Salt.SW.sum_moebius_mul_div_eq_one
  Salt.SW.dh_repulsion_partial
  Salt.SW.LFunction_one_re_ge_partial
  Salt.SW.dh_repulsion_of_LFunction_one_lower
  Salt.SW.norm_dhIntegrand_le
  Salt.SW.norm_riemannZeta_le
  Salt.SW.rectBI_zeta_shift_mul
  Salt.SW.rectBI_zeta_LFunction_kernel
  Salt.SW.zetaHol_differentiable
  Salt.SW.dhLSeries_identity
  Salt.SW.dhDetector_mellin
  Salt.SW.dhDetector_floor
  Salt.SW.grahamTheta_floor
  Salt.SW.sum_abs_grahamTheta_rpow_le
  Salt.SW.tendsto_partialLSeries
  Salt.SW.norm_LFunction_sub_partial_le_strip
  Salt.SW.dhA_nonneg
  Salt.SW.dhA_square_ge_one
  Salt.SW.dhA_mass_floor_real
  Salt.SW.dhA_hyperbola
  Salt.SW.LFunction_zero_count_near_one
  Salt.SW.LFunction_zero_count_near_one_guarded
  Salt.SW.psi1Chi_eq_sum_psi1AP Salt.SW.psi1_fold
  Salt.SW.psi1AP_nonneg Salt.SW.psi1AP_sandwich
  Salt.SW.psi1AP_sub_lower Salt.SW.psi1AP_sub_upper
  Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist
  Salt.SW.kernel_identity Salt.SW.kernel_sum_swap
  Salt.SW.psi1_eq_integral Salt.SW.psi1_eq_integral_logDeriv
  Salt.SW.LFunction_center_lower Salt.SW.LFunction_zero_count_le
  Salt.SW.norm_deriv_le_of_re_le
  Salt.SW.LFunction_eq_growthSum Salt.SW.LFunction_growth
  Salt.SW.LFunction_growth_sphere
  Salt.SW.logDeriv_prod_pow Salt.SW.LFunction_exists_factorization
  Salt.SW.LFunction_partialFraction Salt.SW.norm_logDeriv_sub_sum_le
  Salt.SW.norm_logDeriv_sub_sum_of_blaschke
  Salt.SW.LFunction_norm_logDeriv_sub_sum Salt.SW.neg_re_logDeriv_le
  Salt.SW.norm_reflectedFactor_eq_on_sphere
  Salt.SW.LFunction_norm_logDeriv_sub_sum'
  Salt.SW.LFunction_eq_primitive_mul Salt.SW.eulerCorr_ne_zero
  Salt.SW.logDeriv_LFunction_eq Salt.SW.LFunction_eq_zero_iff_primitive
  Salt.SW.norm_logDeriv_LFunction_sub_primitive_le
  Salt.SW.three_four_one_termwise Salt.SW.three_four_one
  Salt.SW.three_four_one_logDeriv
  Salt.SW.neg_logDeriv_zeta_le Salt.SW.neg_logDeriv_LFunction_trivChar_le
  Salt.SW.zero_free_region_primitive Salt.SW.zero_free_region
  Salt.SW.Zc_growth Salt.SW.entire_zero_count_le
  Salt.SW.entire_norm_logDeriv_sub_sum'
  Salt.SW.neg_logDeriv_zeta_split Salt.SW.zeta_neg_re_logDeriv_le
  Salt.SW.landau_neg_logDeriv_re_lower Salt.SW.analyticOrderAt_eq_of_factorization
  Salt.SW.landau_one_exceptional_at Salt.SW.landau_one_exceptional
  Salt.SW.landau_one_exceptional_simple
  Salt.SW.LFunction_conj Salt.SW.neg_re_logDeriv_trivChar_complex_le
  Salt.SW.zero_free_region_real Salt.SW.zero_free_region_all
  Salt.SW.zero_free_region_all'
  Salt.SW.product_ne_one Salt.SW.page_positivity
  Salt.SW.neg_reLogDeriv_changeLevel_le Salt.SW.page_cross_modulus
  Salt.SW.fourfold_vonMangoldt_nonneg Salt.SW.changeLevel_quadratic
  Salt.SW.fourfoldCoeff_nonneg Salt.SW.fourfoldCoeff_apply_one
  Salt.SW.LSeries_fourfoldCoeff_eq Salt.SW.LSeriesSummable_fourfoldCoeff
  Salt.SW.LFunction_pos_of_one_lt Salt.SW.LFunction_apply_one_pos
  Salt.SW.fourfold_pos_of_one_lt Salt.SW.lambda_pos
  Salt.SW.estermann_fourfold Salt.SW.siegel_dichotomy
  Salt.SW.siegel_L_one_extract Salt.SW.goldfeld_L_one_lower
  Salt.SW.siegel_zero_free_of_exceptional_case
  Salt.SW.landau_truncation Salt.SW.estermannPositivity_core
  Salt.SW.estermannPositivity_of_interface
  Salt.SW.no_estermann_data_for_zero Salt.SW.zeta_nonpos
  Salt.SW.estermannInterface' Salt.SW.estermannInterface
  Salt.SW.estermannPositivity
  Salt.SW.LFunction_one_re_le_mvt Salt.SW.fourfold_disk_bound
  Salt.SW.siegel_L_one_exceptional Salt.SW.siegel_zero_free_exceptional
  Salt.SW.LFunction_apply_one_norm_le Salt.SW.LFunction_norm_le_near_one
  Salt.SW.norm_deriv_LFunction_near_one Salt.SW.LFunction_one_re_le_mvt_sharp
  Salt.SW.norm_eulerCorr_one_le Salt.SW.siegel_theorem
  Salt.SW.rectBI_eq_zero_of_differentiableOn Salt.SW.rectBI_dslope_eq_zero
  Salt.SW.rectBI_inv_eq_two_pi_I Salt.SW.rectBI_cif_eq
  Salt.SW.kernel_residue
  Salt.SW.psi1_contour_shift
  Salt.SW.norm_logDeriv_le_of_ball_dist Salt.SW.rectBI_sub_of_edge_eq
  Salt.SW.psi1_contour_shift_exceptional
  Salt.SW.zeta_neg_re_logDeriv_le_keep Salt.SW.zeta_zero_free_strip
  Salt.SW.zeta_zero_free_region
  Salt.SW.norm_logDeriv_eulerCorr_trivChar_le
  Salt.SW.norm_logDeriv_Zc_le_of_ball_dist
  Salt.SW.psi1_contour_shift_trivchar Salt.SW.psi1_contour_shift_trivchar_full
  Salt.SW.psi1_transfer Salt.SW.psi1Chi_one_primitive Salt.SW.psi1_transfer_one
  Salt.SW.sq_le_C_exp Salt.SW.E_shape_bound
  Salt.SW.psi1_char_bound Salt.SW.psi1_trivchar_bound
  Salt.SW.psi1AP_main_bound
  Salt.SW.siegelWalfisz_holds Salt.SW.bounded_gaps_unconditional
  Salt.SW.zeta_box_divisor_le Salt.SW.zeta_box_count_half
  Salt.SW.Zc_sphere_bound_wide
  Salt.SW.zeta_analyticOrderAt_one_sub Salt.SW.zeta_zero_one_sub_iff
  Salt.SW.zeta_fe_factor_ne_zero Salt.SW.zeta_box_count_full
  Salt.SW.zeta_log_bound Salt.SW.tail_psum_le
  Salt.SW.zeta_full_box_count Salt.SW.zeta_local_density
  Salt.SW.zeta_local_density_card
  Salt.SW.zeta_norm_le_zc Salt.SW.zeta_real_upper
  Salt.SW.zeta_anchor Salt.SW.zeta_deriv_bound
  Salt.SW.zeta_lower_shallow
  Salt.SW.Zc_patch_lower Salt.SW.zeta_inv_shallow
  Salt.SW.LSeries_moebius_eq_zeta_inv Salt.SW.mmu1_eq_integral
  Salt.SW.mmu_rectBI_eq_zero
  Salt.SW.mmuRate_smoothed Salt.SW.mmuRate_holds
  Salt.SW.norm_bsum_kernel_zero_decay Salt.SW.zfr_harvest
  Salt.SW.dhA_mass_upper Salt.SW.sum_hyperbola_comm
  Salt.SW.sum_abs_grahamGc_div_le
  Salt.SW.sum_divisors_eq_hyperbola_symm Salt.SW.dhA_hyperbola_symm
  Salt.SW.zeta_partial_em Salt.SW.zetaHol_bound
  Salt.SW.zetaApprox_strip Salt.SW.norm_zeta_sub_approx_le_strip
  Salt.SW.dhA_mass_eq_char_count Salt.SW.inner_coprime_eq
  Salt.SW.dhA_mul_eq_sum Salt.SW.inner_cop_swap
  Salt.SW.dhA_mass_mul_eq_group Salt.SW.dhA_mass_mul_le
  Salt.SW.sqfree_card_divisors Salt.SW.sum_abs_grahamGc_sigmaSq_div_le
  Salt.SW.dhWeightSqW_one Salt.SW.dhCoeffW_one Salt.SW.dhCoeffW_nonneg
  Salt.SW.dhWeightSqW_eq_sum_gcW Salt.SW.gcW_eq_zero_of_not_squarefree
  Salt.SW.abs_gcW_le Salt.SW.sum_abs_gcW_sigmaSq_div_le Salt.SW.norm_dhCoeffW_term
  Salt.SW.selH_pos Salt.SW.selH_le_two Salt.SW.selH_lt_of_prime Salt.SW.selG_pos
  Salt.SW.selGmul_pos Salt.SW.selHSum_pos Salt.SW.selWeight_apply_one
  Salt.SW.tail_shift_to_beta0
  Salt.SW.selberg_diag Salt.SW.selberg_diag_nonneg Salt.SW.rescale_inv_ge
  Salt.SW.selberg_opt_eq Salt.SW.selweight_abs_le_one Salt.SW.selMainTerm_diag
  Salt.SW.selY_collapse Salt.SW.selNu_inv_eq Salt.SW.selCore_collapse Salt.SW.partial_H_bound
  Salt.SW.sum_mul_index_eq Salt.SW.kernel_abel_sum Salt.SW.sum_Icc_one_shift
  Salt.SW.sum_rpow_le_integral Salt.SW.chiRe_partial_at_zero_le
  Salt.SW.sum_rpow_neg_le Salt.SW.T_em_real Salt.SW.abs_zeta_re_le
  Salt.SW.floor_div_mul_ge Salt.SW.term_rpow_le Salt.SW.natSqrt_le_sqrt
  Salt.SW.natSqrt_mul_rpow_le Salt.SW.sqrt_lt_two_natSqrt Salt.SW.sqrt_pow_bound
  Salt.SW.rpow_sub_le_tangent Salt.SW.dhAbel_hyperbola Salt.SW.dhAbel_leg1_le
  Salt.SW.dhAbel_inner_le Salt.SW.unmoll_extraction_real Salt.SW.L1_lower_siegel
  Salt.SW.selH_local_split Salt.SW.one_sub_inv_pos Salt.SW.one_sub_chiRe_div_pos
  Salt.SW.one_add_selG_eq_local_inv Salt.SW.selHblock_divisors_eq
  Salt.SW.dhExtractionW_regroup
  Salt.SW.sqfree_rpow_prod Salt.SW.alpha_weighted_divprod Salt.SW.rankin_tail_le
  Salt.SW.squarefree_primorial Salt.SW.sqfree_le_eq_primorial_divisors
  Salt.SW.selHSum_eq_primorial_le Salt.SW.selHFull_eq_zetaL Salt.SW.selHFull_eq_add_tail
  Salt.SW.selHSum_ge_full_sub_rankin Salt.SW.selHSum_ge_zetaL_sub_rankin
  Salt.SW.primorial_primeFactors Salt.SW.selHFull_eq_zeta_mul_L
  Salt.SW.zeta_side_prod_eq Salt.SW.mertens_prod_pos Salt.SW.zeta_side_ge
  Salt.SW.kernel_abel_sum_real Salt.SW.rpow_sub_le_tangent_upper Salt.SW.dhAbel_inner_abs_le
  Salt.SW.sum_rpow_ge Salt.SW.sum_rpow_sandwich Salt.SW.unmoll_extraction_abs_real
  Salt.SW.inner_cop_swap_wt Salt.SW.weighted_char_count Salt.SW.dhA_kernel_reduction_inner
  Salt.SW.dhA_kernel_reduction Salt.SW.selWeight_ne_zero_squarefree Salt.SW.selWeight_ne_zero_le
  Salt.SW.gcW_selWeight_eq_zero_of_gt_sq Salt.SW.dhD0_scale_main Salt.SW.dhD0_scale_err
  Salt.SW.selHmul_collection Salt.SW.sum_gcW_selNu_eq_selMainTerm Salt.SW.omega_eq_primeFactors_card
  Salt.SW.paircount Salt.SW.pairkernel_per_m Salt.SW.sum_gcW_pairkernel_le
  Salt.SW.dh_extraction_per_m Salt.SW.dh_extraction_upper_W
  Salt.SW.selHSum_ge_one Salt.SW.selHSum_le_primorial Salt.SW.crush_pointwise
  Salt.SW.selG_ge_partial_geom Salt.SW.H_lower_of_parts Salt.SW.crush_coverage
  Salt.SW.selHSum_ge_dhA_div_sum
  Salt.SW.sum_divisors_eq_hyperbola_asymm Salt.SW.dhAbel_hyperbola_asymm
  Salt.SW.dhAbel_leg1_cut_abs_le Salt.SW.dhAbel_inner_ge
  Salt.SW.dhAbel_inner_ge_err Salt.SW.H_lower
  Salt.SW.dhW_detector_floor_beta0 Salt.SW.dh_balance_beta0_real
  Salt.SW.norm_zeta_rho_le Salt.SW.norm_cpow_pos_floor_sub_le Salt.SW.dhAbel_hyperbola_rho
  Salt.SW.emrho_perterm Salt.SW.clean_cpow_term Salt.SW.dhAbel_leg1_rho Salt.SW.dhAbel_inner_rho
  Salt.SW.norm_LFunction_one_eq_re Salt.SW.sum_mul_index_eq_rho Salt.SW.kernel_abel_sum_rho
  Salt.SW.cpow_unit_tangent_bound Salt.SW.norm_ofReal_cpow_seg_le Salt.SW.sum_cpow_sandwich_rho
  Salt.SW.unmoll_extraction_rho
  Salt.SW.dh_extraction_upper_rho
  Salt.SW.dhW_detector_floor_rho Salt.SW.dh_balance
