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
import Salt.SW.EpsilonZero
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
import Salt.SW.BvWeight
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
import Salt.SW.TBalR8
import Salt.SW.EFSharp
import Salt.SW.EFSharpZeros
import Salt.SW.EFSharpMult
import Salt.SW.DensityCrude
import Salt.SW.WellSpacedAt
import Salt.SW.DensityLogfree
import Salt.SW.TauExt
import Salt.SW.TBalTall
import Salt.SW.BCSup
import Salt.SW.BvL
import Salt.SW.GrahamMean
import Salt.SW.GrahamHard
import Salt.SW.GrahamHard2
import Salt.SW.GrahamHard3
import Salt.SW.Kernel2
import Salt.SW.CoprimeHarmonic
import Salt.SW.PseudoChar
import Salt.SW.PseudoCharH
import Salt.SW.JutilaResidue
import Salt.SW.JutilaHalasz
import Salt.SW.JutilaRatio
import Salt.SW.DensityStrip
import Salt.SW.PseudoCharEuler
import Salt.SW.JutilaDetector
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
  Salt.SW.tbal_tau_le_split Salt.SW.tbal_tau_le_split_k1 Salt.SW.dh_master_ray
  Salt.SW.exp_sub_one_le_e_mul Salt.SW.rpow_sub_one_le Salt.SW.neg_log_le_rpow
  Salt.SW.neg_log_le_rpow'
  Salt.SW.ray_pow_bound Salt.SW.row_1x_cap Salt.SW.row_A_cap Salt.SW.row_rho_main_cap
  -- ⟦B1a⟧ the `k = 1` twins and their two engines (the landed caps above are untouched)
  Salt.SW.log_add_two_le_rpow_nine_tenths Salt.SW.ray_pow_bound_conv
  Salt.SW.row_A_cap_k1 Salt.SW.row_rho_main_cap_k1
  Salt.SW.logz_factor_le
  Salt.SW.logz_factor_pow9_le Salt.SW.row_Eβ_cap Salt.SW.row_Eρ_cap Salt.SW.row_Eβ_cap_k1
  Salt.SW.tbal_hguard Salt.SW.tbal_hscale Salt.SW.tbal_hcov Salt.SW.C2Rho_le
  Salt.SW.dh_repulsion_ordered
  Salt.SW.psi1Chi_sub_eq Salt.SW.psiChiR_sub_riesz_diff_le
  Salt.SW.psi_sharp_of_riesz_bounds Salt.SW.psi_sharp_riesz_at_height
  Salt.SW.vonMangoldt_mass_sdiff_le Salt.SW.cpow_riesz_residue_desmooth
  Salt.SW.efRieszSum_diff_sub_efZeroSum_le Salt.SW.psi_explicit_sharp_of_riesz_residues
  Salt.SW.LFunction_growth_sphere_wide Salt.SW.log_four_M0Lbox_le
  Salt.SW.halfbox_subset_closedBall Salt.SW.LFunction_halfbox_zero_count
  Salt.SW.rectBI_finsetSum Salt.SW.psi1_contour_shift_finset
  Salt.SW.boxZeroSet_finite Salt.SW.mem_boxZeros
  Salt.SW.psi_explicit_sharp Salt.SW.psi_sharp_at_efHeight
  Salt.SW.analyticOrderAt_LFunction_ne_top Salt.SW.analyticOrderAt_LFunction_eq
  Salt.SW.zeroMult_eq_one Salt.SW.one_le_zeroMult Salt.SW.LFunction_local_factor
  Salt.SW.efMultTotal_nonneg Salt.SW.efRieszSumM_eq_of_simple
  Salt.SW.efZeroSumM_eq_of_simple Salt.SW.efMultTotal_eq_card_of_simple
  Salt.SW.rectBI_const_mul Salt.SW.logDeriv_sub_const_pow
  Salt.SW.psi1_contour_shift_finsetM Salt.SW.efRieszSumM_diff_sub_efZeroSumM_le
  Salt.SW.psi_explicit_sharpM_of_riesz_residues
  Salt.SW.psi_explicit_sharpM Salt.SW.psi_sharp_at_efHeightM
  Salt.SW.efMultTotal_le_divisor Salt.SW.efMultTotal_halfbox_le
  Salt.SW.log_39_37_lower Salt.SW.windowConst_le_137 Salt.SW.efMultTotal_box_le
  Salt.SW.zeroCountM_le Salt.SW.zeroCountM_density_crude Salt.SW.zeroCountM_density_log
  Salt.SW.zeroCountM_efHeight_le
  Salt.SW.zeroSum_rpow_le Salt.SW.efZeroSumM_norm_le
  Salt.SW.efZeroSumM_spend_le Salt.SW.efZeroSumM_spend_at_efHeight
  Salt.SW.zetaHol_norm_le_of_lt Salt.SW.zetaHol_norm_le
  Salt.SW.zetaHol_bound_tall Salt.SW.zetaHol_bound_five
  Salt.SW.repulsion_ceiling_of_contract Salt.SW.repulsionCeiling_mono
  Salt.SW.boxZeros_re_le_of_repulsion Salt.SW.efZeroSumM_spend_at_repulsion
  Salt.SW.boxZeros_re_le_unit_box
  Salt.SW.zeta_partial_em_free Salt.SW.norm_zeta_rho_le_tall Salt.SW.emrho_perterm_tall
  Salt.SW.dhAbel_leg1_rho_tall Salt.SW.dhAbel_inner_rho_tall Salt.SW.unmoll_extraction_rho_tall
  Salt.SW.dh_extraction_upper_rho_tall Salt.SW.dh_master_ray_tall Salt.SW.C2Rho_le_tall
  Salt.SW.row_Eρ_cap_tall Salt.SW.dh_repulsion_tall Salt.SW.boxZeros_re_le_at_efHeight
  Salt.SW.row_Eρ_cap_tall_k1 Salt.SW.dh_repulsion_k1_of_floor
  Salt.SW.norm_logDeriv_le_of_bound_off_zeros Salt.SW.norm_sub_le_of_norm_le_on_ball
  Salt.SW.mem_of_LFunction_eq_zero Salt.SW.multiplicity_eq_zeroMult
  Salt.SW.LFunction_partialFraction_remainder_diff
  -- N4b W0 (the prerequisite wave): the β₀ erase-split, the per-zero un-collapse, the
  -- A3 harmonic batching and the harmonic-form erased spend
  Salt.SW.efZeroSumM_erase_split
  Salt.SW.efRieszSumM_diff_sub_efZeroSumM_le_perZero
  Salt.SW.psi_explicit_sharpM_of_riesz_residues_perZero
  Salt.SW.psi_explicit_sharpM_perZero
  Salt.SW.cpow_riesz_diff_norm_le Salt.SW.efRieszSumM_diff_norm_le
  Salt.SW.efRieszSumM_diff_quotient_norm_le
  Salt.SW.sum_range_inv_succ_eq_harmonic Salt.SW.efMultHarmonic_box_le
  Salt.SW.efZeroSumM_norm_le_harmonic Salt.SW.efZeroSumM_erase_norm_le_harmonic
  -- N4b W0.5 (HSEP-GAP): the gap-form contour shift, the box-exact EF, and the
  -- pigeonhole that retires the well-spacing hypothesis outright
  Salt.SW.psi1_contour_shift_finsetM_gap Salt.SW.card_le_efMultTotal
  Salt.SW.psi_explicit_sharpM_perZero_box Salt.SW.psi_explicit_sharpM_box
  Salt.SW.exists_gap_midpoint Salt.SW.exists_contour_params
  Salt.SW.psi_explicit_sharpM_perZero_unsep

-- ⭐ ⟦BW-(ii) 0901⟧ `Salt/SW/EpsilonZero.lean` — 20 declarations, listed by NO gate in the
-- repository until this block (council 2026-09-01 ruling 11; measured on `main ff07fa93`).
-- This is the module that abolishes the COMPACTNESS step in `zeta_zero_free_strip`, i.e. the
-- one that turns an opaque existential `ε₀` into an explicit constant — the effectivity of
-- every consumer that divides by it. An unaudited effectivity repair is the shape of a green
-- track that certifies nothing: `lake build` says it ELABORATES, never that it is axiom-clean.
#audit_axioms Salt.SW.zeta_zero_free_strip_sharp
  Salt.SW.zeta_zero_free_strip_sharp_bounded
  Salt.SW.zeta_zero_free_region_sharp
  Salt.SW.zeta_zero_free_region_sharp_bounded

-- ⟦B2 W0 0904⟧ `Salt/SW/DensityLogfree.lean` — the LOG-FREE density on the low strip
-- `4/5 ≤ σ ≤ 119/120`, `N ≤ 1378·(qT)^{150(1−σ)}`, off the landed count with the two
-- crudities taken sharp at `T ≥ 2`. B2's free half: Jutila's §3 is then needed only on
-- `119/120 < σ ≤ 1`. The literal is a claim about a numeral, so the audit is the gate.
#audit_axioms Salt.SW.zeroCountM_density_logfree_low

-- ⟦B2 W6a 0904⟧ `Salt/SW/BvWeight.lean` — Jutila's two-level Barban–Vehov weight
-- (2.5)/(2.6) as a combination of the landed one-level `grahamTheta`, with the three case
-- rows and Lemma 6's two opening divisor identities (`a_1 = 1`, `a_n = 0` on `2 ≤ n ≤ z₁`).
-- `bvWeight` itself is a def; the five theorems are what the gate can audit.
#audit_axioms Salt.SW.bvWeight_eq_moebius_of_le
  Salt.SW.bvWeight_eq_zero_of_gt
  Salt.SW.bvWeight_eq_of_mem
  Salt.SW.sum_bvWeight_divisors_eq_zero
  Salt.SW.sum_bvWeight_divisors_one

-- ⟦B2 W6b-E 0904⟧ `Salt/SW/BvL.lean` — the coprime log-weighted Möbius sum `bvL g w` on the
-- REALS, its telescope `bvL (p g') w = bvL g' w + (1/p)·bvL (p g') (w/p)` and the envelope
-- `|bvL g w| ≤ C₀·g/φ(g)` (squarefree `g`), whence the sharp pointwise decay
-- `|innerG z g| ≤ C₀/(φ(g)·log z)`. `bvL` itself is a def; the seven theorems are the gate.
#audit_axioms Salt.SW.bvL_of_lt_one
  Salt.SW.innerG_eq_bvL
  Salt.SW.abs_bvL_one_le
  Salt.SW.bvL_step
  Salt.SW.abs_bvL_le
  Salt.SW.innerG_eq_zero_of_not_squarefree
  Salt.SW.abs_innerG_le_sharp

-- ⟦B2 W6b-E 0904⟧ `Salt/SW/GrahamMean.lean` — the Graham / Barban–Vehov MEAN upper bound on
-- the EASY half `x ≥ z²`: `Σ_{n ≤ x} w(n) ≤ C·x/log z`, and the same for Jutila's two-level
-- weight. The hypothesis `x ≥ z²` is strictly weaker than Graham's `x ≥ z` (W6b-H's), and
-- S10's `z₂² ≤ x` is unsatisfiable at B2's closure table — the honest label is in the module
-- docstring, and the audit is what says the constants carry no extra axiom.
#audit_axioms Salt.SW.sum_totient_innerG_sq_le
  Salt.SW.grahamW_sum_eq_floor
  Salt.SW.sum_grahamGc_div_eq
  Salt.SW.sum_abs_grahamTheta_le
  Salt.SW.sum_abs_grahamGc_le
  Salt.SW.grahamW_sum_le
  Salt.SW.sum_sq_sum_bvWeight_le

-- ⟦B2 W6b-H1 0905⟧ `Salt/SW/GrahamHard.lean` — the SUBSTRATE of the Graham mean bound on the
-- HARD half `z ≤ u < z²`: the Λ-identity and its level form with the tail (H1a/b/c), the
-- Cauchy–Schwarz split (H2), `Σ Λ² ≤ (log 4 + 4)x log x` (H3), An's (5.2) four-parameter
-- bijection (H4), two Möbius rows with a power-of-log saving (H6a/H6b), the four elementary
-- divisor-sum bounds (H0b–e) and the below-level mean (H9). Six rows of the cut are ABSENT
-- and flagged (`docs/blueprints/flags.md`, 09-05); the module docstring carries the label.
#audit_axioms Salt.SW.sum_divisors_moebius_mul_log_div_eq
  Salt.SW.log_mul_sum_grahamTheta_eq
  Salt.SW.tailT_eq_zero_of_le
  Salt.SW.grahamW_le_two_mul_sq
  Salt.SW.sum_vonMangoldt_sq_le
  Salt.SW.sum_tailT_sq_eq
  Salt.SW.abs_sum_moebius_le_div_log_pow
  Salt.SW.abs_sum_moebius_div_le_inv_log_pow
  Salt.SW.sum_sigmaQ_le
  Salt.SW.sum_inv_mul_log_sq_le
  Salt.SW.sum_rpow_neg_half_log_sigmaQ_le
  Salt.SW.sum_sigmaQ_div_le
  Salt.SW.grahamW_sum_le_low

-- ⟦B2 W6b-H1b 0905⟧ `Salt/SW/GrahamHard2.lean` — the TWO INPUTS of the six rows W6b-H1 left
-- flagged, now COMPLETE. The coprime-subseries tool (T1–T5) and its two instances (T6 the
-- `ρ₀·r/κ(r)` density, T7 the `c₀·κ(t)/t` one), the counting half (P1, P2) and with it
-- **H5a and H5c**, the exact harmonic identity (C1), the sawtooth-log piece (C2) and with it
-- **THE CONSTANT (C3)** and **H6c**, the `t`-smooth convolution (S1), the smooth partial sum
-- against its Euler product (S2) and its tail (S3), the coprime Möbius sum (S4), and
-- **H6d, H6f, H6e** — ALL TWENTY-TWO frozen rows of the cut, plus THREE PUBLIC helpers the
-- H2 wave consumes (`log_rpow_le_rpow_quarter`, `summable_moebius_sq_div_kappa_totient`,
-- `one_le_c0`) and H6e's frozen `∃ c₀` form as a corollary of its NAMED form. NOTHING is
-- absent; the six W6b-H1 flag entries are RETIRED in `docs/blueprints/flags.md`. The module
-- docstring carries the label. Twenty-six `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.summable_coprime_indicator
  Salt.SW.coprimeSeries_one
  Salt.SW.coprimeSeries_eq_of_primeFactors_eq
  Salt.SW.coprimeSeries_eq_mul_prime
  Salt.SW.coprimeSeries_mul_prod_eq
  Salt.SW.totient_div_mul_coprimeSeries_moebius_div_sq
  Salt.SW.div_totient_mul_coprimeSeries_inv_kappa_totient
  Salt.SW.summable_moebius_sq_div_kappa_totient
  Salt.SW.sum_moebius_sq_dvd_eq
  Salt.SW.abs_card_coprime_sub_le
  Salt.SW.sqf_coprime_count_eq
  Salt.SW.sqf_coprime_sum_log_mul_log_eq
  Salt.SW.log_rpow_le_rpow_quarter
  Salt.SW.sum_moebius_div_mul_harmonic_eq
  Salt.SW.abs_sum_moebius_mul_log_floor_ratio_le
  Salt.SW.abs_sum_moebius_div_mul_log_div_sub_one_le
  Salt.SW.abs_sum_moebius_mul_log_div_add_one_le
  Salt.SW.sum_coprime_moebius_eq_sum_smooth
  Salt.SW.sum_smooth_inv_le
  Salt.SW.div_totient_sub_sum_smooth_inv_le
  Salt.SW.abs_coprime_sum_moebius_div_le
  Salt.SW.coprime_sum_moebius_div_log_eq
  Salt.SW.coprime_sum_moebius_div_kappa_le
  Salt.SW.one_le_c0
  Salt.SW.coprime_sum_moebius_div_kappa_log_eq
  Salt.SW.coprime_sum_moebius_div_kappa_log_exists

-- ⟦B2 W6b-H2 0905⟧ `Salt/SW/GrahamHard3.lean` — the KEYSTONE'S HARD HALF, whole. An 2022 §5's
-- `S₃`: the tail second moment `Σ_{n ≤ u} T_z(n)² ≤ C·u·log z` on `z ≤ u ≤ z²` (**H7**), and
-- with it Graham's mean bound on the FULL range `x ≥ z` (**H8**) and the two-level forms
-- **S10-H** and **S10-L**. Staged as the exact reductions (H7a the lower limit, H7a' the
-- NON-STRICT box) with two public helpers (H7-0 κ-multiplicativity, H7e-0 σ
-- sub-multiplicativity), the evaluation (H7b = H5c instantiated), ΣA (H7c → `c0`, H7c'), ΣB+ΣC
-- (H7d's κ-cancellation, H7d') and ΣD (H7e-1 … H7e-4). ALL SEVENTEEN frozen rows land; NOTHING
-- is absent and `flags.md` gains nothing. The module docstring carries the honest label — upper
-- bound only, non-effective constants, `ρ₀c₀ = 1` never used, S10-L lossy, the two STRUCK H7d
-- mutants. Seventeen `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.sum_filter_side_eq_sqfLogPair_sub
  Salt.SW.sum_tailT_sq_eq_box
  Salt.SW.kappa_mul_of_coprime
  Salt.SW.sigmaQ_mul_le
  Salt.SW.abs_sqfLogPair_sub_le
  Salt.SW.abs_aKernel_sub_c0_le
  Salt.SW.sum_inv_mul_abs_aKernel_le
  Salt.SW.abs_bKernel_le
  Salt.SW.sum_abs_bKernel_le
  Salt.SW.sum_rpow_neg_half_sigmaQ_one_add_log_le
  Salt.SW.sum_sum_errUpper_le
  Salt.SW.sum_sum_errLower_le
  Salt.SW.sum_rpow_neg_three_half_le
  Salt.SW.sum_tailT_sq_le
  Salt.SW.grahamW_sum_le_full
  Salt.SW.sum_sq_sum_bvWeight_le_full
  Salt.SW.sum_sq_sum_bvWeight_le_low

-- ⟦B2 K 0905⟧ `Salt/SW/Kernel2.lean` — the kernel node K: the TWICE-smoothed Riesz kernel
-- `(1 - u)²₊ ↔ 2·y^w/(w(w+1)(w+2))`, i.e. the `Kernel.lean` deliverables re-run with one more
-- pole. `kern2` and its square identity, the Mellin transform `2/(s(s+1)(s+2))`, the two
-- vertical dominants — the `(1/c)`-weighted QUADRATIC one (an integrability tool only) and the
-- CUBIC `((c²+t²)^{3/2})⁻¹` one with NO `c`-dependent constant, which is what W7's contour
-- bound at `Re = 1/2` consumes — the inversion `kernel_identity_2` (with the `y = 2`, `c = 1`
-- control reading `1/4` as an `example` in the file) and the dominated sum↔integral swap
-- `kernel_sum_swap_2`. `Kernel.lean` is byte-identical; the contour node itself is W7's own.
-- Eleven `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.kern2_eq_sq_kern
  Salt.SW.continuous_kern2
  Salt.SW.hasMellin_kern2
  Salt.SW.s2_ne_zero
  Salt.SW.norm_inv_denom2_le
  Salt.SW.norm_inv_denom2_cubic_le
  Salt.SW.verticalIntegrable_mellin_kern2
  Salt.SW.kern2_value
  Salt.SW.kernel_identity_2
  Salt.SW.integrable_Fterm2
  Salt.SW.kernel_sum_swap_2

-- ⟦B2 W2 0905⟧ `Salt/SW/CoprimeHarmonic.lean` — Jutila's Lemma 5 (L5), the `r`-average, as a
-- UNIFORM lower bound: `(6/π²)·(φ(q)/q)·log R ≤ Σ'_{r ≤ R} 1/r` over square-free `r` coprime
-- to `q`, for every `q ≥ 1` and every real `R ≥ 1` — no `R₀`, no `log R ≥ (log q)^{1/2}`, and
-- no asymptotic of Jutila's p.49 consumed. Proved outright by two injections:
-- `log R ≤ Σ_{n ≤ R} 1/n` (the harmonic floor), `n = d·m` with `d` `q`-smooth against the
-- LANDED `sum_smooth_inv_le`, and `m = b²·a` with `a` square-free against `hasSum_zeta_two`.
-- The binder `1 ≤ q` is load-bearing on the two injection rows. `R = 1` smoke row in the file.
-- Six `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.log_le_sum_inv_Icc_floor
  Salt.SW.exists_smooth_mul_coprime
  Salt.SW.sum_inv_Icc_le_coprime_mul_smooth
  Salt.SW.sum_inv_Icc_le_div_totient_mul_coprime
  Salt.SW.sum_coprime_inv_le_zeta_two_mul_sqf
  Salt.SW.sum_sf_coprime_inv_ge
-- ⟦B2 W3 0905⟧ `Salt/SW/PseudoChar.lean` — Jutila's PSEUDOCHARACTERS (L1), whole.
-- `f_r(n) = f(gcd(r, n))` for a multiplicative `f` (Jutila 1977, (1.2) p.45): the two
-- multiplicativities (in `n` on coprime pairs, in `r` on coprime levels), the detection-identity
-- input `f_r(dn) = f_r(d)·f_{r/(r,d)}(n)` — split so that the ℕ gcd identity carries NO
-- square-freeness and only the `f`-split needs it — and Selberg's instance `ψ = μ·φ` with
-- `ψ_r(p) = 1 − p` on `p ∣ r`. The non-square-free failure `ψ_4(4) = 0 ≠ ψ_4(2)·ψ_2(2) = 1` is a
-- THEOREM here, not a comment, so the `Squarefree` binder is load-bearing in Lean. The module
-- docstring carries the honest label — every row is an input to Lemma 6, the coefficients are
-- ℝ-valued and cast once at the point of use, no von Mangoldt detour is ever formed. Sixteen
-- `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.pseudoChar_one_right
  Salt.SW.pseudoChar_one_left
  Salt.SW.pseudoChar_of_coprime
  Salt.SW.pseudoChar_mul_right_of_coprime
  Salt.SW.gcd_mul_eq_gcd_mul_gcd_div
  Salt.SW.pseudoChar_mul_of_squarefree
  Salt.SW.pseudoChar_mul_left_of_coprime
  Salt.SW.pseudoChar_prime_left
  Salt.SW.abs_pseudoChar_le_sum_divisors
  Salt.SW.selbergPsi_apply
  Salt.SW.selbergPsi_isMultiplicative
  Salt.SW.selbergPsi_apply_prime
  Salt.SW.abs_selbergPsi_le
  Salt.SW.abs_pseudoChar_selbergPsi_le
  Salt.SW.pseudoChar_selbergPsi_prime_of_dvd
  Salt.SW.pseudoChar_selbergPsi_four_two_two

-- ⟦B2 W4 0905⟧ `Salt/SW/PseudoCharEuler.lean` — Jutila's LEMMA 1 (L1′), whole: the twisted
-- Euler product `Σ_n χ(n)f_t(n)n^{−s} = L(s,χ)·∏_{p∣t}(1 + (f(p) − 1)χ(p)p^{−s})` on `Re s > 1`
-- for square-free `t`, and with it (2.2) p.48 — `L(s,χ)·M(s,χ,f_r)` — in its per-level form and
-- in the `r`-summed form Lemma 6 consumes, each with the summability that form needs. The
-- product is a PRIME-PEELING INDUCTION over `t.primeFactors` staged as its own private lemma,
-- and the one reindexing helper is the unconditional `LSeries_dvd_mul_eq`; no infinite product
-- and no convergence of one enters. The docstring carries the honest label (`|bvWeight| ≤ 1` and
-- the contour node are Lemma 6's own) and the reason `Squarefree t` is load-bearing: at `t = 4`
-- the identity fails in the SECOND significant digit. Ten `#audit_axioms` names — sized from
-- THIS LIST.
#audit_axioms Salt.SW.jutilaLocal_one
  Salt.SW.jutilaLocal_prime
  Salt.SW.jutilaLocal_mul_of_coprime
  Salt.SW.norm_jutilaLocal_le
  Salt.SW.LSeries_dvd_mul_eq
  Salt.SW.LSeriesSummable_pseudoChar_twist
  Salt.SW.LSeries_pseudoChar_twist_eq
  Salt.SW.LSeries_jutila_coeff_eq
  Salt.SW.LSeriesSummable_jutila_coeff
  Salt.SW.LSeries_jutila_coeff_sum_eq

-- ⟦B2 W7 0905⟧ `Salt/SW/JutilaDetector.lean` — Jutila's LEMMA 6 (L6), whole: the DETECTED
-- Dirichlet polynomial `g(s,χ)`, its Mellin form, THE CONTOUR NODE, and the floor at a zero.
-- (i) the two-level weight's uniform bound `|λ_d| ≤ 1` and Lemma 6's opening split — the `n = 1`
-- term `K(1/x)·Σ'_r r⁻¹` plus the detector, on `1 ≤ x`; (ii) the sizes on the strip
-- `Re s ≥ 1/2`: the local factor `≤ t^{3/2}` (`t ≠ 0` load-bearing), `Σ_{d ≤ z₂} d^{−1/2} ≤ 2√z₂`
-- re-derived here because `GrahamHard2`'s is PRIVATE, and `‖M(s)‖ ≤ 2√z₂·R^{3/2}`; (iii) W4's
-- `r`-summed (2.2) instantiated at W6a's weight, and the ONE vertical integral on `Re w = c > 0`
-- with `1 < β + c` (`kernel_sum_swap_2`, `riesz_tsum_eq`, the unconditional L-series shift);
-- (iv) THE CONTOUR NODE — `φ(w) = w·F(w)` is holomorphic on `Re w > −1` with `φ(0) = 0` at a
-- zero, so `F` IS `dslope φ 0` off `0` and the landed `rectBI_dslope_eq_zero` closes the tall
-- rectangle; the horizontal edges vanish like `T'^{−2}` against `LFunction_growth`, the two
-- verticals become improper integrals by `intervalIntegral_tendsto_integral`, and
-- `tendsto_nhds_unique` shifts `Re w = 2 − β` to `Re w = 1/2 − β`; (v) `∫(m²+t²)^{−3/2} ≤ π/m²`,
-- `∫|t|(m²+t²)^{−3/2} ≤ π/m` and the (2.8) bound
-- `E = 25(T + 2)√q(1 + log q)√z₂ R^{3/2} x^{1/2−β}` at `m = 59/120`; (vi) the floor (2.10) by the
-- reverse triangle inequality against W2's uniform L5; (vii) F5's corollary at the corrected
-- table `(ε, b, a₁, a₂, c) = (1/120, 1/10, 3, 7/2, 13/2)` with `D = qT ≥ 10²⁰`, through
-- `q/φ(q) ≤ ω(q) + 1 ≤ log q/log 2 + 1` (the trivial `φ(q) ≥ 1` does NOT close it) and the
-- linearisation `5625·u ≤ e^{(71/240)u}` for `u ≥ log 10²⁰`. `ζ` never enters and no
-- `vonMangoldt` is formed; `E` is Pólya–Vinogradov-grade, WEAKER than convexity, and the
-- exponent table absorbs the loss with slack `D^{−71/240}`. The two `example`s in the file are
-- the exit rows: the split at `(1, 2, 3, 1, 2, 2)` and the F5 numeral at the threshold. Forty-four
-- `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.abs_bvWeight_le_one
  Salt.SW.abs_sum_bvWeight_divisors_le_card
  Salt.SW.jutilaCoeff_zero
  Salt.SW.jutilaCoeff_one
  Salt.SW.jutilaCoeff_eq_zero_of_le
  Salt.SW.jutilaFull_eq_add_detector
  Salt.SW.norm_jutilaLocal_selbergPsi_le
  Salt.SW.sum_Icc_rpow_neg_half_le
  Salt.SW.norm_jutilaM_selbergPsi_le
  Salt.SW.sum_rFilter_inv_mul_rpow_le
  Salt.SW.norm_jutilaMollifier_le
  Salt.SW.norm_jutilaCoeff_le
  Salt.SW.LSeriesSummable_jutilaCoeff
  Salt.SW.LSeries_jutilaCoeff_eq
  Salt.SW.LSeries_mul_natCast_cpow_neg
  Salt.SW.summable_jutilaCoeff_kernel
  Salt.SW.jutilaFull_eq_tsum
  Salt.SW.jutilaFull_mellin
  Salt.SW.jutilaDetector_mellin
  Salt.SW.jutilaMollifier_differentiable
  Salt.SW.jutilaPhi_differentiableOn
  Salt.SW.jutilaPhi_zero
  Salt.SW.dslope_jutilaPhi_eq
  Salt.SW.rectBI_dslope_jutilaPhi_eq_zero
  Salt.SW.norm_jutilaIntegrand_le
  Salt.SW.norm_inv_denom2_le_abs_im_cube
  Salt.SW.norm_integral_jutilaIntegrand_edge_le
  Salt.SW.norm_inv_denom2_cubic_le_of_min
  Salt.SW.integrable_inv_sq_add_sq_rpow
  Salt.SW.integrable_abs_mul_inv_sq_add_sq_rpow
  Salt.SW.integrable_jutilaIntegrand_line
  Salt.SW.integral_jutilaIntegrand_shift
  Salt.SW.integral_inv_sq_add_sq
  Salt.SW.integral_inv_sq_add_sq_rpow_le
  Salt.SW.integral_abs_mul_inv_sq_add_sq_rpow_le
  Salt.SW.norm_jutilaFull_le
  Salt.SW.jutilaDetector_floor_at_zero
  Salt.SW.div_totient_le_card_primeFactors_add_one
  Salt.SW.card_primeFactors_le_log_div_log_two
  Salt.SW.inv_log_le_totient_div
  Salt.SW.f5_error_bound
  Salt.SW.f5_exp_dominates
  Salt.SW.f5_error_le_main
  Salt.SW.jutilaDetector_floor_F5

-- ⟦B2 W5 0905⟧ `Salt/SW/PseudoCharH.lean` — Jutila's LEMMAS 2 and 3 (L2, L3), whole: the
-- coefficients `h(d; r, r')` of the pseudocharacter product. `hCoef f r r'` is the
-- `ArithmeticFunction` supported on square-free `d` with prime values
-- `h(p) = f_r(p)·f_{r'}(p) − 1` (that is `f(p) − 1` on a prime of exactly one level,
-- `f(p)² − 1` on a common prime, `0` off `r r'` — `pseudoChar_prime_right`, the prime-ARGUMENT
-- evaluation, the mirror of the landed `pseudoChar_prime_left`). Lemma 2 (p.48) is stated twice:
-- over `n.divisors` (`n ≠ 0` load-bearing, `Nat.divisors 0 = ∅`) and over the FINITE range
-- `(r r').divisors` filtered by `d ∣ n`, valid at every `n`. Lemma 3 (p.49) is the orthogonality
-- `Σ_d h(d)/d = δ_{r,r'}·φ(r)` and the size `Σ_d |h(d)| ≤ ∏_{p ∣ r}(p + 1)·∏_{p ∣ r'}(p + 1)`,
-- both for Selberg's `ψ = μ·φ`. One ENGINE row carries all three Euler products: for `g`
-- multiplicative on coprime pairs and vanishing off square-free arguments,
-- `Σ_{d ∣ N} g(d) = ∏_{p ∣ N}(1 + g(p))` at ANY `N ≠ 0` (mathlib's own row needs `N` square-free;
-- the radical reduction is what generalises it, and `N = r r'` is not square-free when `r = r'`).
-- The two `Squarefree` binders on the identity and the orthogonality are load-bearing IN LEAN,
-- as the module docstring's measured receipts record. Nineteen `#audit_axioms` names — sized
-- from THIS LIST.
#audit_axioms Salt.SW.hCoef_apply
  Salt.SW.hCoef_of_squarefree
  Salt.SW.hCoef_of_not_squarefree
  Salt.SW.hCoef_one
  Salt.SW.hCoef_prime
  Salt.SW.pseudoChar_prime_right
  Salt.SW.hCoef_prime_of_not_dvd
  Salt.SW.hCoef_isMultiplicative
  Salt.SW.hCoef_eq_zero_of_not_dvd
  Salt.SW.sum_divisors_eq_prod_primeFactors_of_squarefree_support
  Salt.SW.sum_divisors_hCoef_mul_eq_prod
  Salt.SW.sum_divisors_hCoef_div_eq_prod
  Salt.SW.sum_divisors_abs_hCoef_eq_prod
  Salt.SW.pseudoChar_eq_prod_primeFactors
  Salt.SW.pseudoChar_mul_eq_sum_hCoef
  Salt.SW.pseudoChar_mul_eq_sum_hCoef_filter
  Salt.SW.hCoef_selbergPsi_prime
  Salt.SW.hCoef_sum_div_eq
  Salt.SW.hCoef_abs_sum_le

-- ⟦B2 W1 0905⟧ `Salt/SW/ZeroCountNearOne.lean` — Jutila's LEMMA 8 (Linnik's density lemma) AT
-- HEIGHT: §2's radius-resolved count moved to the centre `1 + it₀`. For a primitive `χ` mod
-- `q ≥ 2`, every real `t₀` and `0 < r < 1/2`, the zeros of `L(·,χ)` in `closedBall (1 + t₀·I) r`
-- (with multiplicity, the `MeromorphicOn.divisor` finsum) number `≤ 7200·(1 + r·log(q+|t₀|+2))`,
-- and in the regime `r ≥ 1/log(q+|t₀|+2)` the `1 +` is absorbed. The route is §2's Landau
-- partial-fraction argument at `σ = 1 + r + t₀·I` inside the Blaschke disk `ball (2 + t₀·I) (3/2)`:
-- the numeric `LFunction_norm_logDeriv_sub_sum'` is already stated at an arbitrary centre, the
-- per-zero geometry is translation-invariant, and the termwise ζ-majorant is re-proved OFF the
-- real axis from `‖χ(n)·n^{−s}‖ = n^{−Re s}` against `−ζ'/ζ(Re s)`. The constant collapses
-- through `log_four_M0_le` at `t = γ = t₀` and `q(|t₀|+2) ≤ (q+|t₀|+2)²`, so the SAME `C = 7200`
-- closes and `t₀ = 0` recovers `LFunction_zero_count_near_one` verbatim (the exit `example`).
-- `7200` is FORCED by this chain (the `r·log` coefficient is `5 × 1440`); the slack is additive
-- only. Four `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.landau_neg_logDeriv_re_lower_of_re
  Salt.SW.re_one_div_sub_ge_at_height
  Salt.SW.LFunction_zero_count_near_one_at_height
  Salt.SW.LFunction_zero_count_near_one_at_height_guarded

-- ⟦B2 W9d 0905⟧ `Salt/SW/WellSpacedAt.lean` — THE `Δ`-SPACED SCHUR SUM, a Mathlib-only LEAF.
-- For a finite `𝒯 ⊆ ℝ` whose distinct points are at least `Δ` apart (`WellSpacedAt`), the
-- off-diagonal sum obeys `Σ_{γ' ∈ 𝒯.erase γ} 1/(γ − γ')² ≤ (π²/3)/Δ²` at every `γ ∈ 𝒯`. The
-- route splits `𝒯.erase γ` at `γ` and indexes each side by `n(x) := ⌊|x − γ|/Δ⌋ ≥ 1`, which is
-- INJECTIVE there (two points sharing an index lie in one half-open interval of length `Δ`, so
-- they are `< Δ` apart — the predicate forbids it) and satisfies `n(x)·Δ ≤ |x − γ|`; each side
-- is then compared with `ζ(2) = π²/6` by `hasSum_zeta_two`, and `2ζ(2) = π²/3`. The constant is
-- TIGHT: the lattice `{0, Δ, 2Δ, …}` at its centre reaches `3.2889` (4001 points) against
-- `π²/3 = 3.2899`. At `Δ = 1` the predicate is `Salt.MR.WellSpaced` verbatim, but that file's
-- closure is eleven Salt modules and nothing in W9 consumes it, so the tie is a docstring
-- sentence and not a row: this file imports Mathlib ONLY. The exit `example` invokes the row at
-- the lattice `{0, 1, 2}`, centre `1` — a point on EACH side, `1 + 1 ≤ π²/3`. One
-- `#audit_axioms` name — sized from THIS LIST.
#audit_axioms Salt.SW.sum_inv_sq_sub_le_of_wellSpacedAt

-- ⟦B2 W9e 0905⟧ `Salt/SW/DensityLogfree.lean` — THE BOXES AT THE SCALE `Δ = 1/log D`: W1 AT
-- HEIGHT PER BOX, WITH W1'S CONSTANT THREADED. `N(σ,T,χ)` is fibred over the boxes
-- `[σ, 1] × [kΔ, (k+1)Δ)`, `k ∈ [−⌈T log D⌉ − 1, ⌈T log D⌉ + 1]` (`boxIndex`, `boxFibre`,
-- `boxIndex_mem_Icc`, `zeroCountM_eq_sum_boxFibre`); each box sits in the disc
-- `closedBall (1 + (k + ½)Δ·I) (Δ·√(λ² + ¼))`, `λ := (1 − σ) log D`
-- (`boxFibre_subset_closedBall` — NO strip binder: the containment is the box's own geometry at
-- every `σ`). W1 at height then counts the disc, its constant carried as the binder `hC₁` (W1 is
-- `∃ C`; the witness `7200` is never a row here): on `D = qT ≥ 10²⁰`, `T ≥ 2`, `q ≥ 2` and the
-- strip `119/120 ≤ σ ≤ 1`, the box's count is `≤ C₁·(7/4 + 3λ/2)` (`efMultTotal_boxFibre_le`),
-- since `√(λ² + ¼) ≤ λ + ½`, `|t₀| ≤ T + 1` and `log(q + T + 3) ≤ log(qT)` there — the numeral
-- `log(10²⁰) = 20(log 2 + log 5) ≥ 46` doing both. `σ ≤ 1` is TRUTH-load-bearing on both count
-- rows: above `1` the box is EMPTY while the bound is NEGATIVE for `λ < −7/6`, and the row is
-- stated for EVERY `k`, so the empty-fibre case needs `0 ≤ RHS`. One representative per box,
-- TOTAL (`boxRep`, the Skolem `dite`; `boxRep_mem`); the representatives of the boxes of one
-- PARITY are `Δ`-well-spaced, because same-parity `k ≠ k'` differ by at least `2`
-- (`wellSpacedAt_parity_reps`); and the count is at most the box bound times the number of
-- NON-EMPTY boxes, the even ones plus the odd ones (`zeroCountM_le_box_bound_mul`). W9f reads
-- the last row with W9c's ratio. Seven `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.boxRep_mem
  Salt.SW.boxIndex_mem_Icc
  Salt.SW.zeroCountM_eq_sum_boxFibre
  Salt.SW.boxFibre_subset_closedBall
  Salt.SW.efMultTotal_boxFibre_le
  Salt.SW.wellSpacedAt_parity_reps
  Salt.SW.zeroCountM_le_box_bound_mul
-- ⟦B2 W9b 0905⟧ `Salt/SW/JutilaResidue.lean` — Jutila's RESIDUE BLOCK `B(s, χ₀)` (pp.52–53), the
-- (ξ,η) device's analytic core, written with the twice-smoothed Riesz kernel `K(u) = (1 − u)²₊` in
-- place of `e^{−u}`. The Halász weight `b_n = n⁻¹(Σ'_{r ≤ R} r⁻¹ψ_r(n))²(K(n/N) − K(n/M))`
-- (`jutilaB`) is expanded by Lemma 2 in its filter form and `n = dm`, the `d^{−1−s}` leaves the
-- `m`-series FIRST (`tsum_trivChar_mul_cpow_eq` — with `(dm)^{−1−s}` on the left the Mellin row is
-- false by exactly `d^{−1−s}` for every `d ≥ 2`), and `kernel_identity_2` + `kernel_sum_swap_2`
-- give the Mellin integral of `2((N/d)^w − (M/d)^w)L(1+s+w, χ₀)/(w(w+1)(w+2))` on `Re w = 1`.
-- ONE contour shift to `Re w = −1/2 − Re s` crosses the single pole `w = −s`: `w = 0` is REMOVABLE
-- (the kernel difference vanishes there — this is why the `M`-term exists), and with mathlib's
-- entire `LFunctionTrivChar₁` the integrand is `(dslope ψ 0)(w)/(w − (−s))`, so `rectBI_cif_eq`
-- extracts `(dslope ψ 0)(−s) = E(χ₀)·resKernel s (N/d) (M/d)` with NO case split at `s = 0` (there
-- it is `ψ'(0)`, Jutila's "interpreted as `log(N/M)`"). On the shifted line the kernel factor is
-- the SUM `(N/d)^{Re w} + (M/d)^{Re w}` — on the LEFT line the `M`-term is the LARGER, and a bound
-- by `2(N/d)^{Re w}` is FALSE there by up to `(1 + (N/M)^{|Re w|})/2` (`1.62` at `(40, 8)`,
-- `Re w = −1/2`) — and the consumer collapses it against the outer `d^{−1−Re s}`
-- (`d^{−1−Re s}(M/d)^{−1/2−Re s} = d^{−1/2}M^{−1/2−Re s} ≤ M^{−1/2}`), never by the split
-- `(M/d)^{−1/2−Re s} ≤ (d/M)^{1/2}`, which is false for `d > M`. The remainder is
-- `‖I(s)‖ ≤ 73·qT·M^{−1/2}·(R(1 + log R))²` for `|Im s| ≤ 2T`, `T ≥ 2`; the `73` is TIGHT — the
-- exact chain is `2[(7/2 + 3|Im s|)/m² + 3/m] = 42.378 + 25.684·|Im s|` at `m = 29/60`, which is
-- `≤ 73T` iff `T ≥ 1.959`. The constants `73`, `7/2 + 3|t|`, `2 + 3‖u‖` are the corpus's
-- (Pólya–Vinogradov-free: ζ's growth here is `norm_riemannZeta_le`'s partial-fraction bound), not
-- Jutila's. Every row is an INPUT to W9's assembly; nothing here bears on twin primes.
-- 37 `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.jutilaB_zero
  Salt.SW.jutilaB_ofReal_eq
  Salt.SW.jutilaB_nonneg
  Salt.SW.jutilaB_eq_zero_of_le
  Salt.SW.jutilaB_eq_of_le
  Salt.SW.jutilaB_pos
  Salt.SW.resKernelFun_zero
  Salt.SW.resKernel_of_ne_zero
  Salt.SW.resKernel_zero
  Salt.SW.norm_resKernel_le_div
  Salt.SW.norm_resKernel_le_log
  Salt.SW.cpow_mul_resKernel_div
  Salt.SW.two_pow_card_primeFactors_le
  Salt.SW.norm_LFunctionTrivChar_le
  Salt.SW.norm_riemannZeta_le_of_half_le
  Salt.SW.norm_riemannZeta_half_le
  Salt.SW.norm_prod_one_sub_inv_le_one
  Salt.SW.summable_trivChar_kern2
  Salt.SW.tsum_trivChar_mul_cpow_eq
  Salt.SW.tsum_trivChar_kern2_eq_integral
  Salt.SW.tsum_trivChar_kern2_diff_eq_integral
  Salt.SW.resPhi_differentiableOn
  Salt.SW.resPhi_zero
  Salt.SW.resIntegrand_eq_dslope_div
  Salt.SW.dslope_resPhi_neg
  Salt.SW.rectBI_resPhi_dslope_div_eq
  Salt.SW.norm_resIntegrand_le
  Salt.SW.norm_integral_resIntegrand_edge_le
  Salt.SW.integrable_resIntegrand_line
  Salt.SW.integral_resIntegrand_shift
  Salt.SW.halaszBTsum_jutilaB_eq_sum
  Salt.SW.halaszBTsum_jutilaB_expand
  Salt.SW.halaszBTsum_jutilaB_eq
  Salt.SW.sum_rFilter_totient_div_sq_le
  Salt.SW.sum_two_pow_card_primeFactors_le
  Salt.SW.sum_rFilter_abs_hCoef_le
  Salt.SW.norm_jutilaI_le

-- ⟦B2 W9a-c 0905⟧ `Salt/SW/JutilaHalasz.lean` — Jutila's §3 (pp.51–53) HALÁSZ INSTANCE at the
-- detector's system, the partial summation, the `S'`-form floor and the two integrated kernel
-- bounds, at a single primitive `χ` mod `q ≥ 2` with `ε = 1/120`. The detector IS a Dirichlet
-- polynomial in the χ-free coefficient `a'_n = a(n)·(Σ'_r r⁻¹ψ_r(n))·K(n/x)·n^{−σ}` at
-- `s = ρ − σ` (`jutilaA`), so W8's Lemma 7 applies with the residue-block weight
-- `b_n = jutilaB q R N M n`: `b_n > 0` wherever `a'_n ≠ 0` on `(z₁, x]` (`M ≤ z₁` kills the
-- `M`-term, `2x ≤ N` keeps `K(n/N) > 0`), the series is finitely supported, and the first Halász
-- factor is `≤ 4·Σ_{n ≤ x} a(n)²n^{1−2σ}` — the CRUDE `K(n/N) ≥ 1/4` on `n ≤ x ≤ N/2` is exactly
-- what `2x ≤ N` buys, and at `N = x/2` the row is FALSE (`18.31 > 9.63` at the toy). The partial
-- summation runs Abel at EVERY scale with `1/2 ≤ σ` — S10-H above `z₂`, S10-L on `[2, z₂]`, the
-- `[1, 2)` sliver absorbed by the constant — and its one analytic step is
-- `Σ_{j ≤ X} j^{−t} ≤ (1 + log X)·X^{1−t}`, proved by induction off `log(X+1) − log X ≥ 1/(X+1)`;
-- no `1/(2σ − 1)` loss appears, and the `log z₂` term is carried ONCE because the telescope is
-- exact. The floor is frozen in the `S'`-FORM (`Σ'_r r⁻¹` UNWEAKENED, Lemma 5 not applied) so
-- that `φ(q)/q` cancels between Halász's two sides and no UPPER bound on the coprime harmonic sum
-- is ever needed; at F5's table the error is at most a third of `S'` (a ratio of the chain's own
-- constants, `D`-uniform), so `‖g(ρ)‖ ≥ S'/2` with the exact rational margin `121/144 − 1/3 −
-- 1/2 = 1/144`. The DIAGONAL integrates the pointwise `‖resKernel s N M‖ ≤ 1.0255·log(N/M)`
-- (`ξ₀ ≥ 0`, i.e. `M = e^ξ ≥ 1`, is TRUTH-load-bearing) with no integrability hypothesis; the
-- OFF-DIAGONAL is a CLOSED FORM — `∫_Ξ∫_H K̃(−s)(e^{−sη} − e^{−sξ}) = K̃(−s)(|Ξ|∫_H − |H|∫_Ξ)`
-- with `‖∫_H e^{−sη}‖ ≤ 2/‖s‖` (needing `η ≥ 0` AND `Re s ≥ 0`) — giving
-- `‖∫∫‖ ≤ 2.051(|Ξ| + |H|)/(Im s)²`, never violated, with C₀'s 2.5 % as the asymptotic margin.
-- THE RATIO `card_system_le_rpow` is NOT here: it is FLAGGED (`B2-W9ac-card_system_le_rpow`) —
-- the device's integration step has no integrable-in-`(ξ, η)` input in the corpus. Every row is
-- an INPUT to W9f; the floor rows are VACUOUS at the object; nothing bears on twin primes.
-- 10 `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.jutilaDetector_eq_dirichletPolyChi
  Salt.SW.jutilaB_pos_of_ne_zero
  Salt.SW.summable_jutilaB_series
  Salt.SW.sum_normSq_jutilaA_div_jutilaB_le
  Salt.SW.sum_sq_sum_bvWeight_mul_rpow_le
  Salt.SW.sq_sum_norm_jutilaDetector_le
  Salt.SW.jutilaDetector_floor_sum
  Salt.SW.jutilaDetector_floor_half_sum
  Salt.SW.integral_norm_resKernel_diag_le
  Salt.SW.norm_integral_resKernel_offdiag_le
-- ⟦B2 W9c-ratio 0906⟧ `Salt/SW/JutilaRatio.lean` — THE RATIO's re-cut: the residue block's
-- integrability over the device's rectangle, the device lemma, and THE RATIO
-- `J ≤ C·(qT)^{13(1−σ)}`. The W9a/c wave flagged `card_system_le_rpow` with its ten inputs
-- landed and ONE named missing: every route to `c·|Ξ||H| ≤ ∫_Ξ∫_H Q` takes `IntervalIntegrable Q`
-- (a non-integrable integrand has interval integral `0` in mathlib, so the LOWER bound is false
-- without it), while the corpus carried bounds on `resKernel`, `jutilaI` and `halaszBTsum` only
-- at a FIXED `(N, M)`. This file supplies it: on the rectangle `e^ξ ≤ e^η ≤ N₁` the residue block
-- is a FINITE sum with a UNIFORM range (`jutilaB q R N M n = 0` for `n ≥ N`), each term
-- continuous in `(ξ, η)`, hence a globally continuous function on `ℝ²` that AGREES with the block
-- on the rectangle; the kernel is continuous in `(ξ, η)` at every `s` (the closed form off `0`,
-- `η − ξ` at `0`); and `jutilaI` needs no row of its own — it is the DIFFERENCE of two continuous
-- integrands through the landed identity. The device lemma integrates a pointwise lower bound
-- over the closed rectangle by `integral_mono_on` twice, its outer integrand continuous by
-- `continuous_parametric_intervalIntegral_of_continuous'`; `hF` is TRUTH-load-bearing (Lean's
-- `∫ = 0` junk value sits on the LOWER side) and so are both orientations. THE RATIO then runs
-- the assembly: the floor `‖g(ρ_j)‖ ≥ S'/2` in the `S'`-form, Halász at the unimodular witnesses
-- with the `/b` bound uniform over the rectangle, the device on the `.re` of the finite-sum form,
-- the expansion per `(j, k)` through the residue-block identity, the diagonal and off-diagonal
-- integrated kernel bounds with the Schur sum, and the `I`-block below `S'²/8` past the
-- threshold. `φ(q)/q` CANCELS between Halász's two sides: `E(χ₀) = ∏_{p ∣ q}(1 − 1/p)` IS
-- `φ(q)/q`, and Lemma 5 is applied exactly once, on the floor's `S'`. `C` and `D₁` are
-- non-effective inside the `∃` (`C_ps` is the partial summation's own `∃`-constant, and `D₁` is
-- produced as a LIMIT, never a closed form); the ratio assumes zeros with `β ≥ 119/120` and is
-- VACUOUS at the object. Nothing here bears on twin primes.
-- 6 `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.halaszBTsum_jutilaB_exp_eq_sum
  Salt.SW.continuous_jutilaB_exp
  Salt.SW.continuous_halaszB_sum_exp
  Salt.SW.continuous_resKernel_exp
  Salt.SW.const_mul_le_integral_integral_of_le
  Salt.SW.card_system_le_rpow

-- ⟦B2 W9f 0905⟧ `Salt/SW/DensityStrip.lean` — THE LOG-FREE ZERO-DENSITY THEOREM, B2's
-- deliverable: `N(σ,T,χ) ≤ C·(qT)^{D(1−σ)}` on `4/5 ≤ σ ≤ 1`, `T ≥ 2`, at a primitive `χ` mod
-- `q ≥ 2`, with `D ≤ 150`. Three suppliers first: at `σ ≥ 1` the count is `0`
-- (`zeroCountM_eq_zero_of_one_le` — the box `σ ≤ Re ≤ 1` is EMPTY by
-- `LFunction_ne_zero_of_one_le_re` at `χ ≠ 1`, which primitivity at `q ≥ 2` supplies); below a
-- threshold `D₀` the `σ`-free crude count is at most the CONSTANT `137(2D₀ + 3)log(D₀(D₀ + 3))`
-- (`zeroCountM_le_const_of_le`; `2 ≤ T` is TRUTH-load-bearing — at the minimal `D₀ = qT < 0.303`
-- that RHS is NEGATIVE while a count never is); and `rpow` is monotone in the exponent above
-- base `1` (`rpow_mul_le_rpow_of_le_150`). THE STRIP (`zeroCountM_density_logfree_strip`, the
-- literal `14 = 2c + 1`) assembles W9e's boxes with W1's constant threaded, W9c′'s RATIO at each
-- parity's representatives, the crude count below `D₀ := max(10²⁰, D₁)` and the non-vanishing at
-- `σ = 1`. The per-parity system is staged as ONE private lemma over an ABSTRACT Finset of box
-- indices: the representatives are zeros with `Re < 1` (the non-vanishing), injectively indexed
-- by their ordinates (`boxIndex` reads `Im` alone and `boxRep k` lies in the `k`-th fibre), and
-- `Δ`-well-spaced BY ANTITONY of `WellSpacedAt` in its Finset — so the image INCLUSION is the
-- whole bridge from `wellSpacedAt_parity_reps`, with no equiv round-trip; `Finset.equivFin`
-- indexes the system as `Fin #S`. The closing chain: `7/4 + 3λ/2 ≤ (7/4)e^{λ}` (equality at
-- `λ = 0`), `e^{λ} = (qT)^{1−σ}` and `(qT)^{13(1−σ)}·(qT)^{1−σ} = (qT)^{14(1−σ)}`, with
-- `C = max(137(2D₀ + 3)log(D₀(D₀ + 3)), (7/2)C₁C_r)`. THE TARGET
-- (`zeroCountM_density_logfree`) glues the landed low half (`1378·(qT)^{150(1−σ)}` on
-- `[4/5, 119/120]`) to the strip lifted to the exponent `150` by the glue; `C = max 1378 C_s`,
-- `D = 150`, and the seam is exact (`150(1 − σ) = 5/4` at `σ = 119/120`, the low half's own
-- crude exponent). `C` is NON-EFFECTIVE (W1's `∃`, the ratio's `∃ C_r` and its threshold
-- `D₁ = 10^59–10^64`, S10's `∃ K`); `2 ≤ T` on the TARGET is TRUTH-load-bearing through a
-- NEGATIVE base (at `q = 3`, `T = −1`, `σ = 9/10` the count is `0` while
-- `Real.rpow (−3) 15 < 0`), on the STRIP JUNK-TRUE (its exponent `14(1 − σ) ≤ 0.1167` never
-- crosses the first `cos(πy)` zero). Landing this file lands B2 WHOLE; nothing here bears on
-- twin primes beyond stating B2's own condition.
-- 5 `#audit_axioms` names — sized from THIS LIST.
#audit_axioms Salt.SW.zeroCountM_eq_zero_of_one_le
  Salt.SW.zeroCountM_le_const_of_le
  Salt.SW.rpow_mul_le_rpow_of_le_150
  Salt.SW.zeroCountM_density_logfree_strip
  Salt.SW.zeroCountM_density_logfree
