/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Taylor
import Salt.Vk.Shift
import Salt.Vk.BoxAvg
import Salt.Vk.BoxMeasure
import Salt.Vk.Pointwise
import Salt.Vk.Block
import Salt.Vk.Spacing
import Salt.Vk.Core
import Salt.Vk.Landau
import Salt.Vk.Strip
import Salt.Vk.Scale
import Salt.Vk.Region
import Salt.Vk.RegionGrowth
import Salt.Vk.Littlewood
import Salt.Vk.Windows
import Salt.Vk.Window
import Salt.Vk.Mid
import Salt.Vk.Growth
import Salt.Vk.PowRegion
import Salt.Vk.GrowthPow
import Salt.Vk.Twist
import Salt.Vk.TwistLadder
import Salt.Vk.TwistHigh
import Salt.Tactic.AuditAxioms

/-!
# The Vinogradov–Korobov track (`Vk`) — aggregate import

THE VMVT-VK CAMPAIGN (JYH ratified 2026-07-18: the power zero-free region
`σ ≥ 1 − c/((log t)^{3/4}(log log t)^3)` from the machine-checked
`Salt.Vmvt.vmvt`, merged with the Littlewood chain; the minimal-power
route θ = 3/4 < 1, MR-gate-satisfying). Freeze: `docs/exploration/vk-freeze.md`;
numeric refuter `scripts/vk_minpow_check.py`.

Opening wave: R1 `VK-TAYLOR` (block Taylor of the ζ-phase), R2 `VK-SHIFT` (the `2π`-Lipschitz
character + block reduction + shift identity), R3 `VK-BOX-AVG` + R4 `VK-POINTWISE` (`vk_block_core`,
the bridge from `Salt.Vmvt.vmvt`).

VK-4 wave (`Landau`/`Strip`/`Scale`): R7 `VK-LANDAU-SCALED` (`entire_norm_logDeriv_sub_sum_scaled`,
the parametric-radius Landau core = LITT-LANDAU), R10 `VK-STRIP-PATCH` (`zeta_block_strip`, the
diagonal-strip `√N` bound = LITT-COVER stone-3), R5-assembly (`vk_sum_Ioc_split`(`_norm_le`), the
general-partition block split). Residuals (R5b window discharge, R6/R8/R9, region):
`docs/blueprints/flags.md` node `VMVT-VK`.
-/

open Salt.Tactic in
#audit_axioms Salt.Vk.log_series_remainder
  Salt.Vk.phi_taylor_block
  Salt.Vk.phi_taylor_block_PY
  Salt.Vk.eR_lipschitz
  Salt.Vk.norm_sum_eR_sub_le
  Salt.Vk.block_reduction
  Salt.Vk.sum_Ioc_shift_boundary
  Salt.Vk.genFun_eq_eR_sum
  Salt.Vk.genFun_lipschitz
  Salt.Vk.genFun_box_variation
  Salt.Vk.eR_intCast
  Salt.Vk.genFun_add_int
  Salt.Vk.vk_box_disjoint_avg
  Salt.Vk.unitMeasure_Ioc_toReal
  Salt.Vk.vkBox_measurable
  Salt.Vk.clip_width_ge
  Salt.Vk.vkBox_measureReal_ge
  Salt.Vk.vkBox_disjoint
  Salt.Vk.vk_box_disjoint_avg_of_centers
  Salt.Vk.poly_shift_orbit
  Salt.Vk.genFun_fract
  Salt.Vk.fract_mem_Icc
  Salt.Vk.vk_shift_genFun_phase
  Salt.Vk.norm_vk_shift_sum
  Salt.Vk.vk_pow_sum_le
  Salt.Vk.vk_shift_average
  Salt.Vk.vk_shift_to_orbit
  Salt.Vk.vk_block_taylor_reduce
  Salt.Vk.fract_sub_abs_ge
  Salt.Vk.vkCoef_abs
  Salt.Vk.choose_mul_sub_le
  Salt.Vk.pow_diff_abs_le
  Salt.Vk.orbit_term_bound
  Salt.Vk.orbit_tail_geom_le
  Salt.Vk.vkOrbit_diff_sub_linear_bound
  Salt.Vk.vkOrbit_linear_abs
  Salt.Vk.vk_orbit_fract_sep
  Salt.Vk.vk_eta_le
  Salt.Vk.vk_const_le
  Salt.Vk.vkDelta_prod_inv
  Salt.Vk.vkDelta_slack_le
  Salt.Vk.vk_exp_ineq
  Salt.Vk.vk_two_Y_le
  Salt.Vk.vk_block_core
  Salt.Vk.entire_norm_logDeriv_sub_sum_scaled
  Salt.Vk.log_2diff_upper
  Salt.Vk.log_2diff_lower
  Salt.Vk.zeta_block_strip
  Salt.Vk.vk_sum_Ioc_split
  Salt.Vk.vk_sum_Ioc_split_norm_le
  Salt.Vk.riemannZeta_conj
  Salt.Vk.riemannZeta_conj_zero
  Salt.Vk.Zc_ratio_sphere_bound
  Salt.Vk.zeta_keep_one_disc
  Salt.Vk.zeta_drop_all_disc
  Salt.Vk.zeta_zero_free_of_disc
  Salt.Vk.region_of_uniform_growth
  Salt.Vk.littlewood_uniform_growth
  Salt.Vk.zeta_zero_free_littlewood_core
  Salt.Vk.littlewood_bracket
  Salt.Vk.zeta_zero_free_region_littlewood
  Salt.Vk.vk_ladder_bound
  Salt.Vk.vk_window_bound
  Salt.Vk.vk_logP_ge
  Salt.Vk.vk_logP_ub
  Salt.Vk.vk_hW2c_form
  Salt.Vk.vk_hW2b_form
  Salt.Vk.vk_hW1_form
  Salt.Vk.vk_hW2a_form
  Salt.Vk.vk_window_scale
  Salt.Vk.vk_window_mid
  Salt.Vk.zeta_sub_dirichlet_bound
  Salt.Vk.vkTheta_anti
  Salt.Vk.vkTheta_pos
  Salt.Vk.pow_uniform_growth
  Salt.Vk.zeta_zero_free_pow_core
  Salt.Vk.zeta_zero_free_region_pow_of_growth
  Salt.Vk.vk_ladder_prefix
  Salt.Vk.vk_window_prefix
  Salt.Vk.vk_window_scale_prefix
  Salt.Vk.vk_window_mid_prefix
  Salt.Vk.vk_dirichlet_block_le
  Salt.Vk.vk_dirichlet_sum_le
  Salt.Vk.zeta_growth_pow
  Salt.Vk.zeta_zero_free_region_pow
  Salt.Vk.twistCoef_of_two_le
  Salt.Vk.twistCoef_sum_Icc
  Salt.Vk.phi_taylor_block_twist
  Salt.Vk.phi_taylor_block_twist_PY
  Salt.Vk.vkOrbit_congr
  Salt.Vk.vkOrbit_twistCoef
  Salt.Vk.vkOrbitPoint_twistCoef
  Salt.Vk.vk_block_taylor_reduce_twist
  Salt.Vk.vk_block_core_twist
  Salt.Vk.vk_window_bound_twist
  Salt.Vk.vk_window_prefix_twist
  Salt.Vk.vk_window_scale_twist
  Salt.Vk.vk_window_scale_prefix_twist
  Salt.Vk.vk_window_mid_twist
  Salt.Vk.vk_window_mid_prefix_twist
  Salt.Vk.vk_weighted_block_twist
  Salt.Vk.vk_dirichlet_block_twist_le
  Salt.Vk.vk_dirichlet_block_twist_le_of_high
  Salt.Vk.zeta_block_dispatch_twist
  Salt.Vk.vk_dirichlet_block_twist_all
