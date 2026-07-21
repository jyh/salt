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
  (`log‖ζ(s)‖ = ∑'_p Re(−log(1−p^{−s}))`, `Re s > 1`).  RESIDUAL (single, flagged
  MR-W3): the `σ = 1` oscillating prime truncation `∑_{p≤x} cos(t·log p)/p` vs the
  full log-Euler sum (EulerLink R5-FINISH open gap) — closes `lambda_nonpret`.
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
