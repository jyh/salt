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
#audit_axioms Salt.SW.psi1Chi_eq_sum_psi1AP Salt.SW.psi1_fold
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
