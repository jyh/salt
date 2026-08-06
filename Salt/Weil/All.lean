/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman
import Salt.Weil.ArtinSchreier
import Salt.Weil.Orbits
import Salt.Weil.LocalFactor
import Salt.Weil.Stepanov
import Salt.Weil.Moments
import Salt.Weil.StepanovCore
import Salt.Weil.PointCount
import Salt.Weil.Composite
import Salt.Weil.LFunction
import Salt.Weil.StepanovSolve
import Salt.Weil.PrimePower
import Salt.Weil.WeilStepanov
import Salt.Weil.CompositeTail
import Salt.Weil.MomentOrbit
import Salt.Weil.NewtonBridge
import Salt.Weil.MomentEigen
import Salt.Weil.CurveBridge
import Salt.Weil.MultiExtract
import Salt.Weil.Descent
import Salt.Weil.Incomplete
import Salt.Weil.CompositeFull
import Salt.Weil.GcdBranch
import Salt.Weil.Estermann
import Salt.Tactic.AuditAxioms

/-!
# The Weil track (`weil`) — aggregate import

The gold thread: the Weil bound |S(a,b;p)| ≤ 2√p via elementary
Stepanov (Harcos/IK Ch. 11; the ladder in docs/exploration/pilot.md
~13:30). Wave 1 (foundations) landed 2026-07-18.
-/

open Salt.Tactic in
#audit_axioms Salt.Weil.norm_kloosterman_le_tau_sqrt
  Salt.Weil.norm_kloosterman_prime_pow_ge_two
  Salt.Weil.norm_kloosterman_prime_pow_odd
  Salt.Weil.kloosterman_zero_right
  Salt.Weil.norm_kloosterman_prime_unit
  Salt.Weil.norm_incomplete_kloosterman_le
  Salt.Weil.norm_kloosterman_le_two_sqrt
  Salt.Weil.norm_kloosterman_le_two_sqrt'
  Salt.Weil.norm_localRoots_eq_sqrt
  Salt.Weil.forall_norm_le_of_powerSum_bound
  Salt.Weil.norm_eq_sqrt_of_pair_of_le
  Salt.Weil.norm_add_le_two_mul_sqrt
  Salt.Weil.sum_kloostermanMoment_eq_pointCount
  Salt.Weil.sum_kloostermanMoment_erase_zero_eq
  Salt.Weil.card_kloosterman_fiber
  Salt.Weil.curvePoly_not_isSquare
  Salt.Weil.sum_card_fiber_eq_pointCount
  Salt.Weil.curvePoly_natDegree
  Salt.Weil.curvePoly_coeff_zero_ne_zero
  Salt.Weil.kloostermanMoment_zero_zero
  Salt.Weil.kloostermanMoment_eq_neg_localPowerSum
  Salt.Weil.newton_bridge
  Salt.Weil.kloostermanMoment_eq_cCoeff
  Salt.Weil.norm_kloosterman_le_mul_of_coprime_unit
  Salt.Weil.weil_stepanov
  Salt.Weil.norm_kloosterman_prime_pow_even
  Salt.Weil.stepanov_solution_exists
  Salt.Weil.stepanov_one_sided_card_le
  Salt.Weil.eta_mul Salt.Weil.T5_a1 Salt.Weil.T5_a2 Salt.Weil.T5_ad
  Salt.Weil.kloosterman_mul_of_coprime
  Salt.Weil.norm_kloosterman_le_mul_of_coprime
  Salt.Weil.pointCount_sub_card
  Salt.Weil.stepanov_locus_card_le
  Salt.Weil.exists_quotient_hasseDeriv_mul_pow
  Salt.Weil.stepanov_dimension_count
  Salt.Weil.stepanovAux_dvd_of_reduced_eval_zero
  Salt.Weil.stepanov_multiplicity_card_le
  Salt.Weil.kloostermanMoment_one
  Salt.Weil.sum_kloostermanMoment_twist Salt.Weil.kloostermanMoment_im
  Salt.Weil.stepanovAux_ne_zero
  Salt.Weil.X_pow_dvd_of_range_sum_eq_zero
  Salt.Weil.stepanovAux_natDegree_le
  Salt.Weil.localPowerSum_rec Salt.Weil.localPowerSum_im
  Salt.Weil.abs_le_sqrt_of_powerSum_bound
  Salt.Weil.irreducible_monic_dvd_X_pow_card_pow_sub_X_iff
  Salt.Weil.squarefree_X_pow_card_pow_sub_X
  Salt.Weil.galoisField_minpoly_natDegree_dvd
  Salt.Weil.trace_surjective
  Salt.Weil.range_artinSchreier_eq_ker_trace
  Salt.Weil.card_artinSchreier_solutions
  Salt.Weil.norm_kloosterman_le_sub_one
  Salt.Weil.kloosterman_conj Salt.Weil.kloosterman_reindex_units
  Salt.Weil.X_sub_C_pow_dvd_iff_hasseDeriv
  Salt.Weil.galoisField_trace_eq_sum_frobenius

/-! ### WEIL-TRIO W1 — the Estermann prime-power grade (2026-08-06)

`Salt.Weil.GcdBranch` (W1-a/b/d) + `Salt.Weil.Estermann` (W1-c). The exit row N7 quotes is
`norm_kloosterman_prime_pow_gcd`: `‖S(A,B;p^e)‖ ≤ 2·√(p^e)·√((p^e,A,B))` at an odd prime `p`,
arbitrary `e ≥ 1` and arbitrary `A, B` — constant `c_e = 2` uniformly, hence
`∏_p c_{e_p} = 2^{ω(k)} ≤ d(k)` for the composite assembly (W3). The 2-adic bookkeeping row is
`factorization_two_kloosterman_modulus` (HB (5.1)+(5.6)+(1.5) ⟹ `v₂(D·δ₁·w₁) = v₂(D)`). -/
open Salt.Tactic in
#audit_axioms Salt.Weil.stdAddChar_mul_descend
  Salt.Weil.stdAddChar_pow_descend
  Salt.Weil.unitsMap_prime_pow_fiber_card
  Salt.Weil.kloosterman_descent
  Salt.Weil.kloosterman_eq_sum_crit
  Salt.Weil.isUnit_of_prime_pow_iff
  Salt.Weil.prime_pow_cast_ne_zero
  Salt.Weil.kloosterman_zero_right_prime_pow
  Salt.Weil.norm_kloosterman_zero_right_prime_pow
  Salt.Weil.odd_of_coprime_of_two_dvd
  Salt.Weil.factorization_two_mul_odd_mul_odd
  Salt.Weil.factorization_two_kloosterman_modulus
  Salt.Weil.two_pow_factorization_dvd_of_odd_cofactors
  Salt.Weil.pj_cube_eq_zero
  Salt.Weil.klSummand_mul_ushift3
  Salt.Weil.crit_mul_ushift3
  Salt.Weil.norm_quadExpSum
  Salt.Weil.castHom_eq_zero_iff_not_isUnit
  Salt.Weil.norm_kloosterman_prime_pow_odd_sharp
  Salt.Weil.norm_kloosterman_prime_pow_unit_sharp
  Salt.Weil.norm_kloosterman_prime_pow_gcd
