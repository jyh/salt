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
import Salt.Tactic.AuditAxioms

/-!
# The Weil track (`weil`) — aggregate import

The gold thread: the Weil bound |S(a,b;p)| ≤ 2√p via elementary
Stepanov (Harcos/IK Ch. 11; the ladder in docs/exploration/pilot.md
~13:30). Wave 1 (foundations) landed 2026-07-18.
-/

open Salt.Tactic in
#audit_axioms Salt.Weil.kloosterman_mul_of_coprime
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
