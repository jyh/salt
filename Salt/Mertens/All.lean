/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Mertens.PrimePower
import Salt.Mertens.Second
import Salt.Mertens.ZetaSide
import Salt.Mertens.GammaIntegral
import Salt.Mertens.Third
import Salt.Mertens.TwinDensity
import Salt.Tactic.AuditAxioms

/-!
# The Mertens track (`Mertens`) — aggregate import

The MERTENS arc (JYH ratified 2026-07-17): Mertens' third theorem
∏_{p≤x}(1−1/p) = e^{−γ}/log x·(1+O(1/log x)) via the Abelian
route (M = γ − B), gating HL-3b's sharp (4+ε)·2Π₂ constant and a
first-class mathlib upstream target. Arc map: MERT-R0's
adjudication in `docs/exploration/pilot.md`.
-/

open Salt.Tactic in
#audit_axioms Salt.Mertens.integral_exp_neg_log
  Salt.Mertens.loglog_integral_asymp
  Salt.Mertens.primeZeta_tendsto
  Salt.Mertens.logZetaReal_eq
  Salt.Mertens.mertens_second_sharp
  Salt.Mertens.mertensB_nonneg
  Salt.Mertens.mertensB_le_two
  Salt.Mertens.neg_log_prod_eq
  Salt.Mertens.mertensB_tail_le
  Salt.Mertens.mertensM_eq_sub
  Salt.Mertens.mertens_M_unique
  Salt.Mertens.mertens_second_sharp'
  Salt.Mertens.abel_primeZeta
  Salt.Mertens.mertens_third_log
  Salt.Mertens.mertens_third
  Salt.Mertens.abs_prodFactor_sub_twinC2_le
  Salt.Mertens.mertens_twin_density
  Salt.Mertens.mertens_twin_density_singularSeries
