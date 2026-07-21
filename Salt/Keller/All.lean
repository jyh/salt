/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Keller.Counterexample
import Salt.Tactic.AuditAxioms

/-!
# The Keller track (`Keller`) — aggregate import

Topical verification (2026-07-21): the first kernel-certified check of the
counterexample to the Jacobian conjecture (Alpöge/Mathew/Fable preprint,
2026-07-20). `Salt/Keller/Counterexample.lean` is fully self-contained
(imports Mathlib only): the formal Jacobian determinant identity
`det Jac F = −2` over ℚ and the three-point fiber collision
`F(0,0,−1/4) = F(1,−3/2,13/2) = F(−1,3/2,13/2) = (−1/4,0,0)`, hence a
non-injective Keller map over ℚ and over ℂ. Verified AS STATED in the
preprint (double-entry transcription). NOT verified here: the preprint's
global-geometry sections, properness at infinity, and the stabilization to
dimensions > 3.
-/

#audit_axioms Keller.jacobian_det
  Keller.eval_point0
  Keller.eval_point1
  Keller.eval_point2
  Keller.points_pairwise_distinct
  Keller.keller_not_injective
  Keller.jacobian_conjecture_counterexample
  Keller.keller_not_injective_C
