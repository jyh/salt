/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.QuadCharSum
import Salt.Tactic.AuditAxioms

/-!
# The Heath-Brown track (`HB`) — aggregate import

HB-ENGINE: the formalization of Heath-Brown, *Prime twins and
Siegel zeros* (Proc. LMS (3) 47 (1983) 193–224) — infinitely many
Siegel zeros imply infinitely many prime twins. The campaign map
(seven work packages, re-frozen against the source PDF) lives in
`docs/exploration/s3-hb3-design.md`; the WP2 L-function nodes land
in `Salt/SW/`; the Kloosterman/Weil inputs are banked in
`Salt/Weil/` (HB-FOUND).
-/

open Salt.Tactic in
#audit_axioms Salt.HB.quadraticChar_sum_two_forms_bound
  Salt.HB.quadraticChar_sum_mul_shift
  Salt.HB.quadraticChar_sum_two_forms_trivial
  Salt.HB.legendre_sum_mul_shift
  Salt.HB.legendre_sum_two_forms_bound
  Salt.HB.legendre_sum_two_forms_trivial
