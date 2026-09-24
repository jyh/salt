/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Frame
import Salt.HardyLittlewood.Sharp
import Salt.Tactic.AuditAxioms

/-!
# The Hardy–Littlewood track (`HardyLittlewood`) — aggregate import

The twin-prime Hardy–Littlewood frame (rung revived by JYH,
2026-07-17): the formal conjecture statement `HardyLittlewoodTwin`
(π₂(x) ~ 𝔖·x/log²x with 𝔖 = 2Π₂), the singular series `Pi2` as an
honest convergent Euler product (reusing the twin-bar `twinC2`
theory), and the order-sharp upper wrapper (Brun/Selberg C=25700).
The sharp `(4+ε)·𝔖` constant is the registered HL-3b arc, gated on
Mertens' third theorem (see `docs/exploration/pilot.md`).
⟦ERRATUM 2026-09-24 (the sentence above is left as written): HL-3b LANDED 2026-07-18 at
`C = 90` (`twinCounting_upper_sharp`, `Sharp.lean`), not at `(4+ε)·𝔖`; the `(4+ε)·𝔖 = 8·Π₂`
target is the registered **HL-3c**, which has never fired. Its named gate is no longer a
gate: Mertens' third theorem landed 2026-07-17 (`Salt/Mertens/Third.lean`) with the twin
corollary MERT-5 (`Salt/Mertens/TwinDensity.lean`), which `Sharp.lean` imports. What HL-3c
lacks is the κ = 2 singular-series density mean value, not Mertens.⟧
-/

open Salt.Tactic in
#audit_axioms Salt.HardyLittlewood.twinCounting_upper_sharp
  Salt.HardyLittlewood.sum_six_pow_omega_le
  Salt.HardyLittlewood.pi2_pos
  Salt.HardyLittlewood.pi2_lt_one
  Salt.HardyLittlewood.pi2_multipliable
  Salt.HardyLittlewood.twinSingularSeries_pos
  Salt.HardyLittlewood.twinSingularSeries_lt_two
  Salt.HardyLittlewood.twinCounting_upper_order
