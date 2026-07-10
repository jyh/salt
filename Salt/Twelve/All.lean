/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.Params
import Salt.Twelve.Certificate
import Salt.Twelve.MomentAtom
import Salt.Twelve.PhiUpper
import Salt.Twelve.MarkedPrime
import Salt.Twelve.BudgetPoly
import Salt.Twelve.BudgetMoment

/-!
# Rung 4a (`explicit12`) — aggregate import

Explicit bounded gaps `≤ 12` from `WindowPNT` + `EHall`, via Maynard's `k = 5`
polynomial sieve. Design: `docs/blueprints/explicit12-design.md`.

Wave 1 (landed): `Certificate` (`M5_cert : M₅ > 2` in exact ℚ), `Params`
(`WindowPNT`/`EHall`, `hSeq 5 = {7,11,13,17,19}`, `diam ≤ 12`, spine audit),
`MomentAtom` (the one-dim moment atom, conditional on the narrow `PhiUpperAtom`).

Wave 2 (landed): `BudgetMoment` (`beta_sum` + `budget_moment`, the normalized
budget-factor moment via Crux 3), `MarkedPrime` (`marked_prime_phi`, the
single-prime marked-sum engine), `BudgetPoly` (the symbolic ℚ layer + ties to
`Certificate`), and `PhiUpper`'s analytic core (`powerful_sum_bounded`;
`phiUpperAtom_holds` discharges `PhiUpperAtom` modulo the `hReindex` residual).
PORT-BLOCKERs deferred to FABLE-QUEUE: `budget_moment_g` (composite marked sum),
`marked_prime_g` (unneeded), `hReindex` (powerful/squarefree reindex).
-/
