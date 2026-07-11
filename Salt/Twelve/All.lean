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
import Salt.Twelve.W3Prep
import Salt.Twelve.MvMoment
import Salt.Twelve.BudgetMomentG
import Salt.Twelve.MvMomentG
import Salt.Twelve.MvI
import Salt.Twelve.MvJ

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

Wave 3 (landed): `W3Prep` (`marked_sqf_phi` composite marked atom, `eval_mul/sq`,
`log_natCap_slip`), `MvMoment` (`decBox` + `mv_monomial`, the general-`n` moment
workhorse), `BudgetMomentG` (`marked_sqf_g` + `budget_moment_g`, the g-sandwich —
drained the `budget_moment_g` FABLE-QUEUE item), `MvMomentG` (`mv_monomial_g`, the
g-weighted workhorse), and the two keystones **`MvI`** (`mv_I` : the 5-dim first
moment `X⁵·simplexInt (sq (ofPoly F))`) and **`MvJ`** (`inner_contract` + `mv_J` :
the 4+2-dim second moment `X⁶·simplexInt (sq (contractAt m F))`). At `F★` these
conclude, via the `BudgetPoly` ties, `X⁵·Ical F★` and `X⁶·Σ_m Jcal m F★`.
PORT-BLOCKERs still in FABLE-QUEUE: `marked_prime_g` (unneeded dead-end record),
`hReindex` (powerful/squarefree reindex; non-blocking).
-/
