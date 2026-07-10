/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.Params
import Salt.Twelve.Certificate
import Salt.Twelve.MomentAtom

/-!
# Rung 4a (`explicit12`) — aggregate import

Explicit bounded gaps `≤ 12` from `WindowPNT` + `EHall`, via Maynard's `k = 5`
polynomial sieve. Design: `docs/blueprints/explicit12-design.md`.

Wave 1 (landed): `Certificate` (`M5_cert : M₅ > 2` in exact ℚ), `Params`
(`WindowPNT`/`EHall`, `hSeq 5 = {7,11,13,17,19}`, `diam ≤ 12`, spine audit),
`MomentAtom` (the one-dim moment atom, conditional on the narrow `PhiUpperAtom`).
-/
