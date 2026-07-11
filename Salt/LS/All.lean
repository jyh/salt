/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Dist

/-!
# Rung 5 opener (`largesieve`) — aggregate import

The large sieve → BDH → Vaughan track. Design:
`docs/blueprints/largesieve.md`. Extended as modules land; wired into
`Salt.lean` from the first commit so the bare `lake build` covers the track.

Landed: `Dist` (L0.2 — the mod-1 circle distance `dist₁`, round-based,
full spec incl. triangle inequality and the integer-difference
characterization).
-/
