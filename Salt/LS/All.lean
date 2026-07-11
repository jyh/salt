/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Dist
import Salt.LS.Defs
import Salt.LS.Parseval
import Salt.LS.Gallagher
import Salt.LS.Farey

/-!
# Rung 5 opener (`largesieve`) — aggregate import

The large sieve → BDH → Vaughan track. Design:
`docs/blueprints/largesieve.md`. Extended as modules land; wired into
`Salt.lean` from the first commit so the bare `lake build` covers the track.

Landed: `Dist` (L0.2 — the mod-1 circle distance `dist₁`, round-based,
full spec incl. triangle inequality and the integer-difference
characterization); `Defs` (L0.1 — the frozen carriers `e`/`expSum` +
trivia, `@[fun_prop]`-tagged continuity); `Parseval` (L1.1 orthogonality +
L1.2 **Parseval** `∫₀¹‖expSum‖² = Σ‖aₙ‖²`); `Gallagher` (L4.1 — the
Sobolev/Gallagher pointwise lemma, `ContDiff ℝ 1` form, frozen constant 2).
W1 probe verdict: GO — keystone risk retired, Gallagher route ratified.
`Farey` (L6.1 — `farey_spacing_core` at `1/(q·q')` + `farey_spacing` at
`1/Q²`, coprimality-free).
-/
