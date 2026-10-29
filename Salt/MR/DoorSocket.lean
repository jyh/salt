/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12Compose

/-!
# The door socket (`DoorSocket`)

The door consumers set the socket threshold `δs := s12DeltaSock δ₀ Kc` and its grade
`ρ := doorRhoOfDelta δs`, then re-derive the same four facts (`0 < δs`, `δs ^ 2 = δ₀ / (16 · Kc)`,
`0 < ρ`, `ρ ≤ 1`); at gate 9 they re-derive `2 · δs ^ 2 = δ₀ / (8 · Kc)` by `field_simp`. This module
states both once (the tactics catalogue's door-socket block and its gate-9 tail). At a site the facts
are obtained BEFORE the two `set`s, so the `set`s rewrite them into `δs` and `ρ`.
-/

namespace Salt.MR

/-- The four socket facts at `δs = s12DeltaSock δ₀ Kc` and `ρ = doorRhoOfDelta δs`, for `0 < δ₀` and
`0 < Kc`: `0 < δs`, `δs ^ 2 = δ₀ / (16 * Kc)`, `0 < ρ` and `ρ ≤ 1`. -/
theorem door_socket_facts {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀) (hKc : 0 < Kc) :
    0 < s12DeltaSock δ₀ Kc ∧ s12DeltaSock δ₀ Kc ^ 2 = δ₀ / (16 * Kc) ∧
      0 < doorRhoOfDelta (s12DeltaSock δ₀ Kc) ∧ doorRhoOfDelta (s12DeltaSock δ₀ Kc) ≤ 1 :=
  ⟨s12DeltaSock_pos hδ₀ hKc, s12DeltaSock_sq hδ₀ hKc,
    doorRhoOfDelta_pos (s12DeltaSock_pos hδ₀ hKc).ne', doorRhoOfDelta_le_one _⟩

/-- `2 * s12DeltaSock δ₀ Kc ^ 2 = δ₀ / (8 * Kc)` for `0 < δ₀` and `0 < Kc` (`s12DeltaSock_sq`,
doubled): the gate-9 budget line. -/
theorem s12DeltaSock_sq_two {δ₀ Kc : ℝ} (hδ₀ : 0 < δ₀) (hKc : 0 < Kc) :
    2 * s12DeltaSock δ₀ Kc ^ 2 = δ₀ / (8 * Kc) := by
  rw [s12DeltaSock_sq hδ₀ hKc]
  field_simp
  ring

end Salt.MR
