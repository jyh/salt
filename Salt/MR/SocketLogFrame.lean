/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The log frame at a socket base

A flat-door terminal instance opens a socket prefix
`Hlo ≤ H ∧ H ≤ Hhi ∧ L ≤ H ∧ 0 < q ∧ _ ∧ _ ∧ _ ∧ 0 < A ∧ _` and a cap grid whose `logX_eight` field
reads `8 ≤ log (A + s)`. Each instance then derives, by hand, the same six facts: `1 ≤ q`, `0 < A`,
`1 ≤ A + s`, `0 < log (A + s)`, `0 < (log (A + s))^(1/2)` and
`30·(log (A + s))^(1/2) + 1 ≤ exp (30·(log (A + s))^(1/2))`. This file states them once.

The 11 call sites that took them inline are in `FlatDoorStandoff`, `S13CapGateLinearLH`,
`S16Budget`, `S16ComposeLH`, `StrideDoorAllGrades`, `V6SiegelFree` and `V7SiegelFree`. Six more,
in `RegisterCompose`, `S16Compose`, `S16ComposeV4`, `S16FlatFinal`, `V7B` and `V7Ks`, are left
inline for now: line cites elsewhere read those files, and moving them would widen this change.
The lemma is over propositions, naturals and reals and imports nothing beyond Mathlib.

## Main results
* `socketLogFrame_facts` — the six frame facts from the socket prefix and the log floor.
-/

namespace Salt.MR

/-- **The log frame.** From a socket prefix carrying `0 < q` in fourth place and `0 < A` in eighth,
and the floor `8 ≤ log (A + s)`: `1 ≤ q`, `0 < A`, `1 ≤ A + s`, `0 < log (A + s)`,
`0 < (log (A + s))^(1/2)` and `30·(log (A + s))^(1/2) + 1 ≤ exp (30·(log (A + s))^(1/2))`. -/
theorem socketLogFrame_facts {P₁ P₂ P₃ P₅ P₆ P₇ R : Prop} {q A : ℕ} (s : ℕ)
    (hb : P₁ ∧ P₂ ∧ P₃ ∧ 0 < q ∧ P₅ ∧ P₆ ∧ P₇ ∧ 0 < A ∧ R)
    (h8 : (8 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)) :
    1 ≤ q ∧ 0 < A ∧ 1 ≤ A + s ∧ (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) ∧
      (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) ∧
      30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
        ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := by
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  exact ⟨hb.2.2.2.1, hA, by omega, hlogX0, Real.rpow_pos_of_pos hlogX0 _, Real.add_one_le_exp _⟩

end Salt.MR
