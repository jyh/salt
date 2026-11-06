/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The window's two endpoints at `Tann = 2T`

Every row instance of the A2 ladder that reads its window at the doubled height `Tann = 2T`
derives the same three facts by hand before it calls the row: the lower endpoint
`2·(X/h) ≤ 2·T`, the upper endpoint `2·T ≤ X`, and `0 < 2·T`. The last comes from
`0 < X/h` (`div_pos`) and the first. This file states the three facts once.

The 30 call sites that took them inline are in `A3Middle` (4), `ThmA2Linear` (18) and
`ThmA2Rows` (8); there they are used as `h2a`, `h2b` and `h2T0`. The lemma is over the reals and
imports nothing beyond Mathlib.

## Main results
* `windowEnds_facts` — the two endpoints and the positivity of `2·T`.
-/

namespace Salt.MR

/-- **The window's two endpoints at `Tann = 2T`.** From `0 < X`, `0 < h`, `X/h ≤ T` and
`2·T ≤ X`: `2·(X/h) ≤ 2·T`, `2·T ≤ X` and `0 < 2·T`. -/
theorem windowEnds_facts {X h T : ℝ} (hX0 : 0 < X) (hh : 0 < h) (hT : X / h ≤ T)
    (hTX : 2 * T ≤ X) :
    2 * (X / h) ≤ 2 * T ∧ (2 : ℝ) * T ≤ X ∧ (0 : ℝ) < 2 * T := by
  have hXh : (0 : ℝ) < X / h := div_pos hX0 hh
  exact ⟨by linarith, hTX, by linarith⟩

end Salt.MR
