/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The flat design constant's six floors, from its `max` definition

The flat-design assemblies choose their design constant as
`A = max (max (max A₀ 162) Awin) (max b (max (4·x₀) H))` and then read off, each time by hand,
that `A` lies above each of the six arguments it was chosen above, and that the `x₀` window
`x₀ ≤ exp (exp (3.2·A) / 10)` holds. This file states those facts once.

The five call sites that took them inline are `S16Uniform`, `S16Compose`, `S16ComposeV4`,
`XThread` and `S16ComposeLH`; at each one `b = budgetAFlat ε β`, `x₀` and `H = Hopq` are casts
of naturals, and the facts are used as `hA162`, `hA₀A`, `hAwinA`, `hAge`, `hopqA` and `hx0win`.
The lemmas here are over reals and import nothing beyond Mathlib.

## Main results
* `x0_le_exp_exp_of_four_le` — `0 ≤ x` and `4·x ≤ A` give `x ≤ exp (exp (3.2·A) / 10)`.
* `flatDesignMax_facts` — the six floors of the `max` design constant.
-/

namespace Salt.MR

/-- **The `x₀` window from `4·x₀ ≤ A`.** For `0 ≤ x` and `4·x ≤ A`,
`x ≤ exp (exp (3.2·A) / 10)`: two uses of `t + 1 ≤ exp t`, then `linarith`. -/
theorem x0_le_exp_exp_of_four_le {x A : ℝ} (hx : 0 ≤ x) (h4 : 4 * x ≤ A) :
    x ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Real.add_one_le_exp _
  linarith

/-- **The flat design constant's floors.** For
`A = max (max (max A₀ 162) Awin) (max b (max (4·x) H))` with `0 ≤ x`: `162 ≤ A`, `A₀ ≤ A`,
`Awin ≤ A`, `b ≤ A`, `H ≤ A`, and the `x` window `x ≤ exp (exp (3.2·A) / 10)`
(`x0_le_exp_exp_of_four_le`). -/
theorem flatDesignMax_facts {A A₀ Awin b x H : ℝ}
    (hAdef : A = max (max (max A₀ 162) Awin) (max b (max (4 * x) H))) (hx : 0 ≤ x) :
    (162 : ℝ) ≤ A ∧ A₀ ≤ A ∧ Awin ≤ A ∧ b ≤ A ∧ H ≤ A ∧
      x ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
  have h4 : 4 * x ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, x0_le_exp_exp_of_four_le hx h4⟩ <;> rw [hAdef]
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

end Salt.MR
