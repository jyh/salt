/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.Regime

/-!
# Every admissible `H` sits below `x`

On a `ChowlaRegime`, every `H ≤ H₊` satisfies `H + 1 ≤ x`: the headroom field gives
`H ≤ H₊ ≤ x / ω`, and `ω ≥ 2` gives `x / ω ≤ x / 2`, which is below `x` because `x ≥ 2`.

The door and stride assemblies under `Salt/MR` derived this inline as a five-line `have hHx`;
`R.add_one_le_x` states it once.

## Main result
* `ChowlaRegime.add_one_le_x` — `∀ H, H ≤ R.Hhi → H + 1 ≤ R.x`.
-/

namespace Salt.Entropy.Chowla

/-- **Every admissible `H` is below `x`.** For `H ≤ H₊`: `H ≤ x / ω ≤ x / 2` (headroom, then
`ω ≥ 2`), and `x / 2 + 1 ≤ x` since `x ≥ 2`. -/
theorem ChowlaRegime.add_one_le_x (R : ChowlaRegime) : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
  intro H hhi
  have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
  have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
  have h2 : 2 ≤ R.x := R.hx
  omega

end Salt.Entropy.Chowla
