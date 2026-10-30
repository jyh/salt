/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.TowerFlatBuilder

/-!
# Below the design-law base (`FlatDesignBound`)

The flat door assemblies bound their count floor `Hopq` by the design-law base
`flatDesignBase A = ⌈exp (exp (3.2 · A))⌉₊` from `hopqA : (Hopq : ℝ) ≤ A`, in the same five lines
at every site (`Real.add_one_le_exp` twice, `linarith`, `Nat.le_ceil`). This module states that
once.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- A natural number at most `A` (as a real) is at most `flatDesignBase A`:
`N ≤ A ≤ 3.2 · A + 1 ≤ exp (3.2 · A) < exp (exp (3.2 · A)) ≤ flatDesignBase A`. The bound `0 ≤ A`
the middle step needs comes from `h` itself, since `0 ≤ (N : ℝ)`. -/
theorem le_flatDesignBase_of_le {N : ℕ} {A : ℝ} (h : (N : ℝ) ≤ A) : N ≤ flatDesignBase A := by
  have hA : (0 : ℝ) ≤ A := le_trans (Nat.cast_nonneg _) h
  have h1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
  have hR : (N : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
  have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
  rw [flatDesignBase]
  exact_mod_cast hceil

end Salt.MR
