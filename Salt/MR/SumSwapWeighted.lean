/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The weighted triple-sum swap (O13-e candidate #43, TACTICS-CATALOGUE #13)

Role: one lemma for a reordering the dyadic row bounds perform at 17 sites. A sum over
`n` of `c` times a `j`-weighted sum of inner `t`-sums equals `c` times the same
`j`-weighted sum with the `n`-sum moved inside the `t`-sum. The weight `w j` rides
the `j` index only, so it factors out of the `n`-sum. Each site was a 7-line `rw`
chain (`Finset.mul_sum`, `Finset.sum_comm`, `Finset.sum_mul` and two `congr 1`).
-/

namespace Salt.MR

open scoped BigOperators

/-- Moving an outer `n`-sum inside a `j`-weighted sum of `t`-sums, past a constant factor:
`∑ n ∈ S, c * ∑ j ∈ J, (∑ t ∈ T j, X j t n) * w j
  = c * ∑ j ∈ J, (∑ t ∈ T j, ∑ n ∈ S, X j t n) * w j`. -/
theorem sum_mul_weighted_sum_comm {ι κ τ : Type*} (S : Finset ι) (J : Finset κ)
    (T : κ → Finset τ) (c : ℝ) (X : κ → τ → ι → ℝ) (w : κ → ℝ) :
    ∑ n ∈ S, c * ∑ j ∈ J, (∑ t ∈ T j, X j t n) * w j
      = c * ∑ j ∈ J, (∑ t ∈ T j, ∑ n ∈ S, X j t n) * w j := by
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

end Salt.MR
