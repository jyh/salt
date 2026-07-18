/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.BoxAvg

/-!
# VMVT-VK rung R4 — the pointwise stone (`VK-POINTWISE`), orbit algebra

R4 (`vk_block_core`) is the load-bearing stone: the block sum's `2b`-moment,
Jensen-averaged over `y = 1..Y` shifts, produces the shifted-coefficient **orbit**
`β_j(y) = ∑_{i ≥ j} C(i,j)·vkCoef_i·y^{i−j}`, whose `j*`-steps are disjoint boxes,
so R3 + `vmvt` (`Salt.Vmvt.Summit2.vmvt`) close the bound.

This file lands the **orbit-coefficient identity** — the binomial regrouping that
turns the shifted polynomial phase `∑_j c_j (m+y)^j` into `∑_i β_i(y) m^i`.  The
assembly through the R3 measure fold + `vmvt` is the residual `VMVT-VK/R4-assembly`
(`docs/blueprints/flags.md`).
-/

namespace Salt.Vk

open Finset
open scoped BigOperators

/-- The R4 **orbit coefficient** `β_i(y) = ∑_{j ≥ i} C(j,i)·c_j·y^{j−i}`. -/
noncomputable def vkOrbit (K : ℕ) (c : ℕ → ℝ) (y : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc i K, (Nat.choose j i : ℝ) * c j * y ^ (j - i)

/-- **R4 orbit identity.**  Shifting the block variable `m ↦ m + y` in the degree-`K`
polynomial phase regroups into the orbit coefficients:
`∑_j c_j (m+y)^j = ∑_i β_i(y) m^i`. -/
theorem poly_shift_orbit (K : ℕ) (c : ℕ → ℝ) (m y : ℝ) :
    ∑ j ∈ Finset.range (K + 1), c j * (m + y) ^ j
      = ∑ i ∈ Finset.range (K + 1), vkOrbit K c y i * m ^ i := by
  have step1 : ∑ j ∈ Finset.range (K + 1), c j * (m + y) ^ j
      = ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (j + 1),
          ((Nat.choose j i : ℝ) * c j * y ^ (j - i)) * m ^ i := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hswap : ∀ j i : ℕ, (j ∈ Finset.range (K + 1) ∧ i ∈ Finset.range (j + 1))
      ↔ (j ∈ Finset.Icc i K ∧ i ∈ Finset.range (K + 1)) := by
    intro j i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  rw [step1, Finset.sum_comm' hswap]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [vkOrbit, Finset.sum_mul]

end Salt.Vk
