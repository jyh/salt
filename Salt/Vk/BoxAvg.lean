/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Shift
import Salt.Vmvt.Fourier

/-!
# VMVT-VK rung R3 — box averaging (`VK-BOX-AVG`), pointwise core

The measure stone folds `Y` disjoint coordinate boxes into `torusMeasure` and
compares the pointwise `2b`-moment of `genFun` at the box centers with the mean
value `Jk` (via `integral_norm_pow_eq_Jk`, RIGHT-to-LEFT).

This file lands the **pointwise variation core** — the input to that folding:
moving the torus point `α` by a coordinate box of half-widths `δ` changes
`‖genFun k (Ioc 0 P) α‖` by at most the `Slack = 2π·P·∑_j δ_j P^j` (through R2's
`2π`-Lipschitz character bound and `genFun`'s `eR_sum` polynomial phase).

The disjoint-box → `Jk` measure assembly is the recorded residual `VMVT-VK/R3-measure`
(see `docs/blueprints/flags.md`).
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-- `genFun` has a single `eR` phase per term: `∏_j eR(α_j n^j) = eR(∑_j α_j n^j)`. -/
lemma genFun_eq_eR_sum (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) :
    genFun k A α = ∑ n ∈ A, eR (∑ j : Deg k, α j * (n : ℝ) ^ (j : ℕ)) := by
  rw [genFun]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  exact (eR_sum Finset.univ (fun j => α j * (n : ℝ) ^ (j : ℕ))).symm

/-- **R3 pointwise stone (Lipschitz form).**  Two torus points `α, β` give
`genFun`'s differing by `≤ 2π·∑_n |∑_j (α_j−β_j) n^j|`. -/
lemma genFun_lipschitz (k : ℕ) (A : Finset ℤ) (α β : Deg k → ℝ) :
    ‖genFun k A α - genFun k A β‖
      ≤ 2 * π * ∑ n ∈ A, |∑ j : Deg k, (α j - β j) * (n : ℝ) ^ (j : ℕ)| := by
  rw [genFun_eq_eR_sum, genFun_eq_eR_sum]
  refine (norm_sum_eR_sub_le A (fun n => ∑ j : Deg k, α j * (n : ℝ) ^ (j : ℕ))
    (fun n => ∑ j : Deg k, β j * (n : ℝ) ^ (j : ℕ))).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **R3 pointwise stone (box form / the Slack).**  If `α` and `β` differ by at
most the box half-widths `δ` in each coordinate, then over the block `Ioc 0 P`,
`‖genFun α − genFun β‖ ≤ 2π·P·∑_j δ_j P^j`. -/
theorem genFun_box_variation (k P : ℕ) (α β δ : Deg k → ℝ)
    (hδ : ∀ j, |α j - β j| ≤ δ j) (hδ0 : ∀ j, 0 ≤ δ j) :
    ‖genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) α - genFun k (Finset.Ioc (0 : ℤ) (P : ℤ)) β‖
      ≤ 2 * π * ((P : ℝ) * ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ)) := by
  refine (genFun_lipschitz k (Finset.Ioc (0 : ℤ) (P : ℤ)) α β).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hbound : ∀ n ∈ Finset.Ioc (0 : ℤ) (P : ℤ),
      |∑ j : Deg k, (α j - β j) * (n : ℝ) ^ (j : ℕ)| ≤ ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnP : (n : ℝ) ≤ (P : ℝ) := by exact_mod_cast hn.2
    calc |∑ j : Deg k, (α j - β j) * (n : ℝ) ^ (j : ℕ)|
        ≤ ∑ j : Deg k, |(α j - β j) * (n : ℝ) ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (j : ℕ))]
          exact mul_le_mul (hδ j) (pow_le_pow_left₀ (by linarith) hnP _)
            (by positivity) (hδ0 j)
  calc ∑ n ∈ Finset.Ioc (0 : ℤ) (P : ℤ), |∑ j : Deg k, (α j - β j) * (n : ℝ) ^ (j : ℕ)|
      ≤ ∑ _n ∈ Finset.Ioc (0 : ℤ) (P : ℤ), ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ) :=
        Finset.sum_le_sum hbound
    _ = (P : ℝ) * ∑ j : Deg k, δ j * (P : ℝ) ^ (j : ℕ) := by
        have hcard : (Finset.Ioc (0 : ℤ) (P : ℤ)).card = P := by rw [Int.card_Ioc]; omega
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

end Salt.Vk
