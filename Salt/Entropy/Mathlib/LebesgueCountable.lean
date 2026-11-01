/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file
`PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`, at commit
a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.MeasureTheory.Integral.Lebesgue.Countable`, `public section`) to a
  plain `import Mathlib`.
- All four lemmas are genuinely absent from mathlib v4.32.0-rc1; statements and
  proofs are ported verbatim.  This residue is in the W1-3 lane's closure:
  upstream `PFR/Mathlib/Probability/Kernel/Disintegration.lean` imports it.
-/
import Mathlib

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]

-- TODO: Change RHS of `lintegral_fintype`
/-- `∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x` on a `Fintype` with measurable singletons: mathlib's
`lintegral_fintype` with the two factors commuted (mathlib writes `f x * μ {x}`). No consumer at
884bd7d7. -/
lemma lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) [Fintype α] :
    ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by
  simp_rw [lintegral_fintype, mul_comm]

/-- `∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x` on a `Countable` type with measurable singletons:
mathlib's `lintegral_countable'` with the two factors commuted. The disintegration lane's
workhorse: read by `disintegration`, `condKernel_compProd_ae_eq`, `condKernel_map_prodMk_left`,
`map_compProd_condDistrib` and `condDistrib_eq_prod_of_indepFun` (all
`Mathlib/KernelDisintegration`). -/
lemma lintegral_eq_tsum (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]

-- TODO: Change RHS of `lintegral_finset`
/-- `∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x` over a finset `s`: mathlib's `lintegral_finset`
with the two factors commuted. Read by `entropy_compProd_aux` (`Kernel/Basic`), twice, and by
`FiniteKernelSupport.compProd` (`Mathlib/KernelDisintegration`), each time after
`lintegral_eq_setLIntegral`. -/
lemma setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]

/-- `∫⁻ x, f x ∂μ = f a * μ {a}` when `f` vanishes off the point `a`: split at `{a}`
(`lintegral_add_compl`), `lintegral_singleton` on the atom, `setLIntegral_congr_fun` to the zero
function on its complement. Read by `condKernel_compProd_apply'`
(`Mathlib/KernelDisintegration`), twice. -/
lemma lintegral_eq_single (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a, f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [← lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton,
    setLIntegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a)),
    lintegral_zero, add_zero]
  simp +contextual [Set.EqOn, ha]

end MeasureTheory
