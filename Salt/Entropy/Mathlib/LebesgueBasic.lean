/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`,
at commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.MeasureTheory.Integral.Lebesgue.Basic`, `public section`) to a plain
  `import Mathlib`.
- Both lemmas are genuinely absent from mathlib v4.32.0-rc1; statements and
  proofs are ported verbatim.  This residue is in the W1-3 lane's closure:
  upstream `PFR/Mathlib/Probability/Kernel/Disintegration.lean` imports it.
-/
import Mathlib

/-!
# TODO

Rename `setLIntegral_congr` to `setLIntegral_congr_set`
-/

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- `∫⁻ x, f x ∂μ = 0` when `f` vanishes on a measurable `s` whose complement is null: split the
integral at `s` (`lintegral_add_compl`); the `sᶜ` part is `setLIntegral_measure_zero`, the `s`
part is `setLIntegral_congr_fun` to the zero function. Read by `FiniteKernelSupport.prod`
(`Mathlib/KernelDisintegration`). -/
lemma lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero sᶜ f hs,
    setLIntegral_congr_fun (f := f) (g := fun _ ↦ 0) hmes hf]
  simp

/-- `∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ` when `μ sᶜ = 0`: the whole integral is the integral over
a full-measure set — `setLIntegral_univ` and `setLIntegral_congr` at `s =ᵐ[μ] univ`
(`ae_eq_univ`). Read by `entropy_compProd_aux` (`Kernel/Basic`), twice, and by
`FiniteKernelSupport.compProd` (`Mathlib/KernelDisintegration`), each time beside
`setLIntegral_eq_sum`. -/
lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

end MeasureTheory
