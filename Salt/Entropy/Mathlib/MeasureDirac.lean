/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Measure/Dirac.lean`, at
commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.MeasureTheory.Measure.Dirac`, `public section`) to a plain
  `import Mathlib`.
- The lemma `dirac_real_apply'` is genuinely absent from mathlib v4.32.0-rc1,
  so its statement and proof are ported verbatim.
-/
import Mathlib

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]

end MeasureTheory.Measure
