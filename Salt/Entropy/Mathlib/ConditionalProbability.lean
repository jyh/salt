/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/Probability/ConditionalProbability.lean`,
at commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.Probability.ConditionalProbability`, `public section`) to a plain
  `import Mathlib`.
- `cond_real_apply` and `cond_isProbabilityMeasure_of_real` are genuinely absent
  from mathlib v4.32.0-rc1 (which provides `cond_apply` /
  `cond_isProbabilityMeasure_of_finite`), so their statements and proofs are
  ported verbatim.
-/
import Mathlib

open MeasureTheory

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
lemma cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
theorem cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  apply cond_isProbabilityMeasure_of_finite
  · intro h
    simp [measureReal_def, h] at hcs
  · intro h
    simp [measureReal_def, h] at hcs

end ProbabilityTheory
