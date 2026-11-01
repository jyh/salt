/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Measure/Real.lean`, at
commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import`s of
  `Mathlib.MeasureTheory.Measure.Real` and
  `PFR.Mathlib.MeasureTheory.Measure.Prod`, `public section`) to a plain
  `import Mathlib`.
- `Measure.prod_real_singleton` upstream used `Measure.prod_apply_singleton`
  from the (unported) PFR patch residue `PFR.Mathlib.MeasureTheory.Measure.Prod`.
  That lemma is absent from mathlib v4.32.0-rc1, so its one-line proof
  (`← Prod.eta`, `← Set.singleton_prod_singleton`, `Measure.prod_prod`) is
  inlined here as a local `have` rather than introducing a new shared residue.
- `measureReal_preimage_fst_singleton_eq_sum` /
  `measureReal_preimage_snd_singleton_eq_sum` rely on
  `measure_preimage_fst/snd_singleton_eq_sum`, which DO exist in mathlib
  v4.32.0-rc1 (`Mathlib.MeasureTheory.Measure.NullMeasurable`); ported verbatim.
- All other declarations, names, and proof bodies are verbatim from upstream.
-/
import Mathlib

open Function Set
open scoped ENNReal NNReal

namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

/-- `(c • μ).real s = c.toReal • μ.real s` for `c : ℝ≥0∞`: real mass is linear in an `ℝ≥0∞`
scalar (`simp`, `ENNReal.toReal_mul` under `Measure.real`). The normalisation step of `Hm[μ]`:
read by `measureEntropy_map_of_injective`, `measureEntropy_comap` and `measureMutualInfo_swap`
(`Measure`). -/
lemma Measure.ennreal_smul_real_apply (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

/-- `(c • μ).real s = c • μ.real s` for `c : ℝ≥0`: an `ℝ≥0` scalar passes through real mass
(`NNReal.smul_def` under `Measure.real`). No consumer at 884bd7d7. -/
lemma Measure.nnreal_smul_real_apply (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by simp [Measure.real, NNReal.smul_def]

/-- `(comap f μ).real s = μ.real (f '' s)` for an injective `f` with measurable images and a
measurable `s`: `Measure.comap_apply` at real masses. Read by `entropy_comap` (`Kernel/Basic`)
and by `measureEntropy_comap` (`Measure`), each at a singleton. -/
lemma Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (comap f μ).real s = μ.real (f '' s) := by simp [Measure.real, comap_apply _ hfi hf μ hs]

/-- `(μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2}` for `ν` σ-finite: the `ℝ≥0∞` identity
(`Prod.eta`, `Set.singleton_prod_singleton`, `Measure.prod_prod` — inlined as a local `have`;
the header says why) read through `Measure.real`. Registered in `Salt/Entropy/All`'s axiom
audit; no other consumer at 884bd7d7. -/
lemma Measure.prod_real_singleton (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  have h : (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
    rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [Measure.real, h]

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

/-- `μ.real (Prod.fst ⁻¹' {x}) = ∑ y, μ.real {(x, y)}` for a finite measure on `Ω × Ω'` with
`Ω'` a `Fintype`: mathlib's `measure_preimage_fst_singleton_eq_sum` with `ENNReal.toReal_sum`
over finite terms. No consumer at 884bd7d7. -/
lemma measureReal_preimage_fst_singleton_eq_sum [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

/-- `μ.real (Prod.snd ⁻¹' {y}) = ∑ x, μ.real {(x, y)}` for a finite measure on `Ω × Ω'` with `Ω`
a `Fintype`: mathlib's `measure_preimage_snd_singleton_eq_sum` with `ENNReal.toReal_sum` over
finite terms. No consumer at 884bd7d7. -/
lemma measureReal_preimage_snd_singleton_eq_sum [Fintype Ω] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (y : Ω') :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : Ω, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  intros
  finiteness

end MeasureTheory
