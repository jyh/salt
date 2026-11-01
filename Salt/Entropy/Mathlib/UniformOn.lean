/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/Probability/UniformOn.lean`, at commit
a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import`s of
  `Mathlib.Probability.UniformOn` and `PFR.Mathlib.Data.Set.Card`,
  `public section`) to a plain `import Mathlib`.
- `uniformOn_real_singleton` upstream used `Set.ncard_inter_singleton` from the
  (unported) PFR patch residue `PFR.Mathlib.Data.Set.Card`. That lemma is absent
  from mathlib v4.32.0-rc1, so its one-line fact
  (`(s ∩ {ω}).ncard = if ω ∈ s then 1 else 0`) is inlined here as a local
  `have` rather than introducing a new shared residue.
- All other declarations, names, and proof bodies are verbatim from upstream.
-/
import Mathlib

open Function MeasureTheory Measure

namespace ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}

/-- `uniformOn s {x} = 1 / Nat.card s` for `x ∈ s` and `s` finite: unfold `uniformOn` and `cond`
— the count of `{x} ∩ s = {x}` is `1` and the count of `s` is `Nat.card s`
(`count_apply_finite`, `Nat.card_eq_card_finite_toFinset`). Read by
`real_uniformOn_apply_singleton_of_mem` below. -/
lemma uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    uniformOn s {x} = 1 / Nat.card s := by
  have : {x} ∩ s = {x} := by ext y; simp +contextual [hx]
  simp only [uniformOn, cond, Measure.smul_apply, MeasurableSet.singleton, Measure.restrict_apply,
    this, Measure.count_singleton', smul_eq_mul, mul_one, one_div, inv_inj]
  rw [Measure.count_apply_finite _ hs, Nat.card_eq_card_finite_toFinset hs]

/-- `(uniformOn s).real {x} = 1 / Nat.card s` for `x ∈ s` and `s` finite:
`uniformOn_apply_singleton_of_mem` at real mass (`measureReal_def`). No consumer at 884bd7d7. -/
lemma real_uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    (uniformOn s).real {x} = 1 / Nat.card s := by
  simp [measureReal_def, uniformOn_apply_singleton_of_mem hx hs]

/-- `uniformOn s {x} = 0` for `x ∉ s`: the conditioned count of a point outside `s` vanishes
(`simp` through `uniformOn` and `cond`). Read by `real_uniformOn_apply_singleton_of_not_mem`
below. -/
lemma uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) : uniformOn s {x} = 0 := by
  simp [uniformOn, cond, hx]

/-- `(uniformOn s).real {x} = 0` for `x ∉ s`: `uniformOn_apply_singleton_of_not_mem` at real
mass. No consumer at 884bd7d7. -/
lemma real_uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) :
    (uniformOn s).real {x} = 0 := by
  simp [measureReal_def, uniformOn_apply_singleton_of_not_mem hx]

/-- `uniformOn s t = 0` when `s ∩ t = ∅`: for a finite `s` by `uniformOn_eq_zero_iff`; for an
infinite `s` because `count s = ∞` makes `uniformOn s` the zero measure
(`Measure.count_apply_infinite`). No consumer at 884bd7d7. -/
theorem uniformOn_apply_eq_zero (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  rcases Set.finite_or_infinite s with hs | hs
  · exact (uniformOn_eq_zero_iff hs).mpr hst
  · simp [uniformOn, cond, Measure.count_apply_infinite hs]

/-- `uniformOn s = 0` for an infinite `s`: the uniform measure on an infinite set is the zero
measure (`simp` with `hs`). Read by `map_uniformOn_apply` below. -/
lemma uniformOn_of_infinite (hs : s.Infinite) : uniformOn s = 0 := by simp [hs]

/-- `uniformOn s t = Nat.card ↑(s ∩ t) / Nat.card s` for a finite `s`: `cond_apply` on the
measurable `s`, both counts finite (`count_apply_finite`) and read as `Nat.card`s
(`Nat.card_eq_card_finite_toFinset`), then `ENNReal.div_eq_inv_mul`. The closed form the rest of
the file reduces to: read by `uniformOn_real` and `map_uniformOn_apply` here. -/
lemma uniformOn_apply (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  rw [uniformOn, cond_apply hs.measurableSet, count_apply_finite _ hs,
    count_apply_finite _ (hs.inter_of_left _), ← Nat.card_eq_card_finite_toFinset,
    ← Nat.card_eq_card_finite_toFinset, ENNReal.div_eq_inv_mul]

/-- `(uniformOn s).real t = Nat.card ↑(s ∩ t) / Nat.card s` for a finite `s`: `uniformOn_apply`
at real mass. Read by `uniformOn_real_singleton` below, by `entropy_of_uniformOn` (`Measure`,
the entropy of the uniform measure) and by `uniformOn_univ_real_coe` (`Chowla/Transport`). -/
lemma uniformOn_real (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  simp [measureReal_def, uniformOn_apply hs]

/-- `(uniformOn s).real {ω} = if ω ∈ s then (s.ncard : ℝ)⁻¹ else 0` for a finite `s`:
`uniformOn_real` at a singleton, with `(s ∩ {ω}).ncard` being `1` or `0` by cases (the fact PFR
took from its `Set.Card` residue, inlined here — the header says why). Registered in
`Salt/Entropy/All`'s axiom audit; no other consumer at 884bd7d7. -/
lemma uniformOn_real_singleton (hs : s.Finite) (ω : Ω) [Decidable (ω ∈ s)] :
    (uniformOn s).real {ω} = if ω ∈ s then (s.ncard : ℝ)⁻¹ else 0 := by
  have hns : (s ∩ {ω}).ncard = if ω ∈ s then 1 else 0 := by split_ifs <;> simp [*]
  simp [uniformOn_real hs, hns]; split <;> simp

instance uniformOn.instIsProbabilityMeasure [Nonempty s] [Finite s] :
    IsProbabilityMeasure (uniformOn s) := isProbabilityMeasure_uniformOn ‹_› .of_subtype

/-- `(uniformOn s).map f t = uniformOn (f '' s) t` for `f` measurable and injective and `t`
measurable: for an infinite `s` both sides vanish (`uniformOn_of_infinite`, the image being
infinite too); for a finite `s`, `map_apply` and `uniformOn_apply` on each side, with
`Nat.card_image_of_injective` and `Set.image_inter_preimage` matching the two counts. Read by
`map_uniformOn` below. -/
lemma map_uniformOn_apply {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) {t : Set Ω'}
    (ht : MeasurableSet t) :
    (uniformOn s).map f t = uniformOn (f '' s) t := by
  obtain hs | hs := s.infinite_or_finite
  · simp [uniformOn_of_infinite, hs, hs.image hf.injOn]
  · rw [map_apply hmes ht, uniformOn_apply hs, uniformOn_apply (hs.image _),
      Nat.card_image_of_injective hf, ← Nat.card_image_of_injective hf, Set.image_inter_preimage]

/-- `(uniformOn s).map f = uniformOn (f '' s)` for `f` measurable and injective:
`map_uniformOn_apply` at every measurable set (`Measure.ext`). No consumer at 884bd7d7. -/
lemma map_uniformOn {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) :
    (uniformOn s).map f = uniformOn (f '' s) := by
  ext t ht
  exact map_uniformOn_apply hmes hf ht

end ProbabilityTheory
