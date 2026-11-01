/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/ForMathlib/Entropy/Measure.lean`, at commit
a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, the `public import`s of
  `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`,
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`, and the four PFR patch
  residues, and `@[expose] public section`) to a plain `import Mathlib` plus
  imports of the ported Salt.Entropy residues. Upstream reached
  `PFR.Mathlib.MeasureTheory.Measure.Prod` transitively through
  `...Measure.Real`; the ported `Salt.Entropy.Mathlib.MeasureReal` inlines its
  own needs and does not re-export it, so `Salt.Entropy.Mathlib.MeasureProd` is
  imported explicitly here (for `Measure.prod_of_full_measure_finset` and the
  `IsZeroOrProbabilityMeasure` product instance).
- The `positivity` extension `evalMeasureMutualInfo` was declared `meta def`
  (module-system syntax); converted to plain `def`.
- NAME-COLLISION DRIFT: mathlib v4.32.0-rc1 provides
  `MeasureTheory.Measure.support` (the topological support, a `Set X` requiring
  `[TopologicalSpace X]`); PFR's pinned mathlib does not, and PFR defines
  `_root_.MeasureTheory.Measure.support` as the finite-support `Finset S`. The
  full names collide and dot-notation forces the full name, so PFR's object is
  renamed here to `MeasureTheory.Measure.finSupport` (and every `μ.support` use
  to `μ.finSupport`). The lemmas `measure_compl_support`, `ae_mem_support`, and
  `mem_support` keep their names (the statements now read `μ.finSupport`).
  Downstream ports (Basic.lean etc.) must use `finSupport`.
- All other declarations, names, notation, namespaces, and proof bodies are
  verbatim from upstream.
- Docstrings added by Salt (2026-11-01, the O83 documentation lane) to the 34 upstream
  declarations that carried none; names, statements and bodies are unchanged.
-/
import Mathlib
import Salt.Entropy.FiniteRange
import Salt.Entropy.Mathlib.MeasureDirac
import Salt.Entropy.Mathlib.MeasureReal
import Salt.Entropy.Mathlib.UniformOn
import Salt.Entropy.Mathlib.MeasureProd

/-!
# Entropy of a measure

## Main definitions

* `measureEntropy`: entropy of a measure `μ`, denoted by `Hm[μ]`
* `measureMutualInfo`: mutual information of a measure over a product space, denoted by `Im[μ]`,
  equal to `Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]`

## Notations

* `Hm[μ] = measureEntropy μ`
* `Im[μ] = measureMutualInfo μ`

-/

open MeasureTheory Real Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U] --[MeasurableSingletonClass U]

section measureEntropy
variable {μ : Measure S}

/-- Entropy of a measure on a measurable space.

We normalize the measure by `(μ Set.univ)⁻¹` to extend the entropy definition to finite measures.
What we really want to do is deal with `μ=0` or `IsProbabilityMeasure μ`, but we don't have
a typeclass for that (we could create one though).
The added complexity ∈ the expression is not an issue because if `μ` is a probability measure,
a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

/-- A measure has finite support if there exists a finite set whose complement has zero measure. -/
class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, ∀ᵐ x ∂μ, x ∈ A

/-- A set on which a measure with finite support is supported. -/
noncomputable
def _root_.MeasureTheory.Measure.finSupport (μ : Measure S) [hμ : FiniteSupport μ] : Finset S :=
  hμ.finite.choose.filter (μ {·} ≠ 0)

/-- `μ μ.finSupportᶜ = 0`: the chosen finite carrier, filtered to its atoms of positive mass,
still carries `μ` — the complement of the chosen set is null and the dropped atoms are null. The
floor of the `FiniteSupport` API: `ae_mem_support`, `mem_support`,
`integrable_of_finiteSupport`, `integral_congr_finiteSupport`,
`Measure.ext_iff_singleton_finiteSupport` and `measureEntropy_prod` here;
`finiteKernelSupport_of_const`, `finiteSupport_of_compProd'` and `FiniteSupport.comap_equiv` in
`Kernel/Basic`. -/
lemma measure_compl_support (μ : Measure S) [hμ : FiniteSupport μ] : μ μ.finSupportᶜ = 0 := by
  let A := hμ.finite.choose
  have : (μ.finSupport : Set S)ᶜ ⊆ (A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x} := by
    intro z hz
    simp only [Measure.finSupport, ne_eq, Finset.coe_filter, mem_compl_iff, mem_setOf_eq, not_and,
      Decidable.not_not] at hz
    by_cases h'z : z ∈ A
    · simp [hz h'z, h'z]
    · simp [h'z]
  apply le_antisymm ?_ bot_le
  calc μ (μ.finSupport : Set S)ᶜ ≤ μ ((A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x}) :=
    measure_mono this
  _ ≤ μ (Aᶜ) + ∑ x ∈ A.filter (μ {·} = 0), μ {x} := by
    apply (measure_union_le _ _).trans
    gcongr
    apply measure_biUnion_finset_le
  _ ≤ 0 + ∑ x ∈ A.filter (μ {·} = 0), 0 := by
    gcongr with x hx
    · exact hμ.finite.choose_spec.le
    · simp only [Finset.mem_filter] at hx
      exact hx.2.le
  _ = 0 := by simp

/-- `∀ᵐ x ∂μ, x ∈ μ.finSupport`: `measure_compl_support` read as an a.e. statement. Read by
`finiteSupport_of_mul` and `finiteSupport_of_comp` here, by `finiteSupport_of_compProd'` and
`entropy_compProd_aux` (`Kernel/Basic`) and by `mutualInfo_nonneg'` (`Kernel/MutualInfo`). -/
lemma ae_mem_support (μ : Measure S) [FiniteSupport μ] : ∀ᵐ x ∂μ, x ∈ μ.finSupport :=
  measure_compl_support _

/-- `x ∈ μ.finSupport ↔ μ {x} ≠ 0`: the carrier is exactly the atoms of positive mass — the
filter in `finSupport`'s definition forwards, `measure_compl_support` backwards. A `simp` lemma;
read by `integral_congr_finiteSupport` and `measureMutualInfo_nonneg_aux`. -/
@[simp] lemma mem_support {μ : Measure S} [hμ : FiniteSupport μ] {x : S} :
    x ∈ μ.finSupport ↔ μ {x} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Measure.finSupport, ne_eq, Finset.mem_filter] at h
    exact h.2
  · contrapose! h
    exact measure_mono_null (by simpa using h) (measure_compl_support μ)

instance finiteSupport_zero : FiniteSupport (0 : Measure S) where
  finite := ⟨(∅ : Finset S), by simp⟩

/-- TODO: replace FiniteSupport hypotheses ∈ these files with FiniteEntropy hypotheses. -/
noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0

instance finiteSupport_of_fintype {μ : Measure S} [Finite S] : FiniteSupport μ := by
  cases nonempty_fintype S
  use Finset.univ
  simp

instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := ⟨μ.finSupport, Measure.ae_smul_measure (ae_mem_support _) _⟩

section

variable [MeasurableSingletonClass S]

/-- The image of a finitely supported measure under a measurable map is finitely supported, on
the image of the carrier (`ae_map_iff`, `ae_mem_support`). Read by `finiteSupport_logMeasureAff`
(`Chowla/StrideDecrement`). -/
lemma finiteSupport_of_comp
    {μ : Measure Ω} [FiniteSupport μ] {X : Ω → S} (hX : Measurable X) :
    FiniteSupport (μ.map X) := by
  classical
  use Finset.image X μ.finSupport
  rw [ae_map_iff hX.aemeasurable (by exact (Finset.finite_toSet _).measurableSet)]
  filter_upwards [ae_mem_support _] using fun _ ↦ Finset.mem_image_of_mem _

instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := ⟨{x}, by simp⟩

/-- duplicate of `FiniteRange.null_of_compl` -/
lemma full_measure_of_finiteRange {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) [hX' : FiniteRange X] :
    (μ.map X) hX'.toFinsetᶜ = 0 := by
  rw [Measure.map_apply hX (MeasurableSet.compl (Finset.measurableSet _))]
  convert measure_empty (μ := μ)
  ext x
  simp [FiniteRange.toFinset]

/-- `∀ᵐ x ∂μ.map X, x ∈ hX'.toFinset` for a variable of finite range:
`full_measure_of_finiteRange` as an a.e. statement. No consumer at 884bd7d7
(`finiteSupport_of_finiteRange` goes through `FiniteRange.null_of_compl`). -/
lemma ae_mem_of_finiteRange {μ : Measure Ω} {X : Ω → S} (hX : Measurable X) [hX' : FiniteRange X] :
    ∀ᵐ x ∂μ.map X, x ∈ hX'.toFinset := full_measure_of_finiteRange hX

instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := by
  use hX'.toFinset
  exact FiniteRange.null_of_compl μ X

instance finiteSupport_of_prod {μ : Measure S} [FiniteSupport μ] {ν : Measure T} [SigmaFinite ν]
    [FiniteSupport ν] :
    FiniteSupport (μ.prod ν) := by
  use μ.finSupport ×ˢ ν.finSupport
  exact Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support ν)

/-- The countability hypothesis can probably be dropped here. Proof is unwieldy and can probably
be golfed. -/
lemma integrable_of_finiteSupport (μ : Measure S) [FiniteSupport μ]
    {β : Type*} [NormedAddCommGroup β] [IsFiniteMeasure μ] [Countable S]
    {f : S → β} :
    Integrable f μ := by
  let A := μ.finSupport
  have hA : μ Aᶜ = 0 := measure_compl_support μ
  by_cases hA' : A = ∅
  · simp only [hA', Finset.coe_empty, compl_empty, Measure.measure_univ_eq_zero] at hA
    rw [hA]
    exact integrable_zero_measure
  have : ∃ s₀, s₀ ∈ A := by
    contrapose! hA'
    ext s
    simpa using hA' s
  rcases this with ⟨s₀, hs₀⟩
  let f' : A → β := fun a ↦ f a
  classical
  let g : S → A := fun s ↦ if h : s ∈ A then ⟨s, h⟩ else ⟨s₀, hs₀⟩
  have : (f' ∘ g) =ᵐ[μ] f := by
    apply Filter.eventuallyEq_of_mem (s := A) hA
    intro a ha
    simp at ha
    simp [f', g, ha]
  apply Integrable.congr _ this
  apply Integrable.comp_measurable .of_finite
  fun_prop

/-- Two integrands agreeing at every atom of positive mass have the same integral against a
finitely supported `μ`: `integral_congr_ae` on the carrier (`measure_compl_support`,
`mem_support`). Read by `condEntropy_eq_kernel_entropy` (`Salt/Entropy/Basic`). -/
lemma integral_congr_finiteSupport {μ : Measure Ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : Ω → G} [FiniteSupport μ]
    (hfg : ∀ x, μ {x} ≠ 0 → f x = g x) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  refine integral_congr_ae <| measure_mono_null ?_ <| measure_compl_support μ
  exact fun x hx hx' ↦ hx <| hfg _ <| mem_support.1 hx'

/-- This generalizes Measure.ext_iff_singleton ∈ MeasureReal -/
theorem Measure.ext_iff_singleton_finiteSupport
    {μ1 μ2 : Measure S} [FiniteSupport μ1] [FiniteSupport μ2] :
    μ1 = μ2 ↔ ∀ x, μ1 {x} = μ2 {x} := by
  classical
  constructor
  · rintro rfl
    simp
  · let A1 := μ1.finSupport
    have hA1 := measure_compl_support μ1
    let A2 := μ2.finSupport
    have hA2 := measure_compl_support μ2
    intro h
    ext s
    have h1 : μ1 s = μ1 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      refine measure_mono_null ?_ hA1
      intro x
      simp (config := { contextual := true }) [A1]
    have h2 : μ2 s = μ2 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      exact measure_mono_null (fun x ↦ by simp (config := { contextual := true }) [A2]) hA2
    rw [h1, h2]
    have hs : Set.Finite (s ∩ (A1 ∪ A2)) := Set.toFinite (s ∩ (↑A1 ∪ ↑A2))
    rw [← hs.coe_toFinset, ← sum_measure_singleton (μ := μ1), ← sum_measure_singleton (μ := μ2)]
    simp_rw [h]

/-- Two finite, finitely supported measures are equal iff their real masses agree on every
singleton: `Measure.ext_iff_singleton_finiteSupport` with `ENNReal.toReal_eq_toReal_iff` on
finite values. No consumer at 884bd7d7. -/
theorem Measure.ext_iff_measureReal_singleton_finiteSupport {μ1 μ2 : Measure S}
    [FiniteSupport μ1] [FiniteSupport μ2] [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton_finiteSupport]
  congr! with x
  have h1 : μ1 {x} ≠ ⊤ := by finiteness
  have h2 : μ2 {x} ≠ ⊤ := by finiteness
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [h1, h2]

end

/-- `Hm[μ] = ∑ s ∈ A, negMulLog (((μ univ)⁻¹ • μ).real {s})` for a finite `A` whose complement
is null: the `tsum` collapses onto `A` (`tsum_eq_sum`), every term outside being `negMulLog 0`.
Read by `measureEntropy_of_isProbabilityMeasure_finite` here and `entropy_compProd_aux`
(`Kernel/Basic`). -/
lemma measureEntropy_eq_sum {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0) :
   Hm[μ] = ∑ s ∈ A, negMulLog (((μ Set.univ)⁻¹ • μ).real {s}) := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ.real {s} = 0 by simp [this]
  rw [Measure.real, measure_mono_null (by simpa) hA]
  simp

/-- `Hm[0] = 0` (`simp [measureEntropy]`). A `simp` lemma; what `simp` reaches in the `μ = 0`
branches of `measureEntropy_univ_smul`, `measureEntropy_nonneg` and
`measureMutualInfo_nonneg_aux`. -/
@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

/-- `Hm[dirac x] = 0`: the normalised measure has one atom, of mass `1`, and `negMulLog 1 = 0`
(`tsum_eq_single`). A `simp` lemma; read by `entropy_deterministic` (`Kernel/Basic`) and by the
A-R1 consumer test (`Salt/Entropy/ConsumerTest`). -/
@[simp]
lemma measureEntropy_dirac [MeasurableSingletonClass S] (x : S) : Hm[Measure.dirac x] = 0 := by
  rw [measureEntropy]
  simp only [MeasurableSet.univ, Measure.dirac_apply', mem_univ, indicator_of_mem, Pi.one_apply,
    inv_one, one_smul]
  rw [tsum_eq_single x]
  · simp only [Measure.real, MeasurableSet.singleton, Measure.dirac_apply', mem_singleton_iff,
    indicator_of_mem, Pi.one_apply, ENNReal.toReal_one, negMulLog_one]
  · simp +contextual [eq_comm]

/-- `Hm[μ] = 0` when `μ` is not finite: `μ univ = ⊤`, so the normalisation `(μ univ)⁻¹ • μ` is
`0`. The infinite-mass branch of `measureEntropy_univ_smul`, `measureEntropy_nonneg`,
`measureEntropy_le_log_card_of_mem` and `measureMutualInfo_of_not_isFiniteMeasure`. -/
lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

/-- `Hm[μ] = ∑' s, negMulLog (μ.real {s})` for a zero-or-probability measure: the normalisation
is the identity (`μ univ = 1`), or `μ = 0`. Read by `entropy_eq_integral_sum` (`Kernel/Basic`);
`measureEntropy_of_isProbabilityMeasure'` is the same statement under a second name. -/
lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [measureEntropy]
  · simp [measureEntropy]

/-- `measureEntropy_of_isProbabilityMeasure` under a second name, kept from upstream (the
statement is the same). No consumer at 884bd7d7. -/
lemma measureEntropy_of_isProbabilityMeasure' (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure μ

/-- `Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s})` for a zero-or-probability measure and a finite `A`
of full measure: `measureEntropy_eq_sum` with the normalisation discharged. Read by
`measureMutualInfo_nonneg_aux` here and by `entropy_sub_le_of_l1` (`Chowla/Fannes`),
`entropy_ge_of_mass_ub` (`Chowla/ResidueUniform`) and `measureEntropy_split_le`
(`Chowla/WeakUniform`). -/
lemma measureEntropy_of_isProbabilityMeasure_finite {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_sum hA]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp

/-- `measureEntropy_of_isProbabilityMeasure_finite` under a second name, kept from upstream.
Read by `measureEntropy_prod`. -/
lemma measureEntropy_of_isProbabilityMeasure_finite' {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure_finite hA

/-- `Hm[(μ univ)⁻¹ • μ] = Hm[μ]`: the entropy is already normalised, so normalising again
changes nothing (both sides `0` when `μ` is not finite or is `0`). Read by
`measureEntropy_le_log_card_of_mem`, `measureEntropy_eq_card_iff_measureReal_eq` and
`measureMutualInfo_univ_smul`. -/
lemma measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => simp [measureEntropy]

/-- `0 ≤ Hm[μ]`: each term is `negMulLog` of a mass in `[0, 1]` after normalisation
(`negMulLog_nonneg`, `prob_le_one`), and `Hm[μ] = 0` when `μ` is not finite. The floor the
random-variable and kernel levels read: `entropy_nonneg` and `condEntropy_nonneg`
(`Salt/Entropy/Basic`), `entropy_nonneg` and `entropy_le_log_card` (`Kernel/Basic`), and the
A-R1 consumer test. -/
lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  apply tsum_nonneg
  intro s
  apply negMulLog_nonneg (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

variable [MeasurableSingletonClass S]

/-- Auxiliary lemma for `measureEntropy_le_log_card_of_mem`, which removes the probability
measure assumption. -/
lemma measureEntropy_le_card_aux {μ : Measure S} [IsProbabilityMeasure μ]
    (A : Finset S) (hμ : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have μA : μ A = 1 := by
    rw [← compl_compl (A : Set S), measure_compl A.measurableSet.compl (measure_ne_top _ _), hμ]
    simp
  let N := A.card
  have N_pos : (0 : ℝ) < N := by
    rcases Finset.eq_empty_or_nonempty A with rfl|hA
    · simp at μA
    · simpa [N] using Finset.card_pos.mpr hA
  simp only [measureEntropy, measure_univ, inv_one, one_smul]
  calc
  ∑' x, negMulLog (μ.real {x})
    = ∑ x ∈ A, negMulLog (μ.real {x}) := by
      apply tsum_eq_sum
      intro i hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [Measure.real, this]
  _ = N * ∑ x ∈ A, (N : ℝ)⁻¹ * negMulLog (μ.real {x}) := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel₀, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x ∈ A, (N : ℝ)⁻¹ * (μ.real {x})) := by
      gcongr
      exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [mul_inv_cancel₀ N_pos.ne', N])
        (by simp)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum]; simp [μA, Measure.real]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ N_pos.ne', N]

/-- For a probability measure on a finite type, `Hm[μ] = log (card S)` iff every atom has real
mass `(card S)⁻¹`: the equality case of Jensen for `negMulLog`
(`strictConcaveOn_negMulLog.map_sum_eq_iff`) at the uniform weights. Read by
`measureEntropy_eq_card_iff_measure_eq_aux` and `measureEntropy_eq_card_iff_measureReal_eq`. -/
lemma measureEntropy_eq_card_iff_measureReal_eq_aux [Fintype S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s, μ.real {s} = (Fintype.card S : ℝ)⁻¹ := by
  cases isEmpty_or_nonempty S
  · simp [Fintype.card_eq_zero, Subsingleton.elim μ 0]
  -- multiply LHS equation through by `N⁻¹`
  set N := Fintype.card S
  have hN : (N:ℝ)⁻¹ ≠ 0 := by positivity
  rw [← mul_right_inj' hN]
  -- setup to use equality case of Jensen
  let w (_ : S) := (N:ℝ)⁻¹
  have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; positivity
  have hw2 : ∑ s : S, w s = 1 := by simp [w, Finset.card_univ, N]
  let p (s : S) := μ.real {s}
  have hp : ∀ s ∈ Finset.univ, 0 ≤ p s := by intros; positivity
  rw [measureEntropy, tsum_fintype, eq_comm]
  convert strictConcaveOn_negMulLog.map_sum_eq_iff hw1 hw2 hp using 2
  · simp [w, p, negMulLog, ← Finset.mul_sum]
  · simp [Finset.mul_sum, w, p]
  · simp [p, ← Finset.mul_sum, w, p]

/-- `measureEntropy_eq_card_iff_measureReal_eq_aux` with the masses in `ℝ≥0∞`:
`μ {s} = (card S : ℝ≥0)⁻¹` (`measureReal_def`, `ENNReal.toReal_eq_toReal_iff'`). No consumer at
884bd7d7. -/
lemma measureEntropy_eq_card_iff_measure_eq_aux
    (μ : Measure S) [Fintype S] [IsProbabilityMeasure μ] :
    Hm[μ] = log (Fintype.card S) ↔ (∀ s : S, μ {s} = (Fintype.card S : ℝ≥0)⁻¹) := by
  rw [measureEntropy_eq_card_iff_measureReal_eq_aux]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s}) (by simp)]
  congr!

set_option linter.flexible false in
/-- `Hm[μ] ≤ log A.card` for any measure carried by the finite set `A`:
`measureEntropy_le_card_aux` after normalising (`measureEntropy_univ_smul`), the `μ = 0` and
infinite-mass branches read off directly. Read by `measureEntropy_le_log_card` and by
`entropy_liouvilleWindow_le` (`Chowla/Windows`). -/
lemma measureEntropy_le_log_card_of_mem
    {A : Finset S} (μ : Measure S) (hμA : μ Aᶜ = 0) :
    Hm[μ] ≤ log A.card := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_natCast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp
    positivity
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux A <| by simp [hμA]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    exact log_natCast_nonneg _

/-- `Hm[μ] ≤ log (card S)` on a finite type: `measureEntropy_le_log_card_of_mem` at `A = univ`.
The log-cardinality ceiling that the random-variable `entropy_le_log_card`
(`Salt/Entropy/Basic`), the kernel `entropy_le_log_card` (`Kernel/Basic`),
`decrement_markov_fintype` (`Chowla/MarkovExtract`) and the A-R1 consumer test read. -/
lemma measureEntropy_le_log_card [Fintype S] (μ : Measure S) : Hm[μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card_of_mem (A := (Finset.univ : Finset S)) μ (by simp)

/-- For a finite nonzero measure on a finite type, `Hm[μ] = log (card S)` iff every atom carries
the same real mass `μ.real univ / card S`: normalise (`measureEntropy_univ_smul`) and apply
`measureEntropy_eq_card_iff_measureReal_eq_aux`. Read by
`measureEntropy_eq_card_iff_measure_eq`. -/
lemma measureEntropy_eq_card_iff_measureReal_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔ ∀ s : S, μ.real {s} = μ.real Set.univ / Fintype.card S := by
  rw [← measureEntropy_univ_smul]
  convert measureEntropy_eq_card_iff_measureReal_eq_aux ((μ Set.univ)⁻¹ • μ) using 2 with s
  simp only [measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_inv, inv_mul_eq_iff_eq_mul₀ (by exact measureReal_univ_ne_zero),
    div_eq_mul_inv]
  rfl

/-- The entropy of a uniform measure is the log of the cardinality of its support. -/
lemma entropy_of_uniformOn (H : Set S) [Nonempty H] [Finite H] :
    measureEntropy (uniformOn H) = log (Nat.card H) := by
  simp only [measureEntropy, measure_univ, inv_one, one_smul, Set.toFinite, uniformOn_real]
  classical
  calc ∑' s, negMulLog ((Nat.card (H ∩ {s} : Set S)) / Nat.card H)
    _ = ∑' s, if s ∈ H then negMulLog (1 / Nat.card H) else 0 := by
      congr with s; by_cases h : s ∈ H <;> simp [h]
    _ = ∑ s ∈ H.toFinite.toFinset, negMulLog (1 / Nat.card H) := by
      convert tsum_eq_sum (s := H.toFinite.toFinset) ?_ using 2 with s hs
      · simp at hs; simp [hs]
      · constructor
        simp
      intro s hs
      simp only [Set.Finite.mem_toFinset] at hs; simp [hs]
    _ = (Nat.card H) * negMulLog (1 / Nat.card H) := by simp [← Set.ncard_coe_finset]
    _ = log (Nat.card H) := by
      simp only [negMulLog, one_div, log_inv, mul_neg, neg_mul, neg_neg, ← mul_assoc]
      rw [mul_inv_cancel₀, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨‹_›, ‹_›⟩

/-- `measureEntropy_eq_card_iff_measureReal_eq` with the masses in `ℝ≥0∞`:
`μ {s} = μ univ / card S`. No consumer at 884bd7d7. -/
lemma measureEntropy_eq_card_iff_measure_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    Hm[μ] = log (Fintype.card S) ↔
    (∀ s : S, μ {s} = μ Set.univ / Fintype.card S) := by
  obtain h | h := isEmpty_or_nonempty S
  · have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  rw [div_eq_mul_inv, measureEntropy_eq_card_iff_measureReal_eq]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  · finiteness

/-- `Hm[μ.map f] = Hm[μ]` for an injective measurable `f`: the sum over `S` restricts to the
image of `f` (`tsum_subtype_eq_of_support_subset`) and re-indexes through `f` (`tsum_image`),
each fibre a singleton. Read by `entropy_comp_of_injective` (`Salt/Entropy/Basic`) and by
`entropy_map_of_injective` and `entropy_snd_compProd_deterministic_of_injective`
(`Kernel/Basic`). -/
lemma measureEntropy_map_of_injective
    (μ : Measure T) (f : T → S) (hf_m : Measurable f) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    map_measureReal_apply hf_m (.singleton _)]
  rw [this]
  classical
  let F (x : S) : ℝ := negMulLog ((μ Set.univ)⁻¹.toReal • μ.real (f ⁻¹' {x}))
  have : ∑' x : S, F x
      = ∑' x : (f '' Set.univ), F x := by
    apply (tsum_subtype_eq_of_support_subset _).symm
    intro x hx
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [F, this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ hf.injOn, tsum_univ fun x ↦ F (f x)]
  congr! with s
  ext s'
  simpa using hf.eq_iff

/-- `Hm[μ.comap f] = Hm[μ]` for a measurable embedding `f` whose range is `μ`-full: the sum over
`S` is the sum over `range f` (`tsum_range`), and the atoms outside the range are null. Read by
`measureEntropy_comap_equiv`. -/
lemma measureEntropy_comap (μ : Measure T) (f : S → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    Hm[μ.comap f] = Hm[μ] := by
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul]
  classical
  rw [← tsum_range (f := fun x ↦ negMulLog ((μ (Set.range f))⁻¹.toReal * μ.real {x})) (g := f)
    hf.injective, measure_congr hf_range ]
  let F (x : T) : ℝ := negMulLog ((μ .univ)⁻¹.toReal * μ.real {x})
  change ∑' x : (Set.range f), F x = ∑' x : T, F x
  apply tsum_subtype_eq_of_support_subset
  intro x hx
  contrapose hx
  suffices μ {x} = 0 by simp [F, Measure.real, this]
  simp only [ae_eq_univ] at hf_range
  exact measure_mono_null (by simp [*]) hf_range

/-- `Hm[μ.comap f] = Hm[μ]` for a measurable equivalence `f`: `measureEntropy_comap` with the
range the whole space. No consumer at 884bd7d7 (the kernel level has its own
`entropy_comap_equiv`). -/
lemma measureEntropy_comap_equiv (μ : Measure T) (f : S ≃ᵐ T) : Hm[μ.comap f] = Hm[μ] := by
  refine measureEntropy_comap μ f f.measurableEmbedding ?_
  simp only [ae_eq_univ]
  have : Set.range f = Set.univ := Equiv.range_eq_univ _
  simp [this]

/-- An ambitious goal would be to replace FiniteSupport with finite entropy. -/
@[simp]
lemma measureEntropy_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableSingletonClass T] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  let A := μ.finSupport
  have hA := measure_compl_support μ
  let B := ν.finSupport
  have hB := measure_compl_support ν
  have hC : (μ.prod ν) (A ×ˢ B : Finset (S × T))ᶜ = 0 := by
    have : ((A ×ˢ B : Finset (S × T)) : Set (S × T))ᶜ
      = ((A : Set S)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set T)ᶜ) := by ext ⟨a, b⟩; simp; tauto
    rw [this]
    simp [hA, hB, A, B]
  have h1 : Hm[μ] = ∑ p ∈ (A ×ˢ B), (negMulLog (μ.real {p.1})) * (ν.real {p.2}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hA, Finset.sum_product]
    congr with s
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices ν.real B = ν.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hB, B]
  have h2 : Hm[ν] = ∑ p ∈ (A ×ˢ B), (negMulLog (ν.real {p.2})) * (μ.real {p.1}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hB, Finset.sum_product_right]
    congr with t
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices μ.real A = μ.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hA, A]
  rw [measureEntropy_of_isProbabilityMeasure_finite' hC, h1, h2, ← Finset.sum_add_distrib]
  congr with ⟨s, t⟩
  simp_rw [← Set.singleton_prod_singleton, measureReal_prod_prod, negMulLog_mul]
  ring

end measureEntropy

section measureMutualInfo

/-- The mutual information between the marginals of a measure on a product space. -/
noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]

/-- The mutual information between the marginals of a measure on a product space. -/
notation:100 "Im[" μ "]" => measureMutualInfo μ

/-- `Im[μ] = Hm[μ.map fst] + Hm[μ.map snd] - Hm[μ]`, by `rfl`: `measureMutualInfo` unfolded. The
first rewrite of `measureMutualInfo_of_not_isFiniteMeasure`, `measureMutualInfo_univ_smul`,
`measureMutualInfo_swap`, `measureMutualInfo_prod` and `measureMutualInfo_nonneg_aux`. -/
lemma measureMutualInfo_def (μ : Measure (S × T)) :
    Im[μ] = Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ] := rfl

/-- `Im[0] = 0` (`simp [measureMutualInfo]`). A `simp` lemma; no named consumer at 884bd7d7. -/
@[simp]
lemma measureMutualInfo_zero_measure : Im[(0 : Measure (S × T))] = 0 := by
  simp [measureMutualInfo]

/-- `Im[μ] = 0` when `μ` is not finite: neither marginal is finite either, so all three
entropies vanish (`measureEntropy_of_not_isFiniteMeasure`). The infinite-mass branch of
`measureMutualInfo_univ_smul` and `measureMutualInfo_nonneg`. -/
lemma measureMutualInfo_of_not_isFiniteMeasure {μ : Measure (S × U)} (h : ¬ IsFiniteMeasure μ) :
    Im[μ] = 0 := by
  rw [measureMutualInfo_def]
  have h1 : ¬ IsFiniteMeasure (μ.map Prod.fst) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_fst MeasurableSet.univ
  have h2 : ¬ IsFiniteMeasure (μ.map Prod.snd) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_snd MeasurableSet.univ
  rw [measureEntropy_of_not_isFiniteMeasure h, measureEntropy_of_not_isFiniteMeasure h1,
    measureEntropy_of_not_isFiniteMeasure h2]
  simp

/-- `Im[(μ univ)⁻¹ • μ] = Im[μ]`: `measureEntropy_univ_smul` on `μ` and on its two marginals
(`Measure.map_smul`), the infinite-mass and zero branches read off. Read by
`measureMutualInfo_nonneg` to pass from a finite measure to a probability measure. -/
lemma measureMutualInfo_univ_smul (μ : Measure (S × U)) : Im[(μ Set.univ)⁻¹ • μ] = Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  rcases eq_zero_or_neZero μ with hμ | _
  · simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1
  · congr 1
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_fst]
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_snd]
  convert measureEntropy_univ_smul

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

/-- `Im[μ.map Prod.swap] = Im[μ]`: the marginals exchange roles (`add_comm`, `Measure.map_map`)
and `Hm[μ.map swap] = Hm[μ]` by re-indexing the sum through the bijection `swap` (`tsum_range`).
No consumer at 884bd7d7. -/
lemma measureMutualInfo_swap (μ : Measure (S × T)) :
    Im[μ.map Prod.swap] = Im[μ] := by
  rw [measureMutualInfo_def, add_comm, Measure.map_map measurable_snd measurable_swap,
    Measure.map_map measurable_fst measurable_swap]
  congr 1
  simp_rw [measureEntropy, Measure.map_apply measurable_swap MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.ennreal_smul_real_apply, smul_eq_mul]
  simp_rw [map_measureReal_apply measurable_swap (.singleton _)]
  have : Set.range (Prod.swap : S × T → T × S) = .univ := Set.range_eq_univ.mpr Prod.swap_surjective
  rw [← tsum_univ, ← this,
    tsum_range (fun x ↦ negMulLog <| (μ Set.univ)⁻¹.toReal * μ.real (Prod.swap⁻¹' {x}))
      Prod.swap_injective]
  congr! with ⟨s, t⟩
  simpa using Prod.swap_injective.preimage_image {(s, t)}

/-- A product measure carries no mutual information: `Im[μ.prod ν] = 0`, by
`measureEntropy_prod` (`Hm[μ.prod ν] = Hm[μ] + Hm[ν]`) and the marginals of a product. A `simp`
lemma; no named consumer at 884bd7d7. -/
@[simp]
lemma measureMutualInfo_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Im[μ.prod ν] = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp

/-- An ambitious goal would be to replace FiniteSupport with finite entropy. Proof is long and slow;
needs to be optimized -/
lemma measureMutualInfo_nonneg_aux {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    0 ≤ Im[μ] ∧
    (Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let E := μ.finSupport
  have hE := measure_compl_support μ
  classical
  set E1 : Finset S := Finset.image Prod.fst E
  set E2 : Finset U := Finset.image Prod.snd E
  have hE' : μ (E1 ×ˢ E2 : Finset (S × U))ᶜ = 0 := by
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    contrapose!
    intro h
    simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
      Finset.coe_product, mem_prod, not_and, Classical.not_imp] at h ⊢
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E, E2,
      mem_support]
    constructor
    · use u
    · use s
  have hE1 : (μ.map Prod.fst) E1ᶜ = 0 := by
    rw [Measure.map_apply measurable_fst (MeasurableSet.compl (Finset.measurableSet E1))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
      mem_support]
    intro h; use u
  have hE1' : (μ.map Prod.fst).real E1 = 1 := by
    rw [prob_compl_eq_zero_iff E1.measurableSet] at hE1
    unfold Measure.real
    rw [hE1]
    norm_num
  have hE2 : (μ.map Prod.snd) E2ᶜ = 0 := by
    rw [Measure.map_apply measurable_snd (MeasurableSet.compl (Finset.measurableSet E2))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
    intro h; use s
  have hE2' : (μ.map Prod.snd).real E2 = 1 := by
    rw [prob_compl_eq_zero_iff E2.measurableSet] at hE2
    unfold Measure.real
    rw [hE2]
    norm_num
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (.singleton _)]
    refine fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (.singleton _)]
    exact fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z ∈ E2, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_eq_right, iUnion_exists, mem_iUnion,
          mem_singleton_iff, Prod.mk.injEq, true_and, exists_prop, exists_and_right,
          exists_eq_right', E2, E] at h2 ⊢
        use s
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  have h2 z : (μ.map Prod.snd).real {z} = ∑ y ∈ E1, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, iUnion_exists,
          mem_iUnion, mem_singleton_iff, Prod.mk.injEq, and_true, exists_prop, exists_eq_right', E1,
          E] at h2 ⊢
        use u
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) := ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p ∈ (E1 ×ˢ E2), 0 ≤ w p := by intros; positivity
  have hw2 : ∑ p ∈ E1 ×ˢ E2, w p = 1 := by
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, sum_measureReal_singleton, w]
    rw [← Finset.sum_mul]
    rw [show (1 : ℝ) = 1 * 1 by norm_num]
    congr
    convert hE1'
    simp
  have hf : ∀ p ∈ E1 ×ˢ E2, 0 ≤ f p := by intros; positivity
  have H :=
  calc
    ∑ p ∈ E1 ×ˢ E2, w p * f p
        = ∑ p ∈ E1 ×ˢ E2, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [f, hp]
          · simp [w, f]
            field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
      _ = 1 := by
        simp only [sum_measureReal_singleton, Finset.coe_product]
        rw [show 1 = μ.real Set.univ by simp]
        apply measureReal_congr
        simpa using hE'
  have H1 : -measureMutualInfo (μ := μ) = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := calc
    _ = ∑ p ∈ E1 ×ˢ E2,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        have H0 : Hm[μ] = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log (μ.real {p}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE', negMulLog, neg_mul,
            Finset.sum_neg_distrib]
        have H1 : Hm[μ.map Prod.fst] = -∑ p ∈ E1 ×ˢ E2,
            μ.real {p} * log ((μ.map Prod.fst).real {p.1}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE1, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product, ← Finset.sum_mul]
          congr! with s _
          exact h1 s
        have H2 : Hm[μ.map Prod.snd] =
            -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log ((μ.map Prod.snd).real {p.2}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE2, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product_right, ← Finset.sum_mul]
          congr! with s _
          exact h2 s
        simp_rw [measureMutualInfo_def, H0, H1, H2]
        simp [Finset.sum_add_distrib]
    _ = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := by
        congr! 1 with p _
        by_cases hp : μ.real {p} = 0
        · simp [f, hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        simp [negMulLog, log_mul, log_inv, h_fst_ne_zero p hp, h_snd_ne_zero p hp, hp, w, f]
        field_simp
        ring
  have H2 : 0 = negMulLog (∑ s ∈ (E1 ×ˢ E2), w s * f s) := by
    rw [H, negMulLog_one]
  constructor
  · rw [← neg_nonpos, H1, H2]
    exact concaveOn_negMulLog.le_map_sum hw1 hw2 hf
  rw [← neg_eq_zero, H1, H2, eq_comm]
  refine (strictConcaveOn_negMulLog.map_sum_eq_iff' hw1 hw2 hf).trans ?_
  have w0 (p : S × U) (hp: w p = 0) : μ.real {p} = 0 := by
    simp only [mul_eq_zero, w] at hp
    rcases hp with hp | hp
    · contrapose! hp; exact (h_fst_ne_zero p) hp
    · contrapose! hp; exact (h_snd_ne_zero p) hp
  constructor
  · intro hyp p
    by_cases hp1 : p.1 ∈ E1
    · by_cases hp2 : p.2 ∈ E2
      · have hp : p ∈ E1 ×ˢ E2 := Finset.mem_product.mpr ⟨hp1, hp2⟩
        by_cases hw : w p = 0
        · rw [w0 p hw]
          exact hw.symm
        replace hyp := hyp p hp hw
        simp_rw [smul_eq_mul, H] at hyp
        have := eq_of_inv_mul_eq_one hyp
        convert this.symm
      have : {p.2} ⊆ (E2 : Set U)ᶜ := by
        simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp2
      replace : (Measure.map Prod.snd μ).real {p.2} = 0 := by
        rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE2
      have hp : μ.real {p} = 0 := by contrapose! this; exact (h_snd_ne_zero p) this
      simp [hp, this]
    have : {p.1} ⊆ (E1 : Set S)ᶜ := by
      simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp1
    replace : (Measure.map Prod.fst μ).real {p.1} = 0 := by
      rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE1
    have hp : μ.real {p} = 0 := by contrapose! this; exact (h_fst_ne_zero p) this
    simp [hp, this]
  intro hyp ⟨s, u⟩ _ hw
  simp_rw [smul_eq_mul, H]
  change (w (s,u))⁻¹ * (μ.real {(s,u)}) = 1
  have : w (s,u) ≠ 0 := by exact hw
  field_simp [this]
  rw [hyp (s,u)]

/-- `0 ≤ Im[μ]` for a finitely supported measure on a product: normalise
(`measureMutualInfo_univ_smul`) and take the first half of `measureMutualInfo_nonneg_aux`; `0`
when `μ` is not finite. Read by the random-variable `mutualInfo_nonneg` (`Salt/Entropy/Basic`),
the kernel `mutualInfo_nonneg'` (`Kernel/MutualInfo`), and the `positivity` extension
`evalMeasureMutualInfo` below. -/
lemma measureMutualInfo_nonneg {μ : Measure (S × U)} [FiniteSupport μ] :
    0 ≤ Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureMutualInfo_univ_smul μ]
    apply measureMutualInfo_nonneg_aux.1
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]

/-- `Im[μ] = 0` iff `μ` is the product of its marginals atom by atom
(`μ.real {p} = (μ.map fst).real {p.1} * (μ.map snd).real {p.2}` for every `p`), for a finitely
supported zero-or-probability measure: the second half of `measureMutualInfo_nonneg_aux` (the
equality case of Jensen). No consumer at 884bd7d7. -/
lemma measureMutualInfo_eq_zero_iff {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    Im[μ] = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2} :=
  measureMutualInfo_nonneg_aux.2

end measureMutualInfo

end ProbabilityTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function ProbabilityTheory

/-- Extension for `measureMutualInfo`. -/
@[positivity measureMutualInfo _]
def evalMeasureMutualInfo : PositivityExt where eval {u α} _
  | none, _ => pure .none
  | some _, e => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@measureMutualInfo $S $T $measS $measT $μ) =>
    assertInstancesCommute
    let _ ← synthInstanceQ q(MeasurableSingletonClass $S)
    let _ ← synthInstanceQ q(MeasurableSingletonClass $T)
    let _ ← synthInstanceQ q(FiniteSupport $μ)
    pure <| .nonnegative q(measureMutualInfo_nonneg (μ := $μ))
  | _, _, _ => throwError "failed to match ProbabilityTheory.measureMutualInfo"

example {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] {μ : Measure (S × T)} [FiniteSupport μ] : 0 ≤ Im[μ] := by
  positivity

end Mathlib.Meta.Positivity
