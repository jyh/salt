/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/ForMathlib/Entropy/Kernel/Basic.lean`, at
commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`; the `public import`s of
  `Mathlib.MeasureTheory.Integral.Prod`, `PFR.ForMathlib.Entropy.Measure`, and
  `PFR.Mathlib.Probability.Kernel.Disintegration`; and `@[expose] public
  section`) to a plain `import Mathlib` plus imports of the Salt ports of the
  two PFR residues, `Salt.Entropy.Measure` and
  `Salt.Entropy.Mathlib.KernelDisintegration`. `Mathlib.MeasureTheory.Integral.Prod`
  is subsumed by `import Mathlib`.
- NAME-COLLISION DRIFT (inherited from `Salt.Entropy.Measure`): the finite
  support of a measure is `Measure.finSupport` here, not `Measure.support`
  (mathlib v4.32.0-rc1 ships a topological `Measure.support`). The 4 dot-notation
  `μ.support`/`ν.support` projections in the upstream file
  (`finiteKernelSupport_of_const`, `finiteSupport_of_compProd'`,
  `FiniteSupport.comap_equiv`, `entropy_compProd_aux`) are rewritten to
  `.finSupport`. The lemma names `measure_compl_support`, `ae_mem_support`,
  `mem_support` are unchanged.
- All other declarations, names, notation, namespaces, and proof bodies are
  verbatim from upstream; drift v4.33-rc1 → v4.32.0-rc1 required no further
  statement or proof changes.
- Docstrings added by Salt (2026-11-01, the O83 documentation lane) to the 34 upstream
  declarations that carried none; names, statements and bodies are unchanged.
-/
import Mathlib
import Salt.Entropy.Measure
import Salt.Entropy.Mathlib.KernelDisintegration

/-!
# Entropy of a kernel with respect to a measure

## Main definitions

* `Kernel.entropy`: entropy of a kernel `κ` with respect to a measure `μ`,
  `μ[fun t ↦ measureEntropy (κ t)]`. We use the notation `Hk[κ, μ]`.

## Main statements

* `chain_rule`: `Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)]`.
* `entropy_map_le`: data-processing inequality for the kernel entropy

## Notations

* `Hk[κ, μ] = Kernel.entropy κ μ`

-/

open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

/-- Entropy of a kernel with respect to a measure. -/
noncomputable
def entropy (κ : Kernel T S) (μ : Measure T) := μ[fun y ↦ Hm[κ y]]

/-- Entropy of a kernel with respect to a measure. -/
notation3:100 "Hk[" κ " , " μ "]" => ProbabilityTheory.Kernel.entropy κ μ

/-- `Hk[κ, 0] = 0`: the kernel entropy against the zero measure vanishes (`simp [entropy]`, an
integral over `0`). A `simp` lemma: what closes the `μ = 0` branch of the
`eq_zero_or_isProbabilityMeasure` splits below (`entropy_prod`, `entropy_map_le`) and in
`Kernel/MutualInfo`. -/
@[simp]
lemma entropy_zero_measure (κ : Kernel T S) : Hk[κ, (0 : Measure T)] = 0 := by simp [entropy]

/-- `Hk[0, μ] = 0`: the entropy of the zero kernel vanishes (`simp [entropy]`, each
`Hm[0 y] = 0`). A `simp` lemma: what closes the `κ = 0` branch of the
`eq_zero_or_isMarkovKernel` splits (`entropy_compProd_aux`, `entropy_map_le`, the
`Kernel/MutualInfo` lemmas). -/
@[simp]
lemma entropy_zero_kernel (μ : Measure T) : Hk[(0 : Kernel T S), μ] = 0 := by simp [entropy]

/-- Kernels equal `μ`-almost everywhere have the same entropy against `μ`: `integral_congr_ae`
under `entropy`. The congruence every `condDistrib`/`condKernel` rewrite rides —
`condEntropy_two_eq_kernel_entropy`, `chain_rule'` and `entropy_submodular` in
`Salt/Entropy/Basic`, `entropy_compProd` and `entropy_prod` here, `mutualInfo_congr` and the
triple lemmas in `Kernel/MutualInfo`. -/
lemma entropy_congr {μ} {κ η : Kernel T S} (h : κ =ᵐ[μ] η) : Hk[κ, μ] = Hk[η, μ] := by
  simp_rw [entropy]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- `0 ≤ Hk[κ, μ]`: an integral of the nonnegative `measureEntropy` (`integral_nonneg`). Closes
`entropy_map_le` (`le_add_iff_nonneg_right`); the random-variable-level `entropy_nonneg` of
`Salt/Entropy/Basic` is its twin at the measure level. -/
lemma entropy_nonneg (κ : Kernel T S) (μ : Measure T) :
    0 ≤ Hk[κ, μ] := integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

/-- `Hk[const T ν, μ] = (μ univ).toReal * Hm[ν]`: a constant kernel's entropy is the total mass
of `μ` times the entropy of `ν` (`simp [entropy, Measure.real]`). A `simp` lemma; no named
consumer at 884bd7d7. -/
@[simp]
lemma entropy_const (ν : Measure S) (μ : Measure T) :
    Hk[Kernel.const T ν, μ] = (μ Set.univ).toReal * Hm[ν] := by
  simp [entropy, Measure.real]

/-- Constant kernels with finite support, have finite kernel support. -/
lemma finiteKernelSupport_of_const (ν : Measure S) [FiniteSupport ν] :
    FiniteKernelSupport (Kernel.const T ν) := by
  intro t
  use ν.finSupport
  simp [measure_compl_support ν]

/-- Composing a finitely supported measure with a finitely supported kernel gives a finitely
supported kernel. -/
lemma finiteSupport_of_compProd' [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  let A := μ.finSupport
  have hA := measure_compl_support μ
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Measure.ae_compProd_iff (by exact (Finset.finite_toSet _).measurableSet)]
  filter_upwards [ae_mem_support μ] with t ht
  filter_upwards [hB t ht] with s hs
  exact Finset.mk_mem_product ht hs

/-- `μ ⊗ₘ κ` has finite support when `μ` does and `κ` has finite kernel support `μ`-a.e.:
`Measure.compProd_congr` to the modification `hκ.mk`, then `finiteSupport_of_compProd'`.
Supplies the finite-support instances `entropy_prodMkRight` here and
`entropy_submodular_compProd` (`Kernel/MutualInfo`) build. -/
lemma finiteSupport_of_compProd
    [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  rw [Measure.compProd_congr hκ.ae_eq_mk]
  exact finiteSupport_of_compProd' hκ.finiteKernelSupport_mk

/-- `condDistrib X Y μ` has finite kernel support `μ.map Y`-a.e. when `X` has finite range:
along `condDistrib_ae_eq` each fibre is the law of `X` conditioned on `Y`, finitely supported by
`finiteSupport_of_finiteRange`. The side condition `entropy_submodular` (`Salt/Entropy/Basic`)
discharges with `fun_prop`. -/
lemma aefiniteKernelSupport_condDistrib
    [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] :
    AEFiniteKernelSupport (condDistrib X Y μ) (μ.map Y) := by
  filter_upwards [condDistrib_ae_eq hX hY μ] with a ha
  rw [ha]
  exact finiteSupport_of_finiteRange.finite
/-- `Hk[κ, μ] ≤ log (card S)` for a probability measure `μ` and a finite `S`:
`integral_mono_of_nonneg` against the constant `log (card S)`, fibrewise
`measureEntropy_le_log_card`. The kernel form of the log-cardinality ceiling; the `Chowla` files
read the random-variable form `ProbabilityTheory.entropy_le_log_card`, and this one has no
consumer at 884bd7d7. -/
lemma entropy_le_log_card
   [MeasurableSingletonClass S]
   (κ : Kernel T S) (μ : Measure T) [Fintype S] [IsProbabilityMeasure μ] :
    Hk[κ, μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp

/-- `Hk[κ, μ] = μ[fun y ↦ ∑' x, negMulLog ((κ y).real {x})]` for a zero-or-Markov kernel:
`measureEntropy_of_isProbabilityMeasure` under `entropy`. The series form of the kernel entropy;
no consumer at 884bd7d7. -/
lemma entropy_eq_integral_sum (κ : Kernel T S) [IsZeroOrMarkovKernel κ] (μ : Measure T) :
    Hk[κ, μ] = μ[fun y ↦ ∑' x, negMulLog ((κ y).real {x})] := by
  simp_rw [entropy, measureEntropy_of_isProbabilityMeasure]

-- entropy_map_of_injective is a special case of this (see def of map)
/-- Composing a Markov kernel `κ` with the deterministic kernel of an `f` injective in its
second argument, then projecting to the output, leaves the entropy unchanged:
`snd (κ ⊗ₖ deterministic f) t = map κ (f (t, ·)) t` fibrewise, then
`measureEntropy_map_of_injective`. The first step of the `calc` in
`entropy_snd_sub_mutualInfo_le_entropy_map_of_injective` (`Kernel/MutualInfo`). -/
lemma entropy_snd_compProd_deterministic_of_injective [MeasurableSingletonClass U]
    (κ : Kernel T S) [IsMarkovKernel κ]
    (μ : Measure T) {f : T × S → U}
    (hf : ∀ t, Function.Injective (fun x ↦ f (t, x))) (hmes : Measurable f) :
    Hk[snd (κ ⊗ₖ deterministic f hmes), μ] = Hk[κ, μ] := by
  have : ∀ t, snd (κ ⊗ₖ deterministic f hmes) t
      = map κ (fun x ↦ f (t, x)) t := by
    intro t
    ext s hs
    rw [snd_apply' _ _ hs, compProd_deterministic_apply, map_apply' _ (by fun_prop) _ hs]
    · rfl
    · exact measurable_snd hs
  simp_rw [entropy]
  congr with y
  convert measureEntropy_map_of_injective (κ y) _ (hmes.comp measurable_prodMk_left) (hf y)
  rw [this y, map_apply _ (by fun_prop)]
  rfl

/-- `Hk[map κ f, μ] = Hk[κ, μ]` for an injective measurable `f`:
`measureEntropy_map_of_injective` fibrewise under `entropy`. Read by `entropy_map_swap`, by
`entropy_map_le` (at `x ↦ (x, f x)`) and by `entropy_triple_add_entropy_le'`
(`Kernel/MutualInfo`, at `prodAssoc.symm`). -/
lemma entropy_map_of_injective [MeasurableSingletonClass U]
    (κ : Kernel T S) (μ : Measure T) {f : S → U} (hf : Function.Injective f) (hmes : Measurable f) :
    Hk[map κ f, μ] = Hk[κ, μ] := by
  simp_rw [entropy, map_apply _ hmes, measureEntropy_map_of_injective _ _ hmes hf]

/-- `Hk[map κ Prod.swap, μ] = Hk[κ, μ]`: `entropy_map_of_injective` at `Prod.swap`. The rewrite
behind `entropy_swapRight`. -/
lemma entropy_map_swap [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    Hk[map κ Prod.swap, μ] = Hk[κ, μ] :=
  entropy_map_of_injective κ μ Prod.swap_injective measurable_swap

/-- `Hk[swapRight κ, μ] = Hk[κ, μ]`: `swapRight_eq` then `entropy_map_swap`. Read by
`chain_rule'` here and by `mutualInfo_swapRight` and `entropy_triple_add_entropy_le` in
`Kernel/MutualInfo`. -/
lemma entropy_swapRight [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    Hk[swapRight κ, μ] = Hk[κ, μ] := by
  rw [swapRight_eq, entropy_map_swap]

/-- Pulling `κ` back along a measurable embedding `f` whose range is `μ`-full, against the comap
measure (finitely supported), preserves the entropy: both sides are the finite sum over the
support, re-indexed through `f` (`Finset.sum_image`). `entropy_comap_equiv` specialises it to a
measurable equivalence. -/
lemma entropy_comap [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel T S) (μ : Measure T) (f : T' → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.comap f)] (hfμ : FiniteSupport (μ.comap f)) :
    Hk[comap κ f hf.measurable, μ.comap f] = Hk[κ, μ] := by
  classical
  rcases hfμ with ⟨A, (hA : ∀ᵐ x ∂μ.comap f, x ∈ A)⟩
  have : ∀ᵐ x ∂μ, x ∈ Finset.image f A := by
    change μ (Finset.image f A : Set T)ᶜ = 0
    simp only [Finset.coe_image, hf.injective.compl_image_eq, measure_union_null_iff]
    constructor
    · rwa [← Measure.comap_apply f hf.injective hf.measurableSet_image']
      exact MeasurableSet.compl (Finset.measurableSet A)
    exact ae_eq_univ.mp hf_range
  simp_rw [entropy]
  simp_rw [integral_eq_setIntegral hA, integral_eq_setIntegral this,
    setIntegral_finset _ .finset,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [← Finset.sum_image (f := fun x ↦ μ.real {x} * measureEntropy (κ x)) (g := f)]
  intro x _ y _ hxy
  exact hf.injective hxy

/-- The comap of a finitely supported measure along a measurable equivalence `f` is finitely
supported, on the image of the support under `f.symm`. Supplies `entropy_comap_equiv`'s
finite-support side condition. -/
lemma FiniteSupport.comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T']
    {μ : Measure T} (f : T' ≃ᵐ T) [FiniteSupport μ] :
    FiniteSupport (μ.comap f) := by
  classical
  let A := μ.finSupport
  have hA := measure_compl_support μ
  refine ⟨Finset.image f.symm A, ?_⟩
  change (Measure.comap (⇑f) μ) (A.image f.symm)ᶜ = 0
  rwa [Finset.coe_image, ← Set.image_compl_eq (MeasurableEquiv.bijective f.symm),
    Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm,
    MeasurableEquiv.image_preimage]
  · exact fun _ ↦ (MeasurableEquiv.measurableSet_image f).mpr
  · exact f.symm.measurableSet_image.mpr A.measurableSet.compl

/-- `Hk[comap κ f, μ.comap f] = Hk[κ, μ]` for a measurable equivalence `f`: `entropy_comap` with
`f.measurableEmbedding`, its range the whole space, and `FiniteSupport.comap_equiv`. Read by
`entropy_comap_swap`, `entropy_prodMkLeft_unit` and `entropy_submodular_compProd`
(`Kernel/MutualInfo`). -/
lemma entropy_comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel T S) {μ : Measure T} (f : T' ≃ᵐ T)
    [IsFiniteMeasure μ] [FiniteSupport μ] :
    Hk[comap κ f f.measurable, μ.comap f] = Hk[κ, μ] := by
  simp [entropy_comap, f.measurableEmbedding, FiniteSupport.comap_equiv f]

/-- `Hk[comap κ Prod.swap, μ.comap Prod.swap] = Hk[κ, μ]`: `entropy_comap_equiv` at
`MeasurableEquiv.prodComm`. The last rewrite of `condEntropy_two_eq_kernel_entropy`
(`Salt/Entropy/Basic`). -/
lemma entropy_comap_swap [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel (T' × T) S) {μ : Measure (T' × T)} [IsFiniteMeasure μ] [FiniteSupport μ] :
    Hk[comap κ Prod.swap measurable_swap, μ.comap Prod.swap] = Hk[κ, μ] :=
  entropy_comap_equiv κ MeasurableEquiv.prodComm

/-- `Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ]`: `entropy_comap_equiv` at
`MeasurableEquiv.punitProd`, the `map` read as the comap of the inverse equivalence. Closes the
conditional-entropy term of `chain_rule'` (`Salt/Entropy/Basic`). -/
lemma entropy_prodMkLeft_unit [MeasurableSingletonClass T]
    (κ : Kernel T S) {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  rw [← MeasurableEquiv.map_symm]
  congr
/-- The chain rule for a composition `κ ⊗ₖ η` under finite kernel supports, with the second term
fibrewise: `Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + μ[fun t ↦ Hk[comap η (Prod.mk t), κ t]]`. Both sides
reduce to finite sums over the supports (`measureEntropy_eq_sum`) and `negMulLog_mul` splits
each product mass. `entropy_compProd'` folds the integral back into `Hk[η, μ ⊗ₘ κ]`. -/
lemma entropy_compProd_aux [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ] (hκ : FiniteKernelSupport κ)
    (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ]
      + μ[fun t ↦ Hk[comap η (Prod.mk t) measurable_prodMk_left, (κ t)]] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  let A := μ.finSupport
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t ∈ A, (μ.real {t}) * (F t) := by
    rw [integral_eq_setIntegral (ae_mem_support μ), setIntegral_finset _ .finset]
    congr with t ht
  simp_rw [entropy, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← mul_add]
  congr
  obtain ⟨B, hB⟩ := local_support_of_finiteKernelSupport hκ A
  obtain ⟨C, hC⟩ := local_support_of_finiteKernelSupport hη (A ×ˢ B)
  rw [integral_eq_setIntegral (hB t ht)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C : Finset (S × U))ᶜ = 0 := by
    rw [Kernel.compProd_apply (Finset.measurableSet _).compl,
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum]
    apply Finset.sum_eq_zero
    intro s hs
    simpa using .inr <| measure_mono_null (by simp [*]) (hC (t, s) <| by simp [ht, hs])
  rw [measureEntropy_eq_sum hκη, measureEntropy_eq_sum (hB t ht),
    setIntegral_finset _ .finset,
    ← Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [measure_univ, inv_one, one_smul, coe_comap, Function.comp_apply, smul_eq_mul]
  have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
  rw [measureEntropy_eq_sum (hC (t, s) hts)]
  simp only [measure_univ, inv_one, one_smul]
  have : negMulLog ((κ t).real {s}) = ∑ u ∈ C, negMulLog ((κ t).real {s}) *
      ((comap η (Prod.mk t) measurable_prodMk_left) s).real {u} := by
    rw [← Finset.mul_sum]
    simp only [coe_comap, Function.comp_apply, sum_measureReal_singleton]
    suffices (η (t, s)).real ↑C = (η (t, s)).real Set.univ by simp [this]
    have := hC (t, s) hts
    rw [ae_iff, ← measureReal_eq_zero_iff] at this
    change (η (t, s)).real Cᶜ = 0 at this
    rw [← measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = (κ t).real {s} * (η (t, s)).real {u} := by
    rw [measureReal_def, compProd_apply (.singleton _),
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum,
      Finset.sum_eq_single_of_mem s hs]
    · simp [measureReal_def, Set.preimage]
    intro b _ hbs
    simp [hbs, Set.preimage]
  rw [this, Kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog]
  ring

/-- `Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ]` under finite kernel supports everywhere:
`entropy_compProd_aux`, then `Measure.integral_compProd` (integrable by
`finiteSupport_of_compProd'`). `entropy_compProd` lifts it to a.e. supports. -/
lemma entropy_compProd' [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  rw [entropy_compProd_aux hκ hη]
  congr
  rw [entropy, Measure.integral_compProd]
  · simp_rw [entropy]
    congr
  · have := finiteSupport_of_compProd' hκ (μ := μ)
    exact integrable_of_finiteSupport (μ ⊗ₘ κ)

/-- The chain rule for a composition: `Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ]` for
a.e.-finitely-supported `κ` and `η`. Both are replaced by their modifications `hκ.mk`, `hη.mk`
(`entropy_congr`, `compProd_congr_ae`) and `entropy_compProd'` applies. Read by `chain_rule`,
`entropy_compProd_deterministic` and `mutualInfo_compProd` (`Kernel/MutualInfo`). -/
lemma entropy_compProd [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
  have h_ent1 : Hk[hκ.mk ⊗ₖ hη.mk, μ] = Hk[κ ⊗ₖ η, μ] := by
    refine entropy_congr <| compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm
  have h_ent2 : Hk[hκ.mk, μ] = Hk[κ, μ] := entropy_congr hκ.ae_eq_mk.symm
  have h_ent3 : Hk[hη.mk, μ ⊗ₘ hκ.mk] = Hk[η, μ ⊗ₘ κ] := by
    rw [h_meas_eq, entropy_congr hη.ae_eq_mk]
  rw [← h_ent1, ← h_ent2, ← h_ent3,
    entropy_compProd' hκ.finiteKernelSupport_mk hη.finiteKernelSupport_mk]
/-- `Hk[deterministic f, μ] = 0`: each fibre is a Dirac mass, whose entropy vanishes
(`measureEntropy_dirac`). A `simp` lemma; what `simp` reaches in
`entropy_compProd_deterministic`. -/
@[simp]
lemma entropy_deterministic [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] (f : T → S) (μ : Measure T) :
    Hk[deterministic f .of_discrete, μ] = 0 := by
  simp_rw [entropy]
  convert integral_zero T ℝ
  apply measureEntropy_dirac

/-- Composing with a deterministic kernel adds no entropy:
`Hk[κ ⊗ₖ deterministic f, μ] = Hk[κ, μ]`, by `entropy_compProd` and `entropy_deterministic`. A
`simp` lemma; no named consumer at 884bd7d7. -/
@[simp]
lemma entropy_compProd_deterministic [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (κ : Kernel T S) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U)
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ ⊗ₖ (deterministic f .of_discrete), μ] = Hk[κ, μ] := by
  simp [entropy_compProd hκ ((FiniteKernelSupport.deterministic f).aefiniteKernelSupport _)]

/-- A Markov kernel out of a nonempty type lands in a nonempty type: the fibre at any point is a
probability measure, hence `NeZero`. Supplies the `Nonempty` instances
`nonempty_of_isProbabilityMeasure_of_isMarkovKernel` and the `Kernel/MutualInfo` triple lemmas
(`entropy_submodular_compProd`, `entropy_compProd_triple_add_entropy_le`) need. -/
lemma nonempty_of_isMarkovKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] [Nonempty α] : Nonempty β :=
  (κ <| Classical.arbitrary _).nonempty_of_neZero

/-- A Markov kernel `κ : Kernel α β` with a probability measure on `α` lands in a nonempty `β`:
`μ.nonempty_of_neZero`, then `nonempty_of_isMarkovKernel`. Read by `entropy_prod` and
`entropy_map_le` here and by the `Kernel/MutualInfo` lemmas that split on
`eq_zero_or_isProbabilityMeasure`. -/
lemma nonempty_of_isProbabilityMeasure_of_isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] : Nonempty β := by
  have : Nonempty α := μ.nonempty_of_neZero
  exact nonempty_of_isMarkovKernel κ

/-- The kernel chain rule: `Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ fst κ]` for
`κ : Kernel T (S × U)`, from `disintegration κ` and `entropy_compProd`. Read by `chain_rule'`
and `entropy_prod` here, by `mutualInfo_eq_snd_sub` and `entropy_compProd_triple_add_entropy_le`
in `Kernel/MutualInfo`, and by the random-variable `chain_rule'` of `Salt/Entropy/Basic`. -/
lemma chain_rule [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ] [hU : Nonempty U]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd hκ.fst (aefiniteKernelSupport_of_cond _ hκ)]

/-- The chain rule conditioning on the second coordinate:
`Hk[κ, μ] = Hk[snd κ, μ] + Hk[condKernel (swapRight κ), μ ⊗ₘ snd κ]`, from `chain_rule` at
`swapRight κ` and `entropy_swapRight`. Read by `entropy_map_le` and by `mutualInfo_eq_fst_sub`
(`Kernel/MutualInfo`). -/
lemma chain_rule' [Nonempty S] [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] = Hk[snd κ, μ] + Hk[condKernel (swapRight κ), μ ⊗ₘ (snd κ)] := by
  rw [← entropy_swapRight, chain_rule hκ.swapRight]
  simp

/-- `Hk[prodMkRight S η, μ ⊗ₘ κ] = Hk[η, μ]` for a Markov `κ`: the kernel ignores the `S`
coordinate, so `Measure.integral_compProd` (integrable by `finiteSupport_of_compProd`)
integrates `κ` out. A `simp` lemma; read by `entropy_prodMkRight'` and `entropy_prod`. -/
@[simp]
lemma entropy_prodMkRight [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T]
    {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[prodMkRight S η, μ ⊗ₘ κ] = Hk[η, μ] := by
  have := finiteSupport_of_compProd hκ (μ := μ)
  simp [entropy, Measure.integral_compProd, integrable_of_finiteSupport]

/-- `Hk[prodMkRight S η, μ.prod ν] = Hk[η, μ]` for a probability measure `ν`:
`entropy_prodMkRight` at the constant kernel `const T ν`, the product measure read as
`μ ⊗ₘ const T ν`. No consumer at 884bd7d7. -/
lemma entropy_prodMkRight' [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T]
    {η : Kernel T U}
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    Hk[prodMkRight S η, μ.prod ν] = Hk[η, μ] := by
  rw [← entropy_prodMkRight (μ := μ) ((finiteKernelSupport_of_const ν).aefiniteKernelSupport _)]
  congr
  ext s hs
  simp_rw [Measure.prod_apply hs, Measure.compProd_apply hs, Kernel.const_apply]

/-- `Hk[prodMkLeft S η, ν.prod μ] = Hk[η, μ]` for a probability measure `ν`: `integral_prod`
integrates the ignored `S` coordinate out. A `simp` lemma; no named consumer at 884bd7d7. -/
@[simp]
lemma entropy_prodMkLeft [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {η : Kernel T U}
    {ν : Measure S} [IsProbabilityMeasure ν] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] [FiniteSupport ν] :
    Hk[prodMkLeft S η, ν.prod μ] = Hk[η, μ] := by
  simp_rw [entropy, prodMkLeft_apply]
  rw [integral_prod]
  swap; · exact integrable_of_finiteSupport (ν.prod μ)
  simp

variable [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]

/-- The entropy of a product kernel is the sum: `Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ]`, by
`chain_rule` at `κ ×ₖ η` (`fst_prod`, `condKernel_prod_ae_eq`, `entropy_prodMkRight`). A `simp`
lemma; read by `mutualInfo_prod` (`Kernel/MutualInfo`). -/
@[simp]
lemma entropy_prod {κ : Kernel T S} {η : Kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    Hk[κ ×ₖ η, μ] = Hk[κ, μ] + Hk[η, μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty U := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ η
  rw [chain_rule (hκ.prod hη), fst_prod,
    entropy_congr (condKernel_prod_ae_eq _ _), entropy_prodMkRight hκ]

/-- Data-processing inequality for the kernel entropy. -/
lemma entropy_map_le
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    (f : S → U) [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[map κ f, μ] ≤ Hk[κ, μ] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  have : Hk[κ, μ] = Hk[map κ (fun x ↦ (x, f x)), μ] := by
    refine (entropy_map_of_injective κ μ (f := fun x ↦ (x, f x)) ?_ (by fun_prop)).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule' hκ.map]
  simp_rw [snd_map_prod κ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _

/-- Kernels that are images of each other (`η = map κ f`, `κ = map η g`) have equal entropy:
`entropy_map_le` both ways. No consumer at 884bd7d7. -/
lemma entropy_of_map_eq_of_map {κ : Kernel T S} {η : Kernel T U}
    [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] (f : S → U) (g : U → S)
    (h1 : η = map κ f) (h2 : κ = map η g)
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    Hk[κ, μ] = Hk[η, μ] := by
  refine le_antisymm ?_ ?_
  · rw [h2]; exact entropy_map_le g hη
  · rw [h1]; exact entropy_map_le f hκ

/-- `Hk[snd κ, μ] ≤ Hk[κ, μ]`: `entropy_map_le` at `Prod.snd` (`snd_eq`). No consumer at
884bd7d7. -/
lemma entropy_snd_le {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] ≤ Hk[κ, μ] := by
  rw [snd_eq]
  exact entropy_map_le _ hκ

/-- `Hk[fst κ, μ] ≤ Hk[κ, μ]`: `entropy_map_le` at `Prod.fst` (`fst_eq`). No consumer at
884bd7d7. -/
lemma entropy_fst_le (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    Hk[fst κ, μ] ≤ Hk[κ, μ] := by
  rw [fst_eq]
  exact entropy_map_le _ hκ

end ProbabilityTheory.Kernel
