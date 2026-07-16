/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/ForMathlib/Entropy/Basic.lean`, at commit
a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`; the `public import`s of
  `PFR.ForMathlib.ConditionalIndependence`,
  `PFR.ForMathlib.Entropy.Kernel.MutualInfo`, `PFR.ForMathlib.Uniform`, and
  `PFR.Mathlib.Probability.ConditionalProbability`; and `@[expose] public
  section`) to a plain `import Mathlib` plus imports of the Salt ports
  `Salt.Entropy.Kernel.MutualInfo` and `Salt.Entropy.Mathlib.ConditionalProbability`.
- FROZEN-SUBSET port (gate amendment A1). The upstream imports
  `PFR.ForMathlib.ConditionalIndependence` and `PFR.ForMathlib.Uniform` are
  DROPPED (unreachable from the frozen entropy API). This file ports the
  frozen-API subset of upstream `Basic.lean`: the four defs (`entropy`,
  `condEntropy`, `mutualInfo`, `condMutualInfo`) with their notations, the named
  frozen lemmas, and their transitive helper closure. The section/`variable`
  skeleton is reproduced verbatim so every ported lemma sees its original
  instance context; unported (reachable but out-of-subset) lemmas are omitted.
  Declarations that consume the dropped imports are skipped — see the
  FROZEN-SUBSET note below.
- All ported declarations, names, notation, and proof bodies are verbatim from
  upstream; drift v4.33-rc1 → v4.32.0-rc1 required no statement or proof
  changes, and this file has no measure-finite-support `.support` projections,
  so the `Measure.finSupport` rename does not apply.
-/
import Mathlib
import Salt.Entropy.Kernel.MutualInfo
import Salt.Entropy.Mathlib.ConditionalProbability

/- FROZEN-SUBSET: skipped upstream declarations that consume the dropped imports
   (`PFR.ForMathlib.Uniform` / `PFR.ForMathlib.ConditionalIndependence`) and are
   therefore unreachable here:
   - `IsUniform.entropy_eq`, `IsUniform.entropy_eq'`  (Uniform: `IsUniform` + its API)
   - `iIndepFun.entropy_eq_add`  (Uniform residue: `finsets_comp'`, `iIndepFun.finsets_comp`)
   - `condMutualInfo_eq_zero`, `ent_of_cond_indep`
       (ConditionalIndependence: `CondIndepFun`, `condIndepFun_iff`)
   - `condEntropy_prod_eq_of_indepFun`
       (ConditionalIndependence: `IndepFun.identDistrib_cond`)
   All other upstream lemmas outside the frozen subset (the independence /
   data-processing API, the `_eq_sum` expansions, `IdentDistrib` congruences,
   etc.) are reachable but simply not part of this port. -/

/-!
# Entropy and conditional entropy

## Main definitions

* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInfo`: mutual information of two random variables

## Main statements

* `chain_rule`: $H[⟨X, Y⟩] = H[Y] + H[X | Y]$
* `entropy_cond_le_entropy`: $H[X | Y] ≤ H[X]$. (Chain rule another way.)
* `entropy_triple_add_entropy_le` (Submodularity of entropy.) :
  $H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]$.

## Notations

* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[|Y ← y]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInfo X Y`

All notations have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" => entropy X (μ[|Y ← y])
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])

/-- Entropy of a random variable agrees with entropy of its distribution. -/
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

/-- Entropy of a random variable is also the kernel entropy of the distribution over a Dirac mass.
-/
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    H[X ; μ] = Hk[Kernel.const Unit (μ.map X), Measure.dirac ()] := by simp [entropy]

/-- Any variable on a zero measure space has zero entropy. -/
@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by simp [entropy]

/-- Entropy is always non-negative. -/
lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

/-- Entropy is at most the logarithm of the cardinality of the range. -/
lemma entropy_le_log_card [Fintype S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) : H[X ; μ] ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

/-- If `X`, `Y` are `S`-valued and `T`-valued random variables, and `Y = f(X)` for
some injection `f : S \to T`, then `H[Y] = H[X]`.
One can also use `entropy_of_comp_eq_of_comp` as an alternative if verifying injectivity is fiddly.
For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := .of_discrete
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]

variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]

variable [Countable T]

/-- `H[X, Y] = H[Y, X]`. -/
lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[(fun ω ↦ (X ω, Y ω)); μ] = H[(fun ω ↦ (Y ω, X ω)) ; μ] := by
  change H[Prod.swap ∘ (fun ω ↦ (Y ω, X ω)) ; μ] = H[(fun ω ↦ (Y ω, X ω)) ; μ]
  exact entropy_comp_of_injective μ (hY.prodMk hX) Prod.swap Prod.swap_injective

end entropy

section condEntropy

variable [MeasurableSpace T]

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]

lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]] := rfl

@[inherit_doc condEntropy] notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume

section

variable [MeasurableSingletonClass T]

/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    H[X | Y ; μ] = Hk[condDistrib X Y μ, μ.map Y] := by
  rw [condEntropy_def, Kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  rw [Measure.map_apply hY (.singleton _)] at ht
  simp only [entropy_def]
  congr
  ext s hs
  rw [condDistrib_apply' hX hY _ _ ht hs, Measure.map_apply hX hs,
      cond_apply (hY (.singleton _))]

variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]

lemma condEntropy_two_eq_kernel_entropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z] :
    H[X | (fun ω ↦ (Y ω, Z ω)) ; μ] =
      Hk[Kernel.condKernel (condDistrib (fun a ↦ (Y a, X a)) Z μ),
        Measure.map Z μ ⊗ₘ Kernel.fst (condDistrib (fun a ↦ (Y a, X a)) Z μ)] := by
  rw [Measure.compProd_congr (condDistrib_fst_ae_eq hY hX hZ μ),
      map_compProd_condDistrib hY hZ,
      Kernel.entropy_congr (condKernel_condDistrib_ae_eq hY hX hZ μ),
      ← Kernel.entropy_congr (swap_condDistrib_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prodMk hZ), Kernel.entropy_comap_swap]

end

/-- Any random variable on a zero measure space has zero conditional entropy. -/
@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : H[X | Y ; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]

/-- Conditional entropy is non-negative. -/
lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

end condEntropy

section pair

variable [MeasurableSpace T]
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

/-- One form of the chain rule : `H[X, Y] = H[X] + H[Y | X]`. -/
lemma chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[(fun ω ↦ (X ω, Y ω)) ; μ] = H[X ; μ] + H[Y | X ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [entropy_eq_kernel_entropy, Kernel.chain_rule]
  · simp_rw [← Kernel.map_const _ (hX.prodMk hY), Kernel.fst_map_prod _ hY, Kernel.map_const _ hX,
      Kernel.map_const _ (hX.prodMk hY)]
    congr 1
    · rw [Kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ Kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prodMk_left hX]
        congr
      rw [this, Kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
        ext s _
        rw [Measure.map_map measurable_prodMk_left hX]
        rfl
      rw [this, Kernel.entropy_prodMkLeft_unit]
  · apply Kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact Kernel.finiteKernelSupport_of_const _

/-- Another form of the chain rule : `H[X, Y] = H[Y] + H[X | Y]`. -/
lemma chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[(fun ω ↦ (X ω, Y ω)) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

end pair

section mutualInfo

variable [MeasurableSpace T]

/-- The mutual information `I[X : Y]` of two random variables
is defined to be `H[X] + H[Y] - H[X ; Y]`. -/
noncomputable
def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[(fun ω ↦ (X ω, Y ω)) ; μ]

@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume

lemma mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[(fun ω ↦ (X ω, Y ω)) ; μ] := rfl

/-- The conditional mutual information `I[X : Y| Z]` is the mutual information of `X| Z=z` and
`Y| Z=z`, integrated over `z`. -/
noncomputable
def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[(fun ω ↦ (X ω, Y ω)) | Z ← z ; μ]]

lemma condMutualInfo_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[(fun ω ↦ (X ω, Y ω)) | Z ← z ; μ]] := rfl

@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- Mutual information is non-negative. -/
lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y ; μ] := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map ((fun ω ↦ (X ω, Y ω)))).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map ((fun ω ↦ (X ω, Y ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : H[(fun ω ↦ (X ω, Y ω)) ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 <| mutualInfo_nonneg hX hY _

variable [Countable S] [Countable T]

/-- `I[X : Y] = H[X] - H[X|Y]`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel

end

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- Conditional information is non-nonegative. -/
lemma condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) {Z : Ω → U} {μ : Measure Ω}
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInfo_nonneg hX hY _

end

section IsProbabilityMeasure

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

variable (μ)
variable [Countable S] [Countable T]

variable [IsZeroOrProbabilityMeasure μ]

/-- `H[X] - H[X|Y] = I[X : Y]` -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

/-- `H[X | Y] ≤ H[X]`. -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 <| by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInfo_nonneg hX hY _

/-- `H[X | Y, Z] ≤ H[X | Z]`. -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X | (fun ω ↦ (Y ω, Z ω)) ; μ] ≤ H[X | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  refine (Kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  · apply Kernel.aefiniteKernelSupport_condDistrib
    all_goals fun_prop
  exact Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)

/-- The submodularity inequality: `H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]`. -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[(fun ω ↦ (X ω, (Y ω, Z ω))) ; μ] + H[Z ; μ]
      ≤ H[(fun ω ↦ (X ω, Z ω)) ; μ] + H[(fun ω ↦ (Y ω, Z ω)) ; μ] := by
  rw [chain_rule _ hX (hY.prodMk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

end IsProbabilityMeasure
end mutualInfo
end ProbabilityTheory

/-! ### Consumer test (A-R1 acceptance)

The three random-variable-level entropy anchors used by the paper — (3.1) the
chain rule, (3.5) mutual information as an entropy decrement, and (3.7) the
log-cardinality bound — as compiled `example`s over generic types. -/
section ConsumerTestRV

open ProbabilityTheory

variable {Ω S T : Type*} [MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

/-- (3.1) Chain rule at the random-variable level: `H[X, Y] = H[X] + H[Y | X]`. -/
example [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] :
    H[(fun ω ↦ (X ω, Y ω)) ; μ] = H[X ; μ] + H[Y | X ; μ] :=
  chain_rule' μ hX hY

/-- (3.5) Mutual information as an entropy decrement: `I[X : Y] = H[X] - H[X | Y]`. -/
example [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] :=
  mutualInfo_eq_entropy_sub_condEntropy hX hY μ

/-- (3.7) Entropy is bounded by log-cardinality: `H[X] ≤ log |S|`. -/
example [Fintype S] : H[X ; μ] ≤ Real.log (Fintype.card S) :=
  entropy_le_log_card X μ

end ConsumerTestRV
