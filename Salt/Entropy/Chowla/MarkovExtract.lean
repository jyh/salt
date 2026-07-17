/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Markov extraction (Tao 1509.05422, the (3.12) → (3.13) step)

From an upper bound `I[Y : X ; μ] ≤ κ` on the mutual information, extract that the
set of conditioning values `x` at which the per-`x` entropy defect
`H[Y; μ] − Hm[condDistrib Y X μ x]` exceeds a threshold `t` has small measure
under `μ.map X`.  This is the random-variable-level form of Tao's step that turns
the entropy-decrement headline (3.12) into the weak-uniformity input (3.13) that
Lemma 3.2 consumes.

## The honest correction term

Tao (p. 20) writes the decomposition
`Σ_x P(X = x)·(H(Y) − H(Y | X = x)) = I(X, Y)` and asserts "by (3.3), the summands
are non-negative", then applies Markov.  This is an abuse: the *average* defect is
`I ≥ 0` (that is what (3.3), `condEntropy_le_entropy`, gives), but the **per-`x`
defect can be negative** — conditioning on an individual `x` can raise the entropy
of `Y`.  (Concretely: `X, Y` binary with `Y | X=0 ≡ 0` and `Y | X=1` uniform makes
`H(Y) − H(Y | X=1) < 0`.)  So a clean Markov on the raw defect is unavailable.

The honest fix used here rescues Tao's argument by his own (3.9): let
`s x := L − Hm[condDistrib Y X μ x]` where `L` is any ceiling with
`Hm[condDistrib Y X μ x] ≤ L` (e.g. `L = log |β|`, via `measureEntropy_le_log_card`).
Then `s ≥ 0` *pointwise* (entropy ≤ log-card), `∫ s d(μ.map X) = L − H[Y | X] =
(L − H[Y]) + I[Y : X]`, and `{x | t < H[Y] − Hm[…]} ⊆ {x | t < s x}` (using
`H[Y] ≤ L`).  Markov on the genuinely-nonneg `s` then yields the bound with the
correction term `L − H[Y; μ]`, the **entropy deficiency of `Y`**.  In the spine
this deficiency is `o(1)` by (3.9) (`Y = residueWindow` is near-uniform), so the
bound degrades to Tao's `κ / t` in the limit — but it is stated here honestly and
unconditionally, with the deficiency exposed for the (3.9) consumer.

## For the consumer (W1-c, Lemma 3.2)

`decrement_markov` bounds exactly the "bad" set `{x | t < H[Y] − Hm[…]}` that
Lemma 3.2 excludes (a good `x` has defect `≤ t`; Lemma 3.2's proof uses the *upper*
bound `H(Y | X = x) ≥ H(Y) − t` on the good side, i.e. the defect `≤ t` direction).
The correction term is supplied to the consumer as the `(3.9)` deficiency
`log |β| − H[Y]`.  The KL-divergence decomposition (`I = 𝔼_x KL(P_{Y|x} ‖ P_Y)`,
with genuinely-nonneg summands) is the textbook alternative, but mathlib's `klDiv`
is `ℝ≥0∞`-valued/irreducible with no mutual-info identity, and bridging KL back to
the entropy-defect form Lemma 3.2 wants needs the *same* near-uniformity input — so
the surrogate-entropy route above is both cheaper and equally honest.
-/
import Salt.Entropy.Chowla.Decrement
import Salt.Entropy.Basic
import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace Salt.Entropy.Chowla

section Markov

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Real-valued Markov, division form: for a `ν`-a.e.-nonnegative integrable `f` on a
finite measure with `∫ f ≤ c` and `t > 0`, the super-level set `{t < f}` has
`ν`-measure at most `c / t`.  (mathlib ships only the multiplicative
`mul_meas_ge_le_integral_of_nonneg`; this packages the division and the strict-`<`
super-level set.) -/
lemma measureReal_gt_le_integral_div {ν : Measure Ω'} [IsFiniteMeasure ν]
    {f : Ω' → ℝ} (hf0 : 0 ≤ᵐ[ν] f) (hf : Integrable f ν) {c t : ℝ} (ht : 0 < t)
    (hc : ∫ x, f x ∂ν ≤ c) :
    ν.real {x | t < f x} ≤ c / t := by
  have hmono : ν.real {x | t < f x} ≤ ν.real {x | t ≤ f x} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact le_of_lt hx
  rw [le_div_iff₀ ht]
  calc ν.real {x | t < f x} * t
      = t * ν.real {x | t < f x} := mul_comm _ _
    _ ≤ t * ν.real {x | t ≤ f x} := mul_le_mul_of_nonneg_left hmono ht.le
    _ ≤ ∫ x, f x ∂ν := mul_meas_ge_le_integral_of_nonneg hf0 hf t
    _ ≤ c := hc

end Markov

variable {Ω α β : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] [Nonempty β]
  {X : Ω → α} {Y : Ω → β} {μ : Measure Ω}

/-- **The mutual-information / entropy-defect decomposition.**  The mutual
information is the `(μ.map X)`-average of the per-`x` entropy defect
`H[Y; μ] − Hm[condDistrib Y X μ x]`.  (This is Tao's `I = Σ_x P(X=x)·defect`; the
per-`x` defect is *not* pointwise nonneg — see the module docstring.) -/
theorem mutualInfo_eq_integral_condDistrib_defect
    (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] :
    I[Y : X ; μ] = ∫ x, (H[Y; μ] - Hm[condDistrib Y X μ x]) ∂(μ.map X) := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hg : Integrable (fun x => Hm[condDistrib Y X μ x]) (μ.map X) :=
    integrable_of_finiteSupport (μ.map X)
  have hcond : ∫ x, Hm[condDistrib Y X μ x] ∂(μ.map X) = H[Y | X ; μ] :=
    (condEntropy_eq_kernel_entropy hY hX μ).symm
  have key : ∫ x, (H[Y; μ] - Hm[condDistrib Y X μ x]) ∂(μ.map X)
      = H[Y; μ] - ∫ x, Hm[condDistrib Y X μ x] ∂(μ.map X) := by
    rw [integral_sub (integrable_const _) hg]
    simp only [integral_const, probReal_univ, one_smul]
  rw [key, hcond, mutualInfo_eq_entropy_sub_condEntropy hY hX μ]

/-- **The Markov extraction (Tao (3.12) → (3.13), honest form).**  Given a ceiling
`L` on the conditional entropies (`Hm[condDistrib Y X μ x] ≤ L` for all `x`, and
`H[Y; μ] ≤ L`) and `I[Y : X ; μ] ≤ κ`, the set of `x` at which the entropy defect
exceeds `t` has `(μ.map X)`-measure at most `(κ + (L − H[Y; μ])) / t`.  The extra
`L − H[Y; μ]` is the entropy deficiency of `Y` (Tao (3.9)); it is `o(1)` in the
spine and vanishes when `Y` is uniform, recovering Tao's `κ / t`. -/
theorem decrement_markov
    (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] {L κ t : ℝ} (ht : 0 < t)
    (hgL : ∀ x, Hm[condDistrib Y X μ x] ≤ L) (hYL : H[Y; μ] ≤ L)
    (hI : I[Y : X ; μ] ≤ κ) :
    (μ.map X).real {x | t < H[Y; μ] - Hm[condDistrib Y X μ x]}
      ≤ (κ + (L - H[Y; μ])) / t := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hg : Integrable (fun x => Hm[condDistrib Y X μ x]) (μ.map X) :=
    integrable_of_finiteSupport (μ.map X)
  have hs0 : 0 ≤ᵐ[μ.map X] fun x => L - Hm[condDistrib Y X μ x] :=
    Filter.Eventually.of_forall (fun x => sub_nonneg.mpr (hgL x))
  have hs_int : Integrable (fun x => L - Hm[condDistrib Y X μ x]) (μ.map X) :=
    (integrable_const L).sub hg
  have hint : ∫ x, (L - Hm[condDistrib Y X μ x]) ∂(μ.map X) ≤ κ + (L - H[Y; μ]) := by
    rw [integral_sub (integrable_const L) hg]
    simp only [integral_const, probReal_univ, one_smul]
    have hcond : ∫ x, Hm[condDistrib Y X μ x] ∂(μ.map X) = H[Y | X ; μ] :=
      (condEntropy_eq_kernel_entropy hY hX μ).symm
    have hmi : H[Y | X ; μ] = H[Y; μ] - I[Y : X ; μ] := by
      rw [mutualInfo_eq_entropy_sub_condEntropy hY hX μ]; ring
    rw [hcond, hmi]; linarith [hI]
  have hsub : {x | t < H[Y; μ] - Hm[condDistrib Y X μ x]}
      ⊆ {x | t < L - Hm[condDistrib Y X μ x]} := by
    intro x hx
    have hD : 0 ≤ L - H[Y; μ] := sub_nonneg.mpr hYL
    simp only [Set.mem_setOf_eq] at hx ⊢
    linarith
  calc (μ.map X).real {x | t < H[Y; μ] - Hm[condDistrib Y X μ x]}
      ≤ (μ.map X).real {x | t < L - Hm[condDistrib Y X μ x]} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (κ + (L - H[Y; μ])) / t :=
        measureReal_gt_le_integral_div hs0 hs_int ht hint

/-- **Fintype specialization.**  When `β` is a `Fintype`, `L = log |β|` is a valid
ceiling (`measureEntropy_le_log_card`, `entropy_le_log_card`), so the correction
term is the concrete deficiency `log |β| − H[Y; μ]`.  This is the form the
residue-window consumer (`Y = residueWindow`, `β = ZMod (PH ε H)`) instantiates. -/
theorem decrement_markov_fintype [Fintype β]
    (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] {κ t : ℝ} (ht : 0 < t)
    (hI : I[Y : X ; μ] ≤ κ) :
    (μ.map X).real {x | t < H[Y; μ] - Hm[condDistrib Y X μ x]}
      ≤ (κ + (Real.log (Fintype.card β) - H[Y; μ])) / t :=
  decrement_markov hX hY ht (fun _ => measureEntropy_le_log_card _)
    (entropy_le_log_card Y μ) hI

end Salt.Entropy.Chowla
