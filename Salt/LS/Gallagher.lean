/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Defs

/-!
# Large sieve track, node L4.1: the Sobolev/Gallagher pointwise lemma

Blueprint: `docs/blueprints/largesieve.md`.

**L4.1** (`gallagher_pointwise`): for `f : ℝ → ℂ` with a continuous derivative
and `0 < δ`, the pointwise Sobolev bound
`‖f t₀‖² ≤ δ⁻¹ · ∫_I ‖f‖² + 2 · ∫_I ‖f‖·‖f'‖`,
where `I = [t₀ − δ/2, t₀ + δ/2]`. The constant `2` is frozen (doctrine: a
constant-factor bound is all the large sieve consumes).

Hypothesis-form choice (per blueprint latitude): `ContDiff ℝ 1 f` **globally**,
rather than the interval-local `HasDerivAt` hypotheses. Doctrine ratifies this
because the W2 consumer (`expSum`) is entire, so a global `C¹` hypothesis costs
nothing downstream and keeps this proof free of `…WithinAt` bookkeeping.

Proof: with `g s = ‖f s‖²`, `HasDerivAt.norm_sq` gives `g' s = 2⟪f s, f' s⟫`
and Cauchy–Schwarz gives `|g' s| ≤ 2‖f s‖‖f' s‖`. FTC-2 turns `g t₀ − g u` into
`∫_u^{t₀} g'`, which is `≤ ∫_I 2‖f‖‖f'‖` for every `u ∈ I` (bound the interval
integral by the norm integral over `Ι u t₀ ⊆ I`). Integrating
`g t₀ ≤ g u + ∫_I 2‖f‖‖f'‖` over `u ∈ I` (length `δ`) and dividing by `δ` closes it.
-/

namespace Salt.LS

open MeasureTheory intervalIntegral Set

/-- **L4.1 — Gallagher pointwise lemma (FROZEN).** For a globally `C¹` function
`f : ℝ → ℂ` and `0 < δ`, writing `I = [t₀ − δ/2, t₀ + δ/2]`,
`‖f t₀‖² ≤ δ⁻¹ · ∫_I ‖f‖² + 2 · ∫_I ‖f‖·‖f'‖`. -/
theorem gallagher_pointwise {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {δ : ℝ} (hδ : 0 < δ)
    (t₀ : ℝ) :
    ‖f t₀‖ ^ 2
      ≤ δ⁻¹ * (∫ t in (t₀ - δ / 2)..(t₀ + δ / 2), ‖f t‖ ^ 2)
        + 2 * ∫ t in (t₀ - δ / 2)..(t₀ + δ / 2), ‖f t‖ * ‖deriv f t‖ := by
  set c := t₀ - δ / 2 with hc_def
  set d := t₀ + δ / 2 with hd_def
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hcd : c ≤ d := by rw [hc_def, hd_def]; linarith
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcont_f : Continuous f := hf.continuous
  have hcont_df : Continuous (deriv f) := hf.continuous_deriv_one
  -- derivative of `‖f ·‖²` and continuity of the two integrands
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun t => ‖f t‖ ^ 2) (2 * inner ℝ (f s) (deriv f s)) s :=
    fun s => (hdiff s).hasDerivAt.norm_sq
  have hcont_g : Continuous (fun s : ℝ => 2 * inner ℝ (f s) (deriv f s)) := by fun_prop
  have hcont_k : Continuous (fun s : ℝ => 2 * (‖f s‖ * ‖deriv f s‖)) := by fun_prop
  -- Cauchy–Schwarz: `‖g' s‖ ≤ 2‖f s‖‖f' s‖`.
  have hCS : ∀ s : ℝ, ‖2 * inner ℝ (f s) (deriv f s)‖ ≤ 2 * (‖f s‖ * ‖deriv f s‖) := by
    intro s
    rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have := abs_real_inner_le_norm (f s) (deriv f s)
    linarith
  set K := ∫ s in c..d, 2 * (‖f s‖ * ‖deriv f s‖) with hK_def
  -- The core one-sided bound for each `u ∈ I`.
  have core : ∀ u ∈ Icc c d, ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 ≤ K := by
    intro u hu
    have ht₀ : t₀ ∈ Icc c d := ⟨by rw [hc_def]; linarith, by rw [hd_def]; linarith⟩
    have hFTC : (∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s)) = ‖f t₀‖ ^ 2 - ‖f u‖ ^ 2 :=
      integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont_g.intervalIntegrable u t₀)
    have hsub : Set.uIoc u t₀ ⊆ Icc c d :=
      Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc (le_inf hu.1 ht₀.1) (sup_le hu.2 ht₀.2))
    rw [← hFTC]
    calc (∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s))
        ≤ ‖∫ s in u..t₀, 2 * inner ℝ (f s) (deriv f s)‖ := Real.le_norm_self _
      _ ≤ ∫ s in Set.uIoc u t₀, ‖2 * inner ℝ (f s) (deriv f s)‖ :=
          norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Set.uIoc u t₀, 2 * (‖f s‖ * ‖deriv f s‖) :=
          setIntegral_mono_on hcont_g.norm.integrableOn_uIoc hcont_k.integrableOn_uIoc
            measurableSet_uIoc (fun s _ => hCS s)
      _ ≤ ∫ s in Icc c d, 2 * (‖f s‖ * ‖deriv f s‖) :=
          setIntegral_mono_set hcont_k.integrableOn_Icc
            (Filter.Eventually.of_forall (fun s => by positivity)) hsub.eventuallyLE
      _ = K := by
          rw [hK_def, MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hcd]
  -- Integrate `‖f t₀‖² ≤ ‖f u‖² + K` over `u ∈ I` (length `δ`).
  have hintegrated : δ * ‖f t₀‖ ^ 2 ≤ (∫ u in c..d, ‖f u‖ ^ 2) + δ * K := by
    have hii : IntervalIntegrable (fun u => ‖f u‖ ^ 2) volume c d :=
      (hcont_f.norm.pow 2).intervalIntegrable c d
    have hle : (∫ _u in c..d, ‖f t₀‖ ^ 2) ≤ ∫ u in c..d, (‖f u‖ ^ 2 + K) :=
      intervalIntegral.integral_mono_on hcd intervalIntegral.intervalIntegrable_const
        (hii.add intervalIntegral.intervalIntegrable_const)
        (fun u hu => by have := core u hu; linarith)
    rw [intervalIntegral.integral_add hii intervalIntegral.intervalIntegrable_const] at hle
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hle
    rw [show d - c = δ from by rw [hc_def, hd_def]; ring] at hle
    exact hle
  -- `K = 2 · ∫_I ‖f‖·‖f'‖`, then divide the integrated bound by `δ`.
  have hK : K = 2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖ := by
    rw [hK_def, intervalIntegral.integral_const_mul]
  rw [hK] at hintegrated
  have hinv : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have key2 : ‖f t₀‖ ^ 2 ≤ δ⁻¹ * (δ * ‖f t₀‖ ^ 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
  refine key2.trans ?_
  calc δ⁻¹ * (δ * ‖f t₀‖ ^ 2)
      ≤ δ⁻¹ * ((∫ u in c..d, ‖f u‖ ^ 2) + δ * (2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖)) :=
        mul_le_mul_of_nonneg_left hintegrated (le_of_lt hinv)
    _ = δ⁻¹ * (∫ t in c..d, ‖f t‖ ^ 2) + 2 * ∫ t in c..d, ‖f t‖ * ‖deriv f t‖ := by
        rw [mul_add]
        congr 1
        rw [← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]

end Salt.LS
