/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Entropy.Chowla.PrimeWindow

/-!
# CRT independence and Hoeffding concentration (Tao Lemma 3.3 substrate)

This file supplies the concentration substrate for Tao arXiv:1509.05422v1 Lemma 3.3.  Its
heart is the **Chinese-remainder independence** of the residue reductions: under
the uniform probability measure on `ZMod P_H` (`P_H` the product of the window
primes, from `PrimeWindow.lean`), the family of natural reductions
`residueProj p : ZMod P_H → ZMod p` (`y ↦ (y : ZMod p)`), indexed by `p ∈ 𝒫_H`,
is `iIndepFun`.

## Contents

* `residueProj` — the natural reduction `ZMod P_H →+* ZMod p` (`ZMod.castHom`).
* `crtEquiv` — the packaged CRT ring iso `ZMod P_H ≃+* ∏ p, ZMod p`
  (`ZMod.prodEquivPi`, with the window primes pairwise coprime and their product
  `= P_H`).  `crtEquiv_apply_eq` identifies its `p`-coordinate with `residueProj`
  via ring-hom uniqueness (`ZMod.subsingleton_ringHom`).
* `iIndepFun_residueProj` — **THE CRT INDEPENDENCE** (PB-floor 1).  Route: the
  pushforward of the uniform measure along `crtEquiv` is the product measure
  `Measure.pi (uniform)` (a per-singleton `card`-count), whose coordinates are
  independent (`iIndepFun_pi`); transported back through
  `iIndepFun_iff_map_fun_eq_pi_map`.
* `hoeffding_two_sided` — **generic two-sided Hoeffding** for a sum of independent
  bounded random variables (`hasSubgaussianMGF_of_mem_Icc` +
  `measure_sum_ge_le_of_iIndepFun`, both tails + a union bound).
* `hoeffding_of_indep` — the ZMod wrapper (PB-floor 2, independence hypothesized):
  bounded `G p` composed with independent projections concentrate.
* `hoeffding_residueProj` — the unconditional export for W2-b: `hoeffding_of_indep`
  fed the CRT independence, over the model uniform measure on `ZMod P_H`.

The specific `F_p` of Tao (3.14) — the choice of `G_p` and its `[lo, hi]` box —
belongs to the downstream node (W2-b); everything here is generic in `G`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

variable (eps : ℚ) (H : ℕ)

/-- `∏ pᵢ⁻¹ = (∏ pᵢ)⁻¹` in `ℝ≥0∞` for finite nonzero, non-`∞` factors. -/
private lemma enn_prod_inv {ι : Type*} (t : Finset ι) (g : ι → ℝ≥0∞)
    (h : ∀ i ∈ t, g i ≠ 0) (h' : ∀ i ∈ t, g i ≠ ⊤) :
    ∏ i ∈ t, (g i)⁻¹ = (∏ i ∈ t, g i)⁻¹ := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    rw [ENNReal.mul_inv (Or.inl (h a (Finset.mem_insert_self a t)))
          (Or.inl (h' a (Finset.mem_insert_self a t))),
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
          (fun i hi => h' i (Finset.mem_insert_of_mem hi))]

/-- Each window prime divides `P_H`. -/
lemma dvd_PH (i : primeWindow eps H) : (i : ℕ) ∣ PH eps H :=
  Finset.dvd_prod_of_mem (fun p => p) i.2

/-- The natural reduction `ZMod P_H → ZMod p` (i.e. `y ↦ (y : ZMod p)`). -/
noncomputable def residueProj (i : primeWindow eps H) :
    ZMod (PH eps H) →+* ZMod (i : ℕ) :=
  ZMod.castHom (dvd_PH eps H i) (ZMod (i : ℕ))

/-- The window primes are pairwise coprime (distinct primes). -/
lemma pairwise_coprime_window :
    Pairwise (fun i j : primeWindow eps H => Nat.Coprime (i : ℕ) (j : ℕ)) := by
  intro i j hij
  exact (Nat.coprime_primes (prime_of_mem_primeWindow i.2) (prime_of_mem_primeWindow j.2)).mpr
    (Subtype.coe_ne_coe.mpr hij)

/-- `P_H` is the product of the window primes indexed by the subtype. -/
lemma PH_eq_prod : PH eps H = ∏ i : primeWindow eps H, (i : ℕ) := by
  rw [PH]; exact (Finset.prod_coe_sort _ _).symm

/-- The CRT ring isomorphism `ZMod P_H ≃+* ∏ p, ZMod p` over the window. -/
noncomputable def crtEquiv :
    ZMod (PH eps H) ≃+* ∀ i : primeWindow eps H, ZMod (i : ℕ) :=
  (ZMod.ringEquivCongr (PH_eq_prod eps H)).trans
    (ZMod.prodEquivPi _ (pairwise_coprime_window eps H))

/-- The `p`-coordinate of the CRT iso *is* the natural reduction `residueProj p`
(both are ring homs `ZMod P_H →+* ZMod p`, and such a hom is unique). -/
lemma crtEquiv_apply_eq (i : primeWindow eps H) (y : ZMod (PH eps H)) :
    crtEquiv eps H y i = residueProj eps H i y := by
  have h := RingHom.congr_fun
    (Subsingleton.elim ((Pi.evalRingHom (fun i : primeWindow eps H => ZMod (i : ℕ)) i).comp
      (crtEquiv eps H : ZMod (PH eps H) →+* _)) (residueProj eps H i)) y
  simpa using h

/-- **The CRT independence** (PB-floor 1).  Under the uniform probability measure on
`ZMod P_H`, the family of natural reductions `residueProj p : ZMod P_H → ZMod p`
(`p ∈ 𝒫_H`) is independent.  This is the heart of Tao's Lemma 3.3. -/
lemma iIndepFun_residueProj :
    iIndepFun (fun (i : primeWindow eps H) (y : ZMod (PH eps H)) => residueProj eps H i y)
      (uniformOn (Set.univ : Set (ZMod (PH eps H)))) := by
  classical
  set μ := uniformOn (Set.univ : Set (ZMod (PH eps H))) with hμ
  set ν : (i : primeWindow eps H) → Measure (ZMod (i : ℕ)) :=
    fun i => uniformOn (Set.univ : Set (ZMod (i : ℕ))) with hν
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  haveI : ∀ i : primeWindow eps H, NeZero (i : ℕ) :=
    fun i => ⟨(prime_of_mem_primeWindow i.2).pos.ne'⟩
  haveI : ∀ i : primeWindow eps H, IsProbabilityMeasure (ν i) :=
    fun i => isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have hfun : (fun (i : primeWindow eps H) (y : ZMod (PH eps H)) => residueProj eps H i y)
            = (fun i y => crtEquiv eps H y i) := by
    funext i y; exact (crtEquiv_apply_eq eps H i y).symm
  rw [hfun]
  have hf : ∀ i, AEMeasurable (fun y => crtEquiv eps H y i) μ :=
    fun i => (measurable_of_countable _).aemeasurable
  have hmap : μ.map (⇑(crtEquiv eps H)) = Measure.pi ν := by
    refine Measure.ext_of_singleton (fun x => ?_)
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
    have hpre : (⇑(crtEquiv eps H)) ⁻¹' {x} = {(crtEquiv eps H).symm x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    rw [hpre, Measure.pi_singleton]
    have hμz : μ {(crtEquiv eps H).symm x} = (PH eps H : ℝ≥0∞)⁻¹ := by
      rw [hμ, uniformOn_univ, Measure.count_singleton, ZMod.card]; simp
    have hνz : ∀ i, ν i {x i} = ((i : ℕ) : ℝ≥0∞)⁻¹ := by
      intro i; rw [hν, uniformOn_univ, Measure.count_singleton, ZMod.card]; simp
    rw [hμz]
    simp_rw [hνz]
    rw [enn_prod_inv _ _ (fun i _ => by exact_mod_cast (prime_of_mem_primeWindow i.2).pos.ne')
          (fun i _ => by simp)]
    congr 1
    rw [PH_eq_prod]; push_cast; rfl
  have hb : ∀ i, μ.map (fun y => crtEquiv eps H y i) = ν i := by
    intro i
    have h1 : (fun y => crtEquiv eps H y i)
            = (Function.eval i) ∘ (⇑(crtEquiv eps H)) := rfl
    rw [h1, ← Measure.map_map (measurable_pi_apply i) (measurable_of_countable _), hmap,
      Measure.pi_map_eval]
    simp
  rw [iIndepFun_iff_map_fun_eq_pi_map hf]
  rw [show (fun i => μ.map (fun y => crtEquiv eps H y i)) = ν from funext hb]
  exact hmap

/-- **Generic two-sided Hoeffding.**  For a family `X` of independent random
variables with `X i` a.e. in `[lo i, hi i]`, the sum `∑ X i` concentrates around
its mean `∑ μ[X i]` with sub-Gaussian tails. -/
theorem hoeffding_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} {lo hi : ι → ℝ}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (lo i) (hi i)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, μ[X i]|}
      ≤ 2 * Real.exp (-ε ^ 2 /
          (2 * ((∑ i ∈ s, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  set c : ι → ℝ≥0 := fun i => (‖hi i - lo i‖₊ / 2) ^ 2 with hc
  set m : ι → ℝ := fun i => μ[X i] with hm
  have hYsub : ∀ i, HasSubgaussianMGF (fun ω => X i ω - m i) (c i) μ :=
    fun i => hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bdd i)
  have hYindep : iIndepFun (fun i ω => X i ω - m i) μ :=
    h_indep.comp (fun i t => t - m i) (fun i => by fun_prop)
  have hNYindep : iIndepFun (fun i ω => -(X i ω - m i)) μ :=
    hYindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hUp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s) hYindep
    (fun i _ => hYsub i) hε
  have hLo := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := s) hNYindep
    (fun i _ => (hYsub i).neg) hε
  have hset : {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, m i|}
      = {ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        ∪ {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    constructor
    · intro h
      rcases abs_choice ((∑ i ∈ s, X i ω) - ∑ i ∈ s, m i) with hch | hch
      · exact Or.inl (hch ▸ h)
      · exact Or.inr (hch ▸ h)
    · rintro (h | h)
      · exact le_trans h (le_abs_self _)
      · exact le_trans h (neg_le_abs _)
  rw [hset]
  calc
    μ.real ({ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        ∪ {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)})
      ≤ μ.real {ω | ε ≤ ∑ i ∈ s, (X i ω - m i)}
        + μ.real {ω | ε ≤ ∑ i ∈ s, -(X i ω - m i)} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ)))
        + Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ))) := add_le_add hUp hLo
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ))) := by ring

/-- **Hoeffding for CRT-factoring functions** (independence hypothesized: PB-floor 2).
Each summand `G i ∘ proj i` depends on `ω` only through the `i`-coordinate `proj i ω`;
given the projections are independent, the sum `∑ G i (proj i ω)` concentrates. -/
theorem hoeffding_of_indep {μ : Measure (ZMod (PH eps H))} [IsProbabilityMeasure μ]
    (proj : (i : primeWindow eps H) → ZMod (PH eps H) → ZMod (i : ℕ))
    (h_indep : iIndepFun proj μ) (G : (i : primeWindow eps H) → ZMod (i : ℕ) → ℝ)
    {lo hi : primeWindow eps H → ℝ} (h_bdd : ∀ i x, G i x ∈ Set.Icc (lo i) (hi i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i, G i (proj i ω)) - ∑ i, μ[fun ω => G i (proj i ω)]|}
      ≤ 2 * Real.exp (-ε ^ 2 /
          (2 * ((∑ i, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  haveI : ∀ i : primeWindow eps H, NeZero (i : ℕ) :=
    fun i => ⟨(prime_of_mem_primeWindow i.2).pos.ne'⟩
  exact hoeffding_two_sided (h_indep.comp G (fun _ => measurable_of_countable _))
    (s := Finset.univ) (fun _ => (measurable_of_countable _).aemeasurable)
    (fun i => ae_of_all _ (fun ω => h_bdd i (proj i ω))) hε

/-- **Hoeffding for the residue reductions under the uniform measure** (PB-floor 1 ∘ 2,
unconditional).  The direct export for Tao's Lemma 3.3: with `G i` bounded, the sum
`∑ G i (n mod p)` over the model uniform measure on `ZMod P_H` concentrates. -/
theorem hoeffding_residueProj (G : (i : primeWindow eps H) → ZMod (i : ℕ) → ℝ)
    {lo hi : primeWindow eps H → ℝ} (h_bdd : ∀ i x, G i x ∈ Set.Icc (lo i) (hi i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | ε ≤ |(∑ i, G i (residueProj eps H i ω)) - ∑ i,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              G i (residueProj eps H i ω)]|}
      ≤ 2 * Real.exp
          (-ε ^ 2 / (2 * ((∑ i, (‖hi i - lo i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  haveI : IsProbabilityMeasure (uniformOn (Set.univ : Set (ZMod (PH eps H)))) :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  exact hoeffding_of_indep eps H (fun i y => residueProj eps H i y)
    (iIndepFun_residueProj eps H) G h_bdd hε

end Salt.Entropy.Chowla
