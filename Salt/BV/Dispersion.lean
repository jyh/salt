/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.MaxReduction
import Salt.BV.SWChar
import Salt.BV.SWMaxY
import Salt.BV.TypeI
import Salt.BV.TypeIIClose
import Salt.LS.Conductor
import Salt.LS.PhiSum
import Salt.LS.TypeSums
import Salt.Tactic.EventuallyBudget

/-!
# V3.1 — the ψ-form BV dispersion assembly

Design: `docs/blueprints/bv.md`, node `V3.1` (6th correction: ∀-fixed-y form).
THE keystone of the `bv` rung.
-/

namespace Salt.BV

open Finset Salt.LS ArithmeticFunction
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

/-! ## The primitive-character L¹ energy -/

open Classical in
/-- `∑_{χ primitive mod f} ‖ψ(y,χ)‖` — the L¹ analogue of `Salt.LS.primEnergy`. -/
noncomputable def primEnergyL1 (y f : ℕ) : ℝ :=
  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
    ‖psiChi y χ‖

lemma primEnergyL1_nonneg (y f : ℕ) : 0 ≤ primEnergyL1 y f :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-! ## The per-modulus L¹ conductor regrouping -/

open Classical in
/-- **L¹ conductor regroup (per modulus).** The L¹ analogue of `Salt.LS.regroup`:
summing `‖ψ(y,χ⋆)‖` over non-principal `χ mod q` is bounded by summing over ALL
primitive characters of the divisors `f ∣ q`, `f ∈ [2,Q]`. The map
`χ ↦ ⟨conductor χ, χ.primitiveCharacter⟩` is injective (left inverse `changeLevel`);
every term is `≥ 0`. -/
lemma regroupL1_perq {y q Q : ℕ} [NeZero q] (hqQ : q ≤ Q) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖psiChi y χ.primitiveCharacter‖
      ≤ ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f := by
  classical
  set D := (Finset.Icc 2 Q).filter (· ∣ q) with hD
  set tt : (f : ℕ) → Finset (DirichletCharacter ℂ f) :=
    fun f => Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive) with htt
  set i : DirichletCharacter ℂ q → Σ f : ℕ, DirichletCharacter ℂ f :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hi
  set G : (Σ f : ℕ, DirichletCharacter ℂ f) → ℝ := fun p => ‖psiChi y p.2‖ with hG
  set r : (Σ f : ℕ, DirichletCharacter ℂ f) → DirichletCharacter ℂ q :=
    fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1 with hr
  set T := D.sigma tt with hT
  have hri : ∀ χ : DirichletCharacter ℂ q, r (i χ) = χ := by
    intro χ
    simp only [hr, hi]
    rw [dif_pos χ.conductor_dvd_level]
    exact DirichletCharacter.changeLevel_primitiveCharacter (χ := χ)
  have hinj : ∀ a ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ∀ b ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, i a = i b → a = b := by
    intro a _ b _ hab
    have h := congrArg r hab
    rwa [hri a, hri b] at h
  have hRHS : ∑ p ∈ T, G p = ∑ f ∈ D, primEnergyL1 y f := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [hG, htt, primEnergyL1]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖psiChi y χ.primitiveCharacter‖
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, G (i χ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        simp only [hG, hi]
    _ = ∑ p ∈ (Finset.univ.erase 1).image i, G p :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ T, G p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rw [Finset.image_subset_iff]
          intro χ hχ
          rw [Finset.mem_erase] at hχ
          obtain ⟨hχ1, _⟩ := hχ
          rw [hT, Finset.mem_sigma]
          have hcd : χ.conductor ∣ q := χ.conductor_dvd_level
          have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
          have hc_pos : 0 < χ.conductor := by
            rcases Nat.eq_zero_or_pos χ.conductor with h0 | hp
            · exact absurd (Nat.eq_zero_of_zero_dvd (h0 ▸ hcd)) (NeZero.ne q)
            · exact hp
          have hc_ne1 : χ.conductor ≠ 1 := by
            intro h
            exact hχ1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
          have hc_le : χ.conductor ≤ q := Nat.le_of_dvd hqpos hcd
          simp only [hi]
          refine ⟨?_, ?_⟩
          · rw [hD, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, le_trans hc_le hqQ⟩, hcd⟩
          · rw [htt, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, DirichletCharacter.primitiveCharacter_isPrimitive (χ := χ)⟩
        · intro p _ _; simp only [hG]; positivity
    _ = ∑ f ∈ D, primEnergyL1 y f := hRHS

/-- **The φ double-counting swap (step 4 tail).** The erase-free half of the regroup:
swap `∑_q (1/φq) ∑_{f∈[2,Q], f∣q}` into `∑_{f∈[2,Q]} (∑_{q≤Q,f∣q} 1/φq)` and fold the
level sum `≤ (4/φf)(1+log Q)` (`sum_inv_totient_dvd_le'`) into the `4(1+log Q)` prefactor. -/
lemma swapPhi_le {y Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f
      ≤ 4 * (1 + Real.log Q) *
        ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * primEnergyL1 y f := by
  -- distribute the weight inside
  have hdist : ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f
      = ∑ q ∈ Finset.Icc 1 Q, ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q),
          (1 / (q.totient : ℝ)) * primEnergyL1 y f := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
  rw [hdist]
  -- swap the order of summation
  rw [Finset.sum_comm' (t' := Finset.Icc 2 Q) (s' := fun f => (Finset.Icc 1 Q).filter (f ∣ ·))
      (by intro q f; simp only [Finset.mem_filter, Finset.mem_Icc]; tauto)]
  -- pull out `primEnergyL1 y f` and apply the φ double-counting sum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun f hf => ?_)
  rw [Finset.mem_Icc] at hf
  have hf1 : 1 ≤ f := by omega
  have hPnn : 0 ≤ primEnergyL1 y f := primEnergyL1_nonneg y f
  rw [← Finset.sum_mul]
  have hφsum := sum_inv_totient_dvd_le' hf1 hQ
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (f ∣ ·), (1 / (q.totient : ℝ))) * primEnergyL1 y f
      ≤ ((4 / (f.totient : ℝ)) * (1 + Real.log Q)) * primEnergyL1 y f :=
        mul_le_mul_of_nonneg_right hφsum hPnn
    _ = 4 * (1 + Real.log Q) * ((1 / (f.totient : ℝ)) * primEnergyL1 y f) := by ring

/-! ## The per-`q` maximal discrepancy summand -/

/-- The reduced residue set `{a < q : gcd q a = 1}` is nonempty for `q ≥ 1`
(its cardinality is `φ(q) ≥ 1`). -/
lemma reduced_nonempty {q : ℕ} (hq : 1 ≤ q) :
    ((Finset.range q).filter (Nat.Coprime q)).Nonempty := by
  rw [← Finset.card_pos, ← Nat.totient_eq_card_coprime]
  exact Nat.totient_pos.mpr hq

open Classical in
/-- **The dispersion discrepancy summand.** The target's per-`q` `sup'` over reduced
residues of `‖ψ(y;q,a) − ψ(y,χ₀)/φq‖` (or `0` on the vacuous set — never happens for
`q ≥ 1`). This is the object the frozen `V3.1` sum ranges over. -/
noncomputable def dispDisc (y q : ℕ) : ℝ :=
  if h : ((Finset.range q).filter (Nat.Coprime q)).Nonempty then
    ((Finset.range q).filter (Nat.Coprime q)).sup' h (fun a => ‖(psiAP y q a : ℂ) -
      psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖)
  else 0

lemma dispDisc_nonneg (y q : ℕ) : 0 ≤ dispDisc y q := by
  rw [dispDisc]
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact le_trans (norm_nonneg _) (Finset.le_sup'
      (fun a => ‖(psiAP y q a : ℂ) - psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖) ha)
  · exact le_refl 0

open Classical in
/-- **Per-`q` bound (V1a + conductor descent + per-`q` regroup).** For `q ∈ [1,Q]`,
`1 ≤ y`, the maximal discrepancy is bounded by the descent error `ω(q)·log y` plus the
`(1/φq)`-weighted primitive-pair energy over the divisors `f ∈ [2,Q]` of `q`. -/
lemma dispDisc_perq_le {y q Q : ℕ} (hy : 1 ≤ y) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    dispDisc y q ≤ (q.primeFactors.card : ℝ) * Real.log y
      + (1 / (q.totient : ℝ)) * ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f := by
  haveI : NeZero q := ⟨by omega⟩
  have hne := reduced_nonempty hq
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
  have hωnn : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
  set E : ℝ := (q.primeFactors.card : ℝ) * Real.log y with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  -- V1a
  have hV1a : dispDisc y q ≤ (1 / (q.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi y χ‖ := by
    rw [dispDisc, dif_pos hne]
    exact psiAP_discrepancy_sup'_le y hne
  -- descent, pointwise
  have hdesc : ∀ χ : DirichletCharacter ℂ q,
      ‖psiChi y χ‖ ≤ ‖psiChi y χ.primitiveCharacter‖ + E := by
    intro χ
    have hsub := norm_psiChi_sub_primitiveCharacter_le χ hy
    have htri : ‖psiChi y χ‖ ≤ ‖psiChi y χ.primitiveCharacter‖
        + ‖psiChi y χ - psiChi y χ.primitiveCharacter‖ := by
      have hn := norm_add_le (psiChi y χ.primitiveCharacter)
        (psiChi y χ - psiChi y χ.primitiveCharacter)
      rwa [show psiChi y χ.primitiveCharacter + (psiChi y χ - psiChi y χ.primitiveCharacter)
        = psiChi y χ by ring] at hn
    rw [hEdef]; linarith
  -- sum the descent over `erase 1`
  set S := (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1 with hSdef
  have hsum_desc : ∑ χ ∈ S, ‖psiChi y χ‖
      ≤ (∑ χ ∈ S, ‖psiChi y χ.primitiveCharacter‖) + (S.card : ℝ) * E := by
    calc ∑ χ ∈ S, ‖psiChi y χ‖
        ≤ ∑ χ ∈ S, (‖psiChi y χ.primitiveCharacter‖ + E) := Finset.sum_le_sum (fun χ _ => hdesc χ)
      _ = (∑ χ ∈ S, ‖psiChi y χ.primitiveCharacter‖) + (S.card : ℝ) * E := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  -- `card S ≤ φq`
  have hcard : (S.card : ℝ) ≤ (q.totient : ℝ) := by
    have h1 : S.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by
      rw [hSdef]; exact Finset.card_erase_le
    have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
    rw [h2] at h1; exact_mod_cast h1
  -- regroup per q
  have hregroup : ∑ χ ∈ S, ‖psiChi y χ.primitiveCharacter‖
      ≤ ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f := regroupL1_perq hqQ
  set P : ℝ := ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f with hPdef
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun f _ => primEnergyL1_nonneg y f)
  -- assemble
  have hwc : (1 / (q.totient : ℝ)) * (S.card : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hφpos]; exact hcard
  calc dispDisc y q ≤ (1 / (q.totient : ℝ)) * ∑ χ ∈ S, ‖psiChi y χ‖ := hV1a
    _ ≤ (1 / (q.totient : ℝ)) * ((∑ χ ∈ S, ‖psiChi y χ.primitiveCharacter‖) + (S.card : ℝ) * E) :=
        mul_le_mul_of_nonneg_left hsum_desc (by positivity)
    _ ≤ (1 / (q.totient : ℝ)) * (P + (S.card : ℝ) * E) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hregroup]
    _ = (1 / (q.totient : ℝ)) * P + ((1 / (q.totient : ℝ)) * (S.card : ℝ)) * E := by ring
    _ ≤ (1 / (q.totient : ℝ)) * P + 1 * E :=
        by have := mul_le_mul_of_nonneg_right hwc hEnn; linarith
    _ = E + (1 / (q.totient : ℝ)) * P := by ring

/-- **Descent + regroup, summed (steps 3–4).** For `1 ≤ y`, `1 ≤ Q`, the summed maximal
discrepancy is bounded by the total descent error plus `4(1+log Q)` times the
`(1/φf)`-weighted primitive energy over `f ∈ [2,Q]`. -/
lemma dispSum_le {y Q : ℕ} (hy : 1 ≤ y) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, dispDisc y q
      ≤ (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) * Real.log y)
        + 4 * (1 + Real.log Q) *
          ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * primEnergyL1 y f := by
  trans (∑ q ∈ Finset.Icc 1 Q, ((q.primeFactors.card : ℝ) * Real.log y
      + (1 / (q.totient : ℝ)) * ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), primEnergyL1 y f))
  · refine Finset.sum_le_sum (fun q hq => ?_)
    rw [Finset.mem_Icc] at hq
    exact dispDisc_perq_le hy hq.1 hq.2
  rw [Finset.sum_add_distrib]
  exact add_le_add (le_refl _) (swapPhi_le hQ)

/-! ## The Vaughan carrier bridge (step 6) -/

/-- **Carrier bridge.** For `1 ≤ U`, `1 ≤ V ≤ y`, `ψ(y,χ)` splits (`psiChi_sub_head_eq`
at `x := y`, whose Type I/II pieces are DEFEQ to the `typeI₁`/`typeI₂`/`typeII` carriers)
as head `+ (typeI₁ − typeI₂ + typeII)`; the triangle inequality gives the four-term bound. -/
lemma vaughan_bridge {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) {U V y : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hVx : V ≤ y) :
    ‖psiChi y χ‖ ≤ ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
      + ‖typeI₁ U V y χ‖ + ‖typeI₂ U V y χ‖ + ‖typeII U V y χ‖ := by
  have hid := psiChi_sub_head_eq χ hU hV hVx
  have he : psiChi y χ = (∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f))
      + (typeI₁ U V y χ - typeI₂ U V y χ + typeII U V y χ) := by
    have hpieces : typeI₁ U V y χ - typeI₂ U V y χ + typeII U V y χ
        = psiChi y χ - ∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f) := by
      unfold typeI₁ typeI₂ typeII
      exact hid.symm
    rw [hpieces]; ring
  rw [he]
  calc ‖(∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f))
          + (typeI₁ U V y χ - typeI₂ U V y χ + typeII U V y χ)‖
      ≤ ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
          + ‖typeI₁ U V y χ - typeI₂ U V y χ + typeII U V y χ‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
          + (‖typeI₁ U V y χ‖ + ‖typeI₂ U V y χ‖ + ‖typeII U V y χ‖) := by
        gcongr
        calc ‖typeI₁ U V y χ - typeI₂ U V y χ + typeII U V y χ‖
            ≤ ‖typeI₁ U V y χ - typeI₂ U V y χ‖ + ‖typeII U V y χ‖ := norm_add_le _ _
          _ ≤ (‖typeI₁ U V y χ‖ + ‖typeI₂ U V y χ‖) + ‖typeII U V y χ‖ := by
              gcongr; exact norm_sub_le _ _
    _ = ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
          + ‖typeI₁ U V y χ‖ + ‖typeI₂ U V y χ‖ + ‖typeII U V y χ‖ := by ring

/-! ## The large-conductor energy (step 6) -/

open Classical in
/-- **Large-conductor primitive energy (step 6).** For conductors `f > (log x)^C`, the
Vaughan bridge decomposes `‖ψ(y,χ⋆)‖` into head + Type I₁ + Type I₂ + Type II; summing
against `(1/φf)` and the primitive characters, the four landed estimates
(`norm_head_le`, `typeI_one_maxdisc_le`, `typeI_two_maxdisc_le`, `typeII_disc_le`) give
the closed four-block bound. -/
lemma largeEnergy_le {x y Q U V : ℕ} {C : ℝ} (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hQ2 : 2 ≤ Q) (hQx : Q ≤ x) (hC : 0 < C) (hyx : y ≤ x) (hVy : V ≤ y) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (Real.log x) ^ C < (f : ℝ)),
        (1 / (f.totient : ℝ)) * primEnergyL1 y f
      ≤ (Q : ℝ) * V * Real.log x
        + 3 * (U : ℝ) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) * (1 + Real.log x) ^ 2
        + 2 * ((U : ℝ) * (V : ℝ)) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
            (1 + Real.log x) ^ 2
        + 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V + x / (Real.log x) ^ C) *
            (1 + Real.log x) ^ 3 := by
  classical
  set S := (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (Real.log x) ^ C < (f : ℝ)) with hSdef
  have hSsub2 : S ⊆ (Finset.Icc 1 Q).filter (2 ≤ ·) := by
    intro f hf; rw [hSdef, Finset.mem_filter] at hf; rw [Finset.mem_filter]; exact ⟨hf.1, hf.2.1⟩
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  -- abbreviations for the four per-`f` term sums
  set headSum := ∑ f ∈ S, (1 / (f.totient : ℝ)) *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖ with hheadSumdef
  set tI1Sum := ∑ f ∈ S, (1 / (f.totient : ℝ)) *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        ‖typeI₁ U V y χ‖ with htI1Sumdef
  set tI2Sum := ∑ f ∈ S, (1 / (f.totient : ℝ)) *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        ‖typeI₂ U V y χ‖ with htI2Sumdef
  set tIISum := ∑ f ∈ S, (1 / (f.totient : ℝ)) *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        ‖typeII U V y χ‖ with htIISumdef
  -- Step A: per-`f` Vaughan decomposition into the four blocks.
  have hstepA : ∑ f ∈ S, (1 / (f.totient : ℝ)) * primEnergyL1 y f
      ≤ headSum + tI1Sum + tI2Sum + tIISum := by
    have hle : ∑ f ∈ S, (1 / (f.totient : ℝ)) * primEnergyL1 y f
        ≤ ∑ f ∈ S, (1 / (f.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
              (‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
                + ‖typeI₁ U V y χ‖ + ‖typeI₂ U V y χ‖ + ‖typeII U V y χ‖) := by
      refine Finset.sum_le_sum (fun f hf => ?_)
      rw [hSdef, Finset.mem_filter] at hf
      have hf2 : 2 ≤ f := hf.2.1
      haveI : NeZero f := ⟨by omega⟩
      rw [primEnergyL1]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun χ _ => vaughan_bridge χ hU hV hVy)) (by positivity)
    refine hle.trans (le_of_eq ?_)
    rw [hheadSumdef, htI1Sumdef, htI2Sumdef, htIISumdef,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  refine le_trans hstepA ?_
  -- Step B: bound each of the four blocks.
  have hhead : headSum ≤ (Q : ℝ) * V * Real.log x := by
    rw [hheadSumdef]
    have hper : ∀ f ∈ S, (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖ ≤ (V : ℝ) * Real.log x := by
      intro f hf
      rw [hSdef, Finset.mem_filter] at hf
      have hf2 : 2 ≤ f := hf.2.1
      haveI : NeZero f := ⟨by omega⟩
      have hφpos : (0 : ℝ) < (f.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hVL : Real.log (V : ℝ) ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < V))
          (by exact_mod_cast (le_trans hVy hyx))
      have hVlognn : (0 : ℝ) ≤ (V : ℝ) * Real.log V := by
        have : 0 ≤ Real.log (V : ℝ) := Real.log_natCast_nonneg V
        positivity
      calc (1 / (f.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
          ≤ (1 / (f.totient : ℝ)) *
              (((Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card : ℝ)
                * ((V : ℝ) * Real.log V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have := Finset.sum_le_card_nsmul
              (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive))
              (fun χ => ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖)
              ((V : ℝ) * Real.log V) (fun χ _ => norm_head_le χ)
            rwa [nsmul_eq_mul] at this
        _ ≤ (1 / (f.totient : ℝ)) * ((f.totient : ℝ) * ((V : ℝ) * Real.log V)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitive_le f) hVlognn
        _ = (V : ℝ) * Real.log V := by rw [one_div, inv_mul_cancel_left₀ hφpos.ne']
        _ ≤ (V : ℝ) * Real.log x := by
            apply mul_le_mul_of_nonneg_left hVL; positivity
    calc ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod f)‖
        ≤ ∑ _f ∈ S, (V : ℝ) * Real.log x := Finset.sum_le_sum hper
      _ = (S.card : ℝ) * ((V : ℝ) * Real.log x) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * ((V : ℝ) * Real.log x) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcardS : S.card ≤ Q := by
            calc S.card ≤ (Finset.Icc 1 Q).card :=
                  Finset.card_le_card (hSsub2.trans (Finset.filter_subset _ _))
              _ = Q := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcardS
      _ = (Q : ℝ) * V * Real.log x := by ring
  -- Type I₁ block dominated by the landed maximal estimate.
  have htI1 : tI1Sum ≤ 3 * (U : ℝ) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
      (1 + Real.log x) ^ 2 := by
    rw [htI1Sumdef]
    refine le_trans ?_ (typeI_one_maxdisc_le hx hU hV hQx)
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub2 ?_ |>.trans (Finset.sum_le_sum ?_)
    · intro f _ _
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => norm_nonneg _))
    · intro f _
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (by positivity)
      exact Finset.le_sup' (fun y' => ‖typeI₁ U V y' χ‖) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hyx⟩)
  -- Type I₂ block dominated by the landed maximal estimate.
  have htI2 : tI2Sum ≤ 2 * ((U : ℝ) * (V : ℝ)) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
      (1 + Real.log x) ^ 2 := by
    rw [htI2Sumdef]
    refine le_trans ?_ (typeI_two_maxdisc_le hx hU hV hQx)
    refine Finset.sum_le_sum_of_subset_of_nonneg hSsub2 ?_ |>.trans (Finset.sum_le_sum ?_)
    · intro f _ _
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => norm_nonneg _))
    · intro f _
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (by positivity)
      exact Finset.le_sup' (fun y' => ‖typeI₂ U V y' χ‖) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hyx⟩)
  -- Type II block: the landed closed form applies verbatim (`S` is its filter).
  have htII : tIISum ≤ 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V +
      x / (Real.log x) ^ C) * (1 + Real.log x) ^ 3 := by
    rw [htIISumdef, hSdef]
    exact typeII_disc_le hx hU hV hQ2 hQx hC y hyx
  linarith [hhead, htI1, htI2, htII]

/-! ## The small-conductor energy (step 5, Siegel–Walfisz) -/

open Classical in
/-- **Small-conductor primitive energy (step 5).** For conductors `f ≤ (log x)^C`, a
localized Siegel–Walfisz bound `hSWloc` (`‖ψ(y,χ⋆)‖ ≤ K·y/(log y)^D` for non-principal
`χ⋆` mod `f`) applied per primitive character (`#{χ⋆ prim} ≤ φf`) and per conductor
(`#{f} ≤ (log x)^C`) gives the `(log x)^C·K·y/(log y)^D` block. The `hSWloc` is the exact
`psiChi_le_of_siegelWalfisz_absorbed` output; its range alignment is threaded by the
caller. -/
lemma smallEnergy_le {x y Q : ℕ} {C D K : ℝ} (hLCnn : 0 ≤ (Real.log x) ^ C)
    (hval : 0 ≤ K * y / (Real.log y) ^ D)
    (hSWloc : ∀ (f : ℕ), 2 ≤ f → ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      (f : ℝ) ≤ (Real.log x) ^ C → ‖psiChi y χ‖ ≤ K * y / (Real.log y) ^ D) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (f : ℝ) ≤ (Real.log x) ^ C),
        (1 / (f.totient : ℝ)) * primEnergyL1 y f
      ≤ (Real.log x) ^ C * (K * y / (Real.log y) ^ D) := by
  classical
  set T := (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (f : ℝ) ≤ (Real.log x) ^ C) with hTdef
  -- per-`f` bound
  have hper : ∀ f ∈ T, (1 / (f.totient : ℝ)) * primEnergyL1 y f
      ≤ K * y / (Real.log y) ^ D := by
    intro f hf
    rw [hTdef, Finset.mem_filter] at hf
    have hf2 : 2 ≤ f := hf.2.1
    have hfLC : (f : ℝ) ≤ (Real.log x) ^ C := hf.2.2
    haveI : NeZero f := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [primEnergyL1]
    calc (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖psiChi y χ‖
        ≤ (1 / (f.totient : ℝ)) *
            (((Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card : ℝ)
              * (K * y / (Real.log y) ^ D)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hb := Finset.sum_le_card_nsmul
            (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive))
            (fun χ => ‖psiChi y χ‖) (K * y / (Real.log y) ^ D) (fun χ hχ => ?_)
          · rwa [nsmul_eq_mul] at hb
          · have hχp : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
            have hχne1 : χ ≠ 1 := by
              intro h1
              have hc : χ.conductor = 1 := (DirichletCharacter.eq_one_iff_conductor_eq_one).mp h1
              have hcf : χ.conductor = f := hχp
              omega
            exact hSWloc f hf2 χ hχne1 hfLC
        _ ≤ (1 / (f.totient : ℝ)) * ((f.totient : ℝ) * (K * y / (Real.log y) ^ D)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitive_le f) hval
        _ = K * y / (Real.log y) ^ D := by rw [one_div, inv_mul_cancel_left₀ hφpos.ne']
  -- `#T ≤ (log x)^C`
  have hcard : (T.card : ℝ) ≤ (Real.log x) ^ C := by
    have hsub : T ⊆ Finset.Icc 1 ⌊(Real.log x) ^ C⌋₊ := by
      intro f hf
      rw [hTdef, Finset.mem_filter, Finset.mem_Icc] at hf
      rw [Finset.mem_Icc]
      exact ⟨by omega, Nat.le_floor hf.2.2⟩
    calc (T.card : ℝ) ≤ ((Finset.Icc 1 ⌊(Real.log x) ^ C⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (⌊(Real.log x) ^ C⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ (Real.log x) ^ C := Nat.floor_le hLCnn
  calc ∑ f ∈ T, (1 / (f.totient : ℝ)) * primEnergyL1 y f
      ≤ ∑ _f ∈ T, (K * y / (Real.log y) ^ D) := Finset.sum_le_sum hper
    _ = (T.card : ℝ) * (K * y / (Real.log y) ^ D) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Real.log x) ^ C * (K * y / (Real.log y) ^ D) := mul_le_mul_of_nonneg_right hcard hval

/-! ## Splitting the energy at the conductor cutoff -/

open Classical in
/-- Split the conductor energy `∑_{f∈[2,Q]}` at the cutoff `(log x)^C` into the
large-conductor and small-conductor blocks (the `smallEnergy_le`/`largeEnergy_le`
filter shapes). -/
lemma energy_split {x y Q : ℕ} {C : ℝ} :
    ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * primEnergyL1 y f
      = (∑ f ∈ (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (Real.log x) ^ C < (f : ℝ)),
            (1 / (f.totient : ℝ)) * primEnergyL1 y f)
        + (∑ f ∈ (Finset.Icc 1 Q).filter (fun (f : ℕ) => 2 ≤ f ∧ (f : ℝ) ≤ (Real.log x) ^ C),
            (1 / (f.totient : ℝ)) * primEnergyL1 y f) := by
  classical
  have hset : Finset.Icc 2 Q = (Finset.Icc 1 Q).filter (fun f => 2 ≤ f) := by
    ext f; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [hset, ← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 Q).filter (fun f => 2 ≤ f)) (fun f => (Real.log x) ^ C < (f : ℝ))
    (fun f => (1 / (f.totient : ℝ)) * primEnergyL1 y f)]
  congr 1
  · rw [Finset.filter_filter]
  · rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro f _; rw [not_lt]

/-! ## The descent error bound (step 3 tail) -/

/-- **Descent error crude bound.** `∑_{q ≤ Q} ω(q)·log y ≤ Q·(logb 2 Q)·log y`
(each `ω(q) ≤ logb 2 q ≤ logb 2 Q`). -/
lemma descentError_le {y Q : ℕ} (hy : 0 ≤ Real.log y) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) * Real.log y
      ≤ (Q : ℝ) * Real.logb 2 Q * Real.log y := by
  have hlogbQ : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) (by exact_mod_cast hQ)
  calc ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) * Real.log y
      ≤ ∑ _q ∈ Finset.Icc 1 Q, Real.logb 2 Q * Real.log y := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_Icc] at hq
        have h1 : (q.primeFactors.card : ℝ) ≤ Real.logb 2 q := primeFactors_card_le_logb hq.1
        have h2 : Real.logb 2 q ≤ Real.logb 2 Q :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hq.1) (by exact_mod_cast hq.2)
        exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hy
    _ = (Q : ℝ) * Real.logb 2 Q * Real.log y := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]; ring

/-! ## The power-saving absorption engine (steps 7–8) -/

open Filter Asymptotics Topology in
/-- **Absorption.** For `θ < 1`, polylog degree `k ≥ 0`, saving `A`, and `M ≥ 0`, the
power-saving term `M·x^θ·(1+log x)^k` is eventually `≤ x/(log x)^A`. Proof: `(1+log x)^k`
is `O((log x)^k)`, so `(1+log x)^k(log x)^A = o(x^{1−θ})` (polylog vs. `rpow`), hence
`M·x^θ·(1+log x)^k(log x)^A = o(x)`; divide by `(log x)^A`. -/
lemma absorb_real {θ k A M : ℝ} (hθ : θ < 1) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    ∀ᶠ x : ℝ in atTop, M * x ^ θ * (1 + Real.log x) ^ k ≤ x / (Real.log x) ^ A := by
  have hε : (0 : ℝ) < 1 - θ := by linarith
  have hlog : (fun x : ℝ => (Real.log x) ^ (k + A)) =o[atTop] (fun x : ℝ => x ^ (1 - θ)) :=
    isLittleO_log_rpow_rpow_atTop (k + A) hε
  -- `(1+log x)^k (log x)^A = O((log x)^(k+A))`
  have hbigO : (fun x : ℝ => (1 + Real.log x) ^ k * (Real.log x) ^ A)
      =O[atTop] (fun x : ℝ => (Real.log x) ^ (k + A)) := by
    rw [isBigO_iff]
    refine ⟨2 ^ k, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hlogx1 : 1 ≤ Real.log x := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_le_log (Real.exp_pos 1) hx
    have hlogxpos : 0 < Real.log x := by linarith
    have hnn : 0 ≤ (1 + Real.log x) ^ k * (Real.log x) ^ A := by positivity
    have h1L : (1 + Real.log x) ^ k ≤ 2 ^ k * (Real.log x) ^ k := by
      rw [← Real.mul_rpow (by norm_num) hlogxpos.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hk
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
    calc (1 + Real.log x) ^ k * (Real.log x) ^ A
        ≤ (2 ^ k * (Real.log x) ^ k) * (Real.log x) ^ A :=
          mul_le_mul_of_nonneg_right h1L (by positivity)
      _ = 2 ^ k * (Real.log x) ^ (k + A) := by rw [Real.rpow_add hlogxpos]; ring
  -- chain: `M x^θ (1+log x)^k (log x)^A = o(x)`
  have hlittle : (fun x : ℝ => (1 + Real.log x) ^ k * (Real.log x) ^ A)
      =o[atTop] (fun x : ℝ => x ^ (1 - θ)) := hbigO.trans_isLittleO hlog
  have hmul : (fun x : ℝ => x ^ θ * ((1 + Real.log x) ^ k * (Real.log x) ^ A))
      =o[atTop] (fun x : ℝ => x ^ θ * x ^ (1 - θ)) :=
    (isBigO_refl (fun x : ℝ => x ^ θ) atTop).mul_isLittleO hlittle
  have hxeq : (fun x : ℝ => x ^ θ * x ^ (1 - θ)) =ᶠ[atTop] (fun x : ℝ => x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]; simp
  have hfinal : (fun x : ℝ => M * (x ^ θ * ((1 + Real.log x) ^ k * (Real.log x) ^ A)))
      =o[atTop] (fun x : ℝ => x) := (hmul.const_mul_left M).congr' EventuallyEq.rfl hxeq
  have hb := hfinal.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (Real.exp 1)] with x hbx hx
  have hlogx1 : 1 ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hlogxpos : 0 < Real.log x := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogxpos A
  have hval_nn : 0 ≤ M * (x ^ θ * ((1 + Real.log x) ^ k * (Real.log x) ^ A)) := by positivity
  rw [Real.norm_of_nonneg hval_nn, one_mul, Real.norm_of_nonneg hxpos.le] at hbx
  rw [le_div_iff₀ hLApos]
  calc M * x ^ θ * (1 + Real.log x) ^ k * (Real.log x) ^ A
      = M * (x ^ θ * ((1 + Real.log x) ^ k * (Real.log x) ^ A)) := by ring
    _ ≤ x := hbx

open Filter in
/-- The natural-number companion of `absorb_real` (compose with `Nat.cast → ∞`). -/
lemma absorb_nat {θ k A M : ℝ} (hθ : θ < 1) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      M * (n : ℝ) ^ θ * (1 + Real.log n) ^ k ≤ (n : ℝ) / (Real.log n) ^ A :=
  tendsto_natCast_atTop_atTop.eventually (absorb_real hθ hk hM)

/-! ## Crude bounds for the small-`y` branch (step 1) -/

/-- `ψ(y) ≤ y·log y` (`Λ(n) ≤ log n ≤ log y`). -/
lemma psiTot_le (y : ℕ) : psiTot y ≤ (y : ℝ) * Real.log y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [psiTot]
  · have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
    calc psiTot y = ∑ n ∈ Finset.Icc 1 y, vonMangoldt n := rfl
      _ ≤ ∑ _n ∈ Finset.Icc 1 y, Real.log y := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Icc] at hn
          exact le_trans vonMangoldt_le_log
            (Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2))
      _ = (y : ℝ) * Real.log y := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast [Nat.add_sub_cancel]; ring

/-- **Crude per-`q` discrepancy bound.** `dispDisc y q ≤ 2·ψ(y)` (`ψ(y;q,a) ≤ ψ(y)`,
`‖ψ(y,χ₀)‖ ≤ ψ(y)`, `φq ≥ 1`). -/
lemma dispDisc_crude {y q : ℕ} (hq : 1 ≤ q) : dispDisc y q ≤ 2 * psiTot y := by
  haveI : NeZero q := ⟨by omega⟩
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hpsiTot0 : 0 ≤ psiTot y := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  have hper : ∀ a : ℕ, ‖(psiAP y q a : ℂ) -
      psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ≤ 2 * psiTot y := by
    intro a
    have hAP : psiAP y q a ≤ psiTot y := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => vonMangoldt_nonneg)
    have hAP0 : 0 ≤ psiAP y q a := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    have hchi : ‖psiChi y (1 : DirichletCharacter ℂ q)‖ ≤ psiTot y := by
      rw [psiChi]
      refine le_trans (norm_sum_le _ _) ?_
      rw [psiTot]
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      calc vonMangoldt n * ‖(1 : DirichletCharacter ℂ q) (n : ZMod q)‖
          ≤ vonMangoldt n * 1 :=
            mul_le_mul_of_nonneg_left ((1 : DirichletCharacter ℂ q).norm_le_one _)
              vonMangoldt_nonneg
        _ = vonMangoldt n := mul_one _
    have hdiv : ‖psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ≤ psiTot y := by
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith : (0 : ℝ) < (q.totient : ℝ))]
      nlinarith [hchi, hpsiTot0, hφ1]
    calc ‖(psiAP y q a : ℂ) - psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖
        ≤ ‖(psiAP y q a : ℂ)‖ + ‖psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ psiTot y + psiTot y := by
          rw [Complex.norm_real, Real.norm_of_nonneg hAP0]
          exact add_le_add hAP hdiv
      _ = 2 * psiTot y := by ring
  rw [dispDisc]
  split_ifs with h
  · exact Finset.sup'_le h _ (fun a _ => hper a)
  · linarith

/-- **Small-`y` branch (step 1).** For `y ≤ √x` and `B ≥ A+1`, the summed discrepancy is
crudely `≤ 2x/(log x)^A`: each summand `≤ 2ψ(y) ≤ 2√x·log x`, and there are `≤ √x/L^B`
of them, giving `2x·L^{1−B} ≤ 2x/L^A`. -/
lemma smallY_bound {x y : ℕ} {A B : ℝ} (hx : 3 ≤ x) (hB : A + 1 ≤ B) (_hA0 : 0 < A)
    (hy : (y : ℝ) ≤ Real.sqrt x) :
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q
      ≤ 2 * x / (Real.log x) ^ A := by
  set L := Real.log (x : ℝ) with hLdef
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hL1 : 1 ≤ L := by
    rw [hLdef, show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hLpos : 0 < L := by linarith
  have hLBpos : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
  have hsqrtx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  set Q := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊ with hQdef
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqle : Real.sqrt x ≤ x := by
    nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ x by positivity), hs1, hsqrtx]
  have hlogy : Real.log y ≤ L := by
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · simp [hLpos.le]
    · exact hLdef ▸ Real.log_le_log (by exact_mod_cast hy0) (le_trans hy hsqle)
  have hpsiTot0 : 0 ≤ psiTot y := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  -- each summand `≤ 2ψ(y) ≤ 2√x·L`
  have h2psi : 2 * psiTot y ≤ 2 * (Real.sqrt x * L) := by
    have hpt : psiTot y ≤ (y : ℝ) * Real.log y := psiTot_le y
    have hlogy0 : 0 ≤ Real.log y := by
      rcases Nat.eq_zero_or_pos y with rfl | hy0
      · simp
      · exact Real.log_nonneg (by exact_mod_cast hy0)
    have : (y : ℝ) * Real.log y ≤ Real.sqrt x * L :=
      mul_le_mul hy hlogy hlogy0 hsqrtx
    linarith
  have h2psinn : 0 ≤ 2 * (Real.sqrt x * L) := by positivity
  calc ∑ q ∈ Finset.Icc 1 Q, dispDisc y q
      ≤ ∑ _q ∈ Finset.Icc 1 Q, 2 * (Real.sqrt x * L) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_Icc] at hq
        exact le_trans (dispDisc_crude hq.1) h2psi
    _ = (Q : ℝ) * (2 * (Real.sqrt x * L)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast [Nat.add_sub_cancel]; ring
    _ ≤ (Real.sqrt x / L ^ B) * (2 * (Real.sqrt x * L)) := by
        refine mul_le_mul_of_nonneg_right ?_ h2psinn
        exact le_trans (Nat.floor_le (by positivity)) (le_refl _)
    _ = 2 * (Real.sqrt x * Real.sqrt x) * (L / L ^ B) := by ring
    _ = 2 * x * (L / L ^ B) := by rw [Real.mul_self_sqrt (by positivity)]
    _ ≤ 2 * x * (1 / L ^ A) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ hLBpos (Real.rpow_pos_of_pos hLpos A), one_mul]
        calc L * L ^ A = L ^ (1 : ℝ) * L ^ A := by rw [Real.rpow_one]
          _ = L ^ (1 + A) := (Real.rpow_add hLpos 1 A).symm
          _ ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = 2 * x / L ^ A := by ring

/-! ## The combined split bound (steps 3–6 assembled) -/

/-- **Assembled split bound.** Combines `dispSum_le` (steps 3–4), `energy_split`, and the
two energy estimates (`largeEnergy_le` step 6, `smallEnergy_le` step 5) plus
`descentError_le` into the explicit `descent + 4(1+log Q)·(large + small)` bound. -/
lemma dispSum_split_le {x y Q U V : ℕ} {Cc K D : ℝ}
    (hx : 2 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hQ2 : 2 ≤ Q) (hQx : Q ≤ x) (hCc : 0 < Cc)
    (hyx : y ≤ x) (hVy : V ≤ y) (hy1 : 1 ≤ y)
    (hLCnn : 0 ≤ (Real.log x) ^ Cc) (hval : 0 ≤ K * y / (Real.log y) ^ D)
    (hSWloc : ∀ (f : ℕ), 2 ≤ f → ∀ χ : DirichletCharacter ℂ f, χ ≠ 1 →
      (f : ℝ) ≤ (Real.log x) ^ Cc → ‖psiChi y χ‖ ≤ K * y / (Real.log y) ^ D) :
    ∑ q ∈ Finset.Icc 1 Q, dispDisc y q
      ≤ (Q : ℝ) * Real.logb 2 Q * Real.log y
        + 4 * (1 + Real.log Q) *
          (((Q : ℝ) * V * Real.log x
              + 3 * (U : ℝ) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) * (1 + Real.log x) ^ 2
              + 2 * ((U : ℝ) * (V : ℝ)) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
                  (1 + Real.log x) ^ 2
              + 2048 * (Real.sqrt x * Q + x / Real.sqrt U + x / Real.sqrt V
                    + x / (Real.log x) ^ Cc) * (1 + Real.log x) ^ 3)
            + (Real.log x) ^ Cc * (K * y / (Real.log y) ^ D)) := by
  have hQ1 : 1 ≤ Q := by omega
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy1)
  refine le_trans (dispSum_le hy1 hQ1) ?_
  refine add_le_add (descentError_le hlogy0 hQ1) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [energy_split (x := x) (y := y) (Q := Q) (C := Cc)]
  exact add_le_add (largeEnergy_le hx hU hV hQ2 hQx hCc hyx hVy)
    (smallEnergy_le hLCnn hval hSWloc)

/-! ## The SW range alignment (step 5) -/

/-- **SW range alignment.** For `L ≥ 2^{Cc+1}` and `L/2 ≤ ly` (`ly = log y ≥ (log x)/2`
in the main branch), `L^Cc ≤ ly^{Cc+1}`: the extra log power absorbs the `2^{Cc+1}`
mismatch between the `(log x)`-cutoff and the `(log y)`-range of Siegel–Walfisz. -/
lemma sw_align {L ly Cc : ℝ} (hCc0 : 0 ≤ Cc) (hL : 2 ^ (Cc + 1) ≤ L) (hly : L / 2 ≤ ly) :
    L ^ Cc ≤ ly ^ (Cc + 1) := by
  have h2c : (0 : ℝ) < 2 ^ (Cc + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hLpos : 0 < L := lt_of_lt_of_le h2c hL
  have hL2pos : 0 < L / 2 := by linarith
  have hLCpos : 0 < L ^ Cc := Real.rpow_pos_of_pos hLpos Cc
  have hstep : L ^ Cc ≤ (L / 2) ^ (Cc + 1) := by
    rw [Real.div_rpow hLpos.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_add hLpos, Real.rpow_one,
      le_div_iff₀ h2c]
    exact mul_le_mul_of_nonneg_left hL hLCpos.le
  exact hstep.trans (Real.rpow_le_rpow hL2pos.le hly (by linarith))

open Filter Asymptotics Topology in
/-- `2·(log x)^B ≤ √x` eventually (polylog `=o` `x^{1/2}`). Used to force the haircut
level `Q = ⌊√x/(log x)^B⌋ ≥ 2` in the main branch. -/
lemma eventually_two_polylog_le_sqrt {B : ℝ} :
    ∀ᶠ n : ℕ in atTop, 2 * (Real.log n) ^ B ≤ Real.sqrt n := by
  have h := isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ B ≤ Real.sqrt x := by
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hbx hx1
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogx0 B),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) (1 / 2))] at hbx
    rw [Real.sqrt_eq_rpow]
    linarith
  exact tendsto_natCast_atTop_atTop.eventually hev

/-! ## The keystone theorem -/

open Filter Topology in
/-- **V3.1 — ψ-form BV dispersion (∀-fixed-y form).** Given `SiegelWalfisz` and the
large-conductor Vaughan branch bound `hlargeY` (the explicit `M·x^{19/20}·(1+log x)^4 +
K·x/(log x)^A` split of `dispSum_split_le`'s output at the operating point `B = A+6`,
`U = V = ⌊x^{1/10}⌋`), the frozen dispersion estimate holds.

The small-`y` branch is `smallY_bound`; the `x^{19/20}` term is absorbed by `absorb_nat`;
the finite small-`x` range is absorbed into the constant via the crude `dispDisc_crude`
bound. `hlargeY` isolates exactly the deferred large-`y` term arithmetic — see
`docs/blueprints/flags.md` (node V3.1). -/
theorem psi_BV_of_siegelWalfisz (_hSW : SiegelWalfisz)
    (hlargeY : ∀ A : ℝ, 0 < A → ∃ Mc Kc : ℝ, 0 ≤ Mc ∧ 0 ≤ Kc ∧
      ∀ x y : ℕ, 1024 ≤ x → 1 ≤ Real.log x →
        2 ≤ ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ →
        ⌊Real.sqrt x⌋₊ < y → y ≤ x → Real.log x / 2 ≤ Real.log y →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
          ≤ Mc * (x : ℝ) ^ (19 / 20 : ℝ) * (1 + Real.log x) ^ (4 : ℝ)
            + Kc * (x : ℝ) / (Real.log x) ^ A) :
    ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ x → y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q
        ≤ C * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨Mc, Kc, hMc, hKc, hLY⟩ := hlargeY A hA
  -- crude bound (all `x ≥ 2`): the sum is `≤ Q·2ψ(x)`.
  have hcrude : ∀ x y : ℕ, 2 ≤ x → y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
        ≤ (⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x) := by
    intro x y hx hy
    have hpsimono : psiTot y ≤ psiTot x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hy)
        (fun _ _ _ => vonMangoldt_nonneg)
    have hpsi0 : 0 ≤ psiTot y := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
        ≤ ∑ _q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, (2 * psiTot y) :=
          Finset.sum_le_sum (fun q hq => dispDisc_crude (Finset.mem_Icc.mp hq).1)
      _ = (⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot y) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast [Nat.add_sub_cancel]; ring
      _ ≤ (⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x) := by
          gcongr
  -- eventual bound.
  have heph : ∀ᶠ x : ℕ in atTop, ∀ y : ℕ, y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
        ≤ (Kc + 3) * x / (Real.log x) ^ A := by
    filter_upwards [absorb_nat (θ := 19 / 20) (k := 4) (A := A) (M := Mc)
        (by norm_num) (by norm_num) hMc,
      eventually_two_polylog_le_sqrt (B := A + 6), eventually_ge_atTop 1024,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ)]
      with x habs hsqrtev hx1024 hLev
    intro y hy
    have hL1 : 1 ≤ Real.log x := hLev
    have hLpos : 0 < Real.log x := by linarith
    have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
    have hxpos : (0 : ℝ) < x := by
      have : (1024 : ℝ) ≤ x := by exact_mod_cast hx1024
      linarith
    have hQ2 : 2 ≤ ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_ofNat, le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
      linarith [hsqrtev]
    by_cases hys : y ≤ ⌊Real.sqrt x⌋₊
    · -- small `y`
      have hyle : (y : ℝ) ≤ Real.sqrt x :=
        le_trans (by exact_mod_cast hys) (Nat.floor_le (Real.sqrt_nonneg _))
      calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
          ≤ 2 * x / (Real.log x) ^ A :=
            smallY_bound (by omega) (by linarith) hA hyle
        _ ≤ (Kc + 3) * x / (Real.log x) ^ A := by
            rw [div_le_div_iff_of_pos_right hLApos]
            nlinarith [hKc, hxpos]
    · -- large `y`
      have hyl : ⌊Real.sqrt x⌋₊ < y := not_le.mp hys
      have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have hsxy : Real.sqrt x ≤ (y : ℝ) := by
        have h1 : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (⌊Real.sqrt x⌋₊ : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hyl
        linarith
      have hly : Real.log x / 2 ≤ Real.log y := by
        rw [← Real.log_sqrt hxpos.le]
        exact Real.log_le_log hsqrtpos hsxy
      calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
          ≤ Mc * (x : ℝ) ^ (19 / 20 : ℝ) * (1 + Real.log x) ^ (4 : ℝ)
              + Kc * (x : ℝ) / (Real.log x) ^ A := hLY x y hx1024 hL1 hQ2 hyl hy hly
        _ ≤ (x : ℝ) / (Real.log x) ^ A + Kc * (x : ℝ) / (Real.log x) ^ A := by linarith [habs]
        _ = (1 + Kc) * x / (Real.log x) ^ A := by ring
        _ ≤ (Kc + 3) * x / (Real.log x) ^ A := by
            rw [div_le_div_iff_of_pos_right hLApos]
            nlinarith [hxpos, hKc]
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp heph
  -- small-`x` constant (finite range absorbed into a sum).
  set Csm : ℝ := ∑ x' ∈ Finset.Icc 2 x₀,
    (⌊Real.sqrt x' / (Real.log x') ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x') * (Real.log x') ^ A / x'
    with hCsmdef
  have hCsm0 : 0 ≤ Csm := by
    rw [hCsmdef]
    refine Finset.sum_nonneg (fun x' hx' => ?_)
    rw [Finset.mem_Icc] at hx'
    have : 0 ≤ psiTot x' := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
    positivity
  refine ⟨A + 6, max (Kc + 3) Csm, by linarith, le_trans hKc (by simp), fun x y hx hy => ?_⟩
  by_cases hxx : x₀ ≤ x
  · -- `x ≥ x₀`: the eventual bound.
    refine le_trans (hx₀ x hxx y hy) ?_
    have hLApos : 0 < (Real.log x) ^ A :=
      Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))) A
    rw [div_le_div_iff_of_pos_right hLApos]
    have hxnn : (0 : ℝ) ≤ x := by positivity
    nlinarith [le_max_left (Kc + 3) Csm, hxnn]
  · -- `2 ≤ x < x₀`: crude bound absorbed into `Csm`.
    have hxmem : x ∈ Finset.Icc 2 x₀ := Finset.mem_Icc.mpr ⟨hx, by omega⟩
    have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
    have hxpos : (0 : ℝ) < x := by linarith
    have hsingle : (⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x)
        * (Real.log x) ^ A / x ≤ Csm := by
      rw [hCsmdef]
      refine Finset.single_le_sum (f := fun x' : ℕ =>
        (⌊Real.sqrt x' / (Real.log x') ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x') * (Real.log x') ^ A / x')
        (fun x' hx' => ?_) hxmem
      rw [Finset.mem_Icc] at hx'
      have : 0 ≤ psiTot x' := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
      positivity
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊, dispDisc y q
        ≤ (⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x) := hcrude x y hx hy
      _ = ((⌊Real.sqrt x / (Real.log x) ^ (A + 6)⌋₊ : ℝ) * (2 * psiTot x) * (Real.log x) ^ A / x)
            * (x / (Real.log x) ^ A) := by field_simp
      _ ≤ Csm * (x / (Real.log x) ^ A) := by
          apply mul_le_mul_of_nonneg_right hsingle (by positivity)
      _ ≤ max (Kc + 3) Csm * x / (Real.log x) ^ A := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Salt.BV
