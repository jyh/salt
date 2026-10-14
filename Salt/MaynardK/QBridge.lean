/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.JSplit
import Salt.Twelve.QdiagBridge
import Salt.Maynard.Lemma53W
import Salt.Maynard.S2DiagRestricted

/-!
# C1 · B4.3c — `qdiag_bridge` at general `n` for a bounded budget weight (`qdiag_bridge_gen`)

Steps 1–4 at general `k`/`n` for a bounded weight; step 5 consumes `mv_J_split_gen`. `A` before
`W'`;
the `1/D` terms carry `(1 + X + PAS)`. `qdiag_bridge_k5` (in `Controls`) recovers the landed
`qdiag_bridge` verbatim.
Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve Salt.Maynard Salt.MaynardK

private lemma gMult_one_R : (gMult 1 : ℝ) = 1 := by
  simp [gMult, Nat.primeFactors_one]

private lemma pas_nn (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg (fun x _ => by positivity)

/-- **Step 1 at general `k`, any weight `y`.** -/
theorem qdiag_eq_yMsq_sum_gen (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) :
    Qdiag_mW k R W' m y
      = ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
          (yM k R W' m y u) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
  classical
  have hdiag : Qdiag_mW k R W' m y
      = ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R W' m y u) ^ 2 := by
    rw [Qdiag_mW]
    exact s2_diag_lam_restricted k R W' m y
  rw [hdiag]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_filter] at hu
  obtain ⟨hbox, hum⟩ := hu
  have hsqf : ∀ i, Squarefree (u i) := fun i => ((mem_kSieveIndex_iff u).mp hbox).1 i
  set Gm : ℝ := ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) with hGmdef
  set V : ℝ := lamPhiContractM k R W' m y u with hVdef
  have hprodg : (∏ i, (gMult (u i) : ℝ)) = Gm := by
    rw [hGmdef, ← Finset.mul_prod_erase Finset.univ (fun i => (gMult (u i) : ℝ))
      (Finset.mem_univ m), hum, gMult_one_R, one_mul]
  have hyMsq : (yM k R W' m y u) ^ 2 = Gm ^ 2 * V ^ 2 := by
    have hP2 : (∏ i, ((μ (u i) : ℤ) : ℝ) * (gMult (u i) : ℝ)) ^ 2
        = (∏ i, (gMult (u i) : ℝ)) ^ 2 := by
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      have hmu : ((μ (u i) : ℤ) : ℝ) ^ 2 = 1 := by
        have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsqf i)
        have hc : ((μ (u i) : ℤ) : ℝ) ^ 2 = (((μ (u i)) ^ 2 : ℤ) : ℝ) := by push_cast; ring
        rw [hc, h]; norm_num
      rw [mul_pow, hmu, one_mul]
    rw [yM, mul_pow, hP2, hprodg]
  rw [hyMsq]
  rw [hprodg]
  by_cases hGm : Gm = 0
  · simp [hGm]
  · field_simp

/-- **Step 2 at general `k`, bounded weight.** -/
theorem yM_sub_inn_le_gen (k R W' D : ℕ) (hk : 1 ≤ k) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hy0 : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR : 2 ≤ R) (hW' : Squarefree W')
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D)
    (u : Fin k → ℕ) (hum : u m = 1) (husupp : u ∈ kSieveIndex k R W') :
    |yM k R W' m y u
        - ∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ lemma53Const * (k : ℝ) * Real.log R / (D : ℝ) := by
  have h := lemma53_tightW k R W' D m y 1 (by norm_num) hy1 hy0 u hum hR
    husupp hW' hDW hk hDk
  simpa using h

/-- **Step 3 ingredient at general `k`: `|Inn(u)| ≤ PAS`.** -/
theorem absInn_le_pas_gen (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hy0 : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W') (u : Fin k → ℕ) :
    |∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ Salt.Maynard.phiAtomSum R W' := by
  classical
  have hstep : ∀ am ∈ Finset.range R,
      |y (Function.update u m am) / (Nat.totient am : ℝ)|
        ≤ (if (Squarefree am ∧ am.Coprime W' ∧ (1 : ℕ) ∣ am)
            then (Real.log am) ^ 0 / (Nat.totient am : ℝ) else 0) := by
    intro am _
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient am : ℝ))]
    split_ifs with hc
    · rw [pow_zero]
      exact div_le_div_of_nonneg_right (hy1 _) (by positivity)
    · have hnot : Function.update u m am ∉ kSieveIndex k R W' := by
        intro hmem
        obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff _).mp hmem
        have h1 : Squarefree am := by
          have := hsqf m; rwa [Function.update_self] at this
        have h2 : am.Coprime W' := by
          have := hcop m; rwa [Function.update_self] at this
        exact hc ⟨h1, h2, one_dvd am⟩
      rw [hy0 _ hnot, abs_zero, zero_div]
  calc |∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update u m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R,
          (if (Squarefree am ∧ am.Coprime W' ∧ (1 : ℕ) ∣ am)
            then (Real.log am) ^ 0 / (Nat.totient am : ℝ) else 0) :=
        Finset.sum_le_sum hstep
    _ = ∑ am ∈ (Finset.range R).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ (1 : ℕ) ∣ r),
          (Real.log am) ^ 0 / (Nat.totient am : ℝ) := (Finset.sum_filter _ _).symm
    _ ≤ (1 / (Nat.totient 1 : ℝ)) * (Real.log R) ^ 0 * Salt.Maynard.phiAtomSum R W' :=
        marked_sqf_phi_rel W' hW' hpos 0 1 R one_pos hR
    _ = Salt.Maynard.phiAtomSum R W' := by simp

private lemma erase_prod_removeNth_e4 {n : ℕ} {M : Type*} [CommMonoid M] (m : Fin (n + 1))
    (F : Fin (n + 1) → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ j : Fin n, F (m.succAbove j) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin (n + 1))) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]

/-- **Step 4 g-moment at general `n`:** the `n`-dimensional `1/∏g`-moment over the pinned
box is `≤ (2·PAS)ⁿ`. -/
theorem gmoment_le_gen (n W' D R : ℕ) (m : Fin (n + 1)) (hW' : Squarefree W') (hpos : 0 < W')
    (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    ∑ u ∈ (kSieveIndex (n + 1) R W').filter (fun u => u m = 1),
        (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      ≤ (2 * Salt.Maynard.phiAtomSum R W') ^ n := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hFRdef
  set M0 := ∑ x ∈ F_R, (1 : ℝ) / (gMult x : ℝ) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * Salt.Maynard.phiAtomSum R W' := by
    have hg1 := marked_sqf_g_rel W' hW' hpos 0 D 1 R hD hDW one_pos hR2
    have hFeq : ((Finset.range R).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ (1 : ℕ) ∣ r)) = F_R := by
      rw [hFRdef]; apply Finset.filter_congr; intro r _
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
    rw [gMult_one_R, hFeq] at hg1
    have hL : ∑ x ∈ F_R, (Real.log x) ^ 0 / (gMult x : ℝ) = M0 := by
      rw [hM0def]; exact Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
    rw [hL] at hg1
    simpa using hg1
  have hreindex : ∑ u ∈ (kSieveIndex (n + 1) R W').filter (fun u => u m = 1),
        (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      = ∑ ρ ∈ kSieveIndex n R W', (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ) := by
    rw [← sum_filt_removeNth_g R W' m (fun ρ => (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ))]
    apply Finset.sum_congr rfl; intro r _
    congr 1
    rw [erase_prod_removeNth_e4 m (fun i => (gMult (r i) : ℝ))]
    exact Finset.prod_congr rfl (fun j _ => by rw [Fin.removeNth_apply])
  rw [hreindex]
  have hsub : kSieveIndex n R W' ⊆ Fintype.piFinset (fun _ : Fin n => F_R) := by
    intro ρ hρ
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
    rw [Fintype.mem_piFinset]; intro j
    rw [hFRdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨kSieveIndex_coord_lt hρ j, hsqf j, hcop j⟩
  calc ∑ ρ ∈ kSieveIndex n R W', (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ)
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
          (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => by positivity)
    _ = ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
          ∏ j, ((1 : ℝ) / (gMult (ρ j) : ℝ)) := by
        apply Finset.sum_congr rfl; intro ρ _
        rw [one_div, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl (fun j _ => by rw [one_div])
    _ = ∏ _j : Fin n, ∑ x ∈ F_R, (1 : ℝ) / (gMult x : ℝ) :=
        (Finset.prod_univ_sum (fun _ : Fin n => F_R)
          (fun _ x => (1 : ℝ) / (gMult x : ℝ))).symm
    _ = M0 ^ n := by
        rw [← hM0def, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 * Salt.Maynard.phiAtomSum R W') ^ n := pow_le_pow_left₀ hM0nn hM0le n

/-- **Steps (1)–(4) at general `n`, any bounded weight `y`.** -/
theorem qdiag_gap_gen (n : ℕ) (m : Fin (n + 1)) (y : (Fin (n + 1) → ℕ) → ℝ)
    (W' D : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (hD : 12 * (n + 1) ^ 2 ≤ D)
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (R : ℕ) (hR2 : 2 ≤ R) (hlogR : 1 ≤ Real.log R)
    (hy1 : ∀ s, |y s| ≤ 1) (hy0 : ∀ s, s ∉ kSieveIndex (n + 1) R W' → y s = 0) :
    |Qdiag_mW (n + 1) R W' m y
      - ∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
          (∑ u ∈ Finset.range R,
              y (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
    ≤ 2 ^ (n + 1) * (lemma53Const * ((n + 1 : ℕ) : ℝ)) * ((W' : ℝ) / W'.totient)
        * (1 + (W'.totient : ℝ) / W' * Real.log R
             + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D
      + 2 ^ n * (lemma53Const * ((n + 1 : ℕ) : ℝ)) ^ 2 * ((W' : ℝ) / W'.totient) ^ 2
        * (1 + (W'.totient : ℝ) / W' * Real.log R
             + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D ^ 2 := by
  classical
  have hStepA := qdiag_eq_yMsq_sum_gen (n + 1) R W' m y
  have hD12 : 12 ≤ D := le_trans (by nlinarith [Nat.zero_le n]) hD
  have hGM := gmoment_le_gen n W' D R m hW' hpos (by omega) hDW hR2
  have hLpos : 0 < Real.log R := by linarith
  have hφpos : 0 < (W'.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hpos
  have hW'0 : (W' : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hφ0 : (W'.totient : ℝ) ≠ 0 := hφpos.ne'
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (12 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD12
    linarith
  have hPAS00 : 0 ≤ Salt.Maynard.phiAtomSum R W' := pas_nn R W'
  set c₀ : ℝ := lemma53Const * ((n + 1 : ℕ) : ℝ) with hc₀def
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκinvdef
  set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  set Y : ℝ := 1 + X + PAS with hYdef
  set ε : ℝ := c₀ * Real.log R / D with hεdef
  set filt := (kSieveIndex (n + 1) R W').filter (fun r => r m = 1) with hfiltdef
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀def]; exact mul_nonneg lemma53Const_nonneg (by positivity)
  have hPAS0 : 0 ≤ PAS := by rw [hPASdef]; exact hPAS00
  have hκinv0 : 0 ≤ κinv := by rw [hκinvdef]; positivity
  have hX0 : 0 ≤ X := by rw [hXdef]; exact mul_nonneg (by positivity) hLpos.le
  have hXY : X ≤ Y := by rw [hYdef]; linarith
  have hPASY : PAS ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := by rw [hYdef]; linarith
  have hε0 : 0 ≤ ε := by rw [hεdef]; exact div_nonneg (mul_nonneg hc₀0 hLpos.le) hDpos.le
  have hκκ : κinv * ((W'.totient : ℝ) / W') = 1 := by rw [hκinvdef]; field_simp
  have hLXκ : Real.log R = κinv * X := by rw [hXdef, ← mul_assoc, hκκ, one_mul]
  have hGmnn : ∀ u : Fin (n + 1) → ℕ, 0 ≤ ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) :=
    fun u => Finset.prod_nonneg (fun i _ => by positivity)
  have habstract : ∀ a b : ℝ, |b| ≤ PAS → |a - b| ≤ ε →
      |a ^ 2 - b ^ 2| ≤ 2 * PAS * ε + ε ^ 2 := by
    intro a b hb hab
    have hid : a ^ 2 - b ^ 2 = 2 * b * (a - b) + (a - b) ^ 2 := by ring
    rw [hid]
    calc |2 * b * (a - b) + (a - b) ^ 2|
        ≤ |2 * b * (a - b)| + |(a - b) ^ 2| := abs_add_le _ _
      _ = 2 * |b| * |a - b| + |a - b| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]; norm_num
      _ ≤ 2 * PAS * ε + ε ^ 2 := by
          have h1 : |b| * |a - b| ≤ PAS * ε := mul_le_mul hb hab (abs_nonneg _) hPAS0
          have h2 : |a - b| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
          nlinarith [h1, h2]
  have hbnd : ∀ u ∈ filt, |(yM (n + 1) R W' m y u) ^ 2
        - (∑ am ∈ Finset.range R,
            y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2|
      ≤ 2 * PAS * ε + ε ^ 2 := by
    intro u hu
    rw [hfiltdef, Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    refine habstract _ _ ?_ ?_
    · rw [hPASdef]; exact absInn_le_pas_gen (n + 1) R W' m y hy1 hy0 hR2 hW' hpos u
    · rw [hεdef, hc₀def]
      exact yM_sub_inn_le_gen (n + 1) R W' D (by omega) m y hy1 hy0 hR2 hW' hDW hD u hum husupp
  have hdiff : Qdiag_mW (n + 1) R W' m y
        - ∑ r ∈ filt, (∑ u ∈ Finset.range R,
              y (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)
      = ∑ u ∈ filt, ((yM (n + 1) R W' m y u) ^ 2
          - (∑ am ∈ Finset.range R,
              y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2)
          / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
    rw [hStepA, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => by rw [sub_div])
  have hb1 : |Qdiag_mW (n + 1) R W' m y
        - ∑ r ∈ filt, (∑ u ∈ Finset.range R,
              y (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
      ≤ (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ n := by
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcoef_nn : 0 ≤ 2 * PAS * ε + ε ^ 2 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hPAS0) hε0) (sq_nonneg ε)
    have hstep : ∑ u ∈ filt, |((yM (n + 1) R W' m y u) ^ 2
          - (∑ am ∈ Finset.range R,
              y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2)
          / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)|
        ≤ ∑ u ∈ filt, (2 * PAS * ε + ε ^ 2)
            * (1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)) := by
      apply Finset.sum_le_sum; intro u hu
      rw [abs_div, abs_of_nonneg (hGmnn u), div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (hbnd u hu) (by positivity)
    refine le_trans hstep ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hGM hcoef_nn
  -- the two `1/D` buckets (PAS, X, Y are atoms; the exponent `n` is symbolic)
  have hXP : X * PAS ^ (n + 1) ≤ Y ^ (n + 2) := by
    calc X * PAS ^ (n + 1) ≤ Y * Y ^ (n + 1) :=
          mul_le_mul hXY (pow_le_pow_left₀ hPAS0 hPASY (n + 1)) (pow_nonneg hPAS0 _) hY0
      _ = Y ^ (n + 2) := by ring
  have hX2P : X ^ 2 * PAS ^ n ≤ Y ^ (n + 2) := by
    calc X ^ 2 * PAS ^ n ≤ Y ^ 2 * Y ^ n :=
          mul_le_mul (pow_le_pow_left₀ hX0 hXY 2) (pow_le_pow_left₀ hPAS0 hPASY n)
            (pow_nonneg hPAS0 n) (pow_nonneg hY0 2)
      _ = Y ^ (n + 2) := by ring
  have hεeq : ε = c₀ * (κinv * X) / D := by rw [hεdef, hLXκ]
  have hb2 : (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ n
      ≤ 2 ^ (n + 1) * c₀ * κinv * Y ^ (n + 2) / D
        + 2 ^ n * c₀ ^ 2 * κinv ^ 2 * Y ^ (n + 2) / D ^ 2 := by
    have hexp : (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ n
        = 2 ^ (n + 1) * (ε * PAS ^ (n + 1)) + 2 ^ n * (ε ^ 2 * PAS ^ n) := by
      rw [mul_pow]; ring
    rw [hexp]
    have hcoef1 : (0 : ℝ) ≤ 2 ^ (n + 1) * c₀ * κinv / D :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hc₀0) hκinv0) hDpos.le
    have hcoef2 : (0 : ℝ) ≤ 2 ^ n * c₀ ^ 2 * κinv ^ 2 / D ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg c₀)) (sq_nonneg κinv))
        (by positivity)
    have ha1 : 2 ^ (n + 1) * (ε * PAS ^ (n + 1)) ≤ 2 ^ (n + 1) * c₀ * κinv * Y ^ (n + 2) / D := by
      rw [hεeq,
        show 2 ^ (n + 1) * ((c₀ * (κinv * X) / D) * PAS ^ (n + 1))
            = (2 ^ (n + 1) * c₀ * κinv / D) * (X * PAS ^ (n + 1)) from by ring,
        show 2 ^ (n + 1) * c₀ * κinv * Y ^ (n + 2) / D
            = (2 ^ (n + 1) * c₀ * κinv / D) * Y ^ (n + 2) from by ring]
      exact mul_le_mul_of_nonneg_left hXP hcoef1
    have ha2 : 2 ^ n * (ε ^ 2 * PAS ^ n) ≤ 2 ^ n * c₀ ^ 2 * κinv ^ 2 * Y ^ (n + 2) / D ^ 2 := by
      rw [hεeq,
        show 2 ^ n * ((c₀ * (κinv * X) / D) ^ 2 * PAS ^ n)
            = (2 ^ n * c₀ ^ 2 * κinv ^ 2 / D ^ 2) * (X ^ 2 * PAS ^ n) from by ring,
        show 2 ^ n * c₀ ^ 2 * κinv ^ 2 * Y ^ (n + 2) / D ^ 2
            = (2 ^ n * c₀ ^ 2 * κinv ^ 2 / D ^ 2) * Y ^ (n + 2) from by ring]
      exact mul_le_mul_of_nonneg_left hX2P hcoef2
    linarith [ha1, ha2]
  exact le_trans hb1 hb2

/-- **Step 5 at general `n`: the triangle with `mv_J_split_gen`.** -/
theorem qdiag_bridge_gen_of (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (Ac Aself : ℝ) (hAc0 : 0 ≤ Ac) (hAself0 : 0 ≤ Aself)
    (hgap : ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' → 12 * (n + 1) ^ 2 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW (n + 1) R W' m (yFg R W' P)
        - ∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
      ≤ Ac * ((W' : ℝ) / W'.totient)
          * (1 + (W'.totient : ℝ) / W' * Real.log R
               + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D
        + Aself * ((W' : ℝ) / W'.totient) ^ 2
          * (1 + (W'.totient : ℝ) / W' * Real.log R
               + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 12 * (n + 1) ^ 2 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW (n + 1) R W' m (yFg R W' P)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D ^ 2 := by
  obtain ⟨A', hA'0, hA'⟩ := mv_J_split_gen n hn P m
  refine ⟨Ac + Aself + A', by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  have hD3 : 3 ≤ D := le_trans (by nlinarith [Nat.zero_le n]) hD
  obtain ⟨c, hc0, hc⟩ := hA' W' D hW' hpos hUpper hD3 hDW
  refine ⟨c, hc0, ?_⟩
  intro R hR2 hlogR
  have hgapWR := hgap W' D hW' hpos hUpper hD hDW R hR2 hlogR
  have hmvJ := hc R hlogR
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκdef
  set Y6 : ℝ := (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) with hY6def
  set Jsum : ℝ := ∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
      (∑ u ∈ Finset.range R,
          yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
        / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) with hJsumdef
  set Main : ℝ := ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
      * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ) with hMaindef
  set Log6 : ℝ := c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
    with hLog6def
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
    linarith
  have hκ1 : (1 : ℝ) ≤ κinv := by
    rw [hκdef, le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hpos)]
    simpa using (by exact_mod_cast Nat.totient_le W' : (W'.totient : ℝ) ≤ (W' : ℝ))
  have hY6nn : 0 ≤ Y6 := by
    rw [hY6def]
    have := pas_nn R W'
    have : 0 ≤ (W'.totient : ℝ) / W' * Real.log R :=
      mul_nonneg (by positivity) (by linarith)
    positivity
  have hq1 : 0 ≤ Y6 / D := by positivity
  have hq2 : 0 ≤ Y6 / D ^ 2 := by positivity
  rw [mul_div_assoc, mul_div_assoc] at hgapWR
  rw [mul_div_assoc] at hmvJ
  rw [mul_div_assoc, mul_div_assoc]
  have hfold1 : A' * (Y6 / D) ≤ A' * κinv * (Y6 / D) := by
    nlinarith [mul_nonneg (mul_nonneg hA'0 hq1) (sub_nonneg.mpr hκ1)]
  have hle1 : (Ac + A') * (κinv * (Y6 / D)) ≤ (Ac + Aself + A') * (κinv * (Y6 / D)) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hq1)
  have hle2 : Aself * (κinv ^ 2 * (Y6 / D ^ 2))
      ≤ (Ac + Aself + A') * (κinv ^ 2 * (Y6 / D ^ 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity) hq2)
  calc |Qdiag_mW (n + 1) R W' m (yFg R W' P) - Main|
      ≤ |Qdiag_mW (n + 1) R W' m (yFg R W' P) - Jsum| + |Jsum - Main| := abs_sub_le _ _ _
    _ ≤ (Ac * κinv * (Y6 / D) + Aself * κinv ^ 2 * (Y6 / D ^ 2))
          + (Log6 + A' * (Y6 / D)) := add_le_add hgapWR hmvJ
    _ = Log6 + (Ac * κinv * (Y6 / D) + A' * (Y6 / D))
          + Aself * κinv ^ 2 * (Y6 / D ^ 2) := by ring
    _ ≤ Log6 + (Ac * κinv * (Y6 / D) + A' * κinv * (Y6 / D))
          + Aself * κinv ^ 2 * (Y6 / D ^ 2) := by linarith [hfold1]
    _ = Log6 + (Ac + A') * (κinv * (Y6 / D)) + Aself * (κinv ^ 2 * (Y6 / D ^ 2)) := by ring
    _ ≤ Log6 + (Ac + Aself + A') * (κinv * (Y6 / D))
          + (Ac + Aself + A') * (κinv ^ 2 * (Y6 / D ^ 2)) := by linarith [hle1, hle2]
    _ = Log6 + (Ac + Aself + A') * κinv * (Y6 / D)
          + (Ac + Aself + A') * κinv ^ 2 * (Y6 / D ^ 2) := by ring

/-- **B4.3c — `qdiag_bridge_gen`.** The S₂ diagonal bridge at general `n` for the budget
weight `yFg R W' P`, under the pointwise bound `hy1`. `A` is `(n, P, m)`-only and precedes
`∀ W'`. -/
theorem qdiag_bridge_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' P s| ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 12 * (n + 1) ^ 2 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW (n + 1) R W' m (yFg R W' P)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D ^ 2 := by
  apply qdiag_bridge_gen_of n hn P m
    (2 ^ (n + 1) * (lemma53Const * ((n + 1 : ℕ) : ℝ)))
    (2 ^ n * (lemma53Const * ((n + 1 : ℕ) : ℝ)) ^ 2)
    (mul_nonneg (by positivity) (mul_nonneg lemma53Const_nonneg (by positivity)))
    (mul_nonneg (by positivity) (sq_nonneg _))
  intro W' D hW' hpos _hUpper hD hDW R hR2 hlogR
  have hy0 : ∀ s, s ∉ kSieveIndex (n + 1) R W' → yFg R W' P s = 0 := by
    intro s hs; unfold yFg; rw [if_neg hs]
  exact qdiag_gap_gen n m (yFg R W' P) W' D hW' hpos hD hDW R hR2 hlogR (hy1 R W') hy0

/-- **The `hy1` adapter from the simplex form** (the shape `eval_F1_abs_le_one` has): on the
box, `tᵢ = log sᵢ / log R ≥ 0` and `∑ tᵢ = log(∏ sᵢ)/log R ≤ 1` since `∏ sᵢ < R`. -/
theorem yFg_abs_le_one_of_simplex {n : ℕ} (P : BPoly (n + 1))
    (hP : ∀ t : Fin (n + 1) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i ≤ 1 → |eval P t| ≤ 1)
    (R W' : ℕ) (s : Fin (n + 1) → ℕ) : |yFg R W' P s| ≤ 1 := by
  unfold yFg
  split_ifs with hs
  · have hR2 : 2 ≤ R := by
      have := kSieveIndex_coord_pos hs 0
      have := kSieveIndex_coord_lt hs 0; omega
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR2.trans_lt' (by norm_num)
    have hLpos : 0 < Real.log R := Real.log_pos hR1
    have hspos : ∀ i, (0 : ℝ) < (s i : ℝ) := fun i => by
      exact_mod_cast kSieveIndex_coord_pos hs i
    apply hP
    · intro i
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast kSieveIndex_coord_pos hs i)) hLpos.le
    · rw [← Finset.sum_div, div_le_one hLpos, ← Real.log_prod (fun i _ => (hspos i).ne')]
      have hprod_lt : ∏ i, s i < R := ((mem_kSieveIndex_iff s).mp hs).2.2.2
      have hprod_pos : (0 : ℝ) < ∏ i, (s i : ℝ) := Finset.prod_pos (fun i _ => hspos i)
      apply Real.log_le_log hprod_pos
      have : ((∏ i, s i : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hprod_lt.le
      simpa using this
  · simp

/-- `qdiag_bridge_gen` with the simplex-form hypothesis (direct plug for `eval_F1_abs_le_one`). -/
theorem qdiag_bridge_gen_simplex (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hP : ∀ t : Fin (n + 1) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i ≤ 1 → |eval P t| ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 12 * (n + 1) ^ 2 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW (n + 1) R W' m (yFg R W' P)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D ^ 2 :=
  qdiag_bridge_gen n hn P m (yFg_abs_le_one_of_simplex P hP)

end Salt.MaynardK

