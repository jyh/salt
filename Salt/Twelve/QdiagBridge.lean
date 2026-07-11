/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvSplit
import Salt.Maynard.Lemma53W
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.S2Eh
import Salt.Twelve.FstarNorm

/-!
# Card W4-5 — the S₂ diagonal bridge `qdiag_bridge`

Design: `docs/blueprints/explicit12-design.md`, card W4-5.  This file connects
the sieve's real second moment `Qdiag_mW 5 R W' m (yF R W' F)` to the
polynomial main term `X⁶ · simplexInt (sq (contractAt m F))` by way of the
outer square sum that `mv_J_split` (W4-2) evaluates.

The route has five steps (card W4-5):

1. **Diagonalise** — `s2_diag_lam_restricted` (landed, free-`W`) rewrites the
   quadratic form as `∑_{u : uₘ=1} (∏ᵢ g(uᵢ))·V(u)²` with `V = lamPhiContractM`;
   the per-term identity `(∏ᵢ g(uᵢ))·V² = yM²/∏_{i≠m}g` (`μ² = 1`, `g(1) = 1`)
   is `qdiag_eq_yMsq_sum` below (unconditional).
2. **Contraction** — `lemma53_tightW` (W4-3) at `B = 1` bounds `|yM(u) − Inn(u)|`
   pointwise by `lemma53Const·5·log R/D`.
3. **Square difference** — `|yM² − Inn²| ≤ |yM − Inn|·(2|Inn| + |yM − Inn|)`.
4. **Sum over `u`** — crude `g`-moments via `marked_sqf_g_rel (s = 1)`.
5. **Consume `mv_J_split`** — `∑_u Inn²/∏_{i≠m}g` is exactly `mv_J_split`'s LHS.

The frozen `1/D` bucket is the **two-term** `A·κ⁻¹·Y⁶/D + A·κ⁻²·Y⁶/D²`
(`κ⁻¹ = W'/φW'`, `Y = 1+X+PAS`), authorized 2026-07-10 after the Opus pre-flight
identified that the square-difference *self*-term `∑_u (yM − Inn)²/∏g` from the
`lemma53` layer contributes `κ⁻²/D²` — affordable at the endgame
(`κ⁻²/D² ≤ 25/D → 0`) but not fittable in a single `κ⁻¹·Y⁶/D` bucket.  Full
`qdiag_bridge` lands here: `qdiag_gap` discharges steps (1)–(4) (the summed
contraction bound), and `qdiag_bridge_of` closes step (5) (triangle with
`mv_J_split`).  `A` is `(F,m)`-only; κ⁻¹ and κ⁻² stay explicit. -/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Twelve

open Salt.Maynard

/-- `(gMult 1 : ℝ) = 1` (the empty prime-factor product). -/
private lemma gMult_one_R : (gMult 1 : ℝ) = 1 := by
  simp [gMult, Nat.primeFactors_one]

/-- **Step 1 (the diagonalisation identity, unconditional).** The free-`W'`
restricted diagonalisation `s2_diag_lam_restricted` rewrites `Qdiag_mW` as the
`u`-sum of `(∏ᵢ g(uᵢ))·V(u)²`; on the pinned box (`uₘ = 1`, each `uᵢ`
squarefree) this per-term equals `yM(u)²/∏_{i≠m}g(uᵢ)` because
`yM = (∏ᵢ μ(uᵢ)g(uᵢ))·V`, `μ(uᵢ)² = 1`, and `∏ᵢ g(uᵢ) = ∏_{i≠m} g(uᵢ)` (the
`m`-factor is `g(1) = 1`).  Matches `mv_J_split`'s outer box **exactly**. -/
theorem qdiag_eq_yMsq_sum (R W' : ℕ) (m : Fin 5) (F : Poly) :
    Qdiag_mW 5 R W' m (yF R W' F)
      = ∑ u ∈ (kSieveIndex 5 R W').filter (fun u => u m = 1),
          (yM 5 R W' m (yF R W' F) u) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
  classical
  -- (Step A) the landed free-`W'` diagonalisation.
  have hdiag : Qdiag_mW 5 R W' m (yF R W' F)
      = ∑ u ∈ (kSieveIndex 5 R W').filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM 5 R W' m (yF R W' F) u) ^ 2 := by
    rw [Qdiag_mW]
    exact s2_diag_lam_restricted 5 R W' m (yF R W' F)
  rw [hdiag]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_filter] at hu
  obtain ⟨hbox, hum⟩ := hu
  -- box facts
  have hsqf : ∀ i, Squarefree (u i) := fun i => ((mem_kSieveIndex_iff u).mp hbox).1 i
  -- ∏ᵢ g(uᵢ) = ∏_{i≠m} g(uᵢ)  (the m-factor is g(1) = 1)
  set Gm : ℝ := ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) with hGmdef
  set V : ℝ := lamPhiContractM 5 R W' m (yF R W' F) u with hVdef
  have hprodg : (∏ i, (gMult (u i) : ℝ)) = Gm := by
    rw [hGmdef, ← Finset.mul_prod_erase Finset.univ (fun i => (gMult (u i) : ℝ))
      (Finset.mem_univ m), hum, gMult_one_R, one_mul]
  -- yM(u)² = Gm² · V²   (μ² = 1 on the squarefree box, and ∏ᵢg = Gm)
  have hyMsq : (yM 5 R W' m (yF R W' F) u) ^ 2 = Gm ^ 2 * V ^ 2 := by
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
  -- Gm² · V² / Gm = (∏ᵢ g) · V² = Gm · V²
  rw [hprodg]
  by_cases hGm : Gm = 0
  · simp [hGm]
  · field_simp

/-! ## Steps 2–3: the pointwise contraction and the `|Inn|` bound -/

/-- Triangle inequality for a `List.sum` of reals. -/
private lemma qb_list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

/-- Monotonicity of `List.sum` under a pointwise `≤`. -/
private lemma qb_list_sum_le {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private lemma eval_ofPoly_sum (F : Poly) (t : Fin 5 → ℝ) :
    eval (ofPoly F) t = (F.map (fun a => (a.2 : ℝ) * ∏ i, t i ^ a.1 i)).sum := by
  simp only [eval, ofPoly, List.map_map, Function.comp_def, pow_zero, mul_one]

private lemma Qabs_cast_R (F : Poly) :
    ((Qabs F : ℚ) : ℝ) = (F.map (fun m => |(m.2 : ℝ)|)).sum := by
  unfold Qabs
  rw [Rat.cast_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
  simp only [Function.comp_apply, Rat.cast_abs]

/-- **General `|yF| ≤ Qabs F`** (the `Fstar1`-free version of W4-4's
`yF_Fstar1_abs_le_one`).  Off the box `yF` vanishes; on the box each coordinate
`t i = log(s i)/log R ∈ [0,1]`, so the budget-`0` monomial bound gives
`|eval (ofPoly F) t| ≤ ∑|coeffs| = Qabs F`.  With `hQ : Qabs F ≤ 1` this yields
the `|y| ≤ 1` hypothesis `lemma53_tightW` needs at `B = 1`. -/
theorem yF_abs_le_Qabs (R W' : ℕ) (F : Poly) (s : Fin 5 → ℕ) :
    |yF R W' F s| ≤ ((Qabs F : ℚ) : ℝ) := by
  unfold yF
  split_ifs with hs
  · have hR2 : 2 ≤ R := by have := kSieveIndex_coord_pos hs 0
                           have := kSieveIndex_coord_lt hs 0; omega
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR2.trans_lt' (by norm_num)
    have hLpos : 0 < Real.log R := Real.log_pos hR1
    have ht0 : ∀ i, 0 ≤ Real.log (s i) / Real.log R := fun i =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast kSieveIndex_coord_pos hs i)) hLpos.le
    have ht1 : ∀ i, Real.log (s i) / Real.log R ≤ 1 := by
      intro i
      rw [div_le_one hLpos]
      exact Real.log_le_log (by exact_mod_cast kSieveIndex_coord_pos hs i)
        (by exact_mod_cast (kSieveIndex_coord_lt hs i).le)
    rw [eval_ofPoly_sum, Qabs_cast_R]
    refine le_trans (qb_list_abs_sum_le F _) (qb_list_sum_le F _ _ (fun a _ => ?_))
    have hprod0 : 0 ≤ ∏ i, (Real.log (s i) / Real.log R) ^ a.1 i :=
      Finset.prod_nonneg (fun i _ => pow_nonneg (ht0 i) _)
    have hprod1 : ∏ i, (Real.log (s i) / Real.log R) ^ a.1 i ≤ 1 :=
      Finset.prod_le_one (fun i _ => pow_nonneg (ht0 i) _)
        (fun i _ => pow_le_one₀ (ht0 i) (ht1 i))
    rw [abs_mul, abs_of_nonneg hprod0]
    calc |(a.2 : ℝ)| * ∏ i, (Real.log (s i) / Real.log R) ^ a.1 i
        ≤ |(a.2 : ℝ)| * 1 := mul_le_mul_of_nonneg_left hprod1 (abs_nonneg _)
      _ = |(a.2 : ℝ)| := mul_one _
  · rw [abs_zero, Qabs_cast_R]
    apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _

/-- **Step 2 (pointwise contraction).** `lemma53_tightW` (W4-3) at `B = 1`
(discharging `|yF| ≤ 1` from `hQ` via `yF_abs_le_Qabs`, support from `yF`'s
`if`, and `12·5² = 300 ≤ D`): `|yM(u) − Inn(u)| ≤ lemma53Const·5·log R/D`. -/
theorem yM_sub_inn_le (R W' D : ℕ) (m : Fin 5) (F : Poly) (hQ : Qabs F ≤ 1)
    (hR : 2 ≤ R) (hW' : Squarefree W')
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hDk : 300 ≤ D)
    (u : Fin 5 → ℕ) (hum : u m = 1) (husupp : u ∈ kSieveIndex 5 R W') :
    |yM 5 R W' m (yF R W' F) u
        - ∑ am ∈ Finset.range R,
            yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ lemma53Const * (5 : ℝ) * Real.log R / (D : ℝ) := by
  have hyB : ∀ s, |yF R W' F s| ≤ 1 := fun s =>
    le_trans (yF_abs_le_Qabs R W' F s) (by exact_mod_cast hQ)
  have hysupp : ∀ s, s ∉ kSieveIndex 5 R W' → yF R W' F s = 0 := by
    intro s hs; unfold yF; rw [if_neg hs]
  have h := lemma53_tightW 5 R W' D m (yF R W' F) 1 (by norm_num) hyB hysupp u hum hR
    husupp hW' hDW (by norm_num) (le_trans (by norm_num : (12 * 5 ^ 2 : ℕ) ≤ 300) hDk)
  simpa using h

/-- **Step 3 ingredient (`|Inn(u)| ≤ PAS`).** Each `|yF| ≤ 1` on the box and
`am` is forced squarefree/coprime there, so `|Inn(u)| ≤ ∑_{am<R, sqf, cop} 1/φ`,
which is `≤ phiAtomSum R W'` by `marked_sqf_phi_rel` at `a = 0`, `s = 1`
(PAS-relative, no opaque constant). -/
theorem absInn_le_pas (R W' : ℕ) (m : Fin 5) (F : Poly) (hQ : Qabs F ≤ 1)
    (hR : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W') (u : Fin 5 → ℕ) :
    |∑ am ∈ Finset.range R,
        yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ Salt.Maynard.phiAtomSum R W' := by
  classical
  have hyB : ∀ s, |yF R W' F s| ≤ 1 := fun s =>
    le_trans (yF_abs_le_Qabs R W' F s) (by exact_mod_cast hQ)
  -- termwise: off the box `= 0`; on the box `≤ 1/φ`
  have hstep : ∀ am ∈ Finset.range R,
      |yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)|
        ≤ (if (Squarefree am ∧ am.Coprime W' ∧ (1 : ℕ) ∣ am)
            then (Real.log am) ^ 0 / (Nat.totient am : ℝ) else 0) := by
    intro am _
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient am : ℝ))]
    split_ifs with hc
    · rw [pow_zero]
      exact div_le_div_of_nonneg_right (hyB _) (by positivity)
    · -- `am` not sqf/cop ⟹ the updated tuple leaves the box ⟹ `yF = 0`
      have hnot : Function.update u m am ∉ kSieveIndex 5 R W' := by
        intro hmem
        obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff _).mp hmem
        have h1 : Squarefree am := by
          have := hsqf m; rwa [Function.update_self] at this
        have h2 : am.Coprime W' := by
          have := hcop m; rwa [Function.update_self] at this
        exact hc ⟨h1, h2, one_dvd am⟩
      rw [show yF R W' F (Function.update u m am) = 0 from by
        unfold yF; rw [if_neg hnot], abs_zero, zero_div]
  calc |∑ am ∈ Finset.range R,
          yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R,
          |yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)| :=
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

/-! ## Step 4: the crude 4-dim `g`-moment and the summed contraction bound -/

private lemma pas_nn (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg (fun x _ => by positivity)

/-- `∏_{i≠m} F i = ∏_{j:Fin 4} F (m.succAbove j)` (reindex the erased product by
`succAbove`). -/
private lemma erase_prod_removeNth {M : Type*} [CommMonoid M] (m : Fin 5)
    (F : Fin 5 → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ j : Fin 4, F (m.succAbove j) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin 5)) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]

/-- **Step 4 g-moment (crude, PAS-relative).** The 4-dimensional `1/∏g`-moment
over the pinned box `uₘ = 1` is `≤ (2·PAS)⁴`: reindex to `kSieveIndex 4`
(`sum_filt_removeNth`), enlarge the box to the per-coordinate product
(`kSieveIndex 4 ⊆ ∏ F_R`), factor via `Finset.prod_univ_sum`, and bound each
coordinate sum `∑_{x<R, sqf, cop} 1/g(x) ≤ 2·PAS` by `marked_sqf_g_rel` at
`a = 0`, `s = 1` (`g(1) = 1`).  No opaque constant. -/
theorem gmoment4_le (W' D R : ℕ) (m : Fin 5) (hW' : Squarefree W') (hpos : 0 < W')
    (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    ∑ u ∈ (kSieveIndex 5 R W').filter (fun u => u m = 1),
        (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      ≤ (2 * Salt.Maynard.phiAtomSum R W') ^ 4 := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hFRdef
  set M0 := ∑ x ∈ F_R, (1 : ℝ) / (gMult x : ℝ) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  -- per-coordinate bound `M0 ≤ 2·PAS`
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
  -- reindex the pinned box to `kSieveIndex 4`
  have hreindex : ∑ u ∈ (kSieveIndex 5 R W').filter (fun u => u m = 1),
        (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      = ∑ ρ ∈ kSieveIndex 4 R W', (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ) := by
    rw [← sum_filt_removeNth R W' m (fun ρ => (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ))]
    apply Finset.sum_congr rfl; intro r _
    congr 1
    rw [erase_prod_removeNth m (fun i => (gMult (r i) : ℝ))]
    exact Finset.prod_congr rfl (fun j _ => by rw [Fin.removeNth_apply])
  rw [hreindex]
  -- enlarge to the per-coordinate product box and factor
  have hsub : kSieveIndex 4 R W' ⊆ Fintype.piFinset (fun _ : Fin 4 => F_R) := by
    intro ρ hρ
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
    rw [Fintype.mem_piFinset]; intro j
    rw [hFRdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨kSieveIndex_coord_lt hρ j, hsqf j, hcop j⟩
  calc ∑ ρ ∈ kSieveIndex 4 R W', (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ)
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
          (1 : ℝ) / ∏ j, (gMult (ρ j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => by positivity)
    _ = ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
          ∏ j, ((1 : ℝ) / (gMult (ρ j) : ℝ)) := by
        apply Finset.sum_congr rfl; intro ρ _
        rw [one_div, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl (fun j _ => by rw [one_div])
    _ = ∏ _j : Fin 4, ∑ x ∈ F_R, (1 : ℝ) / (gMult x : ℝ) :=
        (Finset.prod_univ_sum (fun _ : Fin 4 => F_R)
          (fun _ x => (1 : ℝ) / (gMult x : ℝ))).symm
    _ = M0 ^ 4 := by
        rw [← hM0def, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 * Salt.Maynard.phiAtomSum R W') ^ 4 := pow_le_pow_left₀ hM0nn hM0le 4

/-- **Steps (2)–(4) assembled: the summed contraction bound.** With the
diagonalisation (step 1), the pointwise contraction (step 2, `yM_sub_inn_le`)
and `|Inn| ≤ PAS` (step 3, `absInn_le_pas`), and the crude g-moment (step 4,
`gmoment4_le`),

  `|Qdiag − ∑_u Inn²/∏g| ≤ 32·c₀·κ⁻¹·Y⁶/D + 16·c₀²·κ⁻²·Y⁶/D²`,

where `c₀ = lemma53Const·5`, `κ⁻¹ = W'/φW'`, `Y = 1 + X + PAS`.  Decompose
`yM² − Inn² = 2·Inn·(yM−Inn) + (yM−Inn)²`; the CROSS part sums to `κ⁻¹/D`
(via `logR = κ⁻¹·X`, `X·PAS⁵ ≤ Y⁶`), the SELF part to `κ⁻²/D²`
(via `logR² = κ⁻²·X²`, `X²·PAS⁴ ≤ Y⁶`).  Every constant is `(F,m)`-free
(`c₀` is landed) and `PAS`-relative; **κ⁻¹, κ⁻² stay explicit.** -/
theorem qdiag_gap (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1)
    (W' D : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (hD : 300 ≤ D)
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (R : ℕ) (hR2 : 2 ≤ R) (hlogR : 1 ≤ Real.log R) :
    |Qdiag_mW 5 R W' m (yF R W' F)
      - ∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
          (∑ u ∈ Finset.range R,
              yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
    ≤ 32 * (lemma53Const * 5) * ((W' : ℝ) / W'.totient)
        * (1 + (W'.totient : ℝ) / W' * Real.log R
             + Salt.Maynard.phiAtomSum R W') ^ 6 / D
      + 16 * (lemma53Const * 5) ^ 2 * ((W' : ℝ) / W'.totient) ^ 2
        * (1 + (W'.totient : ℝ) / W' * Real.log R
             + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2 := by
  classical
  have hStepA := qdiag_eq_yMsq_sum R W' m F
  have hGM := gmoment4_le W' D R m hW' hpos (by omega) hDW hR2
  have hLpos : 0 < Real.log R := by linarith
  have hφpos : 0 < (W'.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hpos
  have hW'0 : (W' : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hφ0 : (W'.totient : ℝ) ≠ 0 := hφpos.ne'
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (300 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hPAS00 : 0 ≤ Salt.Maynard.phiAtomSum R W' := pas_nn R W'
  set c₀ : ℝ := lemma53Const * 5 with hc₀def
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκinvdef
  set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  set Y : ℝ := 1 + X + PAS with hYdef
  set ε : ℝ := c₀ * Real.log R / D with hεdef
  set filt := (kSieveIndex 5 R W').filter (fun r => r m = 1) with hfiltdef
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀def]; exact mul_nonneg lemma53Const_nonneg (by norm_num)
  have hPAS0 : 0 ≤ PAS := by rw [hPASdef]; exact hPAS00
  have hκinv0 : 0 ≤ κinv := by rw [hκinvdef]; positivity
  have hX0 : 0 ≤ X := by rw [hXdef]; exact mul_nonneg (by positivity) hLpos.le
  have hXY : X ≤ Y := by rw [hYdef]; linarith
  have hPASY : PAS ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := by rw [hYdef]; linarith
  have hε0 : 0 ≤ ε := by rw [hεdef]; exact div_nonneg (mul_nonneg hc₀0 hLpos.le) hDpos.le
  have hκκ : κinv * ((W'.totient : ℝ) / W') = 1 := by rw [hκinvdef]; field_simp
  have hLXκ : Real.log R = κinv * X := by rw [hXdef, ← mul_assoc, hκκ, one_mul]
  have hGmnn : ∀ u : Fin 5 → ℕ, 0 ≤ ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) :=
    fun u => Finset.prod_nonneg (fun i _ => by positivity)
  -- the pure-algebra square-difference bound
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
  -- per-`u` square-difference bound
  have hbnd : ∀ u ∈ filt, |(yM 5 R W' m (yF R W' F) u) ^ 2
        - (∑ am ∈ Finset.range R,
            yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2|
      ≤ 2 * PAS * ε + ε ^ 2 := by
    intro u hu
    rw [hfiltdef, Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    refine habstract _ _ ?_ ?_
    · rw [hPASdef]; exact absInn_le_pas R W' m F hQ hR2 hW' hpos u
    · rw [hεdef, hc₀def]; exact yM_sub_inn_le R W' D m F hQ hR2 hW' hDW hD u hum husupp
  -- rewrite the difference as a single sum
  have hdiff : Qdiag_mW 5 R W' m (yF R W' F)
        - ∑ r ∈ filt, (∑ u ∈ Finset.range R,
              yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)
      = ∑ u ∈ filt, ((yM 5 R W' m (yF R W' F) u) ^ 2
          - (∑ am ∈ Finset.range R,
              yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2)
          / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
    rw [hStepA, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => by rw [sub_div])
  -- step (1)–(4): the sum is `≤ (2·PAS·ε + ε²)·(2·PAS)⁴`
  have hb1 : |Qdiag_mW 5 R W' m (yF R W' F)
        - ∑ r ∈ filt, (∑ u ∈ Finset.range R,
              yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
      ≤ (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ 4 := by
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcoef_nn : 0 ≤ 2 * PAS * ε + ε ^ 2 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hPAS0) hε0) (sq_nonneg ε)
    have hstep : ∑ u ∈ filt, |((yM 5 R W' m (yF R W' F) u) ^ 2
          - (∑ am ∈ Finset.range R,
              yF R W' F (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2)
          / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)|
        ≤ ∑ u ∈ filt, (2 * PAS * ε + ε ^ 2)
            * (1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)) := by
      apply Finset.sum_le_sum; intro u hu
      rw [abs_div, abs_of_nonneg (hGmnn u), div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (hbnd u hu) (by positivity)
    refine le_trans hstep ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hGM hcoef_nn
  -- step (4)–(5) arithmetic: fit the two `1/D` buckets
  have hXP5 : X * PAS ^ 5 ≤ Y ^ 6 := by
    calc X * PAS ^ 5 ≤ Y * Y ^ 5 :=
          mul_le_mul hXY (pow_le_pow_left₀ hPAS0 hPASY 5) (pow_nonneg hPAS0 5) hY0
      _ = Y ^ 6 := by ring
  have hX2P4 : X ^ 2 * PAS ^ 4 ≤ Y ^ 6 := by
    calc X ^ 2 * PAS ^ 4 ≤ Y ^ 2 * Y ^ 4 :=
          mul_le_mul (pow_le_pow_left₀ hX0 hXY 2) (pow_le_pow_left₀ hPAS0 hPASY 4)
            (pow_nonneg hPAS0 4) (pow_nonneg hY0 2)
      _ = Y ^ 6 := by ring
  have hεeq : ε = c₀ * (κinv * X) / D := by rw [hεdef, hLXκ]
  have hb2 : (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ 4
      ≤ 32 * c₀ * κinv * Y ^ 6 / D + 16 * c₀ ^ 2 * κinv ^ 2 * Y ^ 6 / D ^ 2 := by
    have hexp : (2 * PAS * ε + ε ^ 2) * (2 * PAS) ^ 4
        = 32 * (ε * PAS ^ 5) + 16 * (ε ^ 2 * PAS ^ 4) := by ring
    rw [hexp]
    have hcoef1 : (0 : ℝ) ≤ 32 * c₀ * κinv / D :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc₀0) hκinv0) hDpos.le
    have hcoef2 : (0 : ℝ) ≤ 16 * c₀ ^ 2 * κinv ^ 2 / D ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c₀)) (sq_nonneg κinv))
        (by positivity)
    have ha1 : 32 * (ε * PAS ^ 5) ≤ 32 * c₀ * κinv * Y ^ 6 / D := by
      rw [hεeq,
        show 32 * ((c₀ * (κinv * X) / D) * PAS ^ 5) = (32 * c₀ * κinv / D) * (X * PAS ^ 5) from by
          ring,
        show 32 * c₀ * κinv * Y ^ 6 / D = (32 * c₀ * κinv / D) * Y ^ 6 from by ring]
      exact mul_le_mul_of_nonneg_left hXP5 hcoef1
    have ha2 : 16 * (ε ^ 2 * PAS ^ 4) ≤ 16 * c₀ ^ 2 * κinv ^ 2 * Y ^ 6 / D ^ 2 := by
      rw [hεeq,
        show 16 * ((c₀ * (κinv * X) / D) ^ 2 * PAS ^ 4)
            = (16 * c₀ ^ 2 * κinv ^ 2 / D ^ 2) * (X ^ 2 * PAS ^ 4) from by ring,
        show 16 * c₀ ^ 2 * κinv ^ 2 * Y ^ 6 / D ^ 2
            = (16 * c₀ ^ 2 * κinv ^ 2 / D ^ 2) * Y ^ 6 from by ring]
      exact mul_le_mul_of_nonneg_left hX2P4 hcoef2
    linarith [ha1, ha2]
  exact le_trans hb1 hb2

/-- **The reduction to `mv_J_split` (steps (4)–(5)).** Given the summed step-(4)
bound `hgap` (`|Qdiag − ∑_u Inn²/∏g|` in the two-term `κ⁻¹·Y⁶/D + κ⁻²·Y⁶/D²`
bucket), the S₂ bridge follows by the triangle inequality with `mv_J_split`
(which evaluates `∑_u Inn²/∏g`), folding `mv_J`'s own `Y⁶/D` error into the
first bucket term via `κ⁻¹ ≥ 1`.

The `∑_u Inn²/∏g` sum in `hgap` is **exactly** `mv_J_split`'s left-hand side
(outer box `kSieveIndex 5 R W'` filtered on `·ₘ = 1`, matching
`qdiag_eq_yMsq_sum`'s box with no reindex).  κ⁻¹, κ⁻² stay **explicit**;
`A = Ac + Aself + A'` is `W'`-free (`Ac`, `Aself`, and `mv_J_split`'s `A'` are
all `(F,m)`-only). -/
theorem qdiag_bridge_of (F : Poly) (m : Fin 5)
    (Ac Aself : ℝ) (hAc0 : 0 ≤ Ac) (hAself0 : 0 ≤ Aself)
    (hgap : ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' → 300 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 5 R W' m (yF R W' F)
        - ∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
      ≤ Ac * ((W' : ℝ) / W'.totient)
          * (1 + (W'.totient : ℝ) / W' * Real.log R
               + Salt.Maynard.phiAtomSum R W') ^ 6 / D
        + Aself * ((W' : ℝ) / W'.totient) ^ 2
          * (1 + (W'.totient : ℝ) / W' * Real.log R
               + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' F)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2 := by
  obtain ⟨A', hA'0, hA'⟩ := mv_J_split F m
  refine ⟨Ac + Aself + A', by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨c, hc0, hc⟩ := hA' W' D hW' hpos hUpper (by omega) hDW
  refine ⟨c, hc0, ?_⟩
  intro R hR2 hlogR
  have hgapWR := hgap W' D hW' hpos hUpper hD hDW R hR2 hlogR
  have hmvJ := hc R hlogR
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκdef
  set Y6 : ℝ := (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 with hY6def
  set Jsum : ℝ := ∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
      (∑ u ∈ Finset.range R,
          yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
        / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) with hJsumdef
  set Main : ℝ := ((W'.totient : ℝ) / W' * Real.log R) ^ 6
      * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ) with hMaindef
  set Log6 : ℝ := c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
    with hLog6def
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : (300 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hκ1 : (1 : ℝ) ≤ κinv := by
    rw [hκdef, le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hpos)]
    simpa using (by exact_mod_cast Nat.totient_le W' : (W'.totient : ℝ) ≤ (W' : ℝ))
  have hY6nn : 0 ≤ Y6 := by rw [hY6def]; positivity
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
  calc |Qdiag_mW 5 R W' m (yF R W' F) - Main|
      ≤ |Qdiag_mW 5 R W' m (yF R W' F) - Jsum| + |Jsum - Main| := abs_sub_le _ _ _
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

/-- **Card W4-5 — the S₂ diagonal bridge (frozen, two-term bucket).** Connects
the sieve's real second moment `Qdiag_mW 5 R W' m (yF R W' F)` to the polynomial
main term `X⁶·simplexInt (sq (contractAt m F))`, with a `1/log R` error and a
two-term `1/D` bucket `A·κ⁻¹·Y⁶/D + A·κ⁻²·Y⁶/D²` (`κ⁻¹ = W'/φW'`, `Y = 1+X+PAS`;
the `κ⁻²/D²` term carries the `lemma53` contraction-error SELF-term).  `A` is
`(F,m)`-only; both `κ`-powers are explicit, consumption-safe computables.  The
proof discharges the summed contraction bound `qdiag_gap` (steps 1–4) and feeds
it to `qdiag_bridge_of` (step 5, triangle with `mv_J_split`). -/
theorem qdiag_bridge (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' F)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2 := by
  apply qdiag_bridge_of F m (32 * (lemma53Const * 5)) (16 * (lemma53Const * 5) ^ 2)
    (mul_nonneg (by norm_num) (mul_nonneg lemma53Const_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (sq_nonneg _))
  intro W' D hW' hpos hUpper hD hDW R hR2 hlogR
  exact qdiag_gap F m hQ W' D hW' hpos hD hDW R hR2 hlogR

end Salt.Twelve
