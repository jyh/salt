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

Steps (1)–(3) land unconditionally.  The final assembly `qdiag_bridge` is
reduced to `mv_J_split` plus a single hypothesis `hgap` (the summed step-(4)
bound `|Qdiag − ∑Inn²/∏g| ≤ …`) in `qdiag_bridge_of`.  Discharging `hgap`
against the frozen `κ⁻¹·(1+X+PAS)⁶/D` bucket runs into a `κ⁻²/D²` obstruction
from the square-difference *self*-term `∑_u (yM − Inn)²/∏g`; see the FABLE-QUEUE
flag `docs/blueprints/flags.md` (W4-5).
-/

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

/-- **The reduction to `mv_J_split` (steps (4)–(5)).** Given the summed
step-(4) bound `hgap` — `|Qdiag − ∑_u Inn(u)²/∏_{i≠m}g|` controlled by the
frozen `κ⁻¹·(1+X+PAS)⁶/D` bucket — the S₂ bridge follows by the triangle
inequality with `mv_J_split` (which evaluates `∑_u Inn²/∏g`), folding
`mv_J`'s own `(1+X+PAS)⁶/D` error into the same bucket via `κ⁻¹ ≥ 1`.

The `∑_u Inn²/∏g` sum in `hgap` is **exactly** `mv_J_split`'s left-hand side
(the outer box is `kSieveIndex 5 R W'` filtered on `·ₘ = 1`, matching
`qdiag_eq_yMsq_sum`'s box with no reindex).  The κ⁻¹ = `(W'/φW')` factor stays
**explicit**; the constant `A = Agap + A'` is `W'`-free (both `Agap` and
`mv_J_split`'s `A'` are `(F,m)`-only). -/
theorem qdiag_bridge_of (F : Poly) (m : Fin 5)
    (Agap : ℝ) (hAgap0 : 0 ≤ Agap)
    (hgap : ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' → 300 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 5 R W' m (yF R W' F)
        - ∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)|
      ≤ Agap * ((W' : ℝ) / W'.totient)
          * (1 + (W'.totient : ℝ) / W' * Real.log R
               + Salt.Maynard.phiAtomSum R W') ^ 6 / D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' F)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D := by
  obtain ⟨A', hA'0, hA'⟩ := mv_J_split F m
  refine ⟨Agap + A', by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨c, hc0, hc⟩ := hA' W' D hW' hpos hUpper (by omega) hDW
  refine ⟨c, hc0, ?_⟩
  intro R hR2 hlogR
  have hgapWR := hgap W' D hW' hpos hUpper hD hDW R hR2 hlogR
  have hmvJ := hc R hlogR
  -- notation
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
  -- key facts
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : (300 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hκ1 : (1 : ℝ) ≤ κinv := by
    rw [hκdef, le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hpos)]
    simpa using (by exact_mod_cast Nat.totient_le W' : (W'.totient : ℝ) ≤ (W' : ℝ))
  have hY6nn : 0 ≤ Y6 := by rw [hY6def]; positivity
  have hY6D : 0 ≤ Y6 / D := by positivity
  -- reshape the divisions to a common `* (Y6/D)` factor (Log6/Main opaque)
  rw [mul_div_assoc] at hgapWR hmvJ
  rw [mul_div_assoc]
  -- fold mv_J's own 1/D error into the κ⁻¹ bucket (κ⁻¹ ≥ 1)
  have hfold : A' * (Y6 / D) ≤ A' * κinv * (Y6 / D) := by
    nlinarith [mul_nonneg (mul_nonneg hA'0 hY6D) (sub_nonneg.mpr hκ1)]
  -- triangle inequality + fold
  calc |Qdiag_mW 5 R W' m (yF R W' F) - Main|
      ≤ |Qdiag_mW 5 R W' m (yF R W' F) - Jsum| + |Jsum - Main| :=
        abs_sub_le _ _ _
    _ ≤ Agap * κinv * (Y6 / D) + (Log6 + A' * (Y6 / D)) := add_le_add hgapWR hmvJ
    _ = Log6 + Agap * κinv * (Y6 / D) + A' * (Y6 / D) := by ring
    _ ≤ Log6 + Agap * κinv * (Y6 / D) + A' * κinv * (Y6 / D) := by linarith [hfold]
    _ = Log6 + (Agap + A') * κinv * (Y6 / D) := by ring

end Salt.Twelve
