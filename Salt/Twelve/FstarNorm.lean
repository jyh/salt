/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.Certificate
import Salt.Twelve.BudgetPoly
import Salt.Twelve.MvJ
import Salt.Maynard.Tuple
import Salt.Maynard.KSieve

/-!
# Wave-4 card W4-4 — normalization + instantiation helpers (`Salt/Twelve/FstarNorm.lean`)

The `k = 5` pigeonhole (`sum_S2m_eq`, `bounded_gap_of_S2_gt_S1`, ...) is
degree-2 homogeneous in the sieve weight `y`, so it is scale-invariant: any
positive rescaling of the certified optimum `F★` (`Salt.Twelve.Fstar`) still
certifies `M₅ > 2`, and rescaling by `1 / Qabs F★` (the ℓ¹-norm of `F★`'s
coefficients) makes the associated weight `yF` uniformly bounded by `1` on
the sieve box — the normalization the downstream `|y| ≤ B` contraction
machinery (`lemma53_tightW`, card W4-3) consumes.

This file provides:

* `Qabs`/`Fstar1` — the ℓ¹-normalization of `Fstar`;
* `M5_cert1` — the certificate transported to `Fstar1` (via the exact
  quadratic scaling of `Ical`/`Jcal` in the coefficient list, not by
  re-running the 3136-monomial `norm_num` of `M5_cert`);
* `yF_Fstar1_abs_le_one` — the resulting sieve weight is `≤ 1` in absolute
  value, everywhere (off the box it is `0` by definition; on the box, the
  budget-`0` monomials of `ofPoly` evaluate inside `[0,1]` and their
  absolute coefficients sum to `Qabs Fstar1 = 1`);
* `primorial_hDlt` — the concrete instantiation `W' = primorial D` satisfies
  the free-`(D,W')` hypothesis `∀ p prime, p ∤ W' → D < p` consumed
  throughout the `*W` lemma families (`Salt.Maynard.CollisionQuant`,
  `Salt.Maynard.Lemma53W`, ...), via mathlib's `Nat.Prime.dvd_primorial_iff`.
-/

namespace Salt.Twelve

open Salt.Maynard

/-! ## `Qabs` and the ℓ¹-normalized certificate `Fstar1` -/

/-- The ℓ¹-norm of a polynomial's coefficient list: `Σ |f_α|`. -/
def Qabs (F : Poly) : ℚ := (F.map (fun m => |m.2|)).sum

/-- The certified optimum `F★` rescaled so its coefficients sum in absolute
value to `1` (`Qabs Fstar1 = 1`, see `Qabs_Fstar1`). -/
noncomputable def Fstar1 : Poly := Fstar.map (fun m => (m.1, m.2 / Qabs Fstar))

/-! ## List-algebra scaling lemmas -/

/-- `Qabs` scales by `|c|` under a uniform coefficient rescaling. -/
private lemma Qabs_scale (F : Poly) (c : ℚ) :
    Qabs (F.map (fun m => (m.1, m.2 * c))) = Qabs F * |c| := by
  unfold Qabs
  rw [List.map_map]
  simp only [Function.comp_def, abs_mul]
  rw [List.sum_map_mul_right]

/-- The generic bilinear-in-coefficients pairing shared by `Ical` and
`Jcal m` (with kernels `fun a b => DInt (a+b)` and `fun a b => JD a b m`
respectively): `Σ_{p,q} p.2 · q.2 · ker p.1 q.1`. -/
private def biQuad (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * ker p.1 q.1)).sum)).sum

private lemma Ical_eq_biQuad (F : Poly) : Ical F = biQuad (fun a b => DInt (a + b)) F := rfl

private lemma Jcal_eq_biQuad (m : Fin 5) (F : Poly) :
    Jcal m F = biQuad (fun a b => JD a b m) F := rfl

/-- **Homogeneity.** `biQuad ker` is degree-2 homogeneous in a uniform
coefficient rescaling: this is the algebraic core of `M5_cert1` (the
`k = 5` Maynard functional is scale-invariant). -/
private lemma biQuad_scale (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) (c : ℚ) :
    biQuad ker (F.map (fun m => (m.1, m.2 * c))) = c ^ 2 * biQuad ker F := by
  unfold biQuad
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  dsimp only [Function.comp]
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  dsimp only [Function.comp]
  ring

/-- **Scaling identity for `Ical`.** -/
private lemma Ical_scale (F : Poly) (c : ℚ) :
    Ical (F.map (fun m => (m.1, m.2 * c))) = c ^ 2 * Ical F := by
  rw [Ical_eq_biQuad, Ical_eq_biQuad]
  exact biQuad_scale _ F c

/-- **Scaling identity for `Jcal`.** -/
private lemma Jcal_scale (m : Fin 5) (F : Poly) (c : ℚ) :
    Jcal m (F.map (fun n => (n.1, n.2 * c))) = c ^ 2 * Jcal m F := by
  rw [Jcal_eq_biQuad, Jcal_eq_biQuad]
  exact biQuad_scale _ F c

/-! ## `Qabs Fstar > 0` -/

/-- The concrete value of `Qabs Fstar`: the 56 monomial coefficients of `F★`
sum in absolute value to `1227` (`1 + 5·(19+28) + 10·30 + 5·15 + 20·21 +
10·19`). -/
theorem Qabs_Fstar_eq : Qabs Fstar = 1227 := by
  norm_num [Qabs, Fstar]

theorem Qabs_Fstar_pos : 0 < Qabs Fstar := by rw [Qabs_Fstar_eq]; norm_num

/-! ## `Fstar1` as a coefficient rescaling by `c = (Qabs Fstar)⁻¹` -/

private lemma Fstar1_eq_scale : Fstar1 = Fstar.map (fun m => (m.1, m.2 * (Qabs Fstar)⁻¹)) := by
  unfold Fstar1
  simp only [div_eq_mul_inv]

/-- `Qabs Fstar1 = 1`: the normalization makes the ℓ¹-norm of the
coefficients exactly `1`. -/
theorem Qabs_Fstar1 : Qabs Fstar1 = 1 := by
  rw [Fstar1_eq_scale, Qabs_scale, abs_of_pos (inv_pos.mpr Qabs_Fstar_pos)]
  exact mul_inv_cancel₀ Qabs_Fstar_pos.ne'

/-! ## `M5_cert1` -/

/-- **The transported certificate.** `Fstar1` (the ℓ¹-normalized `F★`) still
certifies `M₅ > 2`: both sides of `M5_cert` scale by `(Qabs Fstar)⁻²` under
the rescaling, so the strict inequality survives (multiplying through by
the positive square). No re-run of the 3136-monomial `norm_num`. -/
theorem M5_cert1 : 2 * Ical Fstar1 < ∑ m : Fin 5, Jcal m Fstar1 := by
  set c : ℚ := (Qabs Fstar)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr Qabs_Fstar_pos
  have hc2pos : 0 < c ^ 2 := by positivity
  have hI : Ical Fstar1 = c ^ 2 * Ical Fstar := by rw [Fstar1_eq_scale]; exact Ical_scale Fstar c
  have hJ : ∀ m : Fin 5, Jcal m Fstar1 = c ^ 2 * Jcal m Fstar := by
    intro m; rw [Fstar1_eq_scale]; exact Jcal_scale m Fstar c
  have hJsum : ∑ m : Fin 5, Jcal m Fstar1 = c ^ 2 * ∑ m : Fin 5, Jcal m Fstar := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => hJ m)
  rw [hI, hJsum]
  calc 2 * (c ^ 2 * Ical Fstar) = c ^ 2 * (2 * Ical Fstar) := by ring
    _ < c ^ 2 * (∑ m : Fin 5, Jcal m Fstar) := mul_lt_mul_of_pos_left M5_cert hc2pos

/-! ## `yF_Fstar1_abs_le_one` -/

/-- `eval (ofPoly F) t` as a `t`-monomial `List.sum` (the budget power is `0`
for `ofPoly`, so the `(1 − Σt)^d` factor collapses to `1`). -/
private lemma eval_ofPoly' (F : Poly) (t : Fin 5 → ℝ) :
    eval (ofPoly F) t = (F.map (fun a => (a.2 : ℝ) * ∏ i, t i ^ a.1 i)).sum := by
  simp only [eval, ofPoly, List.map_map, Function.comp_def, pow_zero, mul_one]

/-- Triangle inequality for a `List.sum` of reals. -/
private lemma fn_list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

/-- Monotonicity of `List.sum` under a pointwise `≤`. -/
private lemma fn_list_sum_le_sum {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The `ℚ → ℝ` cast of `Qabs F` as an explicit `ℝ`-valued `List.sum`. -/
private lemma Qabs_cast (F : Poly) :
    ((Qabs F : ℚ) : ℝ) = (F.map (fun m => |(m.2 : ℝ)|)).sum := by
  unfold Qabs
  rw [Rat.cast_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
  simp only [Function.comp_apply, Rat.cast_abs]

/-- **The uniform budget-`0` monomial bound.** For any `F`, if `t ∈ [0,1]^5`
pointwise, `|eval (ofPoly F) t| ≤ Qabs F` (as a real number). -/
private lemma eval_ofPoly_abs_le (F : Poly) (t : Fin 5 → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    |eval (ofPoly F) t| ≤ ((Qabs F : ℚ) : ℝ) := by
  rw [eval_ofPoly', Qabs_cast]
  refine le_trans (fn_list_abs_sum_le F _) (fn_list_sum_le_sum F _ _ (fun a _ => ?_))
  have hprod0 : 0 ≤ ∏ i, t i ^ a.1 i := Finset.prod_nonneg (fun i _ => pow_nonneg (ht0 i) _)
  have hprod1 : ∏ i, t i ^ a.1 i ≤ 1 :=
    Finset.prod_le_one (fun i _ => pow_nonneg (ht0 i) _) (fun i _ => pow_le_one₀ (ht0 i) (ht1 i))
  rw [abs_mul, abs_of_nonneg hprod0]
  calc |(a.2 : ℝ)| * ∏ i, t i ^ a.1 i ≤ |(a.2 : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left hprod1 (abs_nonneg _)
    _ = |(a.2 : ℝ)| := mul_one _

/-- **The uniform `|yF| ≤ 1` bound (card W4-4 deliverable).** Off the sieve
box `yF` vanishes; on the box, `t i = log(s i)/log R ∈ [0,1]` (each
coordinate is `< R` and `≥ 1`, forcing `R ≥ 2` so `log R > 0`), so the
budget-`0` monomial bound applies with `Qabs Fstar1 = 1`. -/
theorem yF_Fstar1_abs_le_one (R W' : ℕ) (s : Fin 5 → ℕ) :
    |yF R W' Fstar1 s| ≤ 1 := by
  unfold yF
  split_ifs with hs
  · have hs0lt : s 0 < R := kSieveIndex_coord_lt hs 0
    have hs0pos : 0 < s 0 := kSieveIndex_coord_pos hs 0
    have hR2 : 2 ≤ R := by omega
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR2.trans_lt' (by norm_num)
    have hLpos : 0 < Real.log R := Real.log_pos hR1
    have ht0 : ∀ i, 0 ≤ Real.log (s i) / Real.log R := by
      intro i
      have hsipos : 0 < s i := kSieveIndex_coord_pos hs i
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hsipos)) hLpos.le
    have ht1 : ∀ i, Real.log (s i) / Real.log R ≤ 1 := by
      intro i
      have hsipos : 0 < s i := kSieveIndex_coord_pos hs i
      have hsilt : s i < R := kSieveIndex_coord_lt hs i
      rw [div_le_one hLpos]
      exact Real.log_le_log (by exact_mod_cast hsipos) (by exact_mod_cast hsilt.le)
    calc |eval (ofPoly Fstar1) (fun i => Real.log (s i) / Real.log R)|
        ≤ ((Qabs Fstar1 : ℚ) : ℝ) := eval_ofPoly_abs_le Fstar1 _ ht0 ht1
      _ = 1 := by rw [Qabs_Fstar1]; norm_num
  · simp

/-! ## `primorial_hDlt` -/

/-- **Instantiation at `W' = primorial D`.** Every prime not dividing
`primorial D` exceeds `D`, since `primorial D` already contains every prime
`≤ D` (`Nat.Prime.dvd_primorial_iff`). This is the concrete witness for the
free-`(D,W')` hypothesis `hDp : ∀ p, p.Prime → ¬p ∣ W' → D < p` threaded
through the `*W` lemma families, at the endgame instantiation `W' =
primorial D`. -/
theorem primorial_hDlt (D : ℕ) :
    ∀ p : ℕ, p.Prime → ¬p ∣ primorial D → D < p := by
  intro p hp hnd
  by_contra hle
  push Not at hle
  exact hnd (hp.dvd_primorial_iff.mpr hle)

end Salt.Twelve
