/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.JMain

/-!
# C1 · B4.1 — the normalised weight `F1 = F / Qsum`

`Qsum = Σ |a_bc|` over the 42-term coefficient list, `F1 := scale (1/Qsum) (Fpoly 105 F)`. On the
simplex (`tᵢ ≥ 0`, `Σ t ≤ 1`) `|F1| ≤ 1` (`eval_F1_abs_le_one`). Its two Dirichlet integrals are
the certificate's numbers over `Qsum²`: `simplexInt (sq F1) = Iform / Qsum²` (through
`simplexInt_sq_Fpoly`, which turns the list square `sq` into the pairwise expansion `Fsq` by the
multinomial convolution) and `simplexInt (sq (contractB m F1)) = Jform / Qsum²` at every `m`.
-/

open Finset Salt.Twelve
open scoped Nat

namespace Salt.MaynardK

/-- the `ℓ¹` norm of the coefficient list. -/
def Qsum : ℚ := (F.map fun x => |(x.2 : ℚ)|).sum

lemma Qsum_pos : 0 < Qsum := by decide +kernel

/-- the normalised Maynard weight. -/
noncomputable def F1 : BPoly 105 := scale (1 / Qsum) (Fpoly 105 F)

/-! ## the pointwise bound -/

lemma eval_Fpoly {k : ℕ} (cs : List ((ℕ × ℕ) × ℤ)) (t : Fin k → ℝ) :
    eval (Fpoly k cs) t
      = (cs.map fun x => (x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 * (∑ i, t i ^ 2) ^ x.1.2)).sum := by
  unfold Fpoly
  rw [eval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [eval_scale, eval_basisPoly]; push_cast; ring

lemma basis_val_bounds {k : ℕ} (t : Fin k → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1) (b c : ℕ) :
    0 ≤ (1 - ∑ i, t i) ^ b * (∑ i, t i ^ 2) ^ c ∧ (1 - ∑ i, t i) ^ b * (∑ i, t i ^ 2) ^ c ≤ 1 := by
  have hs0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht0 i
  have hq0 : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq1 : ∑ i, t i ^ 2 ≤ 1 := by
    calc ∑ i, t i ^ 2 ≤ (∑ i, t i) ^ 2 := by
          rw [_root_.sq, Finset.sum_mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [_root_.sq]
          exact Finset.single_le_sum (f := fun j => t i * t j)
            (fun j _ => mul_nonneg (ht0 i) (ht0 j)) (Finset.mem_univ i)
      _ ≤ 1 := by nlinarith
  have hb0 : 0 ≤ 1 - ∑ i, t i := by linarith
  have hb1 : 1 - ∑ i, t i ≤ 1 := by linarith
  exact ⟨mul_nonneg (pow_nonneg hb0 _) (pow_nonneg hq0 _),
    mul_le_one₀ (pow_le_one₀ hb0 hb1) (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1)⟩

lemma eval_Fpoly_abs_le {k : ℕ} (cs : List ((ℕ × ℕ) × ℤ)) (t : Fin k → ℝ) (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∑ i, t i ≤ 1) :
    |eval (Fpoly k cs) t| ≤ (cs.map fun x => |(x.2 : ℝ)|).sum := by
  rw [eval_Fpoly]
  induction cs with
  | nil => simp
  | cons x cs ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨h0, h1⟩ := basis_val_bounds t ht0 ht1 x.1.1 x.1.2
    calc |(x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 * (∑ i, t i ^ 2) ^ x.1.2)
          + (cs.map fun x => (x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 * (∑ i, t i ^ 2) ^ x.1.2)).sum|
        ≤ |(x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 * (∑ i, t i ^ 2) ^ x.1.2)|
          + |(cs.map fun x => (x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 * (∑ i, t i ^ 2) ^ x.1.2)).sum| :=
          abs_add_le _ _
      _ ≤ |(x.2 : ℝ)| + (cs.map fun x => |(x.2 : ℝ)|).sum := by
          refine add_le_add ?_ ih
          rw [abs_mul, abs_of_nonneg h0]
          exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- **`|F1| ≤ 1` on the simplex.** -/
theorem eval_F1_abs_le_one (t : Fin 105 → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1) :
    |eval F1 t| ≤ 1 := by
  unfold F1
  rw [eval_scale, abs_mul]
  have hQ : ((Qsum : ℚ) : ℝ) = (F.map fun x => |(x.2 : ℝ)|).sum := by
    unfold Qsum
    rw [Rat.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    simp
  have hQpos : (0 : ℝ) < (Qsum : ℝ) := by exact_mod_cast Qsum_pos
  have hb := eval_Fpoly_abs_le F t ht0 ht1
  rw [← hQ] at hb
  push_cast
  rw [abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hQpos, mul_one]
  exact hb

/-! ## the two integrals -/

lemma simplexInt_sq_scale {k : ℕ} (a : ℚ) (P : BPoly k) :
    simplexInt (sq (scale a P)) = a ^ 2 * simplexInt (sq P) := by
  rw [Salt.Twelve.sq, Salt.Twelve.sq, simplexInt_mul, simplexInt_mul]
  unfold scale
  simp only [List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  ring

lemma contractB_scale {n : ℕ} (m : Fin (n + 1)) (a : ℚ) (P : BPoly (n + 1)) :
    contractB m (scale a P) = scale a (contractB m P) := by
  unfold contractB scale
  simp only [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  ring

lemma Fpoly_eq {k : ℕ} (cs : List ((ℕ × ℕ) × ℤ)) :
    Fpoly k cs = cs.flatMap fun x => (piAntidiag (univ : Finset (Fin k)) x.1.2).toList.map fun e =>
      ((fun i => 2 * e i), x.1.1, (x.2 : ℚ) * (Nat.multinomial univ e : ℕ)) := by
  unfold Fpoly scale basisPoly
  refine List.flatMap_congr fun x _ => ?_
  simp only [List.map_map]
  rfl

/-- the list square of `Fpoly` has the same Dirichlet integral as its pairwise expansion `Fsq`. -/
theorem simplexInt_sq_Fpoly {k : ℕ} (cs : List ((ℕ × ℕ) × ℤ)) :
    simplexInt (sq (Fpoly k cs)) = simplexInt (Fsq k cs) := by
  rw [simplexInt_Fsq, Fpoly_eq, Salt.Twelve.sq, simplexInt_mul]
  simp only [list_sum_flatMap, List.map_map, Function.comp_def, Finset.sum_map_toList]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [finset_list_swap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  have hconv := mult_conv (k := k) x.1.2 y.1.2 (fun h => DInt' (fun i => 2 * h i) (x.1.1 + y.1.1))
  rw [sum_mult_DInt] at hconv
  have h1 : ∀ e ∈ piAntidiag (univ : Finset (Fin k)) x.1.2,
      ∑ f ∈ piAntidiag (univ : Finset (Fin k)) y.1.2,
        (x.2 : ℚ) * (Nat.multinomial univ e : ℕ) * ((y.2 : ℚ) * (Nat.multinomial univ f : ℕ))
          * DInt' ((fun i => 2 * e i) + fun i => 2 * f i) (x.1.1 + y.1.1)
      = ((x.2 * y.2 : ℤ) : ℚ) * ∑ f ∈ piAntidiag (univ : Finset (Fin k)) y.1.2,
          ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ f : ℕ)
            * DInt' (fun i => 2 * (e + f) i) (x.1.1 + y.1.1) := by
    intro e _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hD : ((fun i => 2 * e i) + fun i => 2 * f i) = fun i => 2 * (e + f) i := by
      funext i; simp only [Pi.add_apply]; ring
    rw [hD]; push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hconv]

theorem simplexInt_sq_F1 : simplexInt (sq F1) = Iform / Qsum ^ 2 := by
  unfold F1
  rw [simplexInt_sq_scale, simplexInt_sq_Fpoly, ← Iform_eq]
  field_simp

theorem simplexInt_sq_contractB_F1 (m : Fin 105) :
    simplexInt (sq (contractB m F1)) = Jform / Qsum ^ 2 := by
  unfold F1
  rw [contractB_scale, simplexInt_sq_scale, ← Jform_eq m]
  field_simp

end Salt.MaynardK
