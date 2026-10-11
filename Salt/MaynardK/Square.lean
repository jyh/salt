/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Basis

/-!
# C1 glue — Maynard's `F` and `F²` as symbolic budget polynomials; `Iform` is `simplexInt (F²)`

For a coefficient list `cs` over the basis `(b, c) ↦ (1 − P₁)^b · P₂^c`, `Fpoly k cs` is `F` and
`Fsq k cs` is the pairwise expansion of `F²`, each a concatenation of scaled `basisPoly`s (symbolic
lists, never evaluated). `eval_Fsq`: `eval (Fsq k cs) = (eval (Fpoly k cs))²` pointwise;
`simplexInt_Fsq`: its Dirichlet integral is the double sum of closed forms; `Iform_eq`: the
certificate's `Iform` (`Cert105`) IS `simplexInt (Fsq 105 F)`.
-/

open Finset Nat Salt.Twelve PowerSeries

namespace Salt.MaynardK

/-- scale every coefficient of a budget polynomial. -/
def scale {k : ℕ} (a : ℚ) (P : BPoly k) : BPoly k := P.map fun m => (m.1, m.2.1, a * m.2.2)

lemma eval_append {k : ℕ} (p q : BPoly k) (t : Fin k → ℝ) :
    eval (p ++ q) t = eval p t + eval q t := by
  simp only [eval, List.map_append, List.sum_append]

lemma eval_scale {k : ℕ} (a : ℚ) (P : BPoly k) (t : Fin k → ℝ) :
    eval (scale a P) t = (a : ℝ) * eval P t := by
  unfold eval scale
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
  simp only [Function.comp_apply]; push_cast; ring

lemma simplexInt_scale {k : ℕ} (a : ℚ) (P : BPoly k) :
    simplexInt (scale a P) = a * simplexInt P := by
  unfold simplexInt scale
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
  simp only [Function.comp_apply]; ring

lemma eval_flatMap {k : ℕ} {γ : Type*} (l : List γ) (f : γ → BPoly k) (t : Fin k → ℝ) :
    eval (l.flatMap f) t = (l.map fun x => eval (f x) t).sum := by
  induction l with
  | nil => simp [eval]
  | cons a l ih => rw [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

lemma simplexInt_flatMap {k : ℕ} {γ : Type*} (l : List γ) (f : γ → BPoly k) :
    simplexInt (l.flatMap f) = (l.map fun x => simplexInt (f x)).sum := by
  induction l with
  | nil => simp [simplexInt]
  | cons a l ih => rw [List.flatMap_cons, simplexInt_append, ih, List.map_cons, List.sum_cons]

lemma list_sum_mul_sum {γ : Type*} (l : List γ) (f g : γ → ℝ) :
    (l.map f).sum * (l.map g).sum = (l.map fun x => (l.map fun y => f x * g y).sum).sum := by
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [← List.sum_map_mul_left]

/-- `F = Σ a_{bc} (1 − P₁)^b P₂^c`. -/
noncomputable def Fpoly (k : ℕ) (cs : List ((ℕ × ℕ) × ℤ)) : BPoly k :=
  cs.flatMap fun x => scale (x.2 : ℚ) (basisPoly k x.1.1 x.1.2)

/-- `F²`, expanded pairwise. -/
noncomputable def Fsq (k : ℕ) (cs : List ((ℕ × ℕ) × ℤ)) : BPoly k :=
  cs.flatMap fun x => cs.flatMap fun y =>
    scale ((x.2 * y.2 : ℤ) : ℚ) (basisPoly k (x.1.1 + y.1.1) (x.1.2 + y.1.2))

theorem eval_Fsq (k : ℕ) (cs : List ((ℕ × ℕ) × ℤ)) (t : Fin k → ℝ) :
    eval (Fsq k cs) t = eval (Fpoly k cs) t ^ 2 := by
  unfold Fsq Fpoly
  rw [eval_flatMap, eval_flatMap, pow_two, list_sum_mul_sum]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [eval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  simp only [eval_scale, eval_basisPoly]
  push_cast; ring

/-- the closed form of `∫_{R_k} (1 − P₁)^b P₂^c`. -/
noncomputable def closed (k b c : ℕ) : ℚ :=
  ((b ! : ℕ) : ℚ) * (c ! : ℕ) * coeff c (G ^ k) / ((k + b + 2 * c)! : ℕ)

theorem simplexInt_Fsq (k : ℕ) (cs : List ((ℕ × ℕ) × ℤ)) :
    simplexInt (Fsq k cs) = (cs.map fun x => (cs.map fun y =>
      ((x.2 * y.2 : ℤ) : ℚ) * closed k (x.1.1 + y.1.1) (x.1.2 + y.1.2)).sum).sum := by
  unfold Fsq
  rw [simplexInt_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [simplexInt_flatMap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  rw [simplexInt_scale, simplexInt_basisPoly, closed]

lemma intg_eq_closed (k b c : ℕ) (hc : c < 12) : intg (T k) k b c = closed k b c := by
  unfold intg closed
  push_cast
  rw [T_eq_coeff k c hc]

lemma F_c_le : ∀ x ∈ F, x.1.2 ≤ 5 := by decide

/-- **The certificate's `I` is the Dirichlet integral of `F²`.** -/
theorem Iform_eq : Iform = simplexInt (Fsq 105 F) := by
  rw [simplexInt_Fsq]
  unfold Iform
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
  rw [← T105_eq, intg_eq_closed _ _ _ (by have := F_c_le x hx; have := F_c_le y hy; omega)]

end Salt.MaynardK
