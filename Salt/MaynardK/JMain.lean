/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Vandermonde
import Salt.MaynardK.Square
import Salt.MaynardK.MvJGen
import Salt.MaynardK.JSide

/-!
# C1 bridge B4a — the Dirichlet integral of the contracted square of Maynard's `F`

Splitting a multi-index at the contracted coordinate (`sum_piAntidiag_split`), then collecting the
two
multinomial expansions (`mult_conv`).
-/

open Finset Salt.Twelve
open scoped Nat

namespace Salt.MaynardK
variable [Salt.Maynard.TupleChoice]

/-- the multinomial coefficient splits at a coordinate: `mult e = C(c, e m) · mult (removeNth m e)`.
-/
lemma multinomial_split {n : ℕ} (m : Fin (n + 1)) (e : Fin (n + 1) → ℕ) :
    ((Nat.multinomial univ e : ℕ) : ℚ)
      = (((∑ i, e i).choose (e m) : ℕ) : ℚ) * (Nat.multinomial univ (Fin.removeNth m e) : ℕ) := by
  have hs : ∑ i, e i = e m + ∑ i, Fin.removeNth m e i := by
    rw [Fin.sum_univ_succAbove e m]; rfl
  have hp : ∏ i, (((e i)! : ℕ) : ℚ) = (((e m)! : ℕ) : ℚ) * ∏ i,
          (((Fin.removeNth m e i)! : ℕ) : ℚ) := by
    rw [Fin.prod_univ_succAbove _ m]; rfl
  rw [multinomial_cast, multinomial_cast, hp]
  have hle : e m ≤ ∑ i, e i := by rw [hs]; exact Nat.le_add_right _ _
  have hsub : ∑ i, e i - e m = ∑ i, Fin.removeNth m e i := by omega
  have hc := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hc
  have h1 : (((e m)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (∏ i, (((Fin.removeNth m e i)! : ℕ) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (((∑ i, Fin.removeNth m e i)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast
          (Nat.factorial_pos _).ne'
  rw [← hc]; push_cast; field_simp

/-- **splitting a multi-index at coordinate `m`.** -/
theorem sum_piAntidiag_split {n : ℕ} (m : Fin (n + 1)) (c : ℕ) (Ψ : ℕ → (Fin n → ℕ) → ℚ) :
    ∑ e ∈ piAntidiag (univ : Finset (Fin (n + 1))) c,
        ((Nat.multinomial univ e : ℕ) : ℚ) * Ψ (e m) (Fin.removeNth m e)
      = ∑ j ∈ range (c + 1), ((c.choose j : ℕ) : ℚ) *
          ∑ e' ∈ piAntidiag (univ : Finset (Fin n)) (c - j),
            ((Nat.multinomial univ e' : ℕ) : ℚ) * Ψ j e' := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun e => ⟨e m, Fin.removeNth m e⟩) (fun x => Fin.insertNth m x.1 x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [mem_piAntidiag] at he
    have hs : ∑ i, e i = e m + ∑ i, Fin.removeNth m e i := by rw [Fin.sum_univ_succAbove e m]; rfl
    have hc : ∑ i, e i = c := he.1
    rw [Finset.mem_sigma, Finset.mem_range, mem_piAntidiag]
    dsimp only
    refine ⟨by omega, ?_, fun i _ => Finset.mem_univ i⟩
    change ∑ i, Fin.removeNth m e i = c - e m
    omega
  · intro x hx
    rw [Finset.mem_sigma, Finset.mem_range, mem_piAntidiag] at hx
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    have hs := Fin.sum_univ_succAbove (Fin.insertNth m x.1 x.2) m
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hs
    have h2 : ∑ i, x.2 i = c - x.1 := hx.2.1
    change ∑ i, Fin.insertNth m x.1 x.2 i = c
    rw [hs, h2]; omega
  · intro e _; exact Fin.insertNth_self_removeNth m e
  · intro x _
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  · intro e he
    rw [mem_piAntidiag] at he
    have hc : ∑ i, e i = c := he.1
    simp only
    rw [multinomial_split m e, hc]; ring

/-! ## The contracted square -/

/-- `FJ` for a general coefficient list: the uncollected `t_{n+1}`-inner integral of `Fpoly`. -/
def FJg (cs : List ((ℕ × ℕ) × ℤ)) : List ((ℕ × ℕ) × ℚ) :=
  cs.flatMap fun p => (List.range (p.1.2 + 1)).map fun j =>
    ((p.1.1 + 2 * j + 1, p.1.2 - j),
      (p.2 : ℚ) * ((p.1.2.choose j * p.1.1.factorial * (2 * j).factorial : ℕ) : ℚ) /
        ((p.1.1 + 2 * j + 1).factorial : ℕ))

lemma list_sum_range_q (f : ℕ → ℚ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma list_sum_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℚ) :
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma finset_list_swap {α ι : Type*} (S : Finset ι) (l : List α) (h : ι → α → ℚ) :
    ∑ e ∈ S, (l.map (h e)).sum = (l.map fun y => ∑ e ∈ S, h e y).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- the contraction of `Fpoly`, written out. -/
lemma contractB_Fpoly {n : ℕ} (m : Fin (n + 1)) (cs : List ((ℕ × ℕ) × ℤ)) :
    contractB m (Fpoly (n + 1) cs)
      = cs.flatMap fun x => (piAntidiag (univ : Finset (Fin (n + 1))) x.1.2).toList.map fun e =>
          (Fin.removeNth m (fun i => 2 * e i), 2 * e m + x.1.1 + 1,
            (x.2 : ℚ) * (Nat.multinomial univ e : ℕ) * (((2 * e m)! * x.1.1 ! : ℕ) : ℚ)
              / ((2 * e m + x.1.1 + 1)! : ℕ)) := by
  unfold contractB Fpoly scale basisPoly
  rw [List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  simp only [List.map_map]
  rfl

/-- `Σ_h mult h · DInt'(2h, D)` is the closed form. -/
lemma sum_mult_DInt (n D s : ℕ) :
    ∑ h ∈ piAntidiag (univ : Finset (Fin n)) s,
        ((Nat.multinomial univ h : ℕ) : ℚ) * DInt' (fun i => 2 * h i) D = closed n D s := by
  rw [closed, ← simplexInt_basisPoly]
  unfold simplexInt basisPoly
  rw [List.map_map, Finset.sum_map_toList]
  rfl

/-- split BOTH multi-indices of a double sum at coordinate `m`. -/
lemma double_split {n : ℕ} (m : Fin (n + 1)) (c c' : ℕ)
    (Φ : ℕ → (Fin n → ℕ) → ℕ → (Fin n → ℕ) → ℚ) :
    ∑ e ∈ piAntidiag (univ : Finset (Fin (n + 1))) c, ∑ f ∈ piAntidiag (univ : Finset (Fin (n
            + 1))) c',
        ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ f : ℕ)
          * Φ (e m) (Fin.removeNth m e) (f m) (Fin.removeNth m f)
      = ∑ j ∈ range (c + 1), ∑ j' ∈ range (c' + 1), ((c.choose j : ℕ) : ℚ) * (c'.choose j' : ℕ) *
          ∑ e' ∈ piAntidiag (univ : Finset (Fin n)) (c - j),
            ∑ f' ∈ piAntidiag (univ : Finset (Fin n)) (c' - j'),
              ((Nat.multinomial univ e' : ℕ) : ℚ) * (Nat.multinomial univ f' : ℕ)
                      * Φ j e' j' f' := by
  have h1 : ∀ e ∈ piAntidiag (univ : Finset (Fin (n + 1))) c,
      ∑ f ∈ piAntidiag (univ : Finset (Fin (n + 1))) c',
        ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ f : ℕ)
          * Φ (e m) (Fin.removeNth m e) (f m) (Fin.removeNth m f)
      = ((Nat.multinomial univ e : ℕ) : ℚ) *
          ∑ j' ∈ range (c' + 1), ((c'.choose j' : ℕ) : ℚ) *
            ∑ f' ∈ piAntidiag (univ : Finset (Fin n)) (c' - j'),
              ((Nat.multinomial univ f' : ℕ) : ℚ) * Φ (e m) (Fin.removeNth m e) j' f' := by
    intro e _
    rw [← sum_piAntidiag_split m c' (fun j' f' => Φ (e m) (Fin.removeNth m e) j' f'),
            Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  rw [Finset.sum_congr rfl h1, sum_piAntidiag_split m c (fun j e' =>
    ∑ j' ∈ range (c' + 1), ((c'.choose j' : ℕ) : ℚ) *
      ∑ f' ∈ piAntidiag (univ : Finset (Fin n)) (c' - j'),
        ((Nat.multinomial univ f' : ℕ) : ℚ) * Φ j e' j' f')]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  refine Finset.sum_congr rfl fun e' _ => ?_
  refine Finset.sum_congr rfl fun f' _ => ?_
  ring

/-- one basis pair of the contracted square: the double multinomial sum collapses to closed forms.
-/
lemma pair_closed {n : ℕ} (m : Fin (n + 1)) (b c b' c' : ℕ) (a a' : ℚ) :
    ∑ e ∈ piAntidiag (univ : Finset (Fin (n + 1))) c, ∑ f ∈ piAntidiag (univ : Finset (Fin (n
            + 1))) c',
        (a * (Nat.multinomial univ e : ℕ) * (((2 * e m)! * b ! : ℕ) : ℚ) / ((2 * e m + b
                + 1)! : ℕ)) *
        (a' * (Nat.multinomial univ f : ℕ) * (((2 * f m)! * b' ! : ℕ) : ℚ) / ((2 * f m + b'
                + 1)! : ℕ)) *
        DInt' (Fin.removeNth m (fun i => 2 * e i) + Fin.removeNth m (fun i => 2 * f i))
          (2 * e m + b + 1 + (2 * f m + b' + 1))
      = ∑ j ∈ range (c + 1), ∑ j' ∈ range (c' + 1),
          (a * ((c.choose j * b ! * (2 * j)! : ℕ) : ℚ) / ((b + 2 * j + 1)! : ℕ)) *
          (a' * ((c'.choose j' * b' ! * (2 * j')! : ℕ) : ℚ) / ((b' + 2 * j' + 1)! : ℕ)) *
          closed n (b + 2 * j + 1 + (b' + 2 * j' + 1)) (c - j + (c' - j')) := by
  set Φ : ℕ → (Fin n → ℕ) → ℕ → (Fin n → ℕ) → ℚ := fun j e' j' f' =>
    (a * (((2 * j)! * b ! : ℕ) : ℚ) / ((2 * j + b + 1)! : ℕ)) *
    (a' * (((2 * j')! * b' ! : ℕ) : ℚ) / ((2 * j' + b' + 1)! : ℕ)) *
    DInt' (fun i => 2 * (e' + f') i) (2 * j + b + 1 + (2 * j' + b' + 1)) with hΦ
  have hL : ∀ e ∈ piAntidiag (univ : Finset (Fin (n + 1))) c,
      ∀ f ∈ piAntidiag (univ : Finset (Fin (n + 1))) c',
      (a * (Nat.multinomial univ e : ℕ) * (((2 * e m)! * b ! : ℕ) : ℚ) / ((2 * e m + b + 1)! : ℕ)) *
        (a' * (Nat.multinomial univ f : ℕ) * (((2 * f m)! * b' ! : ℕ) : ℚ) / ((2 * f m + b'
                + 1)! : ℕ)) *
        DInt' (Fin.removeNth m (fun i => 2 * e i) + Fin.removeNth m (fun i => 2 * f i))
          (2 * e m + b + 1 + (2 * f m + b' + 1))
      = ((Nat.multinomial univ e : ℕ) : ℚ) * (Nat.multinomial univ f : ℕ)
          * Φ (e m) (Fin.removeNth m e) (f m) (Fin.removeNth m f) := by
    intro e _ f _
    have hD : Fin.removeNth m (fun i => 2 * e i) + Fin.removeNth m (fun i => 2 * f i)
        = fun i => 2 * (Fin.removeNth m e + Fin.removeNth m f) i := by
      funext i; simp only [Pi.add_apply, Fin.removeNth_apply]; ring
    rw [hD, hΦ]; ring
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun f hf => hL e he f hf,
    double_split m c c' Φ]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
  have hconv := mult_conv (k := n) (c - j) (c' - j')
    (fun h => DInt' (fun i => 2 * h i) (2 * j + b + 1 + (2 * j' + b' + 1)))
  have hΦe : ∀ e' f', Φ j e' j' f' =
      (a * (((2 * j)! * b ! : ℕ) : ℚ) / ((2 * j + b + 1)! : ℕ)) *
      (a' * (((2 * j')! * b' ! : ℕ) : ℚ) / ((2 * j' + b' + 1)! : ℕ)) *
      DInt' (fun i => 2 * (e' + f') i) (2 * j + b + 1 + (2 * j' + b' + 1)) := fun _ _ => rfl
  simp_rw [hΦe]
  have hfact : ∀ e' ∈ piAntidiag (univ : Finset (Fin n)) (c - j),
      ∑ f' ∈ piAntidiag (univ : Finset (Fin n)) (c' - j'),
        ((Nat.multinomial univ e' : ℕ) : ℚ) * (Nat.multinomial univ f' : ℕ) *
          ((a * (((2 * j)! * b ! : ℕ) : ℚ) / ((2 * j + b + 1)! : ℕ)) *
          (a' * (((2 * j')! * b' ! : ℕ) : ℚ) / ((2 * j' + b' + 1)! : ℕ)) *
          DInt' (fun i => 2 * (e' + f') i) (2 * j + b + 1 + (2 * j' + b' + 1)))
      = (a * (((2 * j)! * b ! : ℕ) : ℚ) / ((2 * j + b + 1)! : ℕ)) *
          (a' * (((2 * j')! * b' ! : ℕ) : ℚ) / ((2 * j' + b' + 1)! : ℕ)) *
        ∑ f' ∈ piAntidiag (univ : Finset (Fin n)) (c' - j'),
          ((Nat.multinomial univ e' : ℕ) : ℚ) * (Nat.multinomial univ f' : ℕ) *
            DInt' (fun i => 2 * (e' + f') i) (2 * j + b + 1 + (2 * j' + b' + 1)) := by
    intro e' _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun f' _ => by ring
  rw [Finset.sum_congr rfl hfact, ← Finset.mul_sum, hconv, sum_mult_DInt]
  have hB : 2 * j + b + 1 + (2 * j' + b' + 1) = b + 2 * j + 1 + (b' + 2 * j' + 1) := by ring
  have h1 : 2 * j + b + 1 = b + 2 * j + 1 := by ring
  have h2 : 2 * j' + b' + 1 = b' + 2 * j' + 1 := by ring
  rw [hB, h1, h2]
  push_cast; ring

/-- **B4a core:** the Dirichlet integral of the contracted square of `Fpoly`. -/
theorem simplexInt_sq_contractB {n : ℕ} (m : Fin (n + 1)) (cs : List ((ℕ × ℕ) × ℤ)) :
    simplexInt (sq (contractB m (Fpoly (n + 1) cs)))
      = ((FJg cs).map fun u => ((FJg cs).map fun v =>
          u.2 * v.2 * closed n (u.1.1 + v.1.1) (u.1.2 + v.1.2)).sum).sum := by
  rw [contractB_Fpoly, Salt.Twelve.sq, simplexInt_mul]
  unfold FJg
  simp only [list_sum_flatMap, List.map_map, Function.comp_def, Finset.sum_map_toList,
    list_sum_range_q]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [finset_list_swap, finset_list_swap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  exact pair_closed m x.1.1 x.1.2 y.1.1 y.1.2 x.2 y.2

lemma FJ_c_le : ∀ u ∈ FJ, u.1.2 ≤ 5 := by decide

/-- **B4a: the certificate's `J` is the Dirichlet integral of the contracted square of `F`, at EVERY
coordinate.** -/
theorem Jform_eq (m : Fin 105) : Jform = simplexInt (sq (contractB m (Fpoly 105 F))) := by
  rw [simplexInt_sq_contractB, Jform_eq_J2]
  have hFJ : FJ = FJg F := rfl
  unfold J2
  rw [hFJ]
  refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
  refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
  rw [← hFJ] at hu hv
  rw [← T104_eq, intg_eq_closed _ _ _ (by have := FJ_c_le u hu; have := FJ_c_le v hv; omega)]

end Salt.MaynardK
