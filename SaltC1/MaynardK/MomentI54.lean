/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Series54

/-!
# C1 · A2d (b), (d) — the `I` value table and the `I` form

(b) `WItree_eq`: on every `(A, C)` with `A + weight C ≤ 46`, `WItree` holds
`closedM 13 54 A C · 100!` (from `wi_ok`, `checkWI`'s equation, `p54T_eq` and `factT_eq`).

(d) `Iint_eq_IformM`: `Iint = 100! · IformM 13 54 cs54`. `Iint` is the sum of the 130 row blocks
`Ihalf`, which together are the symmetric half of `Σ_{i,j} c_i c_j WI(k_i + k_j)` over the 1236
rows (`Iint_eq_sum`, `half_sum_eq`); the keys add without carry into
`encKey (a_i + a_j) (C_i + C_j)` (`encKey_ofFn_add`), a key of `WItree_eq`'s range because every
basis entry has `a + weight C ≤ 23`.
Every structural fact is a generic lemma; the data enter only through committed theorems. Nothing
here bears on twin primes.
-/

open Finset
open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

attribute [local irreducible] coefBT cs54L factT p54T WItree

/-! ## Generic sums -/

lemma sum_range_list {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The symmetric half of a symmetric double sum. -/
lemma half_sum_eq {β : Type*} [CommRing β] (n : ℕ) (f : ℕ → ℕ → β) (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ range n, (f i i + 2 * ∑ j ∈ Ico (i + 1) n, f i j)
      = ∑ i ∈ range n, ∑ j ∈ range n, f i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ i ∈ range n, f i i + 2 * ∑ j ∈ Ico (i + 1) (n + 1), f i j
        = (f i i + 2 * ∑ j ∈ Ico (i + 1) n, f i j) + 2 * f i n := by
      intro i hi
      rw [Finset.sum_Ico_succ_top (by have := Finset.mem_range.mp hi; omega)]
      ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih,
      Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    have h2 : ∑ j ∈ range n, f n j = ∑ i ∈ range n, f i n :=
      Finset.sum_congr rfl fun j _ => hf n j
    rw [h2]
    ring

/-! ## (b) The `I` value table -/

/-- **`WItree` is `closedM 13 54 · 100!` on `A + weight C ≤ 46`.** -/
theorem WItree_eq (A : ℕ) (C : Fin 13 → ℕ) (h : A + weight C ≤ 46) :
    ((WItree.findB (encKey A (List.ofFn C)) : ℤ) : ℚ) = closedM 13 54 A C * ((100 ! : ℕ) : ℚ) := by
  have hmem : (A, List.ofFn C) ∈ wiEntries := by
    unfold wiEntries
    rw [List.mem_flatMap]
    refine ⟨List.ofFn C, mem_keysW.mpr (by omega), List.mem_map.mpr ⟨A, ?_, rfl⟩⟩
    rw [List.mem_range, wt_ofFn]
    omega
  have hc := (List.all_eq_true.mp wi_ok) _ hmem
  unfold checkWI at hc
  simp only at hc
  rw [beq_iff_eq, wt_ofFn, factT_eq _ (by omega), factT_eq _ (by omega), factT_eq _ (by omega),
    facProd_ofFn_eq C (fun m => by have := two_mul_le_weight C m; omega)] at hc
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  push_cast at hq
  rw [p54T_eq' C (by omega)] at hq
  unfold closedM
  have hD : (((54 + A + weight C)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hD, hq]

/-! ## (d) The `I` form -/

/-- One row of `Ihalf`. -/
noncomputable def rowI (i : ℕ) : ℤ :=
  (coefBT.getB i).2 * (coefBT.getB i).2 * WItree.findB (2 * (coefBT.getB i).1) +
    2 * ∑ j ∈ Ico (i + 1) nB,
      (coefBT.getB i).2 * (coefBT.getB j).2 * WItree.findB ((coefBT.getB i).1 + (coefBT.getB j).1)

lemma Ihalf_eq (i0 i1 : ℕ) : Ihalf i0 i1 = ∑ i ∈ Ico i0 i1, rowI i := by
  unfold Ihalf
  rw [foldl_add_of _ (fun ii => rowI (i0 + ii)) ?_ _ 0, zero_add, sum_range_list,
    Finset.sum_Ico_eq_sum_range]
  intro acc ii
  unfold rowI
  dsimp only
  generalize coefBT.getB (i0 + ii) = q
  obtain ⟨ki, ci⟩ := q
  dsimp only
  rw [foldl_add_of _ (fun jj => ci * (coefBT.getB (i0 + ii + 1 + jj)).2 *
      WItree.findB (ki + (coefBT.getB (i0 + ii + 1 + jj)).1)) ?_ _ 0, zero_add, sum_range_list,
    Finset.sum_Ico_eq_sum_range, show nB - (i0 + ii) - 1 = nB - (i0 + ii + 1) by omega]
  · ring
  · intro acc2 jj
    dsimp only

lemma Iint_eq_sum : Iint = ∑ i ∈ range 1236, rowI i := by
  unfold Iint
  simp only [Ihalf_eq]
  repeat rw [Finset.sum_Ico_consecutive _ (by norm_num) (by norm_num)]
  rw [Finset.range_eq_Ico]

/-- The row's two lookups, in the Lean side's terms. -/
lemma coefBT_getB' {i : ℕ} (hi : i < 1236) :
    coefBT.getB i = (encKey (ent i).1 (List.ofFn (entC i)), (ent i).2.2) := by
  rw [coefBT_getB hi, ← ent_list hi]

/-- **The `I` form at the common scale.** -/
theorem Iint_eq_IformM : (Iint : ℚ) = ((100 ! : ℕ) : ℚ) * IformM 13 54 cs54 := by
  have hn : nB = 1236 := rfl
  have hrow : ∑ i ∈ range 1236, rowI i = ∑ i ∈ range 1236, ∑ j ∈ range 1236,
      (coefBT.getB i).2 * (coefBT.getB j).2 *
        WItree.findB ((coefBT.getB i).1 + (coefBT.getB j).1) := by
    rw [← half_sum_eq 1236 _ (fun i j => by ring_nf)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold rowI
    rw [hn, two_mul ((coefBT.getB i).1)]
  rw [Iint_eq_sum, hrow]
  unfold IformM
  rw [cs54_eq, List.map_map, list_sum_map_eq_range _ _ (0, [], 0), cs54L_length,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [Function.comp_apply, List.map_map]
  rw [list_sum_map_eq_range _ _ (0, [], 0), cs54L_length, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [show cs54L.getD i (0, [], 0) = ent i from rfl, show cs54L.getD j (0, [], 0) = ent j from rfl,
    show toF (ent i).2.1 = entC i from rfl, show toF (ent j).2.1 = entC j from rfl]
  rw [coefBT_getB' hi', coefBT_getB' hj']
  dsimp only
  rw [encKey_ofFn_add, WItree_eq _ _ (by
    rw [weight_add]; have := ent_basis hi'; have := ent_basis hj'; omega)]
  ring

end SaltC1.MaynardK
