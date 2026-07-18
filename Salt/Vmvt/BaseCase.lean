/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Defs

/-!
# The base case of the Vinogradov mean-value bound

This file ports the **base case** `J_k(A, b) ≤ b! · |A|^b` for `b ≤ k`
(Vaughan PSU Chapter 24, Lemmas 24.2(i) and 24.3).

## The keystone (Lemma 24.2(i))

The load-bearing fact is that *equal power sums up to the tuple length force a
permutation*: if two `b`-tuples `m, n : Fin b → ℤ` have `∑_q (m q)^j = ∑_q (n q)^j`
for every `j = 1, …, b`, then the value multisets `univ.val.map m` and
`univ.val.map n` are equal (`multiset_map_eq_of_powerSum_eq`), and hence `n` is a
permutation of `m` (`exists_perm_of_powerSum_eq`).

## Route (everything over `ℤ`)

The proof stays entirely over the integers.  Newton's identity
`MvPolynomial.mul_esymm_eq_sum` only *multiplies* the `k`-th elementary symmetric
function by `k`, so we cancel `k` in the integral domain `ℤ` (`k ≥ 1`) instead of
dividing over `ℚ` — no field of fractions is needed.

* Evaluate Newton's identity at the tuple via `aeval`, landing on
  `Multiset.esymm` through `MvPolynomial.aeval_esymm_eq_multiset_esymm`.
* Equal power sums `p_1, …, p_b` give equal `Multiset.esymm e_0, …, e_b` by
  strong induction (`esymm_eq_of_powerSum_eq`).
* Equal `esymm` give equal characteristic polynomials
  `∏ (X - C x)` (Vieta, `Multiset.prod_X_sub_X_eq_sum_esymm`), hence equal root
  multisets (`Polynomial.roots_multiset_prod_X_sub_C`).

## The count (Lemma 24.3)

Fibring the solution set over the first coordinate and using that each fibre
injects into `Equiv.Perm (Fin b)` (of cardinality `b!`) gives
`Jk_le_of_le : Jk k b A ≤ b! · |A|^b` for `b ≤ k`, with the interval corollary
`JkI_le`.
-/

namespace Salt.Vmvt

open Finset Polynomial

/-- Evaluating the multivariate power sum `psum` at a tuple `x` gives the ordinary
power sum `∑ i, (x i)^n`. -/
lemma aeval_psum {b : ℕ} (x : Fin b → ℤ) (n : ℕ) :
    MvPolynomial.aeval x (MvPolynomial.psum (Fin b) ℤ n) = ∑ i, (x i) ^ n := by
  simp [MvPolynomial.psum, map_sum]

/-- The zeroth elementary symmetric function of any multiset is `1`. -/
lemma esymm_zero' (s : Multiset ℤ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/-- **Newton's identities, evaluated (Lemma 24.2 core).**  Equal power sums up to
degree `b` force equal `Multiset.esymm` of the value multisets up to degree `b`.

Proof by strong induction on `k`: the Newton recurrence `k · e_k = …` (obtained
by evaluating `MvPolynomial.mul_esymm_eq_sum` at the tuple) expresses `e_k` from
lower `e`'s (handled by the induction hypothesis) and power sums `p_{k-i}` with
`1 ≤ k - i ≤ k ≤ b` (handled by the assumption); cancelling `k ≥ 1` over `ℤ`
finishes. -/
lemma esymm_eq_of_powerSum_eq {b : ℕ} {m n : Fin b → ℤ}
    (h : ∀ j ∈ Finset.Icc 1 b, ∑ i, (m i) ^ j = ∑ i, (n i) ^ j) :
    ∀ k, k ≤ b → (Finset.univ.val.map m).esymm k = (Finset.univ.val.map n).esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [esymm_zero', esymm_zero']
    · have Hm := congrArg (MvPolynomial.aeval m) (MvPolynomial.mul_esymm_eq_sum (Fin b) ℤ k)
      have Hn := congrArg (MvPolynomial.aeval n) (MvPolynomial.mul_esymm_eq_sum (Fin b) ℤ k)
      simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, aeval_psum] at Hm Hn
      have key : (k : ℤ) * (univ.val.map m).esymm k = (k : ℤ) * (univ.val.map n).esymm k := by
        rw [Hm, Hn]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
        obtain ⟨hsum, hlt⟩ := ha
        rw [IH a.1 hlt (by omega), h a.2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hkpos.ne') key

/-- **Lemma 24.2(i), multiset form (the keystone).**  If two `b`-tuples have equal
power sums for every degree `1 ≤ j ≤ b`, then their value multisets are equal. -/
lemma multiset_map_eq_of_powerSum_eq {b : ℕ} {m n : Fin b → ℤ}
    (h : ∀ j ∈ Finset.Icc 1 b, ∑ i, (m i) ^ j = ∑ i, (n i) ^ j) :
    Finset.univ.val.map m = Finset.univ.val.map n := by
  have hE := esymm_eq_of_powerSum_eq h
  set S := Finset.univ.val.map m with hS
  set T := Finset.univ.val.map n with hT
  have hcardS : Multiset.card S = b := by rw [hS]; simp
  have hcardT : Multiset.card T = b := by rw [hT]; simp
  have hpoly : (S.map fun a => X - C a).prod = (T.map fun a => X - C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcardS, hcardT]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    rw [hE j hj]
  have hroots := congrArg Polynomial.roots hpoly
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots

/-- The value multiset of a tuple equals the coercion of its `List.ofFn`. -/
lemma coe_ofFn_eq_map_univ {b : ℕ} (f : Fin b → ℤ) :
    (↑(List.ofFn f) : Multiset ℤ) = Finset.univ.val.map f := by
  simp only [List.ofFn_eq_map, Finset.val_univ_fin, Multiset.map_coe]

/-- **The permutation bridge.**  Two tuples with equal value multisets differ by a
permutation of the index set.  Constructed by sorting both tuples (`Tuple.sort`):
the sorted rearrangements are monotone lists with equal underlying multiset, hence
equal (`List.Perm.eq_of_sortedLE`); composing the two sorting permutations yields
the required `σ`. -/
lemma perm_of_map_univ_eq {b : ℕ} {m n : Fin b → ℤ}
    (h : Finset.univ.val.map m = Finset.univ.val.map n) :
    ∃ σ : Equiv.Perm (Fin b), n = m ∘ σ := by
  set σm := Tuple.sort m with hσm
  set σn := Tuple.sort n with hσn
  have hmono_m : Monotone (m ∘ σm) := Tuple.monotone_sort m
  have hmono_n : Monotone (n ∘ σn) := Tuple.monotone_sort n
  -- sorting preserves the value multiset
  have hval : Finset.univ.val.map (m ∘ σm) = Finset.univ.val.map (n ∘ σn) := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, ← Multiset.map_map,
      Multiset.map_univ_val_equiv, h]
  -- the sorted lists are equal
  have hlist : List.ofFn (m ∘ σm) = List.ofFn (n ∘ σn) := by
    refine List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hmono_m)
      (List.sortedLE_ofFn_iff.mpr hmono_n) ?_
    rw [← Multiset.coe_eq_coe, coe_ofFn_eq_map_univ, coe_ofFn_eq_map_univ, hval]
  have hfun : m ∘ σm = n ∘ σn := List.ofFn_injective hlist
  refine ⟨σm * σn⁻¹, funext fun i => ?_⟩
  have hi := congrFun hfun (σn⁻¹ i)
  have hcancel : σn (σn⁻¹ i) = i := σn.apply_symm_apply i
  simp only [Function.comp_apply, hcancel] at hi
  simp only [Function.comp_apply, Equiv.Perm.mul_apply]
  exact hi.symm

/-- **Lemma 24.2(i), permutation form.**  Equal power sums up to degree `b` force
`n` to be a permutation of `m`. -/
theorem exists_perm_of_powerSum_eq {b : ℕ} {m n : Fin b → ℤ}
    (h : ∀ j ∈ Finset.Icc 1 b, ∑ i, (m i) ^ j = ∑ i, (n i) ^ j) :
    ∃ σ : Equiv.Perm (Fin b), n = m ∘ σ :=
  perm_of_map_univ_eq (multiset_map_eq_of_powerSum_eq h)

/-- **Lemma 24.3, the base case.**  For `b ≤ k`, the Vinogradov count is bounded by
`b! · |A|^b`.  For each fixed first tuple `m`, the admissible second tuples `n` are
permutations of `m`, of which there are at most `b!`; summing over `m ∈ A^b` gives
the bound. -/
theorem Jk_le_of_le {k b : ℕ} (A : Finset ℤ) (hbk : b ≤ k) :
    Jk k b A ≤ b.factorial * A.card ^ b := by
  -- each fibre over the first coordinate has at most `b!` elements
  have hbound : ∀ m : Fin b → ℤ,
      ((solSet k b A).filter fun mn => mn.1 = m).card ≤ b.factorial := by
    intro m
    calc ((solSet k b A).filter fun mn => mn.1 = m).card
        ≤ (Finset.image
            (fun σ : Equiv.Perm (Fin b) => ((m, m ∘ σ) : (Fin b → ℤ) × (Fin b → ℤ)))
            Finset.univ).card := by
          apply Finset.card_le_card
          intro mn hmn
          rw [Finset.mem_filter, mem_solSet] at hmn
          obtain ⟨⟨_, _, hpred⟩, hfst⟩ := hmn
          obtain ⟨σ, hσ⟩ := exists_perm_of_powerSum_eq (m := mn.1) (n := mn.2)
            (fun j hj => hpred j (Finset.Icc_subset_Icc_right hbk hj))
          rw [Finset.mem_image]
          exact ⟨σ, Finset.mem_univ _, Prod.ext hfst.symm (by rw [hσ, hfst])⟩
      _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin b))).card := Finset.card_image_le
      _ = b.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- sum the fibre bound over the first coordinate
  have hfiber : Jk k b A =
      ∑ m ∈ Fintype.piFinset fun _ : Fin b => A,
        ((solSet k b A).filter fun mn => mn.1 = m).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro mn hmn
    simp only [Finset.mem_coe] at hmn ⊢
    rw [mem_solSet] at hmn
    exact Fintype.mem_piFinset.mpr hmn.1
  rw [hfiber]
  calc ∑ m ∈ Fintype.piFinset fun _ : Fin b => A,
          ((solSet k b A).filter fun mn => mn.1 = m).card
      ≤ ∑ _m ∈ Fintype.piFinset fun _ : Fin b => A, b.factorial :=
        Finset.sum_le_sum fun m _ => hbound m
    _ = b.factorial * A.card ^ b := by
        rw [Finset.sum_const, Fintype.card_piFinset_const, smul_eq_mul, Nat.mul_comm]

/-- **Interval corollary.**  `J_k((0, x], b) ≤ b! · x^b` for `b ≤ k`. -/
theorem JkI_le {k b : ℕ} (x : ℕ) (hbk : b ≤ k) :
    JkI k b x ≤ b.factorial * x ^ b := by
  have hcard : (Finset.Ioc (0 : ℤ) (x : ℤ)).card = x := by
    rw [Int.card_Ioc]; simp
  have := Jk_le_of_le (k := k) (b := b) (Finset.Ioc (0 : ℤ) (x : ℤ)) hbk
  rwa [hcard] at this

end Salt.Vmvt
