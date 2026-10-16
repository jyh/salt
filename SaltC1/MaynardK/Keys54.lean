/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.JMainM
import SaltC1.Cert54.All

/-!
# C1 · A2d (c0), (c) — the certificate's `List ℕ` keys as the Lean side's `Fin 13 → ℕ`

The certificate (`SaltC1.Cert54`) indexes exponents by lists `[c₁, …, c₁₃]`; the Lean side
(`Salt.MaynardK`) by tuples `C : Fin M → ℕ`. Every key the bridge meets is `List.ofFn C`, and on
those lists the certificate's functions are the Lean side's: `wt` is `weight`, `encKey a` is
`a + enc`, `subL` is `-`, `boxL` is `tuplesLE`, `facProd` and `chooseProd` are the products,
`keysW 13 w` holds exactly the tuples of weight `≤ w`. `toF` reads a list back (the `cs54`
lambda). On bounded digits `encKey` is injective and `decodeC` inverts it.

(c): `coef_keys_ok` and `coef_basis_ok` read as `coefBT`'s `i`-th leaf being the `i`-th entry's
key and coefficient, every entry a basis function (`a + wt C ≤ 23`, 13 exponents).

Every lemma is generic in the list (or tuple); the certificate's data enter only through its
committed theorems, never by reduction. Nothing here bears on twin primes.
-/

open Finset
open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

-- The data are never unfolded here: every fact about them is a committed certificate theorem.
attribute [local irreducible] coefBT cs54L factT

/-! ## List folds and sums -/

/-- A list fold that adds one term per element is the list sum. -/
lemma foldl_add_of {α β : Type*} [AddCommMonoid β] (F : β → α → β) (G : α → β)
    (hF : ∀ acc a, F acc a = acc + G a) :
    ∀ (l : List α) (x : β), l.foldl F x = x + (l.map G).sum := by
  intro l
  induction l with
  | nil => intro x; simp
  | cons a l ih =>
    intro x
    rw [List.foldl_cons, ih, hF, List.map_cons, List.sum_cons, add_assoc]

/-- A list sum, indexed. -/
lemma list_sum_map_eq_range {α β : Type*} [AddCommMonoid β] (l : List α) (h : α → β) (d : α) :
    (l.map h).sum = ∑ i ∈ range l.length, h (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-! ## (c0) The dictionary on `List.ofFn` -/

/-- A list read as a tuple of 13 exponents (the `cs54` lambda). -/
def toF (c : List ℕ) : Fin 13 → ℕ := fun m => c.getD m 0

lemma toF_ofFn (C : Fin 13 → ℕ) : toF (List.ofFn C) = C := by
  funext m
  unfold toF
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma ofFn_toF {c : List ℕ} (h : c.length = 13) : List.ofFn (toF c) = c := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn]
  unfold toF
  rw [List.getD_eq_getElem _ _ h₂]

lemma length_ofFn13 (C : Fin 13 → ℕ) : (List.ofFn C).length = 13 := List.length_ofFn

variable {M : ℕ}

lemma wtAux_ofFn (C : Fin M → ℕ) (s : ℕ) :
    wtAux (List.ofFn C) s = ∑ m : Fin M, (s + 2 * (m : ℕ)) * C m := by
  induction M generalizing s with
  | zero => simp [wtAux]
  | succ M ih =>
    rw [List.ofFn_succ, wtAux, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, mul_zero, add_zero, Fin.val_succ]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

lemma wt_ofFn (C : Fin M → ℕ) : wt (List.ofFn C) = weight C := by
  rw [wt, wtAux_ofFn]
  unfold weight
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma encAux_ofFn (C : Fin M → ℕ) (p : ℕ) :
    encAux (List.ofFn C) p = ∑ m : Fin M, C m * (p * 64 ^ (m : ℕ)) := by
  induction M generalizing p with
  | zero => simp [encAux]
  | succ M ih =>
    rw [List.ofFn_succ, encAux, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

lemma encKey_ofFn (a : ℕ) (C : Fin M → ℕ) : encKey a (List.ofFn C) = a + enc C := by
  rw [encKey, encAux_ofFn]
  unfold enc
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma encKey_zero_ofFn (C : Fin M → ℕ) : encKey 0 (List.ofFn C) = enc C := by
  rw [encKey_ofFn, zero_add]

/-- Keys add: `encKey a C + encKey a' C' = encKey (a + a') (C + C')` (no digit bound needed). -/
lemma encKey_ofFn_add (a a' : ℕ) (C C' : Fin M → ℕ) :
    encKey a (List.ofFn C) + encKey a' (List.ofFn C') = encKey (a + a') (List.ofFn (C + C')) := by
  rw [encKey_ofFn, encKey_ofFn, encKey_ofFn]
  unfold enc
  rw [add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.add_apply]
  ring

lemma subL_ofFn (C A : Fin M → ℕ) : subL (List.ofFn C) (List.ofFn A) = List.ofFn (C - A) := by
  induction M with
  | zero => simp [subL]
  | succ M ih =>
    rw [List.ofFn_succ, List.ofFn_succ, subL, ih, List.ofFn_succ]
    rfl

lemma allZero_ofFn (A : Fin M → ℕ) : allZero (List.ofFn A) = true ↔ A = 0 := by
  induction M with
  | zero => simp [allZero, eq_iff_true_of_subsingleton]
  | succ M ih =>
    rw [List.ofFn_succ, allZero, Bool.and_eq_true, ih, Nat.beq_eq]
    constructor
    · rintro ⟨h0, ht⟩
      funext m
      refine Fin.cases ?_ (fun j => ?_) m
      · exact h0
      · exact congrFun ht j
    · rintro rfl
      exact ⟨rfl, rfl⟩

lemma leL_ofFn (J C : Fin M → ℕ) : leL (List.ofFn J) (List.ofFn C) = true ↔ ∀ m, J m ≤ C m := by
  induction M with
  | zero => simp [leL]
  | succ M ih =>
    rw [List.ofFn_succ, List.ofFn_succ, leL, Bool.and_eq_true, ih, Nat.ble_eq]
    constructor
    · rintro ⟨h0, ht⟩ m
      refine Fin.cases ?_ (fun j => ?_) m
      · exact h0
      · exact ht j
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

lemma allLt64_ofFn (C : Fin M → ℕ) : allLt64 (List.ofFn C) = true ↔ ∀ m, C m < 64 := by
  induction M with
  | zero => simp [allLt64]
  | succ M ih =>
    rw [List.ofFn_succ, allLt64, Bool.and_eq_true, ih, Nat.blt_eq]
    constructor
    · rintro ⟨h0, ht⟩ m
      refine Fin.cases ?_ (fun j => ?_) m
      · exact h0
      · exact ht j
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-- The certificate's box is `tuplesLE`, element for element and in the same order. -/
lemma boxL_ofFn (C : Fin M → ℕ) : boxL (List.ofFn C) = (tuplesLE M C).map List.ofFn := by
  induction M with
  | zero => simp [boxL, tuplesLE]
  | succ M ih =>
    rw [List.ofFn_succ, boxL, tuplesLE, List.map_flatMap]
    refine List.flatMap_congr fun x _ => ?_
    rw [ih, List.map_map, List.map_map]
    refine List.map_congr_left fun y _ => ?_
    simp [List.ofFn_succ]

lemma facProd_ofFn (C : Fin M → ℕ) : facProd (List.ofFn C) = ∏ m, factT.findB (C m) := by
  induction M with
  | zero => simp [facProd]
  | succ M ih =>
    rw [List.ofFn_succ, facProd, ih, Fin.prod_univ_succ]

lemma chooseProd_ofFn (C J : Fin M → ℕ) :
    chooseProd (List.ofFn C) (List.ofFn J) = ∏ m, (((C m).choose (J m) : ℕ) : ℤ) := by
  induction M with
  | zero => simp [chooseProd]
  | succ M ih =>
    rw [List.ofFn_succ, List.ofFn_succ, chooseProd, ih, Fin.prod_univ_succ]

/-! ## `keysW` holds exactly the tuples of bounded weight -/

lemma mem_keysW_aux : ∀ m, m ≤ 13 → ∀ (rem : ℕ) (l : List ℕ),
    l ∈ keysW m rem ↔ l.length = m ∧ wtAux l (2 * (14 - m)) ≤ rem := by
  intro m
  induction m with
  | zero =>
    intro _ rem l
    simp only [keysW, List.mem_singleton]
    constructor
    · rintro rfl
      simp [wtAux]
    · rintro ⟨h, _⟩
      exact List.eq_nil_of_length_eq_zero h
  | succ m ih =>
    intro hm rem l
    rw [keysW, List.mem_flatMap]
    simp only [List.mem_range, List.mem_map]
    have hs : 0 < 2 * (13 - m) := by omega
    constructor
    · rintro ⟨c, hc, cs, hcs, rfl⟩
      rw [ih (by omega)] at hcs
      obtain ⟨hl, hw⟩ := hcs
      refine ⟨by simp [hl], ?_⟩
      have h1 : c ≤ rem / (2 * (13 - m)) := by omega
      rw [Nat.le_div_iff_mul_le hs] at h1
      have h2 : 2 * (14 - (m + 1)) = 2 * (13 - m) := by omega
      have h3 : 2 * (13 - m) + 2 = 2 * (14 - m) := by omega
      rw [h2, wtAux, h3]
      rw [mul_comm] at h1
      generalize 2 * (13 - m) * c = t at h1 hw ⊢
      omega
    · rintro ⟨hl, hw⟩
      obtain ⟨c, cs, rfl⟩ : ∃ c cs, l = c :: cs := by
        cases l with
        | nil => simp at hl
        | cons c cs => exact ⟨c, cs, rfl⟩
      have h2 : 2 * (14 - (m + 1)) = 2 * (13 - m) := by omega
      have h3 : 2 * (13 - m) + 2 = 2 * (14 - m) := by omega
      rw [h2, wtAux, h3] at hw
      refine ⟨c, ?_, cs, ?_, rfl⟩
      · have : c * (2 * (13 - m)) ≤ rem := by
          rw [mul_comm]
          generalize 2 * (13 - m) * c = t at hw ⊢
          omega
        have := (Nat.le_div_iff_mul_le hs).mpr this
        omega
      · rw [ih (by omega)]
        refine ⟨by simpa using hl, ?_⟩
        generalize 2 * (13 - m) * c = t at hw ⊢
        omega

/-- `keysW 13 w` holds exactly the tuples of weight `≤ w`. -/
lemma mem_keysW {w : ℕ} {C : Fin 13 → ℕ} : List.ofFn C ∈ keysW 13 w ↔ weight C ≤ w := by
  rw [mem_keysW_aux 13 le_rfl, List.length_ofFn]
  simp only [true_and]
  rw [show 2 * (14 - 13) = 2 from rfl, ← wt, wt_ofFn]

/-! ## The factorial table -/

/-- `factT` holds `n!` for `n ≤ 101` (from `fact_ok`, by induction). -/
lemma factT_eq : ∀ n, n ≤ 101 → factT.findB n = ((n ! : ℕ) : ℤ) := by
  have h := fact_ok
  simp only [checkFact, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, hs⟩ := h
  intro n
  induction n with
  | zero => intro _; simpa using h0
  | succ n ih =>
    intro hn
    rw [hs n (by omega), ih (by omega), Nat.factorial_succ]
    push_cast
    ring

lemma facProd_ofFn_eq (C : Fin M → ℕ) (h : ∀ m, C m ≤ 101) :
    facProd (List.ofFn C) = ∏ m, (((C m)! : ℕ) : ℤ) := by
  rw [facProd_ofFn]
  exact Finset.prod_congr rfl fun m _ => factT_eq _ (h m)

/-! ## Bounded digits: `encKey` is injective and `decodeC` inverts it -/

lemma enc0_digit (C : Fin M → ℕ) (hC : ∀ m, C m < 64) :
    ∀ m : Fin M, enc0 C / 64 ^ (m : ℕ) % 64 = C m := by
  induction M with
  | zero => intro m; exact m.elim0
  | succ M ih =>
    intro m
    rw [enc0_succ]
    refine Fin.cases ?_ (fun j => ?_) m
    · simp only [Fin.val_zero, pow_zero, Nat.div_one]
      have := hC 0
      omega
    · simp only [Fin.val_succ]
      rw [pow_succ, mul_comm (64 ^ (j : ℕ)) 64, ← Nat.div_div_eq_div_mul]
      have h0 := hC 0
      have hd : (C 0 + 64 * enc0 (Fin.tail C)) / 64 = enc0 (Fin.tail C) := by omega
      rw [hd, ih (Fin.tail C) (fun m => hC _) j]
      rfl

lemma encKey_ofFn_eq_mul (a : ℕ) (C : Fin M → ℕ) : encKey a (List.ofFn C) = a + 64 * enc0 C := by
  rw [encKey_ofFn, enc_eq]

lemma encKey_ofFn_inj {a a' : ℕ} {C C' : Fin M → ℕ} (ha : a < 64) (ha' : a' < 64)
    (hC : ∀ m, C m < 64) (hC' : ∀ m, C' m < 64)
    (h : encKey a (List.ofFn C) = encKey a' (List.ofFn C')) : a = a' ∧ C = C' := by
  rw [encKey_ofFn_eq_mul, encKey_ofFn_eq_mul] at h
  have h1 : a = a' := by omega
  have h2 : enc0 C = enc0 C' := by omega
  exact ⟨h1, enc0_inj C C' hC hC' h2⟩

/-- `encKey_inj` on lists (the brief's form): bounded digits, 13 of them. -/
lemma encKey_inj {a a' : ℕ} {c c' : List ℕ} (ha : a < 64) (ha' : a' < 64)
    (hc : allLt64 c = true) (hc' : allLt64 c' = true) (hl : c.length = 13) (hl' : c'.length = 13)
    (h : encKey a c = encKey a' c') : a = a' ∧ c = c' := by
  obtain ⟨C, rfl⟩ : ∃ C, c = List.ofFn C := ⟨toF c, (ofFn_toF hl).symm⟩
  obtain ⟨C', rfl⟩ : ∃ C, c' = List.ofFn C := ⟨toF c', (ofFn_toF hl').symm⟩
  rw [allLt64_ofFn] at hc hc'
  obtain ⟨h1, h2⟩ := encKey_ofFn_inj ha ha' hc hc' h
  exact ⟨h1, by rw [h2]⟩

lemma encKey_mod (a : ℕ) (C : Fin M → ℕ) (ha : a < 64) : encKey a (List.ofFn C) % 64 = a := by
  rw [encKey_ofFn_eq_mul]
  omega

lemma decodeC_encKey (a : ℕ) (C : Fin 13 → ℕ) (ha : a < 64) (hC : ∀ m, C m < 64) :
    decodeC (encKey a (List.ofFn C)) = List.ofFn C := by
  refine List.ext_getElem (by simp [decodeC]) fun i h₁ h₂ => ?_
  simp only [decodeC, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [encKey_ofFn_eq_mul, pow_succ, mul_comm (64 ^ i) 64, ← Nat.div_div_eq_div_mul]
  have hd : (a + 64 * enc0 C) / 64 = enc0 C := by omega
  rw [hd]
  exact enc0_digit C hC ⟨i, by simpa using h₂⟩

/-! ## (c) The coefficients -/

/-- The entry accessor (a total `getD`; every index used is `< 1236`). -/
noncomputable def ent (i : ℕ) : ℕ × List ℕ × ℤ := cs54L.getD i (0, [], 0)

lemma coefKeys_spec : cs54L.length = nB ∧ ∀ i, i < nB →
    coefBT.getB i = (encKey (ent i).1 (ent i).2.1, (ent i).2.2) := by
  have h := coef_keys_ok
  unfold checkCoefKeys at h
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun i hi => ?_⟩
  have hi' : i < ((List.range nB).zip cs54L).length := by simp [hlen, hi]
  have hm := hall _ (List.getElem_mem hi')
  rw [List.getElem_zip, List.getElem_range] at hm
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hm
  have he : ent i = cs54L[i]'(by rw [hlen]; exact hi) := by
    unfold ent
    rw [List.getD_eq_getElem]
  rw [he]
  exact Prod.ext hm.1 hm.2

lemma cs54L_length : cs54L.length = 1236 := coefKeys_spec.1

lemma coefBT_getB {i : ℕ} (hi : i < 1236) :
    coefBT.getB i = (encKey (ent i).1 (ent i).2.1, (ent i).2.2) := coefKeys_spec.2 i hi

lemma cs54L_basis : ∀ e ∈ cs54L, e.1 + wt e.2.1 ≤ 23 ∧ e.2.1.length = 13 := by
  have h := coef_basis_ok
  unfold checkCoefBasis at h
  rw [List.all_eq_true] at h
  intro e he
  have := h e he
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at this
  exact this

lemma ent_mem {i : ℕ} (hi : i < 1236) : ent i ∈ cs54L := by
  unfold ent
  rw [List.getD_eq_getElem _ _ (by rw [cs54L_length]; exact hi)]
  exact List.getElem_mem _

/-- The tuple of entry `i`. -/
noncomputable def entC (i : ℕ) : Fin 13 → ℕ := toF (ent i).2.1

lemma ent_list {i : ℕ} (hi : i < 1236) : (ent i).2.1 = List.ofFn (entC i) :=
  (ofFn_toF (cs54L_basis _ (ent_mem hi)).2).symm

lemma ent_basis {i : ℕ} (hi : i < 1236) : (ent i).1 + weight (entC i) ≤ 23 := by
  have h := (cs54L_basis _ (ent_mem hi)).1
  rwa [ent_list hi, wt_ofFn] at h

lemma entC_lt {i : ℕ} (hi : i < 1236) (m : Fin 13) : entC i m ≤ 11 := by
  have h := ent_basis hi
  have := two_mul_le_weight (entC i) m
  omega

/-- `cs54`'s entries are the certificate's, read through `toF`. -/
lemma cs54_eq : cs54 = cs54L.map fun e => ((e.1, toF e.2.1), e.2.2) := rfl

end SaltC1.MaynardK
