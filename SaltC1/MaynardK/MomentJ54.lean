/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.MomentI54

/-!
# C1 · A2d (b), (e) — the `J` value table, the collected marginal, and the `J` form

(b) `WJtree_eq`: on every `(E, G)` with `E + weight G ≤ 48`, `WJtree` holds
`closedM 13 53 E G · 101!`.

(e) `Jint_eq_JformM`: `Jint = (24!)² · 101! · JformM 13 54 cs54`, in four steps.

* (e1) `w_ok`'s fold, read by an invariant (`InvW`, `ShardSpec`, `GInv`): the marginal's terms
  `T = wshards.flatten` are each valid and tied to their coefficient, strictly increasing in
  `(key, i, enc j)`, `|T| = expectedLen`, and `WBT`'s first 1236 leaves are exactly the key runs of
  `T` (strictly increasing keys, each leaf's value the run's sum). Since the triple determines
  `(i, j)`, the map `t ↦ (i, j)` is injective on `T`, and `expectedLen` is the size of
  `{(i, j) : i < 1236, j ≤ C_i}`, so `T` enumerates that set exactly (`sum_T`).
* (e2) each term's key and value are `FJM`'s entry at `(i, j)`, scaled by `24!` (`term_sem`).
* (e3) `WBT`'s leaf at the key of `K ∈ keysJM` is `24! · wtJM K` (`fs_encK`), and its keys are
  `keysJM`, injectively (`reindex`).
* (e4) `Jint` is the symmetric half over `WBT`'s rows (as `Iint`), and the value table at the summed
  key is `WJtree_eq`'s.

Every structural fact is a generic lemma (the fold invariants are over an arbitrary list of
terms); the data enter only through `w_ok`, `w_close`, `coef_keys_ok`, `coef_basis_ok`, `wj_ok`,
`Jint`'s definition and the series tables. Nothing here bears on twin primes.
-/

open Finset
open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

attribute [local irreducible] coefBT cs54L factT p53T WJtree WBT wsh0 wsh1 wsh2

/-! ## (b) The `J` value table -/

/-- **`WJtree` is `closedM 13 53 · 101!` on `E + weight G ≤ 48`.** -/
theorem WJtree_eq (E : ℕ) (G : Fin 13 → ℕ) (h : E + weight G ≤ 48) :
    ((WJtree.findB (encKey E (List.ofFn G)) : ℤ) : ℚ) = closedM 13 53 E G * ((101 ! : ℕ) : ℚ) := by
  have hmem : (E, List.ofFn G) ∈ wjEntries := by
    unfold wjEntries
    rw [List.mem_flatMap]
    refine ⟨List.ofFn G, mem_keysW.mpr (by omega), List.mem_map.mpr ⟨E, ?_, rfl⟩⟩
    rw [List.mem_range, wt_ofFn]
    omega
  have hc := (List.all_eq_true.mp wj_ok) _ hmem
  unfold checkWJ at hc
  simp only at hc
  rw [beq_iff_eq, wt_ofFn, factT_eq _ (by omega), factT_eq _ (by omega), factT_eq _ (by omega),
    facProd_ofFn_eq G (fun m => by have := two_mul_le_weight G m; omega)] at hc
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hc
  push_cast at hq
  rw [p53T_eq' G (by omega)] at hq
  unfold closedM
  have hD : (((53 + E + weight G)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hD, hq]

/-! ## (e1) The marginal fold, read by an invariant -/

/-- A term's key. -/
noncomputable def Kt (t : WTerm) : ℕ := (termKV t).1
/-- A term's value. -/
noncomputable def Vt (t : WTerm) : ℤ := (termKV t).2.1
/-- A term's validity and tie. -/
noncomputable def OKt (t : WTerm) : Bool := (termKV t).2.2 && validT t
/-- A term's order triple `(key, i, enc j)`. -/
noncomputable def tr (t : WTerm) : ℕ × ℕ × ℕ := (Kt t, t.1, encKey 0 t.2.2.2)

/-- The strict lexicographic order on triples. -/
def lt3 (x y : ℕ × ℕ × ℕ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))

/-- Its reflexive closure. -/
def le3 (x y : ℕ × ℕ × ℕ) : Prop := lt3 x y ∨ x = y

lemma lt3_of_le3_lt3 {x y z : ℕ × ℕ × ℕ} (h1 : le3 x y) (h2 : lt3 y z) : lt3 x z := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨z1, z2, z3⟩ := z
  unfold le3 lt3 at *
  simp only [Prod.mk.injEq] at *
  omega

lemma le3_fst {x y : ℕ × ℕ × ℕ} (h : le3 x y) : x.1 ≤ y.1 := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  unfold le3 lt3 at h
  simp only [Prod.mk.injEq] at h
  omega

lemma lt3_irrefl (x : ℕ × ℕ × ℕ) : ¬ lt3 x x := by
  unfold lt3
  omega

/-- The run sum of key `u` over a list of terms. -/
noncomputable def fs (P : List WTerm) (u : ℕ) : ℤ :=
  (P.map fun t => if Kt t = u then Vt t else 0).sum

lemma fs_append (P Q : List WTerm) (u : ℕ) : fs (P ++ Q) u = fs P u + fs Q u := by
  simp [fs, List.map_append, List.sum_append]

lemma fs_singleton (t : WTerm) (u : ℕ) : fs [t] u = if Kt t = u then Vt t else 0 := by
  simp [fs]

lemma fs_eq_zero {P : List WTerm} {u : ℕ} (h : ∀ t ∈ P, Kt t ≠ u) : fs P u = 0 := by
  unfold fs
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [if_neg (h t ht)]

/-- The invariant of the inner fold, on the processed prefix `P` of one shard. -/
def InvW (pos0 pk : ℕ) (P : List WTerm) (st : WState) : Prop :=
  st.2.2.2.1 = true →
    pos0 ≤ st.1 ∧
    (∀ t ∈ P, OKt t = true) ∧
    (P.map tr).Pairwise lt3 ∧
    (∀ t ∈ P, le3 (tr t) (st.2.1, st.2.2.2.2.1, st.2.2.2.2.2.1)) ∧
    (∀ t ∈ P, pk < Kt t ∧ Kt t ≤ st.2.1) ∧
    (∃ t ∈ P, Kt t = st.2.1) ∧
    st.2.2.1 = fs P st.2.1 ∧
    (∀ r, pos0 ≤ r → r < st.1 → (WBT.getB r).1 < st.2.1 ∧
      (WBT.getB r).2 = fs P (WBT.getB r).1 ∧ ∃ t ∈ P, Kt t = (WBT.getB r).1) ∧
    (∀ t ∈ P, Kt t = st.2.1 ∨ ∃ r, pos0 ≤ r ∧ r < st.1 ∧ (WBT.getB r).1 = Kt t) ∧
    (∀ r r', pos0 ≤ r → r < r' → r' < st.1 → (WBT.getB r).1 < (WBT.getB r').1) ∧
    st.2.2.2.2.2.2 = P.length

lemma wStep_eq (pos key : ℕ) (sum : ℤ) (ok : Bool) (pi pj cnt : ℕ) (t : WTerm) :
    wStep (pos, key, sum, ok, pi, pj, cnt) t =
      if Kt t = key then
        (pos, key, sum + Vt t, ok && OKt t && (Nat.blt pi t.1 ||
          (Nat.beq pi t.1 && Nat.blt pj (encKey 0 t.2.2.2))), t.1, encKey 0 t.2.2.2, cnt + 1)
      else
        (pos + 1, Kt t, Vt t, ok && OKt t && Nat.blt key (Kt t) &&
          Nat.beq (WBT.getB pos).1 key && ((WBT.getB pos).2 == sum), t.1, encKey 0 t.2.2.2,
          cnt + 1) := by
  unfold wStep
  by_cases h : Kt t = key
  · rw [if_pos h]
    have hb : Nat.beq (termKV t).1 key = true := by
      change Nat.beq (Kt t) key = true
      rw [h]
      exact Nat.beq_refl key
    simp only [hb]
    rfl
  · rw [if_neg h]
    have hb : Nat.beq (termKV t).1 key = false := by
      rw [Bool.eq_false_iff]
      intro hb'
      exact h (Nat.eq_of_beq_eq_true hb')
    simp only [hb]
    rfl

lemma InvW_step (pos0 pk : ℕ) (P : List WTerm) (st : WState) (t : WTerm)
    (h : InvW pos0 pk P st) : InvW pos0 pk (P ++ [t]) (wStep st t) := by
  obtain ⟨pos, key, sum, ok, pi, pj, cnt⟩ := st
  rw [wStep_eq]
  by_cases hk : Kt t = key
  · rw [if_pos hk]
    unfold InvW at h ⊢
    dsimp only at h ⊢
    intro hok
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hok
    obtain ⟨⟨hok0, hokt⟩, hord⟩ := hok
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h hok0
    have hlt : lt3 (key, pi, pj) (tr t) := by
      unfold tr lt3
      dsimp only
      rw [hk]
      right
      refine ⟨rfl, ?_⟩
      rcases hord with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h10, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h2 s hs
      · rw [List.mem_singleton.mp hs]; exact hokt
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h3, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      rw [List.map_singleton, List.mem_singleton] at hy
      rw [hy]
      exact lt3_of_le3_lt3 (h4 s hs) hlt
    · intro s hs
      have htr : tr t = (key, t.1, encKey 0 t.2.2.2) := by unfold tr; rw [hk]
      rw [← htr]
      rcases List.mem_append.mp hs with hs | hs
      · exact Or.inl (lt3_of_le3_lt3 (h4 s hs) hlt)
      · rw [List.mem_singleton.mp hs]; exact Or.inr rfl
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h5 s hs
      · rw [List.mem_singleton.mp hs, hk]
        obtain ⟨s', hs', hs'k⟩ := h6
        exact ⟨hs'k ▸ (h5 s' hs').1, le_rfl⟩
    · obtain ⟨s', hs', hs'k⟩ := h6
      exact ⟨s', List.mem_append_left _ hs', hs'k⟩
    · rw [fs_append, fs_singleton, if_pos hk, h7]
    · intro r hr1 hr2
      obtain ⟨a1, a2, s', hs', hs'k⟩ := h8 r hr1 hr2
      refine ⟨a1, ?_, s', List.mem_append_left _ hs', hs'k⟩
      rw [fs_append, fs_singleton, if_neg (by omega), add_zero]
      exact a2
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h9 s hs
      · rw [List.mem_singleton.mp hs]; exact Or.inl hk
    · simp only [List.length_append, List.length_singleton]
      omega
  · rw [if_neg hk]
    unfold InvW at h ⊢
    dsimp only at h ⊢
    intro hok
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨hok0, hokt⟩, hkey⟩, hw1⟩, hw2⟩ := hok
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h hok0
    have hlt : ∀ s ∈ P, lt3 (tr s) (tr t) := by
      intro s hs
      have := le3_fst (h4 s hs)
      unfold lt3
      left
      unfold tr at this ⊢
      simp only at this ⊢
      omega
    have hPlt : ∀ s ∈ P, Kt s ≠ Kt t := by
      intro s hs
      have := (h5 s hs).2
      omega
    refine ⟨by omega, ?_, ?_, ?_, ?_, ⟨t, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact h2 s hs
      · rw [List.mem_singleton.mp hs]; exact hokt
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h3, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      rw [List.map_singleton, List.mem_singleton] at hy
      rw [hy]
      exact hlt s hs
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact Or.inl (hlt s hs)
      · rw [List.mem_singleton.mp hs]; exact Or.inr rfl
    · intro s hs
      obtain ⟨s', hs', hs'k⟩ := h6
      have hpk := (h5 s' hs').1
      rcases List.mem_append.mp hs with hs | hs
      · have := h5 s hs
        exact ⟨this.1, by omega⟩
      · rw [List.mem_singleton.mp hs]
        exact ⟨by omega, le_rfl⟩
    · rw [fs_append, fs_singleton, if_pos rfl, fs_eq_zero hPlt, zero_add]
    · intro r hr1 hr2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr2 with hr | hr
      · obtain ⟨a1, a2, s', hs', hs'k⟩ := h8 r hr1 hr
        refine ⟨by omega, ?_, s', List.mem_append_left _ hs', hs'k⟩
        rw [fs_append, fs_singleton, if_neg (by omega), add_zero]
        exact a2
      · subst hr
        refine ⟨by omega, ?_, ?_⟩
        · rw [fs_append, fs_singleton, if_neg (by omega), add_zero, hw2, hw1]
          exact h7
        · obtain ⟨s', hs', hs'k⟩ := h6
          exact ⟨s', List.mem_append_left _ hs', by rw [hs'k, hw1]⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · rcases h9 s hs with h | ⟨r, hr1, hr2, hr3⟩
        · exact Or.inr ⟨pos, h1, by omega, by rw [hw1, h]⟩
        · exact Or.inr ⟨r, hr1, by omega, hr3⟩
      · rw [List.mem_singleton.mp hs]; exact Or.inl rfl
    · intro r r' hr hrr' hr'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr' with hr' | hr'
      · exact h10 r r' hr hrr' hr'
      · subst hr'
        rw [hw1]
        exact (h8 r hr (by omega)).1
    · simp only [List.length_append, List.length_singleton]
      omega

lemma InvW_fold (pos0 pk : ℕ) :
    ∀ (ts P : List WTerm) (st : WState), InvW pos0 pk P st →
      InvW pos0 pk (P ++ ts) (ts.foldl wStep st) := by
  intro ts
  induction ts with
  | nil => intro P st h; simpa using h
  | cons t ts ih =>
    intro P st h
    rw [List.foldl_cons, show P ++ t :: ts = (P ++ [t]) ++ ts by simp]
    exact ih _ _ (InvW_step pos0 pk P st t h)

/-- What one shard's check certifies. -/
def ShardSpec (L : List WTerm) (pos0 pk : ℕ) (res : Bool × ℕ × ℕ × ℕ) : Prop :=
  res.1 = true →
    res.2.2.2 = L.length ∧
    (∀ t ∈ L, OKt t = true) ∧
    (L.map tr).Pairwise lt3 ∧
    pk ≤ res.2.1 ∧
    (∀ t ∈ L, pk < Kt t ∧ Kt t ≤ res.2.1) ∧
    (∀ r, pos0 ≤ r → r < pos0 + res.2.2.1 → (WBT.getB r).1 ≤ res.2.1 ∧
      (WBT.getB r).2 = fs L (WBT.getB r).1 ∧ ∃ t ∈ L, Kt t = (WBT.getB r).1) ∧
    (∀ t ∈ L, ∃ r, pos0 ≤ r ∧ r < pos0 + res.2.2.1 ∧ (WBT.getB r).1 = Kt t) ∧
    (∀ r r', pos0 ≤ r → r < r' → r' < pos0 + res.2.2.1 → (WBT.getB r).1 < (WBT.getB r').1)

lemma checkWFrom_spec (L : List WTerm) (pos0 pk : ℕ) :
    ShardSpec L pos0 pk (checkWFrom L pos0 pk) := by
  cases L with
  | nil =>
    intro _
    simp only [checkWFrom]
    refine ⟨rfl, by simp, by simp, le_rfl, by simp, fun r h1 h2 => by omega, by simp,
      fun r r' h1 h2 h3 => by omega⟩
  | cons t ts =>
    have hinit : InvW pos0 pk [t]
        (pos0, Kt t, Vt t, OKt t && Nat.blt pk (Kt t), t.1, encKey 0 t.2.2.2, 1) := by
      intro hok
      simp only [Bool.and_eq_true, Nat.blt_eq] at hok
      refine ⟨le_rfl, ?_, List.pairwise_singleton _ _, ?_, ?_, ⟨t, List.mem_singleton_self _, rfl⟩,
        ?_, ?_, ?_, ?_, rfl⟩
      · intro s hs; rw [List.mem_singleton.mp hs]; exact hok.1
      · intro s hs; rw [List.mem_singleton.mp hs]; exact Or.inr rfl
      · intro s hs; rw [List.mem_singleton.mp hs]; exact ⟨hok.2, le_rfl⟩
      · simp only; rw [fs_singleton, if_pos rfl]
      · intro r h1 h2; simp only at h2; omega
      · intro s hs; rw [List.mem_singleton.mp hs]; exact Or.inl rfl
      · intro r r' h1 h2 h3; simp only at h3; omega
    have hfold := InvW_fold pos0 pk ts [t] _ hinit
    have hdef : checkWFrom (t :: ts) pos0 pk =
        let st := ts.foldl wStep
          (pos0, Kt t, Vt t, OKt t && Nat.blt pk (Kt t), t.1, encKey 0 t.2.2.2, 1)
        (st.2.2.2.1 && Nat.beq (WBT.getB st.1).1 st.2.1 && ((WBT.getB st.1).2 == st.2.2.1),
          st.2.1, st.1 + 1 - pos0, st.2.2.2.2.2.2) := by
      unfold checkWFrom
      simp only [OKt, Kt, Vt, Bool.and_assoc]
    rw [hdef]
    generalize ts.foldl wStep
      (pos0, Kt t, Vt t, OKt t && Nat.blt pk (Kt t), t.1, encKey 0 t.2.2.2, 1) = st at hfold
    obtain ⟨pos, key, sum, ok, pi, pj, cnt⟩ := st
    intro hok
    simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hok
    obtain ⟨⟨hok0, hw1⟩, hw2⟩ := hok
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hfold hok0
    simp only [List.singleton_append] at *
    obtain ⟨s', hs', hs'k⟩ := h6
    refine ⟨h11, h2, h3, by have := (h5 s' hs').1; omega, h5, ?_, ?_, ?_⟩
    · intro r hr1 hr2
      rcases Nat.lt_or_ge r pos with hr | hr
      · obtain ⟨a1, a2, a3⟩ := h8 r hr1 hr
        exact ⟨a1.le, a2, a3⟩
      · have hr : r = pos := by omega
        subst hr
        exact ⟨hw1.le, by rw [hw2, h7, hw1], s', hs', by rw [hs'k, hw1]⟩
    · intro s hs
      rcases h9 s hs with h | ⟨r, hr1, hr2, hr3⟩
      · exact ⟨pos, h1, by omega, by rw [hw1, h]⟩
      · exact ⟨r, hr1, by omega, hr3⟩
    · intro r r' hr hrr' hr'
      rcases Nat.lt_or_ge r' pos with h' | h'
      · exact h10 r r' hr hrr' h'
      · have : r' = pos := by omega
        subst this
        rw [hw1]
        exact (h8 r hr (by omega)).1

/-- The invariant of the shard fold, on the processed terms `Q`. -/
def GInv (Q : List WTerm) (st : ℕ × ℕ × ℕ × Bool) : Prop :=
  st.2.2.2 = true →
    st.2.2.1 = Q.length ∧
    (∀ t ∈ Q, OKt t = true) ∧
    (Q.map tr).Pairwise lt3 ∧
    (∀ t ∈ Q, Kt t ≤ st.2.1) ∧
    (∀ r, r < st.1 → (WBT.getB r).1 ≤ st.2.1 ∧
      (WBT.getB r).2 = fs Q (WBT.getB r).1 ∧ ∃ t ∈ Q, Kt t = (WBT.getB r).1) ∧
    (∀ t ∈ Q, ∃ r, r < st.1 ∧ (WBT.getB r).1 = Kt t) ∧
    (∀ r r', r < r' → r' < st.1 → (WBT.getB r).1 < (WBT.getB r').1)

lemma GInv_step (Q L : List WTerm) (st : ℕ × ℕ × ℕ × Bool) (h : GInv Q st) :
    GInv (Q ++ L) (wShardStep st L) := by
  obtain ⟨pos, pk, cnt, ok⟩ := st
  have hdef : wShardStep (pos, pk, cnt, ok) L = ((pos + (checkWFrom L pos pk).2.2.1,
      (checkWFrom L pos pk).2.1, cnt + (checkWFrom L pos pk).2.2.2,
      ok && (checkWFrom L pos pk).1)) := by
    unfold wShardStep
    rfl
  rw [hdef]
  have hspec := checkWFrom_spec L pos pk
  generalize checkWFrom L pos pk = res at hspec
  obtain ⟨okS, lk, ng, c⟩ := res
  intro hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h hok.1
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hspec hok.2
  simp only at *
  have hQL : ∀ t ∈ Q, ∀ s ∈ L, Kt t < Kt s := fun t ht s hs => by
    have := g4 t ht; have := (s5 s hs).1; omega
  refine ⟨by rw [List.length_append]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact g2 t ht
    · exact s2 t ht
  · rw [List.map_append, List.pairwise_append]
    refine ⟨g3, s3, ?_⟩
    intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
    unfold lt3 tr
    left
    exact hQL t ht s hs
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have := g4 t ht; omega
    · exact (s5 t ht).2
  · intro r hr
    rcases Nat.lt_or_ge r pos with h' | h'
    · obtain ⟨a1, a2, t, ht, htk⟩ := g5 r h'
      refine ⟨by omega, ?_, t, List.mem_append_left _ ht, htk⟩
      rw [fs_append, fs_eq_zero (P := L) (fun s hs => by have := hQL t ht s hs; omega), add_zero]
      exact a2
    · obtain ⟨a1, a2, t, ht, htk⟩ := s6 r h' hr
      refine ⟨a1, ?_, t, List.mem_append_right _ ht, htk⟩
      have hpk := (s5 t ht).1
      rw [fs_append, fs_eq_zero (P := Q) (fun s hs => by have := g4 s hs; omega), zero_add]
      exact a2
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨r, hr, hrk⟩ := g6 t ht
      exact ⟨r, by omega, hrk⟩
    · obtain ⟨r, hr1, hr2, hrk⟩ := s7 t ht
      exact ⟨r, hr2, hrk⟩
  · intro r r' hrr' hr'
    rcases Nat.lt_or_ge r' pos with h' | h'
    · exact g7 r r' hrr' h'
    · rcases Nat.lt_or_ge r pos with h'' | h''
      · have := (g5 r h'').1
        obtain ⟨_, _, t, ht, htk⟩ := s6 r' h' hr'
        have := (s5 t ht).1
        omega
      · exact s8 r r' h'' hrr' hr'

lemma GInv_fold : ∀ (sh : List (List WTerm)) (Q : List WTerm) (st : ℕ × ℕ × ℕ × Bool),
    GInv Q st → GInv (Q ++ sh.flatten) (sh.foldl wShardStep st) := by
  intro sh
  induction sh with
  | nil => intro Q st h; simpa using h
  | cons s sh ih =>
    intro Q st h
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    exact ih _ _ (GInv_step Q s st h)

/-- The marginal's terms. -/
noncomputable def Tm : List WTerm := wshards.flatten

-- `Tm` is data; it is reached only through `marginal_spec`.
attribute [local irreducible] Tm wshards

/-- **What `w_ok` certifies**, as properties of the term list and `WBT`. -/
lemma marginal_spec :
    expectedLen = Tm.length ∧
    (∀ t ∈ Tm, OKt t = true) ∧
    (Tm.map tr).Pairwise lt3 ∧
    (∀ r, r < 1236 → (WBT.getB r).2 = fs Tm (WBT.getB r).1 ∧ ∃ t ∈ Tm, Kt t = (WBT.getB r).1) ∧
    (∀ t ∈ Tm, ∃ r, r < 1236 ∧ (WBT.getB r).1 = Kt t) ∧
    (∀ r r', r < r' → r' < 1236 → (WBT.getB r).1 < (WBT.getB r').1) := by
  unfold Tm
  have h0 : GInv [] (0, 0, 0, true) := by
    intro _
    simp
  have hf := GInv_fold wshards [] _ h0
  have hw := w_ok
  unfold checkWShards at hw
  simp only [List.nil_append] at hf
  generalize wshards.foldl wShardStep (0, 0, 0, true) = res at hf hw
  obtain ⟨pos, pk, cnt, ok⟩ := res
  simp only [Bool.and_eq_true, Nat.beq_eq] at hw
  obtain ⟨⟨hok, hpos⟩, hcnt⟩ := hw
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hf hok
  have hn : nW = 1236 := rfl
  simp only at *
  rw [hn] at hpos
  subst hpos
  refine ⟨by rw [← hcnt, g1], g2, g3, fun r hr => ⟨(g5 r hr).2.1, (g5 r hr).2.2⟩, g6, g7⟩

lemma Tm_ok : ∀ t ∈ Tm, OKt t = true := marginal_spec.2.1
lemma Tm_pw : (Tm.map tr).Pairwise lt3 := marginal_spec.2.2.1
lemma Tm_run : ∀ r, r < 1236 → (WBT.getB r).2 = fs Tm (WBT.getB r).1 ∧
    ∃ t ∈ Tm, Kt t = (WBT.getB r).1 := marginal_spec.2.2.2.1
lemma Tm_cov : ∀ t ∈ Tm, ∃ r, r < 1236 ∧ (WBT.getB r).1 = Kt t := marginal_spec.2.2.2.2.1
lemma Tm_mono : ∀ r r', r < r' → r' < 1236 → (WBT.getB r).1 < (WBT.getB r').1 :=
  marginal_spec.2.2.2.2.2

/-! ## (e2) Each term is `FJM`'s entry, scaled by `24!` -/

/-- The marginal key of `(i, j)`. -/
noncomputable def Km (i : ℕ) (J : Fin 13 → ℕ) : ℕ × (Fin 13 → ℕ) :=
  ((ent i).1 + weight J + 1, entC i - J)

/-- The marginal weight of `(i, j)`. -/
noncomputable def Vm (i : ℕ) (J : Fin 13 → ℕ) : ℚ :=
  ((ent i).2.2 : ℚ) * wJ (ent i).1 (entC i) J

/-- A key as the certificate encodes it. -/
def encK (K : ℕ × (Fin 13 → ℕ)) : ℕ := encKey K.1 (List.ofFn K.2)

lemma f24q_eq {n : ℕ} (hn : n ≤ 24) : (f24q n : ℚ) = ((24 ! : ℕ) : ℚ) / ((n ! : ℕ) : ℚ) := by
  unfold f24q
  rw [factT_eq 24 (by norm_num), factT_eq n (by omega), Int.toNat_natCast, Int.toNat_natCast]
  rw [Int.ofNat_eq_natCast, Int.cast_natCast]
  exact Nat.cast_div (Nat.factorial_dvd_factorial hn) (by exact_mod_cast (Nat.factorial_pos _).ne')

lemma term_sem {t : WTerm} (ht : OKt t = true) :
    t.1 < 1236 ∧ t.2.2.2 = List.ofFn (toF t.2.2.2) ∧ (∀ m, toF t.2.2.2 m ≤ entC t.1 m) ∧
      Kt t = encK (Km t.1 (toF t.2.2.2)) ∧
      (Vt t : ℚ) = ((24 ! : ℕ) : ℚ) * Vm t.1 (toF t.2.2.2) := by
  obtain ⟨i, a, c, j⟩ := t
  unfold OKt termKV validT at ht
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
  obtain ⟨htie, ⟨⟨⟨⟨⟨hi, hcl⟩, hjl⟩, hle⟩, ha⟩, hc64⟩⟩ := ht
  simp only
  have hj : j = List.ofFn (toF j) := (ofFn_toF hjl).symm
  rw [coefBT_getB' hi] at htie
  simp only at htie
  have hC := entC_lt hi
  have hb := ent_basis hi
  obtain ⟨hai, hci⟩ := encKey_inj (by omega) ha
    (by rw [allLt64_ofFn]; intro m; have := hC m; omega) hc64 (List.length_ofFn) hcl htie
  rw [← hci, hj, leL_ofFn] at hle
  have hwJ : weight (toF j) ≤ weight (entC i) := weight_mono hle
  refine ⟨hi, hj, hle, ?_, ?_⟩
  · unfold Kt termKV encK Km
    simp only
    rw [← hci, hj, ← hai, wt_ofFn, subL_ofFn, toF_ofFn]
  · unfold Vt termKV Vm wJ
    simp only
    rw [coefBT_getB' hi, ← hci, hj, ← hai, wt_ofFn, chooseProd_ofFn, factT_eq _ (by omega),
      factT_eq _ (by omega)]
    simp only [toF_ofFn]
    push_cast
    rw [f24q_eq (by omega)]
    have hD : ((((ent i).1 + weight (toF j) + 1)! : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp

/-! ## (e1) The terms enumerate `{(i, j) : i < 1236, j ≤ C_i}` exactly -/

/-- A term's index pair. -/
noncomputable def phi (t : WTerm) : (_ : ℕ) × (Fin 13 → ℕ) := ⟨t.1, toF t.2.2.2⟩

/-- The index set. -/
noncomputable def Sidx : Finset ((_ : ℕ) × (Fin 13 → ℕ)) :=
  (range 1236).sigma fun i => boxM (entC i)

lemma Sidx_eq : Sidx = (range 1236).sigma fun i => boxM (entC i) := rfl

lemma mem_Sidx {x : (_ : ℕ) × (Fin 13 → ℕ)} : x ∈ Sidx ↔ x.1 < 1236 ∧ ∀ m, x.2 m ≤ entC x.1 m := by
  rw [Sidx_eq, Finset.mem_sigma, Finset.mem_range, boxM, Fintype.mem_piFinset]
  refine and_congr Iff.rfl (forall_congr' fun m => ?_)
  rw [Finset.mem_range]
  omega

-- `Sidx` ranges over `range 1236`; it is reached only through `Sidx_eq` and `mem_Sidx`.
attribute [local irreducible] Sidx

lemma foldl_prod_succ {M : ℕ} (C : Fin M → ℕ) (x : ℕ) :
    (List.ofFn C).foldl (fun p c => p * (c + 1)) x = x * ∏ m, (C m + 1) := by
  induction M generalizing x with
  | zero => simp
  | succ M ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih, Fin.prod_univ_succ, mul_assoc]

lemma card_boxM {M : ℕ} (C : Fin M → ℕ) : (boxM C).card = ∏ m, (C m + 1) := by
  unfold boxM
  rw [Fintype.card_piFinset]
  simp

lemma expectedLen_eq : expectedLen = Sidx.card := by
  unfold expectedLen
  rw [Sidx_eq]
  rw [foldl_add_of _ (fun i => (decodeC (coefBT.getB i).1).foldl (fun p c => p * (c + 1)) 1)
    (fun _ _ => rfl), zero_add, sum_range_list, Finset.card_sigma, show nB = 1236 from rfl]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [card_boxM, coefBT_getB' hi']
  simp only
  rw [decodeC_encKey _ _ (by have := ent_basis hi'; omega)
    (fun m => by have := entC_lt hi' m; omega), foldl_prod_succ, one_mul]

lemma tr_eq {t : WTerm} (ht : OKt t = true) :
    tr t = (encK (Km (phi t).1 (phi t).2), (phi t).1, encKey 0 (List.ofFn (phi t).2)) := by
  obtain ⟨_, hj, _, hK, _⟩ := term_sem ht
  unfold tr phi
  rw [hK, ← hj]

lemma nodup_phi : (Tm.map phi).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  have hpw := Tm_pw
  rw [List.pairwise_map] at hpw
  refine hpw.imp_of_mem fun {s t} hs ht hlt heq => ?_
  rw [tr_eq (Tm_ok s hs), tr_eq (Tm_ok t ht), heq] at hlt
  exact lt3_irrefl _ hlt

lemma phi_mem {t : WTerm} (ht : t ∈ Tm) : phi t ∈ Sidx := by
  have hts := term_sem (Tm_ok t ht)
  rw [mem_Sidx]
  exact ⟨hts.1, hts.2.2.1⟩

lemma toFinset_phi : (Tm.map phi).toFinset = Sidx := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨t, ht, hx⟩ := hx
    rw [← hx]
    exact phi_mem ht
  · rw [List.toFinset_card_of_nodup nodup_phi, List.length_map, ← expectedLen_eq]
    exact marginal_spec.1.le

/-- **(e1)** a sum over the terms is the sum over `{(i, j) : i < 1236, j ≤ C_i}`. -/
lemma sum_T (h : ((_ : ℕ) × (Fin 13 → ℕ)) → ℚ) :
    (Tm.map (fun t => h (phi t))).sum = ∑ i ∈ range 1236, ∑ J ∈ boxM (entC i), h ⟨i, J⟩ := by
  have hm : (Tm.map fun t => h (phi t)) = (Tm.map phi).map h := by rw [List.map_map]; rfl
  rw [hm, ← List.sum_toFinset _ nodup_phi, toFinset_phi, Sidx_eq, Finset.sum_sigma]

/-! ## (e3) The collected marginal -/

lemma Km_bound {i : ℕ} (hi : i < 1236) {J : Fin 13 → ℕ} (hJ : ∀ m, J m ≤ entC i m) :
    (Km i J).1 + weight (Km i J).2 ≤ 24 ∧ (Km i J).1 < 64 ∧ ∀ m, (Km i J).2 m < 64 := by
  have hb := ent_basis hi
  have hs := weight_sub_add hJ
  have hC := entC_lt hi
  unfold Km
  simp only
  refine ⟨by omega, by omega, fun m => ?_⟩
  simp only [Pi.sub_apply]
  have := hC m
  omega

lemma mem_cs54 {x : (ℕ × (Fin 13 → ℕ)) × ℤ} :
    x ∈ cs54 ↔ ∃ i, i < 1236 ∧ x = (((ent i).1, entC i), (ent i).2.2) := by
  rw [cs54_eq, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    refine ⟨i, by rw [← cs54L_length]; exact hi, ?_⟩
    have : ent i = cs54L[i] := by unfold ent; rw [List.getD_eq_getElem]
    rw [← this]
    rfl
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ent i, ent_mem hi, rfl⟩

lemma keysJM_eq : keysJM 13 cs54 = Sidx.image fun x => Km x.1 x.2 := by
  ext K
  unfold keysJM FJM
  rw [List.mem_toFinset, Finset.mem_image]
  simp only [List.mem_map, List.mem_flatMap, mem_tuplesLE]
  constructor
  · rintro ⟨u, ⟨x, hx, j, hj, rfl⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := mem_cs54.mp hx
    refine ⟨⟨i, j⟩, mem_Sidx.mpr ⟨hi, hj⟩, rfl⟩
  · rintro ⟨⟨i, J⟩, hx, rfl⟩
    rw [mem_Sidx] at hx
    refine ⟨_, ⟨(((ent i).1, entC i), (ent i).2.2), mem_cs54.mpr ⟨i, hx.1, rfl⟩, J,
      hx.2, rfl⟩, rfl⟩

lemma filter_sum_eq {α : Type*} [DecidableEq α] (L : List (α × ℚ)) (K : α) :
    ((L.filter fun u => u.1 = K).map Prod.snd).sum =
      (L.map fun u => if u.1 = K then u.2 else 0).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    by_cases h : u.1 = K <;> simp [h, ih]

lemma wtJM_eq (K : ℕ × (Fin 13 → ℕ)) :
    wtJM 13 cs54 K = ∑ i ∈ range 1236, ∑ J ∈ boxM (entC i), if Km i J = K then Vm i J else 0 := by
  unfold wtJM FJM
  rw [filter_sum_eq, list_sum_flatMap, cs54_eq, List.map_map,
    list_sum_map_eq_range _ _ (0, [], 0), cs54L_length]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, List.map_map]
  rw [sum_tuplesLE]
  rfl

lemma keysJM_bound {K : ℕ × (Fin 13 → ℕ)} (hK : K ∈ keysJM 13 cs54) :
    K.1 + weight K.2 ≤ 24 ∧ K.1 < 64 ∧ ∀ m, K.2 m < 64 := by
  rw [keysJM_eq, Finset.mem_image] at hK
  obtain ⟨⟨i, J⟩, hx, rfl⟩ := hK
  rw [mem_Sidx] at hx
  exact Km_bound hx.1 hx.2

/-- **(e3)** the run sum at the key of a marginal key is its collected weight, scaled by `24!`. -/
lemma fs_encK {K : ℕ × (Fin 13 → ℕ)} (hK : K ∈ keysJM 13 cs54) :
    (fs Tm (encK K) : ℚ) = ((24 ! : ℕ) : ℚ) * wtJM 13 cs54 K := by
  have hKb := keysJM_bound hK
  unfold fs
  rw [Int.cast_list_sum, List.map_map, List.map_congr_left (g := fun t =>
      (fun x : (_ : ℕ) × (Fin 13 → ℕ) =>
        if Km x.1 x.2 = K then ((24 ! : ℕ) : ℚ) * Vm x.1 x.2 else 0) (phi t)) ?_]
  · refine (sum_T (fun x : (_ : ℕ) × (Fin 13 → ℕ) =>
        if Km x.1 x.2 = K then ((24 ! : ℕ) : ℚ) * Vm x.1 x.2 else 0)).trans ?_
    rw [wtJM_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    split_ifs <;> simp
  · intro t ht
    have hts := term_sem (Tm_ok t ht)
    have hi := hts.1
    have hle := hts.2.2.1
    have hKt := hts.2.2.2.1
    have hVt := hts.2.2.2.2
    have hb := Km_bound hi hle
    unfold phi
    simp only [Function.comp_apply]
    by_cases h : Km t.1 (toF t.2.2.2) = K
    · rw [if_pos (by rw [hKt, h]), if_pos h, hVt]
    · rw [if_neg, if_neg h, Int.cast_zero]
      rw [hKt]
      intro he
      unfold encK at he
      obtain ⟨h1, h2⟩ := encKey_ofFn_inj hb.2.1 hKb.2.1 hb.2.2 hKb.2.2 he
      exact h (Prod.ext h1 h2)

lemma encK_injOn : Set.InjOn encK (keysJM 13 cs54 : Set (ℕ × (Fin 13 → ℕ))) := by
  intro K hK K' hK' he
  have b := keysJM_bound hK
  have b' := keysJM_bound hK'
  obtain ⟨h1, h2⟩ := encKey_ofFn_inj b.2.1 b'.2.1 b.2.2 b'.2.2 he
  exact Prod.ext h1 h2

/-- **(e3)** the rows of `WBT` are the marginal keys, injectively. -/
lemma reindex (H : ℕ → ℚ) :
    ∑ r ∈ range 1236, H (WBT.getB r).1 = ∑ K ∈ keysJM 13 cs54, H (encK K) := by
  have hinj : Set.InjOn (fun r => (WBT.getB r).1) (range 1236 : Set ℕ) := by
    intro r hr r' hr' he
    simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
    rcases Nat.lt_trichotomy r r' with h | h | h
    · have := Tm_mono r r' h hr'; simp only at he; omega
    · exact h
    · have := Tm_mono r' r h hr; simp only at he; omega
  have hset : (range 1236).image (fun r => (WBT.getB r).1) = (keysJM 13 cs54).image encK := by
    ext u
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hu
      obtain ⟨r, hr, hru⟩ := hu
      have ht := (Tm_run r hr).2
      obtain ⟨t, ht, htk⟩ := ht
      have hKt := (term_sem (Tm_ok t ht)).2.2.2.1
      refine ⟨Km t.1 (toF t.2.2.2), ?_, by rw [← hru, ← htk, hKt]⟩
      rw [keysJM_eq, Finset.mem_image]
      exact ⟨phi t, phi_mem ht, rfl⟩
    · intro hu
      obtain ⟨K, hK, hKu⟩ := hu
      rw [keysJM_eq, Finset.mem_image, ← toFinset_phi] at hK
      obtain ⟨x, hx, hxK⟩ := hK
      rw [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨t, ht, htx⟩ := hx
      obtain ⟨r, hr, hrk⟩ := Tm_cov t ht
      have hKt := (term_sem (Tm_ok t ht)).2.2.2.1
      refine ⟨r, hr, ?_⟩
      rw [hrk, hKt, ← hKu, ← hxK, ← htx]
      rfl
  rw [← Finset.sum_image (f := H) hinj, hset, Finset.sum_image encK_injOn]

/-! ## (e4) The `J` form -/

/-- One row of `Jhalf`. -/
noncomputable def rowJ (x : ℕ) : ℤ :=
  (WBT.getB x).2 * (WBT.getB x).2 * WJtree.findB (2 * (WBT.getB x).1) +
    2 * ∑ y ∈ Ico (x + 1) nW,
      (WBT.getB x).2 * (WBT.getB y).2 * WJtree.findB ((WBT.getB x).1 + (WBT.getB y).1)

lemma Jhalf_eq (x0 x1 : ℕ) : Jhalf x0 x1 = ∑ x ∈ Ico x0 x1, rowJ x := by
  unfold Jhalf
  rw [foldl_add_of _ (fun xx => rowJ (x0 + xx)) ?_ _ 0, zero_add, sum_range_list,
    Finset.sum_Ico_eq_sum_range]
  intro acc xx
  unfold rowJ
  dsimp only
  generalize WBT.getB (x0 + xx) = q
  obtain ⟨kx, wx⟩ := q
  dsimp only
  rw [foldl_add_of _ (fun yy => wx * (WBT.getB (x0 + xx + 1 + yy)).2 *
      WJtree.findB (kx + (WBT.getB (x0 + xx + 1 + yy)).1)) ?_ _ 0, zero_add, sum_range_list,
    Finset.sum_Ico_eq_sum_range, show nW - (x0 + xx) - 1 = nW - (x0 + xx + 1) by omega]
  · ring
  · intro acc2 yy
    dsimp only

lemma Jint_eq_sum : Jint = ∑ x ∈ range 1236, rowJ x := by
  unfold Jint
  simp only [Jhalf_eq]
  repeat rw [Finset.sum_Ico_consecutive _ (by norm_num) (by norm_num)]
  rw [Finset.range_eq_Ico]

/-- **The `J` form at the common scale.** -/
theorem Jint_eq_JformM :
    (Jint : ℚ) = ((24 ! : ℕ) : ℚ) ^ 2 * ((101 ! : ℕ) : ℚ) * JformM 13 54 cs54 := by
  have hn : nW = 1236 := rfl
  have hrow : ∑ x ∈ range 1236, rowJ x = ∑ x ∈ range 1236, ∑ y ∈ range 1236,
      (WBT.getB x).2 * (WBT.getB y).2 *
        WJtree.findB ((WBT.getB x).1 + (WBT.getB y).1) := by
    rw [← half_sum_eq 1236 _ (fun i j => by ring_nf)]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold rowJ
    rw [hn, two_mul ((WBT.getB x).1)]
  rw [Jint_eq_sum, hrow]
  push_cast
  have hval : ∀ x ∈ range 1236, ∀ y ∈ range 1236,
      ((WBT.getB x).2 : ℚ) * ((WBT.getB y).2 : ℚ) *
        ((WJtree.findB ((WBT.getB x).1 + (WBT.getB y).1) : ℤ) : ℚ)
      = (fs Tm (WBT.getB x).1 : ℚ) * (fs Tm (WBT.getB y).1 : ℚ) *
        ((WJtree.findB ((WBT.getB x).1 + (WBT.getB y).1) : ℤ) : ℚ) := by
    intro x hx y hy
    rw [(Tm_run x (Finset.mem_range.mp hx)).1, (Tm_run y (Finset.mem_range.mp hy)).1]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hval x hx y hy]
  rw [Finset.sum_congr rfl fun x _ => reindex (fun u => (fs Tm (WBT.getB x).1 : ℚ) *
    (fs Tm u : ℚ) * ((WJtree.findB ((WBT.getB x).1 + u) : ℤ) : ℚ))]
  rw [reindex (fun v => ∑ K ∈ keysJM 13 cs54, (fs Tm v : ℚ) * (fs Tm (encK K) : ℚ) *
    ((WJtree.findB (v + encK K) : ℤ) : ℚ))]
  unfold JformM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K' hK' => ?_
  have b := keysJM_bound hK
  have b' := keysJM_bound hK'
  rw [fs_encK hK, fs_encK hK']
  unfold encK
  rw [encKey_ofFn_add, WJtree_eq _ _ (by rw [weight_add]; omega),
    show (54 - 1 : ℕ) = 53 from rfl]
  ring

end SaltC1.MaynardK
