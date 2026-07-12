/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs

/-!
# The remainder product (blueprint `p0`, node B4)

The bound (2.12) of Halberstam–Richert, *A new look at Brun's sieve*, Mém. SMF
**25** (1971) 97–106 (numdam `10.24033/msmf.39`), p. 104:
```
  Σ_{d | P(z)} χ_ν(d)·ω(d) ≤ (1 + A·π(z))^{2b−ν+1} · ∏_{n=1}^{r−1} (1 + A·π(z_n))²
```
`r = minLevel Λ z` (B0), `π = Nat.primeCounting`.  With hypothesis **(R)**
`|R_d| ≤ ω(d)` this bounds `Σ_{d∣P(z)} χ_ν(d)|R_d|` — the shape node B5 consumes.

## The mechanism (H-R's "simple combinatorial argument", p. 104)

Every squarefree `d ∣ P(z)` with `χ_ν(d) = 1` factors along the ladder blocks
`[z_{n+1}, z_n)`.  The restricted-count caps of `χ_ν` say: at most `2b−ν+1` prime
factors lie in the top range `[z_1, z)`, and each rung down adds at most `2`
(the increment of `blockBound`).  Peeling the top block and recursing, each block
contributes a factor `(1 + Σ_{p<z_n} ω(p))^{cap increment}`; the *cumulative* cap
is respected by an `F`-lemma that carries the sub-ladder weight `x^{e−|S|}`.

The engine is two pure-`Finset` inequalities:

* `capSum_le` — the `F`-lemma: `Σ_{S⊆B,|S|≤e} (∏_S ω)·x^{e−|S|} ≤ (x + Σ_B ω)^e`
  (induction on `B`; the cumulative-cap absorber).
* `sum_powerset_disjUnion` — subsets of a disjoint union split as a nested sum
  (the block peel).
-/

open Finset Nat

namespace Salt.BrunLower

/-! ## The `F`-lemma: a cumulative-cap absorber -/

/-- **The `F`-lemma.**  For nonnegative weights `ω` on a finite set `B`, a base
`x ≥ 0`, and a cap `e`, the capped weighted subset-sum is dominated by a single
`e`-th power:
```
  Σ_{S ⊆ B, |S| ≤ e} (∏_{p∈S} ω p)·x^{e−|S|} ≤ (x + Σ_{p∈B} ω p)^e.
```
The weight `x^{e−|S|}` is the sub-ladder contribution that lets the block recursion
absorb a smaller top count into extra budget below.  Proved by induction on `B`. -/
lemma capSum_le (ω : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ∀ (B : Finset ℕ), (∀ p ∈ B, 0 ≤ ω p) → ∀ e : ℕ,
      ∑ S ∈ B.powerset.filter (fun S => S.card ≤ e), (∏ p ∈ S, ω p) * x ^ (e - S.card)
        ≤ (x + ∑ p ∈ B, ω p) ^ e := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _ e
    simp [Finset.filter_singleton]
  | @insert a B' ha IH =>
    intro hnn e
    have hnnB' : ∀ p ∈ B', 0 ≤ ω p := fun p hp => hnn p (mem_insert_of_mem hp)
    have hωa : 0 ≤ ω a := hnn a (mem_insert_self a B')
    have hsumB' : 0 ≤ ∑ p ∈ B', ω p := Finset.sum_nonneg hnnB'
    have hxB' : 0 ≤ x + ∑ p ∈ B', ω p := by linarith
    have hsum_insert : ∑ p ∈ insert a B', ω p = ω a + ∑ p ∈ B', ω p := Finset.sum_insert ha
    have hinj : ∀ S ∈ B'.powerset, ∀ T ∈ B'.powerset, insert a S = insert a T → S = T := by
      intro S hS T hT hST
      rw [Finset.mem_powerset] at hS hT
      have haS : a ∉ S := fun h => ha (hS h)
      have haT : a ∉ T := fun h => ha (hT h)
      rw [← Finset.erase_insert haS, ← Finset.erase_insert haT, hST]
    have hsplit :
        (insert a B').powerset.filter (fun S => S.card ≤ e)
          = (B'.powerset.filter (fun S => S.card ≤ e))
            ∪ ((B'.powerset.image (insert a)).filter (fun S => S.card ≤ e)) := by
      rw [Finset.powerset_insert, Finset.filter_union]
    have hdisj :
        Disjoint (B'.powerset.filter (fun S => S.card ≤ e))
          ((B'.powerset.image (insert a)).filter (fun S => S.card ≤ e)) := by
      rw [Finset.disjoint_left]
      intro S hS hS'
      rw [Finset.mem_filter, Finset.mem_image] at hS'
      obtain ⟨⟨T, _, rfl⟩, _⟩ := hS'
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      exact ha (hS.1 (Finset.mem_insert_self a T))
    have hterm : ∀ T ∈ B'.powerset,
        (if (insert a T).card ≤ e then (∏ p ∈ insert a T, ω p) * x ^ (e - (insert a T).card) else 0)
          = (if T.card + 1 ≤ e then ω a * ((∏ p ∈ T, ω p) * x ^ (e - (T.card + 1))) else 0) := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      have haT : a ∉ T := fun h => ha (hT h)
      rw [Finset.card_insert_of_notMem haT, Finset.prod_insert haT]
      split_ifs <;> ring
    have key2 :
        ∑ S ∈ (B'.powerset.image (insert a)).filter (fun S => S.card ≤ e),
            (∏ p ∈ S, ω p) * x ^ (e - S.card)
          = ω a * ∑ T ∈ B'.powerset.filter (fun T => T.card + 1 ≤ e),
              (∏ p ∈ T, ω p) * x ^ (e - (T.card + 1)) := by
      rw [Finset.sum_filter, Finset.sum_image hinj, Finset.sum_congr rfl hterm,
        ← Finset.sum_filter, ← Finset.mul_sum]
    rw [hsplit, Finset.sum_union hdisj, key2, hsum_insert]
    set sumB := ∑ p ∈ B', ω p with hSdef
    rcases e with _ | e''
    · -- `e = 0`: the image piece vanishes.
      have hempty : B'.powerset.filter (fun T => T.card + 1 ≤ 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr; intro T _; omega
      rw [hempty, Finset.sum_empty, mul_zero, add_zero, pow_zero]
      simpa using IH hnnB' 0
    · -- `e = e'' + 1`: peel the top power and use both `IH` instances.
      have hfst := IH hnnB' (e'' + 1)
      have hfilt : B'.powerset.filter (fun T => T.card + 1 ≤ e'' + 1)
          = B'.powerset.filter (fun T => T.card ≤ e'') := by
        ext T; simp only [Finset.mem_filter]
        constructor <;> (rintro ⟨h, h2⟩; exact ⟨h, by omega⟩)
      have hsnd : ∑ T ∈ B'.powerset.filter (fun T => T.card + 1 ≤ e'' + 1),
          (∏ p ∈ T, ω p) * x ^ (e'' + 1 - (T.card + 1))
            ≤ (x + sumB) ^ e'' := by
        rw [hfilt]
        refine le_trans (le_of_eq ?_) (IH hnnB' e'')
        apply Finset.sum_congr rfl; intro T _
        rw [Nat.add_sub_add_right]
      have hPQ : (x + sumB) ^ e'' ≤ (x + (ω a + sumB)) ^ e'' :=
        pow_le_pow_left₀ hxB' (by linarith) e''
      have hc : (0 : ℝ) ≤ x + (ω a + sumB) := by linarith
      calc
        (∑ S ∈ B'.powerset.filter (fun S => S.card ≤ e'' + 1),
            (∏ p ∈ S, ω p) * x ^ (e'' + 1 - S.card))
            + ω a * ∑ T ∈ B'.powerset.filter (fun T => T.card + 1 ≤ e'' + 1),
                (∏ p ∈ T, ω p) * x ^ (e'' + 1 - (T.card + 1))
          ≤ (x + sumB) ^ (e'' + 1) + ω a * (x + sumB) ^ e'' :=
            add_le_add hfst (mul_le_mul_of_nonneg_left hsnd hωa)
        _ = (x + sumB) ^ e'' * (x + (ω a + sumB)) := by rw [pow_succ]; ring
        _ ≤ (x + (ω a + sumB)) ^ e'' * (x + (ω a + sumB)) :=
            mul_le_mul_of_nonneg_right hPQ hc
        _ = (x + (ω a + sumB)) ^ (e'' + 1) := by rw [pow_succ]

/-! ## The block peel: powersets of a disjoint union -/

/-- Subsets of a disjoint union split as a nested sum: `S ↦ (S ∩ B, S ∩ P')`. -/
lemma sum_powerset_disjUnion {α : Type*} [DecidableEq α] (B P' : Finset α)
    (hd : Disjoint B P') (g : Finset α → ℝ) :
    ∑ S ∈ (B ∪ P').powerset, g S
      = ∑ S₁ ∈ B.powerset, ∑ S' ∈ P'.powerset, g (S₁ ∪ S') := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun S _ => (S ∩ B, S ∩ P'))
    (j := fun q _ => q.1 ∪ q.2)
    (fun S hS => ?_) (fun q hq => ?_) (fun S hS => ?_) (fun q hq => ?_) (fun S hS => ?_)
  · rw [Finset.mem_powerset] at hS
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    rw [Finset.mem_powerset]
    exact Finset.union_subset (hq.1.trans Finset.subset_union_left)
      (hq.2.trans Finset.subset_union_right)
  · rw [Finset.mem_powerset] at hS
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]
  · rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hq
    obtain ⟨h1, h2⟩ := hq
    have e1 : (q.1 ∪ q.2) ∩ B = q.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1,
        Finset.disjoint_iff_inter_eq_empty.mp ((hd.mono_right h2).symm), Finset.union_empty]
    have e2 : (q.1 ∪ q.2) ∩ P' = q.2 := by
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp (hd.mono_left h1),
        Finset.inter_eq_left.mpr h2, Finset.empty_union]
    rw [e1, e2]
  · rw [Finset.mem_powerset] at hS
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]

/-! ## The block recursion (induction on the number of ladder levels) -/

/-- The block cap predicate: at every level `n ∈ [1,m]` the number of members of `S`
that are `≥ thresh n` is at most `e + 2(n−1)`.  Named — with a classical `DecidablePred`
instance, exactly as for `chi` (B0) — so the block recursion uses it uniformly as a
`{0,1}` indicator (term-mode `if`s need a stable instance). -/
def capPred (thresh : ℕ → ℝ) (e m : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 1 m, (S.filter (fun p : ℕ => thresh n ≤ (p : ℝ))).card ≤ e + 2 * (n - 1)

noncomputable instance instDecidableCapPred (thresh : ℕ → ℝ) (e m : ℕ) :
    DecidablePred (capPred thresh e m) := fun _ => Classical.propDecidable _

/-- **The block master bound.**  For a decreasing threshold ladder `thresh` with
`thresh 0` at the top and `thresh m` at the bottom (all of `P` sits in
`[thresh m, thresh 0)`), the capped subset-sum — where the cap says at every level
`n ∈ [1,m]` the count of members `≥ thresh n` is `≤ e + 2(n−1)` — is bounded by the
top factor `(1 + Σ_P ω)^e` times block factors `(1 + Σ_{p<thresh n} ω)²`.  This is
the abstract form of H-R (2.12); the exponents `e = 2b−ν+1` (top) and `2` (each
rung) are exactly the increments of `blockBound`.  Proved by induction on `m`,
peeling the top block and absorbing its count via `capSum_le`. -/
lemma capSum_master (ω : ℕ → ℝ) :
    ∀ m : ℕ, 1 ≤ m → ∀ (e : ℕ) (P : Finset ℕ) (thresh : ℕ → ℝ),
      (∀ p ∈ P, 0 ≤ ω p) →
      (∀ p ∈ P, (p : ℝ) < thresh 0) →
      (∀ p ∈ P, thresh m ≤ (p : ℝ)) →
      (∀ i j : ℕ, i ≤ j → j ≤ m → thresh j ≤ thresh i) →
      ∑ S ∈ P.powerset.filter (capPred thresh e m), ∏ p ∈ S, ω p
        ≤ (1 + ∑ p ∈ P, ω p) ^ e
          * ∏ n ∈ Finset.Ico 1 m,
              (1 + ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < thresh n), ω p) ^ 2 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro e P thresh hωP _ hP_lo _
    rw [Finset.Ico_self, Finset.prod_empty, mul_one]
    have hfilt : P.powerset.filter (capPred thresh e 1)
        = P.powerset.filter (fun S => S.card ≤ e) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, capPred, Finset.Icc_self,
        Finset.mem_singleton, forall_eq]
      constructor
      · rintro ⟨hSP, hcard⟩
        refine ⟨hSP, ?_⟩
        have hall : S.filter (fun p : ℕ => thresh 1 ≤ (p : ℝ)) = S :=
          Finset.filter_true_of_mem (fun p hp => hP_lo p (hSP hp))
        rw [hall] at hcard; simpa using hcard
      · rintro ⟨hSP, hcard⟩
        refine ⟨hSP, ?_⟩
        have hall : S.filter (fun p : ℕ => thresh 1 ≤ (p : ℝ)) = S :=
          Finset.filter_true_of_mem (fun p hp => hP_lo p (hSP hp))
        rw [hall]; simpa using hcard
    rw [hfilt]
    simpa using capSum_le ω (by norm_num : (0 : ℝ) ≤ 1) P hωP e
  | succ m hm IH =>
    intro e P thresh hωP hP_hi hP_lo hmono
    -- The top block `B` and the remainder `P'`.
    set B := P.filter (fun p : ℕ => thresh 1 ≤ (p : ℝ)) with hBdef
    set P' := P.filter (fun p : ℕ => ¬ (thresh 1 ≤ (p : ℝ))) with hP'def
    have hpart : P = B ∪ P' := by
      rw [hBdef, hP'def]
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        by_cases h : thresh 1 ≤ (p : ℝ)
        · exact Or.inl ⟨hp, h⟩
        · exact Or.inr ⟨hp, h⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj : Disjoint B P' := by
      rw [hBdef, hP'def, Finset.disjoint_left]
      intro p hp hp'
      rw [Finset.mem_filter] at hp hp'
      exact hp'.2 hp.2
    have hBsub : B ⊆ P := by rw [hBdef]; exact Finset.filter_subset _ _
    have hP'sub : P' ⊆ P := by rw [hP'def]; exact Finset.filter_subset _ _
    have hωB : ∀ p ∈ B, 0 ≤ ω p := fun p hp => hωP p (hBsub hp)
    have hωP' : ∀ p ∈ P', 0 ≤ ω p := fun p hp => hωP p (hP'sub hp)
    -- `P'` is exactly the primes below `thresh 1`.
    have hP'lt : P' = P.filter (fun p : ℕ => (p : ℝ) < thresh 1) := by
      rw [hP'def]; apply Finset.filter_congr; intro p _; simp [not_le]
    -- Members of `B` all pass every level filter `n ∈ [1, m+1]`.
    have hS1filter : ∀ (S₁ : Finset ℕ), S₁ ⊆ B → ∀ n, 1 ≤ n → n ≤ m + 1 →
        S₁.filter (fun p : ℕ => thresh n ≤ (p : ℝ)) = S₁ := by
      intro S₁ hS₁ n hn1 hnm
      apply Finset.filter_true_of_mem
      intro p hp
      have hpB : thresh 1 ≤ (p : ℝ) := by
        have := hS₁ hp; rw [hBdef, Finset.mem_filter] at this; exact this.2
      exact le_trans (hmono 1 n hn1 hnm) hpB
    -- Members of `P'` fail the top filter.
    have hP'filter1 : ∀ (S' : Finset ℕ), S' ⊆ P' →
        S'.filter (fun p : ℕ => thresh 1 ≤ (p : ℝ)) = ∅ := by
      intro S' hS'
      apply Finset.filter_false_of_mem
      intro p hp
      have := hS' hp; rw [hP'def, Finset.mem_filter] at this; exact this.2
    -- Level counts split additively across the block boundary.
    have hcount : ∀ (S₁ S' : Finset ℕ), S₁ ⊆ B → S' ⊆ P' → ∀ n, 1 ≤ n → n ≤ m + 1 →
        ((S₁ ∪ S').filter (fun p : ℕ => thresh n ≤ (p : ℝ))).card
          = S₁.card + (S'.filter (fun p : ℕ => thresh n ≤ (p : ℝ))).card := by
      intro S₁ S' hS₁ hS' n hn1 hnm
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Disjoint.mono hS₁ hS' hdisj)),
        hS1filter S₁ hS₁ n hn1 hnm]
    -- The cap on `S₁ ∪ S'` factors into `|S₁| ≤ e` and a shifted cap on `S'`.
    have hcap_iff : ∀ (S₁ S' : Finset ℕ), S₁ ⊆ B → S' ⊆ P' →
        (capPred thresh e (m + 1) (S₁ ∪ S')
          ↔ (S₁.card ≤ e ∧ capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m S')) := by
      intro S₁ S' hS₁ hS'
      simp only [capPred]
      constructor
      · intro hcap
        have hSe : S₁.card ≤ e := by
          have h1 := hcap 1 (by rw [Finset.mem_Icc]; omega)
          rw [hcount S₁ S' hS₁ hS' 1 (by omega) (by omega),
            hP'filter1 S' hS'] at h1
          simpa using h1
        refine ⟨hSe, fun k hk => ?_⟩
        rw [Finset.mem_Icc] at hk
        have hn := hcap (k + 1) (by rw [Finset.mem_Icc]; omega)
        rw [hcount S₁ S' hS₁ hS' (k + 1) (by omega) (by omega)] at hn
        omega
      · rintro ⟨hSe, hcap'⟩ n hn
        rw [Finset.mem_Icc] at hn
        obtain ⟨hn1, hn2⟩ := hn
        rw [hcount S₁ S' hS₁ hS' n hn1 hn2]
        rcases Nat.lt_or_ge 1 n with h2 | h1
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          have hk := hcap' k (by rw [Finset.mem_Icc]; omega)
          omega
        · have hn_eq : n = 1 := le_antisymm h1 hn1
          subst hn_eq
          rw [hP'filter1 S' hS']
          simpa using hSe
    -- Rewrite the LHS as a nested sum over `(B, P')` and factor.
    rw [Finset.sum_filter, show P.powerset = (B ∪ P').powerset from by rw [← hpart],
      sum_powerset_disjUnion B P' hdisj]
    have hpre : ∀ S₁ ∈ B.powerset, ∀ S' ∈ P'.powerset,
        (if capPred thresh e (m + 1) (S₁ ∪ S') then ∏ p ∈ S₁ ∪ S', ω p else 0)
          = (if (S₁.card ≤ e ∧ capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m S')
              then (∏ p ∈ S₁, ω p) * (∏ p ∈ S', ω p) else 0) := by
      intro S₁ hS₁ S' hS'
      rw [Finset.mem_powerset] at hS₁ hS'
      rw [Finset.prod_union (Disjoint.mono hS₁ hS' hdisj)]
      exact if_congr (hcap_iff S₁ S' hS₁ hS') rfl rfl
    rw [Finset.sum_congr rfl (fun S₁ hS₁ =>
      Finset.sum_congr rfl (fun S' hS' => hpre S₁ hS₁ S' hS'))]
    -- Push the outer/inner `if`s into filters (`I(S₁)` is the inner filtered sum).
    have hinner : ∀ S₁ ∈ B.powerset,
        (∑ S' ∈ P'.powerset, if (S₁.card ≤ e ∧
              capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m S')
            then (∏ p ∈ S₁, ω p) * (∏ p ∈ S', ω p) else 0)
          = if S₁.card ≤ e then (∏ p ∈ S₁, ω p)
              * ∑ S' ∈ P'.powerset.filter
                  (capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m), ∏ p ∈ S', ω p
            else 0 := by
      intro S₁ _
      by_cases hA : S₁.card ≤ e
      · rw [if_pos hA, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro S' _
        simp only [hA, true_and]
      · rw [if_neg hA]
        apply Finset.sum_eq_zero; intro S' _
        simp [hA]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
    -- Apply the IH to each inner sum, then the `F`-lemma to the outer sum.
    set c₁ := ∑ p ∈ P', ω p with hc1def
    set D := ∏ k ∈ Finset.Ico 1 m,
        (1 + ∑ p ∈ P'.filter (fun p : ℕ => (p : ℝ) < thresh (k + 1)), ω p) ^ 2 with hDdef
    have hIH : ∀ S₁ ∈ B.powerset.filter (fun S₁ => S₁.card ≤ e),
        (∑ S' ∈ P'.powerset.filter
            (capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m), ∏ p ∈ S', ω p)
          ≤ (1 + c₁) ^ (e - S₁.card + 2) * D := by
      intro S₁ _
      have := IH (e - S₁.card + 2) P' (fun i => thresh (i + 1)) hωP'
        (fun p hp => by
          rw [hP'lt, Finset.mem_filter] at hp; exact hp.2)
        (fun p hp => hP_lo p (hP'sub hp))
        (fun i j hij hjm => hmono (i + 1) (j + 1) (by omega) (by omega))
      simpa only [hc1def, hDdef] using this
    calc
      (∑ S₁ ∈ B.powerset.filter (fun S₁ => S₁.card ≤ e), (∏ p ∈ S₁, ω p)
          * ∑ S' ∈ P'.powerset.filter
              (capPred (fun i => thresh (i + 1)) (e - S₁.card + 2) m), ∏ p ∈ S', ω p)
        ≤ ∑ S₁ ∈ B.powerset.filter (fun S₁ => S₁.card ≤ e), (∏ p ∈ S₁, ω p)
            * ((1 + c₁) ^ (e - S₁.card + 2) * D) := by
          apply Finset.sum_le_sum; intro S₁ hS₁
          exact mul_le_mul_of_nonneg_left (hIH S₁ hS₁)
            (Finset.prod_nonneg (fun p hp => hωB p
              (Finset.mem_powerset.mp (Finset.mem_of_mem_filter S₁ hS₁) hp)))
      _ = D * (1 + c₁) ^ 2 * ∑ S₁ ∈ B.powerset.filter (fun S₁ => S₁.card ≤ e),
              (∏ p ∈ S₁, ω p) * (1 + c₁) ^ (e - S₁.card) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S₁ _
          rw [show e - S₁.card + 2 = (e - S₁.card) + 2 from rfl, pow_add]
          ring
      _ ≤ D * (1 + c₁) ^ 2 * (1 + ∑ p ∈ P, ω p) ^ e := by
          have hc1nn : (0 : ℝ) ≤ 1 + c₁ := by
            have : 0 ≤ c₁ := Finset.sum_nonneg hωP'
            linarith
          have hFL := capSum_le ω hc1nn B hωB e
          have hsplitP : ∑ p ∈ P, ω p = ∑ p ∈ B, ω p + c₁ := by
            rw [hc1def, hpart, Finset.sum_union hdisj]
          have hDnn : 0 ≤ D := by
            apply Finset.prod_nonneg; intro k _; positivity
          have hpow2 : (0 : ℝ) ≤ (1 + c₁) ^ 2 := by positivity
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ S₁ ∈ B.powerset.filter (fun S₁ => S₁.card ≤ e),
                (∏ p ∈ S₁, ω p) * (1 + c₁) ^ (e - S₁.card)
              ≤ (1 + c₁ + ∑ p ∈ B, ω p) ^ e := hFL
            _ = (1 + ∑ p ∈ P, ω p) ^ e := by rw [hsplitP]; ring_nf
      _ = (1 + ∑ p ∈ P, ω p) ^ e
            * ∏ n ∈ Finset.Ico 1 (m + 1),
                (1 + ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < thresh n), ω p) ^ 2 := by
          -- `c₁ = c 1`, and `D` reindexes to the `Ico 2 (m+1)` tail.
          have hc1 : c₁ = ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < thresh 1), ω p := by
            rw [hc1def, hP'lt]
          have hDeq : D = ∏ n ∈ Finset.Ico 2 (m + 1),
              (1 + ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < thresh n), ω p) ^ 2 := by
            rw [hDdef]
            rw [show (2 : ℕ) = 1 + 1 from rfl, ← Finset.map_add_right_Ico 1 m 1, Finset.prod_map]
            apply Finset.prod_congr rfl; intro k hk
            rw [Finset.mem_Ico] at hk
            have hfe : P'.filter (fun p : ℕ => (p : ℝ) < thresh (k + 1))
                = P.filter (fun p : ℕ => (p : ℝ) < thresh (k + 1)) := by
              rw [hP'lt, Finset.filter_filter]
              apply Finset.filter_congr; intro p _
              have hmono' : thresh (k + 1) ≤ thresh 1 := hmono 1 (k + 1) (by omega) (by omega)
              constructor
              · intro h; exact h.2
              · intro h; exact ⟨lt_of_lt_of_le h hmono', h⟩
            simp only [addRightEmbedding_apply]
            rw [hfe]
          rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : 1 < m + 1), hDeq, ← hc1]
          ring

/-! ## Dressing: prime counting, the divisor bijection, and the `χ_ν`/cap bridge -/

/-- The weight sum over a set of primes all below `w` is `≤ A·π(w)` (uses **(Ω)**
`ω(p) ≤ A` and the prime-count bound `|P| ≤ π(⌊w⌋₊)`). -/
lemma sum_omega_le_pi {A : ℝ} (hA : 1 ≤ A) {ω : ℕ → ℝ} {P : Finset ℕ} {w : ℝ}
    (hPprime : ∀ p ∈ P, p.Prime) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hPlt : ∀ p ∈ P, (p : ℝ) < w) :
    ∑ p ∈ P, ω p ≤ A * (Nat.primeCounting ⌊w⌋₊ : ℝ) := by
  have hcard : P.card ≤ Nat.primeCounting ⌊w⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    have hle : p ≤ ⌊w⌋₊ := Nat.le_floor (le_of_lt (hPlt p hp))
    exact Nat.mem_primesBelow.mpr ⟨by omega, hPprime p hp⟩
  calc ∑ p ∈ P, ω p ≤ ∑ _p ∈ P, A := Finset.sum_le_sum (fun p hp => hωA p (hPprime p hp))
    _ = P.card * A := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.primeCounting ⌊w⌋₊ : ℝ) * A :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by linarith)
    _ = A * (Nat.primeCounting ⌊w⌋₊ : ℝ) := by ring

/-- The divisor sum over a squarefree `N` reindexes along the powerset of its prime
factors (`d ↦ d.primeFactors`, inverse `S ↦ ∏ S`). -/
lemma sum_divisors_squarefree_eq_powerset {N : ℕ} (hN : Squarefree N) (F : ℕ → ℝ) :
    ∑ d ∈ N.divisors, F d = ∑ S ∈ N.primeFactors.powerset, F (∏ p ∈ S, p) := by
  refine Finset.sum_bij' (i := fun d _ => d.primeFactors) (j := fun S _ => ∏ p ∈ S, p)
    (fun d hd => ?_) (fun S hS => ?_) (fun d hd => ?_) (fun S hS => ?_) (fun d hd => ?_)
  · rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hN.ne_zero
  · rw [Finset.mem_powerset] at hS
    have hdvd : (∏ p ∈ S, p) ∣ N := by
      have h1 : (∏ p ∈ S, p) ∣ ∏ p ∈ N.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hS
      rwa [Nat.prod_primeFactors_of_squarefree hN] at h1
    exact Nat.mem_divisors.mpr ⟨hdvd, hN.ne_zero⟩
  · exact Nat.prod_primeFactors_of_squarefree
      (hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · rw [Finset.mem_powerset] at hS
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))
  · rw [Nat.prod_primeFactors_of_squarefree (hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

/-- **The `χ_ν`/cap bridge.**  For a squarefree divisor `d = ∏ S` (`S` a set of primes
below `z`), the H-R block predicate `chi` (all levels `n ≥ 1`) coincides with the
truncated `capPred` (levels `n ≤ r`): below the ladder bottom `z_r ≤ 2` every prime
counts, so the bottom cap subsumes all deeper levels. -/
lemma chi_iff_capPred {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) {side b : ℕ}
    (hb : 1 ≤ b) (hside : side = 1 ∨ side = 2) {S : Finset ℕ}
    (hSprime : ∀ p ∈ S, p.Prime) :
    chi Lam z side b (∏ p ∈ S, p)
      ↔ capPred (zLev Lam z) (2 * b - side + 1) (minLevel Lam z) S := by
  have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hSprime
  have hcnt : ∀ n, bigOmegaGe Lam z n (∏ p ∈ S, p)
      = (S.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ))).card := by
    intro n; unfold bigOmegaGe; rw [hpf]
  have hs2 : side ≤ 2 := by rcases hside with h | h <;> omega
  have hr1 : 1 ≤ minLevel Lam z := (minLevel_mem hLam hz).1
  -- Below the bottom every prime of `S` counts.
  have hfull : ∀ n, minLevel Lam z ≤ n →
      (S.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ))).card = S.card := by
    intro n hn
    rw [Finset.filter_true_of_mem (fun p hp => ?_)]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSprime p hp).two_le
    have hzr : zLev Lam z (minLevel Lam z) ≤ 2 := zLev_minLevel_le_two hLam hz
    have hzn : zLev Lam z n ≤ zLev Lam z (minLevel Lam z) := zLev_antitone hLam.le hz.le hn
    linarith
  constructor
  · intro hchi n hn
    rw [Finset.mem_Icc] at hn
    have h := hchi n hn.1
    rw [hcnt] at h
    unfold blockBound at h
    omega
  · intro hcap n hn1
    rw [hcnt]
    unfold blockBound
    rcases Nat.lt_or_ge n (minLevel Lam z) with hnr | hnr
    · have h := hcap n (Finset.mem_Icc.mpr ⟨hn1, hnr.le⟩)
      omega
    · have hrmem := hcap (minLevel Lam z) (Finset.mem_Icc.mpr ⟨hr1, le_refl _⟩)
      rw [hfull (minLevel Lam z) (le_refl _)] at hrmem
      rw [hfull n hnr]
      omega

/-! ## The remainder product (2.12) -/

/-- **The remainder product (H-R (2.12)).**  For a squarefree `N ∣ P(z)` (all prime
factors below `z`), a nonnegative multiplicative-on-coprimes `ω` with **(Ω)**
`ω(p) ≤ A` (`A ≥ 1`), and `r = minLevel Λ z`:
```
  Σ_{d ∣ N} χ_ν(d)·ω(d) ≤ (1 + A·π(z))^{2b−ν+1} · ∏_{n=1}^{r−1} (1 + A·π(z_n))²
```
with `π = Nat.primeCounting`, `z_n = zLev Λ z n`. -/
theorem remainder_prod_bound {Lam z A : ℝ} {b side N : ℕ} {ω : ℕ → ℝ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b) (hside : side = 1 ∨ side = 2) (hA : 1 ≤ A)
    (hNsf : Squarefree N) (hNlt : ∀ p ∈ N.primeFactors, (p : ℝ) < z)
    (hωnn : ∀ p, p.Prime → 0 ≤ ω p) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hωprod : ∀ d, Squarefree d → ω d = ∏ p ∈ d.primeFactors, ω p) :
    ∑ d ∈ N.divisors, (if chi Lam z side b d then ω d else 0)
      ≤ (1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b - side + 1)
        * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
            (1 + A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2 := by
  have hz0 : (0 : ℝ) < z := by linarith
  -- (A) Reindex the divisor sum over the powerset, converting `χ_ν` to `capPred`.
  have hstep1 : ∑ d ∈ N.divisors, (if chi Lam z side b d then ω d else 0)
      = ∑ S ∈ N.primeFactors.powerset.filter
          (capPred (zLev Lam z) (2 * b - side + 1) (minLevel Lam z)), ∏ p ∈ S, ω p := by
    rw [sum_divisors_squarefree_eq_powerset hNsf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
    have hdvd : (∏ p ∈ S, p) ∣ N := by
      have h1 : (∏ p ∈ S, p) ∣ ∏ p ∈ N.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hS
      rwa [Nat.prod_primeFactors_of_squarefree hNsf] at h1
    have hsqf : Squarefree (∏ p ∈ S, p) := hNsf.squarefree_of_dvd hdvd
    have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hSprime
    refine if_congr (chi_iff_capPred hLam hz hb hside hSprime) ?_ rfl
    rw [hωprod _ hsqf, hpf]
  rw [hstep1]
  -- (B) The block master bound.
  have hr1 : 1 ≤ minLevel Lam z := (minLevel_mem hLam hz).1
  refine le_trans (capSum_master ω (minLevel Lam z) hr1 (2 * b - side + 1) N.primeFactors
    (zLev Lam z)
    (fun p hp => hωnn p (Nat.prime_of_mem_primeFactors hp))
    (fun p hp => by rw [zLev_zero Lam z hz0]; exact hNlt p hp)
    (fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have := zLev_minLevel_le_two hLam hz; linarith)
    (fun i j hij _ => zLev_antitone hLam.le hz.le hij)) ?_
  -- (C) Monotone replacement of the weight sums by `A·π`.
  have hprime : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have htop : (1 : ℝ) + ∑ p ∈ N.primeFactors, ω p ≤ 1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ) := by
    have := sum_omega_le_pi hA hprime hωA hNlt; linarith
  have htopnn : (0 : ℝ) ≤ 1 + ∑ p ∈ N.primeFactors, ω p := by
    have : 0 ≤ ∑ p ∈ N.primeFactors, ω p :=
      Finset.sum_nonneg (fun p hp => hωnn p (hprime p hp))
    linarith
  apply mul_le_mul
  · exact pow_le_pow_left₀ htopnn htop _
  · apply Finset.prod_le_prod
    · intro n _; positivity
    · intro n _
      have hblknn : (0 : ℝ) ≤ 1 + ∑ p ∈ N.primeFactors.filter
          (fun p : ℕ => (p : ℝ) < zLev Lam z n), ω p := by
        have : 0 ≤ ∑ p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) < zLev Lam z n), ω p :=
          Finset.sum_nonneg (fun p hp => hωnn p (hprime p (Finset.mem_of_mem_filter p hp)))
        linarith
      have hblk : ∑ p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) < zLev Lam z n), ω p
          ≤ A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ) :=
        sum_omega_le_pi hA
          (fun p hp => hprime p (Finset.mem_of_mem_filter p hp)) hωA
          (fun p hp => (Finset.mem_filter.mp hp).2)
      exact pow_le_pow_left₀ hblknn (by linarith) 2
  · apply Finset.prod_nonneg; intro n _; positivity
  · positivity

/-- **The (R)-corollary — the shape node B5 consumes.**  If the remainders obey
**(R)** `|R_d| ≤ ω(d)` on divisors of `N`, then `Σ_{d ∣ N} χ_ν(d)|R_d|` is bounded by
the same product. -/
theorem remainder_prod_bound_of_R {Lam z A : ℝ} {b side N : ℕ} {ω R : ℕ → ℝ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b) (hside : side = 1 ∨ side = 2) (hA : 1 ≤ A)
    (hNsf : Squarefree N) (hNlt : ∀ p ∈ N.primeFactors, (p : ℝ) < z)
    (hωnn : ∀ p, p.Prime → 0 ≤ ω p) (hωA : ∀ p, p.Prime → ω p ≤ A)
    (hωprod : ∀ d, Squarefree d → ω d = ∏ p ∈ d.primeFactors, ω p)
    (hR : ∀ d ∈ N.divisors, |R d| ≤ ω d) :
    ∑ d ∈ N.divisors, (if chi Lam z side b d then |R d| else 0)
      ≤ (1 + A * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b - side + 1)
        * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
            (1 + A * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2 := by
  refine le_trans (Finset.sum_le_sum (fun d hd => ?_))
    (remainder_prod_bound hLam hz hb hside hA hNsf hNlt hωnn hωA hωprod)
  by_cases hc : chi Lam z side b d
  · rw [if_pos hc, if_pos hc]; exact hR d hd
  · rw [if_neg hc, if_neg hc]

end Salt.BrunLower
