/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHDetector

/-!
# The symmetric √N Dirichlet hyperbola (mathlib TODO `Misc.lean:428`)

This module lands the classical **symmetric** Dirichlet-hyperbola identity — the
length-`√N` refinement of the asymmetric length-`N` reindexing already in mathlib
(`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`, our `dhA_hyperbola`). It is the exact
antidiagonal bookkeeping

  `Σ_{n≤N} Σ_{d∣n} a d · b (n/d)`
    `= Σ_{d≤√N} a d · (Σ_{e≤N/d} b e) + Σ_{e≤√N} b e · (Σ_{d≤N/e} a d)`
      `- (Σ_{d≤√N} a d) · (Σ_{e≤√N} b e)`,

with the split at `Nat.sqrt N`. The region `R = {(d,e) : 1≤d, 1≤e, d·e ≤ N}` is
`A ∪ B` where `A = {d ≤ √N}`, `B = {e ≤ √N}` and `A ∩ B = {d ≤ √N ∧ e ≤ √N}`;
the identity is inclusion–exclusion (`Finset.sum_union_inter`) plus the two `√N`
facts `Nat.sqrt_le` (`√N·√N ≤ N`) and `Nat.lt_succ_sqrt` (`N < (√N+1)²`).

* `sum_divisors_eq_hyperbola_symm` — the GENERAL identity for any `a b : ℕ → M`
  over a commutative ring `M` (mathlib-clean; this is the unfulfilled TODO).
* `dhA_hyperbola_symm` — the `b = 1` instance for the DH detector `dhA`, the exact
  shape the T-BAL R3 balance (`dhA_mass_upper`) consumes.
-/

namespace Salt.SW

/-- `{e ∈ [1,N] : k·e ≤ N} = [1, N/k]` for `k > 0` (the inner hyperbola block). -/
private lemma Icc_filter_mul_le (k N : ℕ) (hk : 0 < k) :
    (Finset.Icc 1 N).filter (fun x => k * x ≤ N) = Finset.Icc 1 (N / k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hx1, _⟩, hkx⟩
    exact ⟨hx1, (Nat.le_div_iff_mul_le hk).mpr (by rwa [Nat.mul_comm] at hkx)⟩
  · rintro ⟨hx1, hxd⟩
    refine ⟨⟨hx1, le_trans hxd (Nat.div_le_self N k)⟩, ?_⟩
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp hxd

/-- `Σ_{x∈[1,m]} 1 = m` over `ℝ` (the `b = 1` collapse of an inner block). -/
private lemma sum_Icc_one (m : ℕ) : ∑ _x ∈ Finset.Icc 1 m, (1 : ℝ) = (m : ℝ) := by
  rw [Finset.sum_const, Nat.card_Icc]
  simp

/-- **The symmetric √N Dirichlet hyperbola.** For any `a b : ℕ → M` (`M` a
commutative ring) the sum of the Dirichlet convolution `a ∗ b` over `[1,N]` splits at
`Nat.sqrt N` into a `d`-short leg, an `e`-short leg, and the doubly-counted corner
block. EXACT — pure antidiagonal bookkeeping, no estimates. This is the unfulfilled
mathlib TODO at `ArithmeticFunction/Misc.lean:428`. -/
theorem sum_divisors_eq_hyperbola_symm {M : Type*} [CommRing M] (a b : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d)
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), a d * ∑ e ∈ Finset.Icc 1 (N / d), b e)
        + (∑ e ∈ Finset.Icc 1 (Nat.sqrt N), b e * ∑ d ∈ Finset.Icc 1 (N / e), a d)
        - (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), a d)
          * ∑ e ∈ Finset.Icc 1 (Nat.sqrt N), b e := by
  set r := Nat.sqrt N with hr
  set R := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N) with hRdef
  have hrN : r ≤ N := by rw [hr]; exact Nat.sqrt_le_self N
  have hrr : r * r ≤ N := by rw [hr]; exact Nat.sqrt_le N
  have hsub : Finset.Icc 1 r ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hrN
  -- Bridge: the convolution double-sum is the sum over the region `R`.
  have bridge : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d)
      = ∑ p ∈ R, a p.1 * b p.2 := by
    rw [Finset.sum_congr rfl
        (fun n _ => (Nat.sum_divisorsAntidiagonal (fun x y => a x * b y)).symm)]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ)
        (fun n => n.divisorsAntidiagonal) := by
      intro m _ n _ hmn
      simp only [Function.onFun, Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
      rintro p ⟨hpm, -⟩ ⟨hpn, -⟩
      exact hmn (hpm.symm.trans hpn)
    rw [← Finset.sum_biUnion hdisj, hRdef]
    congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨n, ⟨hn1, hnN⟩, hprod, -⟩
      subst hprod
      have hp1 : 0 < p.1 := by
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h, Nat.zero_mul] at hn1; omega
        · exact h
      have hp2 : 0 < p.2 := by
        rcases Nat.eq_zero_or_pos p.2 with h | h
        · rw [h, Nat.mul_zero] at hn1; omega
        · exact h
      have hle1 : p.1 ≤ p.1 * p.2 := le_mul_of_one_le_right (Nat.zero_le _) hp2
      have hle2 : p.2 ≤ p.1 * p.2 := le_mul_of_one_le_left (Nat.zero_le _) hp1
      exact ⟨⟨⟨hp1, by omega⟩, hp2, by omega⟩, hnN⟩
    · rintro ⟨⟨⟨hp1, _⟩, hp2, _⟩, hle⟩
      exact ⟨p.1 * p.2, ⟨Nat.mul_pos hp1 hp2, hle⟩, rfl, (Nat.mul_pos hp1 hp2).ne'⟩
  set A := R.filter (fun p => p.1 ≤ r) with hAdef
  set B := R.filter (fun p => p.2 ≤ r) with hBdef
  -- `A ∪ B = R`: every `(d,e)` with `d·e ≤ N` has `d ≤ √N` or `e ≤ √N`.
  have hunion : A ∪ B = R := by
    rw [hAdef, hBdef, ← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro p hp
    have hle : p.1 * p.2 ≤ N := by rw [hRdef, Finset.mem_filter] at hp; exact hp.2
    by_contra h
    have hge : Nat.succ r * Nat.succ r ≤ p.1 * p.2 := Nat.mul_le_mul (by omega) (by omega)
    have hlt : N < Nat.succ r * Nat.succ r := by rw [hr]; exact Nat.lt_succ_sqrt N
    omega
  -- `A ∩ B = {d ≤ √N ∧ e ≤ √N}`.
  have hinter : A ∩ B = R.filter (fun p => p.1 ≤ r ∧ p.2 ≤ r) := by
    rw [hAdef, hBdef, ← Finset.filter_and]
  -- Leg `A`: `Σ_{d≤√N} a d · Σ_{e≤N/d} b e`.
  have hA : ∑ p ∈ A, a p.1 * b p.2
      = ∑ d ∈ Finset.Icc 1 r, a d * ∑ e ∈ Finset.Icc 1 (N / d), b e := by
    rw [hAdef, hRdef, Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_subset hsub (fun d hdN hdr => ?_)]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      simp only [hd.2, and_true]
      rw [← Finset.sum_filter, Icc_filter_mul_le d N hd.1, Finset.mul_sum]
    · rw [Finset.mem_Icc] at hdN
      rw [Finset.mem_Icc] at hdr
      apply Finset.sum_eq_zero
      intro e _
      apply if_neg
      rintro ⟨_, h2⟩; omega
  -- Leg `B`: `Σ_{e≤√N} b e · Σ_{d≤N/e} a d`.
  have hB : ∑ p ∈ B, a p.1 * b p.2
      = ∑ e ∈ Finset.Icc 1 r, b e * ∑ d ∈ Finset.Icc 1 (N / e), a d := by
    rw [hBdef, hRdef, Finset.filter_filter, Finset.sum_filter, Finset.sum_product_right]
    dsimp only
    rw [← Finset.sum_subset hsub (fun e heN her => ?_)]
    · apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mem_Icc] at he
      simp only [he.2, and_true]
      rw [← Finset.sum_filter]
      rw [show (Finset.Icc 1 N).filter (fun d => d * e ≤ N) = Finset.Icc 1 (N / e) from by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hd1, _⟩, hde⟩
          exact ⟨hd1, (Nat.le_div_iff_mul_le he.1).mpr hde⟩
        · rintro ⟨hd1, hde⟩
          refine ⟨⟨hd1, le_trans hde (Nat.div_le_self N e)⟩, ?_⟩
          exact (Nat.le_div_iff_mul_le he.1).mp hde]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    · rw [Finset.mem_Icc] at heN
      rw [Finset.mem_Icc] at her
      apply Finset.sum_eq_zero
      intro d _
      apply if_neg
      rintro ⟨_, h2⟩; omega
  -- Corner `A ∩ B`: `(Σ_{d≤√N} a d) · (Σ_{e≤√N} b e)`.
  have hC : ∑ p ∈ R.filter (fun p => p.1 ≤ r ∧ p.2 ≤ r), a p.1 * b p.2
      = (∑ d ∈ Finset.Icc 1 r, a d) * ∑ e ∈ Finset.Icc 1 r, b e := by
    have hCset : R.filter (fun p => p.1 ≤ r ∧ p.2 ≤ r)
        = Finset.Icc 1 r ×ˢ Finset.Icc 1 r := by
      rw [hRdef]
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨⟨hp1, _⟩, hp2, _⟩, _⟩, hr1, hr2⟩
        exact ⟨⟨hp1, hr1⟩, hp2, hr2⟩
      · rintro ⟨⟨hp1, hr1⟩, hp2, hr2⟩
        exact ⟨⟨⟨⟨hp1, le_trans hr1 hrN⟩, hp2, le_trans hr2 hrN⟩,
          le_trans (Nat.mul_le_mul hr1 hr2) hrr⟩, hr1, hr2⟩
    rw [hCset, Finset.sum_product]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  -- Inclusion–exclusion assembly.
  have hUI : (∑ p ∈ A ∪ B, a p.1 * b p.2) + ∑ p ∈ A ∩ B, a p.1 * b p.2
      = (∑ p ∈ A, a p.1 * b p.2) + ∑ p ∈ B, a p.1 * b p.2 := Finset.sum_union_inter
  rw [hunion, hinter, hA, hB, hC] at hUI
  rw [bridge]
  exact eq_sub_of_add_eq hUI

/-- **The DH-detector symmetric hyperbola (`b = 1` instance).** The exact shape T-BAL
R3 (`dhA_mass_upper`) consumes: `Σ_{n≤N} dhA χ n` split at `√N` into the `⌊N/d⌋`-leg,
the transposed partial-character leg, and the `√N` corner. -/
lemma dhA_hyperbola_symm {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, dhA χ n
      = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), chiRe χ d * ((N / d : ℕ) : ℝ))
        + (∑ e ∈ Finset.Icc 1 (Nat.sqrt N), ∑ d ∈ Finset.Icc 1 (N / e), chiRe χ d)
        - (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), chiRe χ d) * ((Nat.sqrt N : ℕ) : ℝ) := by
  have key := sum_divisors_eq_hyperbola_symm (chiRe χ) (fun _ => (1 : ℝ)) N
  simp only [one_mul, mul_one, sum_Icc_one] at key
  exact key

end Salt.SW
