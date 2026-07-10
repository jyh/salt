/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.KSieve

/-!
# k-fold divisor count for the sieve index set (endgame prerequisite)

The Maynard sieve index set `kSieveIndex k R W` ranges over `k`-tuples of
positive naturals with product `< R`.  For the `S₁` trivial-error estimate we
need a *sharp* bound on its cardinality: the crude count `N^{2k/5}` exceeds `N`
and is useless.  This file proves

    `#(kSieveIndex k R W) ≤ R · (1 + log R)^k`,

whose constant is `1` — in particular explicit and **independent of `R`** (the
whole point).  The `(1 + log R)^k` factor comes from a `k`-fold harmonic sum.

The engine is `prodTuples_card_le`: the number of `k`-tuples of naturals in
`[1, N]` with product `≤ B ≤ N` is at most `B (1 + log B)^k`.  It is proved by
induction on `k`, splitting off the first coordinate `m` (whose value ranges in
`[1, B]`), reindexing the remaining `k`-tuple as a count with product bound
`B / m`, and summing the harmonic series `∑_{m ≤ B} 1/m ≤ 1 + log B`.
-/

namespace Salt.Maynard

open Finset

/-- `k`-tuples `d : Fin k → ℕ` with every coordinate in `[1, N]` and product
`≤ B`.  Used as the counting object in the divisor-count induction. -/
def prodTuples (k N B : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 N).filter (fun d => ∏ i, d i ≤ B)

/-- Membership in `prodTuples` unfolds to the per-coordinate range plus the
product bound. -/
theorem mem_prodTuples {k N B : ℕ} {d : Fin k → ℕ} :
    d ∈ prodTuples k N B ↔ (∀ i, 1 ≤ d i ∧ d i ≤ N) ∧ ∏ i, d i ≤ B := by
  rw [prodTuples, Finset.mem_filter, Fintype.mem_piFinset]
  simp_rw [Finset.mem_Icc]

/-- Splitting off the first coordinate: the tuples with first coordinate equal
to `m` (for `1 ≤ m ≤ N`) biject with `k`-tuples of product `≤ B / m`, via
`d ↦ Fin.tail d` with inverse `e ↦ Fin.cons m e`. -/
private theorem fiber_card (k N B m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ((prodTuples (k + 1) N B).filter (fun d => d 0 = m)).card
      = (prodTuples k N (B / m)).card := by
  apply Finset.card_nbij' (fun d => Fin.tail d) (fun e => Fin.cons m e)
  · -- MapsTo `Fin.tail` : fiber → prodTuples k N (B / m)
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter, mem_prodTuples] at hd
    obtain ⟨⟨hcoord, hprod⟩, hd0⟩ := hd
    rw [Finset.mem_coe, mem_prodTuples]
    refine ⟨fun i => hcoord i.succ, ?_⟩
    rw [Nat.le_div_iff_mul_le hm1]
    have hsplit : ∏ i, d i = m * ∏ i, Fin.tail d i := by
      rw [Fin.prod_univ_succ, hd0]; rfl
    calc (∏ i, Fin.tail d i) * m = m * ∏ i, Fin.tail d i := by ring
      _ = ∏ i, d i := hsplit.symm
      _ ≤ B := hprod
  · -- MapsTo `Fin.cons m` : prodTuples k N (B / m) → fiber
    intro e he
    rw [Finset.mem_coe, mem_prodTuples] at he
    obtain ⟨hcoord, hprod⟩ := he
    rw [Finset.mem_coe, Finset.mem_filter, mem_prodTuples]
    dsimp only
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [Fin.cons_zero]; exact ⟨hm1, hmN⟩
      · rw [Fin.cons_succ]; exact hcoord j
    · rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      calc m * ∏ i, e i ≤ m * (B / m) := Nat.mul_le_mul (le_refl m) hprod
        _ ≤ B := Nat.mul_div_le B m
    · rw [Fin.cons_zero]
  · -- left inverse: cons m (tail d) = d on the fiber
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    dsimp only
    rw [← hd.2]
    exact Fin.cons_self_tail d
  · -- right inverse: tail (cons m e) = e
    intro e _
    dsimp only
    rw [Fin.tail_cons]

/-- **Main divisor-count bound.**  For `B ≤ N`, the number of `k`-tuples of
naturals in `[1, N]` with product `≤ B` is at most `B (1 + log B)^k`.  The
bound depends only on `B` and `k`, never on the ambient range `N`. -/
theorem prodTuples_card_le (k : ℕ) : ∀ N B : ℕ, B ≤ N →
    ((prodTuples k N B).card : ℝ) ≤ (B : ℝ) * (1 + Real.log B) ^ k := by
  induction k with
  | zero =>
    intro N B _
    rw [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos B with rfl | hBpos
    · -- product of the empty tuple is 1, never ≤ 0, so the set is empty
      have hempty : prodTuples 0 N 0 = ∅ := by
        rw [prodTuples, Finset.filter_eq_empty_iff]
        intro d _
        rw [Fin.prod_univ_zero]
        exact Nat.not_succ_le_zero 0
      rw [hempty]
      simp
    · -- at most the single empty tuple
      have hcard : (prodTuples 0 N B).card ≤ 1 := by
        refine le_trans (Finset.card_filter_le _ _) ?_
        rw [Fintype.card_piFinset]
        simp
      calc ((prodTuples 0 N B).card : ℝ) ≤ 1 := by exact_mod_cast hcard
        _ ≤ (B : ℝ) := by exact_mod_cast hBpos
  | succ k ih =>
    intro N B hB
    -- Step 1: split off the first coordinate, whose value ranges in [1, B].
    have hmaps : Set.MapsTo (fun d : Fin (k + 1) → ℕ => d 0)
        ↑(prodTuples (k + 1) N B) ↑(Finset.Icc 1 B) := by
      intro d hd
      rw [Finset.mem_coe, mem_prodTuples] at hd
      rw [Finset.mem_coe, Finset.mem_Icc]
      obtain ⟨hcoord, hprod⟩ := hd
      refine ⟨(hcoord 0).1, ?_⟩
      calc d 0 ≤ ∏ i, d i := Finset.single_le_prod' (fun i _ => (hcoord i).1) (Finset.mem_univ 0)
        _ ≤ B := hprod
    have hfib : (prodTuples (k + 1) N B).card
        = ∑ m ∈ Finset.Icc 1 B, (prodTuples k N (B / m)).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      exact fiber_card k N B m hm.1 (le_trans hm.2 hB)
    -- Step 2: bound the sum term-by-term and collapse the harmonic factor.
    rw [hfib, Nat.cast_sum]
    have hlogB : (0 : ℝ) ≤ 1 + Real.log B := by
      have := Real.log_natCast_nonneg B; linarith
    calc ∑ m ∈ Finset.Icc 1 B, ((prodTuples k N (B / m)).card : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 B, (B : ℝ) / m * (1 + Real.log B) ^ k := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          rw [Finset.mem_Icc] at hm
          have hlogdiv : (0 : ℝ) ≤ Real.log ((B / m : ℕ) : ℝ) := Real.log_natCast_nonneg _
          have hle : Real.log ((B / m : ℕ) : ℝ) ≤ Real.log (B : ℝ) := by
            rcases Nat.eq_zero_or_pos (B / m) with h0 | hpos
            · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
              exact Real.log_natCast_nonneg B
            · exact Real.log_le_log (by exact_mod_cast hpos)
                (by exact_mod_cast Nat.div_le_self B m)
          calc ((prodTuples k N (B / m)).card : ℝ)
              ≤ ((B / m : ℕ) : ℝ) * (1 + Real.log ((B / m : ℕ) : ℝ)) ^ k :=
                ih N (B / m) (le_trans (Nat.div_le_self B m) hB)
            _ ≤ (B : ℝ) / m * (1 + Real.log B) ^ k := by
                apply mul_le_mul Nat.cast_div_le
                · exact pow_le_pow_left₀ (by linarith) (by linarith) k
                · exact pow_nonneg (by linarith) k
                · positivity
      _ = (B : ℝ) * (1 + Real.log B) ^ k * ∑ m ∈ Finset.Icc 1 B, (m : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => by ring)
      _ ≤ (B : ℝ) * (1 + Real.log B) ^ k * (1 + Real.log B) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hharm : ∑ m ∈ Finset.Icc 1 B, (m : ℝ)⁻¹ = ((harmonic B : ℚ) : ℝ) := by
            rw [harmonic_eq_sum_Icc]; push_cast; rfl
          rw [hharm]
          exact harmonic_le_one_add_log B
      _ = (B : ℝ) * (1 + Real.log B) ^ (k + 1) := by ring

/-- **k-fold divisor count.**  The Maynard sieve index set has cardinality at
most `R (1 + log R)^k`.  The constant is `1`, explicit and independent of `R`
(only the `k`-dependence lives in the exponent).  Feeds the `S₁` trivial-error
estimate (`N4.3`), where the crude bounds are insufficient. -/
theorem kSieveIndex_card_le (k R W : ℕ) (hR : 2 ≤ R) :
    ((kSieveIndex k R W).card : ℝ) ≤ (R : ℝ) * (1 + Real.log R) ^ k := by
  -- `kSieveIndex` embeds into the counting object with `N = B = R - 1`.
  have hsub : kSieveIndex k R W ⊆ prodTuples k (R - 1) (R - 1) := by
    intro r hr
    rw [mem_kSieveIndex_iff] at hr
    rw [mem_prodTuples]
    obtain ⟨hsf, -, -, hprod⟩ := hr
    have hle : ∀ i, r i ≤ ∏ j, r j := fun i =>
      Finset.single_le_prod' (fun j _ => Squarefree.pos (hsf j)) (Finset.mem_univ i)
    refine ⟨fun i => ⟨Squarefree.pos (hsf i), ?_⟩, ?_⟩
    · have := hle i; omega
    · omega
  have hcard : ((kSieveIndex k R W).card : ℝ) ≤ ((prodTuples k (R - 1) (R - 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine hcard.trans ((prodTuples_card_le k (R - 1) (R - 1) le_rfl).trans ?_)
  -- `(R-1)(1 + log (R-1))^k ≤ R (1 + log R)^k`.
  have h1R : (1 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := by
    have : 1 ≤ R - 1 := by omega
    exact_mod_cast this
  have hleR : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.sub_le R 1
  have hlognn : (0 : ℝ) ≤ Real.log ((R - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  apply mul_le_mul hleR
  · exact pow_le_pow_left₀ (by linarith)
      (by have := Real.log_le_log (by linarith : (0:ℝ) < ((R - 1 : ℕ) : ℝ)) hleR; linarith) k
  · exact pow_nonneg (by linarith) k
  · positivity

end Salt.Maynard
