/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Endgame
import Salt.Maynard.S2Eh

/-!
# C1 · B4.0b — the free-`W'` pigeonhole spine at general `k` and diameter

`Salt.Twelve.Pigeonhole12` (k = 5, diameter 12) with `5 → k` and the diameter bullet
`hSeq_diam_le_twelve` replaced by a hypothesis `hdiam` at any diameter `Dm`.
-/

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard

/-- **(1) The counting identity, free `W'`, general `k`.** `Σ_m S₂ᵂ⁽ᵐ⁾ = Σ_{n∈window} P(n)·w(n)`,
`P(n) = #{m : (n+hₘ) prime}`, `w = weightSq ≥ 0` (a sum swap). -/
theorem sum_S2mW_eq_k (k K₀ N R ν₀ W' : ℕ) (y : (Fin k → ℕ) → ℝ) :
    ∑ m : Fin k, S2mW k K₀ N R ν₀ W' m y
      = ∑ n ∈ windowSet K₀ N W' ν₀,
          ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
            * weightSq k R W' y n := by
  simp only [S2mW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_boole]

/-- **(2) Pigeonhole, free `W'`, general `k`.** If `Σ_m S₂ᵂ⁽ᵐ⁾ > S₁`, some window point `n` has at
least two prime shifts `n + hₘ`. -/
theorem exists_window_two_primesW_k (k K₀ N R ν₀ W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hgt : S1 k K₀ N R W' ν₀ y < ∑ m : Fin k, S2mW k K₀ N R ν₀ W' m y) :
    ∃ n ∈ windowSet K₀ N W' ν₀,
      2 ≤ (Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card := by
  by_contra hcon
  rw [sum_S2mW_eq_k, S1] at hgt
  have hle : ∑ n ∈ windowSet K₀ N W' ν₀,
        ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
          * weightSq k R W' y n
      ≤ ∑ n ∈ windowSet K₀ N W' ν₀, weightSq k R W' y n := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hcard : (Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card ≤ 1 := by
      by_contra hc; exact hcon ⟨n, hn, by omega⟩
    calc ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
            * weightSq k R W' y n
        ≤ 1 * weightSq k R W' y n :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (by rw [weightSq]; exact sq_nonneg _)
      _ = weightSq k R W' y n := one_mul _
  linarith [hgt, hle]

/-- **(3) Bounded gap from the sieve inequality, at diameter `Dm`.** Two prime shifts of one window
point differ by a tuple difference, bounded by the hypothesis `hdiam`. -/
theorem bounded_gap_of_S2_gt_S1_diam (k K₀ N R ν₀ W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (Dm : ℤ) (hdiam : ∀ i j : Fin k, (hSeq k j : ℤ) - (hSeq k i : ℤ) ∈ Set.Icc (-Dm) Dm)
    (hgt : S1 k K₀ N R W' ν₀ y < ∑ m : Fin k, S2mW k K₀ N R ν₀ W' m y) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-Dm) Dm := by
  obtain ⟨n, hn, hcard⟩ := exists_window_two_primesW_k k K₀ N R ν₀ W' y hgt
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hcard)
  rw [Finset.mem_filter] at hi hj
  have hnN : N < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  refine ⟨n + hSeq k i, n + hSeq k j, by omega, by omega, ?_, hi.2, hj.2, ?_⟩
  · have : hSeq k i ≠ hSeq k j := fun h => hij (hSeq_injective k h)
    omega
  · -- `(q:ℤ) − (p:ℤ) = (n+hSeq k j) − (n+hSeq k i) = hSeq k j − hSeq k i` (bounded by `hdiam i j`)
    have hd := hdiam i j
    simp only [Set.mem_Icc] at hd ⊢
    omega

/-- **(4) Reduction to the master inequality, at diameter `Dm`.** -/
theorem bounded_gaps_reduces_diam (k W' : ℕ) (Dm : ℤ)
    (hdiam : ∀ i j : Fin k, (hSeq k j : ℤ) - (hSeq k i : ℤ) ∈ Set.Icc (-Dm) Dm)
    (hwin : ∀ N : ℕ, ∃ (N' R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ), N ≤ N' ∧
      S1 k 64 N' R W' ν₀ y < ∑ m : Fin k, S2mW k 64 N' R ν₀ W' m y) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-Dm) Dm := by
  intro N
  obtain ⟨N', R, ν₀, y, hNN', hwinN⟩ := hwin N
  obtain ⟨p, q, hp, hq, hpq, hpp, hqp, hgap⟩ :=
    bounded_gap_of_S2_gt_S1_diam k 64 N' R ν₀ W' y Dm hdiam hwinN
  exact ⟨p, q, by omega, by omega, hpq, hpp, hqp, hgap⟩

end Salt.MaynardK
