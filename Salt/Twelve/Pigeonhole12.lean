/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Endgame
import Salt.Maynard.S2Eh
import Salt.Twelve.Params

/-!
# Rung 4a — W5-5: the free-`W'`, diam-12 pigeonhole spine

Design: `docs/blueprints/explicit12-design.md`, card **W5-5**.  This file ports
the four end-of-proof spine lemmas of `Salt/Maynard/Endgame.lean`
(`sum_S2m_eq:254`, `exists_window_two_primes:268`, `bounded_gap_of_S2_gt_S1:292`,
`bounded_gaps_reduces:349`) to the free modulus `W'` and the concrete tuple
width `k = 5`, sharpening the pigeonhole gap bound from `Icc(-(D₀ k), D₀ k)` to
`Icc(-12, 12)` via `Salt.Twelve.hSeq_diam_le_twelve`.

The reach to `W k` in the original spine is *only* through `S2m` (which is
`S2mW … (W k)` by definition); `S1`, `weightSq`, and `windowSet` are already
`W`-generic, and nothing here needs `Squarefree W'`.  So the port is the pure
substitution `S2m → S2mW`, `W k → W'`, `k → 5`, plus the single interval bullet
swap `hSeq_le_D₀ k → hSeq_diam_le_twelve`.
-/

namespace Salt.Twelve

open Salt.Maynard

/-- **W5-5 (1) — the counting identity, free `W'`.** Mirror of `sum_S2m_eq`:
`Σ_m S₂ᵂ⁽ᵐ⁾ = Σ_{n∈window} P(n)·w(n)`, where `P(n) = #{m : (n+hₘ) prime}` and
`w = weightSq ≥ 0`.  A pure sum swap — identical to the `W k` proof since the
body of `S2mW` is structurally `S2m` with `W k` replaced by `W'`. -/
theorem sum_S2mW_eq (K₀ N R ν₀ W' : ℕ) (y : (Fin 5 → ℕ) → ℝ) :
    ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y
      = ∑ n ∈ windowSet K₀ N W' ν₀,
          ((Finset.univ.filter (fun m : Fin 5 => (n + hSeq 5 m).Prime)).card : ℝ)
            * weightSq 5 R W' y n := by
  simp only [S2mW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_boole]

/-- **W5-5 (2) — pigeonhole, free `W'`.** Mirror of `exists_window_two_primes`:
if `Σ_m S₂ᵂ⁽ᵐ⁾ > S₁ = Σ_n w(n)`, some window point `n` has at least two prime
shifts `n+hₘ`.  Needs only `weightSq ≥ 0` (`sq_nonneg`). -/
theorem exists_window_two_primesW (K₀ N R ν₀ W' : ℕ) (y : (Fin 5 → ℕ) → ℝ)
    (hgt : S1 5 K₀ N R W' ν₀ y < ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y) :
    ∃ n ∈ windowSet K₀ N W' ν₀,
      2 ≤ (Finset.univ.filter (fun m : Fin 5 => (n + hSeq 5 m).Prime)).card := by
  by_contra hcon
  rw [sum_S2mW_eq, S1] at hgt
  have hle : ∑ n ∈ windowSet K₀ N W' ν₀,
        ((Finset.univ.filter (fun m : Fin 5 => (n + hSeq 5 m).Prime)).card : ℝ)
          * weightSq 5 R W' y n
      ≤ ∑ n ∈ windowSet K₀ N W' ν₀, weightSq 5 R W' y n := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hcard : (Finset.univ.filter (fun m : Fin 5 => (n + hSeq 5 m).Prime)).card ≤ 1 := by
      by_contra hc; exact hcon ⟨n, hn, by omega⟩
    calc ((Finset.univ.filter (fun m : Fin 5 => (n + hSeq 5 m).Prime)).card : ℝ)
            * weightSq 5 R W' y n
        ≤ 1 * weightSq 5 R W' y n :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (by rw [weightSq]; exact sq_nonneg _)
      _ = weightSq 5 R W' y n := one_mul _
  linarith [hgt, hle]

/-- **W5-5 (3) — bounded gap from the sieve inequality, diam-12.** Mirror of
`bounded_gap_of_S2_gt_S1`, but the output interval is `Icc(-12, 12)` instead of
`Icc(-(D₀ k), D₀ k)`: the interval bullet (`Endgame.lean:303–306`) is discharged
by `hSeq_diam_le_twelve j i : (hSeq 5 j : ℤ) − (hSeq 5 i : ℤ) ∈ Icc(-12, 12)`
rather than `hSeq_le_D₀`.  The window point, `hSeq_injective` for `p ≠ q`, and
`N < p, q` are unchanged. -/
theorem bounded_gap_of_S2_gt_S1_twelve (K₀ N R ν₀ W' : ℕ) (y : (Fin 5 → ℕ) → ℝ)
    (hgt : S1 5 K₀ N R W' ν₀ y < ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  obtain ⟨n, hn, hcard⟩ := exists_window_two_primesW K₀ N R ν₀ W' y hgt
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hcard)
  rw [Finset.mem_filter] at hi hj
  have hnN : N < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  refine ⟨n + hSeq 5 i, n + hSeq 5 j, by omega, by omega, ?_, hi.2, hj.2, ?_⟩
  · have : hSeq 5 i ≠ hSeq 5 j := fun h => hij (hSeq_injective 5 h)
    omega
  · -- `(q:ℤ) − (p:ℤ) = (n+hSeq 5 j) − (n+hSeq 5 i) = hSeq 5 j − hSeq 5 i`, bounded
    -- by `hSeq_diam_le_twelve j i` (`j i` order matches the subtraction direction).
    have hdiam := hSeq_diam_le_twelve j i
    simp only [Set.mem_Icc] at hdiam ⊢
    omega

/-- **W5-5 (4) — reduction to the master inequality, diam-12.** Mirror of
`bounded_gaps_reduces`, but the output gap interval is directly `Icc(-12, 12)`
(from `bounded_gap_of_S2_gt_S1_twelve`), so the conclusion carries no `∃ C`
witness.  This is the FROZEN card statement — matched verbatim. -/
theorem bounded_gaps_reduces_twelve (W' : ℕ)
    (hwin : ∀ N : ℕ, ∃ (N' R ν₀ : ℕ) (y : (Fin 5 → ℕ) → ℝ), N ≤ N' ∧
      S1 5 64 N' R W' ν₀ y < ∑ m : Fin 5, S2mW 5 64 N' R ν₀ W' m y) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  intro N
  obtain ⟨N', R, ν₀, y, hNN', hwinN⟩ := hwin N
  obtain ⟨p, q, hp, hq, hpq, hpp, hqp, hgap⟩ :=
    bounded_gap_of_S2_gt_S1_twelve 64 N' R ν₀ W' y hwinN
  exact ⟨p, q, by omega, by omega, hpq, hpp, hqp, hgap⟩

end Salt.Twelve
