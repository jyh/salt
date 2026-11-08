/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvMoment

/-!
# Two coordinates of a `decBox` point sharing a prime

The Maynard split bounds (`Twelve.MvI` · `MvJ` · `MvSplit` ×2 and their general-`k` ports
`MaynardK.ISplit` · `MvIGen` · `JMainSplit` · `MvJGen`) each took two steps inline, for a point
`r` of the decoupled box `decBox n R W'` (squarefree coordinates, each `< R` and coprime to `W'`):

* a point that is not pairwise coprime has two coordinates `i ≠ j` sharing a prime `p`, and that
  prime does not divide `W'` and is `< R`;
* the sum of a product weight over the points with `p ∣ r i` and `p ∣ r j` is at most the product,
  over the coordinates, of the one-coordinate sums, where coordinates `i` and `j` are restricted to
  multiples of `p`.

## Main results
* `exists_prime_pair_of_not_pairwise_coprime` — the shared prime, with `¬ p ∣ W'` and `p < R`.
* `decBox_filter_pair_le_prod` — the sum over the `p`-pair slice of the box is at most the product
  of the coordinate sums.
-/

open Finset

namespace Salt.Twelve

/-- **A shared prime.** If the coordinates of `r` (each `< R`, squarefree and coprime to `W'`) are
not pairwise coprime, then two of them, `i ≠ j`, share a prime `p` with `¬ p ∣ W'` and `p < R`.
`p ∤ W'` because `p ∣ r i` and `gcd (r i) W' = 1`; `p < R` because `p ≤ r i < R`. -/
theorem exists_prime_pair_of_not_pairwise_coprime {n R W' : ℕ} {r : Fin n → ℕ}
    (hlt : ∀ i, r i < R) (hsqf : ∀ i, Squarefree (r i)) (hcop : ∀ i, (r i).Coprime W')
    (hpair_neg : ¬ ∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j)) :
    ∃ i j : Fin n, ∃ p : ℕ, i ≠ j ∧ p.Prime ∧ p ∣ r i ∧ p ∣ r j ∧ ¬ p ∣ W' ∧ p < R := by
  simp only [not_forall] at hpair_neg
  obtain ⟨i, j, hij, hncop⟩ := hpair_neg
  have hg1 : Nat.gcd (r i) (r j) ≠ 1 := hncop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
  have hpi : p ∣ r i := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpj : p ∣ r j := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpW' : ¬ p ∣ W' := by
    intro hpW
    have h1 : p ∣ (1 : ℕ) := (hcop i) ▸ Nat.dvd_gcd hpi hpW
    exact absurd (Nat.dvd_one.mp h1) hp.one_lt.ne'
  have hri1 : 1 ≤ r i := Nat.pos_of_ne_zero (hsqf i).ne_zero
  have hpR : p < R := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpi) (hlt i)
  exact ⟨i, j, p, hij, hp, hpi, hpj, hpW', hpR⟩

/-- **The `p`-pair slice of the box, by coordinates.** For a weight `w ≥ 0`, the sum of
`∏ k, w (r k)` over the points of `decBox n R W'` with `p ∣ r i` and `p ∣ r j` is at most the
product over `k` of `∑ w s`, `s` ranging over the squarefree `s < R` coprime to `W'` and divisible
by `p` when `k` is `i` or `j`. The slice embeds in the product box; the extra terms are `≥ 0`. -/
theorem decBox_filter_pair_le_prod {n R W' p : ℕ} (i j : Fin n) (w : ℕ → ℝ)
    (hw : ∀ s, 0 ≤ w s) :
    ∑ r ∈ (decBox n R W').filter (fun r => p ∣ r i ∧ p ∣ r j), ∏ k, w (r k)
      ≤ ∏ k, ∑ s ∈ (Finset.range R).filter
          (fun s => Squarefree s ∧ s.Coprime W' ∧ (if k = i ∨ k = j then p else 1) ∣ s), w s := by
  classical
  set g : Fin n → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  set coordSet : Fin n → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  change _ ≤ ∏ k, ∑ s ∈ coordSet k, w s
  rw [Finset.prod_univ_sum coordSet (fun _ s => w s)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrdec, hpi, hpj⟩ := hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec
    obtain ⟨hlt, hsqf, hcop, _⟩ := hrdec
    rw [Fintype.mem_piFinset]
    intro k
    rw [hcoord, Finset.mem_filter, Finset.mem_range]
    refine ⟨hlt k, hsqf k, hcop k, ?_⟩
    simp only [hg]
    split
    · rename_i hcase
      rcases hcase with hki | hkj
      · rw [hki]; exact hpi
      · rw [hkj]; exact hpj
    · exact one_dvd _
  · intro r _ _
    exact Finset.prod_nonneg (fun k _ => hw _)

end Salt.Twelve
