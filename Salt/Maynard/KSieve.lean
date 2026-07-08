/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Tuple

/-!
# The k-dimensional sieve index set 𝒟 (blueprint N2.1)

The Maynard sieve ranges over `k`-tuples `r : Fin k → ℕ` of pairwise-coprime
squarefrees, each coprime to the modulus `W`, with `∏ᵢ rᵢ < R`. This file
packages that finite index set `kSieveIndex k R W`, its membership
characterization, and the two per-coordinate facts (`r i < R`, `0 < r i`)
used pervasively downstream.
-/

namespace Salt.Maynard

open Finset

/-- The Maynard sieve index set: `k`-tuples `r : Fin k → ℕ` of pairwise-
coprime squarefrees, each coprime to `W`, with `∏ᵢ rᵢ < R`. -/
def kSieveIndex (k R W : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => Finset.range R)).filter
    (fun r => (∀ i, Squarefree (r i)) ∧
              (∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) ∧
              (∀ i, Nat.Coprime (r i) W) ∧
              (∏ i, r i < R))

/-- A squarefree natural is positive. -/
theorem Squarefree.pos {n : ℕ} (hn : Squarefree n) : 0 < n :=
  Nat.pos_of_ne_zero hn.ne_zero

/-- Membership in `kSieveIndex` is exactly the conjunction of the four
sieve conditions. The `r i < R` clause defining `piFinset (range R)` is
recovered from the predicate: each `r i ≥ 1` (squarefree ⇒ nonzero), so
`r i ≤ ∏ⱼ rⱼ < R`. -/
theorem mem_kSieveIndex_iff {k R W : ℕ} (r : Fin k → ℕ) :
    r ∈ kSieveIndex k R W ↔
      (∀ i, Squarefree (r i)) ∧ (∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) ∧
      (∀ i, Nat.Coprime (r i) W) ∧ (∏ i, r i < R) := by
  unfold kSieveIndex
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, hpred⟩
    exact hpred
  · intro hpred
    refine ⟨?_, hpred⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    -- `r i ≤ ∏ⱼ rⱼ < R`, using `r j ≥ 1` from squarefreeness.
    have hprod : r i ≤ ∏ j, r j :=
      Finset.single_le_prod' (fun j _ => Squarefree.pos (hpred.1 j)) (Finset.mem_univ i)
    exact lt_of_le_of_lt hprod hpred.2.2.2

/-- Every coordinate of a sieve tuple is `< R`. -/
theorem kSieveIndex_coord_lt {k R W : ℕ} {r} (hr : r ∈ kSieveIndex k R W)
    (i : Fin k) : r i < R := by
  rw [mem_kSieveIndex_iff] at hr
  have hprod : r i ≤ ∏ j, r j :=
    Finset.single_le_prod' (fun j _ => Squarefree.pos (hr.1 j)) (Finset.mem_univ i)
  exact lt_of_le_of_lt hprod hr.2.2.2

/-- Every coordinate of a sieve tuple is positive (squarefree ⇒ nonzero). -/
theorem kSieveIndex_coord_pos {k R W : ℕ} {r} (hr : r ∈ kSieveIndex k R W)
    (i : Fin k) : 0 < r i := by
  rw [mem_kSieveIndex_iff] at hr
  exact Squarefree.pos (hr.1 i)

end Salt.Maynard
