/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Maynard's theorem (bounded gaps, conditional): formal targets (blueprint M0)

Statements for the Maynard track (`docs/blueprints/maynard.md`). Per repo
policy `main` carries no `sorry`; this file states the targets as `def`s
(`Prop`s) and the elementary counting facts (`N0.1`, `N0.2`) as theorems.
The load-bearing hypothesis `EH` (`N0.3`, a Bombieri–Vinogradov-shaped
level-of-distribution statement, unformalized in any current Lean
library) and the conditional target `BoundedGapsFromEH` are stated here;
they become unconditional theorems as later blueprint milestones land.
-/

open Filter Asymptotics

/-- **N0.1**: `π(x;q,a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
def primesCount (x q a : ℕ) : ℕ :=
  Nat.count (fun p => p.Prime ∧ p % q = a) (x + 1)

theorem primesCount_monotone (q a : ℕ) : Monotone (fun x => primesCount x q a) :=
  fun _ _ h => Nat.count_monotone _ (Nat.succ_le_succ h)

/-- `primesCount x 1 0` specializes to the ordinary prime counting function
`Nat.count Nat.Prime (x+1)`, since every natural is `≡ 0 (mod 1)`. -/
@[simp]
theorem primesCount_one_zero (x : ℕ) :
    primesCount x 1 0 = Nat.count Nat.Prime (x + 1) := by
  unfold primesCount
  congr 1
  funext p
  simp [Nat.mod_one]

/-- **N0.2**: the trivial upper bound — at most one prime per residue class
per block of length `q`, so `π(x;q,a) ≤ x/q + 1`. -/
theorem primesCount_le (x q a : ℕ) (_hq : q ≠ 0) :
    primesCount x q a ≤ x / q + 1 := by
  unfold primesCount
  rw [Nat.count_eq_card_filter_range]
  -- Restrict to the (larger) set of all `n < x+1` with `n % q = a`.
  have hsub :
      (Finset.range (x + 1)).filter (fun p => p.Prime ∧ p % q = a)
        ⊆ (Finset.range (x + 1)).filter (fun n => n % q = a) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.2⟩
  refine (Finset.card_le_card hsub).trans ?_
  -- `n ↦ n / q` is injective on `{n < x+1 : n % q = a}` (fixed residue
  -- determines `n` from its quotient) and lands in `range (x/q + 1)`.
  have hcard : ((Finset.range (x + 1)).filter (fun n => n % q = a)).card
      ≤ (Finset.range (x / q + 1)).card := by
    refine Finset.card_le_card_of_injOn (· / q) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      have hnx : n ≤ x := by omega
      have := Nat.div_le_div_right (c := q) hnx
      omega
    · intro n1 hn1 n2 hn2 heq
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn1 hn2
      have e1 : n1 = q * (n1 / q) + n1 % q := (Nat.div_add_mod n1 q).symm
      have e2 : n2 = q * (n2 / q) + n2 % q := (Nat.div_add_mod n2 q).symm
      have heq' : n1 / q = n2 / q := heq
      rw [heq'] at e1
      rw [hn1.2] at e1
      rw [hn2.2] at e2
      omega
  rwa [Finset.card_range] at hcard

/-- There is always some residue `a < q` coprime to `q`, for `q ≠ 0`
(`a = 0` if `q = 1`, `a = 1` otherwise) — the nonemptiness witness needed
for `maxDiscrepancy`'s `Finset.sup'`. -/
theorem exists_coprime_lt {q : ℕ} (hq : q ≠ 0) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty := by
  by_cases hq1 : q = 1
  · exact ⟨0, by subst hq1; decide⟩
  · have hq2 : 1 < q := by omega
    exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq2, Nat.coprime_one_left q⟩⟩

/-- Auxiliary for **N0.3**: the maximal discrepancy `|π(x;q,a) − π(x)/φ(q)|`
over reduced residues `a mod q`, encoded as a `Finset.sup'` over the
`Finset` of residues `a < q` coprime to `q` (nonempty since `q ≥ 1` always
has such a residue). Junk value `0` when `q = 0`; never reached since `EH`
below only ever sums over `q ≥ 1`. -/
noncomputable def maxDiscrepancy (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0
  else ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup'
    (exists_coprime_lt hq)
    (fun a => |(primesCount x q a : ℝ) - (primesCount x 1 0 : ℝ) / (Nat.totient q : ℝ)|)

theorem maxDiscrepancy_nonneg (x q : ℕ) : 0 ≤ maxDiscrepancy x q := by
  unfold maxDiscrepancy
  split
  · exact le_refl 0
  · rename_i hq
    obtain ⟨a0, ha0⟩ := exists_coprime_lt hq
    refine le_trans (abs_nonneg
      ((primesCount x q a0 : ℝ) - (primesCount x 1 0 : ℝ) / (Nat.totient q : ℝ))) ?_
    exact Finset.le_sup'
      (fun a => |(primesCount x q a : ℝ) - (primesCount x 1 0 : ℝ) / (Nat.totient q : ℝ)|) ha0

open Filter Asymptotics in
/-- **N0.3**: **Level of distribution `θ`**: for every `A > 0`, the maximal
discrepancy between `π(x;q,a)` and its expected value `π(x)/φ(q)`, summed
over moduli `q ≤ x^θ` and maximized over reduced residues `a`, is
`O(x / (log x)^A)`. A Bombieri–Vinogradov-shaped hypothesis, taken here as
a HYPOTHESIS (unformalized in any current Lean library). -/
def EH (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, maxDiscrepancy x q)
      ≤ C * (x : ℝ) / (Real.log x) ^ A

/-- `EH` is antitone in `θ` (a hypothesis at level `θ` implies one at any
smaller level — fewer/smaller moduli to sum over). -/
theorem EH_antitone {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) (_hθ₁ : 0 ≤ θ₁) (hEH : EH θ₂) : EH θ₁ := by
  intro A hA
  obtain ⟨C, hC⟩ := hEH A hA
  refine ⟨C, fun x hx => ?_⟩
  have hxr : (1 : ℝ) ≤ (x : ℝ) := by
    have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hsub : Finset.Icc 1 ⌊(x : ℝ) ^ θ₁⌋₊ ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ₂⌋₊ := by
    apply Finset.Icc_subset_Icc_right
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hxr h)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => maxDiscrepancy_nonneg x q)).trans (hC x hx)

/-- Target (M7): Maynard's theorem, conditional on `EH (1/2)`. -/
def BoundedGapsFromEH : Prop :=
  EH (1 / 2) → ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧
    p.Prime ∧ q.Prime ∧ (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ)
