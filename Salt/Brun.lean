/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Brun's theorem: formal targets (blueprint M0)

Statements for the Brun track (`docs/blueprints/brun.md`). Per repo policy
`main` carries no `sorry`, so targets are stated as `Prop`s; they become
theorems as the blueprint's milestones land from the `brun` branch.
-/

open Filter Asymptotics

/-- Number of twin-prime leaders up to `n`: primes `p ≤ n` with `p + 2` prime. -/
def twinPrimeCounting (n : ℕ) : ℕ :=
  Nat.count (fun p => p.Prime ∧ (p + 2).Prime) (n + 1)

/-- Intermediate target (blueprint M5): the Selberg-sieve counting bound
`twinPrimeCounting N = O(N / (log N)²)`. -/
def TwinCountingBigO : Prop :=
  (fun x : ℝ => (twinPrimeCounting ⌊x⌋₊ : ℝ)) =O[atTop] fun x => x / Real.log x ^ 2

/-- **Brun's theorem** (blueprint M6, the track's target): the sum of
reciprocals of twin primes converges — in contrast to
`not_summable_one_div_on_primes`. -/
def BrunStatement : Prop :=
  Summable (Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} fun n => (1 : ℝ) / n)

theorem twinPrimeCounting_monotone : Monotone twinPrimeCounting :=
  fun _ _ h => Nat.count_monotone _ (Nat.succ_le_succ h)
