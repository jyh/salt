/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Salt

The objective of this project is a formal, machine-checked proof of the
Twin Prime Conjecture — approached by formalizing the known frontier
(sieve theory, Bombieri–Vinogradov, Maynard–Tao) and researching beyond it.

This file states the target and proves a smoke-test lemma validating the
toolchain end to end.
-/

/-- **The Twin Prime Conjecture**: there are infinitely many primes `p` such
that `p + 2` is also prime. This is the statement this project aims to prove.
It is stated here as a definition (not an axiom, not a theorem): the project
succeeds when a `theorem` of this type exists with no `sorry` and no axioms
beyond mathlib's standard three. -/
def TwinPrimeConjecture : Prop :=
  ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ p.Prime ∧ (p + 2).Prime

/-- The first twin pair, `(3, 5)`: a smoke test that mathlib's prime
machinery is wired up and kernel-checked. -/
theorem twin_pair_exists : ∃ p : ℕ, p.Prime ∧ (p + 2).Prime :=
  ⟨3, by norm_num, by norm_num⟩
