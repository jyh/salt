/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun

/-!
# M2 — twin-prime instantiation (blueprint milestone)

Definitions and properties of the sieve function for twin primes.
-/

/-- N2.1: Density of solutions to `n(n+2) ≡ 0 (mod d)`.
Counts the number of residue classes modulo d where n(n+2) ≡ 0.
-/
noncomputable def rho : ℕ → ℕ := fun d =>
  match d with
  | 0 => 0
  | d + 1 =>
      Finset.card (Finset.univ.filter (fun n : ZMod (d + 1) => n * (n + 2) = 0))

/-- The map `n ↦ n * (n + 2)` is strictly monotone on ℕ. -/
lemma twinProd_strictMono : ∀ m n : ℕ, m < n → m * (m + 2) < n * (n + 2) := by
  intros m n hmn
  have : m + 2 > 0 := by omega
  have : n > m := hmn
  calc m * (m + 2)
      < n * (m + 2) := Nat.mul_lt_mul_of_pos_right hmn (by omega)
    _ < n * (n + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
