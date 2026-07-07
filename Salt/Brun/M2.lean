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
Counts the number of residue classes modulo `d` where `n(n+2) ≡ 0`.
-/
noncomputable def rho (d : ℕ) : ℕ :=
  if h : d = 0 then 0
  else
    haveI : NeZero d := ⟨h⟩
    Finset.card (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0))

/-- Unfolds `rho d` for `d ≠ 0` into the filtered `Finset.card` expression. -/
lemma rho_pos {d : ℕ} (hd : d ≠ 0) [NeZero d] :
    rho d = Finset.card (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0)) := by
  simp only [rho, dif_neg hd]

/-- The map `n ↦ n * (n + 2)` is strictly monotone on ℕ. -/
lemma twinProd_strictMono : ∀ m n : ℕ, m < n → m * (m + 2) < n * (n + 2) := by
  intros m n hmn
  have : m + 2 > 0 := by omega
  have : n > m := hmn
  calc m * (m + 2)
      < n * (m + 2) := Nat.mul_lt_mul_of_pos_right hmn (by omega)
    _ < n * (n + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

/-- Solutions to `n(n+2) = 0` in `ZMod p` for prime `p` are exactly `{0, -2}`. -/
lemma sol_set (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun n : ZMod p => n * (n + 2) = 0)) = {0, -2} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · left; exact h1
    · right; linear_combination h2
  · rintro (h1 | h2)
    · simp [h1]
    · rw [h2]; ring

/-- N2.3 (part 1): `rho 2 = 1` — the only solution mod 2 is `n = 0`
(since `0 = -2` in `ZMod 2`). -/
theorem rho_two : rho 2 = 1 := by decide

/-- N2.3 (part 2): `rho p = 2` for odd prime `p` — the solutions `0` and `-2`
are distinct in `ZMod p` since `p ∤ 2`. -/
theorem rho_odd_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : rho p = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [rho_pos hp.ne_zero, sol_set p]
  have hne : (0 : ZMod p) ≠ -2 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := neg_eq_zero.mp h.symm
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
