/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun
import Salt.Brun.CongruenceCounting

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

/-- N2.1 roots, represented as naturals in `[0, d)` via `ZMod.val`. -/
noncomputable def Rnat (d : ℕ) [NeZero d] : Finset ℕ :=
  (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0)).image ZMod.val

lemma Rnat_card (d : ℕ) [NeZero d] : (Rnat d).card = rho d := by
  rw [rho_pos (NeZero.ne d)]
  exact Finset.card_image_of_injective _ (ZMod.val_injective d)

lemma Rnat_subset_range (d : ℕ) [NeZero d] : Rnat d ⊆ Finset.range d := by
  intro r hr
  simp only [Rnat, Finset.mem_image] at hr
  obtain ⟨n, _, rfl⟩ := hr
  simp [ZMod.val_lt]

lemma dvd_iff_mem_Rnat (d : ℕ) [NeZero d] (n : ℕ) : d ∣ n * (n + 2) ↔ n % d ∈ Rnat d := by
  simp only [Rnat, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hdvd
    refine ⟨(n : ZMod d), ?_, ?_⟩
    · have : ((n * (n + 2) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at this
      convert this using 2
    · rw [ZMod.val_natCast]
  · rintro ⟨m, hm, hmn⟩
    have heq : (n : ZMod d) = m := by
      rw [← ZMod.natCast_mod n d, ← hmn, ZMod.natCast_val, ZMod.cast_id]
    have : ((n * (n + 2) : ℕ) : ZMod d) = 0 := by push_cast; rw [heq]; exact hm
    rwa [ZMod.natCast_eq_zero_iff] at this

/-- N2.4: the count of `n ∈ Icc 1 N` with `d ∣ n(n+2)` differs from the
expected `N * rho d / d` by at most `rho d`. -/
theorem progression_count_bound (d N : ℕ) (hd : d ≠ 0) :
    haveI : NeZero d := ⟨hd⟩
    |(((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - N * rho d / d| ≤ rho d := by
  haveI : NeZero d := ⟨hd⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hset_eq :
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card = congCount d (Rnat d) N := by
    unfold congCount
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hdvd⟩
      exact ⟨hn, (dvd_iff_mem_Rnat d n).mp hdvd⟩
    · rintro ⟨hn, hmem⟩
      exact ⟨hn, (dvd_iff_mem_Rnat d n).mpr hmem⟩
  rw [hset_eq]
  have hbound := congCount_bound d (Rnat d) hdpos N
  have hinter : Rnat d ∩ Finset.range d = Rnat d := Finset.inter_eq_left.mpr (Rnat_subset_range d)
  rwa [hinter, Rnat_card d] at hbound
