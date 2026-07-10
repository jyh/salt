/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Tuple

/-!
# Congruence compatibility (blueprint N2.7)

Two load-bearing facts for the Maynard sieve's cross-term analysis:

* `D₀_lt_of_prime_dvd_coprime` — any prime dividing something coprime to
  `W k = primorial (D₀ k)` must exceed `D₀ k`, since the primorial already
  contains every prime `≤ D₀ k`.
* `not_common_prime_cross` — for `i ≠ j`, a prime `p > D₀ k` cannot divide
  both `n + hSeq k i` and `n + hSeq k j`: it would divide their difference
  `hSeq k i − hSeq k j`, a nonzero integer of absolute value `≤ D₀ k < p`.
-/

namespace Salt.Maynard

/-- Every prime factor of anything coprime to `W k` exceeds `D₀ k`
(since `W k = primorial (D₀ k)` contains every prime `≤ D₀ k`). -/
theorem D₀_lt_of_prime_dvd_coprime {k m : ℕ} (hm : Nat.Coprime m (W k))
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) : D₀ k < p := by
  by_contra hle
  push Not at hle
  -- `p ≤ D₀ k` puts `p` into the primorial `W k`.
  have hpW : p ∣ W k := by
    unfold W
    exact hp.dvd_primorial_iff.mpr hle
  -- Then `p` divides the gcd, which is `1`.
  have hp1 : p ∣ 1 := hm ▸ Nat.dvd_gcd hpm hpW
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp hp1)

/-- Cross-collision impossibility: for `i ≠ j` a prime `p > D₀ k` cannot
divide both `n + hSeq k i` and `n + hSeq k j` (it would divide the
nonzero, `≤ D₀ k`, difference of two tuple entries). -/
theorem not_common_prime_cross {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    {n p : ℕ} (hp : p.Prime) (hpD : D₀ k < p)
    (h1 : p ∣ (n + hSeq k i)) (h2 : p ∣ (n + hSeq k j)) : False := by
  -- (`hp` records that `p` is prime; the collision is already ruled out by
  -- size, so primality is not needed beyond fixing the hypothesis.)
  have _hp_pos : 0 < p := hp.pos
  -- Work in ℤ: `p` divides the difference of the two multiples.
  have h1' : (p : ℤ) ∣ ((n : ℤ) + (hSeq k i : ℤ)) := by exact_mod_cast h1
  have h2' : (p : ℤ) ∣ ((n : ℤ) + (hSeq k j : ℤ)) := by exact_mod_cast h2
  have hdvd : (p : ℤ) ∣ ((hSeq k i : ℤ) - (hSeq k j : ℤ)) := by
    have := dvd_sub h1' h2'
    simpa using this
  -- The difference is nonzero, since `hSeq k` is injective and `i ≠ j`.
  have hne : ((hSeq k i : ℤ) - (hSeq k j : ℤ)) ≠ 0 := by
    have : hSeq k i ≠ hSeq k j := fun h => hij (hSeq_injective k h)
    intro hz
    apply this
    have : (hSeq k i : ℤ) = (hSeq k j : ℤ) := by linarith [sub_eq_zero.mp hz]
    exact_mod_cast this
  -- Hence `p = |p| ≤ |diff| ≤ D₀ k`, contradicting `D₀ k < p`.
  have hle : (p : ℤ).natAbs ≤ ((hSeq k i : ℤ) - (hSeq k j : ℤ)).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero hdvd hne
  have hiD : hSeq k i ≤ D₀ k := hSeq_le_D₀ k i
  have hjD : hSeq k j ≤ D₀ k := hSeq_le_D₀ k j
  have hbound : ((hSeq k i : ℤ) - (hSeq k j : ℤ)).natAbs ≤ D₀ k := by
    omega
  rw [Int.natAbs_natCast] at hle
  omega

/-! ## Free-modulus `(D, W')` generalizations (explicit-gaps sweep W2-4)

The same two facts with the primorial cutoff `W k = primorial (D₀ k)` replaced
by a free squarefree modulus `W'` together with an explicit lower-bound
hypothesis `hD : ∀ p prime, p ∤ W' → D ≤ p` (satisfied by `W' = primorial D`,
via `Nat.Prime.dvd_primorial_iff`), and the tuple bound `hSeq k · < D` (supplied
by `hSeq_lt_of_sup_lt`).  Instantiating `W' := W k`, `D := D₀ k + 1` recovers the
`W k`-specific versions above. -/

/-- **Free-`(D,W')` form of `D₀_lt_of_prime_dvd_coprime`.** Any prime dividing
something coprime to `W'` is `≥ D`, where `D` bounds the primes NOT dividing
`W'` from below (`hD`). No squarefreeness needed. -/
theorem D_le_of_prime_dvd_coprime {W' D m : ℕ}
    (hD : ∀ q : ℕ, q.Prime → ¬ q ∣ W' → D ≤ q)
    (hm : Nat.Coprime m W') {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) : D ≤ p := by
  refine hD p hp (fun hpW => ?_)
  have hp1 : p ∣ 1 := hm ▸ Nat.dvd_gcd hpm hpW
  exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)

/-- **Free-`(D,W')` form of `not_common_prime_cross`.** For `i ≠ j`, a prime
`p ≥ D` cannot divide both `n + hSeq k i` and `n + hSeq k j`, provided every
tuple entry is `< D` (`hlt`): `p` would divide the nonzero difference of two
entries, whose absolute value is `< D ≤ p`. -/
theorem not_common_prime_crossW {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    {D : ℕ} (hlt : ∀ l : Fin k, hSeq k l < D)
    {n p : ℕ} (hp : p.Prime) (hpD : D ≤ p)
    (h1 : p ∣ (n + hSeq k i)) (h2 : p ∣ (n + hSeq k j)) : False := by
  have _hp_pos : 0 < p := hp.pos
  have h1' : (p : ℤ) ∣ ((n : ℤ) + (hSeq k i : ℤ)) := by exact_mod_cast h1
  have h2' : (p : ℤ) ∣ ((n : ℤ) + (hSeq k j : ℤ)) := by exact_mod_cast h2
  have hdvd : (p : ℤ) ∣ ((hSeq k i : ℤ) - (hSeq k j : ℤ)) := by
    have := dvd_sub h1' h2'
    simpa using this
  have hne : ((hSeq k i : ℤ) - (hSeq k j : ℤ)) ≠ 0 := by
    have hneq : hSeq k i ≠ hSeq k j := fun h => hij (hSeq_injective k h)
    intro hz
    apply hneq
    have : (hSeq k i : ℤ) = (hSeq k j : ℤ) := by linarith [sub_eq_zero.mp hz]
    exact_mod_cast this
  have hle : (p : ℤ).natAbs ≤ ((hSeq k i : ℤ) - (hSeq k j : ℤ)).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero hdvd hne
  have hiD : hSeq k i < D := hlt i
  have hjD : hSeq k j < D := hlt j
  have hbound : ((hSeq k i : ℤ) - (hSeq k j : ℤ)).natAbs < D := by
    omega
  rw [Int.natAbs_natCast] at hle
  omega

end Salt.Maynard
