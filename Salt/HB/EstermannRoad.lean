/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.RealPrimStructure
import Salt.Weil.EstermannTwoAdic

/-!
# The road-modulus close — Estermann (7.1) with EVERY hypothesis discharged

`Salt.Weil.EstermannTwoAdic` removes the 2-adic factor from the composite Estermann bound
under `v₂(k) ≤ 8`, and at the §5 road modulus `k = D·δ₁·w₁` that reduces to two valuation
bounds, one on `α₂` and one on `q`.  This module discharges the `q` one **from the road's
own standing hypothesis** — `χ` primitive mod `q` — and assembles the result.

## The rows

* `factorization_two_le_three_of_isPrimitive` (D6) — W4-a in valuation form: a primitive
  `DirichletCharacter ℤ q` forces `v₂(q) ≤ 3`.  This is `structure_of_isPrimitive`'s
  `a = 0 ∨ a = 2 ∨ a = 3` read as an inequality; there is no fourth admissible 2-part.
* `norm_kloosterman_estermann_road_of_isPrimitive` (D7) — **the fully discharged close.**
  HB (7.1) verbatim on the road modulus, with the character hypothesis in place of the
  valuation hypothesis on `q`.  Its proof is one `exact`: `3 ≤ 8`.

## ⛔ NEGATIVE CONTROL — read the fence before the row

`two_pow_totient_exceeds_estermann_at_nine` at the end of this file is **NOT a bound and NOT
a positive result.**  It is a boundary witness: it proves the D1′ inequality
`φ(2^e) ≤ d(2^e)·√(2^e)` **FAILS** at `e = 9`, i.e. that the `e ≤ 8` hypothesis carried by
every row above is where the method genuinely stops rather than where the proof got tired.
Quoting it as if it bounded a Kloosterman sum would invert its content.

📌 **Two numbers, deliberately not collapsed.**  The Weil-side rows are stated at `v₂ ≤ 8`
because `9` is where D1′ dies (this control).  The road consumes only `v₂(q) ≤ 3` (D6).  So
the discharge has five powers of two of headroom over the consumer, and that gap is a fact
worth being able to read off — which is why the larger hypothesis set was not silently
narrowed to the one the road happens to need.
-/

namespace Salt.HB

/-- **D6 — W4-a in valuation form.**  A primitive Dirichlet character mod `q` (over `ℤ`,
where the "real" hypothesis is free) forces `v₂(q) ≤ 3`: the structure theorem admits a
2-part of `2^0`, `2^2` or `2^3` and nothing else. -/
theorem factorization_two_le_three_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hprim : χ.IsPrimitive) :
    q.factorization 2 ≤ 3 := by
  obtain ⟨a, m, χ₂, hq, ha, hsq, hodd, hb, hs⟩ := structure_of_isPrimitive χ hprim
  have hm0 : m ≠ 0 := by rintro rfl; exact hodd (dvd_zero 2)
  subst hq
  rw [Nat.factorization_mul (by positivity) hm0]
  have h1 : (2 ^ a : ℕ).factorization 2 = a := by
    simp [Nat.Prime.factorization_pow Nat.prime_two]
  have h2 : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hodd
  simp only [Finsupp.coe_add, Pi.add_apply, h1, h2, add_zero]
  omega

open Salt.Weil in
/-- **D7 — THE FULLY DISCHARGED CLOSE.**  Heath-Brown (7.1) on the road modulus
`k = roadModulus α₂ q · δ₁ · w₁`, with **no 2-adic factor** and with the `q`-side valuation
hypothesis replaced by the road's own primitivity hypothesis on `χ`. -/
theorem norm_kloosterman_estermann_road_of_isPrimitive {α₂ q δ₁ w₁ α : ℕ}
    [NeZero q] (χ : DirichletCharacter ℤ q) (hprim : χ.IsPrimitive)
    (hα₂ : α₂ ≠ 0) (hv2α : α₂.factorization 2 ≤ 8)
    (hα : 2 ∣ α) (hδ : Nat.Coprime δ₁ α) (hw : Nat.Coprime w₁ α)
    [NeZero (roadModulus α₂ q * δ₁ * w₁)] (a b : ZMod (roadModulus α₂ q * δ₁ * w₁)) :
    ‖kloosterman a b‖
      ≤ ((roadModulus α₂ q * δ₁ * w₁).divisors.card : ℝ)
          * Real.sqrt ((roadModulus α₂ q * δ₁ * w₁ : ℕ) : ℝ)
          * Real.sqrt
              ((Nat.gcd (roadModulus α₂ q * δ₁ * w₁) (Nat.gcd a.val b.val) : ℕ) : ℝ) :=
  norm_kloosterman_estermann_road_clean hα₂ (NeZero.ne q) hv2α
    ((factorization_two_le_three_of_isPrimitive χ hprim).trans (by norm_num)) hα hδ hw a b

/-- ⛔ **NEGATIVE CONTROL — NOT A BOUND.  The `e ≤ 8` threshold is SHARP for this method.**

This row states that `Salt.Weil.two_pow_totient_le_estermann`'s inequality is **FALSE** at
`e = 9`: `d(2^9)·√(2^9) = 10·√512 < 256 = φ(2^9)`.  Its content is the *failure* of a bound,
so it can never be composed into an estimate; it exists so that the `≤ 8` hypothesis on
every row above reads as a limit of the method and not as unexamined slack.

*Witness kind: REFUTATION at a point.*  `e = 9` is the first failure — `e = 8` satisfies the
inequality, which is exactly why the hypothesis is `≤ 8` and not something smaller. -/
theorem two_pow_totient_exceeds_estermann_at_nine :
    (((2 ^ 9 : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ 9)
      < (((2 ^ 9 : ℕ).totient : ℕ) : ℝ) := by
  have hd : ((2 ^ 9 : ℕ).divisors.card) = 10 := by decide +kernel
  have ht : ((2 ^ 9 : ℕ).totient) = 256 := by decide +kernel
  rw [hd, ht]
  have h1 : Real.sqrt ((2 : ℝ) ^ 9) < 22.7 := by
    rw [show ((2:ℝ)^9) = 512 by norm_num]
    have h2 : Real.sqrt 512 < Real.sqrt (22.7 ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  norm_num at h1 ⊢
  nlinarith [h1, Real.sqrt_nonneg ((2:ℝ)^9)]

end Salt.HB
