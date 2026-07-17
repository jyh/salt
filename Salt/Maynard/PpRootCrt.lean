/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PpRootCyc
import Salt.Maynard.PpRootTwo

/-!
# The composite-modulus square-root count (node N-PP-CRT)

Third link of the GEH door's `PpLevel` chain. Folds the two landed prime-power
square-root bounds (`card_sq_eq_le_two_units_prime_pow` for odd `p^e`,
`PpRootTwo.card_sq_eq_units_two_pow_le_four` for `2^e`) through the Chinese
Remainder Theorem to bound the number of square roots of a unit `a ∈ (ZMod q)ˣ`
for an arbitrary composite modulus `q`.

## Main results

* `crt_sq_step` — the CRT engine: for coprime `m, n`, the square-root count over
  `ZMod (m*n)` is at most the product of the counts over the factors. Transports
  the root equation through `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.
* `card_sq_units_le_sqBound` — the induction over the prime factorization: the
  count is `≤ sqBound q`, a multiplicative bound (`2` per odd prime power, `4`
  for the `2`-part).
* `card_sq_eq_units_le` — primary deliverable: `N₂(a,q) ≤ 2^(ω(q)+1)`.
* `card_sq_eq_units_le_of_odd` — the sharper odd bound `N₂(a,q) ≤ 2^(ω(q))`.

`sqBound` gives the bonus `+1` exponent only to the (unique) even prime factor,
so it is multiplicative across coprime products — the naive `2^(ω+1)` is not
(the bonus would double). The primary bound then follows by `sqBound q ≤ 2^(ω+1)`.
-/

open Finset

namespace Salt.Maynard

/-- Per-modulus square-root bound: `2^(ω(q)+1)` if `q` is even, `2^(ω(q))` if odd,
where `ω(q) = q.primeFactors.card`. Chosen so that the `2`-adic factor's extra
`×2` is applied exactly once, making the bound multiplicative over coprime factors. -/
def sqBound (q : ℕ) : ℕ :=
  if 2 ∣ q then 2 ^ (q.primeFactors.card + 1) else 2 ^ q.primeFactors.card

/-- `sqBound` is multiplicative across coprime factors: at most one factor is even,
so the single `+1` bonus lands exactly once. -/
theorem sqBound_mul {d₁ d₂ : ℕ} (hcop : d₁.Coprime d₂) :
    sqBound d₁ * sqBound d₂ = sqBound (d₁ * d₂) := by
  have hω : (d₁ * d₂).primeFactors.card
      = d₁.primeFactors.card + d₂.primeFactors.card := by
    rw [hcop.primeFactors_mul, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  unfold sqBound
  by_cases hp1 : 2 ∣ d₁ <;> by_cases hp2 : 2 ∣ d₂
  · exfalso
    have hg : (2 : ℕ) ∣ Nat.gcd d₁ d₂ := Nat.dvd_gcd hp1 hp2
    rw [hcop.gcd_eq_one] at hg
    exact absurd hg (by decide)
  · have hm : 2 ∣ d₁ * d₂ := dvd_mul_of_dvd_left hp1 d₂
    rw [if_pos hp1, if_neg hp2, if_pos hm, hω]; ring
  · have hm : 2 ∣ d₁ * d₂ := dvd_mul_of_dvd_right hp2 d₁
    rw [if_neg hp1, if_pos hp2, if_pos hm, hω]; ring
  · have hm : ¬ 2 ∣ d₁ * d₂ := by
      rw [Nat.prime_two.dvd_mul]; exact not_or.mpr ⟨hp1, hp2⟩
    rw [if_neg hp1, if_neg hp2, if_neg hm, hω]; ring

/-- `sqBound q ≤ 2^(ω(q)+1)` always. -/
theorem sqBound_le (q : ℕ) : sqBound q ≤ 2 ^ (q.primeFactors.card + 1) := by
  unfold sqBound
  split
  · exact le_refl _
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)

/-- For odd `q`, `sqBound q = 2^(ω(q))`. -/
theorem sqBound_odd {q : ℕ} (hq : ¬ 2 ∣ q) : sqBound q = 2 ^ q.primeFactors.card := by
  unfold sqBound; rw [if_neg hq]

/-- **The CRT engine.** For coprime moduli `m, n`, the square-root count of a unit
`a ∈ (ZMod (m*n))ˣ` is at most the product of the per-factor bounds. The root
equation `x^2 = a` transports through the unit CRT isomorphism
`(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ` into a componentwise pair of equations,
so the filtered subtype splits as a product and its cardinality multiplies. -/
theorem crt_sq_step {m n : ℕ} (hcop : m.Coprime n) [NeZero m] [NeZero n] [NeZero (m * n)]
    (Bm Bn : ℕ)
    (h1 : ∀ a₁ : (ZMod m)ˣ, (univ.filter (fun y : (ZMod m)ˣ => y ^ 2 = a₁)).card ≤ Bm)
    (h2 : ∀ a₂ : (ZMod n)ˣ, (univ.filter (fun z : (ZMod n)ˣ => z ^ 2 = a₂)).card ≤ Bn)
    (a : (ZMod (m * n))ˣ) :
    (univ.filter (fun x : (ZMod (m * n))ˣ => x ^ 2 = a)).card ≤ Bm * Bn := by
  classical
  let E : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  have key : ∀ x : (ZMod (m * n))ˣ, (x ^ 2 = a) ↔ (E x) ^ 2 = E a := fun x => by
    rw [← map_pow E x 2]; exact E.injective.eq_iff.symm
  let f1 : {x : (ZMod (m * n))ˣ // x ^ 2 = a}
        ≃ {w : (ZMod m)ˣ × (ZMod n)ˣ // w ^ 2 = E a} :=
    E.toEquiv.subtypeEquiv (fun x => key x)
  let f2 : {w : (ZMod m)ˣ × (ZMod n)ˣ // w ^ 2 = E a}
        ≃ {w : (ZMod m)ˣ × (ZMod n)ˣ // w.1 ^ 2 = (E a).1 ∧ w.2 ^ 2 = (E a).2} :=
    Equiv.subtypeEquivRight (fun _ => Prod.ext_iff)
  let f : {x : (ZMod (m * n))ˣ // x ^ 2 = a}
        ≃ {y : (ZMod m)ˣ // y ^ 2 = (E a).1} × {z : (ZMod n)ˣ // z ^ 2 = (E a).2} :=
    (f1.trans f2).trans
      (Equiv.subtypeProdEquivProd (p := fun y : (ZMod m)ˣ => y ^ 2 = (E a).1)
        (q := fun z : (ZMod n)ˣ => z ^ 2 = (E a).2))
  have hcard : (univ.filter (fun x : (ZMod (m * n))ˣ => x ^ 2 = a)).card
      = (univ.filter (fun y : (ZMod m)ˣ => y ^ 2 = (E a).1)).card
        * (univ.filter (fun z : (ZMod n)ˣ => z ^ 2 = (E a).2)).card := by
    rw [← Fintype.card_subtype (fun x : (ZMod (m * n))ˣ => x ^ 2 = a),
        ← Fintype.card_subtype (fun y : (ZMod m)ˣ => y ^ 2 = (E a).1),
        ← Fintype.card_subtype (fun z : (ZMod n)ˣ => z ^ 2 = (E a).2),
        ← Fintype.card_prod]
    exact Fintype.card_congr f
  rw [hcard]
  exact Nat.mul_le_mul (h1 _) (h2 _)

/-- **The prime-factorization induction.** Over any modulus `q`, the number of square
roots of a unit is `≤ sqBound q`. The base cases are the two landed prime-power
bounds; the coprime step is `crt_sq_step` combined with `sqBound_mul`. -/
theorem card_sq_units_le_sqBound (q : ℕ) : ∀ [NeZero q] (a : (ZMod q)ˣ),
    (univ.filter (fun x : (ZMod q)ˣ => x ^ 2 = a)).card ≤ sqBound q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro _ a
      by_cases hp2 : p = 2
      · subst hp2
        refine le_trans (PpRootTwo.card_sq_eq_units_two_pow_le_four n a) ?_
        have hc : (2 ^ n).primeFactors.card = 1 := by
          rw [Nat.primeFactors_prime_pow hn.ne' hp, Finset.card_singleton]
        unfold sqBound
        rw [if_pos (dvd_pow_self 2 hn.ne'), hc]
        norm_num
      · refine le_trans (card_sq_eq_le_two_units_prime_pow hp hp2 n hn a) ?_
        have hnd : ¬ 2 ∣ p ^ n := fun hd =>
          hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
            (Nat.prime_two.prime.dvd_of_dvd_pow hd)).symm
        have hc : (p ^ n).primeFactors.card = 1 := by
          rw [Nat.primeFactors_prime_pow hn.ne' hp, Finset.card_singleton]
        unfold sqBound
        rw [if_neg hnd, hc]
        norm_num
  | zero => intro hinst; exact absurd rfl hinst.out
  | one =>
      intro _ a
      haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
      have hb : sqBound 1 = 1 := by
        have hc : (1 : ℕ).primeFactors.card = 0 := by
          rw [Nat.primeFactors_one, Finset.card_empty]
        unfold sqBound
        rw [if_neg (by decide : ¬ (2 : ℕ) ∣ 1), hc, pow_zero]
      rw [hb]
      calc (univ.filter (fun x : (ZMod 1)ˣ => x ^ 2 = a)).card
          ≤ (univ : Finset (ZMod 1)ˣ).card := Finset.card_filter_le _ _
        _ = Fintype.card (ZMod 1)ˣ := Finset.card_univ
        _ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  | coprime d₁ d₂ hd₁ hd₂ hcop ih₁ ih₂ =>
      intro _ a
      haveI hne1 : NeZero d₁ := ⟨by omega⟩
      haveI hne2 : NeZero d₂ := ⟨by omega⟩
      have hstep := crt_sq_step hcop (sqBound d₁) (sqBound d₂)
        (fun a₁ => ih₁ a₁) (fun a₂ => ih₂ a₂) a
      rwa [sqBound_mul hcop] at hstep

/-- **Primary deliverable.** For any modulus `q ≥ 2` and unit `a ∈ (ZMod q)ˣ`, the
number of square roots of `a` is at most `2^(ω(q)+1)`, where `ω(q) = q.primeFactors.card`. -/
theorem card_sq_eq_units_le (q : ℕ) (hq : 2 ≤ q) (a : (ZMod q)ˣ) :
    (letI : NeZero q := ⟨by omega⟩;
      (Finset.univ.filter (fun x : (ZMod q)ˣ => x ^ 2 = a)).card)
      ≤ 2 ^ (q.primeFactors.card + 1) := by
  haveI : NeZero q := ⟨by omega⟩
  exact (card_sq_units_le_sqBound q a).trans (sqBound_le q)

/-- **The sharper odd bound.** For an odd modulus `q` (`¬ 2 ∣ q`) the count drops to
`2^(ω(q))`: every prime-power factor contributes exactly `2 = 2^1`. -/
theorem card_sq_eq_units_le_of_odd (q : ℕ) (hq : ¬ 2 ∣ q) (a : (ZMod q)ˣ) :
    (letI : NeZero q := ⟨by rintro rfl; exact hq (dvd_zero 2)⟩;
      (Finset.univ.filter (fun x : (ZMod q)ˣ => x ^ 2 = a)).card)
      ≤ 2 ^ q.primeFactors.card := by
  haveI : NeZero q := ⟨by rintro rfl; exact hq (dvd_zero 2)⟩
  have h := card_sq_units_le_sqBound q a
  rwa [sqBound_odd hq] at h

end Salt.Maynard
