/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PpRootCyc
import Salt.Maynard.PpRootTwo

/-!
# The general-`k` composite-modulus root count (node PP3-NK)

Discharges `PpRootCrt`'s named residual: the CRT fold for arbitrary exponent `k`.
Folds the two landed prime-power `k`-th-root bounds
(`card_pow_eq_le_gcd_units_prime_pow` for odd `p^e`, giving `gcd(k, φ(p^e)) ≤ k`,
and `PpRootTwo.card_pow_eq_units_two_pow_le'` for `2^e`, giving
`gcd(k,2)·gcd(k,2^{e−2}) ≤ 2k`) through the Chinese Remainder Theorem to bound
the number of `k`-th roots of a unit `a ∈ (ZMod q)ˣ` for any composite `q`.

## Main results

* `crt_pow_step` — the general-`k` CRT engine: for coprime `m, n`, the `k`-th-root
  count over `ZMod (m*n)` is at most the product of the counts over the factors.
  The `k`-generic transport of `crt_sq_step` (the `k = 2` there was the consumer's
  specialization, not the engine's).
* `card_pow_units_le_nkBound` — the induction over the prime factorization: the
  count is `≤ nkBound q k`, a multiplicative bound (`k` per odd prime power,
  `2k` for the `2`-part).
* `card_pow_eq_units_le_general` — primary deliverable: `N_k(a,q) ≤ 2k·k^{ω(q)}`.

`nkBound` gives the bonus `×2` only to the (unique) even prime factor, so it is
multiplicative across coprime products (mirrors `sqBound`). The primary bound then
follows by `nkBound q k ≤ 2k·k^{ω(q)}`.
-/

open Finset

namespace Salt.Maynard

/-- **The general-`k` CRT engine.** For coprime moduli `m, n`, the `k`-th-root count
of a unit `a ∈ (ZMod (m*n))ˣ` is at most the product of the per-factor bounds. The
root equation `x^k = a` transports through the unit CRT isomorphism
`(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ` into a componentwise pair of equations,
so the filtered subtype splits as a product and its cardinality multiplies. -/
theorem crt_pow_step {m n : ℕ} (hcop : m.Coprime n) [NeZero m] [NeZero n]
    [NeZero (m * n)] (k : ℕ) (Bm Bn : ℕ)
    (h1 : ∀ a₁ : (ZMod m)ˣ, (univ.filter (fun y : (ZMod m)ˣ => y ^ k = a₁)).card ≤ Bm)
    (h2 : ∀ a₂ : (ZMod n)ˣ, (univ.filter (fun z : (ZMod n)ˣ => z ^ k = a₂)).card ≤ Bn)
    (a : (ZMod (m * n))ˣ) :
    (univ.filter (fun x : (ZMod (m * n))ˣ => x ^ k = a)).card ≤ Bm * Bn := by
  classical
  let E : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  have key : ∀ x : (ZMod (m * n))ˣ, (x ^ k = a) ↔ (E x) ^ k = E a := fun x => by
    rw [← map_pow E x k]; exact E.injective.eq_iff.symm
  let f1 : {x : (ZMod (m * n))ˣ // x ^ k = a}
        ≃ {w : (ZMod m)ˣ × (ZMod n)ˣ // w ^ k = E a} :=
    E.toEquiv.subtypeEquiv (fun x => key x)
  let f2 : {w : (ZMod m)ˣ × (ZMod n)ˣ // w ^ k = E a}
        ≃ {w : (ZMod m)ˣ × (ZMod n)ˣ // w.1 ^ k = (E a).1 ∧ w.2 ^ k = (E a).2} :=
    Equiv.subtypeEquivRight (fun _ => Prod.ext_iff)
  let f : {x : (ZMod (m * n))ˣ // x ^ k = a}
        ≃ {y : (ZMod m)ˣ // y ^ k = (E a).1} × {z : (ZMod n)ˣ // z ^ k = (E a).2} :=
    (f1.trans f2).trans
      (Equiv.subtypeProdEquivProd (p := fun y : (ZMod m)ˣ => y ^ k = (E a).1)
        (q := fun z : (ZMod n)ˣ => z ^ k = (E a).2))
  have hcard : (univ.filter (fun x : (ZMod (m * n))ˣ => x ^ k = a)).card
      = (univ.filter (fun y : (ZMod m)ˣ => y ^ k = (E a).1)).card
        * (univ.filter (fun z : (ZMod n)ˣ => z ^ k = (E a).2)).card := by
    rw [← Fintype.card_subtype (fun x : (ZMod (m * n))ˣ => x ^ k = a),
        ← Fintype.card_subtype (fun y : (ZMod m)ˣ => y ^ k = (E a).1),
        ← Fintype.card_subtype (fun z : (ZMod n)ˣ => z ^ k = (E a).2),
        ← Fintype.card_prod]
    exact Fintype.card_congr f
  rw [hcard]
  exact Nat.mul_le_mul (h1 _) (h2 _)

/-- Per-modulus `k`-th-root bound: `2·k^(ω(q))` if `q` is even, `k^(ω(q))` if odd,
where `ω(q) = q.primeFactors.card`. Each prime power contributes a factor `k`; the
(unique) `2`-adic factor gets one extra `×2`, so the bound is multiplicative over
coprime factors (mirrors `sqBound`). -/
def nkBound (q k : ℕ) : ℕ :=
  if 2 ∣ q then 2 * k ^ q.primeFactors.card else k ^ q.primeFactors.card

/-- `nkBound` is multiplicative across coprime factors: at most one factor is even,
so the single `×2` bonus lands exactly once. -/
theorem nkBound_mul {d₁ d₂ : ℕ} (k : ℕ) (hcop : d₁.Coprime d₂) :
    nkBound d₁ k * nkBound d₂ k = nkBound (d₁ * d₂) k := by
  have hω : (d₁ * d₂).primeFactors.card
      = d₁.primeFactors.card + d₂.primeFactors.card := by
    rw [hcop.primeFactors_mul, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  unfold nkBound
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

/-- `nkBound q k ≤ 2k·k^(ω(q))` always (for `k ≥ 1`): even case loses only the odd
part's `k`, odd case is dominated since `1 ≤ 2k`. -/
theorem nkBound_le (q k : ℕ) (hk : 1 ≤ k) :
    nkBound q k ≤ 2 * k * k ^ q.primeFactors.card := by
  unfold nkBound
  split
  · exact Nat.mul_le_mul (by omega) (le_refl _)
  · calc k ^ q.primeFactors.card
        = 1 * k ^ q.primeFactors.card := (one_mul _).symm
      _ ≤ 2 * k * k ^ q.primeFactors.card := Nat.mul_le_mul (by omega) (le_refl _)

/-- **The uniform `2`-part base case** (all `e`, `k ≥ 1`). The number of `k`-th roots
of any unit in `(ZMod (2^e))ˣ` is at most `2k`. For `e ≥ 3` this is the landed
`gcd(k,2)·gcd(k,2^{e−2}) ≤ 2·k`; for `e ≤ 2` the whole unit group has order `≤ 2`. -/
theorem card_pow_units_two_pow_le_two_mul (e k : ℕ) (hk : 1 ≤ k)
    (a : (ZMod (2 ^ e))ˣ) :
    (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ k = a)).card ≤ 2 * k := by
  classical
  rcases lt_or_ge e 3 with he | he
  · have hsub : (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ k = a)).card
        ≤ Fintype.card (ZMod (2 ^ e))ˣ := by
      rw [← Finset.card_univ]; exact Finset.card_filter_le _ _
    have hcard : Fintype.card (ZMod (2 ^ e))ˣ ≤ 2 := by interval_cases e <;> decide
    calc (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ k = a)).card
        ≤ 2 := hsub.trans hcard
      _ ≤ 2 * k := by omega
  · have h := PpRootTwo.card_pow_eq_units_two_pow_le' he k a
    have hg2 : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right k 2)
    have hgk : Nat.gcd k (2 ^ (e - 2)) ≤ k := Nat.le_of_dvd hk (Nat.gcd_dvd_left k _)
    calc (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ k = a)).card
        ≤ Nat.gcd k 2 * Nat.gcd k (2 ^ (e - 2)) := h
      _ ≤ 2 * k := Nat.mul_le_mul hg2 hgk

/-- **The prime-factorization induction.** Over any modulus `q`, the number of `k`-th
roots of a unit is `≤ nkBound q k`. Base cases are the two landed prime-power bounds
(odd `p^e`: `gcd(k, φ(p^e)) ≤ k`; `2^e`: `≤ 2k`); the coprime step is `crt_pow_step`
combined with `nkBound_mul`. -/
theorem card_pow_units_le_nkBound (k : ℕ) (hk : 1 ≤ k) (q : ℕ) :
    ∀ [NeZero q] (a : (ZMod q)ˣ),
    (univ.filter (fun x : (ZMod q)ˣ => x ^ k = a)).card ≤ nkBound q k := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro _ a
      by_cases hp2 : p = 2
      · subst hp2
        refine le_trans (card_pow_units_two_pow_le_two_mul n k hk a) ?_
        have hc : (2 ^ n).primeFactors.card = 1 := by
          rw [Nat.primeFactors_prime_pow hn.ne' hp, Finset.card_singleton]
        unfold nkBound
        rw [if_pos (dvd_pow_self 2 hn.ne'), hc, pow_one]
      · refine le_trans (card_pow_eq_le_gcd_units_prime_pow hp hp2 n hn k a) ?_
        have hnd : ¬ 2 ∣ p ^ n := fun hd =>
          hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
            (Nat.prime_two.prime.dvd_of_dvd_pow hd)).symm
        have hc : (p ^ n).primeFactors.card = 1 := by
          rw [Nat.primeFactors_prime_pow hn.ne' hp, Finset.card_singleton]
        unfold nkBound
        rw [if_neg hnd, hc, pow_one]
        exact Nat.le_of_dvd hk (Nat.gcd_dvd_left k _)
  | zero => intro hinst; exact absurd rfl hinst.out
  | one =>
      intro _ a
      haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
      have hb : nkBound 1 k = 1 := by
        have hc : (1 : ℕ).primeFactors.card = 0 := by
          rw [Nat.primeFactors_one, Finset.card_empty]
        unfold nkBound
        rw [if_neg (by decide : ¬ (2 : ℕ) ∣ 1), hc, pow_zero]
      rw [hb]
      calc (univ.filter (fun x : (ZMod 1)ˣ => x ^ k = a)).card
          ≤ (univ : Finset (ZMod 1)ˣ).card := Finset.card_filter_le _ _
        _ = Fintype.card (ZMod 1)ˣ := Finset.card_univ
        _ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  | coprime d₁ d₂ hd₁ hd₂ hcop ih₁ ih₂ =>
      intro _ a
      haveI hne1 : NeZero d₁ := ⟨by omega⟩
      haveI hne2 : NeZero d₂ := ⟨by omega⟩
      have hstep := crt_pow_step hcop k (nkBound d₁ k) (nkBound d₂ k)
        (fun a₁ => ih₁ a₁) (fun a₂ => ih₂ a₂) a
      rwa [nkBound_mul k hcop] at hstep

/-- **Primary deliverable** (node PP3-NK). For any modulus `q ≥ 2`, exponent `k ≥ 1`,
and unit `a ∈ (ZMod q)ˣ`, the number of `k`-th roots of `a` is at most `2k·k^{ω(q)}`,
where `ω(q) = q.primeFactors.card`. -/
theorem card_pow_eq_units_le_general (q : ℕ) (hq : 2 ≤ q) (k : ℕ) (hk : 1 ≤ k)
    (a : (ZMod q)ˣ) :
    (letI : NeZero q := ⟨by omega⟩;
      (Finset.univ.filter (fun x : (ZMod q)ˣ => x ^ k = a)).card)
      ≤ 2 * k * k ^ q.primeFactors.card := by
  haveI : NeZero q := ⟨by omega⟩
  exact (card_pow_units_le_nkBound k hk q a).trans (nkBound_le q k hk)

end Salt.Maynard
