/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehPp

/-!
# The pp-in-AP primitives (node G-PpLevel, the root-counting floor's two gaps)

`Salt/Maynard/GehPp.lean` landed the crude uniform per-`q` bound for the prime-power
correction and recorded, in its obstruction ledger, the two missing primitives that a
sharp `PpLevel (3999/4000)` discharge consumes:

1. the **composite-modulus square-root count** `#{r ∈ ZMod q : r² = a} ≤ 2^{ω(q)+1}`;
2. the **three multiplicative sums** `∑_{q≤Q} 2^{ω(q)}/q`, `∑_{q≤Q} 2^{ω(q)}`, and
   `∑_{q≤Q} 1/φ(q)`, each `≪ polylog`.

This file supplies the arithmetic-sum primitives (2), stated in both the `τ`-form
(`τ(q) = #q.divisors`) that the divisor swap proves directly and the `2^{ω(q)}`-form
(via `2^{ω(q)} ≤ τ(q)`) the sharp assembly names.  The `∑ 1/φ` sum is already landed as
`Salt.LS.sum_inv_totient_le`; it is re-exported here for a single consumption point.

All three sums reduce to the classical divisor swap `∑_{q≤Q} F(q) ∑_{d∣q} 1 =
∑_{d≤Q} ∑_{q≤Q, d∣q} F(q)`, closed by `Salt.LS.sum_inv_dvd_multiples_le`
(`∑_{q≤Q, d∣q} 1/q ≤ (1+log Q)/d`) and the harmonic bound `∑_{d≤Q} 1/d ≤ 1+log Q`.
-/

open Finset ArithmeticFunction

/-- `2^{ω(q)} ≤ τ(q)`: the squarefree divisors alone number `2^{ω(q)}`.  Concretely,
`τ(q) = ∏_{p∣q} (v_p(q)+1)` and each factor is `≥ 2`, so the constant product `∏ 2`
is dominated. -/
lemma two_pow_omega_le_card_divisors {q : ℕ} (hq : q ≠ 0) :
    (2 : ℝ) ^ q.primeFactors.card ≤ (q.divisors.card : ℝ) := by
  have hN : (2 : ℕ) ^ q.primeFactors.card ≤ q.divisors.card := by
    rw [Nat.card_divisors hq]
    calc (2 : ℕ) ^ q.primeFactors.card
        = ∏ _p ∈ q.primeFactors, 2 := (Finset.prod_const 2).symm
      _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p + 1) := by
          refine Finset.prod_le_prod' (fun p hp => ?_)
          have hmem := Nat.mem_primeFactors.mp hp
          have hpos : 0 < q.factorization p := hmem.1.factorization_pos_of_dvd hq hmem.2.1
          omega
  exact_mod_cast hN

/-- Harmonic bound over `Icc`: `∑_{d≤Q} 1/d ≤ 1 + log Q`. -/
lemma sum_one_div_Icc_le (Q : ℕ) :
    ∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / d ≤ 1 + Real.log Q := by
  have hEq : ∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / d = (harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    exact Finset.sum_congr rfl (fun d _ => by rw [one_div])
  rw [hEq]; exact harmonic_le_one_add_log Q

/-- **The divisor swap.** For a weight `F` supported on `Icc 1 Q`, the `divisors`-count sum
telescopes to a double sum over `(d, q)` with `d ∣ q`. -/
lemma sum_card_divisors_mul_swap (Q : ℕ) (F : ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) * F q
      = ∑ d ∈ Finset.Icc 1 Q, ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), F q := by
  have hstep : ∀ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) * F q
      = ∑ d ∈ Finset.Icc 1 Q, (if d ∈ q.divisors then F q else 0) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 Q).filter (fun d => d ∈ q.divisors) = q.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨_, hd⟩; exact hd
      · intro hd
        exact ⟨⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hq.2⟩, hd⟩
    rw [hfilt, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [Finset.mem_Icc] at hq
  have hiff : (d ∈ q.divisors) ↔ (d ∣ q) := by
    rw [Nat.mem_divisors]; exact and_iff_left (by omega : q ≠ 0)
  simp only [hiff]

/-- **Primitive 2, sum 1 (`τ`-form).** `∑_{q≤Q} τ(q)/q ≤ (1+log Q)²`.  Divisor swap:
`∑_q (∑_{d∣q} 1)/q = ∑_d ∑_{q≤Q, d∣q} 1/q ≤ ∑_d (1+log Q)/d ≤ (1+log Q)²`. -/
lemma sum_card_divisors_div_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) / q ≤ (1 + Real.log Q) ^ 2 := by
  have hlogQ : (0 : ℝ) ≤ 1 + Real.log Q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ); linarith
  have hrw : ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) / q
      = ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) * ((1 : ℝ) / q) :=
    Finset.sum_congr rfl (fun q _ => by rw [mul_one_div])
  rw [hrw, sum_card_divisors_mul_swap Q (fun q => (1 : ℝ) / q)]
  calc ∑ d ∈ Finset.Icc 1 Q, ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / q
      ≤ ∑ d ∈ Finset.Icc 1 Q, (1 + Real.log Q) / d := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [Finset.mem_Icc] at hd
        exact Salt.LS.sum_inv_dvd_multiples_le d Q hd.1 hd.2
    _ = (1 + Real.log Q) * ∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / d := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [mul_one_div])
    _ ≤ (1 + Real.log Q) * (1 + Real.log Q) :=
        mul_le_mul_of_nonneg_left (sum_one_div_Icc_le Q) hlogQ
    _ = (1 + Real.log Q) ^ 2 := (sq _).symm

/-- **Primitive 2, sum 1 (`2^{ω}`-form).** `∑_{q≤Q} 2^{ω(q)}/q ≤ (1+log Q)²`. -/
lemma sum_two_pow_omega_div_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card / q ≤ (1 + Real.log Q) ^ 2 := by
  refine le_trans (Finset.sum_le_sum (fun q hq => ?_)) (sum_card_divisors_div_le Q hQ)
  rw [Finset.mem_Icc] at hq
  exact div_le_div_of_nonneg_right (two_pow_omega_le_card_divisors (by omega))
    (Nat.cast_nonneg q)

/-- **Primitive 2, sum 2 (`2^{ω}`-form).** `∑_{q≤Q} 2^{ω(q)} ≤ Q·(1+log Q)`.  Dominated
pointwise by `τ(q)` and closed by `Salt.BV.sum_card_divisors_le`. -/
lemma sum_two_pow_omega_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card ≤ (Q : ℝ) * (1 + Real.log Q) := by
  refine le_trans (Finset.sum_le_sum (fun q hq => ?_)) (Salt.BV.sum_card_divisors_le Q hQ)
  rw [Finset.mem_Icc] at hq
  exact two_pow_omega_le_card_divisors (by omega)

/-- **Primitive 2, sum 3** (re-export).  `∑_{q≤Q} 1/φ(q) ≤ 4·(1+log Q)`; already landed
as `Salt.LS.sum_inv_totient_le` (the L8.1b divisor-swap `∑ 1/φ` bound), surfaced here so
all three pp-in-AP arithmetic sums share one consumption point. -/
lemma sum_inv_totient_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ) ≤ 4 * (1 + Real.log Q) :=
  Salt.LS.sum_inv_totient_le Q hQ

/-! ## The remaining floor: primitive 1 and the assembly (obstruction ledger)

Primitive 2 (all three sums) is landed above, sorry-free.  The two remaining pieces are
recorded here as the honest floor; neither is landed (no `sorry` appears — these are the
open obligations, delegated to a Fable/human-tier session).

### Primitive 1 — the composite-modulus square-root count (a spec correction, then a
units-structure development).

The literal target `#{r ∈ ZMod q : r² = a} ≤ 2^{ω(q)+1}` is **false for non-unit `a`**:
e.g. `r² = 0` in `ZMod (p²)` has the `p` roots `{0, p, 2p, …, (p−1)p}`, and `p > 4 =
2^{ω(p²)+1}` for `p ≥ 5`.  The honest statement must restrict to a **unit** `a` (all the
pp-in-AP consumer ever needs: `p² ≡ a (mod q)` with `p` a prime coprime to `q`; the `≤ ω(q)`
primes `p ∣ q` are handled separately), equivalently a 2-torsion bound
`#{r ∈ (ZMod q)ˣ : r² = 1} ≤ 2^{ω(q)+1}`.

Route (all tools present in mathlib, but the assembly is a fresh multi-hundred-line
development): the units product `(ZMod q)ˣ ≃* Π p ∈ q.primeFactors, (ZMod (p^{e_p}))ˣ` via
`Units.mapEquiv (ZMod.equivPi hn).toMulEquiv |>.trans MulEquiv.piUnits`; the 2-torsion of a
product is the product of 2-torsions; each odd factor `≤ 2` by
`IsCyclic.card_pow_eq_one_le` (`ZMod.isCyclic_units_of_prime_pow`); the `p = 2` factor `≤ 4`.
The `p = 2` corner is the load-bearing gap: mathlib supplies only `¬IsCyclic (ZMod 8)ˣ`
(`ZMod.not_isCyclic_units_eight`, via `Monoid.exponent … ∣ 2`), **not** the structure
`(ZMod 2^e)ˣ ≃ ZMod 2 × ZMod 2^{e-2}` nor any 2-torsion count, so bounding that factor by a
constant needs a bespoke development.

### The assembly — `ppLevel_holds : PpLevel (3999/4000)` (needs `k`-th power counts, not
just squares).

The sharp per-`(q,a)` bound folds every proper prime power `p^k ≡ a (mod q)` (`k ≥ 2`) into
`2^{ω(q)+1}·(√x/φ(q) + 1)`-grade.  The `k = 2` term dominates the mass, but the `k ≥ 3` tail
is **not** negligible after summing over `q ≤ Q ≈ x^θ`: its crude total `x^{1/3}·log x` per
class sums to `x^{θ+1/3}·log x ≫ x`.  So the tail also needs the per-class `1/q` saving, i.e.
a root count for `X^k ≡ a (mod q)` for *every* `k ≥ 2` — strictly more than primitive 1's
squares.  With that count in hand, the residue part sums via primitive-2 sums 1–2
(`√x·log² + x^θ·log`) and the mean part via sum 3 (`√x·log²`), giving `≪ x/log^A` at
`B = 0`.  This is a Fable/human-tier obligation. -/
