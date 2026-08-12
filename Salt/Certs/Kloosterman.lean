/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.EstermannGlobal

/-!
# COMPREHENSIBILITY CERTIFICATE — the Kloosterman/Weil bound

**Anchor (row 10 of `docs/CERT-ANCHORS-0811.md`).** The Nature draft,
`${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md:202`, in its surveyed-strength list:

> *"as of [survey date], no public artifact in any proof assistant proves … **the Weil
> bound for Kloosterman sums** …"*

**Landed declaration certified:** `Salt.Weil.norm_kloosterman_estermann`
(`Salt/Weil/EstermannGlobal.lean:318`).

## ⛔ THE GAP THIS CERTIFICATE EXISTS TO CLOSE — and it is a NAME, not a number

The paper's phrase is **"the Weil bound"**. The landed theorem is **Estermann's**
composite-modulus bound. *Those are not the same sentence:* Weil's theorem is the prime
case, `|S(a,b;p)| ≤ 2√p`; Estermann (1961) extends it to every modulus at the cost of a
divisor factor and a 2-adic factor. **A certificate that simply restated the landed
theorem would leave a reader to assume the paper's word and the kernel's theorem name the
same object, on the strength of a shared topic.**

🔑 ***SO THE GAP IS CLOSED BY DERIVATION, NOT BY PROSE: `cert_weil_bound_prime` PROVES
the classical Weil bound `2√p` as a consequence of the landed general bound.*** At an odd
prime the three extra factors are not "small": **TWO of them are exactly one, and the
THIRD IS WEIL'S CONSTANT.** `v₂(p) = 0` so the 2-adic factor is `1`; the gcd factor is `1`
whenever `p ∤ (a,b)`; and `d(p) = 2` — *not* one — **is** the `2` in `2√p`. *The general
bound does not merely imply something Weil-shaped; it lands on Weil's constant on the
nose, and the constant arrives from the DIVISOR COUNT.*

📌 *An earlier draft of this sentence said all three factors "are exactly one" and then
named `d(p) = 2` eleven words later — self-repairing, but the bold phrase overstates in
the CLEAN direction, and a reader who stops there loses where the `2` comes from.
Evidence raised it at the seal (20:53).*

## Direction and scope

**Direction: SPECIALISATION (downward, rule 2's safe side) plus a verbatim restatement.**
`cert_kloosterman_estermann` states the landed bound with every factor named in plain
words; `cert_weil_bound_prime` derives the classical form. Nothing is strengthened.

⚠️ **WHAT THIS CERTIFICATE DOES NOT CLAIM.** *The 2-adic factor is stated, never
discharged* — `2^{v₂(k)/2} ≤ 2^{3/2}` needs `v₂ ≤ 3`, which is `structure_of_isPrimitive`
(W4-a) at the road moduli and is **not** part of this bound. And the survey sentence
anchoring this row is a claim about the LITERATURE as of a survey date; **no Lean theorem
can support or refute it**, and none here tries. The certificate covers the mathematical
half only.

## Axioms

MEASURED at the landing, not asserted — the two named declarations both read

    [propext, Classical.choice, Quot.sound]

from `#print axioms` below. *An earlier draft of this line said "all three declarations";
there are TWO named ones, the third being the anonymous rule-6 `example`. The residue was
right and the count was not — which is the half an unmeasured axiom line always gets
right, and the reason to print rather than recall.*
-/

open Salt.Weil

namespace Salt.Certs

/-- **THE LANDED BOUND, IN PRIMITIVE VOCABULARY.** For every modulus `k ≥ 1` and every
pair `a b : ZMod k`, the Kloosterman sum's modulus is at most the product of exactly four
things: the square root of the 2-power in `k`, the number of divisors of `k`, the square
root of `k`, and the square root of `gcd(k, a, b)`.

*Stated as an `iff` against the landed name would be circular here — this is the same
proposition, so the certificate is `exact`, and the type-check IS the no-trade claim.* -/
theorem cert_kloosterman_estermann {k : ℕ} [NeZero k] (a b : ZMod k) :
    ‖kloosterman a b‖
      ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2)   -- the 2-adic factor
          * (k.divisors.card : ℝ)                  -- d(k), the divisor count
          * Real.sqrt (k : ℝ)                      -- √k, Weil's square-root saving
          * Real.sqrt ((Nat.gcd k (Nat.gcd a.val b.val) : ℕ) : ℝ) :=
  norm_kloosterman_estermann a b

/-- ⭐ **THE CLASSICAL WEIL BOUND, DERIVED — the paper's actual phrase.**
`|S(a,b;p)| ≤ 2√p` for an odd prime `p` not dividing `gcd(a,b)`.

**This is what "the Weil bound for Kloosterman sums" names**, and it falls out of the
landed general bound: TWO correction factors are one and the third supplies the constant
— `v₂(p) = 0`, `gcd(p, a, b) = 1`, and `d(p) = 2`, which IS the `2` in `2√p`. -/
theorem cert_weil_bound_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) [NeZero p]
    (a b : ZMod p) (hab : ¬ (p ∣ Nat.gcd a.val b.val)) :
    ‖kloosterman a b‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have h := norm_kloosterman_estermann (k := p) a b
  have h2 : p.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  have hd : p.divisors.card = 2 := by
    rw [Nat.Prime.divisors hp]
    exact Finset.card_pair (by have := hp.two_le; omega)
  have hg : Nat.gcd p (Nat.gcd a.val b.val) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hab
  rw [h2, hd, hg] at h
  simpa using h

/-- ⛔ **RULE 6 — VACUITY CONTROL.** `cert_weil_bound_prime` carries hypotheses, so they
must be shown SATISFIABLE: a green build plus a clean audit over contradictory hypotheses
is a certificate that says nothing, and no pipeline instrument reaches it.

Witness at `p = 3`, `a = b = 1`: prime, odd, and `3 ∤ gcd(1,1) = 1`. -/
example : (3 : ℕ).Prime ∧ (3 : ℕ) ≠ 2 ∧ ¬ ((3 : ℕ) ∣ Nat.gcd (1 : ℕ) (1 : ℕ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  decide +kernel

#print axioms cert_kloosterman_estermann
#print axioms cert_weil_bound_prime

end Salt.Certs
