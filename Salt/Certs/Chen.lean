/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenTheorem
import Salt.Fulcrum.ChenCorollary

/-!
# COMPREHENSIBILITY CERTIFICATE — Chen's theorem (unconditional). **TWO certs.**

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorems certified — **anchor row 5 names TWO declarations and this file covers
BOTH** (the "one paper phrase, several declarations" hazard, which `Salt/Certs/ChowlaSpine.lean`
hit first):
* `Salt.Chen.chen_headline` (`Salt/Chen/ChenTheorem.lean:32`) — the twin form.
* `Salt.Fulcrum.chen_omega_prod_le_three` (`Salt/Fulcrum/ChenCorollary.lean:34`) — the
  `Ω`-corollary, **the form the Pi paper pins by name**.

**Anchors** (`docs/CERT-ANCHORS-0811.md`, row 5): Nature :201 *"Chen's theorem"* in the
class enumeration and :238 *"Chen's theorem on day 10"*; Pi :324
`\leaninline{Salt.Fulcrum.chen_omega_prod_le_three}` with *"Ω(p(p+2)) ≤ 3 for infinitely
many primes p"*.

## THE PHRASE → DECLARATION MAP
The anchor papers (Pi and the Nature draft) each say *"Chen's theorem"* once; the corpus proves it in three declarations, and a
reader is owed the correspondence:

1. **The twin form** — infinitely many primes `p` with `p + 2` a `P₂`.
   `Salt.Chen.chen_headline`. ✅ certified here as **`cert_chen`** (Part 1).
2. **The `Ω`-corollary** — `Ω(p(p+2)) ≤ 3` infinitely often; **this is the one Pi pins by
   name**. `Salt.Fulcrum.chen_omega_prod_le_three`. ✅ certified here as
   **`cert_chen_omega`** (Part 2).
3. **The Goldbach half** — every sufficiently large even `N` is a prime plus a `P₂`.
   `Salt.Goldbach.chen_goldbach` (`Salt/Goldbach/ChenGoldbach.lean:41`).
   ❌ **NOT certified in this file** — it is anchor row 6 and gets its own certificate.

---

# PART 1 — `cert_chen`, the twin form

## WHAT THE THEOREM SAYS, in one sentence
**There are infinitely many primes `p` such that `p + 2` is either prime or a product of
two primes.**

That is the whole claim. `Set.Infinite` on `{p | …}` means exactly *the set of such `p` is
not finite*, i.e. infinitely many primes `p` have the stated property.

## THE VOCABULARY, unfolded
The landed statement writes the second conjunct as `IsP2 2 (p + 2)`. That name is the only
piece of corpus-internal vocabulary in it, and unfolding it IS this certificate.

`IsP2 z m` (`Salt/Chen/WeightTrivia.lean:270`) is
> `m.Prime ∨ ∃ p q, p.Prime ∧ q.Prime ∧ m = p * q ∧ z ≤ p ∧ z ≤ q`

— *prime, or a semiprime both of whose factors are at least `z`.* The `z` is the sieve's
size decoration; per the definition's own note at the source, a sifted sequence forces
every prime factor above the sieving threshold, which is why the general definition
carries it.

**The landed instance is `IsP2 2 (p + 2)` — the threshold is `z = 2`, where the size
clauses carry no information.** At `z = 2` the two clauses `2 ≤ p`, `2 ≤ q` are
*automatic*: every prime is `≥ 2`
(`Nat.Prime.two_le`). So dropping them loses nothing, and this certificate does not merely
assert that — **it proves it**: the certificate's proof establishes the two sets are
**equal** (`hset`, both inclusions), the reverse inclusion being precisely where the
`2 ≤ p`, `2 ≤ q` decorations are rebuilt from primality. The plain disjunction below is the
landed statement, not a weakening of it.

## DIRECTION (rule 3)
`cert_chen` is the **same set, hence the same proposition** as `Salt.Chen.chen_headline`,
with `IsP2 2` replaced by its definition and the two vacuous size clauses discharged.
Proved from `chen_headline` by rewriting along the proved set equality.
**No generality is traded**; this is not an implication.

## HYPOTHESES (rule 2, named)
**None. The landed theorem is unconditional** — `chen_headline` takes no binders and no
hypotheses (it is the composition of two closed bundles, `hA3_bundle` and `hL_bundle`), and
neither does this certificate. There is no Riemann-hypothesis, no Elliott–Halberstam, and
no unproved sieve axiom standing behind it; the axiom residue below is the whole of what it
rests on.

## WHAT THIS CERTIFICATE DOES **NOT** CLAIM (rule 2, and the claim-language law)
* **Nothing about twin primes.** The disjunction is *inside* the set: for each `p` in it,
  `p + 2` is prime **or** a semiprime, and the theorem does not say which alternative
  occurs. Nothing here yields infinitude of the prime alternative — obtaining that from
  this statement would *be* the twin-prime conjecture.
* **Only the twin half of "Chen's theorem".** The classical result also has a Goldbach
  half (*every sufficiently large even number is a prime plus a `P₂`*). That is the
  separate declaration `chen_goldbach`, row 6 of the anchor table, **not this file.** The
  Nature phrase covers both halves; this certificate covers one.
* **The two prime factors need not be distinct.** `q = r` is permitted, so `p + 2 = q²`
  qualifies: in the semiprime alternative the factors are counted **with multiplicity**
  (`Ω(p + 2) = 2`), and in the prime alternative `Ω(p + 2) = 1`.
* **No priority claim.** The mathematics is Chen's (1973); this corpus claims only a
  machine-checked formalization of it, and the anchor papers' own surveyed as-of language governs.
* **Not the `Ω`-corollary.** Pi :324 pins the *distinct* declaration
  `Salt.Fulcrum.chen_omega_prod_le_three`; that is **Part 2 below**, `cert_chen_omega`,
  a separate theorem — `cert_chen` alone does not state it.
* **Nothing about effectivity.** No `p` is exhibited and no density or counting bound is
  asserted; infinitude is all that is claimed.

---

# PART 2 — `cert_chen_omega`, the `Ω`-corollary (the Pi paper's pinned form)

## WHAT THE THEOREM SAYS, in one sentence
**There are infinitely many primes `p` such that `p·(p + 2)` has at most three prime
factors, counted with multiplicity.**

## THE VOCABULARY, unfolded
The landed statement is `{p | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite`. Two
pieces of vocabulary, both unfolded in the certificate:

* **`Ω` = `ArithmeticFunction.cardFactors`** — the number of prime factors **with
  multiplicity** (`Ω 12 = 3`, since `12 = 2·2·3`), as opposed to `ω`, the number of
  *distinct* primes (`ω 12 = 2`). It is an `ArithmeticFunction` applied by coercion, which
  is the notational obstacle for a reader. `cert_chen_omega` states it as
  **`(p * (p + 2)).primeFactorsList.length ≤ 3`**: `Nat.primeFactorsList m` is the
  literal list of prime factors of `m` repeated to multiplicity (`12 ↦ [2, 2, 3]`; empty
  for `m = 0` and `m = 1`), so the claim is that this list has length at most three. The
  bridge is mathlib's `ArithmeticFunction.cardFactors_apply`.
* **`Set.Infinite`** — again exactly *the set of such `p` is not finite*.

*Where the three factors go:* `p` is prime and contributes one, so the bound's arithmetic
content is `Ω(p + 2) ≤ 2`. **That step is a reader's gloss, not part of this statement** —
it uses complete additivity of `Ω`, and it lives inside the landed proof.

## DIRECTION (rule 3)
`cert_chen_omega` is the **same set, hence the same proposition** as
`Salt.Fulcrum.chen_omega_prod_le_three`, with `Ω` rewritten to the prime-factor list's
length. Proved from that landed declaration by rewriting along the proved set equality.
**No generality traded** relative to the declaration it certifies.

## HYPOTHESES
**None; unconditional.** `chen_omega_prod_le_three` takes no binders, and its only corpus
input is `chen_headline` (`chen_headline.mono`, `Salt/Fulcrum/ChenCorollary.lean:35`; the
rest of its proof is mathlib arithmetic), which is itself unconditional. The axiom residue
below is the whole of what it rests on.

## WHAT `cert_chen_omega` DOES **NOT** CLAIM
* **Not equivalent to `cert_chen`, as far as this file says.** The landed corollary is
  proved by a **superset transport** (`Set.Infinite.mono`): every `p` of Part 1 satisfies
  the `Ω` bound, so the `Ω` set is at least as large. **No converse is proved here and
  none is asserted** — this file does not claim the two sets coincide.
* **Not a bound on `p + 2` in the statement.** The bound is on the *product* `p·(p + 2)`;
  reading it as a statement about `p + 2` requires the extra step `Ω(p) = 1` noted above,
  which is inside the landed proof, not inside this statement.
* **Nothing about twin primes**, and **no priority claim** — both carry over from Part 1
  unchanged.

## AXIOMS
```
'Salt.Certs.cert_chen'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Salt.Certs.cert_chen_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(the standard three each; `#print axioms` fires in-file, so the residue is re-checked on
every build of this module, not only at landing.)
-/

namespace Salt.Certs

open Salt.Chen Salt.Fulcrum ArithmeticFunction

/-- **THE CERTIFICATE.** There are infinitely many primes `p` such that `p + 2` is prime,
or is a product of two primes. Proved from `Salt.Chen.chen_headline` via the set equality
that unfolds `IsP2 2` — the same proposition, no generality traded. -/
theorem cert_chen :
    {p : ℕ | p.Prime ∧ ((p + 2).Prime ∨
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ p + 2 = q * r)}.Infinite := by
  have hset :
      {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}
        = {p : ℕ | p.Prime ∧ ((p + 2).Prime ∨
            ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ p + 2 = q * r)} := by
    ext p
    simp only [Set.mem_setOf_eq, IsP2]
    constructor
    · rintro ⟨hp, hq | ⟨q, r, hq, hr, hqr, -, -⟩⟩
      · exact ⟨hp, Or.inl hq⟩
      · exact ⟨hp, Or.inr ⟨q, r, hq, hr, hqr⟩⟩
    · rintro ⟨hp, hq | ⟨q, r, hq, hr, hqr⟩⟩
      · exact ⟨hp, Or.inl hq⟩
      · exact ⟨hp, Or.inr ⟨q, r, hq, hr, hqr, hq.two_le, hr.two_le⟩⟩
  rw [← hset]
  exact chen_headline

#print axioms cert_chen

/-- **THE CERTIFICATE, second declaration** (the form Pi :324 pins). There are infinitely
many primes `p` such that `p · (p + 2)` has at most three prime factors counted with
multiplicity — stated as the length of the prime-factor list, with `Ω` unfolded. Proved
from `Salt.Fulcrum.chen_omega_prod_le_three`; the same proposition, no generality traded. -/
theorem cert_chen_omega :
    {p : ℕ | p.Prime ∧ (p * (p + 2)).primeFactorsList.length ≤ 3}.Infinite := by
  have hset :
      {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}
        = {p : ℕ | p.Prime ∧ (p * (p + 2)).primeFactorsList.length ≤ 3} := by
    ext p
    simp only [Set.mem_setOf_eq, cardFactors_apply]
  rw [← hset]
  exact chen_omega_prod_le_three

#print axioms cert_chen_omega

end Salt.Certs
