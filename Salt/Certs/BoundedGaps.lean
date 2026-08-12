/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Gate

/-!
# COMPREHENSIBILITY CERTIFICATE — unconditional bounded prime gaps

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.SW.bounded_gaps_unconditional` (`Salt/SW/Gate.lean:376`).
Paper anchor (`docs/CERT-ANCHORS-0811.md`, row 4): **Nature draft :239** — *"unconditional
bounded prime gaps on day 8"*. **No Pi anchor**: the Pi flagship never states this claim.

## WHAT THE THEOREM SAYS, in one sentence
**There is a single finite bound `C` such that, no matter how far out along the number
line you go, you can still find two different primes beyond that point whose difference
is at most `C`** — equivalently, infinitely many pairs of distinct primes lie within `C`
of each other.

## THE VOCABULARY, unfolded
* The landed statement writes the gap as an interval membership,
  `(q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ)`, which is exactly
  `-C ≤ q - p ≤ C`, i.e. `|q - p| ≤ C`. Because the pair is unordered there
  (`p ≠ q` only), the two-sided interval is doing the work of an absolute value.
* This certificate **orders the pair** (`p < q`) instead. That removes the integer
  casts and the interval entirely: the gap is plain `Nat` subtraction, `q - p ≤ C`,
  unambiguous because `p < q`. Distinctness is then visible in the statement rather
  than asserted as `p ≠ q`.
* *"Infinitely many"* is rendered the standard way, as *"beyond every threshold"*:
  `∀ N, ∃ p q, N < p ∧ p < q ∧ …` (the certificate writes `N < p` and `p < q`, which
  gives `N < q` as well). `cert_bounded_gaps_infinitely_many` makes the word literal in
  set vocabulary: the set of primes having a prime partner within `C` above them is
  `Set.Infinite`.
* No corpus-internal definition survives into the certificate: apart from the logical
  connectives `∃ ∀ ∧`, everything in `cert_bounded_gaps` is `Nat`, `<`, `-`, `≤`, and
  `Nat.Prime` — no `Salt.*` name, no `Set.Icc`, no `ℤ` cast.

## DIRECTION (rule 3)
`cert_bounded_gaps` is an **implication, cert ← landed theorem**: it is proved *from*
`Salt.SW.bounded_gaps_unconditional`.

**Nothing is traded, and that is kernel-proved, not asserted.** `cert_bounded_gaps_iff`
states the **pointwise equivalence** of the two statement bodies — for every `C` and
every `N`, the landed matrix (unordered pair, `p ≠ q`, `Set.Icc` on `ℤ`) and the
certificate matrix (ordered pair, `Nat` subtraction) are the same proposition. So the
readability change is a change of notation only, checked by the kernel. The literal
`Set.Infinite` rendering is likewise kernel-tied, by
`cert_bounded_gaps_infinitely_many_iff`: for each `C` the set form and the
threshold form are equivalent. **Both equivalences are proved, not asserted.**

## HYPOTHESES — **there are none**
`Salt.SW.bounded_gaps_unconditional` takes **no arguments and no hypotheses**: it is a
closed proposition, and so is this certificate. Nothing analytic is assumed. In
particular the Siegel–Walfisz input the Bombieri–Vinogradov chain needs is *discharged
inside the corpus* (`Salt.SW.siegelWalfisz_holds`), not assumed here — the
hypothesis-carrying form is the separate declaration
`Salt.BV.bounded_gaps_of_siegelWalfisz (hSW : SiegelWalfisz)`, and this certificate does
not stand on it. **Unconditional means unconditional: zero binders.**

## WHAT THIS CERTIFICATE DOES **NOT** CLAIM (rule 2)
* **No numeric value for `C`.** The statement is `∃ C`. This file does not extract,
  bound, or estimate the gap — it says nothing about 246, 12, or 2. The corpus's
  explicit `≤ 12` results are *different declarations that carry hypotheses*
  (`Salt.Twelve.gaps_le_twelve_of_hasLevel : WindowPNT → HasLevel (3999/4000) → …`).
* **Not the twin prime conjecture.** `C` is not claimed to be 2, and **no route from
  this proposition to `TwinPrimeConjecture` is claimed here** — in this corpus that
  conjecture is a *definition* (`Salt/Basic.lean:25`), not a theorem.
* **No adjacency claim.** `p` and `q` are two distinct primes within `C`; they are *not*
  claimed to be consecutive primes, and nothing is claimed about the primes between them.
* **No effectivity claim.** Whether a particular `C` can be read off is a property of the
  proof, not of this proposition; this file asserts nothing either way.
* **No priority language.** The mathematics is classical (Zhang; Maynard–Tao); the Nature draft — this cert's one anchor —
  makes its own claims under its surveyed as-of form, and **this certificate claims
  nothing about priority, novelty, or firsts** — its whole content is: this proposition
  is proved, from nothing.

## AXIOMS
`#print axioms Salt.Certs.cert_bounded_gaps` ⇒
`'Salt.Certs.cert_bounded_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]`
(the standard three; recorded at the landing of this file). Same residue for the three
companions `cert_bounded_gaps_iff`, `cert_bounded_gaps_infinitely_many_iff`, and
`cert_bounded_gaps_infinitely_many`.
-/

namespace Salt.Certs

/-- **THE NO-TRADE CHECK.** For every bound `C` and every threshold `N`, the landed
theorem's body and the certificate's body are the *same proposition*: an unordered pair
of distinct primes above `N` with `(q : ℤ) - p` in `[-C, C]` exists **iff** an ordered
pair `N < p < q` of primes with `q - p ≤ C` (`Nat` subtraction) exists. This is what
licenses the phrase "no generality is traded" in the header. -/
theorem cert_bounded_gaps_iff (C N : ℕ) :
    (∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
        (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ))
      ↔ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧ q - p ≤ C) := by
  constructor
  · rintro ⟨p, q, hNp, hNq, hne, hp, hq, hmem⟩
    rw [Set.mem_Icc] at hmem
    obtain ⟨hlo, hhi⟩ := hmem
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨p, q, hp, hq, hNp, h, by omega⟩
    · exact ⟨q, p, hq, hp, hNq, h, by omega⟩
  · rintro ⟨p, q, hp, hq, hNp, hpq, hgap⟩
    refine ⟨p, q, hNp, by omega, by omega, hp, hq, ?_⟩
    rw [Set.mem_Icc]
    omega

/-- **THE CERTIFICATE — unconditional bounded prime gaps.**
There is a bound `C` such that for every `N` there are primes `p` and `q` with
`N < p < q` and `q - p ≤ C`: infinitely many pairs of distinct primes lie within `C`
of each other. **No hypotheses.** Proved from `Salt.SW.bounded_gaps_unconditional`
through the pointwise equivalence `cert_bounded_gaps_iff`. -/
theorem cert_bounded_gaps :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧ q - p ≤ C := by
  obtain ⟨C, hC⟩ := Salt.SW.bounded_gaps_unconditional
  exact ⟨C, fun N => (cert_bounded_gaps_iff C N).mp (hC N)⟩

/-- **THE SECOND NO-TRADE CHECK.** For each bound `C`, the set form and the threshold
form say the same thing: the set of primes owning a prime partner within `C` above is
infinite **iff** such a pair exists beyond every threshold. (An infinite set of naturals
is unbounded — `Set.infinite_iff_exists_gt`.) The set form records only the *smaller*
member of each pair, and this iff is why that costs nothing. -/
theorem cert_bounded_gaps_infinitely_many_iff (C : ℕ) :
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p < q ∧ q - p ≤ C}.Infinite
      ↔ ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧ q - p ≤ C := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, ⟨hp, q, hq, hpq, hgap⟩, hNp⟩ := h N
    exact ⟨p, q, hp, hq, hNp, hpq, hgap⟩
  · intro h N
    obtain ⟨p, q, hp, hq, hNp, hpq, hgap⟩ := h N
    exact ⟨p, ⟨hp, q, hq, hpq, hgap⟩, hNp⟩

/-- **"INFINITELY MANY", literally.** There is a bound `C` such that the set of primes
`p` admitting a larger prime `q` with `q - p ≤ C` is **infinite**. Equivalent to
`cert_bounded_gaps` bound-for-bound (`cert_bounded_gaps_infinitely_many_iff`). -/
theorem cert_bounded_gaps_infinitely_many :
    ∃ C : ℕ, {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p < q ∧ q - p ≤ C}.Infinite := by
  obtain ⟨C, hC⟩ := cert_bounded_gaps
  exact ⟨C, (cert_bounded_gaps_infinitely_many_iff C).mpr hC⟩

#print axioms cert_bounded_gaps_iff
#print axioms cert_bounded_gaps
#print axioms cert_bounded_gaps_infinitely_many_iff
#print axioms cert_bounded_gaps_infinitely_many

end Salt.Certs
