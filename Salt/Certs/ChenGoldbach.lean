/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.ChenGoldbach

/-!
# COMPREHENSIBILITY CERTIFICATE — Chen's theorem, the GOLDBACH half

**Anchor (row 6 of `docs/CERT-ANCHORS-0811.md`).** Nature draft,
`${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md:202` — the class enumeration naming
*"Chen's theorem"*. Named by path per M0.

**Landed declaration certified:** `Salt.Goldbach.chen_goldbach`
(`Salt/Goldbach/ChenGoldbach.lean:41`).

## ⛔ WHY THIS FILE EXISTS SEPARATELY FROM `Salt/Certs/Chen.lean`

The paper's phrase *"Chen's theorem"* covers **two theorems**, and the corpus proves them
as **two declarations**:

* the **twin** half — infinitely many primes `p` with `p + 2` a `P₂` — certified in
  `Salt/Certs/Chen.lean` as `cert_chen`;
* the **Goldbach** half — every sufficiently large even `N` is `prime + P₂` — certified
  **here**.

🔑 ***THIS IS THE "ONE PAPER PHRASE, SEVERAL DECLARATIONS" HAZARD, AND IT WAS CAUGHT BY THE
CORPUS BEFORE IT WAS CAUGHT BY A CERTIFICATE:*** `Chen.lean:90` already states in words that
the Goldbach half is *"the separate declaration `chen_goldbach`, row 6 of the anchor table,
**not this file**"*. **A certificate must state no less than its anchor quotes**, and one
file covering one half of a two-half phrase would have left the row half-certified while
looking complete.

## Direction and scope

**Direction: SAME PROPOSITION.** `IsP2 2 q` is replaced by its definition with the two
size decorations dropped, and `cert_chen_goldbach_isP2_iff` **proves** that this trades
nothing — see below. Nothing is strengthened and nothing is weakened.

📏 **THE `z = 2` DECORATIONS, DISCHARGED RATHER THAN ASSERTED.** `IsP2 z m`
(`Salt/Chen/WeightTrivia.lean:270`) is *"`m` is prime, or a semiprime both of whose factors
are `≥ z`"*. The landed instance is `IsP2 2 q`, and at `z = 2` the clauses `2 ≤ r`, `2 ≤ s`
carry **no information**: every prime is `≥ 2` (`Nat.Prime.two_le`), so they are *recoverable*
from the primality conjuncts standing beside them. *This certificate does not merely say so —
`cert_chen_goldbach_isP2_iff` establishes the biconditional, and the reverse direction is
exactly where the decorations are rebuilt.* **The plain disjunction is the landed statement,
not a weakening of it** — the same treatment, and for the same reason, that `cert_chen` gives
the twin half.

⚠️ **WHAT THIS CERTIFICATE DOES NOT CLAIM.** The two prime factors need **not** be distinct
(`r = s` is permitted, so `q = r²` qualifies). `N₀` is existentially bound: no explicit
threshold is asserted, and none is extracted here. And the anchoring Nature sentence is a
claim about the LITERATURE as of a survey date; **no Lean theorem can support or refute it**,
and none here tries.

## Axioms

MEASURED at the landing (`#print axioms` below), not asserted.
-/

open Salt.Chen Salt.Goldbach

namespace Salt.Certs

/-- **THE `P₂` PREDICATE AT `z = 2`, UNFOLDED — and the proof that the size decorations
are free.** `IsP2 2 q` says *`q` is prime, or a product of two primes each `≥ 2`*; the
`≥ 2` clauses are recoverable from primality, so the plain disjunction is the **same**
proposition.

*This is the file's no-trade evidence: the certificate below drops the decorations, and
this biconditional is why that is a restatement rather than a weakening.* -/
theorem cert_chen_goldbach_isP2_iff (q : ℕ) :
    IsP2 2 q ↔ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) := by
  constructor
  · rintro (hq | ⟨r, s, hr, hs, hqrs, _, _⟩)
    · exact Or.inl hq
    · exact Or.inr ⟨r, s, hr, hs, hqrs⟩
  · rintro (hq | ⟨r, s, hr, hs, hqrs⟩)
    · exact Or.inl hq
    · exact Or.inr ⟨r, s, hr, hs, hqrs, hr.two_le, hs.two_le⟩

/-- ⭐ **CHEN'S SECOND THEOREM, FULLY UNFOLDED.** There is a threshold `N₀` such that every
even `N ≥ N₀` splits as `N = p + q` with `p` prime and `q` **either prime or a product of
two primes**.

**The opaque name is gone**: `IsP2 2` is written out, and by
`cert_chen_goldbach_isP2_iff` the omitted `≥ 2` decorations cost nothing. -/
theorem cert_chen_goldbach :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧
        (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) := by
  obtain ⟨N₀, h⟩ := chen_goldbach
  refine ⟨N₀, fun N hN hEven => ?_⟩
  obtain ⟨p, q, hsum, hp, hq⟩ := h N hN hEven
  exact ⟨p, q, hsum, hp, (cert_chen_goldbach_isP2_iff q).mp hq⟩

/-! ### Rule 6 — WITNESS KIND: EXEMPT (no hypotheses)

*Declared per the 2026-08-12 council amendment: "not every cert needs a deep witness; every
cert must say what its witness proves."*

`cert_chen_goldbach` is a **closed proposition** — the signature above carries no
hypotheses, which is defensible from the statement alone without reading this paragraph.
A closed false proposition cannot be proved at all, so a satisfiability witness would
certify nothing, and there is no binder for a degenerate point to hide in.

📌 *`cert_chen_goldbach_isP2_iff` takes `(q : ℕ)` — **data, not a hypothesis.** Every `q`
is admissible, so it is exempt for the same reason: nothing to satisfy. Recorded because
"it only takes a natural number" is precisely the judgement rule 6 exists to replace.* -/

#print axioms cert_chen_goldbach_isP2_iff
#print axioms cert_chen_goldbach

end Salt.Certs
