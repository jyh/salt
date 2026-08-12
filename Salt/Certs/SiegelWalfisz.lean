/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Gate

/-!
# COMPREHENSIBILITY CERTIFICATE — Siegel–Walfisz, unconditional

**Anchor (row 7 of `docs/CERT-ANCHORS-0811.md`), and it lands in BOTH papers** — named
by path per M0, because this house has more than one:

* **Nature draft**, `${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md:200` — the
  surveyed-strength list: *"no public artifact in any proof assistant proves **the
  Siegel–Walfisz theorem**, …"*
* **Pi flagship**, `papers/flagship/main.tex:322` — *"Around these sit **an
  unconditional Siegel–Walfisz theorem**, …"* (prose; no `\label`, so quoted by line).

**Landed declaration certified:** `Salt.SW.siegelWalfisz_holds`
(`Salt/SW/Gate.lean:150`).

## What this certificate is for: the landed statement is TWO opaque names deep

The theorem reads, in full, `siegelWalfisz_holds : Salt.BV.SiegelWalfisz`. **A reader
learns nothing from it.** And unfolding once is not enough: `SiegelWalfisz` is stated in
terms of `psiAP`, which is itself a definition. So this certificate unfolds **both**, and
the statement below is the theorem in primitive vocabulary only — a von Mangoldt sum over
an arithmetic progression, compared with `x/φ(q)`.

🔑 ***IT CLOSES BY `exact`, WHICH IS THE POINT: a fully-unfolded restatement that
type-checks against the landed name is DEFINITIONALLY the same proposition — not
"faithful in my judgement". The kernel certifies the paraphrase.***

## Direction and scope

**Direction: SAME PROPOSITION** (unfold-in-place, nothing traded).

⚠️ **WHAT THIS CERTIFICATE DOES NOT CLAIM.** The anchoring Nature sentence is a claim
about the LITERATURE as of a survey date; **no Lean theorem can support or refute it**,
and none here tries. This file certifies the mathematical half: that the corpus proves
the statement, unconditionally, with no hypothesis of its own.

📌 **AND A STALENESS FOUND BY WRITING THIS DOWN — reported at its true size, not larger.**
`Salt/BV/Defs.lean:31-34`, the docstring of `SiegelWalfisz` itself, still reads *"The
single assumed analytic input of this rung (absent from every Lean artifact as of 2026-07;
**supplied by future formalization or upstream**)"*. The last clause is **stale**: it is
supplied HERE, in this repo, by `siegelWalfisz_holds`.
*The rest of that docstring is fine and should not be swept: `SiegelWalfisz` legitimately
remains a HYPOTHESIS in parameterised consumers (`hSW : SiegelWalfisz` appears across
`Salt/BV/**`), which is ordinary — a proved proposition may still be quantified over. **The
defect is one clause about PROVENANCE, not the predicate's role.*** Not fixed here: it is
another module's docstring, and a cert file is not the place to edit its dependency.

## Axioms

MEASURED at the landing, not asserted (`#print axioms` below).
-/

open ArithmeticFunction

namespace Salt.Certs

/-- ⭐ **SIEGEL–WALFISZ, FULLY UNFOLDED.** For every saving exponent `A` and every
modulus range exponent `C`, there is a constant `K ≥ 0` such that for all `x ≥ 2`, all
moduli `q` with `q ≤ (log x)^C`, and all residues `a` coprime to `q`:

the von Mangoldt sum over `{n ≤ x : n ≡ a (mod q)}` differs from `x/φ(q)` by at most
`K·x/(log x)^A`.

**Both opaque names are gone**: `SiegelWalfisz` is unfolded to its quantifier structure,
and `psiAP` to the sum it abbreviates. Nothing but mathlib primitives remains. -/
theorem cert_siegel_walfisz :
    ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 ≤ K ∧ ∀ x q a : ℕ, 2 ≤ x →
      0 < q → ((q : ℝ) ≤ (Real.log x) ^ C) → Nat.Coprime a q →
      |(∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q), vonMangoldt n)
          - (x : ℝ) / q.totient|
        ≤ K * x / (Real.log x) ^ A :=
  Salt.SW.siegelWalfisz_holds

/-! ### Rule 6 — EXEMPT, stated rather than assumed

`cert_siegel_walfisz` carries **no hypotheses**: its type is a closed proposition, which
the signature above shows directly. A closed false proposition cannot be proved at all,
so a satisfiability witness would certify nothing. *The vacuity control exists for
hypothesis-carrying certs, where contradictory hypotheses give a green build over an
empty claim; that failure mode is unreachable here.*

📌 *An earlier draft of this file discharged the point with a THEOREM —
`cert_siegel_walfisz_is_unconditional`, stating the identical proposition and proved by
`cert_siegel_walfisz`. **It certified nothing its predecessor had not**, which is the
vacuity trap wearing the opposite face: not contradictory hypotheses, but a redundant
conclusion. Deleted before landing. **The type already says it; a theorem that restates a
type is decoration with an axiom line.*** -/

#print axioms cert_siegel_walfisz

end Salt.Certs
