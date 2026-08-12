/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.AnalyticLS
import Salt.LS.CharLS

/-!
# COMPREHENSIBILITY CERTIFICATE — the large sieve, analytic and character forms

**Anchor (row 8 of `docs/CERT-ANCHORS-0811.md`), Nature draft
`${SEAT_DIR}/briefs/2026-08-11-nature-draft-v0.md`** — named by path per M0, and pinned by
PHRASE because line numbers into that file have rotted once already:

* `:201` — *"no public artifact in any proof assistant proves … **the large sieve
  inequality** …"*
* `:205` — the adversary sentence: *"the two live external Bombieri–Vinogradov
  formalization projects **take Siegel–Walfisz and the large sieve as axioms**"*

**Landed declarations certified:** `Salt.LS.analytic_LS` (`Salt/LS/AnalyticLS.lean:58`)
and `Salt.LS.char_LS` (`Salt/LS/CharLS.lean:277`).

## What the second anchor makes this certificate about

The first anchor is an absence claim about the literature; **no Lean theorem can support
or refute it, and none here tries.** The second is different and it is the one that gives
this file its job: the adversaries *take the large sieve as an axiom*. **So the fact worth
certifying is not that a large-sieve-shaped statement exists here, but that it is PROVED,
with the constants written down.**

🔑 ***BOTH CERTIFICATES THEREFORE CARRY THEIR CONSTANTS IN THE STATEMENT — `δ⁻¹ + 13N`
and `Q² + 13N`, explicit numerals, no `O(·)` and no named constant.*** *An axiom can be
stated with any constant one likes; a proof cannot. The `13` is where the difference
between assuming and proving becomes visible to a reader.*

## Direction and scope

**Direction: SAME PROPOSITION** — `analytic_LS`'s `expSum` and `Spaced` are unfolded to
the exponential sum and the circle-separation condition they abbreviate, so nothing but
mathlib primitives remains; `char_LS` is already primitive and is restated verbatim.
Nothing is strengthened.

⚠️ **NOT CLAIMED.** These are the *inequalities*. Bombieri–Vinogradov itself is a
separate landed rung and is not certified here; nor is any statement about what other
projects do or do not assume — that is the anchor's sentence, not a theorem.

## Axioms

MEASURED at the landing (`#print axioms` below), not asserted.
-/

open Salt.LS

namespace Salt.Certs

/-- ⭐ **THE ANALYTIC LARGE SIEVE, FULLY UNFOLDED.** For points `α` that are `δ`-separated
on the circle `ℝ/ℤ` (with `0 < δ ≤ 1/2`), the squared exponential sums at those points
total at most `(δ⁻¹ + 13N)` times the coefficients' energy.

**Both opaque names are gone**: `expSum N a α` is written as `∑_{n<N} aₙ e(nα)`, and
`Spaced δ α` as the separation condition `δ ≤ dist₁ (α r) (α s)` for `r ≠ s`. -/
theorem cert_analytic_large_sieve {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : ∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖∑ n ∈ Finset.range N, a n * e (n * α r)‖ ^ 2
      ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 :=
  analytic_LS a hsp hδ hδ2

/-- ⛔ **RULE 6 — WITNESS KIND: NON-DEGENERACY** (declared per the council amendment of
2026-08-12; `saltworks/docs/cert-layer-design-0811.md`, rule 6).

**What this witness proves:** not merely that the spacing hypothesis is inhabited, but that
it is inhabited by a point where the hypothesis has CONTENT. *This is the amendment's exact
case, and the degenerate point is real rather than hypothetical: at `R = 1` the condition
`∀ r s, r ≠ s → …` holds vacuously — there is no pair to test — so a satisfiability witness
could discharge rule 6 while certifying nothing.* **The witness therefore uses `R = 2`: two
genuinely separated points `{0, 1/2}` at the extreme admissible `δ = 1/2`.**

*Recorded because the amendment postdates this file: the non-degeneracy reasoning was
already here, but the KIND was not declared, and "every cert must say what its witness
proves" is a claim about the docstring, not about the witness.* -/
example : ∃ (δ : ℝ) (α : Fin 2 → ℝ), (0 < δ) ∧ (δ ≤ 1/2) ∧
    (∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)) := by
  refine ⟨1/2, ![0, 1/2], by norm_num, le_refl _, ?_⟩
  intro r s hrs
  fin_cases r <;> fin_cases s <;> simp_all [dist₁, round_eq] <;> norm_num

open Classical in
/-- ⭐ **THE CHARACTER LARGE SIEVE.** Summing over moduli `q ≤ Q` and primitive characters
mod `q`, weighted by `q/φ(q)`, the squared character sums total at most `(Q² + 13N)` times
the coefficients' energy.

*Already primitive — restated verbatim so the constant `Q² + 13N` sits beside the analytic
form's `δ⁻¹ + 13N` where a reader can compare them.* -/
theorem cert_char_large_sieve {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
  char_LS hQ c

/-- **RULE 6 — WITNESS KIND: SATISFIABILITY** (declared per the 2026-08-12 amendment).

**What this witness proves:** that the single hypothesis `2 ≤ Q` is inhabited, at `Q = 2`.
*That is all it proves, and the amendment's point is to say so rather than let a reader
assume more.* Recorded even though it is trivial: **"obviously satisfiable" is the
judgement the rule exists to replace.**

⚠️ **AND A NON-DEGENERACY QUESTION I AM FLAGGING RATHER THAN ANSWERING.** The amendment
asks for a non-degenerate witness *where a degenerate one would leave the check vacuous*.
Here the binder is not inhabited only by degenerate points — `2 ≤ Q` admits every larger
`Q` — so satisfiability is the right control for the HYPOTHESIS. *But the CONCLUSION's
content at `Q = 2` depends on how many primitive characters exist for `q ≤ 2`, and **I have
not measured that**, so I state the question instead of ruling on it: if the primitive-
character sum is empty or near-empty at `Q = 2`, a reader would learn more from a witness
at a `Q` where several moduli contribute.* **This is a docstring question, not a soundness
one — `cert_char_large_sieve` holds for every `Q ≥ 2` either way.** -/
example : (2 : ℕ) ≤ 2 := le_refl 2

#print axioms cert_analytic_large_sieve
#print axioms cert_char_large_sieve

end Salt.Certs
