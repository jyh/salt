/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal

/-!
# COMPREHENSIBILITY CERTIFICATE — log-Chowla: BOTH declarations under `thm:spine`

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorems certified — **`thm:spine` names TWO declarations under one label, and
this file covers BOTH**:
* `Salt.Entropy.Chowla.log_chowla_two_door_only` (`SpineFinal.lean:981`) — the reduction.
* `Salt.Entropy.Chowla.log_chowla_two_budget_head` (`SpineFinal.lean:750`) — the
  ∀-quantified head, the second sentence of Pi's `thm:spine`.

⚠️ *The first version of this file certified only the reduction. **Evidence's adequacy arm
caught the gap** — a certificate must state no less than its anchor quotes, and the anchor
is the whole theorem. This is the "one paper phrase, several declarations" shape recorded
as row 11's hazard in `docs/CERT-ANCHORS-0811.md`; it turned out to apply here too.*
**Anchor** (`docs/CERT-ANCHORS-0811.md`, row 12): Pi `thm:spine` — *"a single
hypothesis … implies the logarithmic two-point Chowla statement at `R`"*.

## WHAT THE THEOREM SAYS, in one sentence
**One hypothesis — and nothing else — yields the logarithmic two-point Chowla bound.**
The landed statement names that hypothesis `MRTUniformity` and names its conclusion
`¬ logChowla2Fails`; **both names are opaque, and unfolding them IS this certificate.**

## THE HYPOTHESIS, unfolded (`MRTDoor.lean:48`)
`MRTUniformity R δ` says:
> for **every** window length `H` in the regime's range (`R.Hlo ≤ H ≤ R.Hhi`) and
> **every** real `α`, the logarithmically-averaged `L¹` mass of the window exponential
> sum is at most `δ · H`:
> `∫ n, ‖windowExpSum H n α‖ ∂(logMeasure R.x R.ω) ≤ δ * H`.

*In words: short exponential sums are small on log-average, **uniformly in the frequency
`α`.** This is the Matomäki–Radziwiłł–Tao door — the one input the reduction consumes.*

## THE CONCLUSION, unfolded (`ChowlaFailure.lean:59`)
`logChowla2Fails ε x ω` is the **failure** predicate
`ε · log ω < |∑_{n ∈ (x/ω, x]} λ(n)·λ(n+1) / n|`.
So `¬ logChowla2Fails` is the Chowla bound itself:
> `|∑_{n ∈ (x/ω, x]} λ(n)·λ(n+1) / n| ≤ ε · log ω`,
with `λ = ArithmeticFunction.liouville`. **Note the shift is `n+1`** (the two-point
correlation `λ(n)λ(n+1)`), not `n+2`.

## DIRECTION (rule 3)
`cert_log_chowla_door_only` is the **same proposition** as the landed theorem, with the
two opaque predicates replaced by their definitions at the statement. Proved by `exact`;
**no generality traded.**

## WHAT THIS CERTIFICATE DOES **NOT** CLAIM
* **Not a proof of Chowla.** `MRTUniformity` is a *hypothesis*: this is a **reduction**,
  and the door is not discharged here or anywhere in the corpus.
* **Not a claim that the regime `R` is unique or optimal** — `R` is existentially bound,
  as is `δ₀`. The companion `log_chowla_two_budget_head` supplies the `∀`-quantified head
  that places the regime floor above a prescribed threshold; that is a *different* theorem.
* **Not a priority claim.** Pi's priority language (surveyed as-of form) governs; this file asserts none.

## AXIOMS
`[propext, Classical.choice, Quot.sound]` — the standard three; verified at landing.
-/

namespace Salt.Certs

open Salt.Entropy.Chowla

/-- **THE CERTIFICATE — the reduction, with both opaque names unfolded in place.**
There are `δ₀ > 0` and a regime `R` such that for every `0 < δ ≤ δ₀`: **if** every window
length `H ∈ [R.Hlo, R.Hhi]` and every frequency `α` satisfy the log-averaged bound
`∫ ‖windowExpSum H n α‖ ≤ δ·H`, **then** the two-point Liouville correlation obeys
`|∑_{n ∈ (x/ω, x]} λ(n)λ(n+1)/n| ≤ ε·log ω`. -/
theorem cert_log_chowla_door_only :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            (∫ n, ‖windowExpSum H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)) →
        ¬ ((R.eps : ℝ) * Real.log (R.ω : ℝ) <
            |∑ n ∈ Finset.Ioc (R.x / R.ω) R.x,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) / (n : ℝ)|) :=
  log_chowla_two_door_only

#print axioms cert_log_chowla_door_only

/-! ## The second declaration under `thm:spine` — the ∀-quantified head

The second sentence of Pi's `thm:spine`: *"A `∀`-quantified head version places the regime floor above
any prescribed threshold."* That is `log_chowla_two_budget_head`, and it differs from the
reduction in three ways a reader should see:

1. **`ε` and `δ₀` are fixed FIRST**, before the regime — so they are uniform across every
   floor, not chosen per regime.
2. **For EVERY prescribed `extraFloor : ℕ` there is a regime `R` with
   `extraFloor ≤ R.Hlo`** — this is the "floor above any threshold" clause, and it is why
   the head version is stronger than picking one regime.
3. **It consumes the Ξ-RESTRICTED door `MRTUniformityXi`, not the full `∀ α` door.** The
   restricted door quantifies only over frequencies `ξ ∈ bigXi R.eps H` at
   `α = −ξ/H`, so it is a **weaker hypothesis** — and a weaker hypothesis makes the
   theorem **stronger**. (`mrtUniformity_implies_xi` is the landed bridge.)
-/

/-- **THE CERTIFICATE, second declaration.** Fixed `ε > 0` and `δ₀ > 0` such that for
**every** prescribed floor there is a regime whose window floor exceeds it, and on which
the Ξ-restricted uniformity door still yields the two-point Chowla bound. -/
theorem cert_log_chowla_budget_head :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ ξ ∈ bigXi R.eps H,
              (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
                ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)) →
          ¬ ((R.eps : ℝ) * Real.log (R.ω : ℝ) <
              |∑ n ∈ Finset.Ioc (R.x / R.ω) R.x,
                (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + 1) : ℝ) / (n : ℝ)|) :=
  log_chowla_two_budget_head

#print axioms cert_log_chowla_budget_head

end Salt.Certs
