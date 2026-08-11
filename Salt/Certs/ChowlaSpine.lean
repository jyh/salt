/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal

/-!
# COMPREHENSIBILITY CERTIFICATE — log-Chowla, door-only (the single-hypothesis reduction)

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.Entropy.Chowla.log_chowla_two_door_only`
(`Salt/Entropy/Chowla/SpineFinal.lean:981`).
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
* **Not a priority claim.** The paper's priority language governs; this file asserts none.

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

end Salt.Certs
