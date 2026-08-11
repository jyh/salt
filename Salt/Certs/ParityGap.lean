/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Parity.Z

/-!
# COMPREHENSIBILITY CERTIFICATE — the gap theorem (parity barrier, with coordinates)

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.Parity.sufficient_true_not_parityInv`
(`Salt/Parity/Z.lean:670`). Paper: Theorem `thm:gap`.

## WHAT THE THEOREM SAYS, in one sentence
**No predicate on completions can be simultaneously parity-invariant and
twin-sufficient** — so a twin-prime proof cannot be built from a criterion that
cannot tell two completions apart.

## THE VOCABULARY, unfolded (all from `Salt/Parity/Z.lean`)
* A **completion** `a : ℕ → ℝ` at `(θ, A₀)` is a nonnegative weight sequence whose
  type-I error obeys `typeIError a θ x ≤ C · x / (log x)^A₀` for some `C > 0` and
  all `x ≥ 2`. *(`Completion`, `:61`.)*
* `ParityInv θ A₀ E` — `E` holds at **every** completion. *(`:68`.)* This is the
  formal sense of "cannot distinguish": a parity-invariant predicate is blind.
* `TwinSufficient θ A₀ E` — whenever `E` holds at a completion, that completion has
  **unbounded** twin mass: `∀ C, ∃ x, C < twinMass a x`. *(`:77`.)*
* `oneWeight = fun _ => 1`; `twinFree n = if n and n+2 are both prime then 0 else 1`.

## THE MECHANISM, in one line (why the theorem is true)
`twinFree` **is** a completion on the certified window, and its twin mass is
identically `0`. A parity-invariant `E` must therefore hold at `twinFree`, and
twin-sufficiency would then force `twinFree`'s twin mass above every bound —
contradicting `0`. **The witness is the twin-free completion; that is the whole proof.**

## DIRECTION (rule 3)
`cert_parity_gap` is the **same proposition** as the landed theorem, restated with
its binders named in plain terms, proved by `exact`. **No generality is traded.**

## ⚠️ TWO HYPOTHESES ARE CARRIED BUT **NOT USED** — reported, not altered
The landed proof opens by discharging two binders as deliberately frozen:
```
have _ := h1  -- frozen hypothesis (amendment J6); unused in the proof
have _ := ht  -- frozen hypothesis; the gap uses ParityInv, not `E oneWeight`
```
* `h1 : 1 ≤ A₀` — **half of what the paper calls "the certified `A₀` range"**
  (Appendix A decodes that phrase as `h1 ∧ h2`, i.e. `1 ≤ A₀ ≤ 2`). Only `h2` is used.
* `ht : E oneWeight` — **the paper's "true (`E(𝟏}`)" conjunct.** Unused.

⇒ ***The landed result is therefore STRICTLY STRONGER than the statement it is
written as: it holds without `1 ≤ A₀` and without `E oneWeight`.*** This certificate
states the theorem **as landed** (rule 3 forbids strengthening: a stronger cert cannot
be proved from a weaker theorem by `exact`). **Whether to drop the frozen binders is a
statement decision and belongs to the design desk under iron rule 1 — flagged here, not
taken.** *A reader of the paper should know that two of the four stated conditions are
not load-bearing in the proof.*

## AXIOMS
`[propext, Classical.choice, Quot.sound]` — the standard three; verified at landing.
-/

namespace Salt.Certs

open Salt.Parity

/-- **THE CERTIFICATE.** On the certified window, no predicate `E` on completions is
at once true at `𝟏`, twin-sufficient, and parity-invariant.

`hA_lo` and `hE_one` are carried because the landed statement carries them; **neither
is used by the proof** — see the module docstring. -/
theorem cert_parity_gap {θ A₀ : ℝ}
    (hθ_pos : 0 < θ) (hθ_half : θ < 1 / 2)
    (hA_lo : 1 ≤ A₀) (hA_hi : A₀ ≤ 2)
    {E : (ℕ → ℝ) → Prop}
    (hSuff : TwinSufficient θ A₀ E) (hE_one : E oneWeight) :
    ¬ ParityInv θ A₀ E :=
  sufficient_true_not_parityInv hθ_pos hθ_half hA_lo hA_hi hSuff hE_one

#print axioms cert_parity_gap

end Salt.Certs
