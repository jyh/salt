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

## ⭐ THIS CERTIFIES THE **RE-CUT** STATEMENT (2026-08-11)
Writing the first version of this file surfaced that the landed theorem carried **two
hypotheses its proof never used** — `h1 : 1 ≤ A₀` (half of what Pi's PRE-RE-CUT
display called "the certified $A_0$ range", `8680167^:main.tex:645` verbatim) and
`ht : E oneWeight` (that display's "true ($E(\mathbf{1})$)" conjunct,
`8680167^:main.tex:646` verbatim) — both phrases were DROPPED from Pi in the
re-cut `8680167`; the quotes here are HISTORICAL, pinned to the pre-re-cut
revision, and correctly absent from today's `main.tex` —
so the kernel held **strictly more** than the statement said. That first cert stated the
theorem *as landed*, because rule 3 forbids a cert from strengthening: a stronger
statement cannot be proved from a weaker theorem by `exact`.

**The Captain ruled the re-cut at council** (ruling (a); amendment J6's flags-wording
guard read and spent), the two binders were dropped from
`sufficient_true_not_parityInv`, and **this certificate now certifies the stronger
form.** The barrier needs neither a lower bound on `A₀` nor truth of `E` at `oneWeight`.

*The theorem's NAME is unchanged, deliberately: strengthening preserves a name's meaning
— every citation written against the old statement is still true of the new one —
whereas weakening would have required a rename under the restatement law.*

## AXIOMS
`[propext, Classical.choice, Quot.sound]` — the standard three; verified at landing.
-/

namespace Salt.Certs

open Salt.Parity

/-- **THE CERTIFICATE.** On the certified window `0 < θ < 1/2`, `A₀ ≤ 2`: **no
predicate `E` on completions is both twin-sufficient and parity-invariant.**

Note what is *absent*: no lower bound on `A₀`, and no assumption that `E` holds at
`oneWeight`. The barrier does not need them. -/
theorem cert_parity_gap {θ A₀ : ℝ}
    (hθ_pos : 0 < θ) (hθ_half : θ < 1 / 2) (hA_hi : A₀ ≤ 2)
    {E : (ℕ → ℝ) → Prop}
    (hSuff : TwinSufficient θ A₀ E) :
    ¬ ParityInv θ A₀ E :=
  sufficient_true_not_parityInv hθ_pos hθ_half hA_hi hSuff

/-- **Rule-6 witness (kind: SATISFIABILITY — DEGENERATE ON THE `E` AXIS, DECLARED;
retrofitted at the 8/12 council amendment).** The packet is satisfiable at
`θ = 1/4`, `A₀ = 2`, `E := fun _ => False`: the degenerate `E` is vacuously
`TwinSufficient` because no completion satisfies it, so the sufficiency
implication never fires. This is the amendment's own case, stated rather than
papered over: **a NON-DEGENERATE witness — a substantive twin-sufficient `E` —
is NOT exhibited in this corpus**, and exhibiting one is research-adjacent
(near the sufficiency side of the conjecture itself). The certificate's force
is unaffected: it is a negative, holding for EVERY `E`, degenerate or not.
(Degenerate-`E` instantiation is landed corpus practice, not an invention of this
witness — see `Z_trivial_of_not_completion`, `Salt/Parity/Z.lean:125`, and its
escape at L1 `:457`.) AND THE WITNESS IS NOT CONTENT-FREE [math's mirror case,
10:39 — an UNDERclaim, corrected]: `ParityInv` at `E := fun _ => False` says
"no completion exists", so this example's NEGATIVE kernel-certifies that a
completion EXISTS at `(θ, A₀) = (1/4, 2)` — degenerate on the `E` axis exactly
as declared, substantive on the `a` axis. -/
example : ¬ ParityInv (1/4) 2 (fun _ => False) :=
  cert_parity_gap (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ h => h.elim)

#print axioms cert_parity_gap

end Salt.Certs
