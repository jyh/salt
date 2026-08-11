/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Vaughan

/-!
# COMPREHENSIBILITY CERTIFICATE — Vaughan's identity

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.LS.vaughan` (`Salt/LS/Vaughan.lean`).

## WHAT THE THEOREM SAYS, in one sentence
For any two truncation parameters `U, V ≥ 1` and any `n > V`, the von Mangoldt
function at `n` decomposes **exactly** into three finite divisor sums:

  `Λ n  =  TypeI  −  Cross  +  TypeII`

where each piece below is an ordinary `Finset` sum over divisors of `n`, with an
explicit size condition. Nothing is approximated and nothing is estimated: this
is an **identity**, an equation between two real numbers, for every admissible
`(U, V, n)`.

## THE VOCABULARY, unfolded
* `Λ = ArithmeticFunction.vonMangoldt` — `Λ m = Real.log p` when `m = p^k` for a
  prime `p` and `k ≥ 1`, and `Λ m = 0` otherwise.
* `μ = ArithmeticFunction.moebius` — `μ m = 0` if `m` has a squared prime factor,
  else `(-1)^(number of prime factors)`. Integer-valued; cast to `ℝ` throughout.
* `m.divisors` — the `Finset` of divisors of `m`; **empty when `m = 0`**.
* `∑ c ∈ (n / d).divisors, …` — the inner index runs over divisors of the
  quotient `n / d`, which is the same as running over `c` with `d * c ∣ n`.

## DIRECTION (rule 3)
`cert_vaughan` is an **equality**, proved from `Salt.LS.vaughan` by `exact`. It is
the landed statement with every notation unfolded and the three summands named —
**no generality is traded**, so this is not an implication and there is nothing
weaker about it.

## WHAT THIS CERTIFICATE DOES **NOT** CLAIM (rule 2, and the claim-language law)
* **Not a priority claim.** Vaughan's identity was **independently formalized
  earlier and publicly**: `Lambda_decomp` in FLDutchmann/lean-bombieri-vinogradov
  (`BV/Defs.lean`, sorry-free from 2026-03-20) and `vaughan_identity_finite`
  (2026-06-18). Ours landed 2026-07-11. This corpus claims **no first** here.
* **Not an estimate.** No bound on any piece is asserted; the analytic work of
  splitting `TypeI/TypeII` into usable ranges happens downstream.
* **Not unconditional in `n`.** The hypothesis `V < n` is load-carrying: it is
  what kills the degenerate term (see the source module's `Route` note).

## AXIOMS
`#print axioms Salt.Certs.cert_vaughan` ⇒ `[propext, Classical.choice, Quot.sound]`
(the standard three; recorded at the landing of this file).
-/

open Finset ArithmeticFunction

namespace Salt.Certs

variable (U V n : ℕ)

/-- **Type I.** The Möbius-weighted logarithm over the *small* divisors `d ≤ U`. -/
noncomputable def typeI : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ U),
    ((moebius d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- **Cross.** Both indices small: `d ≤ U` and `c ≤ V`. Subtracted. -/
noncomputable def cross : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ U),
    ∑ c ∈ (n / d).divisors.filter (fun c => c ≤ V),
      ((moebius d : ℤ) : ℝ) * vonMangoldt c

/-- **Type II.** Both indices large: `d > U` and `c > V`. Added. -/
noncomputable def typeII : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => U < d),
    ∑ c ∈ (n / d).divisors.filter (fun c => V < c),
      ((moebius d : ℤ) : ℝ) * vonMangoldt c

/-- **THE CERTIFICATE.** `Λ n = TypeI − Cross + TypeII`, exactly, for `U, V ≥ 1`
and `n > V`. Proved from `Salt.LS.vaughan`; an equality, no generality traded. -/
theorem cert_vaughan (hU : 1 ≤ U) (hV : 1 ≤ V) (hn : V < n) :
    vonMangoldt n = typeI U n - cross U V n + typeII U V n :=
  Salt.LS.vaughan hU hV hn

#print axioms cert_vaughan

end Salt.Certs
