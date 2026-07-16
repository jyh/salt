/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Ledger3

/-!
# Chen's second theorem (the Goldbach form), unconditional

`chen_goldbach`: every sufficiently large even number is the sum of a prime
and a `P₂` — a prime or a product of two primes.

The composition of the terminal reduction with the ledger bundle:
* `chen_goldbach_of_ledger` (`Salt/Goldbach/Asm6.lean`) — the frozen D0
  statement from ONE analytic bundle, all structural wiring (the three main
  bundles `gold_hA1/hA2/hA3_bundle`, the residue witness `gold_op_residue`,
  the tower rows, the survivor extraction) discharged;
* `gold_hL_bundle` (`Salt/Goldbach/Ledger3.lean`) — that bundle: the
  certified razor `normalized_package` at the punctured Goldbach carriers
  `M1G`/`M2G`/`M3G`, uniformly in the admissible residue, with the error
  bundle `≤ 1/200` (Ledger parts 1–3).

The sieve carriers are punctured at the primes dividing `N` (the Goldbach
singular series); the twin machinery transfers through the `W`-comparison
(`gold_W_ge_twin`), the punctured `W`-ratio (`gold_hWy_at_op`), and the
crumb/count seams — no equidistribution crumb is needed on the count side
(`gold_hcount_seam`).

No `sorry`, no `native_decide`; axioms exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open Salt.Chen

namespace Salt.Goldbach

/-- **Chen's second theorem** (unconditional, the Goldbach form): every
sufficiently large even `N` is the sum `N = p + q` of a prime `p` and a `P₂`
number `q` (a prime, or a product of two primes each `≥ 2`). -/
theorem chen_goldbach : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ IsP2 2 q :=
  chen_goldbach_of_ledger gold_hL_bundle

end Salt.Goldbach
