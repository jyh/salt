/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.FinA3c
import Salt.Chen.FinLed3

/-!
# Chen's theorem, unconditional

`chen_headline`: there are infinitely many primes `p` such that `p + 2` is
prime or a product of two primes.

The composition of the two terminal bundles:
* `hA3_bundle` (`Salt/Chen/FinA3c.lean`) — the A₃ switch side, closed at the
  operating point through the windowed Bombieri–Vinogradov chain;
* `hL_bundle` (`Salt/Chen/FinLed3.lean`) — the ledger side: the certified
  razor with the error bundle `≤ 1/200`;
via `chen_headline_of_A3_ledger` (`Salt/Chen/Headline4.lean`), which carries
the operating-point witnesses into `chen_of_hypotheses_W`
(`Salt/Chen/Assembly.lean`).

No `sorry`, no `native_decide`; axioms exactly
`[propext, Classical.choice, Quot.sound]` (audited in `Salt/Chen/All.lean`).
-/

namespace Salt.Chen

/-- **Chen's theorem** (unconditional): there are infinitely many primes `p`
with `p + 2` prime or a product of two primes. -/
theorem chen_headline : {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_A3_ledger hA3_bundle hL_bundle

end Salt.Chen
