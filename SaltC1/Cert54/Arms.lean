/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.Checks

/-!
# C1 — the `k = 54` certificate's red-first arms

Checks that must FAIL on a mutant and PASS on the real data, kept beside the certificate so they
run wherever it builds (the CI job names this module as a target; `All` does not import it). Each
arm is an `example` the kernel decides; none is a theorem the audit reports.

* FX1 (math's non-author read, 2026-10-15): a marginal term's `(a, c)` are tied to its
  coefficient's by `termKV`'s `encKey` equality, which is injective only on bounded digits — the
  bound is `validT`'s. `validT_old` is the text at `9950190b`
  (`git show 9950190b:SaltC1/Cert54/Checks.lean`, lines 135–137, the name changed and nothing
  else); `t0` is the real term 390 of `wsh0`; `tMut` is its non-injective twin
  `(a, c₁) ↦ (a + 64, c₁ − 1)`, the SAME key. The wave checks `(termKV t).2.2 && validT t`.

Nothing here bears on twin primes.
-/

namespace SaltC1.Cert54.Arms

/-- `validT` as frozen at `9950190b`: no digit bound. -/
def validT_old (t : WTerm) : Bool :=
  Nat.blt t.1 1236 && Nat.beq t.2.2.1.length 13 && Nat.beq t.2.2.2.length 13 && leL t.2.2.2 t.2.2.1

/-- The real term 390 of `wsh0`: `(i, a, c, j) = (390, 0, [1, 0, …], [1, 0, …])`, coefficient
key 64. -/
def t0 : WTerm := (390, 0, [1,0,0,0,0,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0,0])
/-- Its non-injective twin: `a + 64`, `c₁ − 1`; the same `encKey`. -/
def tMut : WTerm := (390, 64, [0,0,0,0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0,0,0,0])

-- the twin has the same key as the real term
example : encKey 64 [0,0,0,0,0,0,0,0,0,0,0,0,0] = encKey 0 [1,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
-- the mechanism, kept visible: the bare equality tie accepts BOTH
example : (termKV t0).2.2 = true := by decide +kernel
example : (termKV tMut).2.2 = true := by decide +kernel
-- the defect, red backwards: the frozen `validT` accepted the twin
example : validT_old tMut = true := by decide +kernel
-- the fix: `validT` rejects it, and the real term still passes (control)
example : validT tMut = false := by decide +kernel
example : validT t0 = true := by decide +kernel

end SaltC1.Cert54.Arms
