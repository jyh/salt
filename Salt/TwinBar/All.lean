/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Defs
import Salt.TwinBar.LogWeight
import Salt.Tactic.AuditAxioms

/-!
# The twin-bar rung (`twinbar`) — aggregate import

Design: `docs/blueprints/twinbar.md`. The flagship NEGATIVE result: for the twin
tuple `{0, 2}` (`k = 2`) the unmodified Maynard–Selberg variational gate
`θ·(J₁+J₂) > 2·I₂` is unsatisfiable by ANY continuous weight at ANY level of
distribution `θ ≤ 1`, because `J₁ F + J₂ F ≤ 2·log 2·I₂ F` with `2·log 2 < 2`
(Polymath8b arXiv:1407.4897, Lemma 6.1 + Cor. 6.4 at `k = 2`). Wired into
`Salt.lean` from the first commit; extended as the analytic nodes (T2–T6) land.

**The honesty contract (read before quoting the theorem).** The headliners H1/H2
(`twin_bar`, `twin_gate_fails`) and the impossibility H3 (`no_twin_weight`)
certify the exact boundary of the UNMODIFIED Maynard class: no continuous weight
`F`, at no equidistribution level `θ ≤ 1`, can push the Selberg functional past
the twin gate. This is the negative dual of the landed `M5_cert` (what the method
CAN do at `k = 5`, gaps ≤ 12). It does NOT claim "sieves cannot prove twin
primes": parity-breaking inputs — bilinear / type-II information à la
Friedlander–Iwaniec, Chen's switching — modify the functional, and a modified
functional is outside the scope of this bound. The Lean theorems are per-`F`
bounds over CONTINUOUS `F`; the standard density bridge to Polymath8b's L²-sup
`M₂` (eq. 33) is noted as a possible later strengthening, not part of the floor.

## Landed (node T1 — carriers + trivia)

`Defs`: the four Fable-frozen carriers `I₂`, `J₁`, `J₂`, `R₂`; nonnegativity of
the quadratic carriers (`I₂_nonneg`, `J₁_nonneg`, `J₂_nonneg`); the Cauchy–Schwarz
weights `w₁`, `w₂` with the magic identity `w₁ + w₂ ≡ 2` plus their `[0,2]` bounds
and continuity; and the `ContinuousOn (uncurry F) R₂ ⇒ IntervalIntegrable` slice
plumbing in both simplex directions (`slice₁_*`, `slice₂_*`: continuity, plain,
square, and weighted-square integrability) that T3/T4 consume.
-/

-- Build-time axiom audit: a stray axiom in the twinbar track fails `lake build`
-- here, not only at out-of-band lint time.
open Salt.Tactic in
#audit_axioms Salt.TwinBar.I₂_nonneg Salt.TwinBar.J₁_nonneg Salt.TwinBar.J₂_nonneg
  Salt.TwinBar.w₁_add_w₂ Salt.TwinBar.w₁_nonneg Salt.TwinBar.w₂_nonneg
  Salt.TwinBar.w₁_le_two Salt.TwinBar.w₂_le_two
  Salt.TwinBar.w₁_continuous Salt.TwinBar.w₂_continuous
  Salt.TwinBar.slice₁_continuousOn Salt.TwinBar.slice₂_continuousOn
  Salt.TwinBar.slice₁_intervalIntegrable Salt.TwinBar.slice₂_intervalIntegrable
  Salt.TwinBar.slice₁_sq_intervalIntegrable Salt.TwinBar.slice₂_sq_intervalIntegrable
  Salt.TwinBar.slice₁_weight_sq_intervalIntegrable
  Salt.TwinBar.slice₂_weight_sq_intervalIntegrable
