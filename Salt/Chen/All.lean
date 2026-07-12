/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchConstant
import Salt.Tactic.AuditAxioms

/-!
# The Chen rung (`chen`) — aggregate import

Design: `docs/blueprints/chen.md`. Target: **`chen_of_siegelWalfisz`**
(`p + 2 = P₂` infinitely often, modulo the SW gate) — the same gate the
SW arc is discharging, so the day it lands both bounded gaps AND Chen
become unconditional. Route: Tao 254A Supp. 5 (native twin form) with
the BJS explicit linear sieve (arXiv:2207.09452v6) as the constants
backbone; margin `M = 2log3 − log6 − c̄ ≈ 0.0424` at assembly
normalization (catch #20), governed by the frozen C0 budget ledger
(catches #21–#24).

## Landed (wave 1, partial)

`SwitchConstant` (C4a, FLOOR): `cbar` (the switch integral), `cbar_pos`,
and **`two_log_three_sub_log_six_sub_cbar_pos`** — the literal budget
line C5 consumes (`2log3 − log6 = log(3/2) ≥ 2/5 > 0.363084`). The
tight `cbar_lt : cbar < 0.363084` (gap 2.7e−7) is DEFERRED: mathlib has
no `Li₂`/polylog and no `norm_num` log extension, so neither the exact
dilog route nor a ≳220-panel tangent majorant is in scope — and C3d's
Lean-shape count bound may come from explicit prime sums rather than
the smooth integral, in which case `cbar_lt` is never consumed. See the
module docstring and `docs/blueprints/flags.md`.
-/

-- Build-time axiom audit: a stray axiom in the `chen` carriers fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.Chen.cbar_pos
  Salt.Chen.two_log_three_sub_log_six_sub_cbar_pos
