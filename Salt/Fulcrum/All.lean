/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Fulcrum.Basic
import Salt.Tactic.AuditAxioms

/-!
# The fulcrum rung (`fulcrum`) — aggregate import

Design: `docs/exploration/fulcrum-pass1.md` (Pass 1 VERDICT). Lands the STATEMENT
layer of `F_min` — the refuter-survived weakest twin-prime hypothesis — beside
the landed Heath-Brown statement, additively.

## Landed (FULCRUM-S1)

* `FulcrumQualityMin` — `F_min` verbatim: the parametric quality-ball hypothesis.
* `fulcrum_zero_real` / `fulcrum_zero_real_zfr` — the reality derivation (DEMAND
  MAP L1): a ball witness at `C ≥ 2/c₀`, `q ≥ 3` is real with `1/2 ≤ Re ρ < 1`,
  from `zero_free_region_all` + `LFunction_ne_zero_of_one_le_re`.
* `SiegelModulusUnbounded` — the compactness gadget INTERFACE (FULCRUM-S2 fills
  the proof).
* `imsz_implies_fulcrum_of_gadget` — `InfinitelyManySiegelZeros → F(C)`,
  conditional on the gadget.

## Coordination (FULCRUM-S1 ↔ FULCRUM-S2, append-only)

The compactness gadget is stated here as `Salt.Fulcrum.SiegelModulusUnbounded`
(in `Salt/Fulcrum/Basic.lean`). FULCRUM-S2 should prove a term of that type
(importing `Salt.Fulcrum.Basic`); feeding it to `imsz_implies_fulcrum_of_gadget`
then yields `InfinitelyManySiegelZeros → FulcrumQualityMin C` unconditionally,
recovering `HeathBrownStatement` as a corollary.
-/

-- Build-time axiom audit: a stray axiom in the fulcrum track fails `lake build`
-- here, not only at out-of-band lint time.
open Salt.Tactic in
#audit_axioms Salt.Fulcrum.fulcrum_zero_real Salt.Fulcrum.fulcrum_zero_real_zfr
  Salt.Fulcrum.imsz_implies_fulcrum_of_gadget
