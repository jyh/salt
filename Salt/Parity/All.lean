/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Parity.Z
import Salt.Parity.Instances
import Salt.Tactic.AuditAxioms

/-!
# The Parity track (`Parity`) — aggregate import

D4 (ratified 2026-07-19): Z — the program's gap statement — as a
mathematical object. `Salt/Parity/Z.lean` is oracle-clean BY IMPORT
LIST (never imports `Salt.HB`/`Salt.TwinBar`); `Instances.lean` is
the census placing the landed corpus inside the parity-invariant
cone. The chain L0–L6: Z ⟺ TPC over the certified window, and the
gap theorem places every true twin-sufficient completion predicate
outside `ParityInv`. `ParityBarrier` is stated, never assumed.
-/

#audit_axioms Salt.Parity.parityInv_of_closed
  Salt.Parity.Z_trivial_of_not_completion
  Salt.Parity.oneWeight_mem
  Salt.Parity.twinFree_mem
  Salt.Parity.twinFree_twinMass
  Salt.Parity.twinMass_oneWeight_unbounded_iff
  Salt.Parity.sufficient_true_not_parityInv
  Salt.Parity.Z_implies_TPC
  Salt.Parity.TPC_implies_Z
  parityInv_S1_le_S2
  parityInv_twin_bar
  parityInv_chen_headline
  parityInv_twin_almost_prime
  parityInv_N5_3
  parityInv_chen_second

/-!
## The four census rows APPENDIX-A found outside every audit block

`Prop 8.4`'s census has nine `parityInv_*` instances; four of them
(`Parity/Instances.lean:53/62/72/93`) were listed in the manuscript's
Appendix A but sat in no `#audit_axioms` block, so the kernel never
re-checked their axiom sets alongside the rest. Folded in here
(N5 wave 2, 2026-08-03).
-/

#audit_axioms parityInv_twin_gate_fails
  parityInv_no_twin_weight
  parityInv_noSiegel_iff
  parityInv_N6_2
