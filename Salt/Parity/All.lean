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
