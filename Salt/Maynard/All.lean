/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard
import Salt.Maynard.Tuple
import Salt.Maynard.PhiAtom
import Salt.Maynard.KSieve
import Salt.Maynard.GFunction
import Salt.Maynard.Compat
import Salt.Maynard.ChebyshevInterval
import Salt.Maynard.GIntegrals
import Salt.Maynard.Mertens
import Salt.Maynard.Rankin
import Salt.Maynard.CongCount
import Salt.Maynard.Diagonal
import Salt.Maynard.DiagonalS2
import Salt.Maynard.LamBound
import Salt.Maynard.EHConsume
import Salt.Maynard.Ratio
import Salt.Maynard.CrossCollision
import Salt.Maynard.Transfer
import Salt.Maynard.S1Error
import Salt.Maynard.K0
import Salt.Maynard.S2Decomp
import Salt.Maynard.TransferSharp
import Salt.Maynard.CollisionQuant
import Salt.Maynard.LamBoundSharp
import Salt.Maynard.DivisorCount
import Salt.Maynard.S1Bound
import Salt.Maynard.CongSolvable
import Salt.Maynard.S2DiagLam
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.Lemma53
import Salt.Maynard.S2MainLower
import Salt.Maynard.TensorA1
import Salt.Maynard.Overshoot
import Salt.Maynard.S2Tensor
import Salt.Maynard.HMain
import Salt.Maynard.HOmit
import Salt.Maynard.HMainClose
import Salt.Maynard.S2TensorClosed
import Salt.Maynard.HA11
import Salt.Maynard.OvershootCheb
import Salt.Maynard.S2TensorCheb
import Salt.Maynard.S2Eh
import Salt.Maynard.S2Collision
import Salt.Maynard.VAbs
import Salt.Maynard.EulerTailL
import Salt.Maynard.Lemma53Rel
import Salt.Maynard.S2CompatEH
import Salt.Maynard.S2MainLowerRel
import Salt.Maynard.S2FiberCount
import Salt.Maynard.S2CompatEHFinal
import Salt.Maynard.RatioCore
import Salt.Maynard.Endgame
import Salt.Maynard.Final
import Salt.Maynard.FrontierDischarge
import Salt.Maynard.FrontierFinal
import Salt.Maynard.Lemma53Tight
import Salt.Maynard.Complete
import Salt.Maynard.Level
import Salt.Maynard.LevelConsume
import Salt.Maynard.GehDoor
import Salt.Maynard.GehPiSeam
import Salt.Maynard.GehVaughan
import Salt.Maynard.GehMulti
import Salt.Maynard.GehTypeI
import Salt.Maynard.GehSW
import Salt.Maynard.GehBridge
import Salt.Maynard.GehSmallQ
import Salt.Maynard.GehDecomp
import Salt.Maynard.GehDecomp2
import Salt.Maynard.GehClose
import Salt.Maynard.GehTail
import Salt.Maynard.GehPp
import Salt.Maynard.GehPp2
import Salt.Maynard.GehWindowPnt
import Salt.Maynard.GehSmallQClose
import Salt.Maynard.GehSmallQEst
import Salt.Maynard.TauSpike
import Salt.Maynard.GehAnchor
import Salt.Maynard.PpRootCyc
import Salt.Maynard.PpRootTwo
import Salt.Maynard.PpRootCrt
import Salt.Maynard.ShiuBlocks
import Salt.Maynard.PpFold
import Salt.Maynard.PpRootGeneral
import Salt.Maynard.PpSums
import Salt.Maynard.PpAssembly
import Salt.Maynard.ShiuDecomp
import Salt.Maynard.ShiuRankin
import Salt.Maynard.ShiuSieve
import Salt.Maynard.ShiuGraded
import Salt.Maynard.ShiuClasses
import Salt.Maynard.ShiuTuned
import Salt.Maynard.ShiuClose
import Salt.Maynard.ShiuFinal
import Salt.Maynard.ShiuIV
import Salt.Maynard.ShiuS5
import Salt.Maynard.ShiuS5b
import Salt.Maynard.GehShiuWire
import Salt.Tactic.AuditAxioms

/-! ⟦AUDIT-ROWS 0802⟧ The Maynard capstone, ledger-absent until TROPHY's
census (this file had no audit block at all).

⟦AUDIT-ROWS 0901⟧ **The GEH/Shiu/Pp road is LIVE, and it is listed here for the
first time** (council 2026-09-01, ruling 11; the helm's audit-coverage sweep of the
same day).  That sweep found this
aggregate listing exactly ONE name against 99 imported modules, and 31 modules —
the whole GEH road — provably outside every audit block's dependency cone in the
repository.  A road with no audited headliner is not a road that failed an audit;
it is a road no audit could see.

⛔ **Why one terminal was not enough, and this is the finding worth carrying.**
`geh_door_of_obligations` is a CONDITIONAL headline: `GEH_min` and the named
obligations enter it as HYPOTHESES.  A hypothesis contributes nothing to a proof
term, so the machinery that will one day DISCHARGE those hypotheses — the Shiu
road, the small-`q` Siegel–Walfisz arm, the Type-I₁ tail — is by construction
*outside* the terminal's cone.  Listing the door covers 11 of the road's 31
modules and cannot, even in principle, reach the other 20.

⇒ 🔑 ***AN AUDIT GATE FOLLOWS PROOF DEPENDENCY, SO A CONDITIONAL TERMINAL CANNOT
COVER ITS OWN SUPPLIERS. THE MORE OBLIGATIONS A HEADLINE CARRIES, THE LESS OF ITS
ROAD ITS AUDIT SEES*** — and the suppliers are exactly the work in progress, i.e.
exactly where a stray axiom would land.  The names below are therefore the road's
seven sub-road ROOTS plus the door and its one discharged obligation, chosen so
that every one of the 31 modules lies in some listed name's cone.  Same policy as
`Salt/LS/All.lean`: terminals, not every declaration; helpers are covered through
them. -/
#audit_axioms Salt.Maynard.bounded_gaps_from_eh_complete
  -- The GEH door: the conditional headline, and the one obligation now discharged.
  geh_door_of_obligations
  Salt.Maynard.ppLevel_holds
  -- The seven roots of the sub-roads the door's own cone cannot reach.
  GehAnchor.pieceObligationU_of_anchored_multiblock
  Salt.Maynard.hdecomp_double
  Salt.Maynard.hshiu_wire_sharp
  Salt.Maynard.window_lambda_disc_le
  tail_obligation_vP1
  Salt.Maynard.windowPNT_holds
  Salt.Maynard.s2_tensor_lower_closed
