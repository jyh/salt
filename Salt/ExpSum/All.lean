/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Basic
import Salt.ExpSum.Kusmin
import Salt.ExpSum.VdCorput2
import Salt.ExpSum.DerivTest
import Salt.ExpSum.DerivTestK
import Salt.ExpSum.ZetaBlock
import Salt.Tactic.AuditAxioms

/-!
# The exponential-sum track (`ExpSum`) — aggregate import

The LITTLEWOOD campaign's toolkit (JYH ratified 2026-07-17: the
staged power-region road — van der Corput machinery → the
Littlewood zero-free region; VMVT registered as the summit
beyond). Campaign map: `docs/exploration/s3-a3-design.md` (VK-R0
adjudication). First anywhere: no proof assistant holds any of
the van der Corput method.
-/

open Salt.Tactic in
#audit_axioms Salt.ExpSum.zeta_block_bound
  Salt.ExpSum.zeta_block_vdC
  Salt.ExpSum.kusmin_landau
  Salt.ExpSum.vdC_second_derivative
  Salt.ExpSum.weyl_vdC_sq
  Salt.ExpSum.weyl_vdC_expSum
  Salt.ExpSum.eR_mul_conj
  Salt.ExpSum.norm_eR
  Salt.ExpSum.vdC_third_derivative
  Salt.ExpSum.vdC_2nd_ZR
  Salt.ExpSum.vdC_kth_derivative
