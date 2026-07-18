/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Defs
import Salt.Tactic.AuditAxioms

/-!
# The Vinogradov track (`Vmvt`) — aggregate import

THE SUMMIT CAMPAIGN (JYH ratified 2026-07-17: "we go for full
VMVT"): the Vinogradov mean value theorem via the elementary
Linnik–Karatsuba p-adic route (porting target: Vaughan PSU
Ch. 24, staged in the session scratchpad), toward the first
power zero-free region in any proof assistant and, through it,
the Matomäki–Radziwiłł gate and unconditional log-Chowla-2.
Campaign map: VMVT-R0's adjudication in
`docs/exploration/s3-a3-design.md`. The gate node: Linnik's
Lemma (VMVT-N3).
-/

open Salt.Tactic in
#audit_axioms Salt.Vmvt.Jk_image_affine
  Salt.Vmvt.Jk_image_add
  Salt.Vmvt.Jk_image_mul
  Salt.Vmvt.Jk_ge_card_pow
  Salt.Vmvt.Jk_mono
