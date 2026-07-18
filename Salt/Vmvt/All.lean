/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Defs
import Salt.Vmvt.BaseCase
import Salt.Vmvt.Linnik
import Salt.Vmvt.Shifted
import Salt.Vmvt.MeanValue
import Salt.Vmvt.PrimeCount
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
#audit_axioms Salt.Vmvt.primes_in_Ioc_ge
  Salt.Vmvt.vmvt_base
  Salt.Vmvt.vmvtExp_succ
  Salt.Vmvt.Jk_shift_le
  Salt.Vmvt.Ncount_union_le
  Salt.Vmvt.Ncount_shift_le
  Salt.Vmvt.linnik_lemma
  Salt.Vmvt.Jk_le_of_le
  Salt.Vmvt.multiset_map_eq_of_powerSum_eq
  Salt.Vmvt.exists_perm_of_powerSum_eq
  Salt.Vmvt.Jk_image_affine
  Salt.Vmvt.Jk_image_add
  Salt.Vmvt.Jk_image_mul
  Salt.Vmvt.Jk_ge_card_pow
  Salt.Vmvt.Jk_mono
