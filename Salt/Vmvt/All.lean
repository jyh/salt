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
import Salt.Vmvt.Transversal
import Salt.Vmvt.Transversal2
import Salt.Vmvt.Holder
import Salt.Vmvt.Fourier
import Salt.Vmvt.HolderTwo
import Salt.Vmvt.Transversal3
import Salt.Vmvt.StepFull
import Salt.Vmvt.Summit
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
  Salt.Vmvt.transversal_prime_exists
  Salt.Vmvt.Jk_le_two_mul_filter_split
  Salt.Vmvt.JkI_le_two_mul_split
  Salt.Vmvt.distinctBox_le_card_mul_sum
  Salt.Vmvt.degenBox_Ncount_le
  Salt.Vmvt.rpow_self_improve
  Salt.Vmvt.pairEqDominant_JkI_le_const
  Salt.Vmvt.crude_exp_ge_vmvtExp
  Salt.Vmvt.vmvt_base
  Salt.Vmvt.old_c0_le
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
  Salt.Vmvt.integral_eR_unit
  Salt.Vmvt.integral_setGen_mul_conj
  Salt.Vmvt.integral_norm_pow_eq_Jk
  Salt.Vmvt.pairEqBox_Ncount_eq_integral
  Salt.Vmvt.sum_prod_filter_eq
  Salt.Vmvt.setGen_pairEqBox_factor
  Salt.Vmvt.holder_step
  Salt.Vmvt.pairEq_Ncount_le_frac
  Salt.Vmvt.residue_distinctModP
  Salt.Vmvt.residue_mem_LinnikSol
  Salt.Vmvt.desigFibre_card_le
  Salt.Vmvt.powerSumEq_sub_const
  Salt.Vmvt.sum_prod_transRestBox
  Salt.Vmvt.setGen_transBox_factor
  Salt.Vmvt.setGen_mixBox_factor
  Salt.Vmvt.genFun_eq_sum_residue
  Salt.Vmvt.transBox_Ncount_le_sum_mixBox
  Salt.Vmvt.ndFibre_card_le
  Salt.Vmvt.gradedPairs_card_le
  Salt.Vmvt.powerSum_split
  Salt.Vmvt.Jk_restSet_le
  Salt.Vmvt.mixBox_fibre_le
  Salt.Vmvt.proj_mem_gradedPairs
  Salt.Vmvt.mixBox_Ncount_le
  Salt.Vmvt.transBox_Ncount_le
  Salt.Vmvt.collector_rpow
  Salt.Vmvt.vmvtResid_eq
  Salt.Vmvt.vmvt_collect_exp
  Salt.Vmvt.vmvtExp_step_diff
  Salt.Vmvt.Jk_Icc_eq_JkI
  Salt.Vmvt.transBox_le_ih
  Salt.Vmvt.le_scale_pow
  Salt.Vmvt.vmvtExp_ge_k
  Salt.Vmvt.bracket_le
  Salt.Vmvt.one_add_rpow_le_exp
  Salt.Vmvt.correction_le
  Salt.Vmvt.transBox_le_const
  Salt.Vmvt.n0_bounds
  Salt.Vmvt.vmvt_step_transversal_large
  Salt.Vmvt.vmvtConst_eq
  Salt.Vmvt.JkI_crude
  Salt.Vmvt.vmvtEta_ge
  Salt.Vmvt.b_le_vmvtExp
  Salt.Vmvt.vmvt_trivial_branch
