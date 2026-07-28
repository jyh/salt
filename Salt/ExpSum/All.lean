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
import Salt.ExpSum.ZetaGrowth
import Salt.ExpSum.ZetaApprox
import Salt.ExpSum.Window
import Salt.ExpSum.Strip
import Salt.ExpSum.Twist
import Salt.ExpSum.TwistStrip
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
#audit_axioms Salt.ExpSum.zeta_growth_strip
  Salt.ExpSum.norm_zeta_sub_approx_le
  Salt.ExpSum.zeta_partial_growth
  Salt.ExpSum.zeta_dyadic_assembly
  Salt.ExpSum.zeta_block_kusmin
  Salt.ExpSum.zeta_block_bound
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
  Salt.ExpSum.zeta_block_window
  Salt.ExpSum.zeta_block_window_meet
  Salt.ExpSum.zeta_block_window_three
  Salt.ExpSum.isVdCBound_16
  Salt.ExpSum.zeta_block_kusmin_prefix
  Salt.ExpSum.zeta_block_vdC_prefix
  Salt.ExpSum.zeta_block_prefix_collapse
  Salt.ExpSum.zeta_window_prefix
  Salt.ExpSum.zeta_seam_prefix
  Salt.ExpSum.zeta_patch_prefix
  Salt.ExpSum.cpow_weight_split
  Salt.ExpSum.abel_antitone_prefix
  Salt.ExpSum.zeta_weighted_block
  Salt.ExpSum.window_coverage
  Salt.ExpSum.zeta_block_dispatch
  Salt.ExpSum.dk_affine
  Salt.ExpSum.dk_add_affine
  Salt.ExpSum.dk_add_linear
  Salt.ExpSum.dk_eq_zero_of_diff_const
  Salt.ExpSum.dk_signed_add_linear
  Salt.ExpSum.dk_window_affine_iff
  Salt.ExpSum.isVdCBound_affine
  Salt.ExpSum.isVdCBound_16_affine
  Salt.ExpSum.zeta_dk_window_twist
  Salt.ExpSum.dyadic_sum_split_gen
  Salt.ExpSum.sum_Icc_rpow_neg_le'
  Salt.ExpSum.sq_le_two_pow
  Salt.ExpSum.head_coeff_le
  Salt.ExpSum.zeta_ladder_bound
  Salt.ExpSum.m0_guard
  Salt.ExpSum.zeta_head_bound
  Salt.ExpSum.zeta_strip_family
  Salt.ExpSum.zeta_block_vdC_prefix_twist
  Salt.ExpSum.zeta_block_prefix_collapse_twist
  Salt.ExpSum.zeta_window_prefix_twist
  Salt.ExpSum.zeta_seam_prefix_twist
  Salt.ExpSum.zeta_patch_prefix_twist
  Salt.ExpSum.zeta_lowt_prefix_twist
