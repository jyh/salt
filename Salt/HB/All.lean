/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.QuadCharSum
import Salt.HB.TwistChain
import Salt.HB.TwistChainC
import Salt.HB.Transfer
import Salt.HB.PairSieve
import Salt.HB.PairInstance
import Salt.Tactic.AuditAxioms

/-!
# The Heath-Brown track (`HB`) — aggregate import

HB-ENGINE: the formalization of Heath-Brown, *Prime twins and
Siegel zeros* (Proc. LMS (3) 47 (1983) 193–224) — infinitely many
Siegel zeros imply infinitely many prime twins. The campaign map
(seven work packages, re-frozen against the source PDF) lives in
`docs/exploration/s3-hb3-design.md`; the WP2 L-function nodes land
in `Salt/SW/`; the Kloosterman/Weil inputs are banked in
`Salt/Weil/` (HB-FOUND).
-/

open Salt.Tactic in
#audit_axioms Salt.HB.pairSieve_lemma8
  Salt.HB.hb_lemma8
  Salt.HB.hbPairSieve
  Salt.HB.card_apResidues
  Salt.HB.hbPairSieve_rem_abs_le
  Salt.HB.hbPairSieve_errSum_le
  Salt.HB.boundingSum_ge_log_sq_of_twinDensity
  Salt.HB.LamStar_nonneg
  Salt.HB.vonMangoldt_le_LamTilde
  Salt.HB.LamTilde_eq_fChi_conv
  Salt.HB.LamStar_eq_fStar_conv
  Salt.HB.eq_nPlus_mul_nMinus
  Salt.HB.coprime_nPlus_nMinus
  Salt.HB.LamTilde_sub_vonMangoldt_le
  Salt.HB.LamTilde_eq_sum_nPlus
  Salt.HB.S1_le_S2
  Salt.HB.S2_sub_S1_le
  Salt.HB.overshoot_sum_nonneg
  Salt.HB.twin_termwise_le
  Salt.HB.overshootLog_eq_zero_of_nMinus_ne_one
  Salt.HB.overshootPP_eq_zero_of_not_isPrimePow
  Salt.HB.coprimeSupport_window
  Salt.HB.quadraticChar_sum_two_forms_bound
  Salt.HB.quadraticChar_sum_mul_shift
  Salt.HB.quadraticChar_sum_two_forms_trivial
  Salt.HB.legendre_sum_mul_shift
  Salt.HB.legendre_sum_two_forms_bound
  Salt.HB.legendre_sum_two_forms_trivial
