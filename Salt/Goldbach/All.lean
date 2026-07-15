/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Base
import Salt.Goldbach.WeightWindow
import Salt.Goldbach.Residue
import Salt.Goldbach.Density
import Salt.Tactic.AuditAxioms

/-!
# The Goldbach rung (`chen_goldbach`) — aggregate import

Sprint Q1 (full in-sprint, JYH-ratified 29a9a68): Chen's second theorem —
every sufficiently large even `N` is `p + P₂`. Design:
`docs/exploration/q1-design.md` (frozen statement D0, waves W0–W4,
post-gate corrections). The reuse contract (D1): the 2A backbone imports
unchanged; wave files are new siblings under `Salt/Goldbach/`. This
aggregator is HOUSE-OWNED: executors never edit it; each wave landing is
wired here at its ceremony.
-/

-- Build-time axiom audit: a stray axiom in the Goldbach rung fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.Goldbach.window_two_thirds_lt
  Salt.Goldbach.card_window_dvd_le Salt.Goldbach.stripSum_le
  Salt.Goldbach.exists_crt_finset Salt.Goldbach.goldbach_residue_witness
  Salt.Goldbach.crtClassG_modEq_left Salt.Goldbach.crtClassG_modEq_right
  Salt.Goldbach.crtClassG_coprime Salt.Goldbach.crt_class_coprimeG
  Salt.Goldbach.goldPs_squarefree Salt.Goldbach.goldPs_primeFactors
  Salt.Goldbach.goldPs_coprime_N Salt.Goldbach.coprime_of_dvd_goldPs
  Salt.Goldbach.goldPs_odd Salt.Goldbach.goldPs_primeFactors_facts
  Salt.Goldbach.coprime_mod_of_coprime Salt.Goldbach.crtClass_coprime_gold
  Salt.Goldbach.card_primesInWindow_dvd_le
  Salt.Goldbach.punctured_correction_le
  Salt.Goldbach.window_prod_upper_punctured
  Salt.Goldbach.exp_correction_le Salt.Goldbach.exp_correction_le_op
  Salt.Goldbach.window_prod_upper_punctured_folded
  Salt.Goldbach.goldPs_nu_eq Salt.Goldbach.goldPs_hnu
