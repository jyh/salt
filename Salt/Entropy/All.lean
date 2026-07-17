/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.FiniteRange
import Salt.Entropy.Mathlib.MeasureDirac
import Salt.Entropy.Mathlib.MeasureReal
import Salt.Entropy.Mathlib.UniformOn
import Salt.Entropy.Mathlib.ConditionalProbability
import Salt.Entropy.Mathlib.SetCard
import Salt.Entropy.Mathlib.MeasureProd
import Salt.Entropy.Mathlib.LebesgueBasic
import Salt.Entropy.Mathlib.LebesgueCountable
import Salt.Entropy.Mathlib.KernelComp
import Salt.Entropy.Mathlib.KernelDisintegration
import Salt.Entropy.Measure
import Salt.Entropy.Kernel.Basic
import Salt.Entropy.Kernel.MutualInfo
import Salt.Entropy.Basic
import Salt.Entropy.Chowla.LogMeasure
import Salt.Entropy.Chowla.Fannes
import Salt.Entropy.Chowla.Invariance
import Salt.Entropy.Chowla.Regime
import Salt.Entropy.Chowla.InvarianceHead
import Salt.Entropy.Chowla.Step
import Salt.Entropy.Chowla.Endpoints
import Salt.Entropy.Chowla.Tower
import Salt.Entropy.Chowla.Decrement
import Salt.Entropy.Chowla.RegimeInst
import Salt.Entropy.Chowla.Diverge
import Salt.Entropy.Chowla.ResidueUniform
import Salt.Entropy.Chowla.MarkovExtract
import Salt.Entropy.Chowla.Concentration
import Salt.Entropy.Chowla.WeakUniform
import Salt.Entropy.Chowla.Dilation
import Salt.Entropy.Chowla.FBridge
import Salt.Entropy.Chowla.Decoupled
import Salt.Entropy.Chowla.CircleMethod
import Salt.Entropy.Chowla.WindowCount
import Salt.Entropy.Chowla.Transport
import Salt.Entropy.Chowla.MRTDoor
import Salt.Entropy.Chowla.QuadrupleCount
import Salt.Entropy.Chowla.LargeSpectrum
import Salt.Entropy.Chowla.OuterCombine
import Salt.Entropy.Chowla.LargeSpectrumBound
import Salt.Entropy.Chowla.GoldbachEnergyM2
import Salt.Entropy.Chowla.GoldbachEnergySieve
import Salt.Entropy.Chowla.GoldbachEnergyHsq
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.Windows
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Entropy.ConsumerTest
import Salt.Tactic.AuditAxioms

/-!
# The entropy library (sprint-3 A-R1) — aggregate import

The discrete Shannon entropy library, ported from the PFR project
(github.com/teorth/pfr, commit a177b2e4, Apache-2.0 — see
`LICENSE-PFR-Apache-2.0` and the per-file attribution headers) per
`docs/exploration/s3-a1-design.md` and its gate verdict.  Wave 1
(scaffolding + patch residues) landed 2026-07-17; waves extend this
file as they land (Measure → kernel glue → Basic → Kernel).

Consumer target: the entropy toolkit (3.1)–(3.7) of Tao,
arXiv:1509.05422 (the entropy decrement argument, rung A-R2).
-/

-- Build-time axiom audit: a stray axiom in the entropy track fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms FiniteRange.real_full FiniteRange.null_of_compl
  MeasureTheory.Measure.dirac_real_apply'
  MeasureTheory.Measure.prod_real_singleton
  ProbabilityTheory.uniformOn_real_singleton
  ProbabilityTheory.cond_real_apply
  ProbabilityTheory.measureEntropy_le_log_card
  ProbabilityTheory.measureEntropy_dirac
  ProbabilityTheory.measureEntropy_prod
  ProbabilityTheory.measureMutualInfo_nonneg
  Salt.Entropy.Chowla.entropy_sub_le_of_l1
  Salt.Entropy.Chowla.harmonic_shift_l1_le
  Salt.Entropy.Chowla.dvd_chowlaTower
  Salt.Entropy.Chowla.fBridge_concentration
  Salt.Entropy.Chowla.fBridge_concentration_sharp
  Salt.Entropy.Chowla.fBridge_concentration_decoupled_sharp
  Salt.Entropy.Chowla.fBridgeG_mean
  Salt.Entropy.Chowla.fBridgeF_mean
  Salt.Entropy.Chowla.fBridge_concentration_decoupled
  Salt.Entropy.Chowla.dft_is_fourier_coeff
  Salt.Entropy.Chowla.dft_parseval
  Salt.Entropy.Chowla.dft_l1_bound
  Salt.Entropy.Chowla.primeWindow_card_le_of_regime
  Salt.Entropy.Chowla.regime_nonvacuous
  Salt.Entropy.Chowla.circle_method_estimate
  Salt.Entropy.Chowla.badSet_transport
  Salt.Entropy.Chowla.badSet_transport_at_calibration
  Salt.Entropy.Chowla.contradiction_of_mrtDoor
  Salt.Entropy.Chowla.addEnergy_eq_sum_repCount_sq
  Salt.Entropy.Chowla.addEnergy_le_of_r_bound
  Salt.Entropy.Chowla.W3_AE_d_of_sieve
  Salt.Entropy.Chowla.expSum_eq_dft_windowPhi
  Salt.Entropy.Chowla.card_bigXi_mul_thresh_le
  Salt.Entropy.Chowla.dft_windowPhi_l4_le
  Salt.Entropy.Chowla.large_spectrum_energy
  Salt.Entropy.Chowla.windowPhi_norm_le
  Salt.Entropy.Chowla.outer_combine
  Salt.Entropy.Chowla.outer_badMass_eq
  Salt.Entropy.Chowla.outer_badMass_le
  Salt.Entropy.Chowla.fBridgeF_abs_le_box
  Salt.Entropy.Chowla.decoupledMean_abs_le_box
  Salt.Entropy.Chowla.bigXi_bounded_of_sieve
  Salt.Entropy.Chowla.rhoG_prime_dvd
  Salt.Entropy.Chowla.rhoG_prime_not_dvd
  Salt.Entropy.Chowla.rhoG_mul_of_coprime
  Salt.Entropy.Chowla.rhoG_squarefree_le
  Salt.Entropy.Chowla.goldProgression_count_bound
  Salt.Entropy.Chowla.nuG_mult
  Salt.Entropy.Chowla.nuG_lt_one_of_prime
  Salt.Entropy.Chowla.goldEnergySieve_abs_rem_le
  Salt.Entropy.Chowla.goldEnergySieve_siftedSum
  Salt.Entropy.Chowla.repCount_le_siftedSum
  Salt.Entropy.Chowla.log_chowla_two_shell
  Salt.Entropy.Chowla.hFac_lcm_sum_le
  Salt.Entropy.Chowla.hFac_mul_of_coprime
  Salt.Entropy.Chowla.sTrunc_le_prod
  Salt.Entropy.Chowla.dilation_error
  Salt.Entropy.Chowla.weakUniform_generic
  Salt.Entropy.Chowla.weakUniform_spine
  Salt.Entropy.Chowla.iIndepFun_residueProj
  Salt.Entropy.Chowla.hoeffding_residueProj
  Salt.Entropy.Chowla.decrement_markov
  Salt.Entropy.Chowla.mutualInfo_eq_integral_condDistrib_defect
  Salt.Entropy.Chowla.entropy_residueWindow_ge
  Salt.Entropy.Chowla.entropy_ge_of_mass_ub
  Salt.Entropy.Chowla.chowlaRegime_exists
  Salt.Entropy.Chowla.dropSum_exceeds_log_two
  Salt.Entropy.Chowla.not_summable_one_div_nat_loglog
  Salt.Entropy.Chowla.entropy_decrement
  Salt.Entropy.Chowla.regime_exists_of_dropSum_exists
  Salt.Entropy.Chowla.regime_xside
  Salt.Entropy.Chowla.tower_telescope Salt.Entropy.Chowla.tower_step
  Salt.Entropy.Chowla.entropy_per_symbol_le
  Salt.Entropy.Chowla.decrement_exists_of_tower
  Salt.Entropy.Chowla.joint_l1_le Salt.Entropy.Chowla.condEntropy_shift_le
  Salt.Entropy.Chowla.step_ineq_3_11
  Salt.Entropy.Chowla.condEntropy_shift_reduction
  Salt.Entropy.Chowla.condEntropy_shift_le_of_l1
  Salt.Entropy.Chowla.isProbabilityMeasure_logMeasure
  Salt.Entropy.Chowla.logMeasure_apply_singleton
  Salt.Entropy.Chowla.harmonic_window_bounds
  entropy_liouvilleWindow_le liouvilleWindow_block
  Salt.Entropy.Chowla.entropy_residueWindow_le_log_PH
  Salt.Entropy.Chowla.log_PH_le Salt.Entropy.Chowla.coprime_PH_of_le
  ProbabilityTheory.entropy_le_log_card ProbabilityTheory.chain_rule'
  ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy
  ProbabilityTheory.condMutualInfo_nonneg
  ProbabilityTheory.Kernel.entropy_triple_add_entropy_le'
  ProbabilityTheory.Kernel.entropy_compProd
  ProbabilityTheory.Kernel.chain_rule
  ProbabilityTheory.Kernel.disintegration
  ProbabilityTheory.Kernel.condKernel_prod_ae_eq
