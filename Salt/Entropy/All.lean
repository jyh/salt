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
import Salt.Entropy.Chowla.ChowlaFailure
import Salt.Entropy.Chowla.WindowMertensLower
import Salt.Entropy.Chowla.GoldbachEnergyG
import Salt.Entropy.Chowla.Prop26
import Salt.Entropy.Chowla.GoldbachEnergyHsqAsm
import Salt.Entropy.Chowla.GoldbachEnergyGc
import Salt.Entropy.Chowla.GoldbachEnergyHsq2
import Salt.Entropy.Chowla.ShiftCorr
import Salt.Entropy.Chowla.GoldbachEnergyHpt
import Salt.Entropy.Chowla.HReduce
import Salt.Entropy.Chowla.GoldbachEnergyFinal
import Salt.Entropy.Chowla.GoldbachEnergyN0
import Salt.Entropy.Chowla.DilationStability
import Salt.Entropy.Chowla.HMainAssembly
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.SpineClose
import Salt.Entropy.Chowla.TowerDischarge
import Salt.Entropy.Chowla.BoundaryMap
import Salt.Entropy.Chowla.RegimeParam
import Salt.Entropy.Chowla.TowerExport
import Salt.Entropy.Chowla.SpineFinal
import Salt.Entropy.Chowla.TransportWall
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
  Salt.Entropy.Chowla.log_chowla_two_shell_xi
  Salt.Entropy.Chowla.hFac_lcm_sum_le
  Salt.Entropy.Chowla.hFac_mul_of_coprime
  Salt.Entropy.Chowla.sTrunc_le_prod
  Salt.Entropy.Chowla.singleCorr_of_fails
  Salt.Entropy.Chowla.liouville_mul
  Salt.Entropy.Chowla.liouville_prime
  Salt.Entropy.Chowla.h211_of_logChowla2Fails
  Salt.Entropy.Chowla.primeWindow_sum_inv_ge
  Salt.Entropy.Chowla.goldSelbergTerms_prime_dvd
  Salt.Entropy.Chowla.goldSelbergTerms_prime_not_dvd
  Salt.Entropy.Chowla.gTwin_le_sCorr_mul_selbergTerms
  Salt.Entropy.Chowla.goldSelbergBoundingSum_ge_log_sq
  Salt.Entropy.Chowla.fBridge_of_singleCorr
  Salt.Entropy.Chowla.fBridgeF_liouville_apply
  Salt.Entropy.Chowla.perPair_dilation
  Salt.Entropy.Chowla.hsq_holds
  Salt.Entropy.Chowla.hsq_holds_gen
  Salt.Entropy.Chowla.sum_sTruncW_sq_le
  Salt.Entropy.Chowla.goldCarrierSum_ge_log_sq_div_sTrunc2
  Salt.Entropy.Chowla.goldSelbergBoundingSum_ge_log_sq_div_sTrunc2
  Salt.Entropy.Chowla.sTrunc2_pos
  Salt.Entropy.Chowla.selbergTerms_eq_gTwin_of_coprime
  Salt.Entropy.Chowla.hFac2_lcm_sum_le
  Salt.Entropy.Chowla.hFac2_mul_of_coprime
  Salt.Entropy.Chowla.hsq_holds2
  Salt.Entropy.Chowla.integral_logMeasure_eq
  Salt.Entropy.Chowla.integral_shift_le
  Salt.Entropy.Chowla.corr_shift_le
  Salt.Entropy.Chowla.repCount_eq_zero_of_window_odd
  Salt.Entropy.Chowla.goldSiftedSum_le_main_add_err
  Salt.Entropy.Chowla.goldBoundingSum_ge_uniform
  Salt.Entropy.Chowla.repCount_even_le_primorial
  Salt.Entropy.Chowla.consumability_probe
  Salt.Entropy.Chowla.hreduce_close
  Salt.Entropy.Chowla.hsq_holds_gen'
  Salt.Entropy.Chowla.hsq_holds3
  Salt.Entropy.Chowla.hpt_holds
  Salt.Entropy.Chowla.bigXi_bounded
  Salt.Entropy.Chowla.perPair_collapse
  Salt.Entropy.Chowla.dilated_window_stability
  Salt.Entropy.Chowla.hreduce_holds
  Salt.Entropy.Chowla.hbudget_holds
  Salt.Entropy.Chowla.hreduce_holds_final
  Salt.Entropy.Chowla.log_chowla_two_conditional
  Salt.Entropy.Chowla.log_chowla_two_conditional_regime
  Salt.Entropy.Chowla.mrtUniformity_implies_xi
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXi
  Salt.Entropy.Chowla.log_chowla_two_of_door
  Salt.Entropy.Chowla.dilation_forces_log
  Salt.Entropy.Chowla.approx_covariance_not_unique
  Salt.Entropy.Chowla.completelyMult_pm_one_collapse
  Salt.Entropy.Chowla.collapse_forces_completelyMult
  Salt.Entropy.Chowla.collapse_iff_completelyMult
  Salt.Entropy.Chowla.chowlaRegime_exists_param
  Salt.Entropy.Chowla.chowlaRegime_exists_param_gen
  Salt.Entropy.Chowla.regimeEnlargeX'
  Salt.Entropy.Chowla.chowlaRegime_exists_param_head'
  Salt.Entropy.Chowla.chowlaRegime_exists_param_tower
  Salt.Entropy.Chowla.chowlaRegime_exists_param_head_tower'
  Salt.Entropy.Chowla.log_chowla_two_budget_head_g
  Salt.Entropy.Chowla.dropSum_exceeds_log_two_base
  Salt.Entropy.Chowla.towerJmin_spec
  Salt.Entropy.Chowla.towerDropSum_le_log_two_of_lt_towerJmin
  Salt.Entropy.Chowla.towerDropSum_ge_half_log_ratio
  Salt.Entropy.Chowla.towerDropSum_le_half_log_ratio_mul
  Salt.Entropy.Chowla.tower_loglog_le Salt.Entropy.Chowla.tower_loglog_ge
  Salt.Entropy.Chowla.log_chowla_two_conditional_hoisted
  Salt.Entropy.Chowla.log_chowla_two_final
  Salt.Entropy.Chowla.log_chowla_two_final_xi
  Salt.Entropy.Chowla.orthogonality_wall
  Salt.Entropy.Chowla.no_slot_derived_twin_linkage
  Salt.Entropy.Chowla.slots_iff_completelyMult
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
  Salt.Entropy.Chowla.regime_outer
  Salt.Entropy.Chowla.omega_big_at Salt.Entropy.Chowla.x_big_at
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

/-! ⟦S0-TOWER — the `K = 9/2` twin chain audit⟧ (`TowerExport` §9 + `SpineFinal`, 2026-07-30,
ruling C-A GRANTED).  The landed export `tower_loglog_le` is `K = 5`; S11-SCOPE's two-λ audit
needs `K ≤ 4.9` (at `K = 5` the compose window is EMPTY by 1.47×).  The exponent is free
arithmetic — the landed proof's crossing budget is `w_J − w₀ ≤ (40/19)·log 2 + 7/300 = 1.4826`,
spent against the line `3/2`, and `3/2 < log (9/2) = 1.50408` (`exp(3/2) = 4.4817 < 4.5`) just
as `3/2 < log 5`.  The twins are ADDITIVE: the `K = 5` chain is untouched and both live side by
side.  Stated at `rpow` (the exponent is not a natural); `rpow_nine_halves_le_pow_five` is the
one-way bridge back to the landed `npow 5` shape under the guard `50 ≤ loglog H₋`. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.three_halves_lt_log_nine_halves
  Salt.Entropy.Chowla.rpow_nine_halves_le_pow_five
  Salt.Entropy.Chowla.tower_loglog_le_45
  Salt.Entropy.Chowla.chowlaRegime_exists_param_tower_45
  Salt.Entropy.Chowla.chowlaRegime_exists_param_head_tower45'
  Salt.Entropy.Chowla.log_chowla_two_budget_head_g_45

/-! ⟦N0-RETHREAD — THE 318-BIT LEVER: the honest-threshold `hpt`/`bigXi` twins⟧
(`GoldbachEnergyN0`, 2026-07-30, CG-SCOPE's `N0 = 2^100` line item).  `hpt_large`'s threshold
`H₁ = max N0 (max tA tB tD)` is squared into `hpt_holds`'s `CS` and squared again through
`C₁²` into `K = 32·K_lcm·C₁²/ε¹⁰`, so each bit of `log₂ H₁` costs FOUR of `log₂ K`.  The audit:
`N0 = 2^100` is honestly `2^20` (its only consumers are `2 ≤ z` and `log z ≥ (1/20)log H`);
the binding threshold underneath is `tB = z₀^10 = 10^20` (the Selberg main-term floor
`M3Assembly.z0 = 100` raised by the truncation `z = ⌊H^(1/10)⌋₊`), itself lowered to `16^10`
by re-running `D3` at `γ = 1/16` (`c₀ : 1/64 → 1/256`, invisible under `102400/ε²`); and the
`CS` shape is lossy by `H₁/2` (the landed proof reads the card at `H₁` and the fraction at
`H = 2`).  Additive: `hpt_holds`/`bigXi_bounded` are untouched and both chains live side by
side.  At `ε = 1/500`: `log₂ C₁ : 193.30 → ≤ 35`, `log₂ K : 538.21 → 221.61` — 316.6 bits. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.mainTermSum_ge_of_sixteen
  Salt.Entropy.Chowla.logZ_ge_twenty
  Salt.Entropy.Chowla.repCount_even_le_primorial_param
  Salt.Entropy.Chowla.hpt_large_thr
  Salt.Entropy.Chowla.hpt_holds_thr
  Salt.Entropy.Chowla.hsq_explicit
  Salt.Entropy.Chowla.bigXi_bounded_explicit
  Salt.Entropy.Chowla.hpt_const_le_pow35
  Salt.Entropy.Chowla.hpt_holds_500
  Salt.Entropy.Chowla.bigXi_bounded_500

/-! ⟦THE L² RESTRUCTURE — stone 3: THE Ξ-SUMMED L² DOOR⟧ (`MRTDoor` §L², 2026-07-30, the
freeze `docs/exploration/l2-restructure-freeze-0730.md` + REF-L2-STONE's BINDING amendment 1).
`MRTUniformityXiL2 R ρ` grades the door by the TOTAL over `Ξ_H` —
`∑_{ξ∈Ξ_H}(1/H²)∫‖windowExpSum H · (−ξ/H)‖²dμ ≤ ρ` — not per frequency: a per-`ξ` twin would
be read `|Ξ_H|` times by the seam and would re-multiply the grade by `K`, and the whole shed of
the restructure evaporates.  `contradiction_of_mrtDoorXiL2` is accordingly `K`-FREE (no
`|Ξ_H| ≤ K` hypothesis, no `δ`-nonnegativity side condition): the chain is
`c₀ε ≤ (the summed L² object) ≤ ρ < c₀ε`.  TAO-FAITHFULNESS (mandate R4): the predicate is a
finite SUM of integrals with no `sup` inside — the seam warning of `MRTUniformity`/
`MRTUniformityXi` is re-stated verbatim on the twin — and `mrtUniformityXiL2_of_xi` is the
safety net: the LANDED `L¹` Ξ_H-door implies the `L²` one at `K·δ` (via `‖·‖² ≤ H‖·‖`), so
nothing here is deeper than Prop 2.4.  Additive: the `L¹` door and its seam are untouched. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2
  Salt.Entropy.Chowla.mrtUniformityXiL2_of_xi
