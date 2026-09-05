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
import Salt.Entropy.Chowla.GoldbachEnergyKc
import Salt.Entropy.Chowla.DilationStability
import Salt.Entropy.Chowla.HMainAssembly
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.SpineClose
import Salt.Entropy.Chowla.TowerDischarge
import Salt.Entropy.Chowla.BoundaryMap
import Salt.Entropy.Chowla.RegimeParam
import Salt.Entropy.Chowla.TowerExport
import Salt.Entropy.Chowla.TowerFlat
import Salt.Entropy.Chowla.TowerShape
import Salt.Entropy.Chowla.TowerFlatRegime
import Salt.Entropy.Chowla.BudgetFlat
import Salt.Entropy.Chowla.StepFlat
import Salt.Entropy.Chowla.DecrementFlat
import Salt.Entropy.Chowla.SpineFinal
import Salt.Entropy.Chowla.TransportWall
import Salt.Entropy.Chowla.Windows
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Entropy.Chowla.HeadPinLeaves
import Salt.Entropy.Chowla.HloExport
import Salt.Entropy.Chowla.SpineFlat
import Salt.Entropy.Chowla.TowerFlatExport
import Salt.Entropy.Chowla.TowerFlatBuilder
import Salt.Entropy.Chowla.HloExportFlat
import Salt.Entropy.Chowla.SpineEpsFence
import Salt.Entropy.Chowla.PinDichotomy
import Salt.Entropy.Chowla.ShiftFork
import Salt.Entropy.Chowla.SignSplit
import Salt.Entropy.Chowla.HeadPinLeavesH
import Salt.Entropy.Chowla.HloExportFlatH
import Salt.Entropy.Chowla.AffineFork
import Salt.Entropy.Chowla.StrideFork
import Salt.Entropy.Chowla.StrideBridge
import Salt.Entropy.Chowla.StridePair
import Salt.Entropy.Chowla.StrideDecrement
import Salt.Entropy.Chowla.StrideCombine
import Salt.Entropy.Chowla.StrideReduce
import Salt.Entropy.Chowla.StrideShell
import Salt.Entropy.Chowla.StrideCircle
import Salt.Entropy.Chowla.GoldbachEnergyKcH
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
arXiv:1509.05422v1 (the entropy decrement argument, rung A-R2).
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
  Salt.Entropy.Chowla.log_chowla_two_shell_xi_h
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

/-! ⟦THE L² RESTRUCTURE — stone 4: THE SPINE HEAD TWIN AT THE `K`-FREE `δ₀`⟧ (`SpineFinal`,
2026-07-30, on bank A).  The head's door threshold is now

    δ₀ = cD3/(16·C) · ε / 4        (= c₀·ε/4)      -- NOT c₀·ε/(2K)

The landed `log_chowla_two_budget_head_g(_45)` divided by the frequency count because the `L¹`
seam multiplied the door's grade by `|Ξ_H| ≤ K` (`contradiction_of_mrtDoorXi`'s
`hsmall : K·δ < c₀ε`).  The Ξ-SUMMED `L²` seam reads that grade ONCE, so the budget is
`hbudget2 : ρ < c₀ε` and `K` leaves the `δ`-line entirely — REF-L2-ARITH's certified table
(`δ₀' = 1.1927·10^(-6)`, shares `1/2 + 1/8 + 1/8`, `b = 65.125` against the ceiling `m ≤ 86`,
20 bits of margin).  The derivation is the landed `:944–953` block minus the `K` step:
`ρ ≤ c₀ε/4 < c₀ε` since `c₀ε > 0`, the same strict-margin shape the landed proof got at
`c₀ε/2 < c₀ε`.

`spine_False_core_xi_sq` (private, in-file per the S0-TOWER precedent) is `spine_False_core_xi`
with three forced binder changes and nothing else: the circle-method input is the SQUARED
DIAGONAL socket (`circle_method_estimate_sq`, ONE window `x1` — the shell's only instantiation
— and the SAME constant `C = 1 + 2C₀`, so `hbudget1` is byte-identical); `K`, `_hK`, `H₀xi`,
`hxi` are ABSENT (the summed seam consumes no cardinality hypothesis), hence the floor binder is
`max H₀red H₀D3 ≤ H`; and `hδ : 0 ≤ δ` is ABSENT (the summed seam derives its collision from
`ρ < c₀ε ≤ mass` alone).  ⟦WHERE THE COUNT WENT⟧ `|Ξ_H| ≤ K` moved from the spine to the ROAD,
where `Salt.MR.sum_bigXi_norm_windowExpSum_sq_le` spends it against the SIEVED leg only; only
the head knows `ε`, so `log_chowla_two_budget_head_g_sq_count` EXPORTS the count gate as a
payload conjunct, and `log_chowla_two_budget_head_g_sq` is that head with the conjunct dropped
(one proof between them).  `K` never touches `δ₀`.  The tower payload is the `9/2` law (ruling
C-A); `Salt.MR.tower_conjunct_45_le_five` downgrades it to `^5` free.

⚠ TAO-FAITHFULNESS (mandate R4): the door hypothesis is `MRTUniformityXiL2` EXACTLY as landed —
a finite SUM of integrals, `∑` outside `∫`, no `sup` inside — SUPPLIED by the road
(`Salt.MR.mrtUniformityXiL2_of_absWindowSqBound`), never claimed from Prop 2.4, and in any case
IMPLIED by the landed `L¹` theorem-door (`mrtUniformityXiL2_of_xi`).  Additive: every landed
head and core is byte-untouched. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count
  Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq


/-! ⟦THE BAR-2 NUMERAL WAVE — `Kc` AT ITS LEAF⟧ (`GoldbachEnergyKc`, 2026-08-02).

`logChowla2_ineffective_v2`'s first inner rider `Kc ≤ 2^539` is a rider only because
`bigXi_bounded`'s `∃ C, 0 < C ∧ …` exports POSITIVITY ALONE.  At the flat head's pinned
`ε = 1/500` the count is already explicit (`bigXi_bounded_500`), and the last opacity is
`hFac2_lcm_sum_le`'s `∃ K` at the closed form `exp(24·ζ(2)) = exp(4π²)`.  GB-14b's body is
replayed verbatim here (its per-prime machinery reached with `open private`, so
`GoldbachEnergyHsq2` is untouched) against the numeral `exp 40`, via mathlib's
`hasSum_zeta_two` and `Real.pi_lt_d6`.  The exported ceiling is
`32·exp 40·(2^35)²·500^10 ≤ 2^5·3^40·2^70·500^10 ≈ 2^228.2` — ~310 bits under the rider. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.hFac2_lcm_sum_le_exp40
  Salt.Entropy.Chowla.hFac2_lcm_sum_le_bounded
  Salt.Entropy.Chowla.exp_forty_le_pow40
  Salt.Entropy.Chowla.bigXi_bounded_500_explicit40
  Salt.Entropy.Chowla.bigXi_bounded_500_ceiling
  Salt.Entropy.Chowla.bigXi_bounded_ceiling_of_pin

/-! ⟦AUDIT-ROWS 0802⟧ The eight Trophy-Room gap closures (Entropy's seven):
the two spine terminals + the five tower laws (THE TOLL + THE SHAPE-FREE
TOLL), named by TROPHY's census as sorry-free but ledger-absent. -/
#audit_axioms Salt.Entropy.Chowla.log_chowla_two_budget_head
  Salt.Entropy.Chowla.log_chowla_two_door_only
  Salt.Entropy.Chowla.log_chowla_two_door_only_xi -- the Ξ_H door-only surface beneath
  -- Pi's `thm:spine` (cert: Salt/Certs/ChowlaSpine.lean:14); covered only transitively till 08/15
  Salt.Entropy.Chowla.towerDropSumFlat_ge_log_ratio
  Salt.Entropy.Chowla.towerDropSumFlat_le_log_ratio_mul
  Salt.Entropy.Chowla.towerFlat_width_ge
  Salt.Entropy.Chowla.towerFlat_width_le
  Salt.Entropy.Chowla.towerShape_width_ge
  Salt.Entropy.Chowla.chowlaTowerShape_const
  Salt.Entropy.Chowla.towerLS_const
  Salt.Entropy.Chowla.towerLamS_const
  Salt.Entropy.Chowla.towerWS_const
  Salt.Entropy.Chowla.towerDropSumShape_const
  Salt.Entropy.Chowla.towerShape_flat_le

/-! ⟦WALL-L2 — THE ε-FLOOR CONSUMPTION FENCE⟧ (`SpineEpsFence`, 2026-08-15).

`log_chowla_two_budget_head` is an existential over a SINGLE `ε : ℚ`, chosen by
`exists_rat_btwn` strictly below the four-arm constant `min (min (min (cE/(32·log 4))
(1/2)) (cD3/16)) (cD3/(16·C))`; every downstream terminal inherits that one margin,
and the `MR` mint `logChowla2_ineffective_v7` carries the same shape with the explicit
floor `1/500 ≤ ε` in its `∃`-prefix.  The margin is a CONSTANT, floored by
construction constants.

`spine_eps_constant_floor` restates the head's conclusion VERBATIM (so a change of
shape from single-`ε` to an `∀ ε`-family would stop type-checking here) and adjoins
the fence at that same `ε`: for any consumer demand `W z → 0` — a sieve density at
unbounded `z`, or any rate-form saving — the demand `ε ≤ W z` fails from some scale
on.  `margin_fails_vanishing_demand` is the reusable arrow behind it.

Scope: an interface fact about a landed object's shape, frozen so no future wave
spends a campaign wiring a constant-margin terminal into a slot that needs a rate.
No new claim about Chowla, the door, or twins. -/
#audit_axioms Salt.Entropy.Chowla.margin_fails_vanishing_demand
  Salt.Entropy.Chowla.margin_not_forall_of_vanishing_demand
  Salt.Entropy.Chowla.spine_eps_constant_floor

/-! ⟦WALL-L1 — THE PIN DICHOTOMY⟧ (`PinDichotomy`, 2026-08-15).

THE GUARD.  `TwinDetecting'` is `TransportWall.lean`'s `TwinDetecting` with the
non-twin index held away from `0` (the added conjunct `1 ≤ n`).  It lands BESIDE the
frozen definition and is used only in this file's door and dichotomy statements;
`TransportWall.lean` is byte-untouched.

THE STRENGTH LAW, WITH ITS POLARITY.  `twinDetecting'_imp` freezes the direction in
the kernel: `TwinDetecting' w → TwinDetecting w`.  The guarded notion is the STRONGER
predicate, so the UNGUARDED one gives the stronger wall — substituting `TwinDetecting'`
into `orthogonality_wall` or `no_slot_derived_twin_linkage` would weaken both while
leaving them true and green, a regression the kernel cannot see.

THE ANTI-REPAIR FENCE, in three theorems.  `slack_witness_twinDetecting` exhibits a
weight (`5` at `0`, `1` elsewhere) that passes both slots and satisfies the landed
`TwinDetecting` at `(m, n) = (3, 0)` while detecting nothing — so re-guarding the
landed definition in place would make that statement UNPROVABLE and break the build.
`slack_witness_not_twinDetecting'` shows the guard rejects it, and
`blind_iff_const_fails_unguarded` states the fence from the far side: at the landed
unguarded definition the dichotomy below is FALSE, so the guard is necessary rather
than stylistic.

THE DICHOTOMY.  `blind_iff_const` — inside the slot class, `¬ TwinDetecting' w` iff
`w n = 1` for all `n ≥ 1`.  `pin_iff_detecting` (with `pinned_door` / `pin_minimal`)
is its contrapositive: one pinned sign at `n ≥ 1` is exactly detection, the bottom
element of the detection-sufficient hypotheses above the slots.  `liouville_pinned`
inhabits the other side at the separator `(3, 7)`.  The descent's route carries a
`GF(2)` positive control at `scripts/l1_gf2_control.py`.

Scope: no new claim about twins — boundary-map completion, zero flagship inches. -/
#audit_axioms Salt.Entropy.Chowla.twinDetecting'_imp
  Salt.Entropy.Chowla.slack_witness_twinDetecting
  Salt.Entropy.Chowla.slack_witness_not_twinDetecting'
  Salt.Entropy.Chowla.blind_iff_const_fails_unguarded
  Salt.Entropy.Chowla.blind_iff_const
  Salt.Entropy.Chowla.pin_iff_detecting
  Salt.Entropy.Chowla.pinned_door
  Salt.Entropy.Chowla.pin_minimal
  Salt.Entropy.Chowla.liouville_pinned

/-! ⟦L3-FORK FOUNDATION⟧ — THE SHIFT-`h` DE-SPECIALIZATION (`ShiftFork`, 2026-08-15).

THE FORK, NOT THE EDIT.  The landed spine is Tao arXiv:1509.05422v1 at `(a, b, h) = (1, 0, 1)`.
`ShiftFork.lean` opens the `h`-family BESIDE it: `logChowlaFails`, `bigXiH`,
`MRTUniformityXiH` are new names at new arities, and NO landed declaration changes a
byte or an arity.  In-place generalization was priced and rejected — `logChowla2Fails`
alone is restated across 59 files, `bigXi` across 35 — so the alongside-fork is the
cheap arm and the compat lemmas are what make it conservative:
`logChowla2Fails_eq_logChowlaFails_one` is `rfl`; `bigXi_eq_bigXiH_one` and
`mrtUniformityXi_eq_xiH_one` pin the landed `Ξ`-set and the landed `Ξ`-door as the
`h = 1` members of the new families.

WHERE THE TWIST LIVES.  Tao's `Ξ_H` carries the frequency twist `−hξ/H`
(`chowla.txt:1296-1300`), and it is INVISIBLE at `h = 1` rather than absent.  It goes
into `bigXiH`'s membership predicate and NOWHERE ELSE: the door's `α` stays at the
untwisted `−ξ.val/H`, because the seam consumes the circle method's surviving DFT
factor at the untwisted `ξ` (`Theorem23Shell.lean:188-193`).  A door twisted to
`−(h·ξ.val)/H` would elaborate cleanly and then fail to compose.

THE TRIPWIRE.  No `h = 1` compat can police that spelling — at `h = 1` the twist
vanishes under `Nat.cast_one`, so `mrtUniformityXi_eq_xiH_one` is provable either way.
`contradiction_of_mrtDoorXiH` is the `h`-GENERAL clone of the landed seam
`contradiction_of_mrtDoorXi` (`MRTDoor.lean:127-157`); its termwise step fires the door
at `ξ` against the sum's own integrand, so it closes at general `h` under the untwisted
door and cannot close under a twisted one.  It landed last, and it landed green.

THE COUNT.  `bigXiH_card_le_gcd_mul` is hypothesis-free: `bigXiH h` is the
`μ_h`-preimage of `bigXi` under `ξ ↦ (h : ZMod H)·ξ` (`mem_bigXiH_iff`), whose fibers
are cosets of a kernel of size `gcd(h,H)`.  `bigXiH_bounded` then transfers
`bigXi_bounded` (Tao Lemma 3.5, unconditional) to the `h`-family with the constant
multiplied by `h`, re-deriving no restriction theorem.  `expSum_add_intCast` records the
frequency invariance the two spellings of the twist differ by.

`h = 0` IS DEGENERATE and is fenced, not hidden: `bigXiH 0` is `ξ`-independent and
`gcd(0,H) = H`, so every statement here that manufactures an `H`-uniform constant
(`bigXiH_card_le_mul`, `bigXiH_bounded`) carries `0 < h` explicitly.

SCOPE.  Definitional/foundational only.  `MRTUniformityXiH h` is the `h`-family's OPEN
HYPOTHESIS — for `h ≥ 2` a STRICTLY STRONGER one than the landed `Ξ`-door — and this
file supplies no producer for it, exactly as the corpus supplies none for
`MRTUniformity`.  No claim about Chowla, about the door, or about twins is made or moved.
The pairing/consumer census behind the fork ruling is re-derived mechanically by
`scripts/l3_shift_census.py`. -/
#audit_axioms Salt.Entropy.Chowla.logChowlaFails
  Salt.Entropy.Chowla.logChowla2Fails_eq_logChowlaFails_one
  Salt.Entropy.Chowla.bigXiH
  Salt.Entropy.Chowla.bigXi_eq_bigXiH_one
  Salt.Entropy.Chowla.mem_bigXiH_iff
  Salt.Entropy.Chowla.expSum_add_intCast
  Salt.Entropy.Chowla.bigXiH_card_le_gcd_mul
  Salt.Entropy.Chowla.bigXiH_card_le_mul
  Salt.Entropy.Chowla.bigXiH_bounded
  Salt.Entropy.Chowla.MRTUniformityXiH
  Salt.Entropy.Chowla.mrtUniformityXi_eq_xiH_one
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXiH

/-! ⟦W-F2⟧ — THE `h`-ENGINE ROOM AND THE `L²` FORK (`CircleMethod` + `ShiftFork`, 2026-08-15).

THE ENGINE, AT OFFSET `p·h`.  `circle_method_estimate_h_core` is Tao's Lemma 3.4 (3.18)
run at the correlation offset `p·h`, and `circle_method_estimate_h` is the same statement
over the fork's own set: line for line the landed `circle_method_estimate`
(`CircleMethod.lean:574-585`) with exactly two changes — the offset `j + p` becomes
`j + p·h`, and the Fourier mass is summed over `bigXiH h eps H` instead of `bigXi eps H`.
The DFT factor stays at the UNTWISTED `ξ`, so the twist still lives only in the membership
predicate, and the seam's spelling is untouched.

WHERE THE OBJECTS SIT, AND WHY.  `ShiftFork` IMPORTS `CircleMethod`, so the estimate
cannot be stated over `bigXiH` inside `CircleMethod` — that is an import cycle, and the
build refuses it.  `bigXiTwistFilter` is therefore the same set spelled on the engine-room
side, `bigXiH_eq_twistFilter` is the filter congruence between them, and
`circle_method_estimate_h` is the five-line restatement across the seam.  No landed
declaration moved and no import was added on either side.

THE CONSTANT IS `h·(1 + 2·C₀)`, NOT `h + 2·C₀`.  The periodization's wraparound is `p·h`
places per prime, so the wrap error is `h·|𝒫_H|` and the multiplier lands on the
PERIODIZATION coefficient `C₀`: the binding constraints are `C ≥ 1 + h·C₀` and `C ≥ 2·C₀`,
and `h + 2·C₀` fails the first from `h = 3, C₀ = 3` on.

`0 < h` IS CONSUMED TWICE, and neither use is cosmetic: the constant is positive only for
`h ≥ 1`, and at `H = 1` the window correlation vanishes only because `1 ≤ p·h`
(`Nat.mul_pos`).  At `h = 0, H = 1` the statement is FALSE, not merely unproven.
`liouville_collapse_h` is correctly UNFENCED in `h` — at `h = 0` it degenerates to
`λ(p·N)² = λ(N)²`, still true — and carries only `p ≠ 0`.

THE PRODUCER STORY IS UNCHANGED.  `mrtUniformity_implies_xiH` is the lemma named as
"future" in `MRTUniformityXiH`'s docstring (`ShiftFork.lean:292-295`): it consumes the
`∀ α` door `MRTUniformity`, which this corpus NEVER produces, so no new supply of the
`h`-door exists.  It would hold over any `Finset (ZMod H)` whatever, which is why it
certifies nothing about the door's spelling — `contradiction_of_mrtDoorXiH` remains the
only tripwire that can.

THE `L²` FORK.  `MRTUniformityXiL2H h` is the Ξ-summed `L²` door
(`MRTDoor.lean:187-190`) over `bigXiH h R.eps H`, `mrtUniformityXiL2_eq_xiL2H_one` pins
the landed door as its `h = 1` member, and `contradiction_of_mrtDoorXiL2H` is its seam
with the lower bound transcribed from the landed one at the untwisted `−ξ.val/H`.  For
`h ≥ 2` it binds the `μ_h`-PREIMAGE of `Ξ_H` — INCOMPARABLE to `Ξ_H` in general, of
cardinality `≤ gcd(h,H)·|Ξ_H|` — an independent open hypothesis, implied by the `∀ α` door
and neither implying nor implied by `MRTUniformityXiL2`.  ⚠ The landed prose at
`ShiftFork.lean:281-284` and at `:502-505` of this file calls the `h`-door "strictly
stronger"; that claim is WRONG for the same reason, and its repair is recorded in
`docs/blueprints/flags.md` for a future wave (this one is additive-only).

NOT IN SCOPE, said out loud: the `h`-clone of the `L²` ESTIMATE
(`circle_method_estimate_sq_h`), any `h`-mint, any spine replay.  This wave makes them
REACHABLE, not done.  ⛔ STALE, CORRECTED 08/26 (commission 7b, correction 3):
`circle_method_estimate_sq_h` IS LANDED and audited; only the `h`-mint remains open.  No claim about Chowla, about the door, or about twins is made or
moved, and no statement is made at any particular `h`. -/
#audit_axioms Salt.Entropy.Chowla.bigXiTwistFilter
  Salt.Entropy.Chowla.fourier_split_h
  Salt.Entropy.Chowla.circle_method_estimate_h_core
  Salt.Entropy.Chowla.bigXiH_eq_twistFilter
  Salt.Entropy.Chowla.circle_method_estimate_h
  Salt.Entropy.Chowla.liouville_collapse_h
  Salt.Entropy.Chowla.mrtUniformity_implies_xiH
  Salt.Entropy.Chowla.MRTUniformityXiL2H
  Salt.Entropy.Chowla.mrtUniformityXiL2_eq_xiL2H_one
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2H

/-! ⟦SIGN SPLIT — THE TWO-SIDED MASS FLOOR⟧ (`SignSplit`, 2026-08-15).

THE OBJECTS.  `agreeMass x ω` and `disagreeMass x ω` are the `1/n`-weighted masses of
the two `λ(n)·λ(n+1)` sign classes inside the log-Chowla window `(x/ω, x]`.  Both are
UNCONDITIONAL in `x` and `ω` — no regime hypothesis enters the definitions or the two
identities beneath them, and the filter predicates are integer inequalities decided by
`Int.decLt`.  `λ` vanishes only at `0` and `window_one_le` puts every window element at
`≥ 1`, so the two classes exhaust the window: `agreeMass_add_disagreeMass` is the
partition `A + D = Σ 1/n`, and `agreeMass_sub_disagreeMass` identifies `A − D` with
exactly the sum whose absolute value `logChowla2Fails` compares against `ε·log ω`.  The
`±1` alphabet of `λ` is used in the second identity and in no other proof of the file.

THE FLOOR.  `sign_split_of_not_fails` is parametric in the regime and takes the plain
hypothesis `¬ logChowla2Fails R.eps R.x R.ω`: from the two identities plus
`harmonic_window_bounds` alone, each mass is `≥ ((1 − ε)·log ω − 1)/2`.  There is no
case split, no minimum lemma and no sign hypothesis — `abs_le` and `linarith` close both
conjuncts — and the chain is NON-STRICT end to end, an equality at `A = D`.
`sign_split_quarter_log` weakens it to the `ε`-free `(1/4)·log ω − 1/2` from `R.heps1`
together with `0 ≤ log ω`; that second hypothesis is consumed, since the `(1 − ε) → 1/2`
step multiplies through by `log ω` and would reverse without it.

THE DOOR IT COSTS.  `sign_split_door_only` instantiates the parametric form at the
spine's witnessed regime through `log_chowla_two_door_only_xi`, so its ONE hypothesis is
the `Ξ_H`-restricted MRT door `MRTUniformityXi` — not the `∀ α` door, and nothing else.

NON-VACUITY, IN THE KERNEL.  `regime_logOmega_ge` re-derives `129 ≤ Real.log R.ω` at
every regime from `hωbig`, `heps1` and `hPNTwindow` — the same three ingredients
`Salt.MR.s13_logOmega_ge` runs to the weaker `4`, repeated in the leaf because that file
sits downstream.  Hence `sign_split_pos`: the floor is `≥ 31.75`, not an empty
inequality.  `sign_split_fifth` restates the content against the window's own mass
`Z = Σ 1/n` — each class carries at least `Z/5` — and the constant `5` is what this
route yields, not a sharpness claim.

SCOPE, SAID OUT LOUD.  Log-weighted, at the single `ε` the spine fixes, at ONE regime,
conditional on the door.  It is a non-degeneracy bound: neither sign class is
asymptotically empty in the harmonic weighting on that window.  No statement is made or
moved about Chowla's conjecture, about the supply of the door, or about twins. -/
#audit_axioms Salt.Entropy.Chowla.agreeMass_add_disagreeMass
  Salt.Entropy.Chowla.agreeMass_sub_disagreeMass
  Salt.Entropy.Chowla.regime_logOmega_ge
  Salt.Entropy.Chowla.sign_split_of_not_fails
  Salt.Entropy.Chowla.sign_split_door_only
  Salt.Entropy.Chowla.sign_split_quarter_log
  Salt.Entropy.Chowla.sign_split_pos
  Salt.Entropy.Chowla.sign_split_fifth

/-! ⟦WALL-L5 — THE DOOR CRITERION + DEGENERATE BLINDNESS⟧ (`PinDichotomy`, 2026-08-15).

THE CRITERION.  `door_criterion` adjudicates a whole GENRE at once: for a family `P`
of weights that strengthens the two slots (`hP`) and is insensitive to the value at
index `0` (`hP0`), the family contains a twin-blind member exactly when it contains
the constant weight `1`.  Testing a proposed slot-strengthening for blindness is
therefore a question about one explicit weight, not a search over the family.
`door_criterion_exists` is the hypothesis-lighter form — no `hP0` — whose right side
is "the family contains a weight that is constantly `1` on `n ≥ 1`".  Both run
through `blind_iff_const` and add no new mathematics; they package it.

THE ZERO FENCE, IN THE KERNEL.  `hP0` is not decoration.
`door_criterion_needs_zero_blindness` proves that the `hP0`-free statement is FALSE,
off `P := (· = slackWitness)`: that weight passes both slots and fails
`TwinDetecting'`, so the left side holds, while the right side would identify it with
the constant weight — and it carries `5` at index `0`.  Neither slot ever reads index
`0`, so the blind point of `blind_iff_const` is a point IN THE VALUES AT `n ≥ 1`, and
the fibre over it is inhabited.

WHICH SLOT DOES THE COLLAPSING.  Outside the `±1` alphabet the picture is the
opposite of a single point.  `corr_zero_blind`: every weight whose pair correlation
`n ↦ w n · w (n+2)` vanishes identically fails the detection clause — that is every
weight whose support contains no pair `{n, n+2}`, an uncountable family, with
`delta1w` (`delta1w_corr`, `delta1w_blind`) as the kernel-borne instance.  And
detectors are there too: `chi4w_detecting'` separates `(3,5)` from `(2,4)`.  Both
weights satisfy slot 2 (`delta1w_pairCollapse`, `chi4w_pairCollapse`) and fail slot 1
(`delta1w_not_pmNormalized`) — so slot 2 alone permits a detector and an uncountable
blind family side by side, and it is slot 1's `±1`-normalization that collapses
WALL-L1's blind set to the single point.

Scope: boundary-map completion, additive in `PinDichotomy.lean`; `TransportWall.lean`
stays byte-frozen and no landed statement changes.  No claim about Chowla, about the
door's supply, or about twins.  The criterion reaches only families that STRENGTHEN
the frozen sharp slots: the probe's literal candidate-3 slot 1 (the windowed
first-moment budget) does not imply `PmNormalized`, so `hP` is unavailable there. -/
#audit_axioms Salt.Entropy.Chowla.chi4w
  Salt.Entropy.Chowla.delta1w
  Salt.Entropy.Chowla.chi4w_detecting'
  Salt.Entropy.Chowla.chi4w_detecting
  Salt.Entropy.Chowla.chi4w_pairCollapse
  Salt.Entropy.Chowla.corr_zero_blind
  Salt.Entropy.Chowla.delta1w_corr
  Salt.Entropy.Chowla.delta1w_blind
  Salt.Entropy.Chowla.delta1w_pairCollapse
  Salt.Entropy.Chowla.delta1w_not_pmNormalized
  Salt.Entropy.Chowla.door_criterion_exists
  Salt.Entropy.Chowla.door_criterion
  Salt.Entropy.Chowla.door_criterion_needs_zero_blindness

/-! ⟦W-F3 WAVE A⟧ — THE F-BRIDGE AT SHIFT `h`: DEFINITIONS AND THE OFFSET-AGNOSTIC BOXES
(`FBridge` + `OuterCombine`, 2026-08-20).

WHY ONLY A WAVE.  The W-F3 design block claimed the `h`-shell was a one-parameter transport;
two refuters killed that framing.  `fBridgeG`'s own docstring names `h = 1` among the model
values `(a,b,h,c_p) = (1,0,1,1)`, so the F-bridge BENEATH the shell is hard-coded at the
offset the shell proposed to vary, and the offset-1 and offset-`p·h` correlations are not
defeq.  The refuters split the work; this stanza is WAVE A, the part both agreed is genuine
transport.

⚠️ THE TWO `1`s.  The `h`-port does NOT touch the gate, and the wave brief that ordered it
said otherwise.  `fBridgeG`'s gate `((j + 1 : ℕ) : ZMod p) = -r` carries the window's
1-INDEXING OFFSET, not the shift: `windowVal H (liouvilleWindow H n) j = λ(n+j+1)`, so Tao's
1-indexed `j` is our `j + 1`.  Tao's indicator `1_{ay+j ≡ pb (mod ap)}` mentions no `h`, and
`fBridgeF_liouville_apply` (`Prop26.lean:87`) proves in the kernel that the gate evaluates to
`p ∣ n + j + 1` — a condition on the FIRST factor's argument, which is exactly what feeds
multiplicativity: at `n+j+1 = p·m`, `λ(p m)·λ(p m + p h) = λ(m)·λ(m + h)` is the shift-`h`
correlation.  A gate moved to `p ∣ n + j + h` would leave `λ(n+j+1)` with no factor of `p`
and kill the reduction Wave B has to run.  Both spellings agree at `h = 1`, so NO `h = 1`
compat lemma can separate them — the same tripwire shape `ShiftFork` records for the twist.
The gate here therefore stays `(j + 1)`; only the second factor's index carries `h`.

WHAT LANDS.  `fBridgeG_h` / `fBridgeF_h` reopen the parameter the docstring froze: the
product base index becomes `j + p·h`.  The four deterministic bounds follow at general `h`
because they never read the offset: `windowVal_prod_abs_le` bounds every term by `1` blind to
its arguments, and the gate does not mention `h`, so `card_filter_natCast_eq_le` applies at
`-r - 1` verbatim.  `boxGrade` and `boxSum_le_grade` are statements about the window primes
alone, so the `H/log H` grade transfers with no arithmetic changed.  MEASURED: all four
bounds ported with their `h = 1` proof scripts intact — none was offset-sensitive.

THE COMPATS ARE NOT `rfl`.  `fBridgeG_h_one` / `fBridgeF_h_one` need `Nat.mul_one`: `(p : ℕ)
* 1` whnf-reduces to `0 + p`, stuck for a variable `p`.  Same shape as `bigXi_eq_bigXiH_one`.

SCOPE — THE WAVE BOUNDARY, STATED.  NOTHING downstream of the deterministic box is ported
here, because nothing downstream is offset-agnostic: no `badSet` at `h`, no `fBridgeG_h_mean`,
no `fBridgeG_h_sum_over_residues`, no `fBridge_concentration*` at `h`, no `outer_combine` at
`h`, no `(2.11)` restated at shift `h`, and no terminal.  Those are waves B (the
concentration/entropy heart, campaign-tier, needs its own design block) and C.  Nothing in
this wave required them — the boundary held.  Every `h = 1` declaration in both files is
byte-frozen and keeps its proof; the new names sit BESIDE them.  No claim about Chowla, about
the door's supply, or about twins is made or moved by this wave. -/
#audit_axioms Salt.Entropy.Chowla.fBridgeG_h
  Salt.Entropy.Chowla.fBridgeF_h
  Salt.Entropy.Chowla.fBridgeG_h_one
  Salt.Entropy.Chowla.fBridgeF_h_one
  Salt.Entropy.Chowla.fBridgeG_h_abs_le
  Salt.Entropy.Chowla.fBridgeG_h_mem_Icc
  Salt.Entropy.Chowla.fBridgeF_h_abs_le_boxSum
  Salt.Entropy.Chowla.decoupledMean_h_abs_le_boxSum
  Salt.Entropy.Chowla.fBridgeF_h_abs_le_box
  Salt.Entropy.Chowla.decoupledMean_h_abs_le_box

/-! ⟦W-F3 WAVE B, NODE B-1⟧ — THE DEVIATION SET AT SHIFT `h` (`Transport`, 2026-08-21).

WHAT LANDS.  `badSet_h` — `badSet` with the bridge replaced by wave A's `fBridgeF_h` and the
decoupled mean's second window index moved from `j + p` to `j + p·h` — together with its
`h = 1` compat `badSet_h_one`.  This is the FIRST object past the deterministic box, i.e. the
first place wave A's declared boundary ("no `badSet` at `h`") is crossed on purpose.

⚠️ THE THREE SYNCHRONISED SITES.  Byte-identity at shift `h` is not a property of one
definition.  The offset is spelled independently at three places: this predicate, the
concentration lemma's deviation set (wave B-2/B-3), and `outer_combine`'s own conclusion
(`OuterCombine.lean:363-364`, which today reads `j + (p : ℕ)` with NO `* h`).  Wave A fixed
the target spelling at `OuterCombine.lean:150` as `windowVal H v (j + (p : ℕ) * h)`; `badSet_h`
matches it verbatim, and the remaining two sites are B-2/B-3 and B-4's obligation, not this
node's.  B-1 lands site 1 only, and says so.

THE COMPAT IS NOT `rfl`, AND FAILS ON BOTH ITS SITES.  `badSet_h_one` needs `fBridgeF_h_one`
for the bridge AND `Nat.mul_one` for the window index; `(p : ℕ) * 1` is stuck for a variable
`p`.  MEASURED with negative controls, not assumed: bare `rfl` reports the two sides not
definitionally equal; dropping `Nat.mul_one` from the rewrite leaves the goal `j + ↑p * 1`
against `j + ↑p`; dropping `fBridgeF_h_one` leaves `fBridgeF_h eps H 1` against `fBridgeF`.
Same shape as `fBridgeG_h_one` / `fBridgeF_h_one` in wave A.

SCOPE.  A definition and one equation.  Nothing about the concentration exponent, the
entropy transport, `badSet_transport`, or `outer_combine` moves; every `h = 1` declaration in
`Transport` stays byte-frozen and the new names sit BESIDE them.  No claim about Chowla,
about the door's supply, or about twins is made or moved by this node. -/
#audit_axioms Salt.Entropy.Chowla.badSet_h
  Salt.Entropy.Chowla.badSet_h_one


/-! ⟦W-F3 WAVE B, NODES B-2 + B-3⟧ — THE MEAN AND CONCENTRATION CONE AT SHIFT `h`
(`FBridge`, `Decoupled`, 2026-08-21).

WHAT LANDS.  The eight-object mean/concentration cone at shift `h`, i.e. everything between
wave A's deterministic box and `outer_combine`.  MEAN: `fBridgeG_h_sum_over_residues` (the
numerator), `fBridgeG_h_mean`, `fBridgeF_h_mean`.  CONCENTRATION:
`fBridge_h_concentration_raw`, `fBridge_h_concentration`, `fBridge_h_concentration_sharp`,
`fBridge_h_concentration_decoupled`, `fBridge_h_concentration_decoupled_sharp`.  Wave A's
declared boundary named `fBridgeG_h_mean`, `fBridgeG_h_sum_over_residues` and
`fBridge_concentration*` at `h` as the not-yet-ported list; all of it is now ported.

THE CENSUS, AND WHAT IS *NOT* IN THE CONE.  The Hoeffding substrate is entirely
offset-blind and needed NO `_h` port: `residueProj_fiber_card` never mentions the pattern
`v`, and `fBridge_varTerm` / `window_lb` / `fBridge_var_le` / `fBridge_var_le_sharp` are
statements about the window primes and the box endpoints alone.  All four are REUSED
VERBATIM.  Consequently the shift costs NOTHING in the concentration grade: the exponents of
`fBridge_h_concentration` and `fBridge_h_concentration_sharp` are character-for-character the
`h = 1` exponents.  Every proof script transferred with only names and the product index
changed; no estimate was re-derived and none was weakened.

⚠️ SITE 2 OF THE THREE SYNCHRONISED SITES IS NOW LANDED.  `fBridgeF_h_mean`,
`fBridge_h_concentration_decoupled` and `fBridge_h_concentration_decoupled_sharp` spell the
offset independently of `badSet_h`; all three use wave A's fixed target spelling
`windowVal H v (j + (p : ℕ) * h)` (`OuterCombine.lean:150`), byte-identical to site 1.
SITE 3 — `outer_combine`'s own conclusion (`OuterCombine.lean:363-364`) — still reads
`j + (p : ℕ)` with no `* h` and is UNTOUCHED: it is node B-4's obligation.

THE `h = 1` RECOVERIES: EXACTLY TWO REWRITES EACH, BUT NOT THE SAME TWO.  B-2/B-3 introduce
no new DEFINITION, so there is no compat EQUATION to state and none is landed (landing one
would duplicate an already-frozen theorem).  The obligation that remains is that the `h = 1`
instance recovers the frozen original, and it was MEASURED, with a negative control per
rewrite, never asserted.  Result: never `rfl`, always exactly two rewrites, and the PAIR
VARIES WITH THE SPELLING THE STATEMENT CARRIES —
`fBridgeG_h_sum_over_residues` / `fBridgeG_h_mean`: `fBridgeG_h_one` + `Nat.mul_one`;
`fBridgeF_h_mean` / `fBridge_h_concentration_decoupled`: `fBridgeF_h_one` + `Nat.mul_one`;
the UN-decoupled `fBridge_h_concentration_raw` (and `_concentration`, `_sharp`): the
statement carries NO product index at all, so `Nat.mul_one` does nothing and the pair is
`fBridgeF_h_one` + `fBridgeG_h_one` instead.  Controls, all run: omitting `Nat.mul_one`
leaves `j + ↑p * 1` against `j + ↑p`; omitting `fBridgeG_h_one` leaves
`fBridgeG_h eps H 1 v p` against `fBridgeG eps H v p`; omitting `fBridgeF_h_one` leaves
`fBridgeF_h eps H 1 v` against `fBridgeF eps H v`; with no rewrite at all BOTH residuals
appear together.

SCOPE.  Eight statements, no new definitions, no new axioms.  Nothing about `badSet_transport`,
the entropy transport, `outer_combine`, `(2.11)`, or the terminal moves; those are B-4 and
wave C.  Every `h = 1` declaration in `FBridge` and `Decoupled` stays byte-frozen and the new
names sit BESIDE them.  No claim about Chowla, about the door's supply, or about twins is made
or moved by these nodes. -/
#audit_axioms Salt.Entropy.Chowla.fBridgeG_h_sum_over_residues
  Salt.Entropy.Chowla.fBridgeG_h_mean
  Salt.Entropy.Chowla.fBridgeF_h_mean
  Salt.Entropy.Chowla.fBridge_h_concentration_raw
  Salt.Entropy.Chowla.fBridge_h_concentration
  Salt.Entropy.Chowla.fBridge_h_concentration_sharp
  Salt.Entropy.Chowla.fBridge_h_concentration_decoupled
  Salt.Entropy.Chowla.fBridge_h_concentration_decoupled_sharp

/-! ⟦W-F3 WAVE B, NODE B-4⟧ — THE OUTER ASSEMBLY AND THE CALIBRATION AT SHIFT `h`
(`Transport`, `OuterCombine`, 2026-08-21).  ⭐ SITE 3 CLOSES; the three-site obligation is
discharged.

WHAT LANDS — FIVE OBJECTS, and the count is the design block's "5" with a DIFFERENT
MEMBERSHIP.  `badSet_transport_h`, `badSet_transport_at_calibration_h` (`Transport`);
`outer_badMass_h_eq`, `outer_badMass_h_le`, `outer_combine_h` (`OuterCombine`).  Wave A's
declared boundary named `outer_combine` at `h` and `(2.11)` restated at shift `h` as its last
two not-yet-ported items; both are now ported, and wave A's list is exhausted.

⭐ SITE 3 OF THE THREE SYNCHRONISED SITES — CLOSED.  `outer_combine`'s conclusion spells the
two-point offset INDEPENDENTLY of site 1 (`badSet_h`, `Transport`) and site 2 (the decoupled
concentration deviation sets, `FBridge`/`Decoupled`); at `h = 1` it reads
`windowVal H (liouvilleWindow H n) (j + (p : ℕ))`, with no `* h`.  `outer_combine_h` writes
wave A's fixed target spelling `windowVal H v (j + (p : ℕ) * h)` (`OuterCombine.lean:150`).
VERIFIED BY `grep -F` ON THE LITERAL, NOT BY EYE: the string `(j + (p : ℕ) * h) : ℝ)` occurs at
site 1 (`Transport.lean:203`), site 2 (`FBridge.lean:789`, `Decoupled.lean:107`) and site 3
(`OuterCombine.lean:638`); after `OuterCombine.lean:436` — the whole B-4 block — the unshifted
literal `(j + (p : ℕ)) : ℝ)` occurs ZERO times.

⛔⛔ CORRECTED 2026-08-21: THIS PARAGRAPH SAID "ALL THREE SITES AGREE" AND THE AGREEMENT
POPULATION IS **SIX FILES**, NOT THREE.  Measured (`grep -rF '(j + (p : ℕ) * h) : ℝ)' Salt/`):
`CircleMethod` · `FBridge` · `OuterCombine` · `Decoupled` · `Transport` · `ShiftFork`.  Two of
them — `circle_method_estimate_h` (`ShiftFork.lean:405`) and `circle_method_estimate_h_core`
(`CircleMethod.lean:1133`) — already carried the identical literal BEFORE wave A opened.
⇒ "THREE SITES" COUNTED WHAT THE ENTROPY CONE HAD TO **MOVE**; IT NEVER COUNTED WHAT MUST
**AGREE**.  The migration population and the agreement population are different sets, and this
file asserted the second while enumerating the first.
⚠️ AND THE NUMBER IS WRONG ON A SCHEDULE, NOT WRONG NOW.  Measured across B-5's five-file stack
(`HBudget`, `HReduce`, `HMainAssembly`, `Prop26`, `ChowlaFailure`) the SHIFTED literal occurs
**0** times, against **15** frozen offset-carrying lines (14 in `HBudget`, 1 at `Prop26:92`);
positive control `Transport.lean` = 2 shifted, so the zero is a real zero.  ⇒ **B-5 does not
INHERIT the agreement population — it CREATES it, and "six" becomes stale the moment B-5 lands.**
⇒ WHEN YOU EXTEND THIS FAMILY, RE-RUN THE `grep -F` AND UPDATE THIS PARAGRAPH.  A count of a
growing population belongs beside the command that produced it, never on its own.

⛔⛔ USE THIS SCOPED ARM, NOT THE UNSCOPED ONE ABOVE — THE UNSCOPED COMMAND COUNTS THIS FILE'S
OWN PROSE, AND IT RATCHETS: every correction that QUOTES the literal in order to explain it adds
another hit, so the census gets one file harder to read each time somebody does the right thing.
    grep -rlF '(j + (p : ℕ) * h) : ℝ)' Salt/Entropy/Chowla/     ⇒ EXPECT EXACTLY 8 FILES
    If it returns more, OPEN THE EXTRA HITS BEFORE BELIEVING THEM — a quotation is not a
    declaration.  (Scoping beats `--exclude=All.lean`, which rots the day this file carries a
    real declaration; measured, it carries ZERO — `grep -cE '^(theorem|lemma|def|private|
    noncomputable)[[:space:]]'` = 0 here, = 8 in `Transport.lean` as the positive control.
    ⚠️ WITHOUT the trailing whitespace class that pattern returns 4 — `defeq`, `definition`,
    `definitionally`, `defect`: ENGLISH PROSE AT COLUMN 0.  The word boundary is load-bearing.)

⛔ AND THE BYTE-IDENTITY CLAIM CARRIES ONE NAMED EXCEPTION — 15/16, NOT 16/16.  `HBudget:1381`
spells the shifted offset `(j + p * h) : ℝ)` with a BARE `p`, because it faithfully mirrors the
FROZEN `(j + p) : ℝ)` at `HBudget:664`.  ⇒ THE FROZEN SIDE WAS NEVER BYTE-UNIFORM EITHER: this
file holds 14 of `(j + (p : ℕ)) : ℝ)` and 1 of `(j + p) : ℝ)`.  The port was right to mirror the
spelling it found rather than normalise it — but every "byte-identical across N files" sentence
in this wave, including the ones above, was asserted about a population NOBODY HAD CHECKED FOR
UNIFORMITY ON THE FROZEN SIDE.  Check the source spelling before claiming identity with it.

✅ RE-RUN AND UPDATED 2026-08-21 BY B-5 (the paragraph above is now a record of the PRE-B-5
world; do not read its `0`/`15`/`six` as current).  Command, verbatim:
`grep -rlF '(j + (p : ℕ) * h) : ℝ)' Salt/`.  The agreement population is now **EIGHT SOURCE
FILES**: `CircleMethod` (8) · `Decoupled` (3) · `FBridge` (10) · `HBudget` (14) ·
`OuterCombine` (8) · `Prop26` (1) · `ShiftFork` (1) · `Transport` (2) — plus this file's own
prose.  B-5 added TWO members, `HBudget` and `Prop26`.
⛔ AND THE PREDICTION WAS WRONG BY ONE, FROM ITS OWN MEASUREMENT.  The B-5 brief said "your
landing makes it SEVEN" while the same brief's census said the frozen lines sit in TWO files
("14 in `HBudget`, 1 at `Prop26:92`").  A stack that carries the offset in two files adds two
members, not one.  ⇒ A POPULATION FORECAST MUST BE DERIVED FROM THE CENSUS THAT SITS BESIDE
IT — this one contradicted its own table and nobody noticed until the grep was re-run.
The frozen literal `(j + (p : ℕ)) : ℝ)` is UNCHANGED at 14 in `HBudget` and RISES 1 → 2 in
`Prop26`, the new one being `fBridgeF_h_liouville_apply_one`, whose whole job is to restate
the LANDED unshifted conclusion.  A frozen-spelling count going UP is the compat working, not
a regression: check WHICH declaration owns the new line before reading a rise as a defect.

⚠️ THE THREE-SITE ROSTER UNDERCOUNTS THE SHIFT-`h` OFFSET POPULATION — census finding, not a
defect.  Two MORE declarations already spelled the offset at shift `h` before wave A opened:
`circle_method_estimate_h` (`ShiftFork.lean:397`) and `circle_method_estimate_h_core`
(`CircleMethod.lean:1125`), both in the TWO-pattern `x1`/`x2` family.  Both already use the
identical literal, so byte-identity in fact holds across FIVE sites.  The wave's "three sites"
counts the sites the entropy cone had to MOVE; it is not the census of the sites that must
AGREE.  A future shift-`h` port should enumerate by the literal, not by the roster.

THE SHIFT COSTS NOTHING, THIRD CONFIRMATION.  The `(t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t`
mass bound, the `(2+ε²)² ≤ 9` calibration step, the sharp exponent
`δ²·log H/(2 C₀ ε²H (2/ε²+1)²)`, its `ε⁶H/(18 C₀ log H)` lower bound and the full error term
`ε²H/log H + 2·boxGrade·(…)` are character-for-character the `h = 1` ones.  No estimate was
re-derived; none was weakened.  `boxGrade`, `boxSum_le_grade`, `uniformOn_univ_real_coe`,
`weakUniform_spine` and `decrement_markov_fintype` are `h`-FREE — checked in their statements,
not assumed from their names — and are REUSED VERBATIM with no `_h` port.

THE `(2.11)` AT SHIFT `h`, STATED PRECISELY.  There is no standalone `(2.11)` declaration:
`(2.11)` enters as `outer_combine`'s hypothesis `h211`.  `outer_combine_h` restates it at shift
`h` by carrying `fBridgeF_h eps H h` in place of `fBridgeF` — that is the whole roster item.
The `(2.11)` PRODUCER chain (`ChowlaFailure.lean`, including its `outer_combine` seam
kill-check) and every `h = 1` consumer of `outer_combine` (`Theorem23Shell` ×3, `SpineClose`,
`SpineFinal`, `HloExport*`, `S16Uniform`) are UNTOUCHED and remain at `h = 1`: door/wave-C
surfaces, named here so the next wave does not have to rediscover them.

THE `h = 1` RECOVERY IS A THIRD SHAPE — ONE REWRITE LEMMA, NOT TWO.  B-1 needed
`fBridgeF_h_one` + `Nat.mul_one`; B-2/B-3 needed that pair or `fBridgeF_h_one` +
`fBridgeG_h_one`.  Four of B-4's five objects mention NEITHER the bridge nor the product index
in the clear — both are sealed inside `badSet_h` — so the entire recovery is B-1's compat
EQUATION `badSet_h_one`, alone.  `outer_combine_h` is the exception: it carries the bridge in
`h211` AND the product index in its conclusion, so it needs `fBridgeF_h_one` + `Nat.mul_one`,
B-2/B-3's second pair.

AND THE TACTIC IS NOT THE LEMMA — a sub-finding the count would have hidden.  `badSet_h_one`
suffices for `badSet_transport_at_calibration_h` under a plain `rw`, but on
`outer_badMass_h_eq` a plain `rw` FAILS OUTRIGHT with "did not find an occurrence": both of
that statement's `badSet_h` occurrences sit UNDER BINDERS (`{n | …}` and the `∫ x₀`), which
`rw` cannot enter.  `simp only [badSet_h_one]` is required.  Same lemma, same count, different
tactic — because of where the occurrence sits, not what it is.

FIVE NEGATIVE CONTROLS, ALL RUN, ALL FAILING AS REQUIRED (measured, never asserted):
dropping `badSet_h_one` from `outer_badMass_h_eq`'s recovery leaves `badSet_h eps H 1` against
`badSet` at both occurrences; using `rw` instead of `simp only` there fails to find the pattern
at all; dropping it from `badSet_transport_at_calibration_h`'s recovery leaves the same
residual at one occurrence; dropping `Nat.mul_one` from `outer_combine_h`'s recovery leaves
`j + ↑p * 1` against `j + ↑p`; dropping `fBridgeF_h_one` leaves `fBridgeF_h eps H 1` against
`fBridgeF`.  As in B-2/B-3, no compat EQUATION is landed for these five — they are theorems,
and landing one would duplicate an already-frozen theorem.

SCOPE.  Five statements, no new definitions, no new axioms, a purely additive diff.  Every
`h = 1` declaration in `Transport` and `OuterCombine` stays byte-frozen and the new names sit
BESIDE them.  The terminal, the `(2.11)` producer and every downstream consumer are wave C.
No claim about Chowla, about the door's supply, or about twins is made or moved by this node. -/
#audit_axioms Salt.Entropy.Chowla.badSet_transport_h
  Salt.Entropy.Chowla.badSet_transport_at_calibration_h
  Salt.Entropy.Chowla.outer_badMass_h_eq
  Salt.Entropy.Chowla.outer_badMass_h_le
  Salt.Entropy.Chowla.outer_combine_h

/-! ⟦W-F3 WAVE B · B-5⟧ — THE SHIFT-`h` PORT OF THE FIVE-FILE BUDGET STACK
(`ChowlaFailure` → `Prop26` → `HReduce` → `HMainAssembly` → `HBudget`, 2026-08-21).
⭐ THE WAVE'S LAST NODE. 16 public + 11 private declarations, ONE new definition, +1178/−0.

THE ONE NEW DEFINITION.  `shiftCorrH x ω k h = ∫ λ(n+k)·λ(n+k+h)` (`HBudget`, `private`, as
its three frozen siblings are).  `shiftCorr` hardcodes the GAP to `1`; `k` is the BASE offset
and telescopes, `h` is the gap and does not.  `shiftCorrH_one` is `rfl`.
⚠️ VISIBILITY IS REPORTED, NOT DECIDED: nothing outside `HBudget.lean` can name it.  That
mirrors the frozen sibling exactly, but a downstream consumer would need it un-privated, and
that is a visibility change for a session that owns the decision.

WHERE THE SHIFT IS PAID — ONE SLICE OF THREE, AND THE GATE IS **LINEAR IN `ε·h`**.  The
`1/8 + 1/16 + 1/16 = 1/4` budget line is UNCHANGED and carries no new term (there is no slack
in that sum; a new term would have been a design act).  Totals 1 and 2 are `h`-FREE, and that
is a measurement, not an assumption: `dilation_error_div` is generic in `f`,
`dilated_window_stability` is generic in `g`, and `corr_shift_le` already takes TWO
INDEPENDENT OFFSETS — so `perPair_collapse_h` is `corr_shift_le k (k+h)` with no new analysis
and the `3ω/x/Z` shift constant never sees the gap.  Total 3, the boundary slice, is the whole
cost: the boundary set becomes `{j < H : H ≤ j + p·h}`, gains exactly one factor `h`, and the
landed gate `ε ≤ c/(32·log 4)` becomes `ε·h ≤ c/(32·log 4)`.  `hbudget_h_gate_implies_epssq_h`
is the seam that feeds that binder — BYTE-IDENTICALLY — into the pre-landed rider
`epsh_gate_implies_epssq_h`, yielding K1's `ε²·h < 1`.  The rider is USED, not re-derived.

⛔ `0 < h` IS FORCED, AND THE BRIEF DID NOT PREDICT IT.  `per_term_h` is where: at `h = 0` the
shifted boundary gate `j + p·h < H` degenerates to `j < H` and no longer bounds `p`, so the
residue bound `r ≤ x/ω` — which the `h = 1` script gets FREE from `j + p < H` — fails.  This
propagates to `hbudget_holds_h` and `hreduce_holds_final_h` as a hypothesis.  It agrees with
`ShiftFork`'s own "`h = 0` is degenerate" note about `logChowlaFails 0`, arrived at from the
opposite end: there it is the Prop that degenerates, here it is the PROOF that loses a bound.

⭐ `boundary_card_le` NEEDED NO PORT — the brief's range list named it (`:428-439`) as part of
the hard step, and it is stated at an ARBITRARY second argument, so `boundary_card_le H (p*h)`
already IS the shifted count `≤ p·h`.  ⇒ A LEMMA STATED GENERICALLY IS ALREADY PORTED; check
the statement's own generality before pricing a port.

⛔ ONE DUPLICATION, DELIBERATE AND FLAGGED.  `collapse_identity_h`/`liouville_sq_h` are
re-proved `private` in `HBudget` although `ShiftFork.lean:434` already has the identical
public `liouville_collapse_h`, and `DilationStability` has the `h = 1` pair.  Reason:
`DilationStability`'s are `private`, and `ShiftFork` is NOT in `HBudget`'s import closure
(both import `ChowlaFailure`; neither imports the other), so reuse would mean ADDING AN IMPORT
to a landed file — a structural change this node does not own.  Reported, not silently chosen.

THE IMPORT CYCLE THAT SHAPED THE STATEMENT.  `singleCorr_of_fails_h`'s hypothesis is the
INEQUALITY that `logChowlaFails h eps x ω` unfolds to, not the named Prop, because `ShiftFork`
IMPORTS `ChowlaFailure` and naming it there would close a cycle.  Verified by seam probe, not
by eye: an `example` feeding a `logChowlaFails h eps x ω` hypothesis straight into
`singleCorr_of_fails_h` elaborates with no coercion.

THE `h = 1` RECOVERY IS A FOURTH SHAPE, AND THE TWO COMPATS OF THIS NODE ARE NOT ALIKE.  The
GAP compat `shiftCorrH_one` is `rfl` (the gap enters as `_ + h`, and `Nat.add` recurses on its
second argument, where a literal `1` reduces).  The OFFSET compat is not (`(p : ℕ) * 1` is
STUCK for a variable `p`), and `fBridgeF_h_liouville_apply_one` therefore routes through the
landed `fBridgeF_h_one` instead.  Under the `∫ n, …` binder the bridge compat needs
`simp only`; `rw` fails outright — the same shape B-4 measured on `outer_badMass_h_eq`.
`hbudget_holds_h_one`'s gate additionally needs `push_cast; linarith` for `ε·((1:ℕ):ℝ)`.

FIVE NEGATIVE CONTROLS, ALL RUN, ALL FAILING AS REQUIRED (and three positive controls passing
beside them, so the suite is not vacuous): `rw [fBridgeF_h_one]` under the integral binder →
"did not find an occurrence of the pattern"; dropping `fBridgeF_h_one` → type mismatch;
`exact heps_small` for the `ε·((1:ℕ):ℝ)` gate → type mismatch; `windowVal H v (j + p*1) =
windowVal H v (j + p) := rfl` → type mismatch; `fBridgeF_h_liouville_apply_one := rfl` → type
mismatch.  Passing beside them: the `logChowlaFails` seam, `simp only [fBridgeF_h_one]`, and
`push_cast; linarith`.

SCOPE, AND WHAT IS **NOT** CLAIMED.  Every `h = 1` declaration in all five files stays
byte-frozen (+1178/−0, zero deletions).  `hbudget_holds_h` is the shift-`h` error budget and
`hreduce_holds_final_h` its capstone; both inherit — UNCHANGED — the `h = 1` chain's standing
conditional status.  In particular `HMainAssembly`'s resolved-stale gate-fix flag and
`HReduce`'s CARRIER-GAP note are `h`-BLIND and neither improved nor worsened by this node.  No
claim about Chowla, about the door's supply, or about twins is made or moved here. -/
#audit_axioms Salt.Entropy.Chowla.singleCorr_of_fails_h
  Salt.Entropy.Chowla.singleCorr_of_fails_h_one
  Salt.Entropy.Chowla.h211_of_logChowla2Fails_h
  Salt.Entropy.Chowla.fBridgeF_h_liouville_apply
  Salt.Entropy.Chowla.fBridgeF_h_liouville_apply_one
  Salt.Entropy.Chowla.perPair_dilation_h
  Salt.Entropy.Chowla.fBridge_of_singleCorr_h
  Salt.Entropy.Chowla.consumability_probe_h
  Salt.Entropy.Chowla.hreduce_close_h
  Salt.Entropy.Chowla.hreduce_close_h_one
  Salt.Entropy.Chowla.hreduce_holds_h
  Salt.Entropy.Chowla.hreduce_holds_h_one
  Salt.Entropy.Chowla.hbudget_holds_h
  Salt.Entropy.Chowla.hbudget_h_gate_implies_epssq_h
  Salt.Entropy.Chowla.epsh_gate_implies_epssq_h
  Salt.Entropy.Chowla.hbudget_holds_h_one
  Salt.Entropy.Chowla.hreduce_holds_final_h
  -- ⭐ ROLLED IN 2026-08-26 (math), discharging QUEUE P1 item 5c's "REPORTED, NOT FIXED".
  -- `log_chowla_two_shell_xi_sq` (`Theorem23Shell.lean:362`) is a LANDED terminal with two
  -- consumers (`HloExport.lean:362`, `HloExportFlat.lean:196`), and three of its four family
  -- members were already audited above (`:163-165`) — it alone was gated by no build.
  -- ⛔ PLACED AT THE END OF THE LIST ON PURPOSE, not beside its siblings: `#audit_axioms`
  -- `throwError`s on the first non-whitelisted dependency and ABORTS the rest of its list, so a
  -- name whose axioms nobody has measured belongs where a failure can mask nothing.
  -- 📌 This asserts NOTHING about its cleanliness — that was 5c's exact objection to rolling in
  -- an unmeasured declaration. It SUBJECTS it to the gate; the build is what measures.
  Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq
  -- ⭐ P2 item 7, first half (2026-08-26, math): the empty cell of the split grid.
  -- `fourier_split_sq_h` has NO consumer yet (`circle_method_estimate_sq_h` is the second half
  -- of the row and is not built), so unlike `fourier_split_sq` — whose axioms ride its audited
  -- consumers — this one is gated by nothing until it is listed here. Same reasoning as
  -- `log_chowla_two_shell_xi_sq` above, and same placement rule: END of the list, because
  -- `#audit_axioms` aborts its remainder on a throw.
  Salt.Entropy.Chowla.fourier_split_sq_h
  -- ⭐ P2 item 7, first object COMPLETE (2026-08-26, math): the top-level twin of the split above.
  -- With this landed, `fourier_split_sq_h` now HAS a consumer and its own row above is redundant
  -- rather than load-bearing — kept, not removed, because a row that was correct when written is
  -- cheaper to leave than to re-audit. ⭐ AMENDED 2026-09-01: this core is consumed ONE LAYER OUT
  -- (`circle_method_estimate_sq_h` → `log_chowla_two_shell_xi_sq_h`); the `bigXiH` wrapper still
  -- belongs on the `ShiftFork` side (that module imports CircleMethod, so naming its objects here
  -- would be an import cycle). No longer a dead socket.
  Salt.Entropy.Chowla.circle_method_estimate_sq_h_core
  -- ⭐ P2 item 7's NAMED object (2026-08-26, math): the `bigXiH`-facing wrapper, mirroring
  -- `circle_method_estimate_h`'s own row. With this landed, `circle_method_estimate_sq_h_core`
  -- has a consumer and its row above is redundant-but-kept, on the same reasoning as the split's.
  -- ⭐ AMENDED 2026-09-01 (DESK row o): the wrapper NOW HAS A CONSUMER —
  -- `log_chowla_two_shell_xi_sq_h`, the row below. Item 7's first object is no longer a socket
  -- connected to nothing. (The three rows above stay: a row that was correct when written is
  -- cheaper to leave than to re-audit, and each still gates its own name transitively.)
  Salt.Entropy.Chowla.circle_method_estimate_sq_h
  -- ⭐ DESK row o (2026-09-01, math): the `L²` h-lane CONSUMER, `Theorem23Shell.lean:624` — the
  -- cross of `log_chowla_two_shell_xi_sq` (`:362`) and `log_chowla_two_shell_xi_h` (`:488`).
  -- Registered HERE, in the same commit that lands it, because an unregistered name is invisible
  -- to this gate forever and its absence looks exactly like a name that passed (the 08/31 catch).
  -- ⛔ It is a CONSUMER: it asserts no supply for `MRTUniformityXiL2H`, which stays an open
  -- hypothesis at every `h`. Placed at the END of the list on the same reasoning as its
  -- neighbours — `#audit_axioms` aborts its remainder on the first non-whitelisted dependency.
  Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_h

-- ⭐ ⟦BW-(ii) 0901⟧ `Salt/Entropy/Mathlib/SetCard.lean` — two mathlib-shaped `Set.ncard`
-- helpers, outside every audit cone in the repository until this block (council 2026-09-01
-- ruling 11). Small, and listed for exactly that reason: the sweep's residue is where nobody
-- looks, and a two-lemma file is the easiest place for an axiom to sit unread.
-- ⚠️ These are declared in the `Set` namespace, not `Salt.*` — which is WHY they were missed
-- by eye: a `Salt.`-prefixed scan of this aggregate's names cannot see them at all.
#audit_axioms Set.ncard_singleton_inter'
  Set.ncard_inter_singleton

/-! ⟦THE PINNED LEAVES AND THE FLAT HEAD AT SHIFT `h` — WAVE X, PARTS (i)/(ii)⟧
(`HeadPinLeavesH`, `HloExportFlatH`, 2026-09-01, math).  The `h = 1` road's EXIT
(`HloExportFlat.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat`) had no twin at
shift `h`: the `h`-register `m4_second_road_L2_H_gk_flatRoot_L` is in DOOR FORM precisely
because nothing at `h ≠ 1` consumed a door.  These two files are that exit's leaves and head.

⚠️ THE LEAVES ARE BODY REPLAYS, NOT WRAPPERS, AND THAT IS FORCED.  `HeadPinLeaves.lean:30-37`
is standing law here: the pinned constant occurs ANTITONICALLY inside each `∃`-leaf, so NO
consequence of the landed form recovers the witness — the only route is to re-run the proof
with the numeral kept.  `hbudget_holds_h_bounded` replays `HBudget.lean:1182-1465` over the
PINNED Mertens leaf (`primeWindow_sum_inv_ge_bounded`) because `hbudget_holds_h` draws its `c`
from the UNPINNED one and `1/4 ≤ cE` is unobtainable by weakening;
`circle_method_estimate_sq_bounded_h_core` replays `CircleMethod.lean:1366-1508` with the cap
`C ≤ h·(1 + 2·C₀)` kept at the witness.

⟦THE HEAD MOVES BY FOUR SCALINGS AND ONE BINDER, NOTHING ELSE⟧ the pins are `1/(500·h) ≤ ε`
and `1/(838400·h²) ≤ δ₀`, under which EVERY gate of the landed head takes exactly its `h = 1`
value (`ε·h = 1/500` exactly); the circle constant is capped at `h·(1 + 2·C₀)`; the large-
spectrum count set is `bigXiH h` with `K` existential — no numeral moves; and `0 < h` is a
stated binder.  The conclusion is `¬ logChowlaFails h` (`ShiftFork.lean:62`), NEVER
`¬ logChowla2Fails`, which hard-codes shift `1` and from which nothing derives the shift-`h`
seed.  ⛔ `hh7 : log h ≤ 7` is NOT carried into this wave: nothing here pays for it.
⛔ NOT here: the compose into the register, which lives on the MR side
(`Salt/MR/S16FlatTerminalExitH.lean`) because the import gate runs MR → Entropy only.
Nothing bears on twin primes: the exit at shift `h` is conditional on the same open door
(`MRTUniformityXiL2H h R ρ`) its `h = 1` twin is conditional on.  Purely additive. -/
#audit_axioms Salt.Entropy.Chowla.hbudget_holds_h_bounded
  Salt.Entropy.Chowla.hreduce_holds_final_h_bounded
  Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_h_core
  Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_h
  Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h

/-! ⟦THE COUNT CONSTANT AT SHIFT `h` — WAVE H2a WORD 1⟧ (`GoldbachEnergyKcH`, 2026-09-01, math).
`Kc ≤ 2^539` was UNREACHABLE on the `h` lane, and for the same reason wave H1's `Cg` cap was:
one `obtain` reaching for the unbounded sibling.  The `h` head took the EXISTENTIAL
`bigXi_bounded` (through `bigXiH_bounded`, `ShiftFork:253`) where the `h = 1` head takes
`bigXi_bounded_ceiling_of_pin` and gets `C ≤ 2^539` with it.

⭐ **THE TWO CASES ARE FORCED, NOT STYLISTIC.**  At `ε = 1/(500·h)`, `T = 2^41·h²` the payoff is
`C₁'(h) ≤ 1.58277·10^10 + 2.58249·10^10·h²` against `2^35·h²`; the `hh7`-uniform
`(log T)² ≤ 1799.4564` therefore **FAILS at `h = 1` by 1.212×**, while the landed
`hpt_const_le_pow35` (`GoldbachEnergyN0:809`) carries `h = 1` on its own tight `(log T)² = 807.70`
at ratio 0.955.  For `h ≥ 2`: 0.867 at `h = 2`, 0.752 at `h = 1096`.
⭐ **`T := 2^41·h²` IS THE CHOICE THAT KEEPS `hTA` `h`-FREE** (`ε²·T = 2^41/250000`); `2^41·h³`
does not, which is what made the obvious uniform route false at `h = 1, 2`.
⚠️ **THE EXPONENT IS `h^15`, NOT `h^11`** — `ε^{-10}` gives ten, the squared constant
`C₁(h)² = 2^70·h^4` gives four, the fiber gives one.  `2^379.53` against `2^539` at `h ≤ 1096`:
159.47 bits.  (An earlier seat figure of 199.9 bits took `C₁ = 2^35` as FIXED; it is not.)
📌 `eps_line_h` is minted although the helm's bus line withdrew the name, because the H2b/H2c
commission cites it twice; the conflict is recorded in its docstring rather than resolved
silently.  `h_le_1096_of_log_le_seven` duplicates `Salt.MR.h_le_1096_of_hh7` deliberately: MR
imports Entropy and not the reverse.
Nothing bears on twin primes: a bound on `|Ξ_H(h)|`, conditional on nothing. -/
#audit_axioms Salt.Entropy.Chowla.h_le_1096_of_log_le_seven
  Salt.Entropy.Chowla.hpt_const_le_pow35_h
  Salt.Entropy.Chowla.hpt_holds_500h
  Salt.Entropy.Chowla.bigXiH_bounded_ceiling_of_pin
  Salt.Entropy.Chowla.eps_line_h

/-! ⟦THE FLAT HEAD AT SHIFT `h`, WITH THE DESIGN CONSTANT HOISTED⟧ (`HloExportFlatH` §4,
2026-09-02, math — wave H3 block U).  The `A₀` pin has ONE origin on the whole `h` lane, at
`:307`, and every `obtain` above it is `A`-free (wave H2a's count hook
`bigXiH_bounded_ceiling_of_pin` takes `h` and `ε` only), so the hoist is `intro A hA26 hAge` —
the legality condition `S16Uniform.flat_head_uniform` states for the `h = 1` twin, holding
verbatim at `h`.  The `h` pins ride out unchanged (`ε = 1/(500·h)`, `δ₀ ≥ 1/(838400·h²)`) and so
does H2a word 1(d)'s `K ≤ 2^539`.  The commission that fired wave H2b priced this as "the real
design block of H3"; measured at the object it is one `intro`.
Nothing bears on twin primes. -/
#audit_axioms Salt.Entropy.Chowla.flat_head_uniform_h
/-! ⟦THE SPINE CORE, RE-EXPORTED FOR THE `xceil` LANE⟧ (`HloExportFlatH` §5, 2026-09-02, math —
wave H3 block C).  One line, and it exists because of an import direction: the `x`-ceiling
apparatus lives entirely in `Salt/MR` and `Salt/Entropy` cannot import `Salt/MR`, so the `h`
lane's `x`-ceilinged head must be built in MR — where two `private` helpers of this module are
out of reach.  The 4-line one is re-proved at the MR site; the 139-line
`spine_False_core_xi_sq_flat_h` is re-exported here instead.
**Deliberately the smallest possible edit: a NEW declaration, not a visibility change.**  No
landed line is touched and no `private` marker is lifted.
Nothing bears on twin primes. -/
#audit_axioms Salt.Entropy.Chowla.spine_False_core_xi_sq_flat_h_export

/-! ⟦AFFINE FORK⟧ — THE STRIDE/OFFSET DE-SPECIALIZATION (`AffineFork`, 2026-09-03, math —
λ-BV wave 2-W, the consumer at Tao Theorem 2.3's affine atom).

`logChowlaFailsAff a b h` is the failure Prop at the affine forms `a·n + b`, `a·n + b + h`
(weight `1/n` in the CLASS index, Tao's own normalisation), with the landed `logChowlaFails h`
as its `(1, 0)` member (`logChowlaFailsAff_one_zero`).  `LogChowlaAffSupply a b h` is THE
SUPPLY DEMAND — a `def`, produced at `(1, 0)` in `Salt/MR/AffineSupplyH.lean` and by NOBODY at
`a ≥ 2` (that is wave 2-S, a port of Tao's general-`a` case; the freeze prices it ≥ the h-fork
and, at strides beyond the one-grade door's numeral budget, co-dependent on the unproved crown
`MRTDoorAllGrades`).

⭐ The finding the block rests on: AT ONE RESIDUE CLASS THE WINDOW'S OWN NORMALISATION IS THE
MAIN TERM.  Where the affine atom does not fail, `Σ (1 − λλ)/n ≥ (1 − ε)·log ω − 1 ≥ 63.5 > 0`
(`affWindow_survivorMass_ge`, from `harmonic_window_bounds` and the LANDED
`regime_logOmega_ge`), so a window element has `λ(an+b)λ(an+b+h) = −1`
(`exists_affSurvivor_of_not_failsAff`) — no `ε` pin, no Möbius sum, no common window.
⛔ That theorem carries `0 < a` because at `(a, b) = (0, 0)` it is FALSE (`liouville 0 = 0`;
the refuter pass's kill).  The prize shape `zRough_oddOmega_infinite_of_affSupply` and its
primorial form `zRough_oddOmega_infinite_of_affSupply_primorial` ("for every fixed `z`,
infinitely many `n` with `n(n+2)` `z`-rough and `Ω(n(n+2))` odd") are CONDITIONAL on the
supply at `(P, r, 2)`; `exists_admissible_class` (`r := P − 1`, explicit) and
`rough_of_coprime_primorial` mint the prize SENTENCE rather than leaving it in a docstring.

Scope: NOT almost-primality, no `∀ε`, nothing on the apex, and the Wave-1 terminal is NOT
collapsed (its left disjunct is an ℓ¹ natural-density mass; everything here is log-weighted
and windowed).  Nothing here bears on twin primes. -/
open Salt.Tactic in
#audit_axioms Salt.Entropy.Chowla.logChowlaFailsAff
  Salt.Entropy.Chowla.logChowlaFailsAff_one_zero
  Salt.Entropy.Chowla.LogChowlaAffSupply
  Salt.Entropy.Chowla.affWindow_survivorMass_ge
  Salt.Entropy.Chowla.exists_affSurvivor_of_not_failsAff
  Salt.Entropy.Chowla.liouville_shift_two_eq_neg_one_iff
  Salt.Entropy.Chowla.coprime_twinProd_of_affine
  Salt.Entropy.Chowla.exists_admissible_class
  Salt.Entropy.Chowla.rough_of_coprime_primorial
  Salt.Entropy.Chowla.flatDesignBase_unbounded
  Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupply
  Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupply_primorial

/-! ⟦STRIDE FORK⟧ — THE FOUNDATION OF THE STRIDE PORT (`StrideFork`, 2026-09-03, math — λ-BV
wave 2-S step F1, the Captain's 12:46 fire, helm refuter verdict REPAIR-THEN-FIRE 6/6).

The stride measure `logMeasureAff a x ω` (the pushforward of `logMeasure` along `n ↦ a·n`: Tao's
tuple `(λ(a·n + j))_j` is the LANDED window under it), the (2.4) ⇒ (2.6) normalisation at the
affine forms (`singleCorr_of_failsAff`), Tao's `Ξ_H` with the `η ∈ ℤ/aℤ` union VISIBLE
(`bigXiAff`, count `≤ a·gcd(h,H)·|Ξ|`, the pinned ceiling `≤ 2^539` at `ε = 1/(500·a·h)`), the
`a`-spelling tripwire `affOffset_spec`, the regime with an offset (`ChowlaRegimeAff extends
ChowlaRegime` by `b`, `hb : b ≤ Hlo` — Tao Lemma 2.5's `|r| ≤ H₋`), the tower re-basing
`chowlaTower C0 a Hlo j = chowlaTower C0 1 (a*Hlo) j`, the flat regime at a general stride, the
`Ξ`-restricted doors at the affine forms reading the regime's own `R.a`, `R.b` (untwisted `ξ`,
quantifier outside) with their `(1, 0)` compats and their seams (the tripwires), and the exact
`x`-scaling of the stride measure on the sums.  Every declaration is foundational: nothing here
produces `LogChowlaAffSupply` at any `a ≥ 2`, nothing moves the door, nothing bears on twin
primes.  25 obligations, 25 first attempt (one Opus executor, 2026-09-03 13:3x–13:5x). -/
#audit_axioms Salt.Entropy.Chowla.logMeasureAff
  Salt.Entropy.Chowla.logMeasureAff_one
  Salt.Entropy.Chowla.integral_logMeasureAff
  Salt.Entropy.Chowla.isProbabilityMeasure_logMeasureAff
  Salt.Entropy.Chowla.singleCorr_of_failsAff
  Salt.Entropy.Chowla.singleCorr_of_failsAff'
  Salt.Entropy.Chowla.affOffset
  Salt.Entropy.Chowla.bigXiAff
  Salt.Entropy.Chowla.mem_bigXiAff_iff
  Salt.Entropy.Chowla.bigXiAff_one_zero
  Salt.Entropy.Chowla.affOffset_spec
  Salt.Entropy.Chowla.card_affPreimage_le
  Salt.Entropy.Chowla.bigXiAff_card_le
  Salt.Entropy.Chowla.bigXiAff_card_le_mul
  Salt.Entropy.Chowla.bigXiAff_bounded
  Salt.Entropy.Chowla.bigXiAff_bounded_ceiling_of_pin
  Salt.Entropy.Chowla.ChowlaRegimeAff.ofRegime
  Salt.Entropy.Chowla.ChowlaRegimeAff.ofRegime_toChowlaRegime
  Salt.Entropy.Chowla.chowlaTower_eq_base_one
  Salt.Entropy.Chowla.towerDropSum_eq_base_one
  Salt.Entropy.Chowla.chowlaRegime_exists_flat_stride
  Salt.Entropy.Chowla.MRTUniformityXiAff
  Salt.Entropy.Chowla.MRTUniformityXiL2Aff
  Salt.Entropy.Chowla.mrtUniformityXiH_eq_xiAff_one_zero
  Salt.Entropy.Chowla.mrtUniformityXiL2H_eq_xiL2Aff_one_zero
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXiAff
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2Aff
  Salt.Entropy.Chowla.sum_window_aff_eq

/-! ⟦STRIDE BRIDGE⟧ — Tao (3.16) / Prop 2.6 AT THE AFFINE FORMS (`StrideBridge`, 2026-09-04,
math — λ-BV wave 2-S step F2, fired by the 09/04 council on the helm's refuter verdict
REPAIR-THEN-FIRE 6/6).

The F-function with the class filter `j + 1 ≡ p·b (mod a)` as a CONJUNCT ON THE SUMMATION INDEX
(the carrier `ZMod (PH eps H)` unchanged; the filter never touches the residue datum), its `(1, 0)`
compats, the box bound, the residue-sum and mean identities, the four concentration bounds
(exponents IDENTICAL to the `h`-lane's — the stride and the offset cost nothing in the
concentration grade), the filter's three KERNEL TRIPWIRES (`affFilter_spec_three` at `a = 3`
where the rival spellings separate, `affFilter_spec_two` on the `j` vs `j + 1` axis,
`fBridgeG_aff_two_one` the object at `(2, 1)`), Prop 2.6's pointwise unfold and the
`(p, r)`-collapse at stride `a` (`a·r + j + 1`; the collapsed base point is the seed's `a·m' + b`
only under `b < a`), and the `(c₁, h211)` glue at the affine forms with the constant EXPLICIT
(`cM/(2a)`: only `H/a` of the window survives the class).  `hreduce_aff` is a HYPOTHESIS here
exactly as `hreduce` is in `Prop26` — its discharge is F4's, at the stride measure.  Nothing here
produces `LogChowlaAffSupply`, moves a door, or bears on twin primes.  23 obligations, 23 first
attempt (one Opus executor, 2026-09-04 10:2x–10:3x). -/
#audit_axioms Salt.Entropy.Chowla.fBridgeG_aff
  Salt.Entropy.Chowla.fBridgeF_aff
  Salt.Entropy.Chowla.fBridgeG_aff_one_zero
  Salt.Entropy.Chowla.fBridgeF_aff_one_zero
  Salt.Entropy.Chowla.fBridgeG_aff_abs_le
  Salt.Entropy.Chowla.fBridgeG_aff_mem_Icc
  Salt.Entropy.Chowla.fBridgeG_aff_sum_over_residues
  Salt.Entropy.Chowla.fBridgeG_aff_mean
  Salt.Entropy.Chowla.fBridge_aff_concentration_raw
  Salt.Entropy.Chowla.fBridge_aff_concentration
  Salt.Entropy.Chowla.fBridge_aff_concentration_sharp
  Salt.Entropy.Chowla.fBridge_aff_concentration_decoupled_sharp
  Salt.Entropy.Chowla.affFilter_spec_three
  Salt.Entropy.Chowla.affFilter_spec_two
  Salt.Entropy.Chowla.fBridgeG_aff_two_one
  Salt.Entropy.Chowla.fBridgeF_aff_liouville_apply
  Salt.Entropy.Chowla.fBridgeF_aff_liouville_apply_one_zero
  Salt.Entropy.Chowla.affGate_index_eq
  Salt.Entropy.Chowla.liouville_collapse_aff
  Salt.Entropy.Chowla.perPair_collapse_aff
  Salt.Entropy.Chowla.affCollapse_base_point
  Salt.Entropy.Chowla.fBridge_of_singleCorr_aff
  Salt.Entropy.Chowla.fBridge_of_singleCorr_aff'
  Salt.Entropy.Chowla.h211_aff
  Salt.Entropy.Chowla.h211_aff_one_zero

/-! ⟦STRIDE PAIR⟧ — THE REGIME PAIRING, SHARE THE TOWER (`StridePair`, 2026-09-04, math — λ-BV
wave 2-S step F3, Entropy half; frozen v1 11:2x, v2 cut on the helm's refuter verdict
REPAIR-THEN-FIRE 4/4, fired 12:0x).

The shrunk regime `regimeShrinkX_stride` (`x/a`, `Rd.a·Hlo/a`, stride `a`, every other field
verbatim) with its tower identity a THEOREM (`regimeShrinkX_stride_tower`), the multiplier's export
`StrideScale`, the grid-restricted affine family `bigXiAffD` (`∅` off `a ∣ H`), the `L²` door at a
generic set family `MRTUniformityXiL2Set` (`= MRTUniformityXiL2H` at `bigXiH`, `rfl`), THE STATEMENT
ACT `MRTUniformityXiL2AffW` — the affine door AT TAO'S RANGE (`R.a ∣ H ∧ R.a·R.Hlo ≤ H`; F1-D2
untouched, the wide door implies it, the seam cloned), the measure transport (the image window is a
SUBSET of the plain window, the normaliser ratio `≤ 1.02` at `log ω ≥ 101`, the endpoint a named
slack term) from the plain door over `bigXiAffD` to the affine door at the shrunk regime, and the
flat-base numerals (`loglog(a·B) ≤ 3.2A + log 2` at the consumer's literal).  Nothing here produces
a door (the receipt is `Salt.MR.StridePairReceipt`'s) or bears on twin primes.  28 obligations,
28 landed (one Opus executor, 2026-09-04 12:0x–12:2x; 24 at one attempt). -/
#audit_axioms Salt.Entropy.Chowla.strideScale_one
  Salt.Entropy.Chowla.chowlaTower_ge_base
  Salt.Entropy.Chowla.regimeShrinkX_stride_x
  Salt.Entropy.Chowla.regimeShrinkX_stride_omega
  Salt.Entropy.Chowla.regimeShrinkX_stride_a
  Salt.Entropy.Chowla.regimeShrinkX_stride_eps
  Salt.Entropy.Chowla.regimeShrinkX_stride_Hlo
  Salt.Entropy.Chowla.regimeShrinkX_stride_Hhi
  Salt.Entropy.Chowla.regimeShrinkX_stride_C0
  Salt.Entropy.Chowla.regimeShrinkX_stride_J
  Salt.Entropy.Chowla.regimeShrinkX_stride_tower
  Salt.Entropy.Chowla.regimeShrinkX_stride_x_mul
  Salt.Entropy.Chowla.bigXiAffD_of_dvd
  Salt.Entropy.Chowla.bigXiAffD_card_le
  Salt.Entropy.Chowla.mrtUniformityXiL2Set_bigXiH_eq
  Salt.Entropy.Chowla.mrtUniformityXiL2AffW_of_aff
  Salt.Entropy.Chowla.mrtUniformityXiL2AffW_mono
  Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2AffW
  Salt.Entropy.Chowla.mrtUniformityXiL2AffW_one_zero_eq
  Salt.Entropy.Chowla.sum_window_image_le
  Salt.Entropy.Chowla.integral_logMeasureAff_le_plain
  Salt.Entropy.Chowla.mrtUniformityXiL2AffW_of_set
  Salt.Entropy.Chowla.strideZRatio_le
  Salt.Entropy.Chowla.strideEndpoint_le
  Salt.Entropy.Chowla.loglog_mul_flatDesignBase_le
  Salt.Entropy.Chowla.flatDesignBase_clears_stride_floors

/-! ⟦STRIDE ENTROPY HALF⟧ — THE ENTROPY HALF AT THE AFFINE REGIME, THE PLAIN ROAD
(`StrideDecrement`, `StrideCombine`, `StrideReduce`, `StrideShell`, 2026-09-04, math — λ-BV wave
2-S step F4a, Entropy half; frozen v1 14:1x, v1.1 cut on the helm's refuter verdict
REPAIR-THEN-FIRE 4/4 at 15:0x, fired 15:0x — D, K, R in parallel, then S).

The affine seam `contradiction_of_mrtDoorXiL2AffW` fired AT TOWER VALUES by a shell mirroring
`log_chowla_two_shell_xi_sq_h` with six substitutions.  D: the decrement at the stride measure
`logMeasureAff` — ONE design lemma `logMeasureAff_map_shift` (a shift by `t` with `a ∣ t` of the
stride measure IS the plain measure shifted by `t/a` then pushed along `a·`), so `joint_l1_le_aff`
is the generic contraction + `base_l1_le` verbatim; `entropy_decrementAff` exports the witness at
TAO'S RANGE `R.a * R.Hlo ≤ H` (the tower's base), and `R.a ∣ H` is consumed exactly once.  K:
residue uniformity as an injective RELABEL (`entropy_comp_of_injective` at the unit `(a : ZMod
PH)`), the class filter at `badSet_aff` and `outer_combine_aff`.  R: the `hreduce_aff` discharge —
two new arithmetic lemmas (`gate_residue_aff` at `gcd(a, p) = 1`, `card_class_range_ge`), the
shift telescoping by `integral_shift_le` at `k/a` with no induction, and the budget
`hbudget_holds_aff` with the main term pinned at `((H/a)/p)` per prime and FIVE SLICES `1/8 + 1/16
+ 1/32 + 1/64 + 1/64 = 1/4` closing exactly at the gate `ε·a·h ≤ c/(64·log 4)` and the count
binder `64·a ≤ ε·H`; the exports carry `1/4 ≤ c` (the `cE` carry, verdict A1).  S: the shell, the
core, THE HEAD `log_chowla_aff_of_door` — the circle-method estimate a SLOT `hcm` with its cap
(F4b's producer), the crown's payload a binder `hcrown` (Entropy cannot import MR) — exporting the
crown's door at grade `a·Zr·ρ + E` BESIDE `∀ ρ' ≤ δ₀_aff, MRTUniformityXiL2AffW h Ra ρ' → ¬
logChowlaFailsAff`, with `1/(838400(ah)²) ≤ δ₀_aff`; NOT composed (the `≈ 214.4` miss is F5's).
The `(1, 0)` receipts carry the affine vocabulary on exactly ONE side (verdict A2).  CONDITIONAL
on F4b through the slot; nothing here proves an estimate, moves a door, or bears on twin primes.
57 obligations, 57 landed (four Opus executors, 2026-09-04 15:0x–15:5x). -/
#audit_axioms Salt.Entropy.Chowla.finiteSupport_logMeasureAff
  Salt.Entropy.Chowla.logMeasureAff_map_shift
  Salt.Entropy.Chowla.joint_l1_le_aff
  Salt.Entropy.Chowla.condEntropy_shift_reduction_aff
  Salt.Entropy.Chowla.condEntropy_shift_le_of_l1_aff
  Salt.Entropy.Chowla.condEntropy_shift_le_aff
  Salt.Entropy.Chowla.condEntropy_kwindow_le_aff
  Salt.Entropy.Chowla.step_ineq_3_11_aff
  Salt.Entropy.Chowla.towerEntropyAff
  Salt.Entropy.Chowla.towerMIAff
  Salt.Entropy.Chowla.tower_step_of_aff
  Salt.Entropy.Chowla.tower_step_aff
  Salt.Entropy.Chowla.tower_telescope_aff
  Salt.Entropy.Chowla.entropy_per_symbol_le_aff
  Salt.Entropy.Chowla.entropy_nonneg_per_symbol_aff
  Salt.Entropy.Chowla.mutualInfo_window_nonneg_aff
  Salt.Entropy.Chowla.mutualInfo_window_comm_aff
  Salt.Entropy.Chowla.decrement_exists_of_tower_aff
  Salt.Entropy.Chowla.entropy_decrementAff
  Salt.Entropy.Chowla.entropy_decrementAff_one
  Salt.Entropy.Chowla.entropy_residueWindow_aff_eq
  Salt.Entropy.Chowla.entropy_residueWindow_ge_aff
  Salt.Entropy.Chowla.weakUniform_spine_aff
  Salt.Entropy.Chowla.badSet_aff
  Salt.Entropy.Chowla.badSet_aff_one_zero
  Salt.Entropy.Chowla.badSet_transport_aff
  Salt.Entropy.Chowla.badSet_transport_at_calibration_aff
  Salt.Entropy.Chowla.fBridgeF_aff_abs_le_boxSum
  Salt.Entropy.Chowla.decoupledMean_aff_abs_le_boxSum
  Salt.Entropy.Chowla.fBridgeF_aff_abs_le_box
  Salt.Entropy.Chowla.decoupledMean_aff_abs_le_box
  Salt.Entropy.Chowla.outer_badMass_aff_eq
  Salt.Entropy.Chowla.outer_badMass_aff_le
  Salt.Entropy.Chowla.outer_combine_aff
  Salt.Entropy.Chowla.outer_combine_aff_one_zero
  Salt.Entropy.Chowla.strideWindow_Z_pos
  Salt.Entropy.Chowla.strideWindow_sum_inv_sq
  Salt.Entropy.Chowla.strideBoundary_card_le
  Salt.Entropy.Chowla.gate_residue_aff
  Salt.Entropy.Chowla.card_class_range_le
  Salt.Entropy.Chowla.card_class_range_ge
  Salt.Entropy.Chowla.card_class_boundary_le
  Salt.Entropy.Chowla.shiftCorrAff
  Salt.Entropy.Chowla.shiftCorrAff_base
  Salt.Entropy.Chowla.shiftCorrAff_le
  Salt.Entropy.Chowla.absXaff_le_one
  Salt.Entropy.Chowla.perPair_collapse_aff_collapsed
  Salt.Entropy.Chowla.perPair_bound_aff
  Salt.Entropy.Chowla.IF_unfold_aff
  Salt.Entropy.Chowla.per_term_aff
  Salt.Entropy.Chowla.hbudget_holds_aff
  Salt.Entropy.Chowla.hreduce_holds_aff
  Salt.Entropy.Chowla.hreduce_close_aff
  Salt.Entropy.Chowla.consumability_probe_aff
  Salt.Entropy.Chowla.hreduce_holds_final_aff
  Salt.Entropy.Chowla.hreduce_holds_aff_one_zero
  Salt.Entropy.Chowla.budgetFloor_le_flatDesignBase
  Salt.Entropy.Chowla.nat_le_flatDesignBase
  Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_aff
  Salt.Entropy.Chowla.spine_False_core_xi_sq_aff
  Salt.Entropy.Chowla.log_chowla_aff_of_door
  Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_aff_one_zero

/-! ⟦STRIDE CIRCLE⟧ — THE AFFINE CIRCLE-METHOD ESTIMATE, THE PRODUCER OF F4a's SLOT
(`StrideCircle`, 2026-09-04, math — λ-BV wave 2-S step F4b; priced 16:0x, frozen statement-only
16:2x, v1.1 cut on the helm's refuter verdict REPAIR-THEN-FIRE 4/4 at 17:2x, fired 17:2x — ONE
Opus executor in file order).

Tao 1509.05422 Lemma 3.4 at the class filter `j + 1 ≡ p·b (mod a)` over the affine large-spectrum
set `bigXiAff a b h eps H`, with the `h`-lane's constant `h·(1 + 2·C₀)` — `a`-FREE in the kernel
(`a` is bound outside the `∃ C`; the cap conjunct `C ≤ h·(1 + 2·C₀)` is the certificate).  The
class filter expanded over `η ∈ ℤ/aℤ` by orthogonality LIFTED through `a ∣ H` (`twistOffset`,
`stdAddChar_lift_of_dvd`, `classFilter_expand`); the twist lands on the SECOND window factor and
TRANSLATES its DFT (`dft_twist`: `𝓕(χ_d·Φ)(k) = 𝓕Φ(k − d)`), so the `h`-lane's diagonal collapse
fails and AM–GM leaves a PARTNER sum over the translated fibre (`fourier_split_sq_twist`); the
partner lands in `bigXiAff` under `gcd(b+h, a) ∣ h` (`xiEta_translate_mem_bigXiAff` — minus that
binder it is FALSE at `(a,b,h) = (8,2,2)`, `H = 8`, `ε = 4/5`); two union bounds supply the `a`
that the expansion's `1/a` cancels.  `circle_method_estimate_sq_bounded_aff` has EXACTLY the shape
of F4a's slot `hcm` and `log_chowla_aff_of_door_unslotted` discharges it by one class-A name at
`C₀ = 2·log 4`.  The estimate holds under two binders F4a's slot did not carry: `a ∣ H` (in the
slot) and `hgcd : Nat.gcd (b + h) a ∣ h` (the producer's, on the discharges; F5's prize gains it).
Moves no door, closes no prize; the `≈ 214.4` miss at `(210, 2)` is F5's; nothing here bears on
twin primes.  19 declarations (2 defs), 17 obligations, 17 landed (one Opus executor, 2026-09-04
17:2x–17:4x). -/
#audit_axioms Salt.Entropy.Chowla.twistOffset
  Salt.Entropy.Chowla.xiEta
  Salt.Entropy.Chowla.affOffset_eq_mul_twistOffset
  Salt.Entropy.Chowla.mem_xiEta
  Salt.Entropy.Chowla.dft_twist
  Salt.Entropy.Chowla.norm_twist_mul
  Salt.Entropy.Chowla.stdAddChar_lift_of_dvd
  Salt.Entropy.Chowla.classFilter_expand
  Salt.Entropy.Chowla.filteredCorr_eq_twistSum
  Salt.Entropy.Chowla.periodization_total_twist
  Salt.Entropy.Chowla.T_collapse_twist
  Salt.Entropy.Chowla.fourier_split_sq_twist
  Salt.Entropy.Chowla.xiEta_subset_bigXiAff
  Salt.Entropy.Chowla.xiEta_translate_mem_bigXiAff
  Salt.Entropy.Chowla.sum_xiEta_le
  Salt.Entropy.Chowla.sum_xiEta_translate_le
  Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_aff
  Salt.Entropy.Chowla.circle_method_estimate_sq_aff_core
  Salt.Entropy.Chowla.log_chowla_aff_of_door_unslotted
