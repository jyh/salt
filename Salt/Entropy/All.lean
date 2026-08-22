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

THE FORK, NOT THE EDIT.  The landed spine is Tao 1509.05422 at `(a, b, h) = (1, 0, 1)`.
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
REACHABLE, not done.  No claim about Chowla, about the door, or about twins is made or
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
