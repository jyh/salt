/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineEpsFence
import Salt.MR.FlatDoorStandoff
import Salt.TwinBar.SevenEighthsStandoff

/-!
# The log-Chowla spine under a Siegel standoff (O13)

`log_chowla_two_budget_head`, `log_chowla_two_door_only` and `spine_eps_constant_floor` reach
`Salt.SW.siegel_theorem` through two producers only: `hreduce_holds_final` and
`primeWindow_sum_inv_ge`, both through `Salt.Chen.lambda_mass_lower`, that is through
`siegelWalfisz_holds` (measured by the rung-4 census, 2026-10-24). Their `_bounded` forms already
have standoff twins (`Salt/MR/FlatDoorStandoff.lean`), whose statements are the unbounded ones with
one extra conjunct `1 / 4 ≤ c`; the two twins below drop it. The three heads, and
`log_chowla_two_door_only_xi` between two of them, are then re-stated under three leading binders
`{cS} (hcS) (hSieg)`, each landed proof verbatim with each producer replaced by its twin. No landed
file is edited.

## What this does and does not say

* Each conclusion is the landed statement token for token (`#assert_conclusion_is`), under the
  open hypothesis `NoSiegelZerosAt cS`, or under the repository's restatement
  `DirichletSevenEighths`, which is a HYPOTHESIS here.
* The certificate below is about the PROOF TERM: each closure contains none of `siegel_theorem`,
  `siegel_L_one_exceptional` and `L1_lower_siegel`, while the landed heads' closures contain
  `siegel_theorem` (the positive controls). `#print axioms` cannot see this.
* The door `MRTUniformityXi` / `MRTUniformity` is still a hypothesis inside each statement, as in
  the landed theorems. Nothing here makes a constant explicit, and nothing here bears on twin
  primes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction
open Filter Topology

open private mutualInfo_window_comm' spine_False_core_xi from Salt.Entropy.Chowla.SpineFinal

namespace Salt.Entropy.Chowla

/-- **⟦STANDOFF TWIN⟧** `hreduce_holds_final` (`HBudget.lean:732`): its statement under the three
standoff binders, from `hreduce_holds_final_bounded_of_standoff` (`Salt/MR/FlatDoorStandoff.lean`)
by dropping its `1 / 4 ≤ c` conjunct. -/
theorem hreduce_holds_final_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, -, H₀, h⟩ := hreduce_holds_final_bounded_of_standoff hcS hSieg
  exact ⟨c, hc, H₀, h⟩

/-- **⟦STANDOFF TWIN⟧** `primeWindow_sum_inv_ge` (`WindowMertensLower.lean:56`): its statement under
the three standoff binders, from `primeWindow_sum_inv_ge_bounded_of_standoff`
(`Salt/MR/FlatDoorStandoff.lean`) by dropping its `1 / 4 ≤ c` conjunct. -/
theorem primeWindow_sum_inv_ge_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ), H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      c / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  obtain ⟨c, hc, -, H₀, h⟩ := primeWindow_sum_inv_ge_bounded_of_standoff hcS hSieg
  exact ⟨c, hc, H₀, h⟩

/-- **⟦STANDOFF TWIN⟧** `log_chowla_two_budget_head` (`SpineFinal.lean:750`): its statement under
the three standoff binders, its proof verbatim with `hreduce_holds_final` and
`primeWindow_sum_inv_ge` replaced by their twins. -/
theorem log_chowla_two_budget_head_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final_of_standoff hcS hSieg
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_of_standoff hcS hSieg
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- choose ε below `min(min(min (cE/(32·log4)) (1/2)) (cD3/16)) (cD3/(16·C))`
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith only [hε0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  refine ⟨ε, cD3 / (16 * C) * (ε : ℝ) / (2 * K), hεQpos,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0)
      (mul_pos (by norm_num) hK), ?_⟩
  intro extraFloor
  obtain ⟨R, hReps, hRHlo⟩ := chowlaRegime_exists_param ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) extraFloor)
  refine ⟨R, hReps, le_trans (le_max_right _ _) hRHlo, ?_⟩
  intro δ hδpos hδ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hxiR : ∀ (H' : ℕ) [NeZero H'], H₀xi ≤ H'
      → ((bigXi R.eps H').card : ℝ) ≤ K := by
    intro H' hne hh
    haveI := hne
    rw [hReps]; exact hxi H' hh
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max (max H₀red H₀D3) H₀xi ≤ H :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  have hbudget2 : K * δ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hle : K * δ ≤ K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ hK.le
    have heq : K * (cD3 / (16 * C) * (ε : ℝ) / (2 * K)) = cD3 / (16 * C) * (ε : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hle, hpos]
  exact spine_False_core_xi R (le_of_lt hδpos) hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm K hK H₀xi hxiR H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

/-- **⟦STANDOFF TWIN⟧** `log_chowla_two_door_only_xi` (`SpineFinal.lean:966`): the same, through
`log_chowla_two_budget_head_of_standoff`. -/
theorem log_chowla_two_door_only_xi_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨_ε, δ₀, _hεpos, hδ₀pos, hbody⟩ := log_chowla_two_budget_head_of_standoff hcS hSieg
  obtain ⟨R, _hReps, _h0Hlo, hδbody⟩ := hbody 0
  exact ⟨δ₀, R, hδ₀pos, hδbody⟩

/-- **⟦STANDOFF TWIN⟧** `log_chowla_two_door_only` (`SpineFinal.lean:981`): the same, through
`log_chowla_two_door_only_xi_of_standoff`. -/
theorem log_chowla_two_door_only_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformity R δ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨δ₀, R, hδ₀pos, hδbody⟩ := log_chowla_two_door_only_xi_of_standoff hcS hSieg
  exact ⟨δ₀, R, hδ₀pos, fun δ hδpos hδ hdoor =>
    hδbody δ hδpos hδ (mrtUniformity_implies_xi R δ hdoor)⟩

/-- **⟦STANDOFF TWIN⟧** `spine_eps_constant_floor` (`SpineEpsFence.lean:102`): the same, through
`log_chowla_two_budget_head_of_standoff`. -/
theorem spine_eps_constant_floor_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (W : ℕ → ℝ) (hW : Tendsto W atTop (𝓝 0)) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      (∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω) ∧
      (∀ᶠ z in atTop, ¬ ((ε : ℝ) ≤ W z)) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hbody⟩ := log_chowla_two_budget_head_of_standoff hcS hSieg
  exact ⟨ε, δ₀, hε, hδ₀, hbody, margin_fails_vanishing_demand ε hε W hW⟩

private theorem log_two_div_eight_pos'' : 0 < Real.log 2 / 8 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- The SPINE-BUDGET head from the 7/8 statement, without Siegel's theorem. -/
theorem log_chowla_two_budget_head_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω :=
  log_chowla_two_budget_head_of_standoff log_two_div_eight_pos''
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h)

/-- The full door-only terminal from the 7/8 statement, without Siegel's theorem. -/
theorem log_chowla_two_door_only_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths) :
    ∃ (δ₀ : ℝ) (R : ChowlaRegime), 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformity R δ →
        ¬ logChowla2Fails R.eps R.x R.ω :=
  log_chowla_two_door_only_of_standoff log_two_div_eight_pos''
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h)

/-- The ε fence from the 7/8 statement, without Siegel's theorem. -/
theorem spine_eps_constant_floor_of_sevenEighths (h : Salt.TwinBar.DirichletSevenEighths)
    (W : ℕ → ℝ) (hW : Tendsto W atTop (𝓝 0)) :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      (∀ extraFloor : ℕ, ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → MRTUniformityXi R δ →
          ¬ logChowla2Fails R.eps R.x R.ω) ∧
      (∀ᶠ z in atTop, ¬ ((ε : ℝ) ≤ W z)) :=
  spine_eps_constant_floor_of_standoff log_two_div_eight_pos''
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) W hW

end Salt.Entropy.Chowla

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head Salt.SW.siegel_theorem
#assert_reaches Salt.Entropy.Chowla.log_chowla_two_door_only Salt.SW.siegel_theorem
#assert_reaches Salt.Entropy.Chowla.spine_eps_constant_floor Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.Entropy.Chowla.hreduce_holds_final_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.hreduce_holds_final_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.hreduce_holds_final_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.primeWindow_sum_inv_ge_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.primeWindow_sum_inv_ge_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.primeWindow_sum_inv_ge_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_xi_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_xi_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_xi_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_sevenEighths
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_budget_head_of_sevenEighths
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_sevenEighths
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.log_chowla_two_door_only_of_sevenEighths
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_sevenEighths
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.Entropy.Chowla.spine_eps_constant_floor_of_sevenEighths
  Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.Entropy.Chowla.hreduce_holds_final_of_standoff 3
  Salt.Entropy.Chowla.hreduce_holds_final
#assert_conclusion_is Salt.Entropy.Chowla.primeWindow_sum_inv_ge_of_standoff 3
  Salt.Entropy.Chowla.primeWindow_sum_inv_ge
#assert_conclusion_is Salt.Entropy.Chowla.log_chowla_two_budget_head_of_standoff 3
  Salt.Entropy.Chowla.log_chowla_two_budget_head
#assert_conclusion_is Salt.Entropy.Chowla.log_chowla_two_door_only_xi_of_standoff 3
  Salt.Entropy.Chowla.log_chowla_two_door_only_xi
#assert_conclusion_is Salt.Entropy.Chowla.log_chowla_two_door_only_of_standoff 3
  Salt.Entropy.Chowla.log_chowla_two_door_only
#assert_conclusion_is Salt.Entropy.Chowla.spine_eps_constant_floor_of_standoff 3
  Salt.Entropy.Chowla.spine_eps_constant_floor
#assert_conclusion_is Salt.Entropy.Chowla.log_chowla_two_budget_head_of_sevenEighths 1
  Salt.Entropy.Chowla.log_chowla_two_budget_head
#assert_conclusion_is Salt.Entropy.Chowla.log_chowla_two_door_only_of_sevenEighths 1
  Salt.Entropy.Chowla.log_chowla_two_door_only
#assert_conclusion_is Salt.Entropy.Chowla.spine_eps_constant_floor_of_sevenEighths 1
  Salt.Entropy.Chowla.spine_eps_constant_floor
