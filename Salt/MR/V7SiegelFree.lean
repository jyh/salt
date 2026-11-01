/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

import Salt.MR.V7Rated
import Salt.MR.V7E
import Salt.MR.V7B
import Salt.MR.V7Ks
import Salt.MR.XThread
import Salt.MR.FlatDoorStandoff
import Salt.TwinBar.SevenEighthsStandoff
import Salt.MR.StrataBounds
import Salt.MR.BlockLenDoor
import Salt.MR.RegimeFloors
import Salt.MR.DoorSocket
import Salt.MR.FlatDesignBound
import Salt.MR.ArcRegimeWeaken
import Salt.Entropy.Chowla.RegimeHeadroom
import Salt.MR.RegimeSupplyFacts
import Salt.Entropy.Chowla.HeadFloors
import Salt.MR.RegimeScaleReads

/-!
# The v7 family of log-Chowla theorems under a Siegel standoff (O13)

`logChowla2_ineffective_v6_csarm`, `logChowla2_ineffective_v7`, `logChowla2_ineffective_v7_g0` and
`logChowla2_v7_rated` reach `Salt.SW.siegel_theorem` through thirteen declarations that had no
standoff twin (measured by the rung-4 census's map probe, 2026-10-24): a chain of six in
`XThread.lean` from `flat_head_uniform_xceil` (which takes `hreduce_holds_final_bounded` and
`primeWindow_sum_inv_ge_bounded`) up to `flat_conditional_uniform_win_xceil_kwide_khoist`, then the
two witnessed-scale forms and `s15_crossing_…_csfree` (`V7Ks`, `V7B`), and the four heads. Every
other reaching child already has a twin (`Salt/MR/FlatDoorStandoff.lean` and the 4.25 chain). Each
declaration below is its landed statement under the three leading binders `{cS} (hcS) (hSieg)`, its
landed proof verbatim with each reaching child replaced by its twin, emitted inside a replay of the
scope that was active at the landed declaration (namespace, sections, `open`s). The text was
generated from the landed sources by script. No landed proof is edited; the ledger
`Salt/MR/All.lean` gains the import and the audit block.

## What this does and does not say

* Each conclusion is the landed statement token for token (`#assert_conclusion_is`), under the open
  hypothesis `NoSiegelZerosAt cS`, or under the repository's restatement `DirichletSevenEighths`,
  which is a HYPOTHESIS here.
* The certificate below is about the PROOF TERM: each closure contains none of `siegel_theorem`,
  `siegel_L_one_exceptional` and `L1_lower_siegel`, while the four landed heads' closures contain
  `siegel_theorem` (the positive controls). `#print axioms` cannot see this.
* Every hypothesis the landed heads carry (the door, the grade binders) is still there. Nothing here
  makes a constant explicit, and nothing here bears on twin primes.
-/

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_head_uniform_xceil` (`XThread.lean:516`): its statement under the
three standoff binders, its proof verbatim with `hreduce_holds_final_bounded` ·
`primeWindow_sum_inv_ge_bounded` replaced by their twins. -/
theorem flat_head_uniform_xceil_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := (hreduce_holds_final_bounded_of_standoff hcS hSieg)
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := (primeWindow_sum_inv_ge_bounded_of_standoff hcS hSieg)
  obtain ⟨C, hC, hCcap, hcm⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- ⟦THE LEAF NUMERALS⟧ `log 4 = 2·log 2 < 1.3863`, hence `C ≤ 6.55`
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hCnum : C ≤ 655 / 100 := by
    rw [hlog4eq] at hCcap; linarith
  -- ⟦THE PIN⟧ `ε := 1/500`
  obtain ⟨ε, hεdef⟩ : ∃ e : ℚ, e = 1 / 500 := ⟨_, rfl⟩
  have hεR : ((ε : ℚ) : ℝ) = 1 / 500 := by rw [hεdef]; norm_num
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by rw [hεR]; norm_num
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    rw [hεR, le_div_iff₀ (by positivity), hlog4eq]
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by rw [hεR]; norm_num
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    rw [hεR, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    rw [hεR, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
  have hεQ1 : ε ≤ 1 / 2 := by rw [hεdef]; norm_num
  -- ⟦THE `δ₀` FLOOR⟧ the binding arm at its worst case
  have hδ₀ge : (1 : ℝ) / 838400 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    rw [hεR]; linarith
  -- ⟦THE ONE EDIT⟧ the count hook at the pin, carrying `Kc ≤ 2^539`
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_of_pin ε hεdef
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hεQpos, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hεdef.ge, hδ₀ge, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil A hA26 ε hεQpos hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  obtain ⟨hFlo, hxiHlo, hbudHlo, hredHlo⟩ :=
    Salt.Entropy.Chowla.flatHeadFloors_facts hOpqdef hFdef hRHlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`
  exact spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor cE hcE H₀red hred cD3 hcD3
    H₀D3 hD3 C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_socket_uniform_xceil` (`XThread.lean:634`): its statement under the
three standoff binders, its proof verbatim with `flat_head_uniform_xceil` replaced by their twins.
-/
theorem flat_socket_uniform_xceil_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (ε : ℚ) (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    (flat_head_uniform_xceil_of_standoff hcS hSieg)
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨ε, K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, _, hRU1, hRg, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd 0 (max U1floor H₀) g hg
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_doorL2_uniform_xceil_khoist` (`XThread.lean:686`): its statement under
the three standoff binders, its proof verbatim with `flat_socket_uniform_xceil` replaced by their
twins. -/
theorem flat_doorL2_uniform_xceil_khoist_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨ε, Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hsk⟩ :=
    (flat_socket_uniform_xceil_of_standoff hcS hSieg)
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hexit U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx := R.add_one_le_x
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_road_uniform_xceil_khoist` (`XThread.lean:746`): its statement under
the three standoff binders, its proof verbatim with `flat_doorL2_uniform_xceil_khoist` replaced by
their twins. -/
theorem flat_road_uniform_xceil_khoist_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hdoor⟩ :=
    (flat_doorL2_uniform_xceil_khoist_of_standoff hcS hSieg)
  refine ⟨Cg, ε, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hmain U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have harc8 := arcDen_cube_le_of_arc3 harc3
  have harc := arcDen_sq_le_of_arc3 harc3
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_blockLen_L_gk K
    (fun H => by have := hBblk0 H; positivity)
    harc ?_ hcov
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_capstone_uniform_win_xceil_kwide_khoist` (`XThread.lean:826`): its
statement under the three standoff binders, its proof verbatim with `flat_road_uniform_xceil_khoist`
replaced by their twins. -/
theorem flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (Cg : ℝ) (ε : ℚ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    (flat_road_uniform_xceil_khoist_of_standoff hcS hSieg)
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, ε, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  obtain ⟨hδs, hδssq, hρpos, hρ1⟩ := door_socket_facts hδ₀ hKc
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    exact gate6_of_j0_floor R hρ1 hj0
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := s12DeltaSock_sq_two hδ₀ hKc
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    linarith [hend, show 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 by field_simp; ring]
end
end Salt.MR

namespace Salt.MR
noncomputable section
open private spine_False_core_xi_sq_uniform uniformCap_arc uniformCap_shuffle from
  Salt.MR.S16Uniform
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_conditional_uniform_win_xceil_kwide_khoist` (`XThread.lean:1111`): its
statement under the three standoff binders, its proof verbatim with
`flat_capstone_uniform_win_xceil_kwide_khoist` replaced by their twins. -/
theorem flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderStrict ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    (flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff hcS hSieg) Awin hband
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg hU
  obtain ⟨hδs, -, hρ0, hρ1⟩ := door_socket_facts hδ₀ hKc
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT⟧ the substituted `g' = s15Arm δ₀ ρ + g` still obeys the
  -- builder-side rider: §2 prices the arm at `log ω + H₊/10^6` and the caller's own `ε²·H₊`
  -- margin (`≥ 4·H₊/10^6` at `ε ≥ 1/500`) pays for it AND for the sum split's `log 2`
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  have hg' : XCeilRider ε (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHhiR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
    have hε2 : (1 : ℝ) / 250000 ≤ (ε : ℝ) ^ 2 := by
      nlinarith [hεR, sq_nonneg ((ε : ℝ) - 1 / 500)]
    have hεsq : 4 * ((Hhi : ℕ) : ℝ) / 1000000 ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hε2 (le_trans (by norm_num) hHhiR)
      linarith
    have harm : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 1000000 := by
      rw [hρdef, hδsdef]
      -- the re-cut estimate is STRICTLY STRONGER; this consumer still spends only `H₊/10^6`
      refine le_trans (s15Arm_log_le hδ₀ hδpin hKc hKcb hH4 hll) ?_
      have : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
      linarith
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hlog2 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
    have harm' : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    have hsum := xt_log_add_le harm' hgb'
    have hslack : Real.log 2 ≤ 3 * ((Hhi : ℕ) : ℝ) / 1000000 := by linarith
    exact le_trans hsum (by linarith)
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) hg'
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  obtain ⟨hHlo, hfl, harcfl⟩ := regime_floors_of_U1 hU hU1 hRcap
  refine ⟨R, hReps, hHlo, hRgg, hRx, hRtow, ?_⟩
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨hlam50, hΛ50, hHreg⟩ := regime_scale_reads R hfl
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧**
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin` (`V7Ks.lean:296`): its
statement under the three standoff binders, its proof verbatim with
`flat_conditional_uniform_win_xceil_kwide_khoist` ·
`s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin` replaced by their twins. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    (flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff hcS hSieg) Awin hband
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := (s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin_of_standoff hcS hSieg)
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε2q
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree`
(`V7B.lean:1687`): its statement under the three standoff binders, its proof verbatim with
`m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs` replaced by their twins. -/
theorem s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        Real.exp (-100) ≤ Ks →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    (m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs_of_standoff hcS hSieg)
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq hKs R M hM hfl hT₀ hblk hcof hcap
  -- ⟦THE RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is the carried conjunct, not an antecedent
  have hgate := s16_capGate_supply_L_gk_sharpT0 K hM hfl hcsf hblk hT₀ hKq hKs hC0 hC40
    (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree`
(`V7B.lean:1733`): its statement under the three standoff binders, its proof verbatim with
`flat_conditional_uniform_win_xceil_kwide_khoist` ·
`s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree` replaced by their twins. -/
theorem logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (Awin : ℝ)
    (hband : S16BandLaneCBoundedL_winU Awin) :
    ∃ (ε : ℚ) (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.exp (-100) ≤ Ks →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    (flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff hcS hSieg) Awin hband
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §1's twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := (s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff hcS hSieg)
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε2q
  have hεR : (1 : ℝ) / 500 ≤ (ε : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hεpin
  refine ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase hA26 hβ hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by
    rw [hReps]
    have : (1 : ℚ) / 2 ^ 9 ≤ 1 / 500 := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win (c := 1) hA26 K hKw (by norm_num) (by norm_num) (by simp) hδ₀ (by simpa using hδpin) hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win (by simpa using heps) hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb hKs R (flatDoorM A) hM1 hfl (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `logChowla2_ineffective_v6_csarm` (`V7B.lean:1846`): its statement under the
three standoff binders, its proof verbatim with `s16_bandLaneWinL_holdsU` ·
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree` replaced by their twins. -/
theorem logChowla2_ineffective_v6_csarm_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := (s16_bandLaneWinL_holdsU_of_standoff hcS hSieg)
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    (logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff hcS hSieg) Awin hband
  -- ⟦THE DESIGN CONSTANT⟧ chosen above all four fixed constants AND above the co-factor
  -- threshold — legal exactly because `C_q` is now minted BEFORE the lever (§1)
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_right (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (le_max_left _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Salt.MR.x0_le_exp_exp_of_four_le hx0nn hx0A
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hT₀ hKs g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  obtain ⟨heps500, hxceil, hM1, heps500R, h518, hfl, hlo, hthrgate⟩ :=
    regime_flat_supply_facts hReps hHlo hRx hdes hεpin hA162 hthrA
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
/-- `logChowla2_ineffective_v6_csarm` from the 7/8 statement, without Siegel's theorem. -/
theorem logChowla2_ineffective_v6_csarm_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) →
        Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) :=
  logChowla2_ineffective_v6_csarm_of_standoff
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `logChowla2_ineffective_v7` (`V7E.lean:76`): its statement under the three
standoff binders, its proof verbatim with `s16_bandLaneWinL_holdsU` ·
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree` replaced by their twins. -/
theorem logChowla2_ineffective_v7_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  -- ⟦THE REPAIRED CO-FACTOR SUPPLY⟧ its four Skolem constants, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ := cofkR_cofactorSupply_L_gk
  obtain ⟨Awin, -, hband⟩ := (s16_bandLaneWinL_holdsU_of_standoff hcS hSieg)
  -- ⟦THE cs-FREE FLAT TERMINAL⟧ V7-B's §4: the floor arrives as `hcsf`, not as an arrow
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    (logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff hcS hSieg) Awin hband
  -- ⟦THE DESIGN CONSTANT, WITH THE `T₀`-ARM⟧ V7-C's sixth arm: chosen above all five landed
  -- thresholds AND above `T₀` itself — legal for the same reason the other five arms are,
  -- every one of the six constants is minted BEFORE the lever, `T₀` at the obtain just above.
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ)))) := ⟨_, rfl⟩
  have hT₀A : T₀ ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hA162 : (162 : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_right (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
      (le_max_left _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _) (le_max_right _ _))
      (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    rw [hAdef]
    exact le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Salt.MR.x0_le_exp_exp_of_four_le hx0nn hx0A
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hKs g hg
  -- ⟦RIDER 2, DISCHARGED⟧ V7-C's arm at the design constant's own sixth `max` slot
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKs g hg
  refine ⟨R, hReps, by rw [hHlo]; exact hbase hopq, hRg, hRtow, hdes, hwin, ?_⟩
  intro hKvtcush
  -- ⟦ITEM 3, DISCHARGED⟧ the base-scale cap at `K = KlevF A`
  -- ⟦RULING 9, DISCHARGED⟧ the co-factor supply at the repaired ladder
  obtain ⟨heps500, hxceil, hM1, heps500R, h518, hfl, hlo, hthrgate⟩ :=
    regime_flat_supply_facts hReps hHlo hRx hdes hεpin hA162 hthrA
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  exact hfire2 hcofsupply
    (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
/-- `logChowla2_ineffective_v7` from the 7/8 statement, without Siegel's theorem. -/
theorem logChowla2_ineffective_v7_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) :=
  logChowla2_ineffective_v7_of_standoff
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `logChowla2_ineffective_v7_g0` (`V7E.lean:203`): its statement under the
three standoff binders, its proof verbatim with `logChowla2_ineffective_v7` replaced by their twins.
-/
theorem logChowla2_ineffective_v7_g0_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, hKvt0, hmain⟩ :=
    (logChowla2_ineffective_v7_of_standoff hcS hSieg) A₀
  refine ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, Kvt,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb, hβ, hA162, hA₀A, hKvt0, ?_⟩
  intro hKs
  -- ⟦THE RIDER, VOID⟧ the caller's request is `0`, and `log 0 = 0` leaves the margin intact
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R, hReps, hHlo, -, hRtow, hdes, hwin, hfire⟩ := hmain hKs (fun _ _ => 0) hzero
  exact ⟨R, hReps, hHlo, hRtow, hdes, hwin, hfire⟩
/-- `logChowla2_ineffective_v7_g0` from the 7/8 statement, without Siegel's theorem. -/
theorem logChowla2_ineffective_v7_g0_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (Kvt : ℕ → ℕ → ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧ Mfl ≤ flatDoorM A ∧
      0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧
      (Real.exp (-100) ≤ Ks →
        ∃ R : ChowlaRegime,
          R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
          3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
          Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
          (32 * Kvt (KlevF A) ⌈arcDen 12 R.Hhi⌉₊
              + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
            ≤ Real.log (R.Hhi : ℝ) / 4 →
            ¬ logChowla2Fails R.eps R.x R.ω)) :=
  logChowla2_ineffective_v7_g0_of_standoff
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) A₀
end
end Salt.MR

namespace Salt.MR
noncomputable section
open Salt.Entropy.Chowla
open scoped BigOperators
/-- **⟦STANDOFF TWIN⟧** `logChowla2_v7_rated` (`V7Rated.lean:975`): its statement under the three
standoff binders, its proof verbatim with `s16_bandLaneWinL_holdsU` ·
`logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin` replaced by their
twins. -/
theorem logChowla2_v7_rated_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        ¬ logChowla2Fails R.eps R.x R.ω := by
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated
  obtain ⟨Awin, -, hband⟩ := (s16_bandLaneWinL_holdsU_of_standoff hcS hSieg)
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨ε, Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    (logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff hcS hSieg) Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Salt.MR.x0_le_exp_exp_of_four_le hx0nn hx0A
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrict_zero ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  obtain ⟨heps500, hxceil, hM1, heps500R, h518, hfl, hlo, hthrgate⟩ :=
    regime_flat_supply_facts hReps hHlo hRx hdes hεpin hA162 hthrA
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush
  have hfireR : ¬ logChowla2Fails R.eps R.x R.ω :=
    hfire2 hcofsupply
      (s16_baseScaleCap96_L_at_klevF hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin)
  exact ⟨ε, Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩
/-- `logChowla2_v7_rated` from the 7/8 statement, without Siegel's theorem. -/
theorem logChowla2_v7_rated_of_sevenEighths
    (h : Salt.TwinBar.DirichletSevenEighths) (A₀ : ℝ) :
    ∃ (ε : ℚ) (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ 1 / 500 ≤ ε ∧ 1 / 838400 ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        ¬ logChowla2Fails R.eps R.x R.ω :=
  logChowla2_v7_rated_of_standoff
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (Salt.TwinBar.noSiegelZerosAt_of_sevenEighths h) A₀
end
end Salt.MR

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see).
#assert_reaches Salt.MR.logChowla2_ineffective_v6_csarm Salt.SW.siegel_theorem
#assert_reaches Salt.MR.logChowla2_ineffective_v7 Salt.SW.siegel_theorem
#assert_reaches Salt.MR.logChowla2_ineffective_v7_g0 Salt.SW.siegel_theorem
#assert_reaches Salt.MR.logChowla2_v7_rated Salt.SW.siegel_theorem

-- THE CERTIFICATE.
#assert_not_reaches Salt.MR.flat_head_uniform_xceil_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_head_uniform_xceil_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_head_uniform_xceil_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_socket_uniform_xceil_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_socket_uniform_xceil_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_socket_uniform_xceil_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_doorL2_uniform_xceil_khoist_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_doorL2_uniform_xceil_khoist_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_doorL2_uniform_xceil_khoist_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_road_uniform_xceil_khoist_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_road_uniform_xceil_khoist_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_road_uniform_xceil_khoist_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff
  Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff
  Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v6_csarm_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_sevenEighths
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_ineffective_v7_g0_of_sevenEighths Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_sevenEighths Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_sevenEighths Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_v7_rated_of_sevenEighths Salt.SW.L1_lower_siegel

-- TOKEN CHECKS: the conclusions are the landed statements.
#assert_conclusion_is Salt.MR.flat_head_uniform_xceil_of_standoff 3 Salt.MR.flat_head_uniform_xceil
#assert_conclusion_is Salt.MR.flat_socket_uniform_xceil_of_standoff 3
  Salt.MR.flat_socket_uniform_xceil
#assert_conclusion_is Salt.MR.flat_doorL2_uniform_xceil_khoist_of_standoff 3
  Salt.MR.flat_doorL2_uniform_xceil_khoist
#assert_conclusion_is Salt.MR.flat_road_uniform_xceil_khoist_of_standoff 3
  Salt.MR.flat_road_uniform_xceil_khoist
#assert_conclusion_is Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist_of_standoff 3
  Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist
#assert_conclusion_is Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist_of_standoff 3
  Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist
#assert_conclusion_is Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_of_standoff 3
  Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin
#assert_conclusion_is Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_of_standoff 3
  Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree
#assert_conclusion_is Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_of_standoff 3
  Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v6_csarm_of_standoff 3
  Salt.MR.logChowla2_ineffective_v6_csarm
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v7_of_standoff 3
  Salt.MR.logChowla2_ineffective_v7
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v7_g0_of_standoff 3
  Salt.MR.logChowla2_ineffective_v7_g0
#assert_conclusion_is Salt.MR.logChowla2_v7_rated_of_standoff 3 Salt.MR.logChowla2_v7_rated
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v6_csarm_of_sevenEighths 1
  Salt.MR.logChowla2_ineffective_v6_csarm
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v7_of_sevenEighths 1
  Salt.MR.logChowla2_ineffective_v7
#assert_conclusion_is Salt.MR.logChowla2_ineffective_v7_g0_of_sevenEighths 1
  Salt.MR.logChowla2_ineffective_v7_g0
#assert_conclusion_is Salt.MR.logChowla2_v7_rated_of_sevenEighths 1 Salt.MR.logChowla2_v7_rated
