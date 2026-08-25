/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.SpineFinal
import Salt.Entropy.Chowla.TowerExport
import Salt.MR.S11ExitL2

/-!
# F-5 — ⟦GAP X, THE THREADING PROBE⟧

`arc.md` §4 F-5.  GAP X is the OUTPUT-side scale quantifier: every landed head
delivers `∃ R, … ∧ ¬ logChowla2Fails R.eps R.x R.ω`, i.e. non-failure at an
`∃`-CHOSEN outer scale, and the `g`-lever only forces that scale to be LARGE.
This file attempts the `∀ X ≥ X₀` form at ONE fixed window `(ω, H₋, H₊)`.

⚠️ NOTHING HERE IS UNCONDITIONAL.  The conclusion is still gated on the `L²`
door `MRTUniformityXiL2`, whose producer is the open arc (GAP α, GAP A.1).
This file changes the SCALE QUANTIFIER ONLY.
-/

open private spine_False_core_xi_sq mutualInfo_window_comm' from
  Salt.Entropy.Chowla.SpineFinal

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.Entropy.Chowla

/-- **⟦THE `L²` SPINE-BUDGET HEAD, SCALE-THREADED⟧** — `log_chowla_two_budget_head_g_sq_count`
with the `g`-lever REPLACED by a prescribed outer scale: one `X₀` and ONE window
`(ω, H₋, H₊)`, then EVERY `X ≥ X₀`. -/
theorem log_chowla_two_budget_head_forallX_sq_count :
    ∃ (ε : ℚ) (K δ₀ : ℝ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ), ∃ (X₀ ω Hlo Hhi : ℕ), ∀ X : ℕ, X₀ ≤ X →
        ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧
        (R.x = X ∧ R.ω = ω ∧ R.Hlo = Hlo ∧ R.Hhi = Hhi) ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  -- ⟦THE ONE CHANGED PRODUCER⟧ the SQUARED circle-method estimate; `C = 1 + 2C₀` unchanged
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate_sq (2 * Real.log 4)
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
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  -- ⟦THE K-FREE δ₀⟧ `c₀·ε/4`, NOT `c₀·ε/(2K)`
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4, hεQpos, hK,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num), ?_⟩
  intro extraFloor U1floor
  obtain ⟨R₀, hR₀eps, hR₀Hlo, hR₀tow⟩ := chowlaRegime_exists_param_tower_45 ε hεQpos hεQ1
    (max (max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4)))) (max extraFloor U1floor))
  refine ⟨R₀.x, R₀.ω, R₀.Hlo, R₀.Hhi, ?_⟩
  intro X hX
  obtain ⟨R, hReps, hRHlo, hRtow, hRg⟩ :
      ∃ R : ChowlaRegime, R.eps = ε ∧
        (max (max (max (max H₀red H₀D3) H₀xi)
          (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4))))
            (max extraFloor U1floor)) ≤ R.Hlo ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        (R.x = X ∧ R.ω = R₀.ω ∧ R.Hlo = R₀.Hlo ∧ R.Hhi = R₀.Hhi) :=
    ⟨regimeEnlargeX' R₀ hX, hR₀eps, hR₀Hlo, hR₀tow, rfl, rfl, rfl, rfl⟩
  have hxiHlo : H₀xi ≤ R.Hlo :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hRHlo
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, ?_, hRtow, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm']; exact hMI
  have hepscR : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε` (the landed `:944–953` chain minus the K step)
  have hbudget2 : ρ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  exact spine_False_core_xi_sq R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm H hlo hhi hH₀ hepscR t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦THE SPLIT SOCKET, ROAD FORM, SCALE-THREADED⟧** — `S11ExitL2.m4_exit_socket_split_sq_arc`
with the `g`-lever replaced by a prescribed outer scale.  Payload sed'd VERBATIM. -/
theorem m4_exit_socket_split_sq_arc_forallX :
    ∃ (ε : ℚ) (K δ₀ : ℝ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ), ∃ (X₀ ω Hlo Hhi : ℕ), ∀ X : ℕ, X₀ ≤ X →
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧
          (R.x = X ∧ R.ω = ω ∧ R.Hlo = Hlo ∧ R.Hhi = Hhi) ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
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
  obtain ⟨ε, K, δ₀, hε, hK, hδ₀, hhead⟩ := log_chowla_two_budget_head_forallX_sq_count
  refine ⟨ε, K, δ₀, hε, hK, hδ₀, ?_⟩
  intro U1floor
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  obtain ⟨X₀, ω, Hlo, Hhi, hfa⟩ := hhead 0 (max U1floor H₀)
  refine ⟨X₀, ω, Hlo, Hhi, ?_⟩
  intro X hX
  obtain ⟨R, hReps, _, hRU1, hRg, hcount, hRtow, hR⟩ := hfa X hX
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)


/-- **⟦THE SEAL, SCALE-THREADED⟧** — `MRTPortTrivialSplit.m4_exit_socket_split_sq_trivial`
with the `g`-lever replaced by a prescribed outer scale.  Payload sed'd VERBATIM. -/
theorem m4_exit_socket_split_sq_trivial_forallX :
    ∃ (ε : ℚ) (c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ (U1floor : ℕ), ∃ (X₀ ω Hlo Hhi : ℕ), ∀ X : ℕ, X₀ ≤ X →
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧
          (R.x = X ∧ R.ω = ω ∧ R.Hlo = Hlo ∧ R.Hhi = Hhi) ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                  ≤ c * (H : ℝ) ^ 2) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, K, δ₀, hε, hK, hδ₀, hsock⟩ := m4_exit_socket_split_sq_arc_forallX
  have hc : 0 < δ₀ / (2 * K) := div_pos hδ₀ (by linarith)
  refine ⟨ε, δ₀ / (2 * K), hε, hc, ?_⟩
  intro U1floor
  obtain ⟨X₀, ω, Hlo, Hhi, hfa⟩ := hsock U1floor
  refine ⟨X₀, ω, Hlo, Hhi, ?_⟩
  intro X hX
  obtain ⟨R, hReps, hRU1, hRg, hRtow, hR⟩ := hfa X hX
  refine ⟨R, hReps, hRU1, hRg, hRtow, ?_⟩
  intro hdoor
  refine hR lamCoeff 0 (fun _ => δ₀ / (2 * K)) 0 (fun m => by simp)
    (fun _ => hc.le) hdoor ?_ ?_
  · intro H _ hlo hhi
    have hz : ∀ (n : ℕ) (α : ℝ), absWindowSum (0 : ℕ → ℂ) H n α = 0 := by
      intro n α
      unfold absWindowSum
      simp
    simp [hz]
  · intro H _ _
    have hK' : (2 : ℝ) * K ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < 2 * K)
    field_simp
    linarith

end Salt.MR

end
