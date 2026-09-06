/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.HloExport

/-!
# The spine head as an `ε`-FAMILY — the conditional `∀ ε ≤ 1/500` restatement
(QUEUE P3 item 11, the design block of 2026-09-05; STATEMENT-ONLY at the freeze)

`log_chowla_two_budget_head_g_sq_count_hloCap_pinned` (`HloExport.lean:519`) PINS `ε := 1/500`
in place of the landed `exists_rat_btwn` choice, so that the door threshold
`δ₀ = cD3/(16·C)·ε/4` is a numeral (`≥ 1/838400`) and the `MR` lane's register can be met.  The
four smallness demands on `ε` are all UPPER bounds (`ε ≤ cE/(32·log 4)`, `ε < 1/2`,
`ε ≤ cD3/16`, `ε ≤ cD3/(16·C)`), each met at `1/500` with headroom (the binding arm at `1.19×`),
so every `ε ≤ 1/500` meets them by monotonicity — and every other input of the head is
`ε`-parametric already (`chowlaRegime_exists_param_head_tower45'_hloCap eps`, `bigXi_bounded ε`,
`hbudget1_witness`).  The `08/21` fence brief said so ("the interior is `ε`-parameterised under
upper bounds only"); this file is that sentence as a STATEMENT: the head at every `ε ≤ 1/500`,
with the door demanded at `ρ ≤ δ₀(ε)` and the EXCHANGE RATE exported as a conjunct,
`ε/1677 ≤ δ₀`.

What this is NOT: an unconditional `∀ ε` theorem.  The door `MRTUniformityXiL2 R ρ` is a binder,
and the `MR` lane PRODUCES it at ONE grade (`mrtUniformityXiL2_holds_flat`: `ρ ≤ 1/837782` on
the flat family at `ε ≥ 1/500`).  Below `ε = 1/500` the demanded grade `δ₀(ε) ∝ ε` falls under
the produced one — the row's "exchange rate, not a wall" — and only the crown
`MRTDoorAllGrades` (`Salt/MR/DoorReceipt.lean:1213`, NO producer) supplies it;
`Salt/MR/EpsFamilyReceipt.lean` states that composition.  The landed tripwire
`spine_eps_constant_floor` (`SpineEpsFence.lean:102`) is UNTOUCHED: this head is added BESIDE
the pinned one (QUEUE item 11, fence (2)), and the tripwire keeps guarding the `∃ ε` terminal.

Honest label: no new unconditional theorem; a restatement whose value is the exported
exchange rate.  Nothing bears on twin primes.  STATEMENT-ONLY at the freeze.
-/

-- The pinned head's core and the two cap helpers are `private` in `HloExport`; they are reached
-- by `open private` (Batteries), the corpus's sanctioned device (`XThread.lean:50`,
-- `S16Compose.lean:63`) — no landed file gains a declaration.
open private spine_False_core_xi_sq_cap mutualInfo_window_comm_cap hloCap_shuffle from
  Salt.Entropy.Chowla.HloExport

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **E1 (class B) — THE `L²` SPINE-BUDGET HEAD AT EVERY `ε ≤ 1/500`, WITH THE EXCHANGE RATE.**
`log_chowla_two_budget_head_g_sq_count_hloCap_pinned`'s statement with `ε` moved from the
`∃`-prefix to a HYPOTHESIS `0 < ε ≤ 1/500`, the two pin conjuncts dropped, and ONE conjunct added:
`ε/1677 ≤ δ₀` (from `δ₀ = cD3/(16·C)·ε/4` with `1/4 ≤ cD3`, `C ≤ 6.55`:
`cD3/(16·C) ≥ 5/2096`, so `δ₀ ≥ 5ε/8384 = ε/1676.8`; `1677` is the SMALLEST integer that works —
the landed leaves give `5/2096` with ZERO slack).  Everything else is the pinned head's, item for
item.  ⚠ NO `K` UPPER BOUND IS EXPORTED here (unlike `FlatHeadForm`'s `K ≤ 2^539`): the exchange
rate is consumable at the L² grade only, so a consumer must not hunt for a `K`-numeral.

Recipe: the pinned head's proof VERBATIM (`HloExport.lean:519–618`) with `hεdef : ε = 1/500`
replaced by the hypothesis: `hεcE`, `hε_half_lt`, `hε_D3`, `hε_D3C`, `hε2`, `hεQ1` each by
`le_trans`/`lt_of_le_of_lt` from `ε ≤ 1/500` and the pinned-leaf numerals (`hcEge`, `hcD3ge`,
`hCnum`, `hlog4eq`); the exchange-rate conjunct from `hkey : 5/2096 ≤ cD3/(16·C)` (the landed
line) by `nlinarith`/`linarith` on `ε ≥ 0`; the three `private` names of `HloExport`
(`spine_False_core_xi_sq_cap`, `mutualInfo_window_comm_cap`, `hloCap_shuffle`) via
`open private … from Salt.Entropy.Chowla.HloExport` (the landed idiom, `XThread.lean:50`;
a second at `S16Compose.lean:63`). -/
theorem log_chowla_two_budget_head_g_sq_count_hloCap_epsFamily (ε : ℚ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 500) :
    ∃ (K δ₀ : ℝ) (Hcap : ℕ), 0 < K ∧ 0 < δ₀ ∧ (ε : ℝ) / 1677 ≤ δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_bounded
  obtain ⟨cD3, hcD3, hcD3ge, H₀D3, hD3⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C, hC, hCcap, hcm⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hCnum : C ≤ 655 / 100 := by
    rw [hlog4eq] at hCcap; linarith
  -- ⟦THE FAMILY⟧ `ε` is a parameter under an upper bound, not a pin
  have hεR : ((ε : ℚ) : ℝ) ≤ 1 / 500 := by
    calc ((ε : ℚ) : ℝ) ≤ (((1 : ℚ) / 500 : ℚ) : ℝ) := by exact_mod_cast hε
      _ = 1 / 500 := by norm_num
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεQpos : 0 < ε := hε0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    have h : (1 : ℝ) / 500 ≤ cE / (32 * Real.log 4) := by
      rw [le_div_iff₀ (by positivity), hlog4eq]; linarith
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by linarith
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    have h : (1 : ℝ) / 500 ≤ cD3 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
    linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    have h : (1 : ℝ) / 500 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    linarith
  have hεQ1 : ε ≤ 1 / 2 := by
    have : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith
  -- ⟦THE EXCHANGE RATE⟧ `δ₀ = cD3/(16·C)·ε/4 ≥ 5ε/8384 ≥ ε/1677`
  have hδ₀ge : (ε : ℝ) / 1677 ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    have hkey : (5 : ℝ) / 2096 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hkey) hεR0.le, hεR0]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4))) := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4,
    max 4000000 (max A (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), hK,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hδ₀ge, ?_⟩
  intro extraFloor U1floor g₅
  obtain ⟨R, hReps, hRHlo, hRg, hRtow, hRcap⟩ :=
    chowlaRegime_exists_param_head_tower45'_hloCap ε hεQpos hεQ1
      (max A (max extraFloor U1floor)) g₅
  rw [hAdef] at hRHlo
  have hxiHlo : H₀xi ≤ R.Hlo :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hRHlo
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, ?_, hRtow, ?_, ?_⟩
  · intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · rw [hRcap]
    exact hloCap_shuffle _ _ _ _ _
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm_cap]; exact hMI
  have hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
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
  have hbudget2 : ρ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  exact spine_False_core_xi_sq_cap R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla
