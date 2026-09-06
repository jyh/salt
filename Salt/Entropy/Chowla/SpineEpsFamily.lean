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

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **E1 (class B) — THE `L²` SPINE-BUDGET HEAD AT EVERY `ε ≤ 1/500`, WITH THE EXCHANGE RATE.**
`log_chowla_two_budget_head_g_sq_count_hloCap_pinned`'s statement with `ε` moved from the
`∃`-prefix to a HYPOTHESIS `0 < ε ≤ 1/500`, the two pin conjuncts dropped, and ONE conjunct added:
`ε/1677 ≤ δ₀` (from `δ₀ = cD3/(16·C)·ε/4` with `1/4 ≤ cD3`, `C ≤ 6.55`:
`cD3/(16·C) ≥ 5/2096`, so `δ₀ ≥ 5ε/8384 = ε/1676.8`).  Everything else is the pinned head's,
item for item.

Recipe: the pinned head's proof VERBATIM (`HloExport.lean:519–640`) with `hεdef : ε = 1/500`
replaced by the hypothesis: `hεcE`, `hε_half_lt`, `hε_D3`, `hε_D3C`, `hε2`, `hεQ1` each by
`le_trans`/`lt_of_le_of_lt` from `ε ≤ 1/500` and the pinned-leaf numerals (`hcEge`, `hcD3ge`,
`hCnum`, `hlog4eq`); the exchange-rate conjunct from `hkey : 5/2096 ≤ cD3/(16·C)` (the landed
line) by `nlinarith`/`linarith` on `ε ≥ 0`; the three `private` names of `HloExport`
(`spine_False_core_xi_sq_cap`, `mutualInfo_window_comm_cap`, `hloCap_shuffle`) via
`open private … from Salt.Entropy.Chowla.HloExport` (the landed idiom, `XThread.lean:330`). -/
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
  sorry

end Salt.Entropy.Chowla
