/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE SPINE AT THE FLAT THRESHOLD (the `entropy_decrement` cone, freeze F-7)

The flat twins of the two spine consumers that actually READ the decrement
threshold `κ`:

* `hbudget1_witnessFlat` — the SPINE-BUDGET AM–GM residual discharged at the
  FLAT `κ = H/(A·log H)` and the HEIGHT-1 floor `budgetFloorFlat`.  This is the
  one place in the whole spine where `κ`'s VALUE is spent (`SpineFinal.lean:632`
  in the landed cone): the four-slice `shellError` margin.  Every arm but the
  `κ`-arm is byte-identical to the landed `hbudget1_witness`; the `κ`-arm is
  `budget_factsFlat` (iv) in place of `budget_facts` (iv).
* `log_chowla_two_of_doorFlat` — `TowerDischarge.lean`'s citation surface at the
  flat threshold: the `H`-selection and `hI` discharged TOGETHER by
  `entropy_decrementFlat`, `hbudget2` folded into `δ₀ = ε/(2K)`.

Everything else in the spine is `κ`-OPAQUE and carries VERBATIM through
`R.toChowlaRegime` — `shellError` itself, `deficit_le_log_two`, `bracket_close`,
`log_chowla_two_conditional`, the whole Concentration/FBridge/Transport/
OuterCombine/WeakUniform chain.  That is what the extension-bundle shape of
`ChowlaRegimeFlat` buys, and it is why this file is short.

## What is NOT here (and why) — for the wave ledger

The `_sq_count` / `hloCap` / `pinned` heads' flat twins cannot be written from
outside their own files: their cores (`spine_False_core`, `spine_False_core_xi`,
`spine_False_core_xi_sq` in `SpineFinal.lean`, `spine_False_core_xi_sq_cap` in
`HloExport.lean`) are `private`.  They additionally need the FLAT BUILDER (a
`ChowlaRegimeFlat`-producing twin of `chowlaRegime_exists_param_head_tower45'`,
whose `Hhi` must be pinned at the FLAT tower value and whose floor must be
re-based per FLAT-REF's `flatBase A`) — an obligation the freeze lists
separately.  Both blockers are recorded rather than worked around: no landed
declaration is edited here.
-/
import Salt.Entropy.Chowla.DecrementFlat
import Salt.Entropy.Chowla.BudgetFlat
import Salt.Entropy.Chowla.SpineClose
import Salt.Entropy.Chowla.Theorem23Shell
import Salt.Entropy.Chowla.BudgetDeficit

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### The mutual-information order swap (the flat cone's own copy) -/

/-- `entropy_decrementFlat` produces `I[liouvilleWindow : residueWindow]`; the
    shell's `hI` binder consumes the other order.  Mutual information is
    symmetric. -/
lemma mutualInfo_window_comm_flat (R : ChowlaRegimeFlat) (H : ℕ) :
    I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  simp only [mutualInfo_def]
  rw [entropy_comm (measurable_residueWindow R.eps H) (measurable_liouvilleWindow H)
    (logMeasure R.x R.ω)]
  ring

/-! ### The SPINE-BUDGET witness at the flat threshold -/

set_option maxHeartbeats 1000000 in
-- the four-slice `shellError` calc is at ~1.3× the default budget here: the landed
-- `hbudget1_witness` reads `κ` as a CLOSED expression, whereas this twin carries `A`
-- as a free real, so `rw`/`linarith` see an extra opaque atom throughout the chain.
/-- **`hbudget1_witness`'s FLAT TWIN** (the one `κ`-VALUE consumer of the spine).
At `c₀ := cD3/(16·C)` the entropy-decrement AM–GM residual is DISCHARGED at the
FLAT budget `κ = H/(A·log H)`: there are decrement parameters `t`, `g` for which
the four-slice `shellError` margin holds.  `S1` is exact, `S2 ⟸ ε ≤ cD3/(16·C)`,
`S3 ⟸ ε ≤ cD3/16`, and `S4` via `bracket_close` and `deficit_le_log_two` at
`β = cD3·ε/(144·log 4)`, with `t = √(g·(κ+log2))`, `g = gcap`.

Stated at a LANDED regime plus a free real `A` — the witness never reads the flat
tower, only the flat threshold's SHAPE — so `hbudget1_witnessFlat` below is a
one-line specialization.  Two binders differ from the landed statement, and only
two: the floor is the HEIGHT-1 `budgetFloorFlat ε β A` (not the height-3
`budgetFloor ε β`), and the design demand `budgetAFlat ε β ≤ A` is carried (it is
exactly what fact (iv) spends). -/
theorem hbudget1_witness_flatKappa (R : ChowlaRegime) (H : ℕ) [NeZero H]
    (A cD3 C : ℝ) (hApos : 0 < A) (hcD3 : 0 < cD3) (hC : 0 < C)
    (hε_half : (R.eps : ℝ) ≤ 1 / 2)
    (hε_D3 : (R.eps : ℝ) ≤ cD3 / 16)
    (hε_D3C : (R.eps : ℝ) ≤ cD3 / (16 * C))
    (hhi : H ≤ R.Hhi)
    (hAge : budgetAFlat (R.eps : ℝ) (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ A)
    (hfloor : budgetFloorFlat (R.eps : ℝ)
        (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) A ≤ H) :
    ∃ (t g : ℝ), 0 < t ∧ 0 < g ∧
      g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
          / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 ∧
      C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H t g ((H : ℝ) / (A * Real.log (H : ℝ)))
        ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by
  classical
  have hlog4_pos : 0 < Real.log 4 := log_four_pos_aux
  have hlog2_pos : 0 < Real.log 2 := log_two_pos_aux
  have hεpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hHRpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  set β : ℝ := cD3 * (R.eps : ℝ) / (144 * Real.log 4) with hβ_def
  have hβpos : 0 < β := by
    rw [hβ_def]
    exact div_pos (mul_pos hcD3 hεpos) (mul_pos (by norm_num) hlog4_pos)
  obtain ⟨hlogH1, hgcap_pos, hApos', hiv, hv⟩ :=
    budget_factsFlat (R.eps : ℝ) β A hεpos hε_half hβpos hApos hAge H hfloor
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith [hlogH1]
  have hΛpos : (0 : ℝ) < (H : ℝ) / Real.log (H : ℝ) := div_pos hHRpos hlogHpos
  set gcap : ℝ := (R.eps : ℝ) ^ 6 * (H : ℝ)
      / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 with hgcap_def
  set κ : ℝ := (H : ℝ) / (A * Real.log (H : ℝ)) with hκ_def
  have hκpos : 0 < κ := by
    rw [hκ_def]; exact div_pos hHRpos (mul_pos hApos' hlogHpos)
  have hs : 0 < κ + Real.log 2 := by linarith [hκpos, hlog2_pos]
  set tcap : ℝ := Real.sqrt (gcap * (κ + Real.log 2)) with htcap_def
  have htcap_pos : 0 < tcap := by
    rw [htcap_def]; exact Real.sqrt_pos.mpr (mul_pos hgcap_pos hs)
  have hdef : Real.log (PH R.eps H : ℝ)
      - H[residueWindow R.eps H ; logMeasure R.x R.ω] ≤ Real.log 2 :=
    deficit_le_log_two R hhi
  have hbr : (tcap + 2 * Real.log 2) / gcap
      + (κ + (Real.log (PH R.eps H : ℝ)
          - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap ≤ β := by
    have hbc := bracket_close gcap β κ
      (κ + (Real.log (PH R.eps H : ℝ)
        - H[residueWindow R.eps H ; logMeasure R.x R.ω]))
      hgcap_pos hβpos hs (by linarith [hdef]) hiv hv
    rw [← htcap_def] at hbc
    exact hbc
  clear_value tcap gcap κ β
  refine ⟨tcap, gcap, htcap_pos, hgcap_pos, le_rfl, ?_⟩
  set W : ℝ := cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) with hW_def
  clear_value W
  have hCne : C ≠ 0 := hC.ne'
  have hS1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ)) = W := by
    rw [hW_def]; field_simp
  have hCε : C * (R.eps : ℝ) ≤ cD3 / 16 := by
    have h16C : (0 : ℝ) < 16 * C := mul_pos (by norm_num) hC
    have h := (le_div_iff₀ h16C).mp hε_D3C
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith [h]
  have hS2 : C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2 ≤ W := by
    have key : C * (R.eps : ℝ) ^ 2 ≤ cD3 / 16 * (R.eps : ℝ) := by nlinarith [hCε, hεpos]
    rw [hW_def]
    calc C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        = ((H : ℝ) / Real.log (H : ℝ)) * (C * (R.eps : ℝ) ^ 2) := by ring
      _ ≤ ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / 16 * (R.eps : ℝ)) :=
          mul_le_mul_of_nonneg_left key hΛpos.le
      _ = cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by ring
  have hshellbd : shellError R H tcap gcap κ ≤ W + W := by
    simp only [shellError, boxGrade]
    have hS3 : (R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) ≤ W := by
      have key : (R.eps : ℝ) ^ 2 ≤ cD3 / 16 * (R.eps : ℝ) := by nlinarith [hε_D3, hεpos]
      rw [hW_def]
      calc (R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          = ((H : ℝ) / Real.log (H : ℝ)) * ((R.eps : ℝ) ^ 2) := by ring
        _ ≤ ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / 16 * (R.eps : ℝ)) :=
            mul_le_mul_of_nonneg_left key hΛpos.le
        _ = cD3 / 16 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := by ring
    have hbox_nn : (0 : ℝ) ≤ 2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
        * ((H : ℝ) / Real.log (H : ℝ)) := by
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (by norm_num) hlog4_pos.le) (by positivity)
      · exact hΛpos.le
    have hcoeff_nn : (0 : ℝ) ≤ 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
        * ((H : ℝ) / Real.log (H : ℝ))) := by linarith [hbox_nn]
    have hS4a : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ)))
        * ((tcap + 2 * Real.log 2) / gcap
            + (κ + (Real.log (PH R.eps H : ℝ)
                - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap)
      ≤ 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ))) * β :=
      mul_le_mul_of_nonneg_left hbr hcoeff_nn
    have hS4b : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ))) * β ≤ W := by
      have h2e : (R.eps : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [hε_half, hεpos]
      have hcD3εA : (0 : ℝ) ≤ cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)) :=
        mul_nonneg (mul_nonneg hcD3.le hεpos.le) hΛpos.le
      have hLHSeq : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
            * ((H : ℝ) / Real.log (H : ℝ))) * β
          = (2 + (R.eps : ℝ) ^ 2)
              * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ))) / 36 := by
        rw [hβ_def]; field_simp; ring
      have hWeq : W = cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)) / 16 := by
        rw [hW_def]; ring
      have h94 : (2 + (R.eps : ℝ) ^ 2) ≤ 9 / 4 := by linarith [h2e]
      have hPQ : (2 + (R.eps : ℝ) ^ 2)
            * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ)))
          ≤ 9 / 4 * (cD3 * (R.eps : ℝ) * ((H : ℝ) / Real.log (H : ℝ))) :=
        mul_le_mul_of_nonneg_right h94 hcD3εA
      rw [hLHSeq, hWeq]
      linarith [hPQ]
    have hS4 : 2 * (2 * Real.log 4 * (2 + (R.eps : ℝ) ^ 2)
          * ((H : ℝ) / Real.log (H : ℝ)))
        * ((tcap + 2 * Real.log 2) / gcap
            + (κ + (Real.log (PH R.eps H : ℝ)
                - H[residueWindow R.eps H ; logMeasure R.x R.ω])) / tcap) ≤ W :=
      le_trans hS4a hS4b
    exact add_le_add hS3 hS4
  have hRHS : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) = 4 * W := by
    rw [hW_def]; ring
  calc C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R H tcap gcap κ
      ≤ W + W + (W + W) := by
        rw [hS1]; exact add_le_add (add_le_add le_rfl hS2) hshellbd
    _ = 4 * W := by ring
    _ = cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) := hRHS.symm

/-- **The SPINE-BUDGET witness at a FLAT REGIME** — `hbudget1_witness_flatKappa`
    at `A := R.A`, the form the flat heads consume. -/
theorem hbudget1_witnessFlat (R : ChowlaRegimeFlat) (H : ℕ) [NeZero H]
    (cD3 C : ℝ) (hcD3 : 0 < cD3) (hC : 0 < C)
    (hε_half : (R.eps : ℝ) ≤ 1 / 2)
    (hε_D3 : (R.eps : ℝ) ≤ cD3 / 16)
    (hε_D3C : (R.eps : ℝ) ≤ cD3 / (16 * C))
    (hhi : H ≤ R.Hhi)
    (hAge : budgetAFlat (R.eps : ℝ) (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ R.A)
    (hfloor : budgetFloorFlat (R.eps : ℝ)
        (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) R.A ≤ H) :
    ∃ (t g : ℝ), 0 < t ∧ 0 < g ∧
      g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
          / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 ∧
      C * ((H : ℝ) / Real.log (H : ℝ)) * (cD3 / (16 * C) * (R.eps : ℝ))
          + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
          + shellError R.toChowlaRegime H t g ((H : ℝ) / (R.A * Real.log (H : ℝ)))
        ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) :=
  hbudget1_witness_flatKappa R.toChowlaRegime H R.A cD3 C R.hApos hcD3 hC
    hε_half hε_D3 hε_D3C hhi hAge hfloor

/-! ### The tower-discharged citation surface at the flat threshold -/

/-- **`log_chowla_two_of_door`'s FLAT TWIN** (`TowerDischarge.lean`'s surface).
For a flat Chowla regime `R`, GIVEN the MRT uniformity door at level `δ`, there
is an admissible decrement level `H ∈ [H₋, H₊]` — produced by
`entropy_decrementFlat` — at which the Liouville/residue mutual information is
below the FLAT budget `κ = H/(A·log H)`, and a door-smallness threshold
`δ₀ = ε/(2K) > 0`, such that log-Chowla-2 does NOT fail as soon as the same
three opaque-constant residuals hold and the door is small.

Discharged here exactly as in the landed twin (no longer inputs): the window
range, `hI` (now at the FLAT `κ`), and `hbudget2`.  The landed
`log_chowla_two_conditional` is consumed VERBATIM through `R.toChowlaRegime` —
it never reads `κ`'s value. -/
theorem log_chowla_two_of_doorFlat (R : ChowlaRegimeFlat) {δ : ℝ}
    (hdoor : MRTUniformity R.toChowlaRegime δ) :
    ∃ (c₁ C K cE κ δ₀ : ℝ) (H₀ H : ℕ),
      0 < c₁ ∧ 0 < C ∧ 0 < K ∧ 0 < cE ∧ 0 < δ₀ ∧
      R.Hlo ≤ H ∧ H ≤ R.Hhi ∧
      I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ ∧
      ∀ (t g : ℝ), 0 < t → 0 < g →
        g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
            / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 →
        H₀ ≤ H →
        (R.eps : ℝ) ≤ cE / (32 * Real.log 4) →
        C * ((H : ℝ) / Real.log (H : ℝ)) * (1 * (R.eps : ℝ))
            + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
            + shellError R.toChowlaRegime H t g κ
          ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) →
        δ ≤ δ₀ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨c₁, C, K, cE, H₀, hc₁, hC, hK, hcE, hblock⟩ :=
    log_chowla_two_conditional R.toChowlaRegime hdoor
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (R.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  refine ⟨c₁, C, K, cE, (H : ℝ) / (R.A * Real.log H),
      (R.eps : ℝ) / (2 * K), H₀, H, hc₁, hC, hK, hcE,
      div_pos hepsRpos (by positivity), hlo, hhi, hI, ?_⟩
  intro t g ht hg hgle hH₀ hepsc hbudget1 hδ hfail
  have hbudget2 : K * δ < 1 * (R.eps : ℝ) := by
    have hle : K * δ ≤ K * ((R.eps : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ (le_of_lt hK)
    have heq : K * ((R.eps : ℝ) / (2 * K)) = (R.eps : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    rw [one_mul]
    linarith
  exact hblock H hlo hhi hH₀ hepsc t g ((H : ℝ) / (R.A * Real.log H)) 1
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla

