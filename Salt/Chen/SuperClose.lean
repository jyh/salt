/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SuperPanelsE
import Salt.Chen.SuperPanelsO
import Salt.Chen.MassLedger
import Salt.Chen.MassLedgerA1

/-!
# SS3c close — the numeric keystone's final output

Design: `docs/blueprints/flags.md`, `2026-07-13 SS2`/`SS3`.  Final composition node of the SS3
transcription.  The two mass-ledger reductions of `SuperSolution.lean` close through the concrete
super-solution `(Ebar, Obar)` of `SuperProfileDef`:

* nonnegativity / integrability / the two `∫`-budgets — `SuperProfileDef`,
* the even inequality `hSE` — `SuperPanelsE.hSE_holds` (this rung, SS3c),
* the odd inequality `hSO` — `SuperPanelsO.hSO_holds` (SS3b).

With both panel inequalities landed, the finals below are **unconditional**.  The mass ledgers of
`MassLedger`/`MassLedgerA1` then turn the budget sums into the `Fchain`/`fchain` value bounds the
H-glue consumes.

## Outputs

* `massSum_le_A2_final`  : `∀ N, Σ_{even k, 2≤k<N} massE k ≤ 43/75`     (the A₂ mass budget).
* `massOSum_le_A1_final` : `∀ N, Σ_{odd j, 3≤j<N} massO j ≤ 11/125`     (the A₁ mass budget).
* `Fchain_A2_final`      : `Fchain N s ≤ 268/100` on `[4/3, 3]`         (the A₂ value bound).
* `fchain_A1_final`      : `9779/10000 ≤ fchain N s` on `[39992/10000, 4]` (the A₁ value bound).
-/

open MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-- **The A₂ mass budget.**  `Σ_{even k, 2≤k<N} massE k ≤ 43/75` for every `N`, from the concrete
super-solution `(Ebar, Obar)`: nonneg + integrable + the even budget (`SuperProfileDef`),
`hSE_holds` (SS3c) and `hSO_holds` (SS3b). -/
theorem massSum_le_A2_final :
    ∀ N, (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k) ≤ 43 / 75 :=
  massSum_le_A2_of_superSolution Ebar Obar Ebar_nonneg Obar_nonneg
    Ebar_intervalIntegrable Obar_intervalIntegrable hSE_holds hSO_holds Ebar_integral_le

/-- **The A₁ mass budget.**  `Σ_{odd j, 3≤j<N} massO j ≤ 11/125` for every `N`. -/
theorem massOSum_le_A1_final :
    ∀ N, (∑ j ∈ (Finset.range N).filter (fun j => Odd j ∧ 3 ≤ j), massO j) ≤ 11 / 125 :=
  massOSum_le_A1_of_superSolution Ebar Obar Ebar_nonneg Obar_nonneg
    Ebar_intervalIntegrable Obar_intervalIntegrable hSE_holds hSO_holds Obar_integral_le

/-- **The A₂ value bound** (the numeric keystone's `Fchain` output).  `Fchain N s ≤ 268/100`
uniformly on the A₂ grid `[4/3, 3]`, for every truncation depth `N ≥ 1`. -/
theorem Fchain_A2_final (N : ℕ) (hN : 1 ≤ N) :
    ∀ s ∈ Set.Icc (4 / 3 : ℝ) 3, Fchain N s ≤ 268 / 100 :=
  Fchain_le_A2_of_massSum N hN (massSum_le_A2_final N)

/-- **The A₁ value bound** (the numeric keystone's `fchain` output).  `9779/10000 ≤ fchain N s`
uniformly on the A₁ window `[39992/10000, 4]`, for every truncation depth `N ≥ 2`. -/
theorem fchain_A1_final (N : ℕ) (hN : 2 ≤ N) :
    ∀ s ∈ Set.Icc (39992 / 10000 : ℝ) 4, (9779 / 10000 : ℝ) ≤ fchain N s :=
  fchain_ge_A1_of_massSums N hN (massSum_le_A2_final N) (massOSum_le_A1_final N)

end Salt.Chen
