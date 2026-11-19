/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE PRICED LEAVES⟧ — the three head constants, CITABLE FROM BELOW (node EPSPIN)

`log_chowla_two_budget_head_g_sq_count_hloCap` (`HloExport.lean:390`) chooses its
`ε` by `exists_rat_btwn` under a four-arm `min` built from three `∃`-delivered
leaf constants, and emits `δ₀ = cD3/(16·C)·ε/4`.  Every one of those leaves is
destructed by `obtain`, i.e. is a `Classical.choose` the kernel cannot evaluate —
so the head's `δ₀` is UNBOUNDED BELOW as stated, and the register witness on the
capstone side can only be checked at closed-form stand-ins (the reachability
caveat of `Salt/MR/ConstantsExposed.lean`).

This file mints the ADDITIVE TWINS that close the gap at the leaves.  Each
declaration is a landed statement plus ONE conjunct pinning the landed `refine`
witness, with the landed body replayed verbatim underneath:

| twin | landed | conjunct |
|---|---|---|
| `primeWindow_sum_inv_ge_bounded` | `WindowMertensLower.lean:249` | `1/4 ≤ c` |
| `hbudget_holds_bounded` | `HBudget.lean:733` | `1/4 ≤ c` (carry) |
| `hreduce_holds_final_bounded` | `HBudget.lean:754` | `1/4 ≤ c` (carry) |
| `circle_method_estimate_sq_bounded` | `CircleMethod.lean:1093` | `C ≤ 1 + 2·C₀` |

Nothing landed is touched; the two carries are the landed proofs reading the
previous twin (the `c` of `hbudget_holds`/`hreduce_holds_final` IS D3's `c`,
passed through unchanged — `HBudget.lean:748`, `HBudget.lean:771`).

⟦WHY THE BODIES ARE REPLAYED⟧  All four statements are `∃`-shaped and the
constant occurs ANTITONICALLY in each (a smaller `c`, a larger `C`, weakens the
statement), so no consequence of the landed form can recover the witness's value:
the only route is to re-run the landed proof with the numeral kept.  The replays
cite `private` helpers of their home files (`window_Z_pos`, `absX_le_one`,
`window_sum_inv_sq`, `IF_unfold`, `per_term`, `boundary_card_le` from `HBudget`;
`windowVal_c_norm_le`, `T_collapse`, `periodization_total` from `CircleMethod`),
reached here by `open private … from … in` — no landed file gains a declaration.

⟦O13-e, 2026-11-14: NONE OF THE FOUR IS A REPLAY NOW⟧  The argument above rules out
recovering the witness from the landed `∃`-FORM, not from the landed PROOF.  The proof of
`primeWindow_sum_inv_ge` is now stated once at its explicit constant
(`WindowMertensLower.primeWindow_sum_inv_ge_at`), that of `circle_method_estimate_sq` likewise
(`CircleMethod.circle_method_estimate_sq_at`), and that of `hbudget_holds` once for any `c`
with its window bound (`HBudget.hbudget_holds_of`); the landed theorems and their twins here
are both corollaries, so those three landed files each gained a declaration.
`hreduce_holds_final_bounded` was never a replay: it is a five-line carry over the budget.

⟦WHAT THEY BUY⟧  `1/4 ≤ cD3` and `C ≤ 1 + 2·C₀ = CcmExpr ≤ 6.55` make all four
`ε`-arms citable at the numeral `ε = 1/500` (`ConstantsExposed.eps_admissible`),
and `1/4 ≤ cE` (the `hreduce` carry — the SAME leaf, D3's constant) covers the
one arm that is not a `cD3` arm.  Downstream: `HloExport.lean` §4.
-/
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.CircleMethod
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction

namespace Salt.Entropy.Chowla

/-! ## §1 The Mertens leaf, with its `1/4` kept -/

/-- **THE `D3` LEAF, PINNED** (`primeWindow_sum_inv_ge_bounded`) —
`WindowMertensLower.primeWindow_sum_inv_ge` plus the conjunct `1/4 ≤ c`, at the
landed `refine` witness `c = 1/4`.  The proof is
`primeWindow_sum_inv_ge_at`, the explicit-constant form both share. -/
theorem primeWindow_sum_inv_ge_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ), H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      c / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
  ⟨1 / 4, by norm_num, le_rfl, primeWindow_sum_inv_ge_at⟩

/-! ## §2 The budget carry -/

/-- **HBUDGET, PINNED** (`hbudget_holds_bounded`) — `HBudget.hbudget_holds` plus
`1/4 ≤ c`.  It reads §1 in place of
`primeWindow_sum_inv_ge` and re-emits the conjunct; the proof is `HBudget.hbudget_holds_of`. -/
theorem hbudget_holds_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded
  exact ⟨c, hc, hcge, H₀, hbudget_holds_of c hc H₀ hD3⟩

/-- **HREDUCE-FINAL, PINNED** (`hreduce_holds_final_bounded`) —
`HBudget.hreduce_holds_final` plus `1/4 ≤ c`, the second verbatim carry
(`HBudget.lean:770–774` reading §2).  This is the `cE` the head consumes. -/
theorem hreduce_holds_final_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
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
  obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_bounded
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig hseed
  exact hreduce_holds eps H hseed
    (hbud eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

/-! ## §3 The circle-method constant, capped -/

/-- **THE SQUARED CIRCLE-METHOD ESTIMATE, CAPPED**
(`circle_method_estimate_sq_bounded`) — `CircleMethod.circle_method_estimate_sq`
plus the conjunct `C ≤ 1 + 2·C₀`, at the landed `refine` witness `C = 1 + 2·C₀`.
The proof is `CircleMethod.circle_method_estimate_sq_at`, the explicit-constant
form both share. -/
theorem circle_method_estimate_sq_bounded (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 + 2 * C₀ ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) :=
  ⟨1 + 2 * C₀, by positivity, le_rfl, circle_method_estimate_sq_at C₀ hC₀⟩

end Salt.Entropy.Chowla

