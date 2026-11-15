/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE PRICED LEAVES AT SHIFT `h`⟧ — wave X of the `_L_gk` h-family, part (i)

`HeadPinLeaves` keeps the three head constants of the `h = 1` budget head citable from below
(`1/4 ≤ cD3`, `1/4 ≤ cE`, `C ≤ 1 + 2·C₀`).  At shift `h` the head (`HloExportFlatH`) needs
the SAME three, at the `h`-family leaves: the Mertens leaf `primeWindow_sum_inv_ge_bounded`
is `h`-blind and REUSED; the two others were replayed here until O13-e (2026-11-14) and are now
corollaries of their bases' shared proofs (below).

⟦WHY THE BODIES ARE REPLAYED, AGAIN⟧  `HeadPinLeaves.lean:30-37` is standing law: the
constant occurs ANTITONICALLY in every pinned `∃`-leaf, so no consequence of the landed form
recovers the witness; the only route is to re-run the proof with the numeral kept.
`hbudget_holds_h` (`HBudget.lean:1515`) draws its `c` from the UNPINNED
`primeWindow_sum_inv_ge`, so `1/4 ≤ cE` is unobtainable by weakening — `hbudget_holds_h_bounded`
reads `primeWindow_sum_inv_ge_bounded` instead and re-emits the conjunct, exactly as
`hbudget_holds_bounded` does for `h = 1`.  Since O13-e (2026-11-14) it does so by calling the
one proof `HBudget.hbudget_holds_h_of`, not by replaying it (`HeadPinLeaves.lean`'s addendum).
`circle_method_estimate_sq_bounded_h_core` is `circle_method_estimate_sq_h_core` with the
cap conjunct `C ≤ h·(1 + 2·C₀)` at the landed witness; both are corollaries of
`CircleMethod.circle_method_estimate_sq_h_core_at` (O13-e, 2026-11-14), and
`circle_method_estimate_sq_bounded_h` is `ShiftFork.circle_method_estimate_sq_h`'s `bigXiH`
wrapper over it.  `hreduce_holds_final_h_bounded` is the seven-line carry.

⟦WHAT MOVES, AND ONLY WHAT MOVES⟧  The cap is `C ≤ h·(1 + 2·C₀)` — the SCALING named in the
commission's word 8(b), because the `h`-core's witness is `h·(1 + 2C₀)` (`CircleMethod.lean`);
nothing else in any statement differs from its `h = 1` twin but the shift and the `ε·h` gate the
`h`-family already carries.  The replays cited `private` helpers of their home files through
`open private … from … in`; since O13-e (2026-11-14) the shared proofs live in those files.

Nothing here bears on twin primes: three constants kept visible at shift `h`.
-/
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.CircleMethod
import Salt.Entropy.Chowla.ShiftFork
import Salt.Entropy.Chowla.HeadPinLeaves
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction

namespace Salt.Entropy.Chowla

/-! ## §1 The budget carry at shift `h` -/

/-- **HBUDGET AT SHIFT `h`, PINNED** (`hbudget_holds_h_bounded`) — `HBudget.hbudget_holds_h`
plus `1/4 ≤ c`.  It reads `primeWindow_sum_inv_ge_bounded`
in place of `primeWindow_sum_inv_ge` and re-emits the conjunct; the proof is
`HBudget.hbudget_holds_h_of`. -/
theorem hbudget_holds_h_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded
  exact ⟨c, hc, hcge, H₀, hbudget_holds_h_of c hc H₀ hD3⟩

/-- **HREDUCE-FINAL AT SHIFT `h`, PINNED** (`hreduce_holds_final_h_bounded`) —
`HBudget.hreduce_holds_final_h` plus `1/4 ≤ c`, the second carry.  This is the `cE` the
`h`-head consumes. -/
theorem hreduce_holds_final_h_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_h_bounded
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
    hseed
  exact hreduce_holds_h h eps H hseed
    (hbud h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

/-! ## §2 The circle-method constant at shift `h`, capped -/

/-- **THE SQUARED CIRCLE-METHOD ESTIMATE AT SHIFT `h`, CAPPED, CORE**
(`circle_method_estimate_sq_bounded_h_core`) — `CircleMethod.circle_method_estimate_sq_h_core`
plus the conjunct `C ≤ h·(1 + 2·C₀)`, at the landed `refine` witness `C = h·(1 + 2·C₀)`.  The
body is `circle_method_estimate_sq_h_core`'s (1366–1508 when written); the one edit is `le_rfl`. -/
theorem circle_method_estimate_sq_bounded_h_core (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * C₀) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiTwistFilter h eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) :=
  ⟨(h : ℝ) * (1 + 2 * C₀), mul_pos (by exact_mod_cast hh) (by positivity), le_rfl,
    circle_method_estimate_sq_h_core_at h hh C₀ hC₀⟩

/-- **THE SQUARED CIRCLE-METHOD ESTIMATE AT SHIFT `h`, CAPPED**
(`circle_method_estimate_sq_bounded_h`)
— the `bigXiH`-facing wrapper (`ShiftFork.circle_method_estimate_sq_h`) over the capped core:
the set swap `bigXiH_eq_twistFilter` is the only step. -/
theorem circle_method_estimate_sq_bounded_h (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * C₀) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiH h eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  obtain ⟨C, hC, hCcap, hest⟩ := circle_method_estimate_sq_bounded_h_core h hh C₀ hC₀
  refine ⟨C, hC, hCcap, ?_⟩
  intro eps H _ x1 hx1 hcard
  rw [bigXiH_eq_twistFilter]
  exact hest eps H x1 hx1 hcard

end Salt.Entropy.Chowla
