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
| `primeWindow_sum_inv_ge_bounded` | `WindowMertensLower.lean:56` | `1/4 ≤ c` |
| `hbudget_holds_bounded` | `HBudget.lean:448` | `1/4 ≤ c` (carry) |
| `hreduce_holds_final_bounded` | `HBudget.lean:705` | `1/4 ≤ c` (carry) |
| `circle_method_estimate_sq_bounded` | `CircleMethod.lean:873` | `C ≤ 1 + 2·C₀` |

Nothing landed is touched; the two carries are the landed proofs reading the
previous twin (the `c` of `hbudget_holds`/`hreduce_holds_final` IS D3's `c`,
passed through unchanged — `HBudget.lean:462`, `HBudget.lean:721`).

⟦WHY THE BODIES ARE REPLAYED⟧  All four statements are `∃`-shaped and the
constant occurs ANTITONICALLY in each (a smaller `c`, a larger `C`, weakens the
statement), so no consequence of the landed form can recover the witness's value:
the only route is to re-run the landed proof with the numeral kept.  The replays
cite `private` helpers of their home files (`window_Z_pos`, `absX_le_one`,
`window_sum_inv_sq`, `IF_unfold`, `per_term`, `boundary_card_le` from `HBudget`;
`windowVal_c_norm_le`, `T_collapse`, `periodization_total` from `CircleMethod`),
reached here by `open private … from … in` — no landed file gains a declaration.

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
(`HBudget.lean:721–725` reading §2).  This is the `cE` the head consumes. -/
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

open private windowVal_c_norm_le T_collapse periodization_total from
  Salt.Entropy.Chowla.CircleMethod in
/-- **THE SQUARED CIRCLE-METHOD ESTIMATE, CAPPED**
(`circle_method_estimate_sq_bounded`) — `CircleMethod.circle_method_estimate_sq`
plus the conjunct `C ≤ 1 + 2·C₀`, at the landed `refine` witness `C = 1 + 2·C₀`.
The body is `CircleMethod.lean:886–989` verbatim; the only edit is the extra
`le_rfl`. -/
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
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  refine ⟨1 + 2 * C₀, by positivity, le_rfl, ?_⟩
  intro eps H _ x1 hx1 hcard
  by_cases hH2 : 2 ≤ H
  · -- main regime: H ≥ 2, so log H > 0
    have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    set Φ₁ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ₁
    have h1 : ∀ j, ‖Φ₁ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    -- the reality reflection at the (real, integer-valued) window datum
    have hreal : Φ₁ = fun j : ZMod H => ((windowVal H x1 (ZMod.val j) : ℝ) : ℂ) := by
      funext j
      simp only [hΦ₁]
      push_cast
      ring
    have hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ₁ (-ξ)‖ = ‖ZMod.dft Φ₁ ξ‖ := by
      intro ξ
      rw [hreal]
      exact norm_dft_neg_of_real (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℝ)) ξ
    set S : ℝ := ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ ^ 2 with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₁ (m + ((p : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₁ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) with hW
    -- collapse and split (the SQUARED major arm)
    have hWT : (H : ℂ) * T = W := T_collapse Φ₁ Φ₁
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * S :=
      fourier_split_sq Φ₁ h1 hrefl hC₀ hlog hcard
    -- cast L and periodization (the diagonal instance of `periodization_total`)
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x1 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total hx1 hx1
    -- assemble
    have hLT : |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by
      have h := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at h
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := h
        _ ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have hTle : ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S := by
      have hHTle : (H : ℝ) * ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
          + (2 * C₀ / Real.log (H : ℝ)) * S := hTnorm ▸ hnormW
      have key : (H : ℝ) * ‖T‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S) := by
        refine hHTle.trans (le_of_eq ?_)
        field_simp
      exact le_of_mul_le_mul_left key hHpos
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => sq_nonneg _)
    have hquot_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hrem_nn : 0 ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + (1 / (H : ℝ)) * S / Real.log (H : ℝ) :=
      add_nonneg (mul_nonneg hC₀.le hquot_nn)
        (div_nonneg (mul_nonneg (by positivity) hS_nn) hlog.le)
    have heq : (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S)
          + C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + (1 / (H : ℝ)) * S / Real.log (H : ℝ)) := by
      field_simp
      ring
    calc |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S) := by
          rw [heq]; linarith [hTle, hcard, hrem_nn]
  · -- degenerate: H = 1
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hp2 := (prime_of_mem_primeWindow p.2).two_le
      have hge : ¬ (j + (p : ℕ) < H) := by omega
      have hz : windowVal H x1 (j + (p : ℕ)) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

end Salt.Entropy.Chowla

