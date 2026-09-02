/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE PRICED LEAVES AT SHIFT `h`⟧ — wave X of the `_L_gk` h-family, part (i)

`HeadPinLeaves` keeps the three head constants of the `h = 1` budget head citable from below
(`1/4 ≤ cD3`, `1/4 ≤ cE`, `C ≤ 1 + 2·C₀`).  At shift `h` the head (`HloExportFlatH`) needs
the SAME three, at the `h`-family leaves: the Mertens leaf `primeWindow_sum_inv_ge_bounded`
is `h`-blind and REUSED; the two others are replayed here.

⟦WHY THE BODIES ARE REPLAYED, AGAIN⟧  `HeadPinLeaves.lean:30-37` is standing law: the
constant occurs ANTITONICALLY in every pinned `∃`-leaf, so no consequence of the landed form
recovers the witness; the only route is to re-run the proof with the numeral kept.
`hbudget_holds_h` (`HBudget.lean:1182`) draws its `c` from the UNPINNED
`primeWindow_sum_inv_ge`, so `1/4 ≤ cE` is unobtainable by weakening — `hbudget_holds_h_bounded`
is that body VERBATIM (`HBudget.lean:1182-1465`) over `primeWindow_sum_inv_ge_bounded`, re-emitting
the conjunct exactly as `hbudget_holds_bounded` does for `h = 1`.
`circle_method_estimate_sq_bounded_h_core` is `CircleMethod.lean:1366-1508` verbatim with the
cap conjunct `C ≤ h·(1 + 2·C₀)` at the landed `refine` witness (one extra `le_rfl`), and
`circle_method_estimate_sq_bounded_h` is `ShiftFork.circle_method_estimate_sq_h`'s `bigXiH`
wrapper over it.  `hreduce_holds_final_h_bounded` is the seven-line carry.

⟦WHAT MOVES, AND ONLY WHAT MOVES⟧  The cap is `C ≤ h·(1 + 2·C₀)` — the SCALING named in the
commission's word 8(b), because the `h`-core's witness is `h·(1 + 2C₀)` (`CircleMethod.lean`);
nothing else in any statement differs from its `h = 1` twin but the shift and the `ε·h` gate the
`h`-family already carries.  Every replay cites `private` helpers of its home file through
`open private … from … in`; no landed file gains a declaration.

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

set_option maxHeartbeats 1600000 in
-- The replayed budget aggregation (∫F unfold + three window totals + double-sum
-- reduction) is a large single elaboration, as at the landed `HBudget.lean:1182` and
-- `HeadPinLeaves.lean:258`; the ceiling here is those declarations', unchanged.
open private window_Z_pos absXh_le_one window_sum_inv_sq IF_unfold_h per_term_h boundary_card_le
  from Salt.Entropy.Chowla.HBudget in
/-- **HBUDGET AT SHIFT `h`, PINNED** (`hbudget_holds_h_bounded`) — `HBudget.hbudget_holds_h`
plus `1/4 ≤ c`.  A pure carry: the landed proof reads `primeWindow_sum_inv_ge_bounded` in place
of `primeWindow_sum_inv_ge` and re-emits the conjunct; the rest of the body is
`HBudget.lean:1182-1465` verbatim (the gate is `ε·h ≤ c/(32·log 4)`, linear in `ε·h`). -/
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
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  -- abbreviations kept raw (they interface with the window lemmas via linarith)
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := window_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| ≤ 1 := absXh_le_one h hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ) * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  -- === total 1: the Z-controlled (collapse+swap) slice ≤ (1/8)·SP·H·ε ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hT1 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hstep : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
        have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Real.log_le_log hpR (hple p hp)
        gcongr
      have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
      linarith [hle, heq.le, heq.ge]
    calc (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (H : ℝ) * ((2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hHR.le
      _ ≤ (H : ℝ) * ((eps : ℝ) / 8 * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hHR.le
          exact mul_le_mul_of_nonneg_right hZεbound hSPpos.le
      _ = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by ring
  -- === total 2: the shift slice ≤ (1/16)·SP·H·ε ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (window_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hT2 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : (H : ℝ) * (((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (mul_nonneg (mul_nonneg hHR.le hSPpos.le) (by norm_num : (0:ℝ) ≤ (1:ℝ)/16))]
    exact le_trans (mul_le_mul_of_nonneg_left hfac hHR.le) hmul
  -- === total 3: the boundary slice ≤ (1/16)·SP·H·ε ===
  have hT3 : ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hhR : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    -- THE GATE IS LINEAR IN `ε·h`, NOT `ε²·h`: the boundary count gains exactly one factor
    -- `h` (`boundary_card_le H (p·h)`), and it multiplies the SAME `ε²H/log H` card bound.
    have h32 : (eps : ℝ) * (h : ℝ) * (32 * Real.log 4) ≤ c :=
      (le_div_iff₀ (by positivity)).mp heps_small
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)
        ≤ (1 / 16) * c * (H : ℝ) * (eps : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h32
        (by positivity : (0 : ℝ) ≤ (eps : ℝ) * (H : ℝ) / 16)]
    calc ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
        ≤ ((primeWindow eps H).card : ℝ) * ((h : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habsX hhR) (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) * (h : ℝ) := by rw [mul_one]
      _ ≤ ((2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hcard hhR
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)) / Real.log H := by ring
      _ ≤ ((1 / 16) * c * (H : ℝ) * (eps : ℝ)) / Real.log H := by
          gcongr
      _ = (1 / 16) * (c / Real.log H) * (H : ℝ) * (eps : ℝ) := by ring
      _ ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) hHR.le) hepsR.le
  -- === the reduction: |IF − MAIN| ≤ H·ΣB + card·|X| ≤ T1 + T2 + T3 ===
  have hIF : (∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
        ∂(logMeasure x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ)
            else 0) ∂(logMeasure x ω) := by
    rw [IF_unfold_h h eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod p) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + p * h) : ℝ) else 0) ∂(logMeasure x ω))
  have hMAIN : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hIF, hMAIN, ← Finset.sum_sub_distrib]
  have hcombine : ∀ p ∈ primeWindow eps H,
      (∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) ∂(logMeasure x ω))
        - ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω))
      = ∑ j ∈ Finset.range H,
          ((∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
              (ArithmeticFunction.liouville (n + j + 1) : ℝ)
                * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)
            ∂(logMeasure x ω))
            - (1 / (p : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω))) :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hcombine]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj =>
    per_term_h h hh eps H hx hω hωx hxωH p hp j (Finset.mem_range.mp hj)))).trans ?_
  -- split the inner sum (per-pair bound j-independent; boundary term counted separately)
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hbnd_total : ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
      (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0)
      ≤ ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) := by
    have hbnd : ∀ p ∈ primeWindow eps H, (∑ j ∈ Finset.range H,
        (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0))
        ≤ (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < p)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      -- `boundary_card_le` is ALREADY `h`-general: it is stated at an arbitrary second
      -- argument, so `boundary_card_le H (p * h)` IS the shifted boundary count.  No port.
      have hcardp : (((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℝ)
          ≤ (p : ℝ) * (h : ℝ) := by
        have hnat := boundary_card_le H (p * h)
        have hR : ((((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℕ) : ℝ)
            ≤ ((p * h : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at hR
        exact hR
      calc (((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℝ)
              * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
          ≤ ((p : ℝ) * (h : ℝ))
              * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) :=
            mul_le_mul_of_nonneg_right hcardp (by positivity)
        _ = (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| := by
            rw [show ((p : ℝ) * (h : ℝ))
                    * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
                  = ((p : ℝ) * (1 / (p : ℝ)))
                    * ((h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
                from by ring, mul_one_div, div_self hpR.ne', one_mul]
    calc ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0)
        ≤ ∑ p ∈ primeWindow eps H, (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| :=
          Finset.sum_le_sum hbnd
      _ = ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hT1, hT2, hT3, hbnd_total]

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

open private windowVal_c_norm_le T_collapse_h periodization_total_h from
  Salt.Entropy.Chowla.CircleMethod in
/-- **THE SQUARED CIRCLE-METHOD ESTIMATE AT SHIFT `h`, CAPPED, CORE**
(`circle_method_estimate_sq_bounded_h_core`) — `CircleMethod.circle_method_estimate_sq_h_core`
plus the conjunct `C ≤ h·(1 + 2·C₀)`, at the landed `refine` witness `C = h·(1 + 2·C₀)`.  The
body is `CircleMethod.lean:1366-1508` verbatim; the only edit is the extra `le_rfl`. -/
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
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  refine ⟨(h : ℝ) * (1 + 2 * C₀), mul_pos hhR (by positivity), le_rfl, ?_⟩
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
    set S : ℝ := ∑ ξ ∈ bigXiTwistFilter h eps H, ‖ZMod.dft Φ₁ ξ‖ ^ 2 with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x1 (j + (p : ℕ) * h) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₁ (m + (((p : ℕ) * h : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₁ (-ξ) *
        expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ)) with hW
    -- collapse and split (the SQUARED major arm)
    have hWT : (H : ℂ) * T = W := T_collapse_h h Φ₁ Φ₁
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * S :=
      fourier_split_sq_h h Φ₁ h1 hrefl hC₀ hlog hcard
    -- cast L and periodization (the diagonal instance of `periodization_total`)
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x1 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x1 (j + (p : ℕ) * h) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x1 (m + (((p : ℕ) * h : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total_h h hx1 hx1
    -- assemble
    have hLT : |L| ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by
      have hna := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at hna
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := hna
        _ ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
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
    have hA_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hB_nn : 0 ≤ S / ((H : ℝ) * Real.log (H : ℝ)) :=
      div_nonneg hS_nn (by positivity)
    have hc1 : 0 ≤ (h : ℝ) - 1 + (h : ℝ) * C₀ := by nlinarith [mul_pos hhR hC₀]
    have hc2 : 0 ≤ (h : ℝ) + 2 * C₀ * ((h : ℝ) - 1) := by
      nlinarith [mul_nonneg hC₀.le (by linarith : (0 : ℝ) ≤ (h : ℝ) - 1)]
    have hrem_nn : 0 ≤ ((h : ℝ) - 1 + (h : ℝ) * C₀)
          * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1)) * (S / ((H : ℝ) * Real.log (H : ℝ))) :=
      add_nonneg (mul_nonneg hc1 hA_nn) (mul_nonneg hc2 hB_nn)
    have heq : (h : ℝ) * (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S)
          + (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
          + (((h : ℝ) - 1 + (h : ℝ) * C₀)
                * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + ((h : ℝ) + 2 * C₀ * ((h : ℝ) - 1))
                  * (S / ((H : ℝ) * Real.log (H : ℝ)))) := by
      field_simp
      ring
    have hhcard : (h : ℝ) * ((primeWindow eps H).card : ℝ)
        ≤ (h : ℝ) * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard hhR.le
    calc |L| ≤ ‖T‖ + (h : ℝ) * ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (h : ℝ) * (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S) := by
          rw [heq]; linarith [hTle, hhcard, hrem_nn]
  · -- degenerate: H = 1
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hp2 := (prime_of_mem_primeWindow p.2).two_le
      have hph : 0 < (p : ℕ) * h := Nat.mul_pos (prime_of_mem_primeWindow p.2).pos hh
      have hge : ¬ (j + (p : ℕ) * h < H) := by omega
      have hz : windowVal H x1 (j + (p : ℕ) * h) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

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
