/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The closed/half-open carrier glue, lifted to L² (node D7)

MRT Theorem A.1's carrier `mrtShortMean` averages over the **CLOSED** window
`x ≤ n ≤ x + h` (`Salt/MR/MRTThmA1.lean`).  The door's carrier reads the
**HALF-OPEN** window `x < n ≤ x + h`.  `shortWindow_closed_sub_open_norm_le`
(`Salt/MR/MRTPropA3.lean`) already prices the difference of the two SUMS at
**one term**, for 1-bounded data; dividing by `h` prices the difference of the
two MEANS at `1/h`.

This file lifts that L¹ endpoint price to L², which is the shape A.1's
left-hand side actually presents.  The whole arithmetic is `(a + b)² ≤ 2a² + 2b²`
over a landed pointwise bound: **nothing new is estimated here.**

⚠️ This closes a named convention residual and nothing more.  It does NOT
compose to the door: the door datum is phased and `MRTThmA1` still has no
producer.
-/
import Mathlib
import Salt.MR.MRTThmA1
import Salt.MR.MRTPropA3

namespace Salt.MR

open scoped BigOperators

/-- `‖a‖² ≤ 2‖b‖² + 2/c²` from a pointwise price `‖a - b‖ ≤ 1/c`.  Stated with
the `1/c` / `2/c²` shape so it unifies directly against the D7 goal. -/
theorem norm_sq_le_two_of_norm_sub_le {a b : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ‖a - b‖ ≤ 1 / c) : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 / c ^ 2 := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcinv : (0 : ℝ) < 1 / c := by positivity
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa using norm_add_le (a - b) b
  have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
  have hkey : ‖a‖ ≤ ‖b‖ + 1 / c := by linarith
  have hsq1 : ‖a‖ ^ 2 ≤ (‖b‖ + 1 / c) ^ 2 := by
    nlinarith [hkey, ha, hb, hcinv.le]
  have hsq2 : (‖b‖ + 1 / c) ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * (1 / c) ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - 1 / c)]
  have hrw : 2 * (1 / c) ^ 2 = 2 / c ^ 2 := by
    field_simp
  linarith [hsq1, hsq2, hrw.le, hrw.ge]

/-- **D7 — A.1's CLOSED-window carrier, bounded by twice the HALF-OPEN filtered
sum plus `2/H²`.**  The endpoint difference is the landed
`shortWindow_closed_sub_open_norm_le` (one term in the sum, `1/H` in the mean);
the lift to L² is `(a + b)² ≤ 2a² + 2b²`. -/
theorem norm_mrtShortMean_sq_le_open {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {y H : ℝ} (hH : 0 < H) :
    ‖mrtShortMean f H y‖ ^ 2
      ≤ 2 * ‖((1 / H : ℝ) : ℂ)
            * ∑ n ∈ (Finset.Icc ⌈y⌉₊ ⌊y + H⌋₊).filter (fun n : ℕ => y < (n : ℝ)), f n‖ ^ 2
        + 2 / H ^ 2
        := by
  refine norm_sq_le_two_of_norm_sub_le hH ?_
  have hcpos : (0 : ℝ) < 1 / H := by positivity
  have hnc : ‖((1 / H : ℝ) : ℂ)‖ = 1 / H := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  have hexp : mrtShortMean f H y
      = ((1 / H : ℝ) : ℂ) * ∑ n ∈ Finset.Icc ⌈y⌉₊ ⌊y + H⌋₊, f n := by
    unfold mrtShortMean
    push_cast
    ring
  have h1 := shortWindow_closed_sub_open_norm_le hf y H
  rw [hexp, ← mul_sub, norm_mul, hnc]
  have h2 := mul_le_mul_of_nonneg_left h1 hcpos.le
  linarith

end Salt.MR
