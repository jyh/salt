/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Final

/-!
# M7 discharge — the analytic frontier, toward the capstone `EH (1/2) → bounded gaps`

This file discharges the `AnalyticFrontier` hypothesis of `bounded_gaps_from_eh`, toward
`bounded_gaps_from_eh_final` (`FrontierFinal.lean`, which keeps `hCompat`; `Complete` drops it).

The work is entirely quantifier-reordering plumbing plus regime-threshold real
analysis (no new mathematics).  The heart is making the three error constants
(`Cs` of `S1_upper_A1`, `C₀` of `S2m_ge_compatMain_eh`, and the compat constant
of `s2CompatFormM_ge_sixteenth`) *uniform in `R`*: their values factor through
`rankin_bound`/`phi_ratio_le`/`eh_error_pow`, all of which are `R`-free, so we
restate each producer with its constant quantified *before* `R`.  All five restatements
now sit beside their producers, each producer being its instance: `lam_abs_le_sharp_uniform`
(`LamBoundSharp`), `S1_trivial_error_le'_uniform` (`S1Bound`), `S1_upper_A1_uniform` (`Endgame`),
`abs_S2m_sub_compatMain_le_disc_R_uniform` and `S2m_ge_compatMain_eh_uniform` (`S2CompatEHFinal`).
-/

open Finset

namespace Salt.Maynard

set_option linter.unusedSectionVars false
variable [TupleChoice]

/-! ## Regime threshold real-analysis: polynomial beats polylog

The `herr1`/`herr2`/`hδlb` thresholds all reduce to "a fixed power of `1+log x`
is eventually dominated by a positive power of `x`". -/

open Filter Asymptotics in
omit [TupleChoice] in
/-- **Polynomial beats polylog.**  For any degree `n`, exponent `a > 0`, and
coefficient `K`, eventually `K·(1+log x)^n ≤ x^a`.  This is the analytic core of
the `herr` thresholds (`R²·(1+log R)^{4k+2} = o(N')` at `R = ⌊N'^{1/5}⌋`). -/
theorem eventually_poly_beats_polylog (n : ℕ) (a K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ n ≤ x ^ a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero, mul_one]
    filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop K] with x hx using hx
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set r := a / (2 * n) with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    have hlog := isLittleO_log_rpow_atTop hrpos
    have hev1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ r := by
      filter_upwards [hlog.eventuallyLE, (eventually_gt_atTop (0 : ℝ))] with x hx hx0
      calc Real.log x ≤ |Real.log x| := le_abs_self _
        _ ≤ |x ^ r| := hx
        _ = x ^ r := abs_of_nonneg (Real.rpow_nonneg hx0.le r)
    have hev2 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x ^ r :=
      (tendsto_rpow_atTop hrpos).eventually_ge_atTop 1
    have hev3 : ∀ᶠ x : ℝ in atTop, K * 2 ^ n ≤ x ^ (a / 2) :=
      (tendsto_rpow_atTop (by positivity : (0 : ℝ) < a / 2)).eventually_ge_atTop (K * 2 ^ n)
    filter_upwards [hev1, hev2, hev3, (eventually_ge_atTop (1 : ℝ))]
      with x hlx h1x h3x hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hbase_nn : 0 ≤ 1 + Real.log x := by linarith
    have hstep : 1 + Real.log x ≤ 2 * x ^ r := by linarith [hlx, h1x]
    -- `(x^r)^n = x^(a/2)` since `r·n = a/2`.
    have hpow : (x ^ r) ^ n = x ^ (a / 2) := by
      rw [← Real.rpow_natCast (x ^ r) n, ← Real.rpow_mul hx0.le]
      congr 1
      rw [hr]; field_simp
    have hxa2nn : (0 : ℝ) ≤ x ^ (a / 2) := Real.rpow_nonneg hx0.le _
    have hxann : (0 : ℝ) ≤ x ^ a := Real.rpow_nonneg hx0.le _
    by_cases hK : 0 ≤ K
    · calc K * (1 + Real.log x) ^ n
          ≤ K * (2 * x ^ r) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hstep n) hK
        _ = K * 2 ^ n * x ^ (a / 2) := by rw [mul_pow, hpow]; ring
        _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right h3x hxa2nn
        _ = x ^ a := by rw [← Real.rpow_add hx0]; congr 1; ring
    · have hle0 : K * (1 + Real.log x) ^ n ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hK)) (pow_nonneg hbase_nn n)
      linarith [hxann]

end Salt.Maynard
