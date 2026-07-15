/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The Chen switch-constant certificate (blueprint `chen`, node C4a)

`docs/blueprints/chen.md`, catch #20. The cost of Chen's switching step in the
assembly is governed by the Bordignon–Johnston–Starichkova (BJS) Lemma-52 constant

  `c̄ = ∫_{1/8}^{1/3} log(2 − 3t) / (t (1 − t)) dt = 0.363083729248…`.

The assembly margin that survives the switch is
`M = log 3 − ½·log 6 − ½·c̄ ≈ 0.0212 > 0`, equivalently (at the carrier
normalisation `Π₂ x / (4 log z)`)

  `2·log 3 − log 6 − c̄ > 0`.

## What node C5 actually consumes

C5 needs ONLY the rational budget line
`two_log_three_sub_log_six_sub_cbar_pos : 0 < 2·log 3 − log 6 − 0.363084`,
which is pure log arithmetic:
`2·log 3 − log 6 = log 3 − log 2 = log(3/2) = log(1 + 1/2) ≥ 2·(1/2)/((1/2)+2) = 2/5`
(via `Real.le_log_one_add_of_nonneg`), and `2/5 = 0.4 > 0.363084`.
This DECOUPLES C5 from the integral: the switch constant enters downstream only
through the literal `0.363084`, and the margin `0.4 − 0.363084 = 0.036916` is
comfortable.  `cbar_pos` is the downstream well-definedness sanity check.

## Status of the honest integral bound `c̄ < 0.363084`  (FLOORED — deferred)

Not proved here. The certificate gap `0.363084 − c̄ ≈ 2.7·10⁻⁷` is intrinsically
tight: any *certified* elementary majorant `h ≥ g` must satisfy `∫h < 0.363084`,
i.e. `∫(h − g) < 2.7·10⁻⁷`, so `h` must hug the integrand to ~6 digits in an
integrated sense.

* A piecewise tangent-line (linear) majorant of the concave factor `log(2 − 3t)`
  has per-panel error `O(h³)`, forcing `≳ 220` panels; a quadratic majorant does
  NOT help because `log` is concave (its tangent line is already the tightest
  simple upper bound, and any quadratic upper bound lies *above* the tangent).
  Worse, each panel's closed-form integral contributes a `log(rational)`
  transcendental constant, and there is no `norm_num` extension for `Real.log`, so
  bounding a ~220-term sum of `log`-constants numerically is not mechanisable.
* The honest route is the exact dilogarithm antiderivative
  `c̄ = [log2·log t − Li₂(3t/2) − log3·log(1−t) − ½·log²(1−t) − Li₂(1/(3(1−t)))]`
  between the endpoints (verified numerically to 12 digits, three ways, at the
  gate), whose evaluation reduces to `Li₂(1/2) = π²/12 − (log 2)²/2` plus the two
  "hard" values `Li₂(3/16)`, `Li₂(8/21)` bounded by their geometric series. But
  mathlib has NO `Li₂`/polylog and no derivative API for it, so this is a
  from-scratch special-function development (a standalone C+ artifact), out of
  scope for this node's tier/budget.

The two theorems below are sorry-free and unblock the rung (C5 needs only the
budget line); `cbar_lt` is left for a dedicated dilog session.
-/

namespace Salt.Chen

open MeasureTheory intervalIntegral Set

/-- The Chen switch constant `c̄` (BJS Lemma 52).  True value `0.363083729248…`. -/
noncomputable def cbar : ℝ :=
  ∫ t in (1/8 : ℝ)..(1/3), Real.log (2 - 3*t) / (t * (1 - t))

/-- The integrand of `cbar` is continuous on `[1/8, 1/3]`: both `2 − 3t` and
`t(1 − t)` are bounded away from `0` there. -/
theorem cbar_integrand_continuousOn :
    ContinuousOn (fun t : ℝ => Real.log (2 - 3*t) / (t * (1 - t)))
      (Set.uIcc (1/8 : ℝ) (1/3)) := by
  have hab : (1 : ℝ)/8 ≤ 1/3 := by norm_num
  have hnum : ContinuousOn (fun t : ℝ => Real.log (2 - 3*t)) (Set.uIcc (1/8 : ℝ) (1/3)) := by
    have hin : ContinuousOn (fun t : ℝ => 2 - 3*t) (Set.uIcc (1/8 : ℝ) (1/3)) := by fun_prop
    apply hin.log
    intro t ht
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht
    exact (by linarith [ht.2] : (0 : ℝ) < 2 - 3*t).ne'
  have hden : ContinuousOn (fun t : ℝ => t * (1 - t)) (Set.uIcc (1/8 : ℝ) (1/3)) := by fun_prop
  have hden0 : ∀ t ∈ Set.uIcc (1/8 : ℝ) (1/3), t * (1 - t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht
    have h1 : (0 : ℝ) < t := by linarith [ht.1]
    have h2 : (0 : ℝ) < 1 - t := by linarith [ht.2]
    exact (by positivity : (0 : ℝ) < t * (1 - t)).ne'
  exact hnum.div hden hden0

/-- `0 < c̄`.  Downstream well-definedness sanity check: the integrand is positive
on the open interval `(1/8, 1/3)` (there `2 − 3t > 1` so `log(2 − 3t) > 0`, and
`t(1 − t) > 0`), and continuous on the closed interval, so the integral is
strictly positive. -/
theorem cbar_pos : 0 < cbar := by
  have hab : (1 : ℝ)/8 < 1/3 := by norm_num
  unfold cbar
  refine intervalIntegral_pos_of_pos_on
    cbar_integrand_continuousOn.intervalIntegrable (fun t ht => ?_) hab
  rw [Set.mem_Ioo] at ht
  apply div_pos
  · exact Real.log_pos (by linarith [ht.2])
  · have h1 : (0 : ℝ) < t := by linarith [ht.1]
    have h2 : (0 : ℝ) < 1 - t := by linarith [ht.2]
    positivity

/-- **The budget line consumed by C5.**  `0 < 2·log 3 − log 6 − 0.363084`.

Pure log arithmetic: `2·log 3 − log 6 = log(3/2) = log(1 + 1/2)`, and
`Real.le_log_one_add_of_nonneg` gives `log(1 + 1/2) ≥ 2·(1/2)/((1/2)+2) = 2/5 = 0.4`,
which clears `0.363084` with margin `0.036916`.  This is the ONLY switch-constant
fact downstream needs, so C5 never touches the integral `cbar`. -/
theorem two_log_three_sub_log_six_sub_cbar_pos :
    0 < 2 * Real.log 3 - Real.log 6 - 0.363084 := by
  have hval : Real.log (1 + 1/2) = 2 * Real.log 3 - Real.log 6 := by
    have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h6, show (1 : ℝ) + 1/2 = 3/2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    ring
  have hb : (2 : ℝ)/5 ≤ Real.log (1 + 1/2) := by
    have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num)
    have he : (2 : ℝ) * (1/2) / ((1/2) + 2) = 2/5 := by norm_num
    rwa [he] at h
  rw [hval] at hb
  linarith

end Salt.Chen
