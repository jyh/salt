/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.MassCert
import Salt.Chen.MassCert2

/-!
# TK1 — the high-order log-majorant toolkit + near-exact certified constants

Design: `docs/blueprints/flags.md` `2026-07-13 THE MR2c GATE` (catches #38/#39: the numeric
keystone re-architected; TK1 = the log-majorant toolkit needed by EVERY route).  Also `MR2`
(catch #36), `MR2b` (catch #37).

## Part 1 — the reusable toolkit

* **Rational log-point sandwiches** (`log_le_of_taylor`, `le_log_of_taylor`): for `q>0` and a
  rational candidate `r`, `Real.log q ≤ r` reduces to `q ≤ ∑_{i<n} rⁱ/i!` (`exp`'s Taylor lower
  bound `sum_le_exp_of_nonneg`), and `r ≤ Real.log q` reduces to
  `∑_{i<n} rⁱ/i! + rⁿ(n+1)/(n!·n) ≤ q` (`Real.exp_bound'`, valid for `0 ≤ r ≤ 1`).  Both are pure
  rational `norm_num` checks; `n = 10` Taylor terms give ≲1e-8 per point on `[1,2]`.  Points with
  `log > 1` (e.g. `log 3`) are split as `log 2 + log(3/2)` (both `< 1`).
* **Panel log envelopes** (`log_half_le_tangent`, `log_half_ge_chord`): on a panel `[p,q] ⊂ (1,∞)`,
  `log(s/2) ≤` the tangent line at the midpoint (concavity, via `log_le_sub_one`) and `≥` the chord
  (concavity, via `strictConcaveOn_log_Ioi`), both with rational log values at the knots.
* **The rational panel quadrature** (`integral_quad`, `panel_le`, `panel_ge`): `∫ (A+Bs+Cs²) =`
  exact rational; with a per-panel linear×linear (log-envelope × rational-weight-envelope) product,
  every panel integral is bounded by an EXACT rational — no logs in the answer, all `norm_num`.

## Part 2 — the certified constants (targets from the MR2c gate crossover table)

* `cflatI_tight : cflatI ≤ 3560/10000` and `cflatI_lower : 3540/10000 ≤ cflatI` (true `0.355408`).
* `massE_two_tight : massE 2 ≤ 2950/10000` and `massE_two_lower : 2900/10000 ≤ massE 2`
  (true `0.293636`).
* `Cphi2_tight : Cphi2 ≤ 1450/10000` (true `0.14127`) — LANDED.  `Cphi1 ≤ 460/10000` (true
  `0.04403`) is NOT landed here (flag `2026-07-13 TK1`): it needs a 4-panel secant upper bound of
  the `log(3/(v−1))` weight (single-panel/crude weight bounds give `> 0.046`); the machinery
  (`Phi_le_quad` + the `log_half_ge_chord` chord via `s = 2v−2`) is in place and the scheme
  certifies `≤ 0.04497 ≤ 0.046`, left as a follow-up.

## Numeric plan (exact rational panels, cross-checked against mpmath dps=50)

Panel-integrate directly on `[2,4]` (`N = 16` uniform panels, `h = 1/8`).  Per panel `[p,q]`,
midpoint `c`: `log(s/2) ≤ Lc + (s−c)/c` (tangent, `Lc ≥ log(c/2)` rational), `log(s/2) ≥
chord(lp,lq)` (`lp ≤ log(p/2)`, `lq ≤ log(q/2)` rational); the weight (`1/(s−1)` for `cflatI`,
`(4−s)/(s−1)` for `massE 2`) is bounded above by its secant and below by its midpoint tangent.
Both product envelopes are quadratics, integrated exactly.

```
constant     true        target(up)   certified(up)   target(lo)  certified(lo)   panels
cflatI       0.3554084   ≤ 0.3560     0.3557504       ≥ 0.3540    0.3550863       16
massE 2      0.2936364   ≤ 0.2950     0.2944997       ≥ 0.2900    0.2929957       16
Cphi2        0.1412700   ≤ 0.1450     0.1419371       —           —               16 (w-panels)
Cphi1        0.0440300   ≤ 0.0460     0.0449650*      —           —               16 + 4 (flagged)
```
Two independent methods agree to ≥ 6 digits (Fraction exact rational panels vs mpmath quad).
Log-point Taylor route validated at `n=10`: `log 2 ∈ [0.6931471, 0.6931472]` (true `0.6931472`).
-/

open intervalIntegral MeasureTheory Set

-- The certified constants below carry long exact-rational literals (quadrature coefficients);
-- the style long-line linter is disabled for this numeric file only.
set_option linter.style.longLine false

namespace Salt.Chen

/-! ## Part 1a — rational log-point sandwiches (via `Real.exp` Taylor bounds) -/

/-- **Rational log upper bound.**  If `0 < q` and `q ≤ ∑_{i<n} rⁱ/i!` with `0 ≤ r`, then
`log q ≤ r`.  (The partial sum lies below `exp r` by `Real.sum_le_exp_of_nonneg`.) -/
theorem log_le_of_taylor {q r : ℝ} (hq : 0 < q) (n : ℕ) (hr : 0 ≤ r)
    (h : q ≤ ∑ i ∈ Finset.range n, r ^ i / (i.factorial : ℝ)) : Real.log q ≤ r := by
  have hexp : (∑ i ∈ Finset.range n, r ^ i / (i.factorial : ℝ)) ≤ Real.exp r :=
    Real.sum_le_exp_of_nonneg hr n
  have hqe : q ≤ Real.exp r := le_trans h hexp
  calc Real.log q ≤ Real.log (Real.exp r) := Real.log_le_log hq hqe
    _ = r := Real.log_exp r

/-- **Rational log lower bound.**  If `0 < q`, `0 ≤ r ≤ 1` and
`∑_{i<n} rⁱ/i! + rⁿ(n+1)/(n!·n) ≤ q`, then `r ≤ log q`.  (`Real.exp_bound'` bounds `exp r` above
by that rational.) -/
theorem le_log_of_taylor {q r : ℝ} {n : ℕ} (hn : 0 < n) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h : (∑ i ∈ Finset.range n, r ^ i / (i.factorial : ℝ))
        + r ^ n * (n + 1) / ((n.factorial : ℝ) * n) ≤ q) : r ≤ Real.log q := by
  have hexp : Real.exp r ≤ (∑ i ∈ Finset.range n, r ^ i / (i.factorial : ℝ))
      + r ^ n * (n + 1) / ((n.factorial : ℝ) * n) := Real.exp_bound' hr0 hr1 hn
  have hqe : Real.exp r ≤ q := le_trans hexp h
  calc r = Real.log (Real.exp r) := (Real.log_exp r).symm
    _ ≤ Real.log q := Real.log_le_log (Real.exp_pos r) hqe

/-! ## Part 1b — panel log envelopes (tangent above, chord below; concavity) -/

/-- **Tangent (upper) log envelope.**  For `0 < c`, `0 < s`, and a rational `Lc ≥ log(c/2)`,
`log(s/2) ≤ Lc + (s−c)/c` (the tangent to the concave `log(·/2)` at `c`). -/
theorem log_half_le_tangent {c s Lc : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hLc : Real.log (c / 2) ≤ Lc) : Real.log (s / 2) ≤ Lc + (s - c) / c := by
  have hsc : (0 : ℝ) < s / c := div_pos hs hc
  have h1 : Real.log (s / c) ≤ s / c - 1 := Real.log_le_sub_one_of_pos hsc
  have h2 : Real.log (s / 2) - Real.log (c / 2) = Real.log (s / c) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have h3 : s / c - 1 = (s - c) / c := by field_simp
  linarith [h1, h2, hLc, h3]

/-- **Chord (lower) log envelope.**  For `0 < p < q`, `s ∈ [p,q]`, and rationals `lp ≤ log(p/2)`,
`lq ≤ log(q/2)`, the chord through `(p,lp),(q,lq)` lies below `log(s/2)` (concavity). -/
theorem log_half_ge_chord {p q s lp lq : ℝ} (hp : 0 < p) (hpq : p < q)
    (hs1 : p ≤ s) (hs2 : s ≤ q) (hlp : lp ≤ Real.log (p / 2)) (hlq : lq ≤ Real.log (q / 2)) :
    lp * ((q - s) / (q - p)) + lq * ((s - p) / (q - p)) ≤ Real.log (s / 2) := by
  have hqp : 0 < q - p := by linarith
  have hqpne : q - p ≠ 0 := hqp.ne'
  set a := (q - s) / (q - p) with ha_def
  set b := (s - p) / (q - p) with hb_def
  have ha : 0 ≤ a := div_nonneg (by linarith) hqp.le
  have hb : 0 ≤ b := div_nonneg (by linarith) hqp.le
  have hab : a + b = 1 := by rw [ha_def, hb_def]; field_simp; ring
  have hmemp : (p / 2) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hmemq : (q / 2) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 hmemp hmemq ha hb hab
  simp only [smul_eq_mul] at hconc
  have hcomb : a * (p / 2) + b * (q / 2) = s / 2 := by rw [ha_def, hb_def]; field_simp; ring
  rw [hcomb] at hconc
  have hstep : lp * a + lq * b ≤ a * Real.log (p / 2) + b * Real.log (q / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hlp ha, mul_le_mul_of_nonneg_right hlq hb]
  calc lp * ((q - s) / (q - p)) + lq * ((s - p) / (q - p)) = lp * a + lq * b := by
        rw [ha_def, hb_def]
    _ ≤ a * Real.log (p / 2) + b * Real.log (q / 2) := hstep
    _ ≤ Real.log (s / 2) := hconc

/-! ## Part 1c — the rational panel quadrature -/

/-- Interval-integrability of the panel quadratic (continuity). -/
theorem quad_ii (A B C p q : ℝ) :
    IntervalIntegrable (fun s : ℝ => A + B * s + C * s ^ 2) volume p q := by
  apply Continuous.intervalIntegrable; fun_prop

/-- `∫_p^q (A + B·s + C·s²) ds = A(q−p) + B(q²−p²)/2 + C(q³−p³)/3` (exact rational). -/
theorem integral_quad (A B C p q : ℝ) :
    (∫ s in p..q, (A + B * s + C * s ^ 2))
      = A * (q - p) + B * (q ^ 2 - p ^ 2) / 2 + C * (q ^ 3 - p ^ 3) / 3 := by
  have iAB : IntervalIntegrable (fun s : ℝ => A + B * s) volume p q := by
    apply Continuous.intervalIntegrable; fun_prop
  have iC : IntervalIntegrable (fun s : ℝ => C * s ^ 2) volume p q := by
    apply Continuous.intervalIntegrable; fun_prop
  have iA : IntervalIntegrable (fun _ : ℝ => A) volume p q := _root_.intervalIntegrable_const
  have iB : IntervalIntegrable (fun s : ℝ => B * s) volume p q := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add iAB iC, intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, _root_.integral_id, _root_.integral_pow]
  push_cast
  ring

/-- **Panel upper bound.**  If `f ≤ A+B·s+C·s²` pointwise on `[p,q]` and the quadratic integral
equals `val`, then `∫_p^q f ≤ val`. -/
theorem panel_le (f : ℝ → ℝ) {p q A B C val : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q)
    (hpt : ∀ s ∈ Set.Icc p q, f s ≤ A + B * s + C * s ^ 2)
    (hval : A * (q - p) + B * (q ^ 2 - p ^ 2) / 2 + C * (q ^ 3 - p ^ 3) / 3 = val) :
    (∫ s in p..q, f s) ≤ val := by
  have hbound : (∫ s in p..q, f s) ≤ ∫ s in p..q, (A + B * s + C * s ^ 2) :=
    intervalIntegral.integral_mono_on hpq hf (quad_ii A B C p q) hpt
  rw [integral_quad] at hbound
  linarith [hbound]

/-- **Panel lower bound.**  If `A+B·s+C·s² ≤ f` pointwise on `[p,q]` and the quadratic integral
equals `val`, then `val ≤ ∫_p^q f`. -/
theorem panel_ge (f : ℝ → ℝ) {p q A B C val : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q)
    (hpt : ∀ s ∈ Set.Icc p q, A + B * s + C * s ^ 2 ≤ f s)
    (hval : A * (q - p) + B * (q ^ 2 - p ^ 2) / 2 + C * (q ^ 3 - p ^ 3) / 3 = val) :
    val ≤ ∫ s in p..q, f s := by
  have hbound : (∫ s in p..q, (A + B * s + C * s ^ 2)) ≤ ∫ s in p..q, f s :=
    intervalIntegral.integral_mono_on hpq (quad_ii A B C p q) hf hpt
  rw [integral_quad] at hbound
  linarith [hbound]

/-! ## Part 1d — concrete certified log-value sandwiches (`n = 10` Taylor terms) -/

/-- `log 2 ≤ 6931472/10000000`. -/
theorem log_two_le : Real.log 2 ≤ 6931472 / 10000000 :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `6931471/10000000 ≤ log 2`. -/
theorem le_log_two : (6931471 : ℝ) / 10000000 ≤ Real.log 2 :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log (3/2) ≤ 4054652/10000000`. -/
theorem log_threehalf_le : Real.log (3 / 2) ≤ 4054652 / 10000000 :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `4054651/10000000 ≤ log (3/2)`. -/
theorem le_log_threehalf : (4054651 : ℝ) / 10000000 ≤ Real.log (3 / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log 3 ≤ 10986124/10000000` (via `log 3 = log 2 + log(3/2)`). -/
theorem log_three_le : Real.log 3 ≤ 10986124 / 10000000 := by
  have h : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [h]; linarith [log_two_le, log_threehalf_le]

/-- `10986122/10000000 ≤ log 3`. -/
theorem le_log_three : (10986122 : ℝ) / 10000000 ≤ Real.log 3 := by
  have h : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [h]; linarith [le_log_two, le_log_threehalf]

/-! ## Part 2a — shared certified log-point sandwiches on the [2,4] partition

`N = 16` uniform panels; midpoints `c_i = (33+2i)/16`, knots `k_j = (16+j)/8`. -/

/-- `log(c_0/2) ≤ (307717/10000000)`, `c_0 = (33/16)`. -/
theorem logU_0 : Real.log ((33/16) / 2) ≤ (307717/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_1/2) ≤ (448061/5000000)`, `c_1 = (35/16)`. -/
theorem logU_1 : Real.log ((35/16) / 2) ≤ (448061/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_2/2) ≤ (1451821/10000000)`, `c_2 = (37/16)`. -/
theorem logU_2 : Real.log ((37/16) / 2) ≤ (1451821/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_3/2) ≤ (989129/5000000)`, `c_3 = (39/16)`. -/
theorem logU_3 : Real.log ((39/16) / 2) ≤ (989129/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_4/2) ≤ (1239181/5000000)`, `c_4 = (41/16)`. -/
theorem logU_4 : Real.log ((41/16) / 2) ≤ (1239181/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_5/2) ≤ (2954643/10000000)`, `c_5 = (43/16)`. -/
theorem logU_5 : Real.log ((43/16) / 2) ≤ (2954643/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_6/2) ≤ (1704633/5000000)`, `c_6 = (45/16)`. -/
theorem logU_6 : Real.log ((45/16) / 2) ≤ (1704633/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_7/2) ≤ (3844117/10000000)`, `c_7 = (47/16)`. -/
theorem logU_7 : Real.log ((47/16) / 2) ≤ (3844117/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_8/2) ≤ (1065211/2500000)`, `c_8 = (49/16)`. -/
theorem logU_8 : Real.log ((49/16) / 2) ≤ (1065211/2500000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_9/2) ≤ (2330449/5000000)`, `c_9 = (51/16)`. -/
theorem logU_9 : Real.log ((51/16) / 2) ≤ (2330449/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_10/2) ≤ (5045561/10000000)`, `c_10 = (53/16)`. -/
theorem logU_10 : Real.log ((53/16) / 2) ≤ (5045561/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_11/2) ≤ (5415973/10000000)`, `c_11 = (55/16)`. -/
theorem logU_11 : Real.log ((55/16) / 2) ≤ (5415973/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_12/2) ≤ (2886577/5000000)`, `c_12 = (57/16)`. -/
theorem logU_12 : Real.log ((57/16) / 2) ≤ (2886577/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_13/2) ≤ (47797/78125)`, `c_13 = (59/16)`. -/
theorem logU_13 : Real.log ((59/16) / 2) ≤ (47797/78125) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_14/2) ≤ (322569/500000)`, `c_14 = (61/16)`. -/
theorem logU_14 : Real.log ((61/16) / 2) ≤ (322569/500000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log(c_15/2) ≤ (6773989/10000000)`, `c_15 = (63/16)`. -/
theorem logU_15 : Real.log ((63/16) / 2) ≤ (6773989/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `0 ≤ log(k_0/2)`, `k_0 = (2)`. -/
theorem logL_0 : ((0) : ℝ) ≤ Real.log ((2) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(303123/5000000) ≤ log(k_1/2)`, `k_1 = (17/8)`. -/
theorem logL_1 : ((303123/5000000) : ℝ) ≤ Real.log ((17/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(117783/1000000) ≤ log(k_2/2)`, `k_2 = (9/4)`. -/
theorem logL_2 : ((117783/1000000) : ℝ) ≤ Real.log ((9/4) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(859251/5000000) ≤ log(k_3/2)`, `k_3 = (19/8)`. -/
theorem logL_3 : ((859251/5000000) : ℝ) ≤ Real.log ((19/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(446287/2000000) ≤ log(k_4/2)`, `k_4 = (5/2)`. -/
theorem logL_4 : ((446287/2000000) : ℝ) ≤ Real.log ((5/2) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(2719337/10000000) ≤ log(k_5/2)`, `k_5 = (21/8)`. -/
theorem logL_5 : ((2719337/10000000) : ℝ) ≤ Real.log ((21/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(3184537/10000000) ≤ log(k_6/2)`, `k_6 = (11/4)`. -/
theorem logL_6 : ((3184537/10000000) : ℝ) ≤ Real.log ((11/4) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(1814527/5000000) ≤ log(k_7/2)`, `k_7 = (23/8)`. -/
theorem logL_7 : ((1814527/5000000) : ℝ) ≤ Real.log ((23/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(4054651/10000000) ≤ log(k_8/2)`, `k_8 = (3)`. -/
theorem logL_8 : ((4054651/10000000) : ℝ) ≤ Real.log ((3) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(4462871/10000000) ≤ log(k_9/2)`, `k_9 = (25/8)`. -/
theorem logL_9 : ((4462871/10000000) : ℝ) ≤ Real.log ((25/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(2427539/5000000) ≤ log(k_10/2)`, `k_10 = (13/4)`. -/
theorem logL_10 : ((2427539/5000000) : ℝ) ≤ Real.log ((13/4) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(5232481/10000000) ≤ log(k_11/2)`, `k_11 = (27/8)`. -/
theorem logL_11 : ((5232481/10000000) : ℝ) ≤ Real.log ((27/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(5596157/10000000) ≤ log(k_12/2)`, `k_12 = (7/2)`. -/
theorem logL_12 : ((5596157/10000000) : ℝ) ≤ Real.log ((7/2) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(5947071/10000000) ≤ log(k_13/2)`, `k_13 = (29/8)`. -/
theorem logL_13 : ((5947071/10000000) : ℝ) ≤ Real.log ((29/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(3143043/5000000) ≤ log(k_14/2)`, `k_14 = (15/4)`. -/
theorem logL_14 : ((3143043/5000000) : ℝ) ≤ Real.log ((15/4) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(206687/312500) ≤ log(k_15/2)`, `k_15 = (31/8)`. -/
theorem logL_15 : ((206687/312500) : ℝ) ≤ Real.log ((31/8) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `(6931471/10000000) ≤ log(k_16/2)`, `k_16 = (4)`. -/
theorem logL_16 : ((6931471/10000000) : ℝ) ≤ Real.log ((4) / 2) :=
  le_log_of_taylor (n := 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-! ## Part 2b — the `cflatI` integrand and its interval-integrability -/

/-- `s ↦ log(s/2)/(s−1)` is interval-integrable on `[a,b]` for `1 < a ≤ b`. -/
theorem cflat_ii {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => Real.log (s / 2) / (s - 1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
  · intro s hs; rw [Set.uIcc_of_le hab] at hs
    have : a ≤ s := hs.1; exact (show (0:ℝ) < s / 2 by linarith).ne'
  · intro s hs; rw [Set.uIcc_of_le hab] at hs
    have : a ≤ s := hs.1; intro h; rw [sub_eq_zero] at h; linarith

/-! ## Part 2c — `cflatI` panel bounds (upper) -/

/-- Panel 0 upper: `∫_{(2)}^{(17/8)} log(s/2)/(s−1) ≤ (507887711/142560000000)`. -/
theorem cflatU_0 :
    (∫ s in ((2):ℝ)..(17/8), Real.log (s / 2) / (s - 1)) ≤ (507887711/142560000000) := by
  apply panel_le _ (A := (-3230761/1200000)) (B := (819845339/371250000)) (C := (-128/297))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (307717/10000000) + (s - (33/16)) / (33/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_0
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (307717/10000000) + (s - (33/16)) / (33/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (25/9) + (-8/9) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((307717/10000000) + (s - (33/16)) / (33/16)) * ((25/9) + (-8/9) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-3230761/1200000) + (819845339/371250000) * s + (-128/297) * s ^ 2 := by ring

/-- Panel 1 upper: `∫_{(17/8)}^{(9/4)} log(s/2)/(s−1) ≤ (177776339/18900000000)`. -/
theorem cflatU_1 :
    (∫ s in ((17/8):ℝ)..(9/4), Real.log (s / 2) / (s - 1)) ≤ (177776339/18900000000) := by
  apply panel_le _ (A := (-13655817/6250000)) (B := (9540397/5468750)) (C := (-512/1575))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (448061/5000000) + (s - (35/16)) / (35/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_1
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (448061/5000000) + (s - (35/16)) / (35/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (12/5) + (-32/45) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((448061/5000000) + (s - (35/16)) / (35/16)) * ((12/5) + (-32/45) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-13655817/6250000) + (9540397/5468750) * s + (-512/1575) * s ^ 2 := by ring

/-- Panel 2 upper: `∫_{(9/4)}^{(19/8)} log(s/2)/(s−1) ≤ (3374194751/244200000000)`. -/
theorem cflatU_2 :
    (∫ s in ((9/4):ℝ)..(19/8), Real.log (s / 2) / (s - 1)) ≤ (3374194751/244200000000) := by
  apply panel_le _ (A := (-247897191/137500000)) (B := (896282623/635937500)) (C := (-512/2035))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1451821/10000000) + (s - (37/16)) / (37/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_2
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (1451821/10000000) + (s - (37/16)) / (37/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (116/55) + (-32/55) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((1451821/10000000) + (s - (37/16)) / (37/16)) * ((116/55) + (-32/55) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-247897191/137500000) + (896282623/635937500) * s + (-512/2035) * s ^ 2 := by ring

/-- Panel 3 upper: `∫_{(19/8)}^{(5/2)} log(s/2)/(s−1) ≤ (2656746139/154440000000)`. -/
theorem cflatU_3 :
    (∫ s in ((19/8):ℝ)..(5/2), Real.log (s / 2) / (s - 1)) ≤ (2656746139/154440000000) := by
  apply panel_le _ (A := (-41445667/27500000)) (B := (42402179/36562500)) (C := (-256/1287))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (989129/5000000) + (s - (39/16)) / (39/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_3
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (989129/5000000) + (s - (39/16)) / (39/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (62/33) + (-16/33) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((989129/5000000) + (s - (39/16)) / (39/16)) * ((62/33) + (-16/33) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-41445667/27500000) + (42402179/36562500) * s + (-256/1287) * s ^ 2 := by ring

/-- Panel 4 upper: `∫_{(5/2)}^{(21/8)} log(s/2)/(s−1) ≤ (152219263/7675200000)`. -/
theorem cflatU_4 :
    (∫ s in ((5/2):ℝ)..(21/8), Real.log (s / 2) / (s - 1)) ≤ (152219263/7675200000) := by
  apply panel_le _ (A := (-41369009/32500000)) (B := (484193579/499687500)) (C := (-256/1599))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1239181/5000000) + (s - (41/16)) / (41/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_4
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (1239181/5000000) + (s - (41/16)) / (41/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (22/13) + (-16/39) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((1239181/5000000) + (s - (41/16)) / (41/16)) * ((22/13) + (-16/39) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-41369009/32500000) + (484193579/499687500) * s + (-256/1599) * s ^ 2 := by ring

/-- Panel 5 upper: `∫_{(21/8)}^{(11/4)} log(s/2)/(s−1) ≤ (112978259/5160000000)`. -/
theorem cflatU_5 :
    (∫ s in ((21/8):ℝ)..(11/4), Real.log (s / 2) / (s - 1)) ≤ (112978259/5160000000) := by
  apply panel_le _ (A := (-7045357/6500000)) (B := (77150027/94062500)) (C := (-512/3913))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2954643/10000000) + (s - (43/16)) / (43/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_5
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (2954643/10000000) + (s - (43/16)) / (43/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (20/13) + (-32/91) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((2954643/10000000) + (s - (43/16)) / (43/16)) * ((20/13) + (-32/91) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-7045357/6500000) + (77150027/94062500) * s + (-512/3913) * s ^ 2 := by ring

/-- Panel 6 upper: `∫_{(11/4)}^{(23/8)} log(s/2)/(s−1) ≤ (1333727639/56700000000)`. -/
theorem cflatU_6 :
    (∫ s in ((11/4):ℝ)..(23/8), Real.log (s / 2) / (s - 1)) ≤ (1333727639/56700000000) := by
  apply panel_le _ (A := (-121928579/131250000)) (B := (14808329/21093750)) (C := (-512/4725))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1704633/5000000) + (s - (45/16)) / (45/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_6
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (1704633/5000000) + (s - (45/16)) / (45/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (148/105) + (-32/105) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((1704633/5000000) + (s - (45/16)) / (45/16)) * ((148/105) + (-32/105) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-121928579/131250000) + (14808329/21093750) * s + (-512/4725) * s ^ 2 := by ring

/-- Panel 7 upper: `∫_{(23/8)}^{(3)} log(s/2)/(s−1) ≤ (16792635407/676800000000)`. -/
theorem cflatU_7 :
    (∫ s in ((23/8):ℝ)..(3), Real.log (s / 2) / (s - 1)) ≤ (16792635407/676800000000) := by
  apply panel_le _ (A := (-80026479/100000000)) (B := (356442167/587500000)) (C := (-64/705))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (3844117/10000000) + (s - (47/16)) / (47/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_7
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (3844117/10000000) + (s - (47/16)) / (47/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (13/10) + (-4/15) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((3844117/10000000) + (s - (47/16)) / (47/16)) * ((13/10) + (-4/15) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-80026479/100000000) + (356442167/587500000) * s + (-64/705) * s ^ 2 := by ring

/-- Panel 8 upper: `∫_{(3)}^{(25/8)} log(s/2)/(s−1) ≤ (303814033/11760000000)`. -/
theorem cflatU_8 :
    (∫ s in ((3):ℝ)..(25/8), Real.log (s / 2) / (s - 1)) ≤ (303814033/11760000000) := by
  apply panel_le _ (A := (-58826349/85000000)) (B := (275304661/520625000)) (C := (-64/833))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1065211/2500000) + (s - (49/16)) / (49/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_8
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (1065211/2500000) + (s - (49/16)) / (49/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (41/34) + (-4/17) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((1065211/2500000) + (s - (49/16)) / (49/16)) * ((41/34) + (-4/17) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-58826349/85000000) + (275304661/520625000) * s + (-64/833) * s ^ 2 := by ring

/-- Panel 9 upper: `∫_{(25/8)}^{(13/4)} log(s/2)/(s−1) ≤ (2494910879/93636000000)`. -/
theorem cflatU_9 :
    (∫ s in ((25/8):ℝ)..(13/4), Real.log (s / 2) / (s - 1)) ≤ (2494910879/93636000000) := by
  apply panel_le _ (A := (-114790693/191250000)) (B := (566147101/1219218750)) (C := (-512/7803))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2330449/5000000) + (s - (51/16)) / (51/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_9
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (2330449/5000000) + (s - (51/16)) / (51/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (172/153) + (-32/153) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((2330449/5000000) + (s - (51/16)) / (51/16)) * ((172/153) + (-32/153) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-114790693/191250000) + (566147101/1219218750) * s + (-512/7803) * s ^ 2 := by ring

/-- Panel 10 upper: `∫_{(13/4)}^{(27/8)} log(s/2)/(s−1) ≤ (29673035363/1087560000000)`. -/
theorem cflatU_10 :
    (∫ s in ((13/4):ℝ)..(27/8), Real.log (s / 2) / (s - 1)) ≤ (29673035363/1087560000000) := by
  apply panel_le _ (A := (-4954439/9500000)) (B := (1162585267/2832187500)) (C := (-512/9063))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (5045561/10000000) + (s - (53/16)) / (53/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_10
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (5045561/10000000) + (s - (53/16)) / (53/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (20/19) + (-32/171) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((5045561/10000000) + (s - (53/16)) / (53/16)) * ((20/19) + (-32/171) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-4954439/9500000) + (1162585267/2832187500) * s + (-512/9063) * s ^ 2 := by ring

/-- Panel 11 upper: `∫_{(27/8)}^{(7/2)} log(s/2)/(s−1) ≤ (6968357251/250800000000)`. -/
theorem cflatU_11 :
    (∫ s in ((27/8):ℝ)..(7/2), Real.log (s / 2) / (s - 1)) ≤ (6968357251/250800000000) := by
  apply panel_le _ (A := (-215449269/475000000)) (B := (238424297/653125000)) (C := (-256/5225))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (5415973/10000000) + (s - (55/16)) / (55/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_11
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (5415973/10000000) + (s - (55/16)) / (55/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (94/95) + (-16/95) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((5415973/10000000) + (s - (55/16)) / (55/16)) * ((94/95) + (-16/95) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-215449269/475000000) + (238424297/653125000) * s + (-256/5225) * s ^ 2 := by ring

/-- Panel 12 upper: `∫_{(7/2)}^{(29/8)} log(s/2)/(s−1) ≤ (20232791347/718200000000)`. -/
theorem cflatU_12 :
    (∫ s in ((7/2):ℝ)..(29/8), Real.log (s / 2) / (s - 1)) ≤ (20232791347/718200000000) := by
  apply panel_le _ (A := (-14793961/37500000)) (B := (610465111/1870312500)) (C := (-256/5985))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2886577/5000000) + (s - (57/16)) / (57/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_12
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (2886577/5000000) + (s - (57/16)) / (57/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (14/15) + (-16/105) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((2886577/5000000) + (s - (57/16)) / (57/16)) * ((14/15) + (-16/105) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-14793961/37500000) + (610465111/1870312500) * s + (-256/5985) * s ^ 2 := by ring

/-- Panel 13 upper: `∫_{(29/8)}^{(15/4)} log(s/2)/(s−1) ≤ (181852421/6388593750)`. -/
theorem cflatU_13 :
    (∫ s in ((29/8):ℝ)..(15/4), Real.log (s / 2) / (s - 1)) ≤ (181852421/6388593750) := by
  apply panel_le _ (A := (-2062304/6015625)) (B := (312259264/1064765625)) (C := (-512/13629))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (47797/78125) + (s - (59/16)) / (59/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_13
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (47797/78125) + (s - (59/16)) / (59/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (68/77) + (-32/231) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((47797/78125) + (s - (59/16)) / (59/16)) * ((68/77) + (-32/231) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-2062304/6015625) + (312259264/1064765625) * s + (-512/13629) * s ^ 2 := by ring

/-- Panel 14 upper: `∫_{(15/4)}^{(31/8)} log(s/2)/(s−1) ≤ (531171143/18519600000)`. -/
theorem cflatU_14 :
    (∫ s in ((15/4):ℝ)..(31/8), Real.log (s / 2) / (s - 1)) ≤ (531171143/18519600000) := by
  apply panel_le _ (A := (-9403843/31625000)) (B := (63823291/241140625)) (C := (-512/15433))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (322569/500000) + (s - (61/16)) / (61/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_14
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (322569/500000) + (s - (61/16)) / (61/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (212/253) + (-32/253) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((322569/500000) + (s - (61/16)) / (61/16)) * ((212/253) + (-32/253) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-9403843/31625000) + (63823291/241140625) * s + (-512/15433) * s ^ 2 := by ring

/-- Panel 15 upper: `∫_{(31/8)}^{(4)} log(s/2)/(s−1) ≤ (60163344287/2086560000000)`. -/
theorem cflatU_15 :
    (∫ s in ((31/8):ℝ)..(4), Real.log (s / 2) / (s - 1)) ≤ (60163344287/2086560000000) := by
  apply panel_le _ (A := (-11828707/46000000)) (B := (1303238693/5433750000)) (C := (-128/4347))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (6773989/10000000) + (s - (63/16)) / (63/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_15
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hTnn : 0 ≤ (6773989/10000000) + (s - (63/16)) / (63/16) := le_trans hlognn hlog
  have hWsec : 1 / (s - 1) ≤ (55/69) + (-8/69) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  calc Real.log (s / 2) / (s - 1) = Real.log (s / 2) * (1 / (s - 1)) := by rw [mul_one_div]
    _ ≤ ((6773989/10000000) + (s - (63/16)) / (63/16)) * ((55/69) + (-8/69) * s) :=
        mul_le_mul hlog hWsec (one_div_pos.mpr hsm1).le hTnn
    _ = (-11828707/46000000) + (1303238693/5433750000) * s + (-128/4347) * s ^ 2 := by ring

/-! ## Part 2d — `cflatI` panel bounds (lower) -/

/-- Panel 0 lower: `(101041/28900000) ≤ ∫_{(2)}^{(17/8)} log(s/2)/(s−1)`. -/
theorem cflatL_0 :
    ((101041/28900000):ℝ) ≤ ∫ s in ((2):ℝ)..(17/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-2424984/903125)) (B := (49712172/22578125)) (C := (-9699936/22578125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_0 logL_1
  have hMnn : 0 ≤ (0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (800/289) + (-256/289) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (33/16))]
  calc (-2424984/903125) + (49712172/22578125) * s + (-9699936/22578125) * s ^ 2
      = ((800/289) + (-256/289) * s) * ((0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 1 lower: `(8426729/902500000) ≤ ∫_{(17/8)}^{(9/4)} log(s/2)/(s−1)`. -/
theorem cflatL_1 :
    ((8426729/902500000):ℝ) ≤ ∫ s in ((17/8):ℝ)..(9/4), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-122994207/56406250)) (B := (1963476/1128125)) (C := (-9145344/28203125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_1 logL_2
  have hMnn : 0 ≤ (303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (864/361) + (-256/361) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (35/16))]
  calc (-122994207/56406250) + (1963476/1128125) * s + (-9145344/28203125) * s ^ 2
      = ((864/361) + (-256/361) * s) * ((303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 2 lower: `(15160687/1102500000) ≤ ∫_{(9/4)}^{(19/8)} log(s/2)/(s−1)`. -/
theorem cflatL_2 :
    ((15160687/1102500000):ℝ) ≤ ∫ s in ((9/4):ℝ)..(19/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-1968839/1093750)) (B := (16155836/11484375)) (C := (-2883584/11484375))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_2 logL_3
  have hMnn : 0 ≤ (117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (928/441) + (-256/441) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (37/16))]
  calc (-1968839/1093750) + (16155836/11484375) * s + (-2883584/11484375) * s ^ 2
      = ((928/441) + (-256/441) * s) * ((117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 3 lower: `(3400409/198375000) ≤ ∫_{(19/8)}^{(5/2)} log(s/2)/(s−1)`. -/
theorem cflatL_3 :
    ((3400409/198375000):ℝ) ≤ ∫ s in ((19/8):ℝ)..(5/2), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-9953759/6612500)) (B := (47856296/41328125)) (C := (-8206928/41328125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_3 logL_4
  have hMnn : 0 ≤ (859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (992/529) + (-256/529) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (39/16))]
  calc (-9953759/6612500) + (47856296/41328125) * s + (-8206928/41328125) * s ^ 2
      = ((992/529) + (-256/529) * s) * ((859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 4 lower: `(61803333/3125000000) ≤ ∫_{(5/2)}^{(21/8)} log(s/2)/(s−1)`. -/
theorem cflatL_4 :
    ((61803333/3125000000):ℝ) ≤ ∫ s in ((5/2):ℝ)..(21/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-49675593/39062500)) (B := (47254742/48828125)) (C := (-7806432/48828125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_4 logL_5
  have hMnn : 0 ≤ (446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1056/625) + (-256/625) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (41/16))]
  calc (-49675593/39062500) + (47254742/48828125) * s + (-7806432/48828125) * s ^ 2
      = ((1056/625) + (-256/625) * s) * ((446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 5 lower: `(238874297/10935000000) ≤ ∫_{(21/8)}^{(11/4)} log(s/2)/(s−1)`. -/
theorem cflatL_5 :
    ((238874297/10935000000):ℝ) ≤ ∫ s in ((21/8):ℝ)..(11/4), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-49349041/45562500)) (B := (46663726/56953125)) (C := (-297728/2278125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_5 logL_6
  have hMnn : 0 ≤ (2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1120/729) + (-256/729) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (43/16))]
  calc (-49349041/45562500) + (46663726/56953125) * s + (-297728/2278125) * s ^ 2
      = ((1120/729) + (-256/729) * s) * ((2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 6 lower: `(5923379/252300000) ≤ ∫_{(11/4)}^{(23/8)} log(s/2)/(s−1)`. -/
theorem cflatL_6 :
    ((5923379/252300000):ℝ) ≤ ∫ s in ((11/4):ℝ)..(23/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-244008969/262812500)) (B := (46083932/65703125)) (C := (-7112272/65703125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_6 logL_7
  have hMnn : 0 ≤ (3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1184/841) + (-256/841) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (45/16))]
  calc (-244008969/262812500) + (46083932/65703125) * s + (-7112272/65703125) * s ^ 2
      = ((1184/841) + (-256/841) * s) * ((3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 7 lower: `(89269871/3603750000) ≤ ∫_{(23/8)}^{(3)} log(s/2)/(s−1)`. -/
theorem cflatL_7 :
    ((89269871/3603750000):ℝ) ≤ ∫ s in ((23/8):ℝ)..(3), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-240227403/300312500)) (B := (9103184/15015625)) (C := (-6809552/75078125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_7 logL_8
  have hMnn : 0 ≤ (1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1248/961) + (-256/961) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (47/16))]
  calc (-240227403/300312500) + (9103184/15015625) * s + (-6809552/75078125) * s ^ 2
      = ((1248/961) + (-256/961) * s) * ((1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 8 lower: `(421413229/16335000000) ≤ ∫_{(3)}^{(25/8)} log(s/2)/(s−1)`. -/
theorem cflatL_8 :
    ((421413229/16335000000):ℝ) ≤ ∫ s in ((3):ℝ)..(25/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-235447789/340312500)) (B := (44959298/85078125)) (C := (-1306304/17015625))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_8 logL_9
  have hMnn : 0 ≤ (4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1312/1089) + (-256/1089) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (49/16))]
  calc (-235447789/340312500) + (44959298/85078125) * s + (-1306304/17015625) * s ^ 2
      = ((1312/1089) + (-256/1089) * s) * ((4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 9 lower: `(488996219/18375000000) ≤ ∫_{(25/8)}^{(13/4)} log(s/2)/(s−1)`. -/
theorem cflatL_9 :
    ((488996219/18375000000):ℝ) ≤ ∫ s in ((25/8):ℝ)..(13/4), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-57429768/95703125)) (B := (8882882/19140625)) (C := (-6275312/95703125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_9 logL_10
  have hMnn : 0 ≤ (4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1376/1225) + (-256/1225) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (51/16))]
  calc (-57429768/95703125) + (8882882/19140625) * s + (-6275312/95703125) * s ^ 2
      = ((1376/1225) + (-256/1225) * s) * ((4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 10 lower: `(186556941/6845000000) ≤ ∫_{(13/4)}^{(27/8)} log(s/2)/(s−1)`. -/
theorem cflatL_10 :
    ((186556941/6845000000):ℝ) ≤ ∫ s in ((13/4):ℝ)..(27/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-446166/855625)) (B := (8776214/21390625)) (C := (-6038448/106953125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_10 logL_11
  have hMnn : 0 ≤ (2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1440/1369) + (-256/1369) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (53/16))]
  calc (-446166/855625) + (8776214/21390625) * s + (-6038448/106953125) * s ^ 2
      = ((1440/1369) + (-256/1369) * s) * ((2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 11 lower: `(126658697/4563000000) ≤ ∫_{(27/8)}^{(7/2)} log(s/2)/(s−1)`. -/
theorem cflatL_11 :
    ((126658697/4563000000):ℝ) ≤ ∫ s in ((27/8):ℝ)..(7/2), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-215578237/475312500)) (B := (43359086/118828125)) (C := (-5818816/118828125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_11 logL_12
  have hMnn : 0 ≤ (5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1504/1521) + (-256/1521) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (55/16))]
  calc (-215578237/475312500) + (43359086/118828125) * s + (-5818816/118828125) * s ^ 2
      = ((1504/1521) + (-256/1521) * s) * ((5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 12 lower: `(141946613/5043000000) ≤ ∫_{(7/2)}^{(29/8)} log(s/2)/(s−1)`. -/
theorem cflatL_12 :
    ((141946613/5043000000):ℝ) ≤ ∫ s in ((7/2):ℝ)..(29/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-41448463/105062500)) (B := (42848442/131328125)) (C := (-5614624/131328125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_12 logL_13
  have hMnn : 0 ≤ (5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1568/1681) + (-256/1681) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (57/16))]
  calc (-41448463/105062500) + (42848442/131328125) * s + (-5614624/131328125) * s ^ 2
      = ((1568/1681) + (-256/1681) * s) * ((5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 13 lower: `(262956373/9245000000) ≤ ∫_{(29/8)}^{(15/4)} log(s/2)/(s−1)`. -/
theorem cflatL_13 :
    ((262956373/9245000000):ℝ) ≤ ∫ s in ((29/8):ℝ)..(15/4), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-49525641/144453125)) (B := (42348258/144453125)) (C := (-1084848/28890625))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_13 logL_14
  have hMnn : 0 ≤ (5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1632/1849) + (-256/1849) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (59/16))]
  calc (-49525641/144453125) + (42348258/144453125) * s + (-1084848/28890625) * s ^ 2
      = ((1632/1849) + (-256/1849) * s) * ((5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 14 lower: `(108823847/3796875000) ≤ ∫_{(15/4)}^{(31/8)} log(s/2)/(s−1)`. -/
theorem cflatL_14 :
    ((108823847/3796875000):ℝ) ≤ ∫ s in ((15/4):ℝ)..(31/8), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-31365877/105468750)) (B := (41858896/158203125)) (C := (-5246368/158203125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_14 logL_15
  have hMnn : 0 ≤ (3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1696/2025) + (-256/2025) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (61/16))]
  calc (-31365877/105468750) + (41858896/158203125) * s + (-5246368/158203125) * s ^ 2
      = ((1696/2025) + (-256/2025) * s) * ((3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- Panel 15 lower: `(159132639/5522500000) ≤ ∫_{(31/8)}^{(4)} log(s/2)/(s−1)`. -/
theorem cflatL_15 :
    ((159132639/5522500000):ℝ) ≤ ∫ s in ((31/8):ℝ)..(4), Real.log (s / 2) / (s - 1) := by
  apply panel_ge _ (A := (-35509243/138062500)) (B := (41379796/172578125)) (C := (-5079792/172578125))
    (by norm_num) (cflat_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_15 logL_16
  have hMnn : 0 ≤ (206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hWtan : (1760/2209) + (-256/2209) * s ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (63/16))]
  calc (-35509243/138062500) + (41379796/172578125) * s + (-5079792/172578125) * s ^ 2
      = ((1760/2209) + (-256/2209) * s) * ((206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8)))) := by ring
    _ ≤ (1 / (s - 1)) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn (one_div_pos.mpr hsm1).le
    _ = Real.log (s / 2) / (s - 1) := by rw [one_div_mul_eq_div]

/-- **Certified flat coefficient, tight upper bound.**  `cflatI ≤ 3560/10000` (true `0.3554`). -/
theorem cflatI_tight : cflatI ≤ 3560 / 10000 := by
  unfold cflatI
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (2)) (b := (17/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (17/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (17/8)) (b := (9/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (9/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (9/4)) (b := (19/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (19/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (19/8)) (b := (5/2)) (by norm_num) (by norm_num))
    (cflat_ii (a := (5/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (5/2)) (b := (21/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (21/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (21/8)) (b := (11/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (11/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (11/4)) (b := (23/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (23/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (23/8)) (b := (3)) (by norm_num) (by norm_num))
    (cflat_ii (a := (3)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (3)) (b := (25/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (25/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (25/8)) (b := (13/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (13/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (13/4)) (b := (27/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (27/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (27/8)) (b := (7/2)) (by norm_num) (by norm_num))
    (cflat_ii (a := (7/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (7/2)) (b := (29/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (29/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (29/8)) (b := (15/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (15/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (15/4)) (b := (31/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (31/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  linarith [cflatU_0, cflatU_1, cflatU_2, cflatU_3, cflatU_4, cflatU_5, cflatU_6, cflatU_7, cflatU_8, cflatU_9, cflatU_10, cflatU_11, cflatU_12, cflatU_13, cflatU_14, cflatU_15]

/-- **Certified flat coefficient, lower bound.**  `3540/10000 ≤ cflatI`. -/
theorem cflatI_lower : (3540 : ℝ) / 10000 ≤ cflatI := by
  unfold cflatI
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (2)) (b := (17/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (17/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (17/8)) (b := (9/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (9/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (9/4)) (b := (19/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (19/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (19/8)) (b := (5/2)) (by norm_num) (by norm_num))
    (cflat_ii (a := (5/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (5/2)) (b := (21/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (21/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (21/8)) (b := (11/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (11/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (11/4)) (b := (23/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (23/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (23/8)) (b := (3)) (by norm_num) (by norm_num))
    (cflat_ii (a := (3)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (3)) (b := (25/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (25/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (25/8)) (b := (13/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (13/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (13/4)) (b := (27/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (27/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (27/8)) (b := (7/2)) (by norm_num) (by norm_num))
    (cflat_ii (a := (7/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (7/2)) (b := (29/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (29/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (29/8)) (b := (15/4)) (by norm_num) (by norm_num))
    (cflat_ii (a := (15/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cflat_ii (a := (15/4)) (b := (31/8)) (by norm_num) (by norm_num))
    (cflat_ii (a := (31/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  linarith [cflatL_0, cflatL_1, cflatL_2, cflatL_3, cflatL_4, cflatL_5, cflatL_6, cflatL_7, cflatL_8, cflatL_9, cflatL_10, cflatL_11, cflatL_12, cflatL_13, cflatL_14, cflatL_15]

/-! ## Part 2e — the `massE 2` integrand: interval-integrability + the closed form -/

/-- `s ↦ (4−s)/(s−1)·log(s/2)` is interval-integrable on `[a,b]` for `1 < a ≤ b`. -/
theorem masse_ii {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => (4 - s) / (s - 1) * Real.log (s / 2)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    (ContinuousOn.log (by fun_prop) ?_)
  · intro s hs; rw [Set.uIcc_of_le hab] at hs
    have : a ≤ s := hs.1; intro h; rw [sub_eq_zero] at h; linarith
  · intro s hs; rw [Set.uIcc_of_le hab] at hs
    have : a ≤ s := hs.1; exact (show (0:ℝ) < s / 2 by linarith).ne'

/-- `massE 2 = ∫_2^4 (4−s)/(s−1)·log(s/2) ds` (the recursion with the explicit `f₁`
predecessor, `fseq 1 (s−1) = (4−s)/(s−1)` on the flat window). -/
theorem massE_two_integral :
    massE 2 = ∫ s in (2:ℝ)..4, (4 - s) / (s - 1) * Real.log (s / 2) := by
  have h := massE_recursion (m := 1) (by decide)
  norm_num at h
  rw [h]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by norm_num)] at hs
  have hs1 : (1:ℝ) ≤ s - 1 := by linarith [hs.1]
  have hs3 : s - 1 ≤ 3 := by linarith [hs.2]
  change fseq 1 (s - 1) * Real.log (s / 2) = (4 - s) / (s - 1) * Real.log (s / 2)
  rw [fseq_one_window hs1 hs3, show (3:ℝ) - (s - 1) = 4 - s by ring]

/-! ## Part 2f — `massE 2` panel bounds (upper) -/

/-- Panel 0 upper: `∫_{(2)}^{(17/8)} (4−s)/(s−1)·log(s/2) ≤ (325103813/47520000000)`. -/
theorem masseU_0 :
    (∫ s in ((2):ℝ)..(17/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (325103813/47520000000) := by
  apply panel_le _ (A := (-35538371/5000000)) (B := (69076849/11250000)) (C := (-128/99))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (307717/10000000) + (s - (33/16)) / (33/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_0
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (22/3) + (-8/3) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (22/3) + (-8/3) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((22/3) + (-8/3) * s) * ((307717/10000000) + (s - (33/16)) / (33/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-35538371/5000000) + (69076849/11250000) * s + (-128/99) * s ^ 2 := by ring

/-- Panel 1 upper: `∫_{(17/8)}^{(9/4)} (4−s)/(s−1)·log(s/2) ≤ (214413463/12600000000)`. -/
theorem masseU_1 :
    (∫ s in ((17/8):ℝ)..(9/4), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (214413463/12600000000) := by
  apply panel_le _ (A := (-141110109/25000000)) (B := (26121191/5468750)) (C := (-512/525))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (448061/5000000) + (s - (35/16)) / (35/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_1
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (31/5) + (-32/15) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (31/5) + (-32/15) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((31/5) + (-32/15) * s) * ((448061/5000000) + (s - (35/16)) / (35/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-141110109/25000000) + (26121191/5468750) * s + (-512/525) * s ^ 2 := by ring

/-- Panel 2 upper: `∫_{(9/4)}^{(19/8)} (4−s)/(s−1)·log(s/2) ≤ (3793933767/162800000000)`. -/
theorem masseU_2 :
    (∫ s in ((9/4):ℝ)..(19/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (3793933767/162800000000) := by
  apply panel_le _ (A := (-2504616447/550000000)) (B := (2413847869/635937500)) (C := (-1536/2035))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1451821/10000000) + (s - (37/16)) / (37/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_2
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (293/55) + (-96/55) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (293/55) + (-96/55) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((293/55) + (-96/55) * s) * ((1451821/10000000) + (s - (37/16)) / (37/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-2504616447/550000000) + (2413847869/635937500) * s + (-1536/2035) * s ^ 2 := by ring

/-- Panel 3 upper: `∫_{(19/8)}^{(5/2)} (4−s)/(s−1)·log(s/2) ≤ (345934279/12870000000)`. -/
theorem masseU_3 :
    (∫ s in ((19/8):ℝ)..(5/2), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (345934279/12870000000) := by
  apply panel_le _ (A := (-204554421/55000000)) (B := (12467393/4062500)) (C := (-256/429))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (989129/5000000) + (s - (39/16)) / (39/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_3
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (51/11) + (-16/11) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (51/11) + (-16/11) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((51/11) + (-16/11) * s) * ((989129/5000000) + (s - (39/16)) / (39/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-204554421/55000000) + (12467393/4062500) * s + (-256/429) * s ^ 2 := by ring

/-- Panel 4 upper: `∫_{(5/2)}^{(21/8)} (4−s)/(s−1)·log(s/2) ≤ (456007789/15990000000)`. -/
theorem masseU_4 :
    (∫ s in ((5/2):ℝ)..(21/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (456007789/15990000000) := by
  apply panel_le _ (A := (-199323407/65000000)) (B := (419193579/166562500)) (C := (-256/533))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1239181/5000000) + (s - (41/16)) / (41/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_4
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (53/13) + (-16/13) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (53/13) + (-16/13) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((53/13) + (-16/13) * s) * ((1239181/5000000) + (s - (41/16)) / (41/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-199323407/65000000) + (419193579/166562500) * s + (-256/533) * s ^ 2 := by ring

/-- Panel 5 upper: `∫_{(21/8)}^{(11/4)} (4−s)/(s−1)·log(s/2) ≤ (98906869/3440000000)`. -/
theorem masseU_5 :
    (∫ s in ((21/8):ℝ)..(11/4), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (98906869/3440000000) := by
  apply panel_le _ (A := (-331131779/130000000)) (B := (196450081/94062500)) (C := (-1536/3913))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2954643/10000000) + (s - (43/16)) / (43/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_5
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (47/13) + (-96/91) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (47/13) + (-96/91) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((47/13) + (-96/91) * s) * ((2954643/10000000) + (s - (43/16)) / (43/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-331131779/130000000) + (196450081/94062500) * s + (-1536/3913) * s ^ 2 := by ring

/-- Panel 6 upper: `∫_{(11/4)}^{(23/8)} (4−s)/(s−1)·log(s/2) ≤ (1056577093/37800000000)`. -/
theorem masseU_6 :
    (∫ s in ((11/4):ℝ)..(23/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (1056577093/37800000000) := by
  apply panel_le _ (A := (-372376471/175000000)) (B := (12308329/7031250)) (C := (-512/1575))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1704633/5000000) + (s - (45/16)) / (45/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_6
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (113/35) + (-32/35) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (113/35) + (-32/35) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((113/35) + (-32/35) * s) * ((1704633/5000000) + (s - (45/16)) / (45/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-372376471/175000000) + (12308329/7031250) * s + (-512/1575) * s ^ 2 := by ring

/-- Panel 7 upper: `∫_{(23/8)}^{(3)} (4−s)/(s−1)·log(s/2) ≤ (5952225467/225600000000)`. -/
theorem masseU_7 :
    (∫ s in ((23/8):ℝ)..(3), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (5952225467/225600000000) := by
  apply panel_le _ (A := (-178520607/100000000)) (B := (869326501/587500000)) (C := (-64/235))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (3844117/10000000) + (s - (47/16)) / (47/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_7
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (29/10) + (-4/5) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (29/10) + (-4/5) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((29/10) + (-4/5) * s) * ((3844117/10000000) + (s - (47/16)) / (47/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-178520607/100000000) + (869326501/587500000) * s + (-64/235) * s ^ 2 := by ring

/-- Panel 8 upper: `∫_{(3)}^{(25/8)} (4−s)/(s−1)·log(s/2) ≤ (95032677/3920000000)`. -/
theorem masseU_8 :
    (∫ s in ((3):ℝ)..(25/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (95032677/3920000000) := by
  apply panel_le _ (A := (-127696221/85000000)) (B := (655913983/520625000)) (C := (-192/833))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (1065211/2500000) + (s - (49/16)) / (49/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_8
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (89/34) + (-12/17) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (89/34) + (-12/17) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((89/34) + (-12/17) * s) * ((1065211/2500000) + (s - (49/16)) / (49/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-127696221/85000000) + (655913983/520625000) * s + (-192/833) * s ^ 2 := by ring

/-- Panel 9 upper: `∫_{(25/8)}^{(13/4)} (4−s)/(s−1)·log(s/2) ≤ (6764615243/312120000000)`. -/
theorem masseU_9 :
    (∫ s in ((25/8):ℝ)..(13/4), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (6764615243/312120000000) := by
  apply panel_le _ (A := (-323015671/255000000)) (B := (438647101/406406250)) (C := (-512/2601))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2330449/5000000) + (s - (51/16)) / (51/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_9
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (121/51) + (-32/51) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (121/51) + (-32/51) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((121/51) + (-32/51) * s) * ((2330449/5000000) + (s - (51/16)) / (51/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-323015671/255000000) + (438647101/406406250) * s + (-512/2601) * s ^ 2 := by ring

/-- Panel 10 upper: `∫_{(13/4)}^{(27/8)} (4−s)/(s−1)·log(s/2) ≤ (13618151383/725040000000)`. -/
theorem masseU_10 :
    (∫ s in ((13/4):ℝ)..(27/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (13618151383/725040000000) := by
  apply panel_le _ (A := (-203131999/190000000)) (B := (877585267/944062500)) (C := (-512/3021))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (5045561/10000000) + (s - (53/16)) / (53/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_10
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (41/19) + (-32/57) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (41/19) + (-32/57) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((41/19) + (-32/57) * s) * ((5045561/10000000) + (s - (53/16)) / (53/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-203131999/190000000) + (877585267/944062500) * s + (-512/3021) * s ^ 2 := by ring

/-- Panel 11 upper: `∫_{(27/8)}^{(7/2)} (4−s)/(s−1)·log(s/2) ≤ (654332733/41800000000)`. -/
theorem masseU_11 :
    (∫ s in ((27/8):ℝ)..(7/2), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (654332733/41800000000) := by
  apply panel_le _ (A := (-857213049/950000000)) (B := (47752081/59375000)) (C := (-768/5225))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (5415973/10000000) + (s - (55/16)) / (55/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_11
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (187/95) + (-48/95) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (187/95) + (-48/95) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((187/95) + (-48/95) * s) * ((5415973/10000000) + (s - (55/16)) / (55/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-857213049/950000000) + (47752081/59375000) * s + (-768/5225) * s ^ 2 := by ring

/-- Panel 12 upper: `∫_{(7/2)}^{(29/8)} (4−s)/(s−1)·log(s/2) ≤ (1478314001/119700000000)`. -/
theorem masseU_12 :
    (∫ s in ((7/2):ℝ)..(29/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (1478314001/119700000000) := by
  apply panel_le _ (A := (-19020807/25000000)) (B := (145155037/207812500)) (C := (-256/1995))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (2886577/5000000) + (s - (57/16)) / (57/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_12
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (9/5) + (-16/35) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (9/5) + (-16/35) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((9/5) + (-16/35) * s) * ((2886577/5000000) + (s - (57/16)) / (57/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-19020807/25000000) + (145155037/207812500) * s + (-256/1995) * s ^ 2 := by ring

/-- Panel 13 upper: `∫_{(29/8)}^{(15/4)} (4−s)/(s−1)·log(s/2) ≤ (75984371/8518125000)`. -/
theorem masseU_13 :
    (∫ s in ((29/8):ℝ)..(15/4), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (75984371/8518125000) := by
  apply panel_le _ (A := (-3851656/6015625)) (B := (216009264/354921875)) (C := (-512/4543))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (47797/78125) + (s - (59/16)) / (59/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_13
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (127/77) + (-32/77) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (127/77) + (-32/77) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((127/77) + (-32/77) * s) * ((47797/78125) + (s - (59/16)) / (59/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-3851656/6015625) + (216009264/354921875) * s + (-512/4543) * s ^ 2 := by ring

/-- Panel 14 upper: `∫_{(15/4)}^{(31/8)} (4−s)/(s−1)·log(s/2) ≤ (333504053/61732000000)`. -/
theorem masseU_14 :
    (∫ s in ((15/4):ℝ)..(31/8), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (333504053/61732000000) := by
  apply panel_le _ (A := (-67956073/126500000)) (B := (128219873/241140625)) (C := (-1536/15433))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (322569/500000) + (s - (61/16)) / (61/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_14
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (383/253) + (-96/253) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (383/253) + (-96/253) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((383/253) + (-96/253) * s) * ((322569/500000) + (s - (61/16)) / (61/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-67956073/126500000) + (128219873/241140625) * s + (-1536/15433) * s ^ 2 := by ring

/-- Panel 15 upper: `∫_{(31/8)}^{(4)} (4−s)/(s−1)·log(s/2) ≤ (1270283921/695520000000)`. -/
theorem masseU_15 :
    (∫ s in ((31/8):ℝ)..(4), (4 - s) / (s - 1) * Real.log (s / 2)) ≤ (1270283921/695520000000) := by
  apply panel_le _ (A := (-3226011/7187500)) (B := (843238693/1811250000)) (C := (-128/1449))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : Real.log (s / 2) ≤ (6773989/10000000) + (s - (63/16)) / (63/16) :=
    log_half_le_tangent (by norm_num) (by linarith) logU_15
  have hlognn : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWsec : (4 - s) / (s - 1) ≤ (32/23) + (-8/23) * s := by
    rw [div_le_iff₀ hsm1]
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) (sub_nonneg.2 hsq)]
  have hWnn : 0 ≤ (32/23) + (-8/23) * s := le_trans hW0 hWsec
  calc (4 - s) / (s - 1) * Real.log (s / 2)
      ≤ ((32/23) + (-8/23) * s) * ((6773989/10000000) + (s - (63/16)) / (63/16)) :=
        mul_le_mul hWsec hlog hlognn hWnn
    _ = (-3226011/7187500) + (843238693/1811250000) * s + (-128/1449) * s ^ 2 := by ring

/-! ## Part 2g — `massE 2` panel bounds (lower) -/

/-- Panel 0 lower: `(154895853/23120000000) ≤ ∫_{(2)}^{(17/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_0 :
    ((154895853/23120000000):ℝ) ≤ ∫ s in ((2):ℝ)..(17/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-639892653/90312500)) (B := (1105489581/180625000)) (C := (-29099808/22578125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_0 logL_1
  have hMnn : 0 ≤ (0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2111/289) + (-768/289) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (33/16))]
  calc (-639892653/90312500) + (1105489581/180625000) * s + (-29099808/22578125) * s ^ 2
      = ((2111/289) + (-768/289) * s) * ((0) * (((17/8) - s) / ((17/8) - (2))) + (303123/5000000) * ((s - (2)) / ((17/8) - (2)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 1 lower: `(243470133/14440000000) ≤ ∫_{(17/8)}^{(9/4)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_1 :
    ((243470133/14440000000):ℝ) ≤ ∫ s in ((17/8):ℝ)..(9/4), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-10162965771/1805000000)) (B := (134364336/28203125)) (C := (-27436032/28203125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_1 logL_2
  have hMnn : 0 ≤ (303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2231/361) + (-768/361) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (35/16))]
  calc (-10162965771/1805000000) + (134364336/28203125) * s + (-27436032/28203125) * s ^ 2
      = ((2231/361) + (-768/361) * s) * ((303123/5000000) * (((9/4) - s) / ((9/4) - (17/8))) + (117783/1000000) * ((s - (17/8)) / ((9/4) - (17/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 2 lower: `(136130791/5880000000) ≤ ∫_{(9/4)}^{(19/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_2 :
    ((136130791/5880000000):ℝ) ≤ ∫ s in ((9/4):ℝ)..(19/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-159068613/35000000)) (B := (14500028/3828125)) (C := (-2883584/3828125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_2 logL_3
  have hMnn : 0 ≤ (117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (781/147) + (-256/147) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (37/16))]
  calc (-159068613/35000000) + (14500028/3828125) * s + (-2883584/3828125) * s ^ 2
      = ((781/147) + (-256/147) * s) * ((117783/1000000) * (((19/8) - s) / ((19/8) - (9/4))) + (859251/5000000) * ((s - (9/4)) / ((19/8) - (9/4)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 3 lower: `(2263006847/84640000000) ≤ ∫_{(19/8)}^{(5/2)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_3 :
    ((2263006847/84640000000):ℝ) ≤ ∫ s in ((19/8):ℝ)..(5/2), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-785704783/211600000)) (B := (2025760651/661250000)) (C := (-24620784/41328125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_3 logL_4
  have hMnn : 0 ≤ (859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2447/529) + (-768/529) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (39/16))]
  calc (-785704783/211600000) + (2025760651/661250000) * s + (-24620784/41328125) * s ^ 2
      = ((2447/529) + (-768/529) * s) * ((859251/5000000) * (((5/2) - s) / ((5/2) - (19/8))) + (446287/2000000) * ((s - (19/8)) / ((5/2) - (19/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 4 lower: `(709721867/25000000000) ≤ ∫_{(5/2)}^{(21/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_4 :
    ((709721867/25000000000):ℝ) ≤ ∫ s in ((5/2):ℝ)..(21/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-3828031303/1250000000)) (B := (981644433/390625000)) (C := (-23419296/48828125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_4 logL_5
  have hMnn : 0 ≤ (446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2543/625) + (-768/625) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (41/16))]
  calc (-3828031303/1250000000) + (981644433/390625000) * s + (-23419296/48828125) * s ^ 2
      = ((2543/625) + (-768/625) * s) * ((446287/2000000) * (((21/8) - s) / ((21/8) - (5/2))) + (2719337/10000000) * ((s - (5/2)) / ((21/8) - (5/2)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 5 lower: `(1670026679/58320000000) ≤ ∫_{(21/8)}^{(11/4)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_5 :
    ((1670026679/58320000000):ℝ) ≤ ∫ s in ((21/8):ℝ)..(11/4), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-6182729851/2430000000)) (B := (39598501/18984375)) (C := (-297728/759375))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_5 logL_6
  have hMnn : 0 ≤ (2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (877/243) + (-256/243) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (43/16))]
  calc (-6182729851/2430000000) + (39598501/18984375) * s + (-297728/759375) * s ^ 2
      = ((877/243) + (-256/243) * s) * ((2719337/10000000) * (((11/4) - s) / ((11/4) - (21/8))) + (3184537/10000000) * ((s - (21/8)) / ((11/4) - (21/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 6 lower: `(3747176369/134560000000) ≤ ∫_{(11/4)}^{(23/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_6 :
    ((3747176369/134560000000):ℝ) ≤ ∫ s in ((11/4):ℝ)..(23/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-17878603107/8410000000)) (B := (1838189939/1051250000)) (C := (-21336816/65703125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_6 logL_7
  have hMnn : 0 ≤ (3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2711/841) + (-768/841) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (45/16))]
  calc (-17878603107/8410000000) + (1838189939/1051250000) * s + (-21336816/65703125) * s ^ 2
      = ((2711/841) + (-768/841) * s) * ((3184537/10000000) * (((23/8) - s) / ((23/8) - (11/4))) + (1814527/5000000) * ((s - (11/4)) / ((23/8) - (11/4)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 7 lower: `(4042502983/153760000000) ≤ ∫_{(23/8)}^{(3)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_7 :
    ((4042502983/153760000000):ℝ) ≤ ∫ s in ((23/8):ℝ)..(3), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-17142381091/9610000000)) (B := (1775765443/1201250000)) (C := (-20428656/75078125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_7 logL_8
  have hMnn : 0 ≤ (1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2783/961) + (-768/961) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (47/16))]
  calc (-17142381091/9610000000) + (1775765443/1201250000) * s + (-20428656/75078125) * s ^ 2
      = ((2783/961) + (-768/961) * s) * ((1814527/5000000) * (((3) - s) / ((3) - (23/8))) + (4054651/10000000) * ((s - (23/8)) / ((3) - (23/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 8 lower: `(420964187/17424000000) ≤ ∫_{(3)}^{(25/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_8 :
    ((420964187/17424000000):ℝ) ≤ ∫ s in ((3):ℝ)..(25/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-5449754921/3630000000)) (B := (142791227/113437500)) (C := (-1306304/5671875))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_8 logL_9
  have hMnn : 0 ≤ (4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (949/363) + (-256/363) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (49/16))]
  calc (-5449754921/3630000000) + (142791227/113437500) * s + (-1306304/5671875) * s ^ 2
      = ((949/363) + (-256/363) * s) * ((4054651/10000000) * (((25/8) - s) / ((25/8) - (3))) + (4462871/10000000) * ((s - (3)) / ((25/8) - (3)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 9 lower: `(4233391483/196000000000) ≤ ∫_{(25/8)}^{(13/4)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_9 :
    ((4233391483/196000000000):ℝ) ≤ ∫ s in ((25/8):ℝ)..(13/4), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-484647141/382812500)) (B := (330287621/306250000)) (C := (-18825936/95703125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_9 logL_10
  have hMnn : 0 ≤ (4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2903/1225) + (-768/1225) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (51/16))]
  calc (-484647141/382812500) + (330287621/306250000) * s + (-18825936/95703125) * s ^ 2
      = ((2903/1225) + (-768/1225) * s) * ((4462871/10000000) * (((13/4) - s) / ((13/4) - (25/8))) + (2427539/5000000) * ((s - (25/8)) / ((13/4) - (25/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 10 lower: `(819919613/43808000000) ≤ ∫_{(13/4)}^{(27/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_10 :
    ((819919613/43808000000):ℝ) ≤ ∫ s in ((13/4):ℝ)..(27/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-73146437/68450000)) (B := (1589626653/1711250000)) (C := (-18115344/106953125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_10 logL_11
  have hMnn : 0 ≤ (2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (2951/1369) + (-768/1369) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (53/16))]
  calc (-73146437/68450000) + (1589626653/1711250000) * s + (-18115344/106953125) * s ^ 2
      = ((2951/1369) + (-768/1369) * s) * ((2427539/5000000) * (((27/8) - s) / ((27/8) - (13/4))) + (5232481/10000000) * ((s - (13/4)) / ((27/8) - (13/4)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 11 lower: `(1897516561/121680000000) ≤ ∫_{(27/8)}^{(7/2)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_11 :
    ((1897516561/121680000000):ℝ) ≤ ∫ s in ((27/8):ℝ)..(7/2), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-4573010687/5070000000)) (B := (127340411/158437500)) (C := (-5818816/39609375))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_11 logL_12
  have hMnn : 0 ≤ (5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (997/507) + (-256/507) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (55/16))]
  calc (-4573010687/5070000000) + (127340411/158437500) * s + (-5818816/39609375) * s ^ 2
      = ((997/507) + (-256/507) * s) * ((5232481/10000000) * (((7/2) - s) / ((7/2) - (27/8))) + (5596157/10000000) * ((s - (27/8)) / ((7/2) - (27/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 12 lower: `(826822953/67240000000) ≤ ∫_{(7/2)}^{(29/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_12 :
    ((826822953/67240000000):ℝ) ≤ ∫ s in ((7/2):ℝ)..(29/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-2557116401/3362000000)) (B := (733419391/1050625000)) (C := (-16843872/131328125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_12 logL_13
  have hMnn : 0 ≤ (5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (3023/1681) + (-768/1681) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (57/16))]
  calc (-2557116401/3362000000) + (733419391/1050625000) * s + (-16843872/131328125) * s ^ 2
      = ((3023/1681) + (-768/1681) * s) * ((5596157/10000000) * (((29/8) - s) / ((29/8) - (7/2))) + (5947071/10000000) * ((s - (7/2)) / ((29/8) - (7/2)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 13 lower: `(524940903/59168000000) ≤ ∫_{(29/8)}^{(15/4)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_13 :
    ((524940903/59168000000):ℝ) ≤ ∫ s in ((29/8):ℝ)..(15/4), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-2958914277/4622500000)) (B := (1405877649/2311250000)) (C := (-3254544/28890625))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_13 logL_14
  have hMnn : 0 ≤ (5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (3047/1849) + (-768/1849) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (59/16))]
  calc (-2958914277/4622500000) + (1405877649/2311250000) * s + (-3254544/28890625) * s ^ 2
      = ((3047/1849) + (-768/1849) * s) * ((5947071/10000000) * (((15/4) - s) / ((15/4) - (29/8))) + (3143043/5000000) * ((s - (29/8)) / ((15/4) - (29/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 14 lower: `(868131541/162000000000) ≤ ∫_{(15/4)}^{(31/8)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_14 :
    ((868131541/162000000000):ℝ) ≤ ∫ s in ((15/4):ℝ)..(31/8), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-604236989/1125000000)) (B := (224205593/421875000)) (C := (-5246368/52734375))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_14 logL_15
  have hMnn : 0 ≤ (3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (1021/675) + (-256/675) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (61/16))]
  calc (-604236989/1125000000) + (224205593/421875000) * s + (-5246368/52734375) * s ^ 2
      = ((1021/675) + (-256/675) * s) * ((3143043/5000000) * (((31/8) - s) / ((31/8) - (15/4))) + (206687/312500) * ((s - (15/4)) / ((31/8) - (15/4)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- Panel 15 lower: `(631556593/353440000000) ≤ ∫_{(31/8)}^{(4)} (4−s)/(s−1)·log(s/2)`. -/
theorem masseL_15 :
    ((631556593/353440000000):ℝ) ≤ ∫ s in ((31/8):ℝ)..(4), (4 - s) / (s - 1) * Real.log (s / 2) := by
  apply panel_ge _ (A := (-9913535023/22090000000)) (B := (51396057/110450000)) (C := (-15239376/172578125))
    (by norm_num) (masse_ii (by norm_num) (by norm_num)) ?_ (by norm_num)
  intro s hs; obtain ⟨hsp, hsq⟩ := hs
  have hsm1 : (0:ℝ) < s - 1 := by linarith
  have hlog : (206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8))) ≤ Real.log (s / 2) :=
    log_half_ge_chord (by norm_num) (by norm_num) hsp hsq logL_15 logL_16
  have hMnn : 0 ≤ (206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8))) := by
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
    · exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by norm_num))
  have hW0 : 0 ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hWtan : (3071/2209) + (-768/2209) * s ≤ (4 - s) / (s - 1) := by
    rw [le_div_iff₀ hsm1]; nlinarith [sq_nonneg (s - (63/16))]
  calc (-9913535023/22090000000) + (51396057/110450000) * s + (-15239376/172578125) * s ^ 2
      = ((3071/2209) + (-768/2209) * s) * ((206687/312500) * (((4) - s) / ((4) - (31/8))) + (6931471/10000000) * ((s - (31/8)) / ((4) - (31/8)))) := by ring
    _ ≤ (4 - s) / (s - 1) * Real.log (s / 2) := mul_le_mul hWtan hlog hMnn hW0

/-- **Certified level-2 head mass, tight upper bound.**  `massE 2 ≤ 2950/10000` (true `0.2936`). -/
theorem massE_two_tight : massE 2 ≤ 2950 / 10000 := by
  rw [massE_two_integral]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (2)) (b := (17/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (17/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (17/8)) (b := (9/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (9/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (9/4)) (b := (19/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (19/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (19/8)) (b := (5/2)) (by norm_num) (by norm_num))
    (masse_ii (a := (5/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (5/2)) (b := (21/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (21/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (21/8)) (b := (11/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (11/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (11/4)) (b := (23/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (23/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (23/8)) (b := (3)) (by norm_num) (by norm_num))
    (masse_ii (a := (3)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (3)) (b := (25/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (25/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (25/8)) (b := (13/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (13/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (13/4)) (b := (27/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (27/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (27/8)) (b := (7/2)) (by norm_num) (by norm_num))
    (masse_ii (a := (7/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (7/2)) (b := (29/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (29/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (29/8)) (b := (15/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (15/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (15/4)) (b := (31/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (31/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  linarith [masseU_0, masseU_1, masseU_2, masseU_3, masseU_4, masseU_5, masseU_6, masseU_7, masseU_8, masseU_9, masseU_10, masseU_11, masseU_12, masseU_13, masseU_14, masseU_15]

/-- **Certified level-2 head mass, lower bound.**  `2900/10000 ≤ massE 2`. -/
theorem massE_two_lower : (2900 : ℝ) / 10000 ≤ massE 2 := by
  rw [massE_two_integral]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (2)) (b := (17/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (17/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (17/8)) (b := (9/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (9/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (9/4)) (b := (19/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (19/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (19/8)) (b := (5/2)) (by norm_num) (by norm_num))
    (masse_ii (a := (5/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (5/2)) (b := (21/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (21/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (21/8)) (b := (11/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (11/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (11/4)) (b := (23/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (23/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (23/8)) (b := (3)) (by norm_num) (by norm_num))
    (masse_ii (a := (3)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (3)) (b := (25/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (25/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (25/8)) (b := (13/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (13/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (13/4)) (b := (27/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (27/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (27/8)) (b := (7/2)) (by norm_num) (by norm_num))
    (masse_ii (a := (7/2)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (7/2)) (b := (29/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (29/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (29/8)) (b := (15/4)) (by norm_num) (by norm_num))
    (masse_ii (a := (15/4)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (masse_ii (a := (15/4)) (b := (31/8)) (by norm_num) (by norm_num))
    (masse_ii (a := (31/8)) (b := (4:ℝ)) (by norm_num) (by norm_num))]
  linarith [masseL_0, masseL_1, masseL_2, masseL_3, masseL_4, masseL_5, masseL_6, masseL_7, masseL_8, masseL_9, masseL_10, masseL_11, masseL_12, masseL_13, masseL_14, masseL_15]

/-! ## Part 3 — the Φ-moment constants `Cphi1`, `Cphi2` (near-exact certified upper bounds)

Route: bound the inner integrand `h(w) = log((w+1)/2)/w ≤ a + b·w` (`a = 2487/10000`,
`b = −3/625`) on `[3,5]` via 16 sub-interval tangents, giving the rational-quadratic envelope
`Φ(v) ≤ P(v) = a(v−2) + b((v+1)²−9)/2` (`Phi_le_quad`); then the outer integral for `Cphi2` is
elementary and certifies `Cphi2 ≤ 0.14194 ≤ 0.145`.  `Cphi1` is NOT landed here (see the header
flag): its `log(3/(v−1))` weight needs a 4-panel secant upper bound to reach `≤ 0.04497 ≤ 0.046`. -/

/-- `log((wc_0+1)/2) ≤ (3543257/5000000)`. -/
theorem logW_0 : Real.log ((65/16) / 2) ≤ (3543257/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_1+1)/2) ≤ (57731/78125)`. -/
theorem logW_1 : Real.log ((67/16) / 2) ≤ (57731/78125) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_2+1)/2) ≤ (7683707/10000000)`. -/
theorem logW_2 : Real.log ((69/16) / 2) ≤ (7683707/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_3+1)/2) ≤ (49809/62500)`. -/
theorem logW_3 : Real.log ((71/16) / 2) ≤ (49809/62500) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_4+1)/2) ≤ (2061809/2500000)`. -/
theorem logW_4 : Real.log ((73/16) / 2) ≤ (2061809/2500000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_5+1)/2) ≤ (8517523/10000000)`. -/
theorem logW_5 : Real.log ((75/16) / 2) ≤ (8517523/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_6+1)/2) ≤ (1097587/1250000)`. -/
theorem logW_6 : Real.log ((77/16) / 2) ≤ (1097587/1250000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_7+1)/2) ≤ (28241/31250)`. -/
theorem logW_7 : Real.log ((79/16) / 2) ≤ (28241/31250) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_8+1)/2) ≤ (4643567/5000000)`. -/
theorem logW_8 : Real.log ((81/16) / 2) ≤ (4643567/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_9+1)/2) ≤ (1191381/1250000)`. -/
theorem logW_9 : Real.log ((83/16) / 2) ≤ (1191381/1250000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_10+1)/2) ≤ (1953831/2000000)`. -/
theorem logW_10 : Real.log ((85/16) / 2) ≤ (1953831/2000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_11+1)/2) ≤ (2500431/2500000)`. -/
theorem logW_11 : Real.log ((87/16) / 2) ≤ (2500431/2500000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_12+1)/2) ≤ (10229007/10000000)`. -/
theorem logW_12 : Real.log ((89/16) / 2) ≤ (10229007/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_13+1)/2) ≤ (5225619/5000000)`. -/
theorem logW_13 : Real.log ((91/16) / 2) ≤ (5225619/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_14+1)/2) ≤ (5334319/5000000)`. -/
theorem logW_14 : Real.log ((93/16) / 2) ≤ (5334319/5000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `log((wc_15+1)/2) ≤ (10881413/10000000)`. -/
theorem logW_15 : Real.log ((95/16) / 2) ≤ (10881413/10000000) :=
  log_le_of_taylor (by norm_num) 10 (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- Panel 0: `log((w+1)/2) ≤ a·w + b·w²` on `[(3),(25/8)]`. -/
theorem hpoly_0 : ∀ w ∈ Set.Icc ((3):ℝ) (25/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (3543257/5000000) + ((w + 1) - (65/16)) / (65/16) :=
    log_half_le_tangent (c := (65/16)) (s := w + 1) (by norm_num) (by linarith) logW_0
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 1: `log((w+1)/2) ≤ a·w + b·w²` on `[(25/8),(13/4)]`. -/
theorem hpoly_1 : ∀ w ∈ Set.Icc ((25/8):ℝ) (13/4),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (57731/78125) + ((w + 1) - (67/16)) / (67/16) :=
    log_half_le_tangent (c := (67/16)) (s := w + 1) (by norm_num) (by linarith) logW_1
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 2: `log((w+1)/2) ≤ a·w + b·w²` on `[(13/4),(27/8)]`. -/
theorem hpoly_2 : ∀ w ∈ Set.Icc ((13/4):ℝ) (27/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (7683707/10000000) + ((w + 1) - (69/16)) / (69/16) :=
    log_half_le_tangent (c := (69/16)) (s := w + 1) (by norm_num) (by linarith) logW_2
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 3: `log((w+1)/2) ≤ a·w + b·w²` on `[(27/8),(7/2)]`. -/
theorem hpoly_3 : ∀ w ∈ Set.Icc ((27/8):ℝ) (7/2),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (49809/62500) + ((w + 1) - (71/16)) / (71/16) :=
    log_half_le_tangent (c := (71/16)) (s := w + 1) (by norm_num) (by linarith) logW_3
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 4: `log((w+1)/2) ≤ a·w + b·w²` on `[(7/2),(29/8)]`. -/
theorem hpoly_4 : ∀ w ∈ Set.Icc ((7/2):ℝ) (29/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (2061809/2500000) + ((w + 1) - (73/16)) / (73/16) :=
    log_half_le_tangent (c := (73/16)) (s := w + 1) (by norm_num) (by linarith) logW_4
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 5: `log((w+1)/2) ≤ a·w + b·w²` on `[(29/8),(15/4)]`. -/
theorem hpoly_5 : ∀ w ∈ Set.Icc ((29/8):ℝ) (15/4),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (8517523/10000000) + ((w + 1) - (75/16)) / (75/16) :=
    log_half_le_tangent (c := (75/16)) (s := w + 1) (by norm_num) (by linarith) logW_5
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 6: `log((w+1)/2) ≤ a·w + b·w²` on `[(15/4),(31/8)]`. -/
theorem hpoly_6 : ∀ w ∈ Set.Icc ((15/4):ℝ) (31/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (1097587/1250000) + ((w + 1) - (77/16)) / (77/16) :=
    log_half_le_tangent (c := (77/16)) (s := w + 1) (by norm_num) (by linarith) logW_6
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 7: `log((w+1)/2) ≤ a·w + b·w²` on `[(31/8),(4)]`. -/
theorem hpoly_7 : ∀ w ∈ Set.Icc ((31/8):ℝ) (4),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (28241/31250) + ((w + 1) - (79/16)) / (79/16) :=
    log_half_le_tangent (c := (79/16)) (s := w + 1) (by norm_num) (by linarith) logW_7
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 8: `log((w+1)/2) ≤ a·w + b·w²` on `[(4),(33/8)]`. -/
theorem hpoly_8 : ∀ w ∈ Set.Icc ((4):ℝ) (33/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (4643567/5000000) + ((w + 1) - (81/16)) / (81/16) :=
    log_half_le_tangent (c := (81/16)) (s := w + 1) (by norm_num) (by linarith) logW_8
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 9: `log((w+1)/2) ≤ a·w + b·w²` on `[(33/8),(17/4)]`. -/
theorem hpoly_9 : ∀ w ∈ Set.Icc ((33/8):ℝ) (17/4),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (1191381/1250000) + ((w + 1) - (83/16)) / (83/16) :=
    log_half_le_tangent (c := (83/16)) (s := w + 1) (by norm_num) (by linarith) logW_9
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 10: `log((w+1)/2) ≤ a·w + b·w²` on `[(17/4),(35/8)]`. -/
theorem hpoly_10 : ∀ w ∈ Set.Icc ((17/4):ℝ) (35/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (1953831/2000000) + ((w + 1) - (85/16)) / (85/16) :=
    log_half_le_tangent (c := (85/16)) (s := w + 1) (by norm_num) (by linarith) logW_10
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 11: `log((w+1)/2) ≤ a·w + b·w²` on `[(35/8),(9/2)]`. -/
theorem hpoly_11 : ∀ w ∈ Set.Icc ((35/8):ℝ) (9/2),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (2500431/2500000) + ((w + 1) - (87/16)) / (87/16) :=
    log_half_le_tangent (c := (87/16)) (s := w + 1) (by norm_num) (by linarith) logW_11
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 12: `log((w+1)/2) ≤ a·w + b·w²` on `[(9/2),(37/8)]`. -/
theorem hpoly_12 : ∀ w ∈ Set.Icc ((9/2):ℝ) (37/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (10229007/10000000) + ((w + 1) - (89/16)) / (89/16) :=
    log_half_le_tangent (c := (89/16)) (s := w + 1) (by norm_num) (by linarith) logW_12
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 13: `log((w+1)/2) ≤ a·w + b·w²` on `[(37/8),(19/4)]`. -/
theorem hpoly_13 : ∀ w ∈ Set.Icc ((37/8):ℝ) (19/4),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (5225619/5000000) + ((w + 1) - (91/16)) / (91/16) :=
    log_half_le_tangent (c := (91/16)) (s := w + 1) (by norm_num) (by linarith) logW_13
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 14: `log((w+1)/2) ≤ a·w + b·w²` on `[(19/4),(39/8)]`. -/
theorem hpoly_14 : ∀ w ∈ Set.Icc ((19/4):ℝ) (39/8),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (5334319/5000000) + ((w + 1) - (93/16)) / (93/16) :=
    log_half_le_tangent (c := (93/16)) (s := w + 1) (by norm_num) (by linarith) logW_14
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- Panel 15: `log((w+1)/2) ≤ a·w + b·w²` on `[(39/8),(5)]`. -/
theorem hpoly_15 : ∀ w ∈ Set.Icc ((39/8):ℝ) (5),
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hwp, hwq⟩ := hw
  have ht : Real.log ((w + 1) / 2) ≤ (10881413/10000000) + ((w + 1) - (95/16)) / (95/16) :=
    log_half_le_tangent (c := (95/16)) (s := w + 1) (by norm_num) (by linarith) logW_15
  nlinarith [ht, mul_nonneg (sub_nonneg.2 hwp) (sub_nonneg.2 hwq)]

/-- `log((w+1)/2) ≤ a·w + b·w²` on all of `[3,5]` (16-panel case split). -/
theorem hlog2poly_all : ∀ w ∈ Set.Icc (3:ℝ) 5,
    Real.log ((w + 1) / 2) ≤ (2487/10000) * w + (-3/625) * w ^ 2 := by
  intro w hw; obtain ⟨hw3, hw5⟩ := hw
  rcases le_or_gt w (25/8) with hh0 | hh0
  · exact hpoly_0 w ⟨hw3, hh0⟩
  · rcases le_or_gt w (13/4) with hh1 | hh1
    · exact hpoly_1 w ⟨hh0.le, hh1⟩
    · rcases le_or_gt w (27/8) with hh2 | hh2
      · exact hpoly_2 w ⟨hh1.le, hh2⟩
      · rcases le_or_gt w (7/2) with hh3 | hh3
        · exact hpoly_3 w ⟨hh2.le, hh3⟩
        · rcases le_or_gt w (29/8) with hh4 | hh4
          · exact hpoly_4 w ⟨hh3.le, hh4⟩
          · rcases le_or_gt w (15/4) with hh5 | hh5
            · exact hpoly_5 w ⟨hh4.le, hh5⟩
            · rcases le_or_gt w (31/8) with hh6 | hh6
              · exact hpoly_6 w ⟨hh5.le, hh6⟩
              · rcases le_or_gt w (4) with hh7 | hh7
                · exact hpoly_7 w ⟨hh6.le, hh7⟩
                · rcases le_or_gt w (33/8) with hh8 | hh8
                  · exact hpoly_8 w ⟨hh7.le, hh8⟩
                  · rcases le_or_gt w (17/4) with hh9 | hh9
                    · exact hpoly_9 w ⟨hh8.le, hh9⟩
                    · rcases le_or_gt w (35/8) with hh10 | hh10
                      · exact hpoly_10 w ⟨hh9.le, hh10⟩
                      · rcases le_or_gt w (9/2) with hh11 | hh11
                        · exact hpoly_11 w ⟨hh10.le, hh11⟩
                        · rcases le_or_gt w (37/8) with hh12 | hh12
                          · exact hpoly_12 w ⟨hh11.le, hh12⟩
                          · rcases le_or_gt w (19/4) with hh13 | hh13
                            · exact hpoly_13 w ⟨hh12.le, hh13⟩
                            · rcases le_or_gt w (39/8) with hh14 | hh14
                              · exact hpoly_14 w ⟨hh13.le, hh14⟩
                              · exact hpoly_15 w ⟨hh14.le, hw5⟩

/-- `∫_p^q (A + B·w) dw = A(q−p) + B(q²−p²)/2`. -/
theorem integral_line (A B p q : ℝ) :
    (∫ w in p..q, (A + B * w)) = A * (q - p) + B * (q ^ 2 - p ^ 2) / 2 := by
  have iA : IntervalIntegrable (fun _ : ℝ => A) volume p q := _root_.intervalIntegrable_const
  have iB : IntervalIntegrable (fun w : ℝ => B * w) volume p q := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add iA iB, intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_const_mul, _root_.integral_id]
  ring

/-- Integrability of `c0·(1/v) + c1 + c2·v` on `[2,4]`. -/
private theorem gII :
    IntervalIntegrable (fun v => (-2391/5000) * (1 / v) + (2439/10000) + (-3/1250) * v) volume 2 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num)]
  have hv0 : ∀ v ∈ Set.Icc (2:ℝ) 4, v ≠ 0 :=
    fun v hv => (show (0:ℝ) < v by linarith [hv.1]).ne'
  exact ((continuousOn_const.mul (continuousOn_const.div continuousOn_id hv0)).add
    continuousOn_const).add (continuousOn_const.mul continuousOn_id)

/-- `Φ(v) ≤ a(v−2) + b((v+1)²−9)/2` on `[2,4]` (integrate the panel envelope). -/
theorem Phi_le_quad : ∀ v ∈ Set.Icc (2:ℝ) 4,
    Phi v ≤ (2487/10000) * (v - 2) + (-3/625) * ((v + 1) ^ 2 - 9) / 2 := by
  intro v hv; obtain ⟨hv2, hv4⟩ := hv
  have hb1 : (3:ℝ) ≤ v + 1 := by linarith
  have hsub : Set.Icc (3:ℝ) (v + 1) ⊆ Set.Icc (3:ℝ) 5 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hii_h : IntervalIntegrable (fun w => Real.log ((w + 1) / 2) / w) volume 3 (v + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
    · intro x hx; rw [Set.uIcc_of_le hb1] at hx
      have : (3:ℝ) ≤ x := hx.1; exact (show (0:ℝ) < (x + 1) / 2 by linarith).ne'
    · intro x hx; rw [Set.uIcc_of_le hb1] at hx
      have : (3:ℝ) ≤ x := hx.1; intro h; rw [h] at this; norm_num at this
  have hii_l : IntervalIntegrable (fun w => (2487/10000) + (-3/625) * w) volume 3 (v + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hmono : (∫ w in (3:ℝ)..(v + 1), Real.log ((w + 1) / 2) / w)
      ≤ ∫ w in (3:ℝ)..(v + 1), ((2487/10000) + (-3/625) * w) := by
    apply intervalIntegral.integral_mono_on hb1 hii_h hii_l
    intro x hx
    have hx3 : (3:ℝ) ≤ x := hx.1
    have hx0 : (0:ℝ) < x := by linarith
    have hpoly := hlog2poly_all x (hsub hx)
    rw [div_le_iff₀ hx0]; nlinarith [hpoly]
  have heval : (∫ w in (3:ℝ)..(v + 1), ((2487/10000) + (-3/625) * w))
      = (2487/10000) * (v - 2) + (-3/625) * ((v + 1) ^ 2 - 9) / 2 := by
    rw [integral_line]; ring
  unfold Phi
  rw [heval] at hmono; exact hmono

/-- **Certified Φ-moment tail-mass constant.**  `Cphi2 ≤ 1450/10000` (true `0.14127`). -/
theorem Cphi2_tight : Cphi2 ≤ 1450 / 10000 := by
  have hiiP : IntervalIntegrable (fun v => Phi v / v) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact Phi_continuousOn.div continuousOn_id
      (fun v hv => (show (0:ℝ) < v by linarith [hv.1]).ne')
  have hmono : Cphi2 ≤ ∫ v in (2:ℝ)..4,
      ((-2391/5000) * (1 / v) + (2439/10000) + (-3/1250) * v) := by
    unfold Cphi2
    apply intervalIntegral.integral_mono_on (by norm_num) hiiP gII
    intro v hv; obtain ⟨hv2, hv4⟩ := hv
    have hv0 : (0:ℝ) < v := by linarith
    have hP := Phi_le_quad v ⟨hv2, hv4⟩
    have h1 : Phi v / v ≤
        ((2487/10000) * (v - 2) + (-3/625) * ((v + 1) ^ 2 - 9) / 2) / v := by gcongr
    have h2 : ((2487/10000) * (v - 2) + (-3/625) * ((v + 1) ^ 2 - 9) / 2) / v
        = (-2391/5000) * (1 / v) + (2439/10000) + (-3/1250) * v := by field_simp; ring
    rw [h2] at h1; exact h1
  have heval : (∫ v in (2:ℝ)..4,
      ((-2391/5000) * (1 / v) + (2439/10000) + (-3/1250) * v))
      = (-2391/5000) * (Real.log 4 - Real.log 2) + (2439/10000) * 2 + (-3/1250) * 6 := by
    have hv0 : ∀ v ∈ Set.uIcc (2:ℝ) 4, v ≠ 0 := by
      intro v hv; rw [Set.uIcc_of_le (by norm_num)] at hv
      exact (show (0:ℝ) < v by linarith [hv.1]).ne'
    have iA : IntervalIntegrable (fun v : ℝ => (-2391/5000) * (1 / v)) volume 2 4 := by
      apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.mul (continuousOn_const.div continuousOn_id hv0)
    have iB : IntervalIntegrable (fun _ : ℝ => (2439/10000 : ℝ)) volume 2 4 := by
      apply Continuous.intervalIntegrable; fun_prop
    have iC : IntervalIntegrable (fun v : ℝ => (-3/1250) * v) volume 2 4 := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add (iA.add iB) iC, intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const_mul, integral_one_div (by norm_num),
      Real.log_div (by norm_num) (by norm_num), intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, _root_.integral_id]
    ring
  rw [heval] at hmono
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog4] at hmono
  linarith [hmono, le_log_two]

end Salt.Chen
