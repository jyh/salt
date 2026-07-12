/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# V2.SW-maxy — the `y`-uniform lift for the SW piece (`Salt/BV/SWMaxY.lean`)

Design: `docs/blueprints/bv.md`, node `V2.SW-maxy`. The per-`y` Siegel–Walfisz
bound `‖ψ(y,χ)‖ ≤ K·y/(log y)^A` (for `y ≥ 2`) needs lifting to a `y`-uniform
statement at the top scale `x`, for the V3.1 assembly's `max_{y ≤ x}`
packaging. The catch: `t ↦ t/(log t)^A` is *not* monotone all the way down to
`t = 2` — it is increasing only once `log t > A`, i.e. `t > exp A` — so the
max over `2 ≤ y ≤ x` needs an extra additive constant to cover the small-`y`
regime below the threshold `exp A`.

## Route (two-regime split at `T = exp A`)

* **Small `y` (`y ≤ T`):** since `y ≥ 2`, `log y ≥ log 2 > 0`, so
  `(log y)^A ≥ (log 2)^A` (`Real.rpow_le_rpow`), giving the crude bound
  `y/(log y)^A ≤ y/(log 2)^A ≤ T/(log 2)^A =: C`. This `C` depends only on
  `A` and absorbs the entire small-`y` regime (the `x/(log x)^A` term is
  added for free since it is `≥ 0`).
* **Large `y` (`y > T`, hence also `x ≥ y > T`):** `f(t) = t/(log t)^A` is
  `MonotoneOn (Set.Ici T)`. Route: `f = (fun t => t) / (fun t => (log t)^A)`,
  differentiated via `HasDerivAt.div` composed with `HasDerivAt.rpow_const`
  on `Real.hasDerivAt_log`; the resulting derivative
  `((log t)^A − A·(log t)^(A−1)) / ((log t)^A)²` factors (via `rpow_add`) as
  `(log t)^(A−1)·(log t − A) / ((log t)^A)²`, manifestly `≥ 0` exactly when
  `log t ≥ A`, i.e. `t ≥ T`. `monotoneOn_of_hasDerivWithinAt_nonneg` then
  gives `f y ≤ f x` for `T ≤ y ≤ x` (`C` is added for free since `C ≥ 0`).

Both regimes land inside `C + x/(log x)^A`, closing the deliverable exactly
as stated in the node brief (no statement weakening was needed — the
calculus route landed cleanly).
-/

namespace Salt.BV

/-- The pointwise derivative of `t ↦ t / (log t)^A`, valid for `1 < t` (so
`log t ≠ 0` and the quotient rule applies). Route: `HasDerivAt.div` (on
`id`/`fun t => (log t)^A`) composed with `HasDerivAt.rpow_const` on
`Real.hasDerivAt_log`. -/
private theorem hasDerivAt_div_log_rpow {A t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => t / (Real.log t) ^ A)
      ((1 * (Real.log t) ^ A - t * (t⁻¹ * A * (Real.log t) ^ (A - 1))) / ((Real.log t) ^ A) ^ 2)
      t := by
  have ht0 : t ≠ 0 := (lt_trans one_pos ht).ne'
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogne : Real.log t ≠ 0 := hlogpos.ne'
  have hd : HasDerivAt (fun t : ℝ => (Real.log t) ^ A)
      (t⁻¹ * A * (Real.log t) ^ (A - 1)) t :=
    (Real.hasDerivAt_log ht0).rpow_const (Or.inl hlogne)
  have hdenom : (Real.log t) ^ A ≠ 0 := (Real.rpow_pos_of_pos hlogpos A).ne'
  have hc : HasDerivAt (fun t : ℝ => t) (1 : ℝ) t := hasDerivAt_id t
  exact hc.div hd hdenom

/-- The derivative of `t ↦ t/(log t)^A` from `hasDerivAt_div_log_rpow` is
nonnegative once `log t ≥ A`. Route: `field_simp` clears the `t·t⁻¹`
cancellation, then `rpow_add` factors `(log t)^A = (log t)^(A-1)·(log t)`,
isolating the sign-determining factor `log t − A`. -/
private theorem deriv_div_log_rpow_nonneg {A t : ℝ} (ht : 1 < t) (hge : A ≤ Real.log t) :
    (0 : ℝ) ≤ (1 * (Real.log t) ^ A - t * (t⁻¹ * A * (Real.log t) ^ (A - 1)))
      / ((Real.log t) ^ A) ^ 2 := by
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hnum : (1 * (Real.log t) ^ A - t * (t⁻¹ * A * (Real.log t) ^ (A - 1)))
      = (Real.log t) ^ A - A * (Real.log t) ^ (A - 1) := by field_simp
  rw [hnum]
  have hsplit : (Real.log t) ^ A = (Real.log t) ^ (A - 1) * (Real.log t) ^ (1 : ℝ) := by
    rw [← Real.rpow_add hlogpos]; ring_nf
  rw [hsplit, Real.rpow_one]
  have hpow_pos : 0 < (Real.log t) ^ (A - 1) := Real.rpow_pos_of_pos hlogpos _
  have hnum2 : (Real.log t) ^ (A - 1) * Real.log t - A * (Real.log t) ^ (A - 1)
      = (Real.log t) ^ (A - 1) * (Real.log t - A) := by ring
  rw [hnum2]
  exact div_nonneg (mul_nonneg hpow_pos.le (by linarith)) (by positivity)

/-- `t ↦ t/(log t)^A` is monotone on `[exp A, ∞)` (`A > 0`): the derivative
is nonnegative there by `deriv_div_log_rpow_nonneg`, via
`monotoneOn_of_hasDerivWithinAt_nonneg`. -/
private theorem monotoneOn_div_log_rpow {A : ℝ} (hA : 0 < A) :
    MonotoneOn (fun t : ℝ => t / (Real.log t) ^ A) (Set.Ici (Real.exp A)) := by
  have hExpA1 : 1 < Real.exp A := by
    have h := Real.exp_lt_exp.mpr hA
    simpa using h
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (Real.exp A))
  · intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hExpA1 ht
    exact (hasDerivAt_div_log_rpow ht1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht1 : 1 < t := lt_trans hExpA1 ht
    exact (hasDerivAt_div_log_rpow ht1).hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht1 : 1 < t := lt_trans hExpA1 ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have hlogge : A ≤ Real.log t := le_of_lt ((Real.lt_log_iff_exp_lt ht0).mpr ht)
    exact deriv_div_log_rpow_nonneg ht1 hlogge

/-- **V2.SW-maxy.** The `y`-uniform lift: for `A > 0` there is a constant
`C = exp(A)/(log 2)^A ≥ 0`, depending only on `A`, such that for all
`2 ≤ y ≤ x` (with `x ≥ 3`), `y/(log y)^A ≤ C + x/(log x)^A`. This is exactly
the shape the V3.1 assembly needs to turn the per-`y` SW bound into a bound
at the top scale `x` uniform over `y ≤ x`. Route: split at the threshold
`T = exp A` — below `T`, `y/(log y)^A ≤ T/(log 2)^A = C` since `log y ≥ log 2`
for `y ≥ 2`; above `T` (where `x ≥ y > T` too), `monotoneOn_div_log_rpow`
gives `y/(log y)^A ≤ x/(log x)^A` directly. -/
theorem sup_div_log_pow_le {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ y → y ≤ x → 3 ≤ x →
      (y : ℝ) / (Real.log y) ^ A ≤ C + (x : ℝ) / (Real.log x) ^ A := by
  set C : ℝ := Real.exp A / (Real.log 2) ^ A with hCdef
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hCnonneg : 0 ≤ C := div_nonneg (Real.exp_pos A).le (Real.rpow_pos_of_pos hlog2pos A).le
  refine ⟨C, hCnonneg, ?_⟩
  intro x y hy2 hxy hx3
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxyR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxy
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hxlogpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hxnonneg : 0 ≤ (x : ℝ) / (Real.log x) ^ A :=
    div_nonneg hxpos.le (Real.rpow_pos_of_pos hxlogpos A).le
  by_cases hcase : (y : ℝ) ≤ Real.exp A
  · -- Small-`y` regime: absorbed by `C`.
    have hylog_ge : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2R
    have hpow_ge : (Real.log 2) ^ A ≤ (Real.log y) ^ A :=
      Real.rpow_le_rpow hlog2pos.le hylog_ge hA.le
    have hypos : (0 : ℝ) < (y : ℝ) := by linarith
    calc (y : ℝ) / (Real.log y) ^ A
        ≤ (y : ℝ) / (Real.log 2) ^ A :=
          div_le_div_of_nonneg_left hypos.le (Real.rpow_pos_of_pos hlog2pos A) hpow_ge
      _ ≤ Real.exp A / (Real.log 2) ^ A :=
          div_le_div_of_nonneg_right hcase (Real.rpow_pos_of_pos hlog2pos A).le
      _ = C := hCdef.symm
      _ ≤ C + (x : ℝ) / (Real.log x) ^ A := by linarith
  · -- Large-`y` regime: monotonicity of `t ↦ t/(log t)^A` on `[exp A, ∞)`.
    have hcase' : Real.exp A < (y : ℝ) := not_le.mp hcase
    have hyD : (y : ℝ) ∈ Set.Ici (Real.exp A) := le_of_lt hcase'
    have hxD : (x : ℝ) ∈ Set.Ici (Real.exp A) := le_trans hyD hxyR
    have hmono := monotoneOn_div_log_rpow hA hyD hxD hxyR
    calc (y : ℝ) / (Real.log y) ^ A ≤ (x : ℝ) / (Real.log x) ^ A := hmono
      _ ≤ C + (x : ℝ) / (Real.log x) ^ A := by linarith

end Salt.BV
