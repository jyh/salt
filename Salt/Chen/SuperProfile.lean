/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SuperSolution
import Salt.Chen.LogToolkit

/-!
# SS2 — the concrete super-solution profile (the numeric keystone's final node)

Design: `docs/blueprints/flags.md`, `2026-07-13 TK3b GATE` / `SS1` / `SS2`.

SS1 (`SuperSolution.lean`) reduced BOTH mass ledgers to exhibiting ONE concrete pair
`(Ebar, Obar)` discharging six hypothesis groups (nonneg, integrable, `hSE`, `hSO`, and the two
`∫`-budgets), via `massSum_le_A2_of_superSolution` / `massOSum_le_A1_of_superSolution`.  This file
records the **explicit, exact-rational-certified profile** that discharges them, together with the
reusable **structural layer** those hypotheses factor through.

## STATUS (this session)

* **The profile is fully solved and EXACT-RATIONAL certified in Python** (fractions, no floats in
  the certificate): a valid super-solution meeting BOTH frozen budgets exists and every panel
  check passes.  See "The certified profile" below — the object exists.
* **Landed here (sorry-free):** the four reusable structural lemmas that the `∀ b` hypotheses and
  the head/tail bounds factor through (`hSE_reduce`, `hSO_reduce`, `fseq2_upper_of_log_lower`,
  `tail_integral_le`), plus the achieved-budget arithmetic (`budE_le`, `budO_le`).
* **REMAINING (heavy-mechanical, flagged):** the generated per-panel transcription — 200 `Ebar`
  panels + 220 `Obar` panels, each a `norm_num`/`nlinarith` rational quadratic check, plus the
  PL trapezoid budget sums and the PL integrability/nonneg.  This is a multi-thousand-line
  code-generation grind that exceeds a single session's build budget; it is NOT below-floor math
  risk (the certificate proves it goes through), it is transcription volume.  See the SS2 flag
  entry for the full plan.

## The construction (why it escapes the Perron wall; see the TK3b gate)

Total even/odd sums satisfy the closed monotone system `E = f₂ + T_e[O]`, `O = T_o[E]`
(`SuperSolution.Xe_recursion` / `odd_step` in the `K → ∞` limit).  A **super-solution pair**
`(Ebar, Obar)` — nonneg, integrable, dominating the operator images pointwise — dominates every
truncation (`SuperSolution.superSol_dominates`), so `∫Ebar`/`∫Obar` cap the ledger sums.  We take
piecewise-linear (PL) `Ebar`, `Obar` on a shared uniform grid plus a power-law tail; PL (not step)
is forced by the budgets (step wastes `~0.03` on the even side, `~0.01` on the odd side; the odd
slack is only `11/125 − ∫O ≈ 1.45·10⁻³`).

## The certified profile (deterministic, reproducible — regenerate exactly)

Shared grid spacing `h = 1/20`.  `Ebar` PL on knots `{2, 2+1/20, …, 12}` (200 panels); `Obar` PL
on `{1, 1+1/20, …, 12}` (220 panels; flat region `[1,3)` carries the `T_o` image but does NOT
enter the odd budget `∫_3^∞`).  Beyond `W = 12`: power tail `Ebar v = Obar v = K / v³`,
`K = 1/10000`.  Knot values are the **round-up** (`⌈·⌉` to denominator `10⁷`) of the discrete
super-solution fixed point:

* `cE[a] := ⌈ f₂maj(a, a+h) + GO(a−1)/a ⌉`   (`GO x := ∫_x^∞ Obar`, exact rational),
* `cO[d] := ⌈ GE(max(d−1, 2))/d ⌉`             (`GE x := ∫_x^∞ Ebar`, exact rational),

iterated to a fixed point (25 iterations), where `f₂maj(a, ap)` is the tight chord upper bound of
`sup_[a,ap] fseq 2` from `fseq2_upper_of_log_lower` with rational log knots (`log((a−1))` chord
lower bounds, `log 3` upper `= L3up`).  This recipe is deterministic and reproduces the identical
certified table.

**Certificate (all EXACT rationals):**
* `∫Ebar = 126695471/225000000 ≈ 0.5630910 ≤ 43/75 = 0.5733333`  (even budget, slack `1.02·10⁻²`),
* `∫_3^∞ Obar = 312655139/3600000000 ≈ 0.0868486 ≤ 11/125 = 0.088`  (odd budget, slack `1.15·10⁻³`),
* hSE: all 200 panels pass (per panel: `Ebar(v)·v − f₂maj_num(v) − GO(v−1) ≥ 0`, a rational
  quadratic ≥ 0 on the panel — `nlinarith` shape, cf. TK1's `masseU_*`),
* hSO: all 220 panels pass (per panel: `Obar(w)·w − GE(w−1) ≥ 0` for `w ≥ 3`, and
  `Obar(w)·w − GE(2) ≥ 0` on the flat `[1,3)` — rational quadratics ≥ 0),
* tail (`v ≥ 13`): `2(v−1)² ≥ v²` (i.e. `(v−2)² ≥ 2`) ⟹ the power tail self-dominates; the seam
  `[12,13)` closes because `K ≥ 169·(∫_{11}^{12} Obar + K/(2·12²))` (checked: `10⁻⁴ ≥ 7.56·10⁻⁵`).

The `∀ b` quantification in `hSE`/`hSO` is removed by `hSE_reduce`/`hSO_reduce` (below): since the
integrands are nonnegative, `∫_v^b Obar(t−1) ≤ ∫_{v−1}^∞ Obar =: TO v`, a fixed rational upper
bound on each panel (`GO(v−1)` on `[v−1, W]` plus the tail `K/(2W²)` via `tail_integral_le`).

## The reusable structural layer (this file)

`hSE_reduce` / `hSO_reduce` turn the `∀ b` finite-integral hypotheses of SS1 into panel-local
checks against a fixed total-tail bound; `fseq2_upper_of_log_lower` is the head tool (tight chord
`fseq 2` majorant, reusing `LogToolkit`'s log sandwiches); `tail_integral_le` is the tail tool
(`∫_W^b K/x³ ≤ K/(2W²)`, exact).  These are profile-independent and feed the transcription.
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ## The achieved budgets (exact-rational certificate targets) -/

/-- The certified even integral budget clears the frozen A₂ constant `43/75`
(`∫Ebar = 126695471/225000000`, slack `≈ 1.02·10⁻²`). -/
theorem budE_le : (126695471 : ℝ) / 225000000 ≤ 43 / 75 := by norm_num

/-- The certified odd integral budget clears the frozen A₁ constant `11/125`
(`∫_3^∞ Obar = 312655139/3600000000`, slack `≈ 1.15·10⁻³` — the binding constraint). -/
theorem budO_le : (312655139 : ℝ) / 3600000000 ≤ 11 / 125 := by norm_num

/-! ## The `∀ b` reductions (SS1's `hSE`/`hSO` shapes ← panel-local checks)

Both hypotheses quantify over all finite tops `b`.  Because `Obar, Ebar ≥ 0`, the finite integral
is bounded by the (fixed) improper tail `TO`/`TE`, reducing each to a panel-local pointwise fact.
The `1/v ≥ 0` scaling is the only ingredient. -/

/-- **`hSE` reduction.**  If a fixed `TO v` bounds `∫_v^b Obar(t−1)` for every top `b ≥ v`, and the
panel-local inequality `fseq 2 v + (1/v)·TO v ≤ Ebar v` holds, then SS1's full `∀ b` `hSE` holds. -/
theorem hSE_reduce (Ebar Obar TO : ℝ → ℝ)
    (hTO : ∀ v, (2 : ℝ) ≤ v → ∀ b, v ≤ b → (∫ t in v..b, Obar (t - 1)) ≤ TO v)
    (hpt : ∀ v, (2 : ℝ) ≤ v → fseq 2 v + (1 / v) * TO v ≤ Ebar v) :
    ∀ v, (2 : ℝ) ≤ v → ∀ b, v ≤ b →
      fseq 2 v + (1 / v) * ∫ t in v..b, Obar (t - 1) ≤ Ebar v := by
  intro v hv b hvb
  have hv0 : (0 : ℝ) < v := by linarith
  have h1 : (1 / v) * (∫ t in v..b, Obar (t - 1)) ≤ (1 / v) * TO v :=
    mul_le_mul_of_nonneg_left (hTO v hv b hvb) (by positivity)
  linarith [hpt v hv]

/-- **`hSO` reduction.**  Sibling of `hSE_reduce` for the odd side (`max w 3` lower limit). -/
theorem hSO_reduce (Ebar Obar TE : ℝ → ℝ)
    (hTE : ∀ w, (1 : ℝ) ≤ w → ∀ b, max w 3 ≤ b → (∫ t in (max w 3)..b, Ebar (t - 1)) ≤ TE w)
    (hpt : ∀ w, (1 : ℝ) ≤ w → (1 / w) * TE w ≤ Obar w) :
    ∀ w, (1 : ℝ) ≤ w → ∀ b, max w 3 ≤ b →
      (1 / w) * ∫ t in (max w 3)..b, Ebar (t - 1) ≤ Obar w := by
  intro w hw b hwb
  have hw0 : (0 : ℝ) < w := by linarith
  have h1 : (1 / w) * (∫ t in (max w 3)..b, Ebar (t - 1)) ≤ (1 / w) * TE w :=
    mul_le_mul_of_nonneg_left (hTE w hw b hwb) (by positivity)
  linarith [hpt w hw]

/-! ## The head tool: the tight `fseq 2` majorant

On `[2,4]`, `fseq 2 v = (v − 3·log(v−1) + 3·log 3 − 4)/v` (`fseq_two_window`).  A rational lower
bound `clog ≤ log(v−1)` (per panel: the `LogToolkit.log_half_ge_chord` chord via `s = 2v−2`) and a
rational upper bound `L3up ≥ log 3` (`LogToolkit.log_three_le`) give a rational majorant; combined
with `GO(v−1)` this yields the per-panel `hSE` quadratic. -/

/-- **`fseq 2` chord majorant.**  For `v ∈ [2,4]`, `clog ≤ log(v−1)` and `log 3 ≤ L3up`,
`fseq 2 v ≤ (v − 3·clog + 3·L3up − 4)/v` (a rational function once `clog`, `L3up` are rational). -/
theorem fseq2_upper_of_log_lower {v clog L3up : ℝ} (hv2 : 2 ≤ v) (hv4 : v ≤ 4)
    (hclog : clog ≤ Real.log (v - 1)) (hL3 : Real.log 3 ≤ L3up) :
    fseq 2 v ≤ (v - 3 * clog + 3 * L3up - 4) / v := by
  rw [fseq_two_window hv2 hv4]
  have hv0 : (0 : ℝ) < v := by linarith
  have hnum : v - 3 * Real.log (v - 1) + 3 * Real.log 3 - 4 ≤ v - 3 * clog + 3 * L3up - 4 := by
    linarith [hclog, hL3]
  exact div_le_div_of_nonneg_right hnum hv0.le

/-! ## The tail tool: the power-law tail integral

Beyond `W`, `Ebar v = Obar v = K/v³`; its improper integral is the exact rational `K/(2W²)`, and
each finite top is bounded by it — the fixed tail contribution to `TO`/`TE` and to the budgets. -/

/-- **Power-tail integral bound.**  For `0 ≤ K`, `0 < W ≤ b`, `∫_W^b K/x³ ≤ K/(2W²)`
(antiderivative `−K/(2x²)`; the missing `−K/(2b²)` term is nonnegative). -/
theorem tail_integral_le {K W b : ℝ} (hK : 0 ≤ K) (hW : 0 < W) (hb : W ≤ b) :
    (∫ x in W..b, K / x ^ 3) ≤ K / (2 * W ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc W b, HasDerivAt (fun y => -(K / 2) / y ^ 2) (K / x ^ 3) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hW hx.1
    have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h := (hasDerivAt_const x (-(K / 2))).div hden (by positivity)
    have heq : (0 * x ^ 2 - -(K / 2) * (2 * x)) / (x ^ 2) ^ 2 = K / x ^ 3 := by
      have hxne : x ≠ 0 := hx0.ne'
      field_simp
      ring
    rw [heq] at h
    exact h
  have hcont : IntervalIntegrable (fun x => K / x ^ 3) volume W b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    have : (0 : ℝ) < x := lt_of_lt_of_le hW hx.1
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hW hb
  have e1 : -(K / 2) / b ^ 2 = -(K / (2 * b ^ 2)) := by rw [neg_div, div_div]
  have e2 : -(K / 2) / W ^ 2 = -(K / (2 * W ^ 2)) := by rw [neg_div, div_div]
  rw [e1, e2]
  have : (0 : ℝ) ≤ K / (2 * b ^ 2) := by positivity
  linarith

end Salt.Chen
