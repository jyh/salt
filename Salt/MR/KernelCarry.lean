/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronMeanSq

/-!
# S8 MR-CORE, node A3a-R3 — the KERNEL-CARRYING mean square (the truncation unpinned)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 22–23 (Lemma 14; frozen statement transcribed in `Salt.MR.ParsevalSL`).

This file discharges the named residual `A3a-R3` recorded in `Salt.MR.Lemma14`'s truncation
page: the `Vⱼ` exit that CARRIES the Saffari–Vaughan kernel factor `min(hⱼ/x, 2/|t|)²`, so
that Lemma 14's Perron truncation is no longer pinned at one dyadic block.

## The defect it repairs (`Lemma14`'s page, restated)

`vtail_mean_sq_bound` (`Lemma14Vtail`, LANDED and untouched here) bounds the `x`-averaged mean
square of the weighted `V`-difference by `164π·∫_α^β ‖A(1+it)‖²` — **kernel-free**.  Its
Cauchy–Schwarz step `vSeg_diff_sq_le` (`‖(1/h)∫_x^{x+h}F‖² ≤ (1/h)∫_x^{x+h}‖F‖²`) uses only
`‖(1/h)·K‖ ≤ 1`, discarding the oscillation of the short-window average.  Consequently the
far blocks cost `∫‖A‖²` with no decay, the weighted-sup datum
`hMsup : ∀ T ≥ W, (W/T)·∫_{T≤|t|≤2T}‖A‖² ≤ Msup` (`W := X/h₁`) gives
`∫_{2^k W}^{2^{k+1}W}‖A‖² ≤ 2^k·Msup`, and the dyadic sum `(2^N − 1)·Msup` **diverges**:
only the block `k = 0` is affordable, whence `lemma14_contour`'s forced `Tcut = 2W`.
`dyadic_tail_proper` (`Lemma14Bridge`, LANDED) consumes `∫ ‖A‖²·(min b (2/t))²` and returns
the `N`-uniform `8·Msup/(W·Tmax)` — but nothing produced its input.  That is `A3a-R3`.

## THE DEVICE (what actually pays for the kernel)

**Absorb the kernel's `1/s` into the coefficient, and re-run the LANDED separation.**
On the critical line the sharp Perron kernel is `((x+h)^{1+it} − x^{1+it})/(1+it)`, so with
the *damped coefficient* `B(t) := A(1+it)/(1+it)` (`dampA`) and `G := tailT B α β`,

`Vⱼ(x) = I·((x+hⱼ)·G(x+hⱼ) − x·G(x))`   (`vSeg_eq_damp_endpoints`, R3-a)

— a difference of two ENDPOINT values, no Fubini, no integrability side condition.  Then
`‖(1/h₁)V₁ − (1/h₂)V₂‖² ≤ 36·(X/h₁)²·(‖G(x+h₁)‖² + ‖G(x+h₂)‖² + 2‖G(x)‖²)` pointwise, the
`x`-average of each term is a translate of `∫_X^{3X}‖G‖²`, and the LANDED tent separation
`tailT_mean_sq_bound` applies **to `G`**, giving

`(1/X)∫_X^{2X}‖(1/h₁)V₁ − (1/h₂)V₂‖² ≤ 5904π·(X/h₁)²·∫_α^β ‖A(1+it)‖²/(1+t²) dt`
                                                                (`vtail_meansq_damped`, R3-c)

and `1/(1+t²)` IS the kernel decay: `1/(1+t²) ≤ (2/|t|)²`.  The `x`-average is never
Cauchy–Schwarzed away; the `1/s` that the early CS threw out is carried on the coefficient
through the same Schur/AM–GM machinery that was already kernel-checked.

**The two arms and the glue.**  The `min` has two regimes and each is paid by a different
landed stone, against the SAME weight `k`: `|t| ≤ 2W` by the weight-1 exit (there
`1 ≤ W²·k²`), `|t| ≥ 2W` by the damped exit (there `1/(1+t²) ≤ k²`).  A segment straddling
`2W` is split and the two pieces added (`‖a+b‖² ≤ 2‖a‖²+2‖b‖²`), which is the only place the
constant doubles.  Hence the exit

`(1/X)∫_X^{2X}‖(1/h₁)V₁ − (1/h₂)V₂‖² ≤ 11808π·(X/h₁)²·∫_α^β ‖A(1+it)‖²·(min(h₁/X, 2/t))² dt`
                                                                 (`vtail_meansq_kernel`, R3-d)

for `0 < α ≤ β`, and its reflection `vtail_meansq_kernel_neg` (`β < 0`, weight
`min(h₁/X, 2/(−t))`) for Lemma 14's other half-tail.

**Why the `(X/h₁)²` is not slack.**  The *normalized* kernel `(1/h)·K(x,h,t)` is an average of
unimodular numbers, hence `≍ 1` in the mid-range, i.e. `(X/h₁)·min(h₁/X, ·)` and never
`min(h₁/X, ·)` (`uKernel_norm_le`, `uKernel_wdiff_norm_le`, R3-b).  It cancels EXACTLY against
the consumer: `dyadic_tail_proper` at `Tmax = W` returns `8·Msup/W²`.

## What lands here

* `dampA`, `dampA_normSq`, `vSeg_eq_damp_endpoints` — R3-a, the kernel-carrying form.
* `uKernel_norm_le`, `uKernel_wdiff_norm_le` — R3-b, the honest (normalized) kernel size.
* `vtail_meansq_damped` — R3-c, the far arm: `5904π·(X/h₁)²·∫‖A‖²/(1+t²)`.
* `vtail_meansq_kernel`, `vtail_meansq_kernel_neg` — R3-d, THE EXIT (both half-tails).
* `lemma14_contour_kernel` — R3-e, Lemma 14's contour assembly at `Tcut = 2^N·(X/h₁)`,
  `≤ 2000(log X)^{−2/15} + 820π·∫_{T₀≤|t|≤W}‖A‖² + 944640π·Msup`, **uniformly in `N`**.
* `lemma14_shortInterval_meansq_kernel` — R3-f, the frozen `Sⱼ` form at that truncation, with
  `Egap(N,δ) = 34560δ(π + 2log(1+2^N X/h₁))² + 1152(12h₁/(2^Nδ) + (8h₁/2^N)(1+log 3X))²`:
  **both pieces now vanish** (take `δ ≍ 2^{−N/2}`, MR's `δ ≍ √(X/Tcut)`), where at the pinned
  `Tcut = 2W` the far-band piece `4h₁(1+log 3X)` was an irreducible floor.

## Scope notes

The improper `∫^∞` limit is still not taken: everything is at finite truncation `2^N·(X/h₁)`,
uniformly in `N` — the honest form (the truncated-Perron bridge `Aperron_short_interval` is
finite-`T` too).  The frequency window in R3-d is a single segment avoiding `0`; Lemma 14's
two-sided tail is the sum of the two half-tails, which is how `lemma14_contour_kernel` uses it.
The five `Lemma14` privates (`coeff_sum_inv_le`, `norm_sum_five_sq_le`, `integral_five_add`,
`uSlab_eq_vSeg`, `vSeg_split_five`, `five_split_integral_bound`) and the `vdiffR` device are
re-derived verbatim here, per the standing precedent.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## R3-0 — the critical line's denominator -/

/-- `1 + it ≠ 0` (the critical line `Re s = 1`). -/
private lemma one_add_I_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro hc
  have hre : ((1 : ℂ) + (t : ℂ) * I).re = 1 := by simp
  rw [hc] at hre
  simp at hre

/-- `‖1 + it‖ = √(1+t²)`. -/
private lemma norm_one_add_I (t : ℝ) : ‖(1 : ℂ) + (t : ℂ) * I‖ = Real.sqrt (1 + t ^ 2) := by
  rw [show ((1 : ℂ) + (t : ℂ) * I) = (((1 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) by norm_num,
    Complex.norm_add_mul_I]
  norm_num

/-! ## R3-a — the damped coefficient and the kernel-carrying representation -/

/-- The **damped coefficient** `B(t) = A(1+it)/(1+it)`: the Perron kernel's `1/s` factor moved
onto the coefficient.  This is the whole device of `A3a-R3` — the `Vⱼ` object becomes a
DIFFERENCE OF TWO ENDPOINT VALUES of the damped tail transform (`vSeg_eq_damp_endpoints`),
and the `1/(1+t²)` that the frozen statement's `min(hⱼ/x, 2/|t|)` far arm needs is then
carried by `B` through the *landed* weight-1 separation. -/
def dampA (A : ℝ → ℂ) (t : ℝ) : ℂ := A t / ((1 : ℂ) + (t : ℂ) * I)

lemma dampA_continuous {A : ℝ → ℂ} (hA : Continuous A) : Continuous (dampA A) := by
  have hden : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) := by fun_prop
  exact hA.div hden one_add_I_ne_zero

/-- The damping is exactly the `1/(1+t²)` weight in mean square. -/
lemma dampA_normSq (A : ℝ → ℂ) (t : ℝ) : ‖dampA A t‖ ^ 2 = ‖A t‖ ^ 2 / (1 + t ^ 2) := by
  rw [dampA, norm_div, div_pow, norm_one_add_I, Real.sq_sqrt (by positivity)]

/-- **R3-a — the kernel-carrying representation.**  For `x > 0`, `h ≥ 0`,
`Vⱼ(x) = I·((x+hⱼ)·G(x+hⱼ) − x·G(x))`,  `G := tailT (dampA A) α β`.
The sharp Perron kernel `((x+h)^{1+it} − x^{1+it})/(1+it)` splits at the two endpoints once
the `1/(1+it)` is absorbed into the coefficient, and `y^{1+it} = y·y^{it}` turns each endpoint
term into `y` times the damped tail transform at `y`.  No Fubini, no integrability side
condition beyond continuity — the exchange is the *pointwise* one. -/
theorem vSeg_eq_damp_endpoints {A : ℝ → ℂ} (hA : Continuous A) {x h α β : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) :
    vSeg A x h α β
      = I * (((x + h : ℝ) : ℂ) * tailT (dampA A) α β (x + h)
          - ((x : ℝ) : ℂ) * tailT (dampA A) α β x) := by
  have hxh : (0 : ℝ) < x + h := by linarith
  have hBc : Continuous (dampA A) := dampA_continuous hA
  -- the two endpoint integrands are continuous
  have hcont : ∀ y : ℝ, 0 < y →
      Continuous (fun t : ℝ => dampA A t * ((y : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)) := by
    intro y hy
    have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hden : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) := by fun_prop
    exact hBc.mul (hden.const_cpow (Or.inl hyne))
  -- pointwise: the kernel splits once `1/s` is absorbed
  have hpt : ∀ t : ℝ, A t * uKernel x h t
      = dampA A t * ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)
        - dampA A t * ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) := by
    intro t
    have h0 : (1 : ℂ) + (t : ℂ) * I ≠ 0 := one_add_I_ne_zero t
    rw [uKernel, dampA]
    field_simp
  -- each endpoint integral is `y` times the damped tail transform at `y`
  have hend : ∀ y : ℝ, 0 < y →
      (∫ t in α..β, dampA A t * ((y : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
        = ((y : ℝ) : ℂ) * tailT (dampA A) α β y := by
    intro y hy
    have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [tailT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show (1 : ℂ) + (t : ℂ) * I = 1 + (t : ℂ) * I from rfl, Complex.cpow_add _ _ hyne,
      Complex.cpow_one]
    ring
  rw [vSeg, intervalIntegral.integral_congr (g := fun t =>
      dampA A t * ((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)
        - dampA A t * ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)) (fun t _ => hpt t),
    intervalIntegral.integral_sub ((hcont _ hxh).intervalIntegrable _ _)
      ((hcont _ hx).intervalIntegrable _ _), hend _ hxh, hend _ hx]

/-! ## R3-b — the honest size of the sharp kernel (why the exit carries `(X/h₁)²`) -/

/-- **R3-b — the Saffari–Vaughan kernel bound, sharp form.**  For `x > 0`, `h ≥ 0`,
`‖((x+h)^{1+it} − x^{1+it})/(1+it)‖ ≤ (x+h)·min(h/x, 2/√(1+t²))`.
`sharp_kernel_factor` takes out `x^{1+it}` (norm `x`), `sv_smooth_kernel_bound` at `c = 1`
bounds the remaining smoothed kernel by `(1+h/x)·min(h/x, 2/‖s‖)`, and `x·(1+h/x) = x+h`. -/
theorem uKernel_norm_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (t : ℝ) :
    ‖uKernel x h t‖ ≤ (x + h) * min (h / x) (2 / Real.sqrt (1 + t ^ 2)) := by
  have hxh : (0 : ℝ) < x + h := by linarith
  set s : ℂ := (1 : ℂ) + (t : ℂ) * I with hs
  have hfac : uKernel x h t
      = ((x : ℝ) : ℂ) ^ s * ((((1 + h / x : ℝ) : ℂ) ^ s - 1) / s) :=
    sharp_kernel_factor hx hxh s
  have hsv := sv_smooth_kernel_bound (c := 1) one_pos t (u := h / x) (by positivity)
  rw [Complex.ofReal_one, Real.rpow_one] at hsv
  have hsn : ‖s‖ = Real.sqrt (1 + t ^ 2) := by rw [hs]; exact norm_one_add_I t
  rw [hsn] at hsv
  have hxs : ‖((x : ℝ) : ℂ) ^ s‖ = x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, show s.re = 1 by rw [hs]; simp, Real.rpow_one]
  have hmin0 : (0 : ℝ) ≤ min (h / x) (2 / Real.sqrt (1 + t ^ 2)) :=
    le_min (by positivity) (by positivity)
  have hxfac : x * ((1 + h / x) * min (h / x) (2 / Real.sqrt (1 + t ^ 2)))
      = (x + h) * min (h / x) (2 / Real.sqrt (1 + t ^ 2)) := by
    field_simp
  rw [hfac, norm_mul, hxs, ← hxfac]
  exact mul_le_mul_of_nonneg_left hsv hx.le

/-- **R3-b′ — the weighted-difference kernel bound.**  For `0 < h₁ ≤ h₂ ≤ x`,
`‖(1/h₁)·K(x,h₁,t) − (1/h₂)·K(x,h₂,t)‖ ≤ 4·(x/h₁)·min(h₁/x, 2/√(1+t²))`.
This is the *honest normalized* kernel size, and it is why the `A3a-R3` exit must carry a
`(X/h₁)²`: the normalized kernel is `≍ 1` in the mid-range (each `(1/h)∫_x^{x+h}u^{it}du` is
an average of unimodular numbers), i.e. `(X/h₁)·min(h₁/X, ·)`, NOT `min(h₁/X, ·)`. -/
theorem uKernel_wdiff_norm_le {x h₁ h₂ : ℝ} (hx : 0 < x) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂)
    (hh2x : h₂ ≤ x) (t : ℝ) :
    ‖((1 / h₁ : ℝ) : ℂ) * uKernel x h₁ t - ((1 / h₂ : ℝ) : ℂ) * uKernel x h₂ t‖
      ≤ 4 * (x / h₁) * min (h₁ / x) (2 / Real.sqrt (1 + t ^ 2)) := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hc : (0 : ℝ) < 2 / Real.sqrt (1 + t ^ 2) := by positivity
  set c : ℝ := 2 / Real.sqrt (1 + t ^ 2) with hcdef
  -- `(1/h)·(x+h)·min(h/x, c) ≤ 2·(x/h₁)·min(h₁/x, c)` for `h₁ ≤ h ≤ x`
  have key : ∀ h : ℝ, 0 < h → h₁ ≤ h → h ≤ x →
      (1 / h) * ((x + h) * min (h / x) c) ≤ 2 * (x / h₁) * min (h₁ / x) c := by
    intro h hh hh1h hhx
    have hstep : (1 / h) * min (h / x) c ≤ (1 / h₁) * min (h₁ / x) c := by
      rcases le_total (h / x) c with hle | hle
      · rw [min_eq_left hle]
        have h2 : (1 / h) * (h / x) = 1 / x := by field_simp
        rw [h2]
        rcases le_total (h₁ / x) c with hle1 | hle1
        · rw [min_eq_left hle1]
          have : (1 / h₁) * (h₁ / x) = 1 / x := by field_simp
          rw [this]
        · rw [min_eq_right hle1]
          have hmono : h₁ / x ≤ h / x := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hh1h (inv_nonneg.mpr hx.le)
          have hceq : c = h₁ / x := le_antisymm hle1 (le_trans hmono hle)
          rw [hceq, show (1 : ℝ) / h₁ * (h₁ / x) = 1 / x by field_simp]
      · rw [min_eq_right hle]
        have hmin1 : min (h₁ / x) c = min (h₁ / x) c := rfl
        have hcle : c ≤ min (h₁ / x) c ∨ min (h₁ / x) c = h₁ / x := by
          rcases le_total (h₁ / x) c with h' | h'
          · exact Or.inr (min_eq_left h')
          · exact Or.inl (le_of_eq (min_eq_right h').symm)
        rcases hcle with h' | h'
        · calc (1 / h) * c ≤ (1 / h₁) * c := by
                have : (1 : ℝ) / h ≤ 1 / h₁ := by
                  apply one_div_le_one_div_of_le hh1 hh1h
                exact mul_le_mul_of_nonneg_right this hc.le
            _ ≤ (1 / h₁) * min (h₁ / x) c := mul_le_mul_of_nonneg_left h' (by positivity)
        · rw [h']
          have hh1x : h₁ / x ≤ h / x := by gcongr
          calc (1 / h) * c ≤ (1 / h) * (h / x) := mul_le_mul_of_nonneg_left hle (by positivity)
            _ = 1 / x := by field_simp
            _ = (1 / h₁) * (h₁ / x) := by field_simp
    have hxh2 : x + h ≤ 2 * x := by linarith
    have hminnn : (0 : ℝ) ≤ min (h / x) c := le_min (by positivity) hc.le
    calc (1 / h) * ((x + h) * min (h / x) c)
        = (x + h) * ((1 / h) * min (h / x) c) := by ring
      _ ≤ (2 * x) * ((1 / h₁) * min (h₁ / x) c) := by
          refine mul_le_mul hxh2 hstep (by positivity) (by linarith)
      _ = 2 * (x / h₁) * min (h₁ / x) c := by field_simp
  have hb1 := uKernel_norm_le hx hh1.le t
  have hb2 := uKernel_norm_le hx hh2.le t
  have hn1 : ‖((1 / h₁ : ℝ) : ℂ) * uKernel x h₁ t‖ = (1 / h₁) * ‖uKernel x h₁ t‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hn2 : ‖((1 / h₂ : ℝ) : ℂ) * uKernel x h₂ t‖ = (1 / h₂) * ‖uKernel x h₂ t‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have k1 := key h₁ hh1 le_rfl (le_trans hh12 hh2x)
  have k2 := key h₂ hh2 hh12 hh2x
  calc ‖((1 / h₁ : ℝ) : ℂ) * uKernel x h₁ t - ((1 / h₂ : ℝ) : ℂ) * uKernel x h₂ t‖
      ≤ ‖((1 / h₁ : ℝ) : ℂ) * uKernel x h₁ t‖ + ‖((1 / h₂ : ℝ) : ℂ) * uKernel x h₂ t‖ :=
        norm_sub_le _ _
    _ = (1 / h₁) * ‖uKernel x h₁ t‖ + (1 / h₂) * ‖uKernel x h₂ t‖ := by rw [hn1, hn2]
    _ ≤ (1 / h₁) * ((x + h₁) * min (h₁ / x) c) + (1 / h₂) * ((x + h₂) * min (h₂ / x) c) := by
        gcongr
    _ ≤ 2 * (x / h₁) * min (h₁ / x) c + 2 * (x / h₁) * min (h₁ / x) c := by linarith
    _ = 4 * (x / h₁) * min (h₁ / x) c := by ring

/-! ## R3-c — the two arms of the kernel-carrying `x`-average

The `x`-integrability device is `Lemma14`'s `vdiffR` (private there, re-derived verbatim). -/

/-- The weighted `V`-difference through the `max`-regularized tail transform — globally
continuous in `x`, equal to the honest difference for `x ≥ X` (re-derived from `Lemma14`). -/
private def vdiffR (A : ℝ → ℂ) (X h₁ h₂ α β x : ℝ) : ℂ :=
  ((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
    - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)

private lemma vdiffR_continuous {A : ℝ → ℂ} (hA : Continuous A) {X : ℝ} (hX : 0 < X)
    (h₁ h₂ α β : ℝ) : Continuous (fun x : ℝ => vdiffR A X h₁ h₂ α β x) := by
  have hFr : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  simp only [vdiffR]
  exact (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₁))).sub
    (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₂)))

private lemma vdiffR_eq {A : ℝ → ℂ} (hA : Continuous A) {X x h₁ h₂ : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh1 : 0 ≤ h₁) (hh2 : 0 ≤ h₂) {α β : ℝ} :
    vdiffR A X h₁ h₂ α β x
      = ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
  have key : ∀ h : ℝ, 0 ≤ h →
      vSeg A x h α β = I * ∫ u in x..(x + h), tailTr A α β (X / 2) u := by
    intro h hh
    rw [vSeg_eq_tailT_integral hA hx0 hh]
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith : x ≤ x + h), Set.mem_Icc] at hu
    exact (tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)).symm
  simp only [vdiffR]
  rw [key h₁ hh1, key h₂ hh2]

/-- The `x`-integrability of the squared weighted `V`-difference on a frequency segment. -/
private lemma vdiff_sq_intervalIntegrable {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (α β : ℝ) :
    IntervalIntegrable (fun x : ℝ =>
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      volume X (2 * X) := by
  have hc : Continuous (fun x : ℝ => ‖vdiffR A X h₁ h₂ α β x‖ ^ 2) :=
    ((vdiffR_continuous hA hX h₁ h₂ α β).norm).pow 2
  refine (hc.intervalIntegrable X (2 * X)).congr (fun x hx => ?_)
  rw [Set.uIoc_of_le (by linarith : X ≤ 2 * X), Set.mem_Ioc] at hx
  rw [vdiffR_eq hA hX hx.1.le hh1.le hh2.le]

/-- **R3-c, THE FAR ARM (the kernel carried).**  For `0 < h₁ ≤ h₂ ≤ X`,
`(1/X)∫_X^{2X} ‖(1/h₁)V₁ − (1/h₂)V₂‖² dx ≤ 5904π·(X/h₁)²·∫_α^β ‖A(1+it)‖²/(1+t²) dt`.

This is the whole of `A3a-R3`: the early Cauchy–Schwarz of `vSeg_diff_sq_le` is NOT run.
Instead `vSeg_eq_damp_endpoints` writes each `Vⱼ` as a difference of two ENDPOINT values of
the *damped* tail transform `G = tailT (A/(1+it))`, and the landed weight-1 separation
(`tailT_mean_sq_bound`, the tent window) is re-run on `G`.  The kernel's `1/(1+it)` therefore
survives the mean square as the `1/(1+t²)` weight — exactly the decay the frozen statement's
`min(hⱼ/x, 2/|t|)` far arm needs, and exactly what the `u`-average had destroyed. -/
theorem vtail_meansq_damped {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ α β : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 5904 * Real.pi * (X / h₁) ^ 2 * ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2) := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X
  have hX2 : X ≤ 2 * X := by linarith
  have hBc : Continuous (dampA A) := dampA_continuous hA
  have hGrc : Continuous (tailTr (dampA A) α β (X / 2)) :=
    tailTr_continuous hBc α β (by linarith)
  have hG2c : Continuous (fun u : ℝ => ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2) :=
    hGrc.norm.pow 2
  -- the pointwise endpoint bound
  have hpt : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2
        ≤ 36 * (X / h₁) ^ 2 * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
            + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2
            + 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
    intro x hx1 hx2
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx1
    have hnorm : ∀ h : ℝ, 0 < h → h ≤ X →
        ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖
          ≤ (1 / h) * ((x + h) * ‖tailTr (dampA A) α β (X / 2) (x + h)‖
              + x * ‖tailTr (dampA A) α β (X / 2) x‖) := by
      intro h hh hhX
      rw [vSeg_eq_damp_endpoints hA hx0 hh.le,
        ← tailTr_eq (dampA A) α β (by linarith : X / 2 ≤ x + h),
        ← tailTr_eq (dampA A) α β (by linarith : X / 2 ≤ x), norm_mul, norm_mul,
        Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ x + h),
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    have hb1 := hnorm h₁ hh1 hh1X
    have hb2 := hnorm h₂ hh2 hh2X
    have hinv : (1 : ℝ) / h₂ ≤ 1 / h₁ := one_div_le_one_div_of_le hh1 hh12
    have hna : (0 : ℝ) ≤ ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ := norm_nonneg _
    have hnb : (0 : ℝ) ≤ ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ := norm_nonneg _
    have hnc : (0 : ℝ) ≤ ‖tailTr (dampA A) α β (X / 2) x‖ := norm_nonneg _
    have hs1 : (1 / h₁) * ((x + h₁) * ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
          + x * ‖tailTr (dampA A) α β (X / 2) x‖)
        ≤ (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖) := by
      rw [show (3 : ℝ) * X / h₁ = (1 / h₁) * (3 * X) by ring, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    have hs2 : (1 / h₂) * ((x + h₂) * ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
          + x * ‖tailTr (dampA A) α β (X / 2) x‖)
        ≤ (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖) := by
      have hstep : (1 / h₂) * ((x + h₂) * ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
            + x * ‖tailTr (dampA A) α β (X / 2) x‖)
          ≤ (1 / h₂) * (3 * X * (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
              + ‖tailTr (dampA A) α β (X / 2) x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith
      refine hstep.trans ?_
      have h3 : (1 / h₂) * (3 * X * (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖))
          ≤ (1 / h₁) * (3 * X * (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      refine h3.trans (le_of_eq ?_)
      ring
    have htot : ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β
          - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖
        ≤ (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
            + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
            + 2 * ‖tailTr (dampA A) α β (X / 2) x‖) := by
      refine (norm_sub_le _ _).trans ?_
      have := add_le_add (hb1.trans hs1) (hb2.trans hs2)
      calc ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β‖
              + ‖((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖
          ≤ (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
              + ‖tailTr (dampA A) α β (X / 2) x‖)
            + (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
              + ‖tailTr (dampA A) α β (X / 2) x‖) := this
        _ = (3 * X / h₁) * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
              + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
              + 2 * ‖tailTr (dampA A) α β (X / 2) x‖) := by ring
    have hWnn : (0 : ℝ) ≤ 3 * X / h₁ := by positivity
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htot 2
    have hW2 : (3 * X / h₁) ^ 2 = 9 * (X / h₁) ^ 2 := by field_simp; ring
    rw [mul_pow, hW2] at hsq
    refine hsq.trans ?_
    have hquad : (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
          + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
          + 2 * ‖tailTr (dampA A) α β (X / 2) x‖) ^ 2
        ≤ 4 * (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
          + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2
          + 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
          - ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖),
        sq_nonneg (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖
          - ‖tailTr (dampA A) α β (X / 2) x‖),
        sq_nonneg (‖tailTr (dampA A) α β (X / 2) (x + h₂)‖
          - ‖tailTr (dampA A) α β (X / 2) x‖)]
    nlinarith [sq_nonneg (X / h₁), hquad]
  -- integrate the pointwise bound
  have hmajc : Continuous (fun x : ℝ => 36 * (X / h₁) ^ 2 *
      (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
        + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2
        + 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2)) := by
    have c1 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    have c2 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    exact continuous_const.mul ((c1.add c2).add (continuous_const.mul hG2c))
  have hmono : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ ∫ x in X..(2 * X), 36 * (X / h₁) ^ 2 *
          (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
            + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2
            + 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) :=
    intervalIntegral.integral_mono_on hX2 (vdiff_sq_intervalIntegrable hA hX hh1 hh2 α β)
      (hmajc.intervalIntegrable _ _)
      (fun x hx => hpt x (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  -- the three shifted window integrals
  have hshift : ∀ c : ℝ, 0 ≤ c → c ≤ X →
      (∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) (x + c)‖ ^ 2)
        ≤ ∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2 := by
    intro c hc0 hcX
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2) c]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun u => by positivity))
      (hG2c.intervalIntegrable _ _)
  have hbase : (∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2)
      ≤ ∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hX2 (by linarith)
      (Filter.Eventually.of_forall (fun u => by positivity)) (hG2c.intervalIntegrable _ _)
  have hsplit : (∫ x in X..(2 * X), 36 * (X / h₁) ^ 2 *
        (‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
          + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2
          + 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2))
      = 36 * (X / h₁) ^ 2 * ((∫ x in X..(2 * X),
            ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2)
          + (∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2)
          + 2 * ∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
    have c1 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    have c2 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    have i1 : IntervalIntegrable (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2)
        volume X (2 * X) := c1.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2)
        volume X (2 * X) := c2.intervalIntegrable _ _
    have i12 : IntervalIntegrable (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h₁)‖ ^ 2
        + ‖tailTr (dampA A) α β (X / 2) (x + h₂)‖ ^ 2) volume X (2 * X) := i1.add i2
    have i3 : IntervalIntegrable (fun x : ℝ => 2 * ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2)
        volume X (2 * X) := (hG2c.const_mul 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i12 i3,
      intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul]
  -- the landed separation, on the damped transform
  have hsep : (∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2)
      ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2) := by
    have hc : (∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2)
        = ∫ u in X..(3 * X), ‖tailT (dampA A) α β u‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 3 * X), Set.mem_Icc] at hu
      rw [tailTr_eq (dampA A) α β (by linarith [hu.1] : X / 2 ≤ u)]
    have hJ : (∫ t in α..β, ‖dampA A t‖ ^ 2) = ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2) :=
      intervalIntegral.integral_congr (fun t _ => dampA_normSq A t)
    rw [hc, ← hJ]
    exact tailT_mean_sq_bound hBc hX hab
  -- assemble
  have hJnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2) :=
    intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
  have hchain : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 36 * (X / h₁) ^ 2 * (4 * (41 * X * Real.pi
          * ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2))) := by
    refine hmono.trans (le_of_eq hsplit |>.trans ?_)
    have h1 := hshift h₁ hh1.le hh1X
    have h2 := hshift h₂ hh2.le hh2X
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hsep]
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  refine (mul_le_mul_of_nonneg_left hchain hXinv.le).trans (le_of_eq ?_)
  field_simp
  ring

/-! ## R3-d — the exit: both arms against ONE kernel weight -/

/-- Adjacent frequency segments add (re-derived from `Lemma14`). -/
private lemma vSeg_add_adj {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (p q r : ℝ) :
    vSeg A x h p q + vSeg A x h q r = vSeg A x h p r := by
  have hc : Continuous (fun t : ℝ => A t * uKernel x h t) :=
    hA.mul (uKernel_continuous hx hxh)
  rw [vSeg, vSeg, vSeg, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]

/-- **The per-segment arm.**  On a frequency segment carrying EITHER certificate — the mid-range
one `1 ≤ (X/h₁)²·k(t)²` (paid by the landed weight-1 separation) or the far one
`1/(1+t²) ≤ k(t)²` (paid by `vtail_meansq_damped`) — the `x`-averaged mean square is
`≤ 5904π·(X/h₁)²·∫ ‖A‖²·k²`.  The two arms are stated against the SAME weight `k`, which is
what lets the caller glue two adjacent segments into one `min`-kernel integral. -/
private lemma vtail_meansq_arm {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ p q : ℝ} {k : ℝ → ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X) (hpq : p ≤ q)
    (hkc : ContinuousOn k (Set.uIcc p q))
    (harm : (∀ t ∈ Set.Icc p q, 1 ≤ (X / h₁) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2)) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ p q - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ p q‖ ^ 2)
      ≤ 5904 * Real.pi * (X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X
  have hKi : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 * k t ^ 2) volume p q :=
    ((hA.norm.pow 2).continuousOn.mul (hkc.pow 2)).intervalIntegrable
  have hKnn : (0 : ℝ) ≤ ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
    intervalIntegral.integral_nonneg hpq (fun t _ => by positivity)
  have hpk : (0 : ℝ) ≤ Real.pi * ((X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2) := by
    have : (0 : ℝ) ≤ (X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
      mul_nonneg (sq_nonneg _) hKnn
    nlinarith [Real.pi_pos]
  rcases harm with hlow | hhigh
  · have h1 := vtail_mean_sq_bound hA hX hh1 hh2 hh1X hh2X hpq
    have h2 : (∫ t in p..q, ‖A t‖ ^ 2)
        ≤ (X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hpq ((hA.norm.pow 2).intervalIntegrable _ _)
        (hKi.const_mul _) (fun t ht => ?_)
      nlinarith [hlow t ht, sq_nonneg ‖A t‖]
    have h3 : 164 * Real.pi * (∫ t in p..q, ‖A t‖ ^ 2)
        ≤ 164 * Real.pi * ((X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3, hpk]
  · have h1 := vtail_meansq_damped hA hX hh1 hh12 hh2X hpq
    have hDi : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 / (1 + t ^ 2)) volume p q := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact (hA.norm.pow 2).div (by fun_prop) (fun t => by positivity)
    have h2 : (∫ t in p..q, ‖A t‖ ^ 2 / (1 + t ^ 2))
        ≤ ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
      refine intervalIntegral.integral_mono_on hpq hDi hKi (fun t ht => ?_)
      have hd : ‖A t‖ ^ 2 / (1 + t ^ 2) = ‖A t‖ ^ 2 * (1 / (1 + t ^ 2)) := by ring
      rw [hd]
      exact mul_le_mul_of_nonneg_left (hhigh t ht) (sq_nonneg _)
    have h3 : 5904 * Real.pi * (X / h₁) ^ 2 * (∫ t in p..q, ‖A t‖ ^ 2 / (1 + t ^ 2))
        ≤ 5904 * Real.pi * (X / h₁) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3]

/-- **The glue.**  Two adjacent segments, each carrying either arm's certificate, compose into
a single `x`-averaged bound with twice the constant (`‖a+b‖² ≤ 2‖a‖² + 2‖b‖²`). -/
private lemma vtail_meansq_glue {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ α m β : ℝ}
    {k : ℝ → ℝ} (hX : 0 < X) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X)
    (hαm : α ≤ m) (hmβ : m ≤ β) (hkc : ContinuousOn k (Set.uIcc α β))
    (harm1 : (∀ t ∈ Set.Icc α m, 1 ≤ (X / h₁) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc α m, 1 / (1 + t ^ 2) ≤ k t ^ 2))
    (harm2 : (∀ t ∈ Set.Icc m β, 1 ≤ (X / h₁) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc m β, 1 / (1 + t ^ 2) ≤ k t ^ 2)) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 11808 * Real.pi * (X / h₁) ^ 2 * ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hab : α ≤ β := le_trans hαm hmβ
  have hX2 : X ≤ 2 * X := by linarith
  have hsub1 : Set.uIcc α m ⊆ Set.uIcc α β := by
    rw [Set.uIcc_of_le hαm, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl hmβ
  have hsub2 : Set.uIcc m β ⊆ Set.uIcc α β := by
    rw [Set.uIcc_of_le hmβ, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc hαm le_rfl
  have hKi1 : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 * k t ^ 2) volume α m :=
    ((hA.norm.pow 2).continuousOn.mul ((hkc.mono hsub1).pow 2)).intervalIntegrable
  have hKi2 : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 * k t ^ 2) volume m β :=
    ((hA.norm.pow 2).continuousOn.mul ((hkc.mono hsub2).pow 2)).intervalIntegrable
  have hKadd : (∫ t in α..m, ‖A t‖ ^ 2 * k t ^ 2) + (∫ t in m..β, ‖A t‖ ^ 2 * k t ^ 2)
      = ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals hKi1 hKi2
  -- the pointwise segment split
  have hadd : ∀ x : ℝ, 0 < x →
      ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β
        = (((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α m - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α m)
          + (((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ m β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ m β) := by
    intro x hx0
    rw [← vSeg_add_adj hA hx0 (by linarith : (0 : ℝ) < x + h₁) α m β,
      ← vSeg_add_adj hA hx0 (by linarith : (0 : ℝ) < x + h₂) α m β]
    ring
  have hpt : ∀ x : ℝ, X ≤ x →
      ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2
        ≤ 2 * ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α m
              - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α m‖ ^ 2
          + 2 * ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ m β
              - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ m β‖ ^ 2 := by
    intro x hx
    rw [hadd x (lt_of_lt_of_le hX hx)]
    set u : ℂ := ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α m
      - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α m with hu
    set v : ℂ := ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ m β
      - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ m β with hv
    nlinarith [pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2,
      sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]
  have hI1 := vdiff_sq_intervalIntegrable hA hX hh1 hh2 α m
  have hI2 := vdiff_sq_intervalIntegrable hA hX hh1 hh2 m β
  have hI := vdiff_sq_intervalIntegrable hA hX hh1 hh2 α β
  have hmono : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 2 * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α m
            - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α m‖ ^ 2)
        + 2 * ∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ m β
            - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ m β‖ ^ 2 := by
    have hstep := intervalIntegral.integral_mono_on hX2 hI
      ((hI1.const_mul 2).add (hI2.const_mul 2))
      (fun x hx => hpt x (Set.mem_Icc.mp hx).1)
    rwa [intervalIntegral.integral_add (hI1.const_mul 2) (hI2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono hXinv.le
  have hb1 := vtail_meansq_arm hA hX hh1 hh12 hh2X hαm (hkc.mono hsub1) harm1
  have hb2 := vtail_meansq_arm hA hX hh1 hh12 hh2X hmβ (hkc.mono hsub2) harm2
  rw [← hKadd]
  linarith [hmul, hb1, hb2]

/-- **R3-d — THE EXIT (`vtail_meansq_kernel`).**  For `0 < h₁ ≤ h₂ ≤ X` and a POSITIVE
frequency segment `0 < α ≤ β`,

`(1/X)·∫_X^{2X} ‖(1/h₁)V₁(x) − (1/h₂)V₂(x)‖² dx`
`   ≤ 11808π·(X/h₁)²·∫_α^β ‖A(1+it)‖²·(min(h₁/X, 2/t))² dt`.

This is the kernel-carrying separation the frozen Lemma 14 needs: the integrand now carries the
Saffari–Vaughan factor `min(b, 2/t)²` (`b = h₁/X`), which is exactly what `dyadic_tail_proper`
consumes, so the Perron truncation is no longer pinned at one dyadic block.

The `(X/h₁)²` is NOT slack: the *normalized* kernel `(1/h)·((x+h)^{1+it} − x^{1+it})/(1+it)`
is an average of unimodular numbers, hence `≍ 1 = (X/h₁)·b` in the mid-range
(`uKernel_wdiff_norm_le`), so `(X/h₁)²·min(b, 2/t)²` — not `min(b, 2/t)²` — is the true size.
With `Tmax = W = X/h₁` the consumer's `8·Msup/(W·Tmax) = 8·Msup/W²` cancels it exactly. -/
theorem vtail_meansq_kernel {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ α β : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X) (hα : 0 < α) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 11808 * Real.pi * (X / h₁) ^ 2
          * ∫ t in α..β, ‖A t‖ ^ 2 * (min (h₁ / X) (2 / t)) ^ 2 := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X
  have hW : (0 : ℝ) < X / h₁ := div_pos hX hh1
  have hb : (0 : ℝ) < h₁ / X := div_pos hh1 hX
  have hbW : (h₁ / X) * (X / h₁) = 1 := by field_simp
  set k : ℝ → ℝ := fun t => min (h₁ / X) (2 / t) with hk
  have hknn : ∀ t : ℝ, 0 < t → 0 ≤ k t := fun t ht => le_min hb.le (by positivity)
  -- the mid-range certificate on a segment with `t ≤ 2·(X/h₁)`
  have hcert_low : ∀ p q : ℝ, 0 < p → (∀ t ∈ Set.Icc p q, t ≤ 2 * (X / h₁)) →
      ∀ t ∈ Set.Icc p q, 1 ≤ (X / h₁) ^ 2 * k t ^ 2 := by
    intro p q hp hle t ht
    have ht0 : 0 < t := lt_of_lt_of_le hp (Set.mem_Icc.mp ht).1
    have hbt : h₁ / X ≤ 2 / t := by
      rw [div_le_div_iff₀ hX ht0]
      calc h₁ * t ≤ h₁ * (2 * (X / h₁)) :=
            mul_le_mul_of_nonneg_left (hle t ht) hh1.le
        _ = 2 * X := by field_simp
    have hkt : k t = h₁ / X := by rw [hk]; exact min_eq_left hbt
    rw [hkt, ← mul_pow, mul_comm (X / h₁) (h₁ / X), hbW, one_pow]
  -- the far certificate on a segment with `t ≥ 2·(X/h₁)`
  have hcert_high : ∀ p q : ℝ, (∀ t ∈ Set.Icc p q, 2 * (X / h₁) ≤ t) →
      ∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2 := by
    intro p q hge t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) (hge t ht)
    have h2t : 2 / t ≤ h₁ / X := by
      rw [div_le_div_iff₀ ht0 hX]
      calc 2 * X = h₁ * (2 * (X / h₁)) := by field_simp
        _ ≤ h₁ * t := mul_le_mul_of_nonneg_left (hge t ht) hh1.le
    have hkt : k t = 2 / t := by rw [hk]; exact min_eq_right h2t
    rw [hkt]
    have hexp : (2 / t) ^ 2 = 4 / t ^ 2 := by
      rw [div_pow]; norm_num
    rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t]
  have hkc : ∀ p q : ℝ, 0 < p → p ≤ q → ContinuousOn k (Set.uIcc p q) := by
    intro p q hp hpq
    have hne : ∀ t ∈ Set.uIcc p q, t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hpq, Set.mem_Icc] at ht
      exact (lt_of_lt_of_le hp ht.1).ne'
    exact continuousOn_const.inf (continuousOn_const.div continuousOn_id hne)
  rcases le_or_gt β (2 * (X / h₁)) with hlow | hlow
  · refine le_trans (vtail_meansq_arm hA hX hh1 hh12 hh2X hab (hkc α β hα hab)
      (Or.inl (hcert_low α β hα (fun t ht => le_trans (Set.mem_Icc.mp ht).2 hlow)))) ?_
    have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
    nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h₁),
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h₁))) hKnn]
  · rcases le_or_gt (2 * (X / h₁)) α with hhigh | hhigh
    · refine le_trans (vtail_meansq_arm hA hX hh1 hh12 hh2X hab (hkc α β hα hab)
        (Or.inr (hcert_high α β (fun t ht => le_trans hhigh (Set.mem_Icc.mp ht).1)))) ?_
      have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
      nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h₁),
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h₁))) hKnn]
    · exact vtail_meansq_glue hA hX hh1 hh12 hh2X hhigh.le hlow.le (hkc α β hα hab)
        (Or.inl (hcert_low α (2 * (X / h₁)) hα (fun t ht => (Set.mem_Icc.mp ht).2)))
        (Or.inr (hcert_high (2 * (X / h₁)) β (fun t ht => (Set.mem_Icc.mp ht).1)))

/-- **R3-d′ — THE EXIT on a NEGATIVE frequency segment** (`β < 0`), with the reflected kernel
weight `min(h₁/X, 2/(−t))`.  Lemma 14's tail is two-sided; the consumer applies this arm to
`[−2^N·W, −W]` and then reflects the frequency variable to feed `dyadic_tail_proper`
(which is stated for `t > 0`). -/
theorem vtail_meansq_kernel_neg {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ α β : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh12 : h₁ ≤ h₂) (hh2X : h₂ ≤ X) (hβ : β < 0) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 11808 * Real.pi * (X / h₁) ^ 2
          * ∫ t in α..β, ‖A t‖ ^ 2 * (min (h₁ / X) (2 / (-t))) ^ 2 := by
  have hh2 : (0 : ℝ) < h₂ := lt_of_lt_of_le hh1 hh12
  have hW : (0 : ℝ) < X / h₁ := div_pos hX hh1
  have hb : (0 : ℝ) < h₁ / X := div_pos hh1 hX
  have hbW : (h₁ / X) * (X / h₁) = 1 := by field_simp
  set k : ℝ → ℝ := fun t => min (h₁ / X) (2 / (-t)) with hk
  have hcert_low : ∀ p q : ℝ, q < 0 → (∀ t ∈ Set.Icc p q, -(2 * (X / h₁)) ≤ t) →
      ∀ t ∈ Set.Icc p q, 1 ≤ (X / h₁) ^ 2 * k t ^ 2 := by
    intro p q hq hle t ht
    have ht0 : 0 < -t := by linarith [(Set.mem_Icc.mp ht).2]
    have hbt : h₁ / X ≤ 2 / (-t) := by
      rw [div_le_div_iff₀ hX ht0]
      calc h₁ * -t ≤ h₁ * (2 * (X / h₁)) :=
            mul_le_mul_of_nonneg_left (by linarith [hle t ht]) hh1.le
        _ = 2 * X := by field_simp
    have hkt : k t = h₁ / X := by rw [hk]; exact min_eq_left hbt
    rw [hkt, ← mul_pow, mul_comm (X / h₁) (h₁ / X), hbW, one_pow]
  have hcert_high : ∀ p q : ℝ, q < 0 → (∀ t ∈ Set.Icc p q, t ≤ -(2 * (X / h₁))) →
      ∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2 := by
    intro p q hq hge t ht
    have ht0 : 0 < -t := by linarith [(Set.mem_Icc.mp ht).2]
    have h2t : 2 / (-t) ≤ h₁ / X := by
      rw [div_le_div_iff₀ ht0 hX]
      calc 2 * X = h₁ * (2 * (X / h₁)) := by field_simp
        _ ≤ h₁ * -t := mul_le_mul_of_nonneg_left (by linarith [hge t ht]) hh1.le
    have hkt : k t = 2 / (-t) := by rw [hk]; exact min_eq_right h2t
    rw [hkt]
    have ht2 : (0 : ℝ) < t ^ 2 := by nlinarith
    have hexp : (2 / (-t)) ^ 2 = 4 / t ^ 2 := by
      rw [div_pow, neg_pow]; norm_num
    rw [hexp, div_le_div_iff₀ (by positivity) ht2]
    nlinarith [sq_nonneg t]
  have hkc : ∀ p q : ℝ, q < 0 → p ≤ q → ContinuousOn k (Set.uIcc p q) := by
    intro p q hq hpq
    have hne : ∀ t ∈ Set.uIcc p q, -t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hpq, Set.mem_Icc] at ht
      have : t < 0 := lt_of_le_of_lt ht.2 hq
      linarith
    exact continuousOn_const.inf
      (continuousOn_const.div continuousOn_id.neg hne)
  rcases le_or_gt (-(2 * (X / h₁))) α with hlow | hlow
  · refine le_trans (vtail_meansq_arm hA hX hh1 hh12 hh2X hab (hkc α β hβ hab)
      (Or.inl (hcert_low α β hβ (fun t ht => le_trans hlow (Set.mem_Icc.mp ht).1)))) ?_
    simp only [hk]
    have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * (min (h₁ / X) (2 / (-t))) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
    nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h₁),
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h₁))) hKnn]
  · rcases le_or_gt β (-(2 * (X / h₁))) with hhigh | hhigh
    · refine le_trans (vtail_meansq_arm hA hX hh1 hh12 hh2X hab (hkc α β hβ hab)
        (Or.inr (hcert_high α β hβ (fun t ht => le_trans (Set.mem_Icc.mp ht).2 hhigh)))) ?_
      simp only [hk]
      have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * (min (h₁ / X) (2 / (-t))) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
      nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h₁),
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h₁))) hKnn]
    · refine vtail_meansq_glue hA hX hh1 hh12 hh2X hlow.le hhigh.le (hkc α β hβ hab)
        (Or.inr (hcert_high α (-(2 * (X / h₁))) (by linarith)
          (fun t ht => (Set.mem_Icc.mp ht).2)))
        (Or.inl (hcert_low (-(2 * (X / h₁))) β hβ (fun t ht => (Set.mem_Icc.mp ht).1)))

/-! ## R3-e — the consumption: Lemma 14's contour at `Tcut = 2^N·(X/h₁)`, UNIFORMLY in `N`

The five `Lemma14` privates below are re-derived verbatim (they are `private` there). -/

/-- The coefficient mass of an `[X, 4X]`-supported index set: `∑_{m ∈ s0} 1/m ≤ 5`. -/
private lemma coeff_sum_inv_le {X : ℝ} (hX : 1 ≤ X) (s0 : Finset ℕ)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    (∑ m ∈ s0, 1 / (m : ℝ)) ≤ 5 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hsub : s0 ⊆ Finset.Icc 0 ⌊4 * X⌋₊ := by
    intro m hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.le_floor (hrange m hm).2⟩
  have hcard : (s0.card : ℝ) ≤ 4 * X + 1 := by
    have h1 : s0.card ≤ ⌊4 * X⌋₊ + 1 := by
      have h2 := Finset.card_le_card hsub
      rwa [Nat.card_Icc, Nat.sub_zero] at h2
    have h3 : ((⌊4 * X⌋₊ : ℕ) : ℝ) ≤ 4 * X := Nat.floor_le (by linarith)
    have h4 : (s0.card : ℝ) ≤ ((⌊4 * X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_one] at h4
    linarith
  calc (∑ m ∈ s0, 1 / (m : ℝ)) ≤ ∑ _m ∈ s0, 1 / X :=
        Finset.sum_le_sum fun m hm => one_div_le_one_div_of_le hX0 (hrange m hm).1
    _ = s0.card * (1 / X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * X + 1) * (1 / X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 5 := by rw [mul_one_div, div_le_iff₀ hX0]; linarith

/-- `‖z₁+z₂+z₃+z₄+z₅‖² ≤ 5·(‖z₁‖²+⋯+‖z₅‖²)`. -/
private lemma norm_sum_five_sq_le (z₁ z₂ z₃ z₄ z₅ : ℂ) :
    ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ^ 2
      ≤ 5 * (‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 + ‖z₃‖ ^ 2 + ‖z₄‖ ^ 2 + ‖z₅‖ ^ 2) := by
  have htri : ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ + ‖z₅‖ := by
    have t1 : ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ≤ ‖z₁ + z₂ + z₃ + z₄‖ + ‖z₅‖ := norm_add_le _ _
    have t2 : ‖z₁ + z₂ + z₃ + z₄‖ ≤ ‖z₁ + z₂ + z₃‖ + ‖z₄‖ := norm_add_le _ _
    have t3 : ‖z₁ + z₂ + z₃‖ ≤ ‖z₁ + z₂‖ + ‖z₃‖ := norm_add_le _ _
    have t4 : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    linarith
  refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
  nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖), sq_nonneg (‖z₁‖ - ‖z₃‖), sq_nonneg (‖z₁‖ - ‖z₄‖),
    sq_nonneg (‖z₁‖ - ‖z₅‖), sq_nonneg (‖z₂‖ - ‖z₃‖), sq_nonneg (‖z₂‖ - ‖z₄‖),
    sq_nonneg (‖z₂‖ - ‖z₅‖), sq_nonneg (‖z₃‖ - ‖z₄‖), sq_nonneg (‖z₃‖ - ‖z₅‖),
    sq_nonneg (‖z₄‖ - ‖z₅‖)]

/-- Additivity of an interval integral over a five-term sum. -/
private lemma integral_five_add {f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ} {p q : ℝ}
    (h₁ : IntervalIntegrable f₁ volume p q) (h₂ : IntervalIntegrable f₂ volume p q)
    (h₃ : IntervalIntegrable f₃ volume p q) (h₄ : IntervalIntegrable f₄ volume p q)
    (h₅ : IntervalIntegrable f₅ volume p q) :
    (∫ x in p..q, (f₁ x + f₂ x + f₃ x + f₄ x + f₅ x))
      = (∫ x in p..q, f₁ x) + (∫ x in p..q, f₂ x) + (∫ x in p..q, f₃ x)
        + (∫ x in p..q, f₄ x) + ∫ x in p..q, f₅ x := by
  rw [intervalIntegral.integral_add (((h₁.add h₂).add h₃).add h₄) h₅,
    intervalIntegral.integral_add ((h₁.add h₂).add h₃) h₄,
    intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂]

/-- The `U`-slab at truncation `T` IS the `V`-segment on `[−T, T]`. -/
private lemma uSlab_eq_vSeg (A : ℝ → ℂ) (x h T : ℝ) : uSlab A x h T = vSeg A x h (-T) T := rfl

/-- The five-way frequency split. -/
private lemma vSeg_split_five {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (T₀ W Tc : ℝ) :
    vSeg A x h (-Tc) Tc
      = vSeg A x h (-Tc) (-W) + vSeg A x h (-W) (-T₀) + vSeg A x h (-T₀) T₀
        + vSeg A x h T₀ W + vSeg A x h W Tc := by
  have e : ∀ p q r : ℝ, vSeg A x h p q + vSeg A x h q r = vSeg A x h p r :=
    fun p q r => vSeg_add_adj hA hx hxh p q r
  rw [← e (-Tc) W Tc, ← e (-Tc) T₀ W, ← e (-Tc) (-T₀) T₀, ← e (-Tc) (-W) (-T₀)]

/-- The five-way split of the `x`-integrated squared weighted Perron difference. -/
private lemma five_split_integral_bound {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (T₀ W Tc : ℝ) :
    (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc‖ ^ 2)
      ≤ 5 * ((∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-Tc) (-W) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-W) (-T₀) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-T₀) T₀ x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ T₀ W x‖ ^ 2)
          + ∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ W Tc x‖ ^ 2) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hc : ∀ α β : ℝ, Continuous (fun x : ℝ => vdiffR A X h₁ h₂ α β x) :=
    fun α β => vdiffR_continuous hA hX h₁ h₂ α β
  have hsq : ∀ α β : ℝ, Continuous (fun x : ℝ => ‖vdiffR A X h₁ h₂ α β x‖ ^ 2) :=
    fun α β => ((hc α β).norm).pow 2
  have hsplit : ∀ x : ℝ, X ≤ x →
      ((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc
        = vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
          + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
          + vdiffR A X h₁ h₂ W Tc x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
    rw [vdiffR_eq hA hX hx hh1.le hh2.le, vdiffR_eq hA hX hx hh1.le hh2.le,
      vdiffR_eq hA hX hx hh1.le hh2.le, vdiffR_eq hA hX hx hh1.le hh2.le,
      vdiffR_eq hA hX hx hh1.le hh2.le, uSlab_eq_vSeg, uSlab_eq_vSeg,
      vSeg_split_five hA hx0 (show (0 : ℝ) < x + h₁ by linarith) T₀ W Tc,
      vSeg_split_five hA hx0 (show (0 : ℝ) < x + h₂ by linarith) T₀ W Tc]
    ring
  have hcongr : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc‖ ^ 2)
      = ∫ x in X..(2 * X),
          ‖vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
            + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
            + vdiffR A X h₁ h₂ W Tc x‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hX2, Set.mem_Icc] at hx
    rw [hsplit x hx.1]
  rw [hcongr]
  have hcs : Continuous (fun x : ℝ =>
      ‖vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
        + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
        + vdiffR A X h₁ h₂ W Tc x‖ ^ 2) :=
    ((((((hc _ _).add (hc _ _)).add (hc _ _)).add (hc _ _)).add (hc _ _)).norm).pow 2
  have hcm : Continuous (fun x : ℝ =>
      5 * (‖vdiffR A X h₁ h₂ (-Tc) (-W) x‖ ^ 2 + ‖vdiffR A X h₁ h₂ (-W) (-T₀) x‖ ^ 2
        + ‖vdiffR A X h₁ h₂ (-T₀) T₀ x‖ ^ 2 + ‖vdiffR A X h₁ h₂ T₀ W x‖ ^ 2
        + ‖vdiffR A X h₁ h₂ W Tc x‖ ^ 2)) :=
    continuous_const.mul
      (((((hsq _ _).add (hsq _ _)).add (hsq _ _)).add (hsq _ _)).add (hsq _ _))
  refine le_trans (intervalIntegral.integral_mono_on hX2 (hcs.intervalIntegrable _ _)
    (hcm.intervalIntegrable _ _) (fun x _ => norm_sum_five_sq_le _ _ _ _ _)) (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact integral_five_add ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _)

/-- **R3-e — Lemma 14's contour assembly at the DYADICALLY EXTENDED truncation.**  With
`T₀ = (log X)^{1/15}`, `W = X/h₁` and `Tcut = 2^N·W` for ANY `N`,

`(1/X)∫_X^{2X} ‖(1/h₁)P₁(x) − (1/h₂)P₂(x)‖² dx`
`  ≤ 2000·(log X)^{−2/15} + 820π·∫_{T₀ ≤ |t| ≤ W} ‖A(1+it)‖² dt + 944640π·Msup`,

`Pⱼ(x) = uSlab (dpolyA a s0) x hⱼ (2^N·(X/h₁))` — **uniformly in `N`**.  This is what
`lemma14_contour` could not do: there the far blocks were paid by the kernel-free
`vtail_mean_sq_bound`, whose dyadic sum diverges like `2^N`, pinning `Tcut = 2W`
(see `Lemma14`'s truncation page).  Here the far blocks are paid by `vtail_meansq_kernel`
(`+` its reflection) and `dyadic_tail_proper`: the kernel factor `min(h₁/X, 2/|t|)²` makes the
dyadic sum geometric, `8·Msup/W²`, and the exit's `(X/h₁)² = W²` cancels it exactly. -/
theorem lemma14_contour_kernel (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ h₂ Msup : ℝ} (N : ℕ)
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
      ≤ 2000 * (Real.log X) ^ (-(2 / 15 : ℝ))
        + 820 * Real.pi * ((∫ t in ((Real.log X) ^ (1 / 15 : ℝ))..(X / h₁),
              ‖dpolyA a s0 t‖ ^ 2)
            + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 15 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
        + 944640 * Real.pi * Msup := by
  -- the arithmetic environment (as in `lemma14_contour`)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hh2X' : h₂ ≤ X := by nlinarith
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X'
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hWpos : (0 : ℝ) < X / h₁ := div_pos hXpos hh1'
  have hT0pos : (0 : ℝ) < (Real.log X) ^ (1 / 15 : ℝ) := Real.rpow_pos_of_pos hLp _
  have hT0W : (Real.log X) ^ (1 / 15 : ℝ) ≤ X / h₁ := by
    have hstep1 : (Real.log X) ^ (1 / 15 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h₂ := by
      rw [le_div_iff₀ hh2']
      have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
      calc (Real.log X) ^ (1 / 5 : ℝ) * h₂
          ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) :=
            mul_le_mul_of_nonneg_left hh2X hL5
        _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
        _ = X := by rw [← Real.rpow_add hLp]; norm_num
    have hstep3 : X / h₂ ≤ X / h₁ := by gcongr
    linarith
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hTcW : X / h₁ ≤ 2 ^ N * (X / h₁) := le_mul_of_one_le_left hWpos.le h2N
  -- `Msup ≥ 0`
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hMsupW := hMsup (X / h₁) le_rfl
    rw [div_self hWpos.ne', one_mul] at hMsupW
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  -- the mid segments (the landed weight-1 separation)
  have hSC : ∀ α β : ℝ, α ≤ β →
      1 / X * (∫ x in X..(2 * X), ‖vdiffR (dpolyA a s0) X h₁ h₂ α β x‖ ^ 2)
        ≤ 164 * Real.pi * ∫ t in α..β, ‖dpolyA a s0 t‖ ^ 2 := by
    intro α β hab
    have hcongr : (∫ x in X..(2 * X), ‖vdiffR (dpolyA a s0) X h₁ h₂ α β x‖ ^ 2)
        = ∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₁ α β
              - ((1 / h₂ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₂ α β‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le]
    rw [hcongr]
    exact vtail_mean_sq_bound hAc hXpos hh1' hh2' hh1X hh2X' hab
  -- the slab (S-B, `x`-uniform)
  have hSB : 1 / X * (∫ x in X..(2 * X),
      ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 15 : ℝ)))
        ((Real.log X) ^ (1 / 15 : ℝ)) x‖ ^ 2) ≤ 400 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by
    have hs5 : (∑ m ∈ s0, 1 / (m : ℝ)) ≤ 5 := coeff_sum_inv_le (by linarith) s0 hrange
    have hs0 : (0 : ℝ) ≤ ∑ m ∈ s0, 1 / (m : ℝ) := Finset.sum_nonneg fun m _ => by positivity
    have hsq25 : (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 ≤ 25 := by nlinarith
    have hLnn : (0 : ℝ) ≤ (Real.log X) ^ (-(2 / 15 : ℝ)) := Real.rpow_nonneg hLp.le _
    have hpt : ∀ x ∈ Set.Icc X (2 * X),
        ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 15 : ℝ)))
          ((Real.log X) ^ (1 / 15 : ℝ)) x‖ ^ 2
          ≤ 400 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le, ← uSlab_eq_vSeg, ← uSlab_eq_vSeg]
      refine le_trans (uSlab_taylor_main_sq a s0 hX1 hx.1 hh1 hh12 hh2X hpos ha) ?_
      calc 16 * (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 * (Real.log X) ^ (-(2 / 15 : ℝ))
          ≤ 16 * 25 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by gcongr
        _ = 400 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by norm_num
    have hmono := intervalIntegral.integral_mono_on (by linarith : X ≤ 2 * X)
      (((vdiffR_continuous hAc hXpos h₁ h₂ _ _).norm).pow 2 |>.intervalIntegrable _ _)
      (_root_.intervalIntegrable_const (μ := volume)) hpt
    have heval : (∫ _x in X..(2 * X), (400 * (Real.log X) ^ (-(2 / 15 : ℝ))))
        = 400 * (Real.log X) ^ (-(2 / 15 : ℝ)) * X := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [heval] at hmono
    calc 1 / X * (∫ x in X..(2 * X),
          ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 15 : ℝ)))
            ((Real.log X) ^ (1 / 15 : ℝ)) x‖ ^ 2)
        ≤ 1 / X * (400 * (Real.log X) ^ (-(2 / 15 : ℝ)) * X) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 400 * (Real.log X) ^ (-(2 / 15 : ℝ)) := by field_simp
  -- the two far blocks, paid by the KERNEL exit and the dyadic tail
  have hGnn : ∀ t : ℝ, (0 : ℝ) ≤ ‖dpolyA a s0 t‖ ^ 2 := fun t => by positivity
  have hGc : Continuous (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) := hAc.norm.pow 2
  have hGnnN : ∀ t : ℝ, (0 : ℝ) ≤ ‖dpolyA a s0 (-t)‖ ^ 2 := fun t => by positivity
  have hGcN : Continuous (fun t : ℝ => ‖dpolyA a s0 (-t)‖ ^ 2) :=
    (hAc.comp continuous_neg).norm.pow 2
  have hMsupP : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * (∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup := by
    intro T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hWpos hT
    have h := hMsup T hT
    have hn : (0 : ℝ) ≤ ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    nlinarith [mul_nonneg (le_of_lt (div_pos hWpos hT0)) hn]
  have hMsupN : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * (∫ t in T..(2 * T), ‖dpolyA a s0 (-t)‖ ^ 2) ≤ Msup := by
    intro T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hWpos hT
    have hcomp : (∫ t in T..(2 * T), ‖dpolyA a s0 (-t)‖ ^ 2)
        = ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_comp_neg (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2)
    rw [hcomp]
    have h := hMsup T hT
    have hn : (0 : ℝ) ≤ ∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    nlinarith [mul_nonneg (le_of_lt (div_pos hWpos hT0)) hn]
  have hdyP := dyadic_tail_proper (G := fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) (b := h₁ / X)
    (W := X / h₁) (Msup := Msup) (Tmax := X / h₁) hWpos hWpos (by positivity) hMnn
    hGnn hGc hMsupP N
  have hdyN := dyadic_tail_proper (G := fun t : ℝ => ‖dpolyA a s0 (-t)‖ ^ 2) (b := h₁ / X)
    (W := X / h₁) (Msup := Msup) (Tmax := X / h₁) hWpos hWpos (by positivity) hMnn
    hGnnN hGcN hMsupN N
  have hWne : (X / h₁) ≠ 0 := hWpos.ne'
  have hfarP : 1 / X * (∫ x in X..(2 * X),
      ‖vdiffR (dpolyA a s0) X h₁ h₂ (X / h₁) (2 ^ N * (X / h₁)) x‖ ^ 2)
      ≤ 94464 * Real.pi * Msup := by
    have hcongr : (∫ x in X..(2 * X),
          ‖vdiffR (dpolyA a s0) X h₁ h₂ (X / h₁) (2 ^ N * (X / h₁)) x‖ ^ 2)
        = ∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₁ (X / h₁) (2 ^ N * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₂ (X / h₁)
                  (2 ^ N * (X / h₁))‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le]
    rw [hcongr]
    refine (vtail_meansq_kernel hAc hXpos hh1' hh12 hh2X' hWpos hTcW).trans ?_
    have hmul : 11808 * Real.pi * (X / h₁) ^ 2
          * (∫ t in (X / h₁)..(2 ^ N * (X / h₁)),
              ‖dpolyA a s0 t‖ ^ 2 * (min (h₁ / X) (2 / t)) ^ 2)
        ≤ 11808 * Real.pi * (X / h₁) ^ 2 * (8 * Msup / ((X / h₁) * (X / h₁))) :=
      mul_le_mul_of_nonneg_left hdyP (by positivity)
    refine hmul.trans (le_of_eq ?_)
    field_simp
    ring
  have hfarN : 1 / X * (∫ x in X..(2 * X),
      ‖vdiffR (dpolyA a s0) X h₁ h₂ (-(2 ^ N * (X / h₁))) (-(X / h₁)) x‖ ^ 2)
      ≤ 94464 * Real.pi * Msup := by
    have hcongr : (∫ x in X..(2 * X),
          ‖vdiffR (dpolyA a s0) X h₁ h₂ (-(2 ^ N * (X / h₁))) (-(X / h₁)) x‖ ^ 2)
        = ∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₁ (-(2 ^ N * (X / h₁))) (-(X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₂ (-(2 ^ N * (X / h₁)))
                  (-(X / h₁))‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le]
    rw [hcongr]
    refine (vtail_meansq_kernel_neg hAc hXpos hh1' hh12 hh2X'
      (by linarith : -(X / h₁) < 0) (by linarith : -(2 ^ N * (X / h₁)) ≤ -(X / h₁))).trans ?_
    have hconv : (∫ t in (-(2 ^ N * (X / h₁)))..(-(X / h₁)),
          ‖dpolyA a s0 t‖ ^ 2 * (min (h₁ / X) (2 / (-t))) ^ 2)
        = ∫ t in (X / h₁)..(2 ^ N * (X / h₁)),
            ‖dpolyA a s0 (-t)‖ ^ 2 * (min (h₁ / X) (2 / t)) ^ 2 := by
      rw [← intervalIntegral.integral_comp_neg
        (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2 * (min (h₁ / X) (2 / (-t))) ^ 2)]
      exact intervalIntegral.integral_congr (fun t _ => by rw [neg_neg])
    rw [hconv]
    have hmul : 11808 * Real.pi * (X / h₁) ^ 2
          * (∫ t in (X / h₁)..(2 ^ N * (X / h₁)),
              ‖dpolyA a s0 (-t)‖ ^ 2 * (min (h₁ / X) (2 / t)) ^ 2)
        ≤ 11808 * Real.pi * (X / h₁) ^ 2 * (8 * Msup / ((X / h₁) * (X / h₁))) :=
      mul_le_mul_of_nonneg_left hdyN (by positivity)
    refine hmul.trans (le_of_eq ?_)
    field_simp
    ring
  -- assemble
  have hstep := five_split_integral_bound hAc hXpos hh1' hh2'
    ((Real.log X) ^ (1 / 15 : ℝ)) (X / h₁) (2 ^ N * (X / h₁))
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / X)
  have hb2 := hSC (-(X / h₁)) (-((Real.log X) ^ (1 / 15 : ℝ))) (by linarith)
  have hb4 := hSC ((Real.log X) ^ (1 / 15 : ℝ)) (X / h₁) hT0W
  linarith [hmul, hb2, hb4, hSB, hfarP, hfarN]

/-! ## R3-f — the gap close: the `Sⱼ` mean square with a VANISHING Perron defect -/

/-- **R3-f — Lemma 14 in the frozen `Sⱼ` form at `Tcut = 2^N·(X/h₁)`.**  Every hypothesis
discharged internally (boundary guards a.e., gap majorant, integrability), for any `N` and any
bump width `0 < δ ≤ 1`:

`(1/X)∫_X^{2X} ‖(1/h₁)S₁(x) − (1/h₂)S₂(x)‖² dx`
`  ≤ (1/2π²)·[(2000 + 944640π)·((log X)^{−2/15} + ∫_{T₀≤|t|≤W}‖A‖² + Msup) + Egap(N,δ)]`,
`Egap(N,δ) = 34560·δ·(π + 2log(1 + 2^N·X/h₁))² + 1152·(12h₁/(2^N δ) + (8h₁/2^N)(1+log 3X))²`.

**THE GAP CLOSES.**  At the pinned truncation of `lemma14_shortInterval_meansq_concrete`
(`N = 1`) the far-band term is `4h₁(1 + log 3X)` — irreducible, because `Tcut` could not be
raised.  Here BOTH pieces of `Egap` tend to `0`: take e.g. `δ = 2^{−N/2}` (MR's `δ ≍ √(X/Tcut)`
up to the `h₁` scaling), giving `Egap ≪ 2^{−N/2}·(N log 2 + log(X/h₁))² + h₁²·2^{−N}`.  The
Perron truncation defect is no longer a floor — that is what the kernel bought. -/
theorem lemma14_shortInterval_meansq_kernel (a : ℕ → ℂ) (s0 : Finset ℕ)
    {X h₁ h₂ Msup δ : ℝ} (N : ℕ)
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * ((2000 + 944640 * Real.pi)
          * ((Real.log X) ^ (-(2 / 15 : ℝ))
            + ((∫ t in ((Real.log X) ^ (1 / 15 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
                + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 15 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
            + Msup)
        + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h₁))) ^ 2
          + 1152 * (12 * h₁ / (2 ^ N * δ)
              + (8 * h₁ / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2)) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX1' : (1 : ℝ) < X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1'
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2 : (1 : ℝ) ≤ h₂ := le_trans hh1 hh12
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hh2X' : h₂ ≤ X := by nlinarith
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X'
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hWpos : (0 : ℝ) < X / h₁ := div_pos hXpos hh1'
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hTpos : (0 : ℝ) < 2 ^ N * (X / h₁) := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the gap majorant and its two discharged side conditions
  have hPerron : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))),
      ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
        ≤ gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x := by
    have hguards := perron_guards_ae s0 h₁ h₂ (volume.restrict (Set.Icc X (2 * X)))
    have hmem : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))), x ∈ Set.Icc X (2 * X) :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hguards, hmem] with x hg hxmem
    obtain ⟨g0, g1, g2⟩ := hg
    rw [Set.mem_Icc] at hxmem
    exact perron_gap_le_gapMaj a s0 hX1 hh1 hh2 hTpos hδ0 hxmem.1
      (by linarith [hxmem.2]) (by linarith [hxmem.2]) ha hrange g0 g1 g2
  have hGint := gapMaj_sq_intervalIntegrable s0 hX1 hTpos hδ0 h₁ h₂ X (2 * X)
  have hGsq : 1 / X * (∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2)
      ≤ 34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h₁))) ^ 2
        + 1152 * (12 * h₁ / (2 ^ N * δ)
            + (8 * h₁ / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2 := by
    refine (gapMaj_meansq_le s0 hX1 hTpos hδ0 hδ1 hh1 hh2 hrange).trans (le_of_eq ?_)
    have hk1 : 12 * X / (2 ^ N * (X / h₁) * δ) = 12 * h₁ / (2 ^ N * δ) := by
      field_simp
    have hk2 : 8 * X / (2 ^ N * (X / h₁)) = 8 * h₁ / 2 ^ N := by
      field_simp
    rw [hk1, hk2]
  -- the pointwise transfer from the contour object to `Sⱼ`
  have hnormI : ∀ z : ℂ, ‖2 * (Real.pi : ℂ) * I * z‖ = 2 * Real.pi * ‖z‖ := by
    intro z
    have hre : 2 * (Real.pi : ℂ) * I * z = ((2 * Real.pi : ℝ) : ℂ) * (I * z) := by
      push_cast; ring
    rw [hre, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hpt : (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] fun x : ℝ => 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2) := by
    filter_upwards [hPerron] with x hgap
    have hsplit : 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
        = (((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁)))
          - (((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))
              - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
                  - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)) := by ring
    have htri : 2 * Real.pi * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖
        ≤ ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖
          + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x := by
      rw [← hnormI, hsplit]
      exact le_trans (norm_sub_le _ _) (by linarith [hgap])
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.pi
      * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖) htri 2
    rw [show (1 : ℝ) / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2)
        = (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2)
          / (2 * Real.pi ^ 2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)]
    nlinarith [hsq, hpi, sq_nonneg (‖((1 / h₁ : ℝ) : ℂ)
      * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
      - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖
      - gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x)]
  -- integrate the transfer
  have hPint : IntervalIntegrable (fun x : ℝ =>
      ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
      volume X (2 * X) :=
    vdiff_sq_intervalIntegrable hAc hXpos hh1' hh2' (-(2 ^ N * (X / h₁))) (2 ^ N * (X / h₁))
  have hRint : IntervalIntegrable (fun x : ℝ => 1 / (2 * Real.pi ^ 2)
      * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2
        + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2)) volume X (2 * X) :=
    (hPint.add hGint).const_mul _
  have hSint := shortSum_diff_sq_intervalIntegrable a s0 hh1' hh2' X (2 * X)
  have hmono := intervalIntegral.integral_mono_ae_restrict (by linarith : X ≤ 2 * X)
    hSint hRint hpt
  have heval : (∫ x in X..(2 * X), 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2))
      = 1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
        + ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hPint hGint]
  rw [heval] at hmono
  have hstep1 : 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
        + 1 / X * ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / X)
    calc 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
        ≤ 1 / X * (1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
          + ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2)) := h1
      _ = 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 ^ N * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 ^ N * (X / h₁))‖ ^ 2)
          + 1 / X * ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h₁)) δ h₁ h₂ x ^ 2) := by ring
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- the grouped kernel contour bound
  have hcont := lemma14_contour_kernel a s0 N hX hh1 hh12 hh2X ha hrange hMsup
  have hLnn : (0 : ℝ) ≤ (Real.log X) ^ (-(2 / 15 : ℝ)) := Real.rpow_nonneg hLp.le _
  have hSnn : (0 : ℝ) ≤ (∫ t in ((Real.log X) ^ (1 / 15 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
      + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 15 : ℝ))), ‖dpolyA a s0 t‖ ^ 2 := by
    have hT0W : (Real.log X) ^ (1 / 15 : ℝ) ≤ X / h₁ := by
      have hstep1 : (Real.log X) ^ (1 / 15 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h₂ := by
        rw [le_div_iff₀ hh2']
        have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
        calc (Real.log X) ^ (1 / 5 : ℝ) * h₂
            ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) :=
              mul_le_mul_of_nonneg_left hh2X hL5
          _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
          _ = X := by rw [← Real.rpow_add hLp]; norm_num
      have hstep3 : X / h₂ ≤ X / h₁ := by gcongr
      linarith
    have hn1 : (0 : ℝ) ≤ ∫ t in ((Real.log X) ^ (1 / 15 : ℝ))..(X / h₁),
        ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0W (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 15 : ℝ))),
        ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hMsupW := hMsup (X / h₁) le_rfl
    rw [div_self hWpos.ne', one_mul] at hMsupW
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  nlinarith [hcont, hGsq, hLnn, hSnn, hMnn, hpi]

end Salt.MR
