/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Eq26Compose

/-!
# S8 ladder, node A2-1 — THE SINGLE-`h` PARSEVAL

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 21–23 (Lemma 14), read against MRT p. 21's own license for the single-window form.

## What this file is, and what it is NOT

The landed Lemma-14 chain (`Lemma14Vtail` → `KernelCarry`) proves the **difference** form
`(1/X)∫_X^{2X} ‖(1/h₁)S₁(x) − (1/h₂)S₂(x)‖² dx ≤ …`, whose `|t| ≤ T₀` block is paid by a
Taylor expansion of `(x+h)ˢ − xˢ` (the `U`-slab), producing MR's `(log X)^{−14/45}` main term.
That expansion is what forces the two-scale difference: at ONE `h` the leading term survives.

**The mechanism (pinned by the S8 source scoper, freeze `s8-freeze-0727.md` row A2-1):**
drop the `U`/`V` split entirely and run the `V`-argument from `t = 0`.  The Saffari–Vaughan
kernel bound `‖K(x,h,t)‖ ≤ (x+h)·min(h/x, 2/√(1+t²))` (`uKernel_norm_le`) is valid AT `t = 0`
(the `min` is `h/x` there), the tent-window double integral and its `1/(|t₁−t₂|²+1)` kernel are
untouched, and there is **no log loss**: the `T₀`-block is simply paid as a *frequency integral*
`∫_{−T₀}^{T₀} ‖A(1+it)‖² dt` at the same log-free constant as every other mid band.  MRT p. 21:
*"no need to split the integral into two parts, and one can just work as for `V(x)` there."*

Supplying that `T₀`-band integral is node A2-3's problem, not this file's: it is left as an
explicit summand of the exit.

## The honest constants (against the landed difference form)

Every single-`h` engine here is the landed engine with the triangle inequality opened once
instead of twice.  The extraction is a **quarter**, not a half, of the difference-form constant
at each stage (`‖a − b‖² ≤ 2‖a‖² + 2‖b‖²` costs a factor 2, and the two `hⱼ` windows cost
another 2):

| engine | difference form | single `h` (here) |
|---|---|---|
| weight-1 separation | `164π` (`vtail_mean_sq_bound`) | `41π` (`vtail_single_mean_sq_bound`) |
| damped far arm | `5904π·(X/h₁)²` (`vtail_meansq_damped`) | `1476π·(X/h)²` |
| kernel exit | `11808π·(X/h₁)²` (`vtail_meansq_kernel`) | `2952π·(X/h)²` |
| far block, per side | `94464π·Msup` | `23616π·Msup` |
| assembled contour | `820π` mid, `944640π·Msup` | `205π` mid + `205π` slab, `236160π·Msup` |

The pointwise damped step is `9·(X/h)²` where the difference form carries `36·(X/h)²` — the
refuter's reading of `vtail_meansq_damped :352–355` confirmed pre-dispatch.

## The `Egap` analogue

**Unchanged in shape.**  The single-`h` Perron gap `‖(1/h)U(x) − 2πi·(1/h)S(x)‖` is majorized
by the LANDED `gapMaj s0 X T δ h h x` — the two-scale majorant instantiated at `h₁ = h₂ = h`,
which dominates the one-scale gap term-by-term (`perron_gap_single_le_gapMaj`).  Hence
`gapMaj_meansq_le` applies verbatim and the exit's defect is the same
`34560·δ·(π + 2log(1+2^N·X/h))² + 1152·(12h/(2^N δ) + (8h/2^N)(1+log 3X))²`,
which tends to `0` along `δ = 2^{−N/2}` exactly as in `lemma14_shortInterval_meansq_kernel`.

## Glyph note (freeze trap)

`T₀` here is **`(log X)^{1/45}`** (the recentring radius `seamT0`), never MRT's set `𝒯₀` and
never the contour height `(log X)²`.

## The ladder in this file

* `vtail_single_mean_sq_bound` — S-1, the weight-1 separation at one `h` (`41π`).
* `vtail_single_meansq_damped` — S-1, the damped far arm (`1476π·(X/h)²`).
* `vtail_single_meansq_kernel` / `_neg` — S-1, the kernel-carrying exits (`2952π·(X/h)²`).
* `perron_gap_single_le_gapMaj` — S-2, the single-`h` Perron gap against the landed majorant.
* `contour_single_h_kernel` — S-3, the five-way assembly at one `h`, uniform in `N`.
* `parseval_single_h` — S-4, THE EXIT, in the `lemma14_shortInterval_meansq_kernel` shape.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory Complex

/-! ## S-1a — the single-`h` object, regularized (the `x`-integrability device)

`KernelCarry`'s `vdiffR` is `private` there; its one-scale analogue is re-derived here. -/

/-- The weighted single-`h` `V`-object through the `max`-regularized tail transform — globally
continuous in `x`, equal to the honest `(1/h)·vSeg` for `x ≥ X`. -/
private noncomputable def vsingR (A : ℝ → ℂ) (X h α β x : ℝ) : ℂ :=
  ((1 / h : ℝ) : ℂ) * (I * ∫ u in x..(x + h), tailTr A α β (X / 2) u)

private lemma vsingR_continuous {A : ℝ → ℂ} (hA : Continuous A) {X : ℝ} (hX : 0 < X)
    (h α β : ℝ) : Continuous (fun x : ℝ => vsingR A X h α β x) := by
  have hFr : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  simp only [vsingR]
  exact continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h))

/-- The `V`-segment through the regularized transform, for `x ≥ X`. -/
private lemma vSeg_eq_tailTr {A : ℝ → ℂ} (hA : Continuous A) {X x h : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh : 0 ≤ h) (α β : ℝ) :
    vSeg A x h α β = I * ∫ u in x..(x + h), tailTr A α β (X / 2) u := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
  rw [vSeg_eq_tailT_integral hA hx0 hh]
  congr 1
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le (by linarith : x ≤ x + h), Set.mem_Icc] at hu
  exact (tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)).symm

private lemma vsingR_eq {A : ℝ → ℂ} (hA : Continuous A) {X x h : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh : 0 ≤ h) {α β : ℝ} :
    vsingR A X h α β x = ((1 / h : ℝ) : ℂ) * vSeg A x h α β := by
  simp only [vsingR]
  rw [vSeg_eq_tailTr hA hX hx hh α β]

/-- The `x`-integrability of the squared weighted single-`h` `V`-object. -/
private lemma vsing_sq_intervalIntegrable {A : ℝ → ℂ} (hA : Continuous A) {X h : ℝ}
    (hX : 0 < X) (hh : 0 < h) (α β : ℝ) :
    IntervalIntegrable (fun x : ℝ => ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      volume X (2 * X) := by
  have hc : Continuous (fun x : ℝ => ‖vsingR A X h α β x‖ ^ 2) :=
    ((vsingR_continuous hA hX h α β).norm).pow 2
  refine (hc.intervalIntegrable X (2 * X)).congr (fun x hx => ?_)
  rw [Set.uIoc_of_le (by linarith : X ≤ 2 * X), Set.mem_Ioc] at hx
  rw [vsingR_eq hA hX hx.1.le hh.le]

/-! ## S-1b — the weight-1 separation at ONE `h` (the `41π` engine)

The landed `vtail_mean_sq_bound` is triangle-first: it majorizes each `hⱼ` window ADDITIVELY
(`vSeg_diff_sq_le`'s inner `key`) before the two are combined.  Re-cutting the `key` half alone
gives the one-scale bound at a quarter of the constant. -/

/-- **The pointwise single-`h` Cauchy–Schwarz step.**  `‖(1/h)V(x)‖² ≤ (1/h)∫_x^{x+h}‖F‖²`,
`F` the (regularized) tail transform.  This is `vSeg_diff_sq_le`'s `key` at one window. -/
private lemma vsing_sq_le_window {A : ℝ → ℂ} (hA : Continuous A) {X x h α β : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh : 0 < h) :
    ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2
      ≤ (1 / h) * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2 := by
  have hxh : x ≤ x + h := by linarith
  have hFrc : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  have hGc : ContinuousOn (fun u : ℝ => ‖tailTr A α β (X / 2) u‖) (Set.uIcc x (x + h)) :=
    hFrc.norm.continuousOn
  have hnorm : ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖
      = (1 / h) * ‖∫ u in x..(x + h), tailTr A α β (X / 2) u‖ := by
    rw [vSeg_eq_tailTr hA hX hx hh.le α β, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
  have htri : ‖∫ u in x..(x + h), tailTr A α β (X / 2) u‖
      ≤ ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ :=
    intervalIntegral.norm_integral_le_integral_norm hxh
  have hcs := sq_intervalIntegral_le hxh hGc
  rw [hnorm, mul_pow]
  have hsq : ‖∫ u in x..(x + h), tailTr A α β (X / 2) u‖ ^ 2
      ≤ h * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2 := by
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) htri 2) ?_
    simpa using hcs
  have hinv : (0 : ℝ) < (1 / h) ^ 2 := by positivity
  calc (1 / h) ^ 2 * ‖∫ u in x..(x + h), tailTr A α β (X / 2) u‖ ^ 2
      ≤ (1 / h) ^ 2 * (h * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hinv.le
    _ = (1 / h) * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2 := by field_simp

/-- **S-1, the single-`h` weight-1 exit.**  For `0 < h ≤ X`,
`(1/X)·∫_X^{2X} ‖(1/h)V(x)‖² dx ≤ 41π·∫_α^β ‖A(1+it)‖² dt`
— a QUARTER of the landed difference form's `164π` (`vtail_mean_sq_bound`), log-free, and valid
on EVERY frequency segment including one straddling `t = 0`. -/
theorem vtail_single_mean_sq_bound {A : ℝ → ℂ} (hA : Continuous A) {X h α β : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 41 * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
  have hX2 : X ≤ 2 * X := by linarith
  have hFrc : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  have hGrc : Continuous (fun u : ℝ => ‖tailTr A α β (X / 2) u‖ ^ 2) := hFrc.norm.pow 2
  have hGrnn : ∀ u : ℝ, 0 ≤ ‖tailTr A α β (X / 2) u‖ ^ 2 := fun u => by positivity
  have hMc : Continuous (fun x : ℝ =>
      (1 / h) * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2) :=
    continuous_const.mul (continuous_window_integral hGrc h)
  have hmono : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ ∫ x in X..(2 * X), (1 / h) * ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2 :=
    intervalIntegral.integral_mono_on hX2 (vsing_sq_intervalIntegrable hA hX hh α β)
      (hMc.intervalIntegrable _ _)
      (fun x hx => vsing_sq_le_window hA hX (Set.mem_Icc.mp hx).1 hh)
  have hsep : (∫ u in X..(3 * X), ‖tailTr A α β (X / 2) u‖ ^ 2)
      ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
    have hc : (∫ u in X..(3 * X), ‖tailTr A α β (X / 2) u‖ ^ 2)
        = ∫ u in X..(3 * X), ‖tailT A α β u‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 3 * X), Set.mem_Icc] at hu
      rw [tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)]
    rw [hc]
    exact tailT_mean_sq_bound hA hX hab
  have havg := xavg_window_le hX hh hhX hGrc hGrnn
  have hchain : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by linarith
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  refine (mul_le_mul_of_nonneg_left hchain hXinv.le).trans (le_of_eq ?_)
  field_simp

/-! ## S-1c — the damped far arm at ONE `h` (the `1476π·(X/h)²` engine) -/

/-- **S-1, THE FAR ARM at one `h`.**  For `0 < h ≤ X`,
`(1/X)∫_X^{2X} ‖(1/h)V(x)‖² dx ≤ 1476π·(X/h)²·∫_α^β ‖A(1+it)‖²/(1+t²) dt`
— a QUARTER of `vtail_meansq_damped`'s `5904π`.  The pointwise endpoint step carries
`9·(X/h)²`, against the difference form's `36·(X/h)²`. -/
theorem vtail_single_meansq_damped {A : ℝ → ℂ} (hA : Continuous A) {X h α β : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 1476 * Real.pi * (X / h) ^ 2 * ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hBc : Continuous (dampA A) := dampA_continuous hA
  have hGrc : Continuous (tailTr (dampA A) α β (X / 2)) :=
    tailTr_continuous hBc α β (by linarith)
  have hG2c : Continuous (fun u : ℝ => ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2) :=
    hGrc.norm.pow 2
  -- the pointwise endpoint bound
  have hpt : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2
        ≤ 18 * (X / h) ^ 2 * (‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2
            + ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
    intro x hx1 hx2
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx1
    have hnorm : ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖
        ≤ (1 / h) * ((x + h) * ‖tailTr (dampA A) α β (X / 2) (x + h)‖
            + x * ‖tailTr (dampA A) α β (X / 2) x‖) := by
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
    have hna : (0 : ℝ) ≤ ‖tailTr (dampA A) α β (X / 2) (x + h)‖ := norm_nonneg _
    have hnc : (0 : ℝ) ≤ ‖tailTr (dampA A) α β (X / 2) x‖ := norm_nonneg _
    have hs1 : (1 / h) * ((x + h) * ‖tailTr (dampA A) α β (X / 2) (x + h)‖
          + x * ‖tailTr (dampA A) α β (X / 2) x‖)
        ≤ (3 * X / h) * (‖tailTr (dampA A) α β (X / 2) (x + h)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖) := by
      rw [show (3 : ℝ) * X / h = (1 / h) * (3 * X) by ring, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    have htot : ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖
        ≤ (3 * X / h) * (‖tailTr (dampA A) α β (X / 2) (x + h)‖
            + ‖tailTr (dampA A) α β (X / 2) x‖) := le_trans hnorm hs1
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htot 2
    have hW2 : (3 * X / h) ^ 2 = 9 * (X / h) ^ 2 := by field_simp; ring
    rw [mul_pow, hW2] at hsq
    refine hsq.trans ?_
    have hquad : (‖tailTr (dampA A) α β (X / 2) (x + h)‖
          + ‖tailTr (dampA A) α β (X / 2) x‖) ^ 2
        ≤ 2 * (‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2
          + ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖tailTr (dampA A) α β (X / 2) (x + h)‖
        - ‖tailTr (dampA A) α β (X / 2) x‖)]
    nlinarith [sq_nonneg (X / h), hquad]
  -- integrate the pointwise bound
  have hmajc : Continuous (fun x : ℝ => 18 * (X / h) ^ 2 *
      (‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2
        + ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2)) := by
    have c1 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    exact continuous_const.mul (c1.add hG2c)
  have hmono : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ ∫ x in X..(2 * X), 18 * (X / h) ^ 2 *
          (‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2
            + ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) :=
    intervalIntegral.integral_mono_on hX2 (vsing_sq_intervalIntegrable hA hX hh α β)
      (hmajc.intervalIntegrable _ _)
      (fun x hx => hpt x (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  -- the two shifted window integrals
  have hshift : (∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2)
      ≤ ∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2 := by
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2) h]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun u => by positivity))
      (hG2c.intervalIntegrable _ _)
  have hbase : (∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2)
      ≤ ∫ u in X..(3 * X), ‖tailTr (dampA A) α β (X / 2) u‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hX2 (by linarith)
      (Filter.Eventually.of_forall (fun u => by positivity)) (hG2c.intervalIntegrable _ _)
  have hsplit : (∫ x in X..(2 * X), 18 * (X / h) ^ 2 *
        (‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2
          + ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2))
      = 18 * (X / h) ^ 2 * ((∫ x in X..(2 * X),
            ‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2)
          + ∫ x in X..(2 * X), ‖tailTr (dampA A) α β (X / 2) x‖ ^ 2) := by
    have c1 : Continuous (fun x : ℝ => ‖tailTr (dampA A) α β (X / 2) (x + h)‖ ^ 2) :=
      hG2c.comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (c1.intervalIntegrable _ _)
        (hG2c.intervalIntegrable _ _)]
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
  have hchain : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 18 * (X / h) ^ 2 * (2 * (41 * X * Real.pi
          * ∫ t in α..β, ‖A t‖ ^ 2 / (1 + t ^ 2))) := by
    refine hmono.trans (le_of_eq hsplit |>.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hsep]
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  refine (mul_le_mul_of_nonneg_left hchain hXinv.le).trans (le_of_eq ?_)
  field_simp
  ring

/-! ## S-1d — the arm / glue / kernel exits at ONE `h` -/

/-- Adjacent frequency segments add (re-derived; `KernelCarry`'s copy is `private`). -/
private lemma vSeg_add_adj' {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (p q r : ℝ) :
    vSeg A x h p q + vSeg A x h q r = vSeg A x h p r := by
  have hc : Continuous (fun t : ℝ => A t * uKernel x h t) :=
    hA.mul (uKernel_continuous hx hxh)
  rw [vSeg, vSeg, vSeg, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]

/-- **The per-segment arm, single `h`.**  Either certificate — the mid-range
`1 ≤ (X/h)²·k(t)²` (paid by the weight-1 separation) or the far `1/(1+t²) ≤ k(t)²` (paid by
the damped arm) — gives `≤ 1476π·(X/h)²·∫‖A‖²k²`. -/
private lemma vtail_single_meansq_arm {A : ℝ → ℂ} (hA : Continuous A) {X h p q : ℝ}
    {k : ℝ → ℝ} (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hpq : p ≤ q)
    (hkc : ContinuousOn k (Set.uIcc p q))
    (harm : (∀ t ∈ Set.Icc p q, 1 ≤ (X / h) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2)) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h p q‖ ^ 2)
      ≤ 1476 * Real.pi * (X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
  have hKi : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 * k t ^ 2) volume p q :=
    ((hA.norm.pow 2).continuousOn.mul (hkc.pow 2)).intervalIntegrable
  have hKnn : (0 : ℝ) ≤ ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
    intervalIntegral.integral_nonneg hpq (fun t _ => by positivity)
  have hpk : (0 : ℝ) ≤ Real.pi * ((X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2) := by
    have hnn : (0 : ℝ) ≤ (X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
      mul_nonneg (sq_nonneg _) hKnn
    nlinarith [Real.pi_pos]
  rcases harm with hlow | hhigh
  · have h1 := vtail_single_mean_sq_bound hA hX hh hhX hpq
    have h2 : (∫ t in p..q, ‖A t‖ ^ 2)
        ≤ (X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hpq ((hA.norm.pow 2).intervalIntegrable _ _)
        (hKi.const_mul _) (fun t ht => ?_)
      nlinarith [hlow t ht, sq_nonneg ‖A t‖]
    have h3 : 41 * Real.pi * (∫ t in p..q, ‖A t‖ ^ 2)
        ≤ 41 * Real.pi * ((X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3, hpk]
  · have h1 := vtail_single_meansq_damped hA hX hh hhX hpq
    have hDi : IntervalIntegrable (fun t : ℝ => ‖A t‖ ^ 2 / (1 + t ^ 2)) volume p q := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact (hA.norm.pow 2).div (by fun_prop) (fun t => by positivity)
    have h2 : (∫ t in p..q, ‖A t‖ ^ 2 / (1 + t ^ 2))
        ≤ ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 := by
      refine intervalIntegral.integral_mono_on hpq hDi hKi (fun t ht => ?_)
      have hd : ‖A t‖ ^ 2 / (1 + t ^ 2) = ‖A t‖ ^ 2 * (1 / (1 + t ^ 2)) := by ring
      rw [hd]
      exact mul_le_mul_of_nonneg_left (hhigh t ht) (sq_nonneg _)
    have h3 : 1476 * Real.pi * (X / h) ^ 2 * (∫ t in p..q, ‖A t‖ ^ 2 / (1 + t ^ 2))
        ≤ 1476 * Real.pi * (X / h) ^ 2 * ∫ t in p..q, ‖A t‖ ^ 2 * k t ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3]

/-- **The glue, single `h`.**  Two adjacent segments compose at twice the constant. -/
private lemma vtail_single_meansq_glue {A : ℝ → ℂ} (hA : Continuous A) {X h α m β : ℝ}
    {k : ℝ → ℝ} (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hαm : α ≤ m) (hmβ : m ≤ β) (hkc : ContinuousOn k (Set.uIcc α β))
    (harm1 : (∀ t ∈ Set.Icc α m, 1 ≤ (X / h) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc α m, 1 / (1 + t ^ 2) ≤ k t ^ 2))
    (harm2 : (∀ t ∈ Set.Icc m β, 1 ≤ (X / h) ^ 2 * k t ^ 2)
      ∨ (∀ t ∈ Set.Icc m β, 1 / (1 + t ^ 2) ≤ k t ^ 2)) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 2952 * Real.pi * (X / h) ^ 2 * ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 := by
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
  have hadd : ∀ x : ℝ, 0 < x →
      ((1 / h : ℝ) : ℂ) * vSeg A x h α β
        = ((1 / h : ℝ) : ℂ) * vSeg A x h α m + ((1 / h : ℝ) : ℂ) * vSeg A x h m β := by
    intro x hx0
    rw [← vSeg_add_adj' hA hx0 (by linarith : (0 : ℝ) < x + h) α m β]
    ring
  have hpt : ∀ x : ℝ, X ≤ x →
      ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2
        ≤ 2 * ‖((1 / h : ℝ) : ℂ) * vSeg A x h α m‖ ^ 2
          + 2 * ‖((1 / h : ℝ) : ℂ) * vSeg A x h m β‖ ^ 2 := by
    intro x hx
    rw [hadd x (lt_of_lt_of_le hX hx)]
    set u : ℂ := ((1 / h : ℝ) : ℂ) * vSeg A x h α m with hu
    set v : ℂ := ((1 / h : ℝ) : ℂ) * vSeg A x h m β with hv
    nlinarith [pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2,
      sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]
  have hI1 := vsing_sq_intervalIntegrable hA hX hh α m
  have hI2 := vsing_sq_intervalIntegrable hA hX hh m β
  have hI := vsing_sq_intervalIntegrable hA hX hh α β
  have hmono : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 2 * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α m‖ ^ 2)
        + 2 * ∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h m β‖ ^ 2 := by
    have hstep := intervalIntegral.integral_mono_on hX2 hI
      ((hI1.const_mul 2).add (hI2.const_mul 2))
      (fun x hx => hpt x (Set.mem_Icc.mp hx).1)
    rwa [intervalIntegral.integral_add (hI1.const_mul 2) (hI2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono hXinv.le
  have hb1 := vtail_single_meansq_arm hA hX hh hhX hαm (hkc.mono hsub1) harm1
  have hb2 := vtail_single_meansq_arm hA hX hh hhX hmβ (hkc.mono hsub2) harm2
  rw [← hKadd]
  linarith [hmul, hb1, hb2]

/-- **S-1, THE KERNEL EXIT at one `h`** (positive segment `0 < α ≤ β`):
`(1/X)∫_X^{2X} ‖(1/h)V(x)‖² dx ≤ 2952π·(X/h)²·∫_α^β ‖A(1+it)‖²·(min(h/X, 2/t))² dt`
— a QUARTER of `vtail_meansq_kernel`'s `11808π`.  The kernel factor is what
`dyadic_tail_proper` consumes, so the Perron truncation is uniform in the dyadic depth. -/
theorem vtail_single_meansq_kernel {A : ℝ → ℂ} (hA : Continuous A) {X h α β : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hα : 0 < α) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 2952 * Real.pi * (X / h) ^ 2
          * ∫ t in α..β, ‖A t‖ ^ 2 * (min (h / X) (2 / t)) ^ 2 := by
  have hb : (0 : ℝ) < h / X := div_pos hh hX
  have hbW : (h / X) * (X / h) = 1 := by field_simp
  set k : ℝ → ℝ := fun t => min (h / X) (2 / t) with hk
  have hcert_low : ∀ p q : ℝ, 0 < p → (∀ t ∈ Set.Icc p q, t ≤ 2 * (X / h)) →
      ∀ t ∈ Set.Icc p q, 1 ≤ (X / h) ^ 2 * k t ^ 2 := by
    intro p q hp hle t ht
    have ht0 : 0 < t := lt_of_lt_of_le hp (Set.mem_Icc.mp ht).1
    have hbt : h / X ≤ 2 / t := by
      rw [div_le_div_iff₀ hX ht0]
      calc h * t ≤ h * (2 * (X / h)) := mul_le_mul_of_nonneg_left (hle t ht) hh.le
        _ = 2 * X := by field_simp
    have hkt : k t = h / X := by rw [hk]; exact min_eq_left hbt
    rw [hkt, ← mul_pow, mul_comm (X / h) (h / X), hbW, one_pow]
  have hcert_high : ∀ p q : ℝ, (∀ t ∈ Set.Icc p q, 2 * (X / h) ≤ t) →
      ∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2 := by
    intro p q hge t ht
    have hW : (0 : ℝ) < X / h := div_pos hX hh
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) (hge t ht)
    have h2t : 2 / t ≤ h / X := by
      rw [div_le_div_iff₀ ht0 hX]
      calc 2 * X = h * (2 * (X / h)) := by field_simp
        _ ≤ h * t := mul_le_mul_of_nonneg_left (hge t ht) hh.le
    have hkt : k t = 2 / t := by rw [hk]; exact min_eq_right h2t
    rw [hkt]
    have hexp : (2 / t) ^ 2 = 4 / t ^ 2 := by rw [div_pow]; norm_num
    rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t]
  have hkc : ∀ p q : ℝ, 0 < p → p ≤ q → ContinuousOn k (Set.uIcc p q) := by
    intro p q hp hpq
    have hne : ∀ t ∈ Set.uIcc p q, t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hpq, Set.mem_Icc] at ht
      exact (lt_of_lt_of_le hp ht.1).ne'
    exact continuousOn_const.inf (continuousOn_const.div continuousOn_id hne)
  rcases le_or_gt β (2 * (X / h)) with hlow | hlow
  · refine le_trans (vtail_single_meansq_arm hA hX hh hhX hab (hkc α β hα hab)
      (Or.inl (hcert_low α β hα (fun t ht => le_trans (Set.mem_Icc.mp ht).2 hlow)))) ?_
    have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
    nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h),
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h))) hKnn]
  · rcases le_or_gt (2 * (X / h)) α with hhigh | hhigh
    · refine le_trans (vtail_single_meansq_arm hA hX hh hhX hab (hkc α β hα hab)
        (Or.inr (hcert_high α β (fun t ht => le_trans hhigh (Set.mem_Icc.mp ht).1)))) ?_
      have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * k t ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
      nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h),
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h))) hKnn]
    · exact vtail_single_meansq_glue hA hX hh hhX hhigh.le hlow.le (hkc α β hα hab)
        (Or.inl (hcert_low α (2 * (X / h)) hα (fun t ht => (Set.mem_Icc.mp ht).2)))
        (Or.inr (hcert_high (2 * (X / h)) β (fun t ht => (Set.mem_Icc.mp ht).1)))

/-- **S-1, THE KERNEL EXIT at one `h`, NEGATIVE segment** (`β < 0`), reflected weight. -/
theorem vtail_single_meansq_kernel_neg {A : ℝ → ℂ} (hA : Continuous A) {X h α β : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) (hβ : β < 0) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2)
      ≤ 2952 * Real.pi * (X / h) ^ 2
          * ∫ t in α..β, ‖A t‖ ^ 2 * (min (h / X) (2 / (-t))) ^ 2 := by
  have hb : (0 : ℝ) < h / X := div_pos hh hX
  have hbW : (h / X) * (X / h) = 1 := by field_simp
  set k : ℝ → ℝ := fun t => min (h / X) (2 / (-t)) with hk
  have hcert_low : ∀ p q : ℝ, q < 0 → (∀ t ∈ Set.Icc p q, -(2 * (X / h)) ≤ t) →
      ∀ t ∈ Set.Icc p q, 1 ≤ (X / h) ^ 2 * k t ^ 2 := by
    intro p q hq hle t ht
    have ht0 : 0 < -t := by linarith [(Set.mem_Icc.mp ht).2]
    have hbt : h / X ≤ 2 / (-t) := by
      rw [div_le_div_iff₀ hX ht0]
      calc h * -t ≤ h * (2 * (X / h)) :=
            mul_le_mul_of_nonneg_left (by linarith [hle t ht]) hh.le
        _ = 2 * X := by field_simp
    have hkt : k t = h / X := by rw [hk]; exact min_eq_left hbt
    rw [hkt, ← mul_pow, mul_comm (X / h) (h / X), hbW, one_pow]
  have hcert_high : ∀ p q : ℝ, q < 0 → (∀ t ∈ Set.Icc p q, t ≤ -(2 * (X / h))) →
      ∀ t ∈ Set.Icc p q, 1 / (1 + t ^ 2) ≤ k t ^ 2 := by
    intro p q hq hge t ht
    have ht0 : 0 < -t := by linarith [(Set.mem_Icc.mp ht).2]
    have h2t : 2 / (-t) ≤ h / X := by
      rw [div_le_div_iff₀ ht0 hX]
      calc 2 * X = h * (2 * (X / h)) := by field_simp
        _ ≤ h * -t := mul_le_mul_of_nonneg_left (by linarith [hge t ht]) hh.le
    have hkt : k t = 2 / (-t) := by rw [hk]; exact min_eq_right h2t
    rw [hkt]
    have ht2 : (0 : ℝ) < t ^ 2 := by nlinarith
    have hexp : (2 / (-t)) ^ 2 = 4 / t ^ 2 := by rw [div_pow, neg_pow]; norm_num
    rw [hexp, div_le_div_iff₀ (by positivity) ht2]
    nlinarith [sq_nonneg t]
  have hkc : ∀ p q : ℝ, q < 0 → p ≤ q → ContinuousOn k (Set.uIcc p q) := by
    intro p q hq hpq
    have hne : ∀ t ∈ Set.uIcc p q, -t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hpq, Set.mem_Icc] at ht
      have htneg : t < 0 := lt_of_le_of_lt ht.2 hq
      linarith
    exact continuousOn_const.inf (continuousOn_const.div continuousOn_id.neg hne)
  rcases le_or_gt (-(2 * (X / h))) α with hlow | hlow
  · refine le_trans (vtail_single_meansq_arm hA hX hh hhX hab (hkc α β hβ hab)
      (Or.inl (hcert_low α β hβ (fun t ht => le_trans hlow (Set.mem_Icc.mp ht).1)))) ?_
    simp only [hk]
    have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * (min (h / X) (2 / (-t))) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
    nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h),
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h))) hKnn]
  · rcases le_or_gt β (-(2 * (X / h))) with hhigh | hhigh
    · refine le_trans (vtail_single_meansq_arm hA hX hh hhX hab (hkc α β hβ hab)
        (Or.inr (hcert_high α β hβ (fun t ht => le_trans (Set.mem_Icc.mp ht).2 hhigh)))) ?_
      simp only [hk]
      have hKnn : (0 : ℝ) ≤ ∫ t in α..β, ‖A t‖ ^ 2 * (min (h / X) (2 / (-t))) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
      nlinarith [Real.pi_pos, hKnn, sq_nonneg (X / h),
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (X / h))) hKnn]
    · refine vtail_single_meansq_glue hA hX hh hhX hlow.le hhigh.le (hkc α β hβ hab)
        (Or.inr (hcert_high α (-(2 * (X / h))) (by linarith)
          (fun t ht => (Set.mem_Icc.mp ht).2)))
        (Or.inl (hcert_low (-(2 * (X / h))) β hβ (fun t ht => (Set.mem_Icc.mp ht).1)))

/-! ## S-3 — the five-way assembly at ONE `h`

The `KernelCarry` privates are re-derived at one scale.  The `|t| ≤ T₀` block is NOT a Taylor
main term here: it is the third frequency-integral summand. -/

/-- `‖z₁+z₂+z₃+z₄+z₅‖² ≤ 5·(‖z₁‖²+⋯+‖z₅‖²)`. -/
private lemma norm_sum_five_sq_le' (z₁ z₂ z₃ z₄ z₅ : ℂ) :
    ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ^ 2
      ≤ 5 * (‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 + ‖z₃‖ ^ 2 + ‖z₄‖ ^ 2 + ‖z₅‖ ^ 2) := by
  have htri : ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ + ‖z₅‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h4 : ‖z₁ + z₂ + z₃ + z₄‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have h3 : ‖z₁ + z₂ + z₃‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ := by
        refine le_trans (norm_add_le _ _) ?_
        linarith [norm_add_le z₁ z₂]
      linarith
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  refine hsq.trans ?_
  nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖), sq_nonneg (‖z₁‖ - ‖z₃‖), sq_nonneg (‖z₁‖ - ‖z₄‖),
    sq_nonneg (‖z₁‖ - ‖z₅‖), sq_nonneg (‖z₂‖ - ‖z₃‖), sq_nonneg (‖z₂‖ - ‖z₄‖),
    sq_nonneg (‖z₂‖ - ‖z₅‖), sq_nonneg (‖z₃‖ - ‖z₄‖), sq_nonneg (‖z₃‖ - ‖z₅‖),
    sq_nonneg (‖z₄‖ - ‖z₅‖)]

/-- Additivity of an interval integral over a five-term sum. -/
private lemma integral_five_add' {f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ} {p q : ℝ}
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
private lemma uSlab_eq_vSeg' (A : ℝ → ℂ) (x h T : ℝ) : uSlab A x h T = vSeg A x h (-T) T := rfl

/-- The five-way frequency split. -/
private lemma vSeg_split_five' {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (T₀ W Tc : ℝ) :
    vSeg A x h (-Tc) Tc
      = vSeg A x h (-Tc) (-W) + vSeg A x h (-W) (-T₀) + vSeg A x h (-T₀) T₀
        + vSeg A x h T₀ W + vSeg A x h W Tc := by
  have e : ∀ p q r : ℝ, vSeg A x h p q + vSeg A x h q r = vSeg A x h p r :=
    fun p q r => vSeg_add_adj' hA hx hxh p q r
  rw [← e (-Tc) W Tc, ← e (-Tc) T₀ W, ← e (-Tc) (-T₀) T₀, ← e (-Tc) (-W) (-T₀)]

/-- The five-way split of the `x`-integrated squared weighted single-`h` Perron slab. -/
private lemma five_split_single_bound {A : ℝ → ℂ} (hA : Continuous A) {X h : ℝ}
    (hX : 0 < X) (hh : 0 < h) (T₀ W Tc : ℝ) :
    (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * uSlab A x h Tc‖ ^ 2)
      ≤ 5 * ((∫ x in X..(2 * X), ‖vsingR A X h (-Tc) (-W) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vsingR A X h (-W) (-T₀) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vsingR A X h (-T₀) T₀ x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vsingR A X h T₀ W x‖ ^ 2)
          + ∫ x in X..(2 * X), ‖vsingR A X h W Tc x‖ ^ 2) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hc : ∀ α β : ℝ, Continuous (fun x : ℝ => vsingR A X h α β x) :=
    fun α β => vsingR_continuous hA hX h α β
  have hsq : ∀ α β : ℝ, Continuous (fun x : ℝ => ‖vsingR A X h α β x‖ ^ 2) :=
    fun α β => ((hc α β).norm).pow 2
  have hsplit : ∀ x : ℝ, X ≤ x →
      ((1 / h : ℝ) : ℂ) * uSlab A x h Tc
        = vsingR A X h (-Tc) (-W) x + vsingR A X h (-W) (-T₀) x
          + vsingR A X h (-T₀) T₀ x + vsingR A X h T₀ W x + vsingR A X h W Tc x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
    rw [vsingR_eq hA hX hx hh.le, vsingR_eq hA hX hx hh.le, vsingR_eq hA hX hx hh.le,
      vsingR_eq hA hX hx hh.le, vsingR_eq hA hX hx hh.le, uSlab_eq_vSeg',
      vSeg_split_five' hA hx0 (show (0 : ℝ) < x + h by linarith) T₀ W Tc]
    ring
  have hcongr : (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * uSlab A x h Tc‖ ^ 2)
      = ∫ x in X..(2 * X),
          ‖vsingR A X h (-Tc) (-W) x + vsingR A X h (-W) (-T₀) x
            + vsingR A X h (-T₀) T₀ x + vsingR A X h T₀ W x + vsingR A X h W Tc x‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hX2, Set.mem_Icc] at hx
    rw [hsplit x hx.1]
  rw [hcongr]
  have hcs : Continuous (fun x : ℝ =>
      ‖vsingR A X h (-Tc) (-W) x + vsingR A X h (-W) (-T₀) x
        + vsingR A X h (-T₀) T₀ x + vsingR A X h T₀ W x + vsingR A X h W Tc x‖ ^ 2) :=
    ((((((hc _ _).add (hc _ _)).add (hc _ _)).add (hc _ _)).add (hc _ _)).norm).pow 2
  have hcm : Continuous (fun x : ℝ =>
      5 * (‖vsingR A X h (-Tc) (-W) x‖ ^ 2 + ‖vsingR A X h (-W) (-T₀) x‖ ^ 2
        + ‖vsingR A X h (-T₀) T₀ x‖ ^ 2 + ‖vsingR A X h T₀ W x‖ ^ 2
        + ‖vsingR A X h W Tc x‖ ^ 2)) :=
    continuous_const.mul
      (((((hsq _ _).add (hsq _ _)).add (hsq _ _)).add (hsq _ _)).add (hsq _ _))
  refine le_trans (intervalIntegral.integral_mono_on hX2 (hcs.intervalIntegrable _ _)
    (hcm.intervalIntegrable _ _) (fun x _ => norm_sum_five_sq_le' _ _ _ _ _)) (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact integral_five_add' ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _)

/-- **S-3 — the single-`h` contour assembly at the DYADICALLY EXTENDED truncation.**  With
`T₀ = (log X)^{1/45}`, `W = X/h` and `Tcut = 2^N·W`, for ANY `N`:

`(1/X)∫_X^{2X} ‖(1/h)P(x)‖² dx`
`  ≤ 205π·∫_{T₀ ≤ |t| ≤ W} ‖A(1+it)‖² dt + 205π·∫_{−T₀}^{T₀} ‖A(1+it)‖² dt + 236160π·Msup`,

`P(x) = uSlab (dpolyA a s0) x h (2^N·(X/h))` — **uniformly in `N`**, and with **NO
`(log X)^{−14/45}` term**: the `|t| ≤ T₀` block is paid as a frequency integral at the SAME
log-free constant as the two mid bands (the third summand; its supply is node A2-3's). -/
theorem contour_single_h_kernel (a : ℕ → ℂ) (s0 : Finset ℕ) {X h Msup : ℝ} (N : ℕ)
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h ≤ T →
      X / h / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
      ≤ 205 * Real.pi * ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h),
              ‖dpolyA a s0 t‖ ^ 2)
            + ∫ t in (-(X / h))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
        + 205 * Real.pi * (∫ t in (-((Real.log X) ^ (1 / 45 : ℝ)))..((Real.log X) ^ (1 / 45 : ℝ)),
              ‖dpolyA a s0 t‖ ^ 2)
        + 236160 * Real.pi * Msup := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hh' : (0 : ℝ) < h := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hhX' : h ≤ X := by nlinarith
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hWpos : (0 : ℝ) < X / h := div_pos hXpos hh'
  have hT0pos : (0 : ℝ) < (Real.log X) ^ (1 / 45 : ℝ) := Real.rpow_pos_of_pos hLp _
  have hT0W : (Real.log X) ^ (1 / 45 : ℝ) ≤ X / h := by
    have hstep1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h := by
      rw [le_div_iff₀ hh']
      have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
      calc (Real.log X) ^ (1 / 5 : ℝ) * h
          ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) :=
            mul_le_mul_of_nonneg_left hhX hL5
        _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
        _ = X := by rw [← Real.rpow_add hLp]; norm_num
    linarith
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hTcW : X / h ≤ 2 ^ N * (X / h) := le_mul_of_one_le_left hWpos.le h2N
  -- `Msup ≥ 0`
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hMsupW := hMsup (X / h) le_rfl
    rw [div_self hWpos.ne', one_mul] at hMsupW
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h)..(2 * (X / h)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h)))..(-(X / h)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  -- the `vsingR` ↔ honest-object dictionary
  have hcv : ∀ α β : ℝ, (∫ x in X..(2 * X), ‖vsingR (dpolyA a s0) X h α β x‖ ^ 2)
      = ∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * vSeg (dpolyA a s0) x h α β‖ ^ 2 := by
    intro α β
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hx
    rw [vsingR_eq hAc hXpos hx.1 hh'.le]
  -- the three weight-1 bands (the T₀-slab among them — no Taylor term)
  have hSC : ∀ α β : ℝ, α ≤ β →
      1 / X * (∫ x in X..(2 * X), ‖vsingR (dpolyA a s0) X h α β x‖ ^ 2)
        ≤ 41 * Real.pi * ∫ t in α..β, ‖dpolyA a s0 t‖ ^ 2 := by
    intro α β hab
    rw [hcv α β]
    exact vtail_single_mean_sq_bound hAc hXpos hh' hhX' hab
  -- the two far blocks, paid by the KERNEL exit and the dyadic tail
  have hGnn : ∀ t : ℝ, (0 : ℝ) ≤ ‖dpolyA a s0 t‖ ^ 2 := fun t => by positivity
  have hGc : Continuous (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) := hAc.norm.pow 2
  have hGnnN : ∀ t : ℝ, (0 : ℝ) ≤ ‖dpolyA a s0 (-t)‖ ^ 2 := fun t => by positivity
  have hGcN : Continuous (fun t : ℝ => ‖dpolyA a s0 (-t)‖ ^ 2) :=
    (hAc.comp continuous_neg).norm.pow 2
  have hMsupP : ∀ T : ℝ, X / h ≤ T →
      X / h / T * (∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup := by
    intro T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hWpos hT
    have hM := hMsup T hT
    have hn : (0 : ℝ) ≤ ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    nlinarith [mul_nonneg (le_of_lt (div_pos hWpos hT0)) hn]
  have hMsupN : ∀ T : ℝ, X / h ≤ T →
      X / h / T * (∫ t in T..(2 * T), ‖dpolyA a s0 (-t)‖ ^ 2) ≤ Msup := by
    intro T hT
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hWpos hT
    have hcomp : (∫ t in T..(2 * T), ‖dpolyA a s0 (-t)‖ ^ 2)
        = ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_comp_neg (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2)
    rw [hcomp]
    have hM := hMsup T hT
    have hn : (0 : ℝ) ≤ ∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    nlinarith [mul_nonneg (le_of_lt (div_pos hWpos hT0)) hn]
  have hdyP := dyadic_tail_proper (G := fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) (b := h / X)
    (W := X / h) (Msup := Msup) (Tmax := X / h) hWpos hWpos (by positivity) hMnn
    hGnn hGc hMsupP N
  have hdyN := dyadic_tail_proper (G := fun t : ℝ => ‖dpolyA a s0 (-t)‖ ^ 2) (b := h / X)
    (W := X / h) (Msup := Msup) (Tmax := X / h) hWpos hWpos (by positivity) hMnn
    hGnnN hGcN hMsupN N
  have hfarP : 1 / X * (∫ x in X..(2 * X),
      ‖vsingR (dpolyA a s0) X h (X / h) (2 ^ N * (X / h)) x‖ ^ 2)
      ≤ 23616 * Real.pi * Msup := by
    rw [hcv (X / h) (2 ^ N * (X / h))]
    refine (vtail_single_meansq_kernel hAc hXpos hh' hhX' hWpos hTcW).trans ?_
    have hmul : 2952 * Real.pi * (X / h) ^ 2
          * (∫ t in (X / h)..(2 ^ N * (X / h)),
              ‖dpolyA a s0 t‖ ^ 2 * (min (h / X) (2 / t)) ^ 2)
        ≤ 2952 * Real.pi * (X / h) ^ 2 * (8 * Msup / ((X / h) * (X / h))) :=
      mul_le_mul_of_nonneg_left hdyP (by positivity)
    refine hmul.trans (le_of_eq ?_)
    field_simp
    ring
  have hfarN : 1 / X * (∫ x in X..(2 * X),
      ‖vsingR (dpolyA a s0) X h (-(2 ^ N * (X / h))) (-(X / h)) x‖ ^ 2)
      ≤ 23616 * Real.pi * Msup := by
    rw [hcv (-(2 ^ N * (X / h))) (-(X / h))]
    refine (vtail_single_meansq_kernel_neg hAc hXpos hh' hhX'
      (by linarith : -(X / h) < 0) (by linarith : -(2 ^ N * (X / h)) ≤ -(X / h))).trans ?_
    have hconv : (∫ t in (-(2 ^ N * (X / h)))..(-(X / h)),
          ‖dpolyA a s0 t‖ ^ 2 * (min (h / X) (2 / (-t))) ^ 2)
        = ∫ t in (X / h)..(2 ^ N * (X / h)),
            ‖dpolyA a s0 (-t)‖ ^ 2 * (min (h / X) (2 / t)) ^ 2 := by
      rw [← intervalIntegral.integral_comp_neg
        (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2 * (min (h / X) (2 / (-t))) ^ 2)]
      exact intervalIntegral.integral_congr (fun t _ => by rw [neg_neg])
    rw [hconv]
    have hmul : 2952 * Real.pi * (X / h) ^ 2
          * (∫ t in (X / h)..(2 ^ N * (X / h)),
              ‖dpolyA a s0 (-t)‖ ^ 2 * (min (h / X) (2 / t)) ^ 2)
        ≤ 2952 * Real.pi * (X / h) ^ 2 * (8 * Msup / ((X / h) * (X / h))) :=
      mul_le_mul_of_nonneg_left hdyN (by positivity)
    refine hmul.trans (le_of_eq ?_)
    field_simp
    ring
  -- assemble
  have hstep := five_split_single_bound hAc hXpos hh'
    ((Real.log X) ^ (1 / 45 : ℝ)) (X / h) (2 ^ N * (X / h))
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / X)
  have hb2 := hSC (-(X / h)) (-((Real.log X) ^ (1 / 45 : ℝ))) (by linarith)
  have hb3 := hSC (-((Real.log X) ^ (1 / 45 : ℝ))) ((Real.log X) ^ (1 / 45 : ℝ))
    (by linarith)
  have hb4 := hSC ((Real.log X) ^ (1 / 45 : ℝ)) (X / h) hT0W
  linarith [hmul, hb2, hb3, hb4, hfarP, hfarN]

/-! ## S-2 — the single-`h` Perron gap against the LANDED majorant -/

/-- **S-2 — the single-`h` Perron gap.**  `‖(1/h)U(x) − 2πi·(1/h)S(x)‖ ≤ gapMaj s0 X T δ h h x`:
the LANDED two-scale majorant at `h₁ = h₂ = h` dominates the one-scale gap term-by-term (it
carries two bump sums where one suffices, and `24K` where `12K` suffices), so the whole
`gapMaj_meansq_le` / `gapMaj_sq_intervalIntegrable` layer applies unchanged. -/
theorem perron_gap_single_le_gapMaj (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h T δ : ℝ}
    (hX : 1 ≤ X) (hh : 1 ≤ h) (hT : 0 < T) (hδ0 : 0 < δ)
    (hx : X ≤ x) (hxh : x + h ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_h : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h T
        - 2 * (Real.pi : ℂ) * I * (((1 / h : ℝ) : ℂ) * shortSum a s0 x h)‖
      ≤ gapMaj s0 X T δ h h x := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hmain := uSlab_gap_le_minDev a s0 hX hh0 hT hx hxh ha hrange hne_x hne_h
  have hkey : ((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h T
        - 2 * (Real.pi : ℂ) * I * (((1 / h : ℝ) : ℂ) * shortSum a s0 x h)
      = ((1 / h : ℝ) : ℂ)
        * (uSlab (dpolyA a s0) x h T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h) := by
    ring
  rw [hkey, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
  have hn : (1 : ℝ) / h ≤ 1 := by rw [div_le_one hh0]; linarith
  have hstep : (1 / h) * ‖uSlab (dpolyA a s0) x h T
        - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h‖
      ≤ 1 * (6 * minDev s0 T (x + h) + 6 * minDev s0 T x) :=
    mul_le_mul hn hmain (norm_nonneg _) zero_le_one
  have s1 := minDev_shift_le s0 (x := x) (c := h) (y := x + h) rfl hX hT hδ0
    (by linarith) (by linarith) hrange
  have s2 := minDev_shift_le s0 (x := x) (c := 0) (y := x) (add_zero x).symm hX hT hδ0
    hx (by linarith) hrange
  have hB : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hb1 := bumpSum_nonneg s0 (δ := δ) (B := Real.pi + 2 * Real.log (1 + T))
    (c := h) (y := x) hB
  have hb0 := bumpSum_nonneg s0 (δ := δ) (B := Real.pi + 2 * Real.log (1 + T))
    (c := 0) (y := x) hB
  have hlog : (0 : ℝ) ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ 12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)) := by
    have hk1 : (0 : ℝ) ≤ 12 * X / (T * δ) := by positivity
    have h8 : (0 : ℝ) ≤ 8 * X / T := by positivity
    nlinarith
  rw [gapMaj]
  linarith

/-! ## S-4 — THE EXIT -/

/-- **A2-1 — THE SINGLE-`h` PARSEVAL.**  For `aₘ` supported on `[X, 4X]` with `‖aₘ‖ ≤ 1`,
`4 ≤ h ≤ X(log X)^{−1/5}`, any dyadic depth `N` and any bump width `0 < δ ≤ 1`:

`(1/X)∫_X^{2X} ‖(1/h)S(x)‖² dx`
`  ≤ (1/2π²)·[ 205π·∫_{T₀ ≤ |t| ≤ X/h} ‖A(1+it)‖² dt`
`             + 205π·∫_{−T₀}^{T₀} ‖A(1+it)‖² dt`
`             + 236160π·Msup + Egap(N,δ) ]`,

`T₀ = (log X)^{1/45}`, `Msup` any bound for the weighted far family
`(X/h)/T·∫_{T ≤ |t| ≤ 2T}‖A‖²` over `T ≥ X/h`, and
`Egap(N,δ) = 34560·δ·(π + 2log(1 + 2^N·X/h))² + 1152·(12h/(2^N δ) + (8h/2^N)(1+log 3X))²`
— the SAME defect as the landed difference form, vanishing along `δ = 2^{−N/2}`.

**No `(log X)^{−14/45}`, no log loss.**  The `U`/`V` split is dropped: the `V`-argument runs
from `t = 0`, and the `|t| ≤ T₀` block is the second summand — a frequency integral at the
same log-free constant as the mid bands.  Supplying it is node A2-3's obligation. -/
theorem parseval_single_h (a : ℕ → ℂ) (s0 : Finset ℕ) {X h Msup δ : ℝ} (N : ℕ)
    (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h ≤ T →
      X / h / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * ((205 * Real.pi
            * ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + 205 * Real.pi * (∫ t in (-((Real.log X) ^ (1 / 45 : ℝ)))..((Real.log X) ^ (1 / 45 : ℝ)),
              ‖dpolyA a s0 t‖ ^ 2)
          + 236160 * Real.pi * Msup)
        + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h))) ^ 2
          + 1152 * (12 * h / (2 ^ N * δ)
              + (8 * h / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2)) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX1' : (1 : ℝ) < X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1'
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh' : (0 : ℝ) < h := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hhX' : h ≤ X := by nlinarith
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hWpos : (0 : ℝ) < X / h := div_pos hXpos hh'
  have hTpos : (0 : ℝ) < 2 ^ N * (X / h) := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the gap majorant and its two discharged side conditions
  have hPerron : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))),
      ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))
        - 2 * (Real.pi : ℂ) * I * (((1 / h : ℝ) : ℂ) * shortSum a s0 x h)‖
        ≤ gapMaj s0 X (2 ^ N * (X / h)) δ h h x := by
    have hguards := perron_guards_ae s0 h h (volume.restrict (Set.Icc X (2 * X)))
    have hmem : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))), x ∈ Set.Icc X (2 * X) :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hguards, hmem] with x hg hxmem
    obtain ⟨g0, g1, _⟩ := hg
    rw [Set.mem_Icc] at hxmem
    exact perron_gap_single_le_gapMaj a s0 hX1 hh1 hTpos hδ0 hxmem.1
      (by linarith [hxmem.2]) ha hrange g0 g1
  have hGint := gapMaj_sq_intervalIntegrable s0 hX1 hTpos hδ0 h h X (2 * X)
  have hGsq : 1 / X * (∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2)
      ≤ 34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h))) ^ 2
        + 1152 * (12 * h / (2 ^ N * δ)
            + (8 * h / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2 := by
    refine (gapMaj_meansq_le s0 hX1 hTpos hδ0 hδ1 hh1 hh1 hrange).trans (le_of_eq ?_)
    have hk1 : 12 * X / (2 ^ N * (X / h) * δ) = 12 * h / (2 ^ N * δ) := by field_simp
    have hk2 : 8 * X / (2 ^ N * (X / h)) = 8 * h / 2 ^ N := by field_simp
    rw [hk1, hk2]
  -- the pointwise transfer from the contour object to `S`
  have hnormI : ∀ z : ℂ, ‖2 * (Real.pi : ℂ) * I * z‖ = 2 * Real.pi * ‖z‖ := by
    intro z
    have hre : 2 * (Real.pi : ℂ) * I * z = ((2 * Real.pi : ℝ) : ℂ) * (I * z) := by
      push_cast; ring
    rw [hre, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hpt : (fun x : ℝ => ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2)
      ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] fun x : ℝ => 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2) := by
    filter_upwards [hPerron] with x hgap
    have hsplit : 2 * (Real.pi : ℂ) * I * (((1 / h : ℝ) : ℂ) * shortSum a s0 x h)
        = ((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))
          - (((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))
              - 2 * (Real.pi : ℂ) * I * (((1 / h : ℝ) : ℂ) * shortSum a s0 x h)) := by
      ring
    have htri : 2 * Real.pi * ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖
        ≤ ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖
          + gapMaj s0 X (2 ^ N * (X / h)) δ h h x := by
      rw [← hnormI, hsplit]
      exact le_trans (norm_sub_le _ _) (by linarith [hgap])
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.pi
      * ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖) htri 2
    rw [show (1 : ℝ) / (2 * Real.pi ^ 2)
        * (‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2)
        = (‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2) / (2 * Real.pi ^ 2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)]
    nlinarith [hsq, hpi, sq_nonneg (‖((1 / h : ℝ) : ℂ)
      * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖
      - gapMaj s0 X (2 ^ N * (X / h)) δ h h x)]
  -- integrate the transfer
  have hPint : IntervalIntegrable (fun x : ℝ =>
      ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
      volume X (2 * X) :=
    vsing_sq_intervalIntegrable hAc hXpos hh' (-(2 ^ N * (X / h))) (2 ^ N * (X / h))
  have hRint : IntervalIntegrable (fun x : ℝ => 1 / (2 * Real.pi ^ 2)
      * (‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2
        + gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2)) volume X (2 * X) :=
    (hPint.add hGint).const_mul _
  have hSint : IntervalIntegrable
      (fun x : ℝ => ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2) volume X (2 * X) := by
    have hz := shortSum_sub_const_sq_intervalIntegrable a s0 hh' (0 : ℂ) X (2 * X)
    simpa using hz
  have hmono := intervalIntegral.integral_mono_ae_restrict (by linarith : X ≤ 2 * X)
    hSint hRint hpt
  have heval : (∫ x in X..(2 * X), 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2
          + gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2))
      = 1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
        + ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hPint hGint]
  rw [heval] at hmono
  have hstep1 : 1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
        + 1 / X * ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / X)
    calc 1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2)
        ≤ 1 / X * (1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
            ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
          + ∫ x in X..(2 * X), gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2)) := h1
      _ = 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
            ‖((1 / h : ℝ) : ℂ) * uSlab (dpolyA a s0) x h (2 ^ N * (X / h))‖ ^ 2)
          + 1 / X * ∫ x in X..(2 * X),
              gapMaj s0 X (2 ^ N * (X / h)) δ h h x ^ 2) := by ring
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hcont := contour_single_h_kernel a s0 N hX hh1 hhX hrange hMsup
  linarith [hcont, hGsq]

end Salt.MR
