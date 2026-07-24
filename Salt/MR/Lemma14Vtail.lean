/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Lemma14Taylor
import Salt.MR.Lemma14Bridge

/-!
# S8 MR-CORE, node A3a — the `Vⱼ` tail mean square (Lemma 14, stone S-C: THE RISK JOIN)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 22–23 (Lemma 14; frozen statement transcribed verbatim in `Salt.MR.ParsevalSL`).

Companion stones: `Lemma14Taylor` (S-B, the `Uⱼ` slab: `|t| ≤ T₀`) and `Lemma14Bridge`
(S-A the Perron bridge, S-D the far-tail dyadic machinery).  This file is the `Vⱼ`
(`|t| > T₀`) arm: the step where the `x`-average must manufacture frequency separation.

## THE HONEST PAGE (the fail-fast the scoper priced)

**The mechanism, exactly.**  The sharp Perron kernel is *literally a short average*:
`((x+h)^{1+it} − x^{1+it})/(1+it) = ∫_x^{x+h} u^{it} du`
(`uKernel_eq_integral`; FTC, mathlib's `integral_cpow` at `Re(it) = 0 > −1` — unconditional).
Hence, with the **tail transform** `F(u) := ∫_α^β A(1+it)·u^{it} dt` (`tailT`), Fubini on the
compact rectangle gives `Vⱼ(x) = I·∫_x^{x+hⱼ} F(u) du` (`vSeg_eq_tailT_integral`): the whole
`hⱼ`-dependence of the `Vⱼ` object collapses to *"average `F` over a window of length `hⱼ`"*.
So `(1/h₁)V₁ − (1/h₂)V₂` is a difference of two averages of ONE function, and (Cauchy–Schwarz
on each average, then Fubini + translation in `x`) the entire mean square is controlled by the
single scalar `M := (1/X)·∫_X^{3X} ‖F(u)‖² du`.

**Where the `x`-average pays.**  Insert a nonnegative weight `ω ≥ 1` on `[X,3X]`; expanding
`‖F‖²` and exchanging the `u`-integral inwards,
`∫ ω(u)‖F(u)‖² du = ∫∫ A(1+it₁)·conj A(1+it₂)·Ω(t₁−t₂) dt₁ dt₂`,  `Ω(θ) := ∫ ω(u)·u^{iθ} du`,
and Schur/AM–GM turn this into `‖Ω‖_{L¹}·∫ ‖A(1+it)‖² dt`.  **The entire cost is `‖Ω‖_{L¹}/X`,
and it is decided by the shape of the `x`-window:**

* **SHARP window** `ω = 1_{[X,3X]}` (the literal `(1/X)∫_X^{2X}` of the frozen statement).
  Then `Ω(θ) = ((3X)^{1+iθ} − X^{1+iθ})/(1+iθ)`, so `‖Ω(θ)‖ ≤ 4X/√(1+θ²)` — this IS the
  advertised `≪ X/(1+|t₁−t₂|)` separation, produced by the elementary explicit antiderivative
  (no stationary phase).  **But `∫_{|θ|≤2T₁} ‖Ω‖ ≍ X·log T₁`: a `log X` LOSS.**  It is not
  absorbable: the `T₀`-floor does not help (`t₁,t₂` may be adjacent anywhere in the window),
  and the Saffari–Vaughan `min(hⱼ/x, 2/‖s‖)` kernel has **no decay at all** in the mid-range
  `|t| ≤ X/h₁` (there the `min` is `hⱼ/x`); its decay lives only in the far arm `|t| > X/h₁`,
  which is exactly the region `Lemma14Bridge`'s dyadic machinery already owns.
* **SMOOTHED window — the fix, and it is MR's own** (v4 p. 23 runs the argument against a
  smooth cut-off `g(x/X)`; Montgomery–Vaughan p. 32 make the same remark).  One derivative is
  enough — a **tent** suffices, no bump functions, no Plancherel: with
  `ω_X(u) := max(0, 3 − 2|u−2X|/X)` (`xTent`; `≥ 1` on `[X,3X]`, supported on `[X/2, 7X/2]`,
  piecewise linear) the per-piece FTC boundary terms telescope (`ω` is continuous and vanishes
  at the outer ends) and leave the exact closed form
  `Ω_X(θ) = ((X/2)^s − 8(2X)^s + 7(7X/2)^s)/(s(s+1))`,  `s := 1 + iθ`   (`xTentT_eq`),
  whence `‖Ω_X(θ)‖ ≤ 41X/(1+θ²)` (`xTentT_norm_le`, since `‖c^s‖ = c` on `Re s = 1` and
  `‖s‖·‖s+1‖ ≥ 1+θ²`) and `∫_ℝ ‖Ω_X‖ ≤ 41π·X` (`xTentT_row_bound`, via `arctan`).
  **LOG-FREE, with an explicit constant.**

**Verdict (the exact page).**  The separation closes and reduces the double integral to the
single-frequency mean square at **zero log cost** — provided the `x`-window is smoothed by one
derivative.  This is *not* a statement change and *not* a design defect: since `ω_X ≥ 1` on
`[X,3X] ⊇ [X,2X]`, the smoothed bound **implies** the frozen sharp-window statement (smoothing
only enlarges the left-hand side).  The `log X` appears only if one insists on running Schur
against the sharp indicator's transform — which is precisely why MR write `g(x/X)`.

## What lands here

* `uKernel_eq_integral` — the kernel-as-average identity (the structural key).
* `tailT`, `vSeg`, `vSeg_eq_tailT_integral` — the `Vⱼ` object as an average of `F`.
* `xTent`, `xTentT`, `ramp_cpow_integral`, `xTentT_eq` — the smoothed window and its EXACT
  transform `((X/2)^s − 8(2X)^s + 7(7X/2)^s)/(s(s+1))`.
* `xTentT_norm_le` (`≤ 41X/(1+θ²)`), `xTentT_row_bound`/`xTentT_row_bound'` (`≤ 41πX`,
  the log-free Schur row mass).
* `tailT_normSq_expand`, `tailT_weight_inner`, `tailT_weighted_expand` — the two Fubini swaps
  that turn the `u`-average of `‖F‖²` into the double frequency integral against `Ω_X(t₁−t₂)`.
* `tailT_weighted_mean_sq`, `tailT_mean_sq_bound` — **THE SEPARATION**:
  `∫_X^{3X} ‖F(u)‖² du ≤ 41πX·∫_α^β ‖A(t)‖² dt`.
* `sq_intervalIntegral_le`, `vSeg_diff_sq_le` — Cauchy–Schwarz on the short average.
* `tailTr`, `continuous_window_integral`, `xavg_window_le` — the `x`-average (Fubini +
  translation) and the regularization that keeps every continuity hypothesis honest.
* `vtail_mean_sq_bound` — **THE EXIT**:
  `(1/X)∫_X^{2X} ‖(1/h₁)V₁ − (1/h₂)V₂‖² dx ≤ 164π·∫_α^β ‖A(t)‖² dt`  (`0 < h₁,h₂ ≤ X`).

## Scope notes (what is deliberately NOT here)

The frequency window is a **finite segment** `[α,β]`; Lemma 14's two-sided tail
`T₀ ≤ |t| ≤ T₁` is the sum of `[−T₁,−T₀]` and `[T₀,T₁]`, so the exit applies to each and the
caller adds them (`‖a+b‖² ≤ 2‖a‖²+2‖b‖²`).  The **far arm** `|t| > X/h₁` (Lemma 14's weighted
`max`-term) is `Lemma14Bridge`'s landed dyadic machinery, not this file; and the improper
`∫^∞` limit is still not supplied — everything here is at finite truncation `T₁ = β`, which is
the honest form (the truncated Perron representation `Aperron_short_interval` is finite-`T`
too, so no improper limit is needed for the chain).

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## V1 — the sharp Perron kernel IS a short average of `u^{it}` -/

/-- **V1 — the kernel-as-average identity.**
`((x+h)^{1+it} − x^{1+it})/(1+it) = ∫_x^{x+h} u^{it} du`.
FTC: `u^{1+it}/(1+it)` is an antiderivative of `u^{it}`; mathlib's `integral_cpow` applies at
`r = it` because `Re r = 0 > −1`, so **no positivity hypothesis is needed**.  This is the
structural key of the whole `Vⱼ` analysis: the `hⱼ`-dependence becomes "window of length `hⱼ`". -/
theorem uKernel_eq_integral (x h t : ℝ) :
    uKernel x h t = ∫ u in x..(x + h), (u : ℂ) ^ ((t : ℂ) * I) := by
  have hre : ((t : ℂ) * I).re = 0 := by simp
  rw [integral_cpow (Or.inl (by rw [hre]; norm_num)), uKernel, add_comm ((t : ℂ) * I) 1]

/-! ## V2 — the tail transform `F(u) = ∫_α^β A(1+it)·u^{it} dt` and the `Vⱼ` object -/

/-- The **tail transform** `F(u) = ∫_α^β A(t)·u^{it} dt` on a frequency segment `[α,β]`
(`A t` plays the role of `A(1+it)`; the two-sided tail `T₀ ≤ |t| ≤ T₁` is the sum of the
segments `[−T₁,−T₀]` and `[T₀,T₁]`). -/
def tailT (A : ℝ → ℂ) (α β u : ℝ) : ℂ := ∫ t in α..β, A t * (u : ℂ) ^ ((t : ℂ) * I)

/-- The **`Vⱼ` object on a frequency segment**, in `ParsevalAsm`'s `I · ∫` normalization
(the same normalization as `Lemma14Taylor.uSlab`, on the complementary `t`-range). -/
def vSeg (A : ℝ → ℂ) (x h α β : ℝ) : ℂ := I * ∫ t in α..β, A t * uKernel x h t

/-- Continuity of `u ↦ u^{it}` on a positive interval (off the branch cut). -/
private lemma cpowI_contOn {P Q : ℝ} (hP : 0 < P) (t : ℝ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ ((t : ℂ) * I)) (Set.Icc P Q) := by
  intro u hu
  rw [Set.mem_Icc] at hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  exact (continuousAt_ofReal_cpow_const u ((t : ℂ) * I) (Or.inr hu0)).continuousWithinAt

/-- Joint continuity of `(t,u) ↦ A t · u^{it}` on a rectangle with positive `u`-side. -/
private lemma tail_uncurry_contOn {A : ℝ → ℂ} (hA : Continuous A) {α β P Q : ℝ} (hP : 0 < P) :
    ContinuousOn (Function.uncurry fun (t u : ℝ) => A t * (u : ℂ) ^ ((t : ℂ) * I))
      (Set.uIcc α β ×ˢ Set.Icc P Q) := by
  intro p hp
  have hu0 : p.2 ≠ 0 := by
    have := hp.2
    rw [Set.mem_Icc] at this
    linarith [this.1]
  have h1 : ContinuousAt (fun q : ℝ × ℝ => A q.1) p := hA.continuousAt.comp continuousAt_fst
  have h2 : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ) ^ ((q.1 : ℂ) * I)) p := by
    have := continuousAt_ofReal_cpow p.2 ((p.1 : ℂ) * I) (Or.inr hu0)
    exact this.comp₂_of_eq (by fun_prop) (by fun_prop) rfl
  exact (h1.mul h2).continuousWithinAt

/-- **V2 — the `Vⱼ` object is an average of the tail transform.**  For `0 < x`, `0 ≤ h` and a
continuous weight `A`, `vSeg A x h α β = I · ∫_x^{x+h} F(u) du` with `F = tailT A α β`.
Route: `uKernel_eq_integral` pointwise in `t`, then Fubini on the compact rectangle
`[α,β] × [x,x+h]` (`intervalIntegral_intervalIntegral_swap`, integrand jointly continuous). -/
theorem vSeg_eq_tailT_integral {A : ℝ → ℂ} (hA : Continuous A) {x h α β : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) :
    vSeg A x h α β = I * ∫ u in x..(x + h), tailT A α β u := by
  have hxh : x ≤ x + h := by linarith
  have hstep1 : (∫ t in α..β, A t * uKernel x h t)
      = ∫ t in α..β, ∫ u in x..(x + h), A t * (u : ℂ) ^ ((t : ℂ) * I) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [uKernel_eq_integral, intervalIntegral.integral_const_mul]
  have hcont := tail_uncurry_contOn hA (α := α) (β := β) (P := x) (Q := x + h) hx
  have hint : IntegrableOn
      (Function.uncurry fun (t u : ℝ) => A t * (u : ℂ) ^ ((t : ℂ) * I))
      (Set.uIoc α β ×ˢ Set.uIoc x (x + h)) volume := by
    have hK : IntegrableOn
        (Function.uncurry fun (t u : ℝ) => A t * (u : ℂ) ^ ((t : ℂ) * I))
        (Set.uIcc α β ×ˢ Set.Icc x (x + h)) volume :=
      hcont.integrableOn_compact (isCompact_uIcc.prod isCompact_Icc)
    refine hK.mono_set (Set.prod_mono (fun p hp => ?_) (fun p hp => ?_))
    · exact Set.uIoc_subset_uIcc hp
    · rw [Set.uIoc_of_le hxh] at hp
      exact Set.Ioc_subset_Icc_self hp
  rw [vSeg, hstep1, intervalIntegral_intervalIntegral_swap hint]
  rfl

/-! ## V3 — the smoothed `x`-window (the tent) -/

/-- The **tent window** `ω_X(u) = max(0, 3 − 2|u−2X|/X)`: nonnegative, supported on
`[X/2, 7X/2]`, `≥ 1` on all of `[X, 3X]`, piecewise linear.  This is the concrete stand-in for
MR's smooth cut-off `g(x/X)` (v4 p. 23) — one derivative is all the separation step needs. -/
def xTent (X u : ℝ) : ℝ := max 0 (3 - 2 * |u - 2 * X| / X)

lemma xTent_nonneg (X u : ℝ) : 0 ≤ xTent X u := le_max_left _ _

lemma xTent_continuous (X : ℝ) : Continuous (xTent X) := by
  unfold xTent
  exact continuous_const.max
    (continuous_const.sub (((continuous_const.mul
      ((continuous_id.sub continuous_const).abs))).div_const X))

/-- The tent dominates `1` on `[X, 3X]` — so the smoothed mean square dominates the sharp one. -/
lemma one_le_xTent {X u : ℝ} (hX : 0 < X) (h1 : X ≤ u) (h2 : u ≤ 3 * X) : 1 ≤ xTent X u := by
  have habs : |u - 2 * X| ≤ X := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiv : 2 * |u - 2 * X| / X ≤ 2 := by rw [div_le_iff₀ hX]; linarith
  exact le_max_of_le_right (by linarith)

lemma xTent_left {X u : ℝ} (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 2 * X) :
    xTent X u = 2 * u / X - 1 := by
  have habs : |u - 2 * X| = 2 * X - u := by rw [abs_of_nonpos (by linarith)]; ring
  have hval : 3 - 2 * |u - 2 * X| / X = 2 * u / X - 1 := by
    rw [habs]; field_simp; ring
  rw [xTent, hval, max_eq_right]
  rw [sub_nonneg, le_div_iff₀ hX]
  linarith

lemma xTent_right {X u : ℝ} (hX : 0 < X) (h1 : 2 * X ≤ u) (h2 : u ≤ 7 * X / 2) :
    xTent X u = 7 - 2 * u / X := by
  have habs : |u - 2 * X| = u - 2 * X := abs_of_nonneg (by linarith)
  have hval : 3 - 2 * |u - 2 * X| / X = 7 - 2 * u / X := by
    rw [habs]; field_simp; ring
  rw [xTent, hval, max_eq_right]
  rw [sub_nonneg, div_le_iff₀ hX]
  linarith

/-! ## V4 — the ramp integral and the exact tent transform -/

/-- The elementary **ramp integral**: for `0 < a ≤ b`,
`∫_a^b (p + q·u)·u^{iθ} du = p·(b^{1+iθ} − a^{1+iθ})/(1+iθ) + q·(b^{2+iθ} − a^{2+iθ})/(2+iθ)`.
Both pieces are mathlib's `integral_cpow` (at `Re = 0` and `Re = 1`, both `> −1`); the
`u·u^{iθ} = u^{1+iθ}` step is `Complex.cpow_add` off `u = 0`. -/
lemma ramp_cpow_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p q : ℂ) (θ : ℝ) :
    (∫ u in a..b, (p + q * (u : ℂ)) * (u : ℂ) ^ ((θ : ℂ) * I))
      = p * (((b : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I) - (a : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
            / ((1 : ℂ) + (θ : ℂ) * I))
        + q * (((b : ℂ) ^ ((2 : ℂ) + (θ : ℂ) * I) - (a : ℂ) ^ ((2 : ℂ) + (θ : ℂ) * I))
            / ((2 : ℂ) + (θ : ℂ) * I)) := by
  have hcongr : Set.EqOn (fun u : ℝ => (p + q * (u : ℂ)) * (u : ℂ) ^ ((θ : ℂ) * I))
      (fun u : ℝ => p * (u : ℂ) ^ ((θ : ℂ) * I) + q * (u : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
      (Set.uIcc a b) := by
    intro u hu
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hu.1] : u ≠ 0)
    simp only
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
    ring
  have hi1 : IntervalIntegrable (fun u : ℝ => p * (u : ℂ) ^ ((θ : ℂ) * I)) volume a b :=
    (intervalIntegrable_cpow (Or.inl (by simp))).const_mul p
  have hi2 : IntervalIntegrable
      (fun u : ℝ => q * (u : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)) volume a b :=
    (intervalIntegrable_cpow (Or.inl (by simp))).const_mul q
  have e1 : (∫ u in a..b, (u : ℂ) ^ ((θ : ℂ) * I))
      = ((b : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I) - (a : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
          / ((1 : ℂ) + (θ : ℂ) * I) := by
    rw [integral_cpow (Or.inl (by simp)), add_comm ((θ : ℂ) * I) 1]
  have e2 : (∫ u in a..b, (u : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
      = ((b : ℂ) ^ ((2 : ℂ) + (θ : ℂ) * I) - (a : ℂ) ^ ((2 : ℂ) + (θ : ℂ) * I))
          / ((2 : ℂ) + (θ : ℂ) * I) := by
    rw [integral_cpow (Or.inl (by simp)),
      show (1 : ℂ) + (θ : ℂ) * I + 1 = (2 : ℂ) + (θ : ℂ) * I by ring]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, e1, e2]

/-- The **tent transform** `Ω_X(θ) = ∫ ω_X(u)·u^{iθ} du` (the `x`-window's Mellin datum on the
line `Re s = 1`: this is what the `x`-average of the mean square produces). -/
def xTentT (X θ : ℝ) : ℂ :=
  ∫ u in (X / 2)..(7 * X / 2), (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I)

/-- `c^{2+iθ} = c·c^{1+iθ}` for `c > 0` — the relation that collapses the ramp output. -/
private lemma cpow_two_eq {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ((c : ℝ) : ℂ) ^ ((2 : ℂ) + (θ : ℂ) * I)
      = ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I) := by
  have hne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [show (2 : ℂ) + (θ : ℂ) * I = 1 + ((1 : ℂ) + (θ : ℂ) * I) by ring,
    Complex.cpow_add _ _ hne, Complex.cpow_one]

/-- **V4 — the exact tent transform.**  For `X > 0`,
`Ω_X(θ) = ((X/2)^s − 8(2X)^s + 7(7X/2)^s)/(s(s+1))` with `s = 1+iθ`.
The two ramp pieces' `1/s` boundary terms cancel at the join `u = 2X` (the tent is continuous
and vanishes at `X/2`, `7X/2`) — this telescoping is exactly the "one derivative" that turns
the sharp window's `1/s` into the smoothed window's `1/(s(s+1))`. -/
theorem xTentT_eq {X : ℝ} (hX : 0 < X) (θ : ℝ) :
    xTentT X θ
      = (((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
          - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
          + 7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
        / (((1 : ℂ) + (θ : ℂ) * I) * ((2 : ℂ) + (θ : ℂ) * I)) := by
  have hXne : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hs1 : ((1 : ℂ) + (θ : ℂ) * I) ≠ 0 := by
    intro hc
    have : ((1 : ℂ) + (θ : ℂ) * I).re = 1 := by simp
    rw [hc] at this; simp at this
  have hs2 : ((2 : ℂ) + (θ : ℂ) * I) ≠ 0 := by
    intro hc
    have : ((2 : ℂ) + (θ : ℂ) * I).re = 2 := by simp
    rw [hc] at this; simp at this
  -- the two pieces
  have hlt1 : X / 2 ≤ 2 * X := by linarith
  have hlt2 : (2 : ℝ) * X ≤ 7 * X / 2 := by linarith
  have hcont : ContinuousOn (fun u : ℝ => (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
      (Set.Icc (X / 2) (7 * X / 2)) :=
    (Complex.continuous_ofReal.comp (xTent_continuous X)).continuousOn.mul
      (cpowI_contOn (by linarith : (0 : ℝ) < X / 2) θ)
  have hI1 : IntervalIntegrable (fun u : ℝ => (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
      volume (X / 2) (2 * X) := by
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hlt1]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hI2 : IntervalIntegrable (fun u : ℝ => (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
      volume (2 * X) (7 * X / 2) := by
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hlt2]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hsplit : xTentT X θ
      = (∫ u in (X / 2)..(2 * X), (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
        + ∫ u in (2 * X)..(7 * X / 2), (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  -- replace the tent by its linear pieces
  have hc1 : Set.EqOn (fun u : ℝ => (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
      (fun u : ℝ => ((-1 : ℂ) + ((2 : ℂ) / (X : ℂ)) * (u : ℂ)) * (u : ℂ) ^ ((θ : ℂ) * I))
      (Set.uIcc (X / 2) (2 * X)) := by
    intro u hu
    rw [Set.uIcc_of_le hlt1, Set.mem_Icc] at hu
    simp only
    rw [xTent_left hX hu.1 hu.2]
    congr 1
    push_cast
    field_simp
    ring
  have hc2 : Set.EqOn (fun u : ℝ => (xTent X u : ℂ) * (u : ℂ) ^ ((θ : ℂ) * I))
      (fun u : ℝ => ((7 : ℂ) + (-(2 : ℂ) / (X : ℂ)) * (u : ℂ)) * (u : ℂ) ^ ((θ : ℂ) * I))
      (Set.uIcc (2 * X) (7 * X / 2)) := by
    intro u hu
    rw [Set.uIcc_of_le hlt2, Set.mem_Icc] at hu
    simp only
    rw [xTent_right hX hu.1 hu.2]
    congr 1
    push_cast
    field_simp
    ring
  rw [hsplit, intervalIntegral.integral_congr hc1, intervalIntegral.integral_congr hc2,
    ramp_cpow_integral (by linarith : (0 : ℝ) < X / 2) hlt1,
    ramp_cpow_integral (by linarith : (0 : ℝ) < 2 * X) hlt2,
    cpow_two_eq (by linarith : (0 : ℝ) < X / 2), cpow_two_eq (by linarith : (0 : ℝ) < 2 * X),
    cpow_two_eq (by linarith : (0 : ℝ) < 7 * X / 2)]
  push_cast
  field_simp
  ring

/-! ## V5 — the tent transform's `1/(1+θ²)` decay and its log-free `L¹` mass -/

/-- `‖c^{1+iθ}‖ = c` for `c > 0` (the line `Re s = 1`). -/
private lemma norm_cpow_line_one {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖((c : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖ = c := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hc, show ((1 : ℂ) + (θ : ℂ) * I).re = 1 by simp,
    Real.rpow_one]

/-- **V5 — the smoothed window's separation kernel.**  `‖Ω_X(θ)‖ ≤ 41X/(1+θ²)`.
This is the payoff of the tent: the sharp window only gives `‖Ω‖ ≤ 4X/√(1+θ²)` (whose `L¹`
mass over `|θ| ≤ 2T₁` is `≍ X log T₁` — the `log X` loss), whereas one derivative upgrades the
denominator to `s(s+1)` and the kernel becomes `L¹` with mass `O(X)`. -/
theorem xTentT_norm_le {X : ℝ} (hX : 0 < X) (θ : ℝ) :
    ‖xTentT X θ‖ ≤ 41 * X / (1 + θ ^ 2) := by
  have hz1 : ‖(1 : ℂ) + (θ : ℂ) * I‖ = Real.sqrt (1 + θ ^ 2) := by
    rw [show ((1 : ℂ) + (θ : ℂ) * I) = (((1 : ℝ) : ℂ) + ((θ : ℝ) : ℂ) * I) by norm_num,
      Complex.norm_add_mul_I]
    norm_num
  have hz2 : ‖(2 : ℂ) + (θ : ℂ) * I‖ = Real.sqrt (4 + θ ^ 2) := by
    rw [show ((2 : ℂ) + (θ : ℂ) * I) = (((2 : ℝ) : ℂ) + ((θ : ℝ) : ℂ) * I) by norm_num,
      Complex.norm_add_mul_I]
    norm_num
  have hsq : Real.sqrt (1 + θ ^ 2) * Real.sqrt (1 + θ ^ 2) = 1 + θ ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  have hmono : Real.sqrt (1 + θ ^ 2) ≤ Real.sqrt (4 + θ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hden : (1 : ℝ) + θ ^ 2 ≤ ‖((1 : ℂ) + (θ : ℂ) * I) * ((2 : ℂ) + (θ : ℂ) * I)‖ := by
    rw [norm_mul, hz1, hz2]
    nlinarith [Real.sqrt_nonneg (1 + θ ^ 2)]
  have hdpos : (0 : ℝ) < ‖((1 : ℂ) + (θ : ℂ) * I) * ((2 : ℂ) + (θ : ℂ) * I)‖ := by
    have : (0 : ℝ) < 1 + θ ^ 2 := by positivity
    linarith
  have hnum : ‖((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
      - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
      + 7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖ ≤ 41 * X := by
    have e1 := norm_cpow_line_one (by linarith : (0 : ℝ) < X / 2) θ
    have e2 := norm_cpow_line_one (by linarith : (0 : ℝ) < 2 * X) θ
    have e3 := norm_cpow_line_one (by linarith : (0 : ℝ) < 7 * X / 2) θ
    calc ‖((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
            - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
            + 7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖
        ≤ ‖((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
            - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖
          + ‖7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖ := norm_add_le _ _
      _ ≤ (‖((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖
            + ‖8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖)
          + ‖7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)‖ := by
            gcongr
            exact norm_sub_le _ _
      _ = 41 * X := by
            rw [norm_mul, norm_mul, e1, e2, e3]
            norm_num
            ring
  rw [xTentT_eq hX, norm_div, div_le_div_iff₀ hdpos (by positivity)]
  nlinarith [norm_nonneg (((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
    - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
    + 7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))]

lemma xTentT_continuous {X : ℝ} (hX : 0 < X) : Continuous (xTentT X) := by
  have hfun : xTentT X = fun θ : ℝ =>
      (((X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
        - 8 * ((2 * X : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)
        + 7 * ((7 * X / 2 : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I))
      / (((1 : ℂ) + (θ : ℂ) * I) * ((2 : ℂ) + (θ : ℂ) * I)) :=
    funext (fun θ => xTentT_eq hX θ)
  rw [hfun]
  have hs : Continuous (fun θ : ℝ => (1 : ℂ) + (θ : ℂ) * I) := by fun_prop
  have hs' : Continuous (fun θ : ℝ => (2 : ℂ) + (θ : ℂ) * I) := by fun_prop
  have hb : ∀ c : ℝ, 0 < c → Continuous (fun θ : ℝ => ((c : ℝ) : ℂ) ^ ((1 : ℂ) + (θ : ℂ) * I)) :=
    fun c hc => hs.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  have hne : ∀ θ : ℝ, ((1 : ℂ) + (θ : ℂ) * I) * ((2 : ℂ) + (θ : ℂ) * I) ≠ 0 := by
    intro θ
    refine mul_ne_zero (fun hc => ?_) (fun hc => ?_)
    · have h1 : ((1 : ℂ) + (θ : ℂ) * I).re = 1 := by simp
      rw [hc] at h1; simp at h1
    · have h1 : ((2 : ℂ) + (θ : ℂ) * I).re = 2 := by simp
      rw [hc] at h1; simp at h1
  exact (((hb _ (by linarith : (0 : ℝ) < X / 2)).sub
      (continuous_const.mul (hb _ (by linarith : (0 : ℝ) < 2 * X)))).add
      (continuous_const.mul (hb _ (by linarith : (0 : ℝ) < 7 * X / 2)))).div (hs.mul hs') hne

/-- **V5' — the row `L¹` mass, LOG-FREE.**  `∫_a^b ‖Ω_X(c−t)‖ dt ≤ 41π·X`, uniformly in the
segment `[a,b]` and the centre `c`.  This is the Schur row-sum the separation step consumes:
the bound is independent of the length of the frequency window, which is exactly what the
sharp `x`-window fails to give (there the same integral grows like `X·log`). -/
theorem xTentT_row_bound {X : ℝ} (hX : 0 < X) {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, ‖xTentT X (c - t)‖) ≤ 41 * X * Real.pi := by
  have hcont : Continuous (fun t : ℝ => ‖xTentT X (c - t)‖) :=
    ((xTentT_continuous hX).comp (continuous_const.sub continuous_id)).norm
  have hgcont : Continuous (fun t : ℝ => 41 * X / (1 + (c - t) ^ 2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hstep1 : (∫ t in a..b, ‖xTentT X (c - t)‖) ≤ ∫ t in a..b, 41 * X / (1 + (c - t) ^ 2) := by
    refine intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
      (hgcont.intervalIntegrable a b) (fun t _ => xTentT_norm_le hX (c - t))
  have hstep2 : (∫ t in a..b, 41 * X / (1 + (c - t) ^ 2))
      = 41 * X * ∫ t in a..b, (1 + (c - t) ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => div_eq_mul_inv _ _)
  have hstep3 : (∫ t in a..b, (1 + (c - t) ^ 2)⁻¹)
      = ∫ t in (c - b)..(c - a), (1 + t ^ 2)⁻¹ :=
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => (1 + t ^ 2)⁻¹) c
  have hstep4 : (∫ t in (c - b)..(c - a), (1 + t ^ 2)⁻¹)
      = Real.arctan (c - a) - Real.arctan (c - b) := integral_inv_one_add_sq
  have hpi : Real.arctan (c - a) - Real.arctan (c - b) ≤ Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two (c - a)
    have h2 := Real.neg_pi_div_two_lt_arctan (c - b)
    linarith
  calc (∫ t in a..b, ‖xTentT X (c - t)‖)
      ≤ ∫ t in a..b, 41 * X / (1 + (c - t) ^ 2) := hstep1
    _ = 41 * X * (Real.arctan (c - a) - Real.arctan (c - b)) := by
        rw [hstep2, hstep3, hstep4]
    _ ≤ 41 * X * Real.pi := by
        refine mul_le_mul_of_nonneg_left hpi (by positivity)

/-- The row bound in the shifted form `‖Ω_X(t − c)‖`. -/
theorem xTentT_row_bound' {X : ℝ} (hX : 0 < X) {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, ‖xTentT X (t - c)‖) ≤ 41 * X * Real.pi := by
  have hcont : Continuous (fun t : ℝ => ‖xTentT X (t - c)‖) :=
    ((xTentT_continuous hX).comp (continuous_id.sub continuous_const)).norm
  have hgcont : Continuous (fun t : ℝ => 41 * X / (1 + (t - c) ^ 2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hstep1 : (∫ t in a..b, ‖xTentT X (t - c)‖) ≤ ∫ t in a..b, 41 * X / (1 + (t - c) ^ 2) :=
    intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
      (hgcont.intervalIntegrable a b) (fun t _ => xTentT_norm_le hX (t - c))
  have hstep2 : (∫ t in a..b, 41 * X / (1 + (t - c) ^ 2))
      = 41 * X * ∫ t in a..b, (1 + (t - c) ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => div_eq_mul_inv _ _)
  have hstep3 : (∫ t in a..b, (1 + (t - c) ^ 2)⁻¹)
      = ∫ t in (a - c)..(b - c), (1 + t ^ 2)⁻¹ :=
    intervalIntegral.integral_comp_sub_right (fun t : ℝ => (1 + t ^ 2)⁻¹) c
  have hpi : Real.arctan (b - c) - Real.arctan (a - c) ≤ Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two (b - c)
    have h2 := Real.neg_pi_div_two_lt_arctan (a - c)
    linarith
  calc (∫ t in a..b, ‖xTentT X (t - c)‖)
      ≤ ∫ t in a..b, 41 * X / (1 + (t - c) ^ 2) := hstep1
    _ = 41 * X * (Real.arctan (b - c) - Real.arctan (a - c)) := by
        rw [hstep2, hstep3, integral_inv_one_add_sq]
    _ ≤ 41 * X * Real.pi := mul_le_mul_of_nonneg_left hpi (by positivity)

/-! ## V6 — the Parseval / Schur join: the `x`-average manufactures the separation -/

/-- `u^{it} = exp(i·t·log u)` for `u > 0`. -/
private lemma cpowI_eq_exp {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (u : ℂ) ^ ((t : ℂ) * I) = Complex.exp (((t * Real.log u : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    ← Complex.ofReal_log hu.le]
  congr 1
  push_cast
  ring

/-- **The frequency-difference collapse.**  `u^{it₁}·conj(u^{it₂}) = u^{i(t₁−t₂)}` for `u > 0`:
this is why the `u`-average of the expanded square sees only the frequency DIFFERENCE. -/
private lemma cpowI_mul_conj {u : ℝ} (hu : 0 < u) (t₁ t₂ : ℝ) :
    (u : ℂ) ^ ((t₁ : ℂ) * I) * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I))
      = (u : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I) := by
  rw [cpowI_eq_exp hu, cpowI_eq_exp hu, cpowI_eq_exp hu, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Conjugation passes through an interval integral. -/
private lemma ii_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ t in a..b, (starRingEnd ℂ) (f t)) = (starRingEnd ℂ) (∫ t in a..b, f t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- The tail transform is continuous on `[c, ∞)` for `c > 0` (a parametric interval integral
with jointly continuous integrand off the branch cut; the `max u c` regularization keeps the
mathlib lemma's global-continuity hypothesis honest). -/
private lemma tailT_continuousOn {A : ℝ → ℂ} (hA : Continuous A) (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (tailT A α β) (Set.Ici c) := by
  have hunc : Continuous (Function.uncurry
      (fun (u t : ℝ) => A t * ((max u c : ℝ) : ℂ) ^ ((t : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hne : (max p.1 c) ≠ 0 := (lt_of_lt_of_le hc (le_max_right _ _)).ne'
    have h2 : ContinuousAt (fun q : ℝ × ℝ => ((max q.1 c : ℝ) : ℂ) ^ ((q.2 : ℂ) * I)) p :=
      (continuousAt_ofReal_cpow (max p.1 c) ((p.2 : ℂ) * I) (Or.inr hne)).comp₂_of_eq
        (by fun_prop) (by fun_prop) rfl
    exact (hA.continuousAt.comp continuousAt_snd).mul h2
  have hg : Continuous (fun u : ℝ => ∫ t in α..β, A t * ((max u c : ℝ) : ℂ) ^ ((t : ℂ) * I)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hunc α β
  refine hg.continuousOn.congr (fun u hu => ?_)
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [max_eq_left (Set.mem_Ici.mp hu)]

/-- Joint continuity of `(u,t) ↦ u^{it}` off `u = 0`. -/
private lemma cpowI_uncurry_contOn {s : Set ℝ} (hs : ∀ u ∈ s, u ≠ 0) (v : Set ℝ) :
    ContinuousOn (Function.uncurry fun (u t : ℝ) => (u : ℂ) ^ ((t : ℂ) * I)) (s ×ˢ v) := by
  intro p hp
  exact ((continuousAt_ofReal_cpow p.1 ((p.2 : ℂ) * I) (Or.inr (hs p.1 hp.1))).comp₂_of_eq
    (by fun_prop) (by fun_prop) rfl).continuousWithinAt

/-- Product-integrability from continuity on a compact rectangle (the Fubini side condition). -/
private lemma integrableOn_rect {G : ℝ → ℝ → ℂ} {P Q α β : ℝ} (hPQ : P ≤ Q)
    (hG : ContinuousOn (Function.uncurry G) (Set.Icc P Q ×ˢ Set.uIcc α β)) :
    IntegrableOn (Function.uncurry G) (Set.uIoc P Q ×ˢ Set.uIoc α β) volume := by
  have hK : IntegrableOn (Function.uncurry G) (Set.Icc P Q ×ˢ Set.uIcc α β) volume :=
    hG.integrableOn_compact (isCompact_Icc.prod isCompact_uIcc)
  refine hK.mono_set (Set.prod_mono (fun p hp => ?_) (fun p hp => Set.uIoc_subset_uIcc hp))
  rw [Set.uIoc_of_le hPQ] at hp
  exact Set.Ioc_subset_Icc_self hp

/-- **V6a — the pointwise square expansion.**  For `u > 0`,
`‖F(u)‖² = ∫∫ A(t₁)·conj A(t₂)·u^{i(t₁−t₂)} dt₁ dt₂`. -/
lemma tailT_normSq_expand {A : ℝ → ℂ} {α β u : ℝ} (hu : 0 < u) :
    ((‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)
      = ∫ t₁ in α..β, ∫ t₂ in α..β,
          A t₁ * (starRingEnd ℂ) (A t₂) * (u : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I) := by
  have h1 : ((‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)
      = (∫ t in α..β, A t * (u : ℂ) ^ ((t : ℂ) * I))
        * (starRingEnd ℂ) (∫ t in α..β, A t * (u : ℂ) ^ ((t : ℂ) * I)) := by
    rw [show (∫ t in α..β, A t * (u : ℂ) ^ ((t : ℂ) * I)) = tailT A α β u from rfl,
      Complex.mul_conj']
    push_cast
    ring
  rw [h1, ← ii_conj, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr (fun t₁ _ => ?_)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t₂ _ => ?_)
  rw [map_mul, ← cpowI_mul_conj hu t₁ t₂]
  ring

/-- **V6b — the inner `u`-integral (first Fubini swap).**  For each fixed `t₂`,
`∫ ω_X(u)·F(u)·conj(u^{it₂}) du = ∫_α^β A(t₁)·Ω_X(t₁−t₂) dt₁`. -/
lemma tailT_weight_inner {A : ℝ → ℂ} (hA : Continuous A) {X α β : ℝ} (hX : 0 < X) (t₂ : ℝ) :
    (∫ u in (X / 2)..(7 * X / 2),
        (xTent X u : ℂ) * tailT A α β u * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I)))
      = ∫ t₁ in α..β, A t₁ * xTentT X (t₁ - t₂) := by
  have hP : (0 : ℝ) < X / 2 := by linarith
  have hPQ : X / 2 ≤ 7 * X / 2 := by linarith
  have hne : ∀ u ∈ Set.Icc (X / 2) (7 * X / 2), u ≠ 0 := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have : (0 : ℝ) < u := lt_of_lt_of_le hP hu.1
    exact this.ne'
  have hcpow := cpowI_uncurry_contOn hne (Set.uIcc α β)
  have hint : IntegrableOn (Function.uncurry fun (u t₁ : ℝ) =>
      (xTent X u : ℂ) * (A t₁ * (u : ℂ) ^ ((t₁ : ℂ) * I))
        * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I)))
      (Set.uIoc (X / 2) (7 * X / 2) ×ˢ Set.uIoc α β) volume := by
    refine integrableOn_rect hPQ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (xTent X p.1 : ℂ))
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) :=
      ((Complex.continuous_ofReal.comp (xTent_continuous X)).comp continuous_fst).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => A p.2)
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) :=
      (hA.comp continuous_snd).continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (starRingEnd ℂ) ((p.1 : ℂ) ^ ((t₂ : ℂ) * I)))
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) := by
      intro p hp
      have hca : ContinuousAt (fun p : ℝ × ℝ => (starRingEnd ℂ) ((p.1 : ℂ) ^ ((t₂ : ℂ) * I))) p :=
        Complex.continuous_conj.continuousAt.comp
          ((continuousAt_ofReal_cpow_const p.1 ((t₂ : ℂ) * I)
            (Or.inr (hne p.1 hp.1))).comp continuousAt_fst)
      exact hca.continuousWithinAt
    exact ((h1.mul (h2.mul hcpow)).mul h3)
  have hcongr : Set.EqOn
      (fun u : ℝ => (xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I)))
      (fun u : ℝ => ∫ t₁ in α..β,
        (xTent X u : ℂ) * (A t₁ * (u : ℂ) ^ ((t₁ : ℂ) * I))
          * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I)))
      (Set.uIcc (X / 2) (7 * X / 2)) := by
    intro u _
    simp only [tailT]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr (fun t₁ _ => ?_)
  rw [xTentT, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le hPQ, Set.mem_Icc] at hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hP hu.1
  rw [← cpowI_mul_conj hu0 t₁ t₂]
  ring

/-- **V6c — the weighted mean square as a double frequency integral (second Fubini swap).**
`∫ ω_X(u)‖F(u)‖² du = ∫∫ conj A(t₂)·A(t₁)·Ω_X(t₁−t₂) dt₁ dt₂`.  This is the Parseval step:
after the `u`-average only the frequency DIFFERENCE survives, weighted by the window's
transform `Ω_X`. -/
theorem tailT_weighted_expand {A : ℝ → ℂ} (hA : Continuous A) {X α β : ℝ} (hX : 0 < X) :
    ((∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)
      = ∫ t₂ in α..β, ∫ t₁ in α..β,
          (starRingEnd ℂ) (A t₂) * (A t₁ * xTentT X (t₁ - t₂)) := by
  have hP : (0 : ℝ) < X / 2 := by linarith
  have hPQ : X / 2 ≤ 7 * X / 2 := by linarith
  have hne : ∀ u ∈ Set.Icc (X / 2) (7 * X / 2), u ≠ 0 := by
    intro u hu
    rw [Set.mem_Icc] at hu
    exact (lt_of_lt_of_le hP hu.1).ne'
  have hFc : ContinuousOn (tailT A α β) (Set.Ici (X / 2)) := tailT_continuousOn hA α β hP
  have hint : IntegrableOn (Function.uncurry fun (u t₂ : ℝ) =>
      (xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)))
      (Set.uIoc (X / 2) (7 * X / 2) ×ˢ Set.uIoc α β) volume := by
    refine integrableOn_rect hPQ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (xTent X p.1 : ℂ))
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) :=
      ((Complex.continuous_ofReal.comp (xTent_continuous X)).comp continuous_fst).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => tailT A α β p.1)
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) := by
      refine hFc.comp continuous_fst.continuousOn (fun p hp => ?_)
      exact Set.mem_Ici.mpr (Set.mem_Icc.mp hp.1).1
    have h3 : ContinuousOn
        (fun p : ℝ × ℝ => (starRingEnd ℂ) (A p.2 * (p.1 : ℂ) ^ ((p.2 : ℂ) * I)))
        (Set.Icc (X / 2) (7 * X / 2) ×ˢ Set.uIcc α β) := by
      intro p hp
      have hca : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) ^ ((q.2 : ℂ) * I)) p :=
        (continuousAt_ofReal_cpow p.1 ((p.2 : ℂ) * I) (Or.inr (hne p.1 hp.1))).comp₂_of_eq
          (by fun_prop) (by fun_prop) rfl
      exact (Complex.continuous_conj.continuousAt.comp
        ((hA.continuousAt.comp continuousAt_snd).mul hca)).continuousWithinAt
    exact (h1.mul h2).mul h3
  have hcongr : Set.EqOn
      (fun u : ℝ => ((xTent X u * ‖tailT A α β u‖ ^ 2 : ℝ) : ℂ))
      (fun u : ℝ => ∫ t₂ in α..β, (xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)))
      (Set.uIcc (X / 2) (7 * X / 2)) := by
    intro u hu
    rw [Set.uIcc_of_le hPQ, Set.mem_Icc] at hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hP hu.1
    have hexp : ((‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)
        = tailT A α β u * (starRingEnd ℂ) (tailT A α β u) := by
      rw [Complex.mul_conj']; push_cast; ring
    have hsplit : (starRingEnd ℂ) (tailT A α β u)
        = ∫ t₂ in α..β, (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)) :=
      (ii_conj _ α β).symm
    change ((xTent X u * ‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)
        = ∫ t₂ in α..β, (xTent X u : ℂ) * tailT A α β u
            * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I))
    have hrhs : (∫ t₂ in α..β, (xTent X u : ℂ) * tailT A α β u
          * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)))
        = ((xTent X u : ℂ) * tailT A α β u)
          * ∫ t₂ in α..β, (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)) :=
      intervalIntegral.integral_const_mul _ _
    rw [hrhs, ← hsplit, Complex.ofReal_mul, hexp]
    ring
  rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_congr hcongr,
    intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr (fun t₂ _ => ?_)
  have hpt : Set.EqOn
      (fun u : ℝ => (xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I)))
      (fun u : ℝ => (starRingEnd ℂ) (A t₂) * ((xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I))))
      (Set.uIcc (X / 2) (7 * X / 2)) := by
    intro u _
    change (xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) (A t₂ * (u : ℂ) ^ ((t₂ : ℂ) * I))
      = (starRingEnd ℂ) (A t₂) * ((xTent X u : ℂ) * tailT A α β u
        * (starRingEnd ℂ) ((u : ℂ) ^ ((t₂ : ℂ) * I)))
    rw [map_mul]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    tailT_weight_inner hA hX t₂, ← intervalIntegral.integral_const_mul]

/-- **V6d — the Schur / AM–GM bound (THE SEPARATION).**  The weighted mean square of the tail
transform is bounded by the single-frequency mean square with the LOG-FREE constant `41πX`:
`∫ ω_X(u)‖F(u)‖² du ≤ 41πX · ∫_α^β ‖A(t)‖² dt`.
Route: `tailT_weighted_expand`, then `‖A(t₂)‖‖A(t₁)‖ ≤ ½(‖A(t₁)‖² + ‖A(t₂)‖²)` and the two
row bounds `xTentT_row_bound`/`xTentT_row_bound'` (each `≤ 41πX`, uniformly in the window). -/
theorem tailT_weighted_mean_sq {A : ℝ → ℂ} (hA : Continuous A) {X α β : ℝ}
    (hX : 0 < X) (hab : α ≤ β) :
    (∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2)
      ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
  set C : ℝ := 41 * X * Real.pi with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hOc : Continuous (fun θ : ℝ => ‖xTentT X θ‖) := (xTentT_continuous hX).norm
  -- the two joint-continuity facts
  have hKc : Continuous (Function.uncurry
      fun (t₂ t₁ : ℝ) => ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖) := by
    exact (((hA.norm.comp continuous_fst).mul (hA.norm.comp continuous_snd)).mul
      (hOc.comp ((continuous_snd).sub continuous_fst)))
  have hPc : Continuous (Function.uncurry
      fun (t₂ t₁ : ℝ) => ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖) := by
    exact (((hA.norm.comp continuous_snd).pow 2).mul
      (hOc.comp ((continuous_snd).sub continuous_fst)))
  have hQc : Continuous (Function.uncurry
      fun (t₂ t₁ : ℝ) => ‖A t₂‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖) := by
    exact (((hA.norm.comp continuous_fst).pow 2).mul
      (hOc.comp ((continuous_snd).sub continuous_fst)))
  -- the `Q`-row: no swap needed
  have hQrow : ∀ t₂ : ℝ, (∫ t₁ in α..β, ‖A t₂‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
      ≤ ‖A t₂‖ ^ 2 * C := by
    intro t₂
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (xTentT_row_bound' hX hab t₂) (by positivity)
  -- the `P`-row after the swap
  have hPswap : (∫ t₂ in α..β, ∫ t₁ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
      = ∫ t₁ in α..β, ∫ t₂ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖ := by
    refine intervalIntegral_intervalIntegral_swap ?_
    have hK : IntegrableOn (Function.uncurry
        fun (t₂ t₁ : ℝ) => ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
        (Set.uIcc α β ×ˢ Set.uIcc α β) volume :=
      hPc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    exact hK.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hPc' : Continuous (Function.uncurry
      fun (t₁ t₂ : ℝ) => ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖) :=
    ((hA.norm.comp continuous_fst).pow 2).mul (hOc.comp (continuous_fst.sub continuous_snd))
  have hPbound : (∫ t₂ in α..β, ∫ t₁ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
      ≤ C * ∫ t in α..β, ‖A t‖ ^ 2 := by
    have hiL : IntervalIntegrable
        (fun t₁ : ℝ => ∫ t₂ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖) volume α β :=
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hPc' α β).intervalIntegrable α β
    have hiR : IntervalIntegrable (fun t : ℝ => C * ‖A t‖ ^ 2) volume α β := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [hPswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab hiL hiR (fun t₁ _ => ?_)
    rw [intervalIntegral.integral_const_mul, mul_comm C (‖A t₁‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left (xTentT_row_bound hX hab t₁) (by positivity)
  -- the AM–GM row bound
  have hrow : ∀ t₂ : ℝ, (∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖)
      ≤ (1 / 2) * (∫ t₁ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
        + (1 / 2) * (‖A t₂‖ ^ 2 * C) := by
    intro t₂
    have hsum : (∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖)
        ≤ ∫ t₁ in α..β, ((1 / 2) * (‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
          + (1 / 2) * (‖A t₂‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)) := by
      refine intervalIntegral.integral_mono_on hab
        ((hKc.uncurry_left t₂).intervalIntegrable α β)
        ((((hPc.uncurry_left t₂).const_mul (1 / 2)).add
          ((hQc.uncurry_left t₂).const_mul (1 / 2))).intervalIntegrable α β)
        (fun t₁ _ => ?_)
      have hnn : (0 : ℝ) ≤ ‖xTentT X (t₁ - t₂)‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖A t₂‖ - ‖A t₁‖), norm_nonneg (A t₂), norm_nonneg (A t₁)]
    refine hsum.trans ?_
    rw [intervalIntegral.integral_add
      (((hPc.uncurry_left t₂).const_mul (1 / 2)).intervalIntegrable α β)
      (((hQc.uncurry_left t₂).const_mul (1 / 2)).intervalIntegrable α β),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith [hQrow t₂]
  -- assemble the double integral bound
  have hdouble : (∫ t₂ in α..β, ∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖)
      ≤ C * ∫ t in α..β, ‖A t‖ ^ 2 := by
    have hiK : IntervalIntegrable
        (fun t₂ : ℝ => ∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖) volume α β :=
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hKc α β).intervalIntegrable α β
    have hiP : IntervalIntegrable
        (fun t₂ : ℝ => (1 / 2) * ∫ t₁ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖) volume α β :=
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hPc α β).const_mul (1 / 2)).intervalIntegrable α β
    have hiQ : IntervalIntegrable
        (fun t₂ : ℝ => (1 / 2) * (‖A t₂‖ ^ 2 * C)) volume α β := by
      apply Continuous.intervalIntegrable; fun_prop
    have hmono : (∫ t₂ in α..β, ∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖)
        ≤ ∫ t₂ in α..β, ((1 / 2) * (∫ t₁ in α..β, ‖A t₁‖ ^ 2 * ‖xTentT X (t₁ - t₂)‖)
          + (1 / 2) * (‖A t₂‖ ^ 2 * C)) :=
      intervalIntegral.integral_mono_on hab hiK (hiP.add hiQ) (fun t₂ _ => hrow t₂)
    refine hmono.trans ?_
    rw [intervalIntegral.integral_add hiP hiQ, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have hQtot : (∫ t₂ in α..β, ‖A t₂‖ ^ 2 * C) = (∫ t in α..β, ‖A t‖ ^ 2) * C :=
      intervalIntegral.integral_mul_const C _
    rw [hQtot]
    linarith [hPbound]
  -- from the complex identity to the real bound
  have hLC := tailT_weighted_expand hA (α := α) (β := β) hX
  have hnorm : ‖((∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)‖
      ≤ C * ∫ t in α..β, ‖A t‖ ^ 2 := by
    have hDc : Continuous (Function.uncurry
        fun (t₂ t₁ : ℝ) => (starRingEnd ℂ) (A t₂) * (A t₁ * xTentT X (t₁ - t₂))) :=
      (Complex.continuous_conj.comp (hA.comp continuous_fst)).mul
        ((hA.comp continuous_snd).mul
          ((xTentT_continuous hX).comp (continuous_snd.sub continuous_fst)))
    have hiD : IntervalIntegrable
        (fun t₂ : ℝ => ‖∫ t₁ in α..β, (starRingEnd ℂ) (A t₂) * (A t₁ * xTentT X (t₁ - t₂))‖)
        volume α β :=
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hDc α β).norm.intervalIntegrable α β
    have hiK : IntervalIntegrable
        (fun t₂ : ℝ => ∫ t₁ in α..β, ‖A t₂‖ * ‖A t₁‖ * ‖xTentT X (t₁ - t₂)‖) volume α β :=
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hKc α β).intervalIntegrable α β
    rw [hLC]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine le_trans (intervalIntegral.integral_mono_on hab hiD hiK (fun t₂ _ => ?_)) hdouble
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine le_of_eq (intervalIntegral.integral_congr (fun t₁ _ => ?_))
    simp only [norm_mul, RCLike.norm_conj]
    ring
  calc (∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2)
      ≤ ‖((∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ C * ∫ t in α..β, ‖A t‖ ^ 2 := hnorm

/-- **V7 — the sharp-window exit.**  Since `ω_X ≥ 1` on `[X,3X]`, the smoothed bound implies the
SHARP one: `∫_X^{3X} ‖F(u)‖² du ≤ 41πX·∫_α^β ‖A(t)‖² dt`.  The smoothing lives entirely inside
the proof — the statement is the sharp-window mean square of the frozen Lemma 14. -/
theorem tailT_mean_sq_bound {A : ℝ → ℂ} (hA : Continuous A) {X α β : ℝ}
    (hX : 0 < X) (hab : α ≤ β) :
    (∫ u in X..(3 * X), ‖tailT A α β u‖ ^ 2) ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
  have hP : (0 : ℝ) < X / 2 := by linarith
  have hFc : ContinuousOn (tailT A α β) (Set.Ici (X / 2)) := tailT_continuousOn hA α β hP
  have hgc : ContinuousOn (fun u : ℝ => xTent X u * ‖tailT A α β u‖ ^ 2) (Set.Ici (X / 2)) :=
    (xTent_continuous X).continuousOn.mul (hFc.norm.pow 2)
  have hsub1 : Set.uIcc X (3 * X) ⊆ Set.Ici (X / 2) := by
    rw [Set.uIcc_of_le (by linarith : X ≤ 3 * X)]
    exact fun u hu => Set.mem_Ici.mpr (by linarith [(Set.mem_Icc.mp hu).1])
  have hsub2 : Set.uIcc (X / 2) (7 * X / 2) ⊆ Set.Ici (X / 2) := by
    rw [Set.uIcc_of_le (by linarith : X / 2 ≤ 7 * X / 2)]
    exact fun u hu => Set.mem_Ici.mpr (Set.mem_Icc.mp hu).1
  have hi1 : IntervalIntegrable (fun u : ℝ => ‖tailT A α β u‖ ^ 2) volume X (3 * X) :=
    ((hFc.norm.pow 2).mono hsub1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun u : ℝ => xTent X u * ‖tailT A α β u‖ ^ 2)
      volume X (3 * X) := (hgc.mono hsub1).intervalIntegrable
  have hi3 : IntervalIntegrable (fun u : ℝ => xTent X u * ‖tailT A α β u‖ ^ 2)
      volume (X / 2) (7 * X / 2) := (hgc.mono hsub2).intervalIntegrable
  have hstep1 : (∫ u in X..(3 * X), ‖tailT A α β u‖ ^ 2)
      ≤ ∫ u in X..(3 * X), xTent X u * ‖tailT A α β u‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) hi1 hi2 (fun u hu => ?_)
    rw [Set.mem_Icc] at hu
    nlinarith [one_le_xTent hX hu.1 hu.2, sq_nonneg ‖tailT A α β u‖]
  have hstep2 : (∫ u in X..(3 * X), xTent X u * ‖tailT A α β u‖ ^ 2)
      ≤ ∫ u in (X / 2)..(7 * X / 2), xTent X u * ‖tailT A α β u‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall
        (fun u => mul_nonneg (xTent_nonneg X u) (sq_nonneg _))) hi3
  exact le_trans (le_trans hstep1 hstep2) (tailT_weighted_mean_sq hA hX hab)

/-! ## V8 — the `Vⱼ` mean square: Cauchy–Schwarz on the average, then the `x`-average -/

/-- **Cauchy–Schwarz on a segment, variance form**: `(∫_a^b G)² ≤ (b−a)·∫_a^b G²`. -/
lemma sq_intervalIntegral_le {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G (Set.uIcc a b)) :
    (∫ u in a..b, G u) ^ 2 ≤ (b - a) * ∫ u in a..b, G u ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hL : (0 : ℝ) < b - a := by linarith
  set m : ℝ := (∫ u in a..b, G u) / (b - a) with hm
  have hiG : IntervalIntegrable G volume a b := hG.intervalIntegrable
  have hiG2 : IntervalIntegrable (fun u => G u ^ 2) volume a b := (hG.pow 2).intervalIntegrable
  have hexp : (∫ u in a..b, (G u - m) ^ 2)
      = (∫ u in a..b, G u ^ 2) + ((-(2 * m)) * (∫ u in a..b, G u) + m ^ 2 * (b - a)) := by
    rw [intervalIntegral.integral_congr
      (g := fun u => G u ^ 2 + ((-(2 * m)) * G u + m ^ 2)) (fun u _ => by ring),
      intervalIntegral.integral_add hiG2 ((hiG.const_mul _).add _root_.intervalIntegrable_const),
      intervalIntegral.integral_add (hiG.const_mul _) _root_.intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hnn : (0 : ℝ) ≤ ∫ u in a..b, (G u - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  rw [hexp] at hnn
  have hmL : m * (b - a) = ∫ u in a..b, G u := by
    rw [hm]; field_simp
  nlinarith [hnn, hmL, hL]

/-- **V8a — the pointwise `Vⱼ` weighted-difference bound.**  Using `vSeg_eq_tailT_integral`
(the `Vⱼ` object is `I` times the average of `F` over `[x, x+hⱼ]`), Cauchy–Schwarz on each
average gives
`‖(1/h₁)V₁ − (1/h₂)V₂‖² ≤ 2·(1/h₁)∫_x^{x+h₁}‖F‖² + 2·(1/h₂)∫_x^{x+h₂}‖F‖²`. -/
theorem vSeg_diff_sq_le {A : ℝ → ℂ} (hA : Continuous A) {x h₁ h₂ α β : ℝ}
    (hx : 0 < x) (hh1 : 0 < h₁) (hh2 : 0 < h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2
      ≤ 2 * ((1 / h₁) * ∫ u in x..(x + h₁), ‖tailT A α β u‖ ^ 2)
        + 2 * ((1 / h₂) * ∫ u in x..(x + h₂), ‖tailT A α β u‖ ^ 2) := by
  have hFc : ContinuousOn (tailT A α β) (Set.Ici x) := tailT_continuousOn hA α β hx
  have key : ∀ h : ℝ, 0 < h →
      ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖ ^ 2
        ≤ (1 / h) * ∫ u in x..(x + h), ‖tailT A α β u‖ ^ 2 := by
    intro h hh
    have hxh : x ≤ x + h := by linarith
    have hsub : Set.uIcc x (x + h) ⊆ Set.Ici x := by
      rw [Set.uIcc_of_le hxh]
      exact fun u hu => Set.mem_Ici.mpr (Set.mem_Icc.mp hu).1
    have hGc : ContinuousOn (fun u => ‖tailT A α β u‖) (Set.uIcc x (x + h)) :=
      (hFc.mono hsub).norm
    have hnorm : ‖((1 / h : ℝ) : ℂ) * vSeg A x h α β‖
        = (1 / h) * ‖∫ u in x..(x + h), tailT A α β u‖ := by
      rw [vSeg_eq_tailT_integral hA hx hh.le, norm_mul, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
    have htri : ‖∫ u in x..(x + h), tailT A α β u‖ ≤ ∫ u in x..(x + h), ‖tailT A α β u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxh
    have hcs := sq_intervalIntegral_le hxh hGc
    have hnn : (0 : ℝ) ≤ ∫ u in x..(x + h), ‖tailT A α β u‖ :=
      intervalIntegral.integral_nonneg hxh (fun u _ => norm_nonneg _)
    rw [hnorm, mul_pow]
    have hsq : ‖∫ u in x..(x + h), tailT A α β u‖ ^ 2
        ≤ h * ∫ u in x..(x + h), ‖tailT A α β u‖ ^ 2 := by
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) htri 2) ?_
      simpa using hcs
    have hinv : (0 : ℝ) < (1 / h) ^ 2 := by positivity
    calc (1 / h) ^ 2 * ‖∫ u in x..(x + h), tailT A α β u‖ ^ 2
        ≤ (1 / h) ^ 2 * (h * ∫ u in x..(x + h), ‖tailT A α β u‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsq hinv.le
      _ = (1 / h) * ∫ u in x..(x + h), ‖tailT A α β u‖ ^ 2 := by
          field_simp
  have h1 := key h₁ hh1
  have h2 := key h₂ hh2
  set a : ℂ := ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β with ha
  set b : ℂ := ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β with hb
  have hsq : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [hsq, h1, h2, sq_nonneg (‖a‖ - ‖b‖)]

/-- The `max`-regularized tail transform: globally continuous, equal to `tailT` on `[c,∞)`. -/
def tailTr (A : ℝ → ℂ) (α β c u : ℝ) : ℂ := tailT A α β (max u c)

lemma tailTr_eq (A : ℝ → ℂ) (α β : ℝ) {c u : ℝ} (hu : c ≤ u) :
    tailTr A α β c u = tailT A α β u := by rw [tailTr, max_eq_left hu]

lemma tailTr_continuous {A : ℝ → ℂ} (hA : Continuous A) (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (tailTr A α β c) := by
  have hunc : Continuous (Function.uncurry
      (fun (u t : ℝ) => A t * ((max u c : ℝ) : ℂ) ^ ((t : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hne : (max p.1 c) ≠ 0 := (lt_of_lt_of_le hc (le_max_right _ _)).ne'
    have h2 : ContinuousAt (fun q : ℝ × ℝ => ((max q.1 c : ℝ) : ℂ) ^ ((q.2 : ℂ) * I)) p :=
      (continuousAt_ofReal_cpow (max p.1 c) ((p.2 : ℂ) * I) (Or.inr hne)).comp₂_of_eq
        (by fun_prop) (by fun_prop) rfl
    exact (hA.continuousAt.comp continuousAt_snd).mul h2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hunc α β

/-- `x ↦ ∫_x^{x+h} f` is continuous for continuous `f` (difference of two primitives). -/
lemma continuous_window_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) (h : ℝ) :
    Continuous (fun x : ℝ => ∫ u in x..(x + h), f u) := by
  have h1 : Continuous (fun x : ℝ => ∫ u in (0 : ℝ)..(x + h), f u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ) (t : ℝ) => f t) (a₀ := 0) (by fun_prop) (by fun_prop)
  have h2 : Continuous (fun x : ℝ => ∫ u in (0 : ℝ)..x, f u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ) (t : ℝ) => f t) (a₀ := 0) (by fun_prop) continuous_id
  refine (h1.sub h2).congr (fun x => ?_)
  exact intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)

/-- **V8b — the `x`-average of a short-window mean (Fubini + translation).**  For `0 < h ≤ X`
and nonnegative continuous `G`,
`∫_X^{2X} ((1/h)∫_x^{x+h} G) dx ≤ ∫_X^{3X} G`: the window average, averaged over `x ∈ [X,2X]`,
never sees more than `[X, 3X]`. -/
lemma xavg_window_le {G : ℝ → ℝ} {X h : ℝ} (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hG : Continuous G) (hGnn : ∀ u, 0 ≤ G u) :
    (∫ x in X..(2 * X), (1 / h) * ∫ u in x..(x + h), G u) ≤ ∫ u in X..(3 * X), G u := by
  have htr : ∀ x : ℝ, (∫ u in x..(x + h), G u) = ∫ w in (0 : ℝ)..h, G (x + w) := by
    intro x
    have hc := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := h) G x
    rw [add_zero] at hc
    exact hc.symm
  have hswap : (∫ x in X..(2 * X), ∫ w in (0 : ℝ)..h, G (x + w))
      = ∫ w in (0 : ℝ)..h, ∫ x in X..(2 * X), G (x + w) := by
    refine intervalIntegral_intervalIntegral_swap ?_
    have hK : IntegrableOn (Function.uncurry fun (x w : ℝ) => G (x + w))
        (Set.uIcc X (2 * X) ×ˢ Set.uIcc (0 : ℝ) h) volume :=
      (hG.comp (continuous_fst.add continuous_snd)).continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)
    exact hK.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hinner : ∀ w ∈ Set.Icc (0 : ℝ) h,
      (∫ x in X..(2 * X), G (x + w)) ≤ ∫ u in X..(3 * X), G u := by
    intro w hw
    rw [Set.mem_Icc] at hw
    rw [intervalIntegral.integral_comp_add_right G w]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hGnn) (hG.intervalIntegrable _ _)
  calc (∫ x in X..(2 * X), (1 / h) * ∫ u in x..(x + h), G u)
      = (1 / h) * ∫ x in X..(2 * X), ∫ w in (0 : ℝ)..h, G (x + w) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun x _ => by rw [htr x])
    _ = (1 / h) * ∫ w in (0 : ℝ)..h, ∫ x in X..(2 * X), G (x + w) := by rw [hswap]
    _ ≤ (1 / h) * ∫ _w in (0 : ℝ)..h, (∫ u in X..(3 * X), G u) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine intervalIntegral.integral_mono_on hh.le ?_ _root_.intervalIntegrable_const hinner
        exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun (w x : ℝ) => G (x + w))
          (hG.comp (continuous_snd.add continuous_fst)) X (2 * X)).intervalIntegrable _ _
    _ = ∫ u in X..(3 * X), G u := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        field_simp

/-- **V9 — THE EXIT.**  The `x`-averaged mean square of the weighted `Vⱼ` difference on a
frequency segment `[α,β]`, with an explicit LOG-FREE constant:
`(1/X)·∫_X^{2X} ‖(1/h₁)V₁(x) − (1/h₂)V₂(x)‖² dx ≤ 164π·∫_α^β ‖A(t)‖² dt`
for `0 < h₁, h₂ ≤ X`.  (`A t` is `A(1+it)`; the two-sided `|t| > T₀` tail of Lemma 14 is the
sum of the segments `[−T₁,−T₀]` and `[T₀,T₁]`, so the bound applies to each.)

Chain: `vSeg_eq_tailT_integral` (the `Vⱼ` object is an average of `F`) → `vSeg_diff_sq_le`
(Cauchy–Schwarz on each average) → `xavg_window_le` (the `x`-average, Fubini + translation)
→ `tailT_mean_sq_bound` (THE SEPARATION, the tent window's log-free `L¹` kernel mass). -/
theorem vtail_mean_sq_bound {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ α β : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (hh1X : h₁ ≤ X) (hh2X : h₂ ≤ X) (hab : α ≤ β) :
    (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 164 * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
  have hP : (0 : ℝ) < X / 2 := by linarith
  have hX2 : X ≤ 2 * X := by linarith
  have hFrc : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β hP
  have hGrc : Continuous (fun u : ℝ => ‖tailTr A α β (X / 2) u‖ ^ 2) := hFrc.norm.pow 2
  have hGrnn : ∀ u : ℝ, 0 ≤ ‖tailTr A α β (X / 2) u‖ ^ 2 := fun u => by positivity
  -- the regularized window integrals agree with the honest ones on `[X, 2X]`
  have hwin : ∀ (x h : ℝ), X ≤ x → 0 ≤ h →
      (∫ u in x..(x + h), ‖tailT A α β u‖ ^ 2)
        = ∫ u in x..(x + h), ‖tailTr A α β (X / 2) u‖ ^ 2 := by
    intro x h hx hh
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith : x ≤ x + h), Set.mem_Icc] at hu
    rw [tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)]
  have hVreg : ∀ (x h : ℝ), X ≤ x → 0 ≤ h →
      vSeg A x h α β = I * ∫ u in x..(x + h), tailTr A α β (X / 2) u := by
    intro x h hx hh
    rw [vSeg_eq_tailT_integral hA (by linarith : 0 < x) hh]
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith : x ≤ x + h), Set.mem_Icc] at hu
    exact (tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)).symm
  -- continuity of the regularized V-difference
  have hVc : Continuous (fun x : ℝ =>
      ‖((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
        - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)‖ ^ 2) :=
    (((continuous_const.mul (continuous_const.mul (continuous_window_integral hFrc h₁))).sub
      (continuous_const.mul
        (continuous_const.mul (continuous_window_integral hFrc h₂)))).norm.pow 2)
  have hMc : Continuous (fun x : ℝ =>
      2 * ((1 / h₁) * ∫ u in x..(x + h₁), ‖tailTr A α β (X / 2) u‖ ^ 2)
        + 2 * ((1 / h₂) * ∫ u in x..(x + h₂), ‖tailTr A α β (X / 2) u‖ ^ 2)) :=
    (continuous_const.mul (continuous_const.mul (continuous_window_integral hGrc h₁))).add
      (continuous_const.mul (continuous_const.mul (continuous_window_integral hGrc h₂)))
  -- the x-integral of the majorant
  have hmaj : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ 4 * ∫ u in X..(3 * X), ‖tailTr A α β (X / 2) u‖ ^ 2 := by
    have hcongr : (∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
        = ∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
            - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le hX2, Set.mem_Icc] at hx
      rw [hVreg x h₁ hx.1 hh1.le, hVreg x h₂ hx.1 hh2.le]
    rw [hcongr]
    have hstep : (∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
            - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)‖ ^ 2)
        ≤ ∫ x in X..(2 * X),
          (2 * ((1 / h₁) * ∫ u in x..(x + h₁), ‖tailTr A α β (X / 2) u‖ ^ 2)
            + 2 * ((1 / h₂) * ∫ u in x..(x + h₂), ‖tailTr A α β (X / 2) u‖ ^ 2)) := by
      refine intervalIntegral.integral_mono_on hX2 (hVc.intervalIntegrable _ _)
        (hMc.intervalIntegrable _ _) (fun x hx => ?_)
      rw [Set.mem_Icc] at hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      have hpt := vSeg_diff_sq_le hA (α := α) (β := β) hx0 hh1 hh2
      rw [hVreg x h₁ hx.1 hh1.le, hVreg x h₂ hx.1 hh2.le,
        hwin x h₁ hx.1 hh1.le, hwin x h₂ hx.1 hh2.le] at hpt
      exact hpt
    refine hstep.trans ?_
    have hi1 : IntervalIntegrable (fun x : ℝ =>
        2 * ((1 / h₁) * ∫ u in x..(x + h₁), ‖tailTr A α β (X / 2) u‖ ^ 2)) volume X (2 * X) :=
      ((continuous_window_integral hGrc h₁).const_mul (1 / h₁)).const_mul 2
        |>.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x : ℝ =>
        2 * ((1 / h₂) * ∫ u in x..(x + h₂), ‖tailTr A α β (X / 2) u‖ ^ 2)) volume X (2 * X) :=
      ((continuous_window_integral hGrc h₂).const_mul (1 / h₂)).const_mul 2
        |>.intervalIntegrable _ _
    have e1 : (∫ x in X..(2 * X),
          2 * ((1 / h₁) * ∫ u in x..(x + h₁), ‖tailTr A α β (X / 2) u‖ ^ 2))
        = 2 * ∫ x in X..(2 * X), ((1 / h₁) * ∫ u in x..(x + h₁),
            ‖tailTr A α β (X / 2) u‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    have e2 : (∫ x in X..(2 * X),
          2 * ((1 / h₂) * ∫ u in x..(x + h₂), ‖tailTr A α β (X / 2) u‖ ^ 2))
        = 2 * ∫ x in X..(2 * X), ((1 / h₂) * ∫ u in x..(x + h₂),
            ‖tailTr A α β (X / 2) u‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    rw [intervalIntegral.integral_add hi1 hi2, e1, e2]
    have b1 := xavg_window_le hX hh1 hh1X hGrc hGrnn
    have b2 := xavg_window_le hX hh2 hh2X hGrc hGrnn
    linarith
  -- the separation, on the regularized transform
  have hsep : (∫ u in X..(3 * X), ‖tailTr A α β (X / 2) u‖ ^ 2)
      ≤ 41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2 := by
    have hc : (∫ u in X..(3 * X), ‖tailTr A α β (X / 2) u‖ ^ 2)
        = ∫ u in X..(3 * X), ‖tailT A α β u‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 3 * X), Set.mem_Icc] at hu
      rw [tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)]
    rw [hc]
    exact tailT_mean_sq_bound hA hX hab
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  have hfin : (1 / X) * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β‖ ^ 2)
      ≤ (1 / X) * (4 * (41 * X * Real.pi * ∫ t in α..β, ‖A t‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left (hmaj.trans ?_) hXinv.le
    linarith
  refine hfin.trans (le_of_eq ?_)
  field_simp
  ring

end Salt.MR
