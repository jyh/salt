/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Lemma14Vtail

/-!
# S8 MR-CORE, node A3a — Lemma 14, THE ASSEMBLY (stone S-E)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 21–23 (Lemma 14; frozen statement transcribed in `Salt.MR.ParsevalSL`).

This file joins the four landed stones of the Lemma-14 ladder:

* **S-A** `Aperron_short_interval` / `Aperron_short_interval_collapsed` /
  `residue_diff_eq_shortInterval` (`Lemma14Bridge`) — the finite-`T` Perron bridge.
* **S-B** `uSlab_taylor_main_sq` (`Lemma14Taylor`) — the `|t| ≤ T₀` slab, `(log X)^{−14/45}`.
* **S-C** `vtail_mean_sq_bound` (`Lemma14Vtail`) — the per-segment `x`-averaged mean square,
  `≤ 164π·∫_α^β ‖A(1+it)‖²`, log-free.
* **S-D** `dyadic_tail_block` / `dyadic_tail_proper` (`Lemma14Bridge`) — the weighted
  max-term machinery (see the truncation page below for why only its `N = 1` instance is
  reachable from the landed separation).

## The truncation page (worked FIRST — `Tcut = 2X/h₁` is forced, not chosen)

Write `W := X/h₁`, `T₀ := (log X)^{1/45}`, `A(1+it) = ∑_{m∈s0} aₘ/m^{1+it}` (`dpolyA`).

The landed separation `vtail_mean_sq_bound` carries **no kernel decay**: its Cauchy–Schwarz
step (`vSeg_diff_sq_le`, `‖(1/h)∫_x^{x+h}F‖² ≤ (1/h)∫_x^{x+h}‖F‖²`) discards precisely the
oscillation of the short window average that manufactures MR's `min(hⱼ/x, 2/|t|)` factor.
Consequently the far arm can only be paid for by the *raw* mean square `∫‖A‖²`, and the
weighted-sup datum

`hMsup : ∀ T ≥ X/h₁, ((X/h₁)/T)·∫_{T ≤ |t| ≤ 2T} ‖A(1+it)‖² ≤ Msup`

gives `∫_{2^k W}^{2^{k+1} W} ‖A‖² ≤ 2^k·Msup`, whose dyadic sum over `k < N` is
`(2^N − 1)·Msup` — **divergent in `N`**.  Only the single block `k = 0` is affordable, where
the weight is `W/W = 1` and the block bound is exactly `Msup`.  Hence the Perron truncation
is pinned at

`Tcut := 2·(X/h₁)`,

and Lemma 14's third term is consumed at its single cheapest instance `T = X/h₁`.  Going
beyond one block needs a *kernel-carrying* Schur bound — i.e. `∫ ‖A(1+it)‖²·(min b (2/t))² dt`
in place of `∫ ‖A‖²` — which is what `dyadic_tail_proper` consumes but which the `V`-object
exit does not produce.  That is a **named residual** (`A3a-R3`, the kernel-weighted
separation); the two cheap dodges both lose:
`(∫‖A‖k)² ≤ (∫‖A‖²k)(∫k)` gives `N·Msup/W`, and `(∫‖A‖k)² ≤ (∫‖A‖²k²)(Tcut−W)` carries the
segment length.

## The Perron defect (why the `Sⱼ` form carries `Eper`)

At `c = 1` the landed truncation error is
`E(T) = 2·(12(π + 2·log(1+T)) + (32X/T)·(1 + log 3X))` (`Aperron_short_interval_collapsed`).
The first piece is the near-diagonal (`m ≈ y`) zone-1 loss; it **grows** with `T` and never
vanishes, while the second needs `T` large.  No `T` makes `E(T)` small — this is the classical
truncated-Perron boundary loss.  MR sidestep it with the exact (`T = ∞`, conditionally
convergent) Perron formula, which is the **un-landed** residual `A3a-R1`
(`ParsevalSL` docstring, item 1).  So the honest `Sⱼ` statement carries the defect as a named
datum: `lemma14_shortInterval_of_perron` takes `hPerron` with bound `Eper` and returns the
frozen right-hand side plus `Eper²`; `perron_gap_collapsed` discharges `hPerron` at any finite
`T` with the explicit `E(T)` (under the boundary guards and `x + hⱼ ≤ 2X`).

## What lands here

* `lemma14_contour` — **the assembly**, on the truncated contour object at `Tcut = 2X/h₁`:
  `(1/X)∫_X^{2X}‖(1/h₁)P₁(x) − (1/h₂)P₂(x)‖² dx`
  `  ≤ 2000·(log X)^{−14/45} + 820π·(∫_{T₀ ≤ |t| ≤ X/h₁}‖A(1+it)‖²) + 820π·Msup`,
  with `Pⱼ(x) = uSlab (dpolyA a s0) x hⱼ (2X/h₁)`.  All three frozen terms, absolute
  constants.
* `lemma14_contour_grouped` — the same in the frozen `≪` shape, constant `2000 + 820π`.
* `shortSum`, `perron_gap_collapsed` — the (half-open) `Sⱼ(x) = ∑_{x < m ≤ x+hⱼ} aₘ` and the
  explicit finite-`T` Perron defect for the *weighted difference*.
* `perron_guards_ae`, `shortSum_diff_sq_intervalIntegrable` — the two side conditions of the
  `Sⱼ` form, both **discharged**: the boundary guards fail only on a null (finite) set, and
  `x ↦ ‖(1/h₁)S₁ − (1/h₂)S₂‖²` is a bounded measurable step function, hence integrable.
* `lemma14_shortInterval_of_perron` — the frozen `Sⱼ` conclusion, modulo `Eper²`.

**The exact delta from the frozen statement.**  Two, both named and both upstream of this
file: (i) the truncation `Tcut = 2X/h₁` in place of MR's `T = ∞` — forced by the missing
kernel-carrying separation (`A3a-R3`); (ii) the Perron defect `Eper` on the `Sⱼ` form —
forced by the missing exact critical-line Perron representation (`A3a-R1`).  Nothing else:
the three right-hand terms, the `(log X)^{−14/45}` exponent, the mid-range `∫_{T₀ ≤ |t| ≤ X/h₁}`
and the `(X/h₁)/T`-weighted max-term are all present with absolute constants.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## E0 — elementary scaffolding -/

/-- The coefficient mass of an `[X, 4X]`-supported index set: `∑_{m ∈ s0} 1/m ≤ 5`.
(`s0 ⊆ [0, ⌊4X⌋]` gives `card ≤ 4X + 1`, and each term is `≤ 1/X`.) -/
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

/-- `‖z₁+z₂+z₃+z₄+z₅‖² ≤ 5·(‖z₁‖²+⋯+‖z₅‖²)` — the five-way triangle/AM–QM step. -/
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

/-! ## E1 — the frequency split of the truncated Perron object -/

/-- The `U`-slab at truncation `T` IS the `V`-segment on `[−T, T]` (same normalization). -/
private lemma uSlab_eq_vSeg (A : ℝ → ℂ) (x h T : ℝ) : uSlab A x h T = vSeg A x h (-T) T := rfl

/-- Adjacent frequency segments add. -/
private lemma vSeg_add_adjacent {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (p q r : ℝ) :
    vSeg A x h p q + vSeg A x h q r = vSeg A x h p r := by
  have hc : Continuous (fun t : ℝ => A t * uKernel x h t) :=
    hA.mul (uKernel_continuous hx hxh)
  rw [vSeg, vSeg, vSeg, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]

/-- **The five-way frequency split** of the truncated Perron object:
`[−Tc, Tc] = [−Tc, −W] ∪ [−W, −T₀] ∪ [−T₀, T₀] ∪ [T₀, W] ∪ [W, Tc]`. -/
private lemma vSeg_split_five {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (T₀ W Tc : ℝ) :
    vSeg A x h (-Tc) Tc
      = vSeg A x h (-Tc) (-W) + vSeg A x h (-W) (-T₀) + vSeg A x h (-T₀) T₀
        + vSeg A x h T₀ W + vSeg A x h W Tc := by
  have e : ∀ p q r : ℝ, vSeg A x h p q + vSeg A x h q r = vSeg A x h p r :=
    fun p q r => vSeg_add_adjacent hA hx hxh p q r
  rw [← e (-Tc) W Tc, ← e (-Tc) T₀ W, ← e (-Tc) (-T₀) T₀, ← e (-Tc) (-W) (-T₀)]

/-! ## E2 — the regularized weighted `V`-difference (continuity in `x`) -/

/-- The weighted `V`-difference on a frequency segment, written through the `max`-regularized
tail transform `tailTr` — globally continuous in `x`, and equal to the honest
`(1/h₁)·vSeg − (1/h₂)·vSeg` for `x ≥ X` (`vdiffR_eq`).  This is the device that makes every
`x`-integral in the assembly interval-integrable. -/
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

/-- The `x`-integrability of the squared weighted Perron difference (through `vdiffR`). -/
private lemma uSlab_diff_sq_integrable {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (T : ℝ) :
    IntervalIntegrable (fun x : ℝ =>
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ T - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ T‖ ^ 2)
      volume X (2 * X) := by
  have hc : Continuous (fun x : ℝ => ‖vdiffR A X h₁ h₂ (-T) T x‖ ^ 2) :=
    ((vdiffR_continuous hA hX h₁ h₂ (-T) T).norm).pow 2
  refine (hc.intervalIntegrable X (2 * X)).congr (fun x hx => ?_)
  rw [Set.uIoc_of_le (by linarith : X ≤ 2 * X), Set.mem_Ioc] at hx
  rw [vdiffR_eq hA hX hx.1.le hh1.le hh2.le, uSlab_eq_vSeg, uSlab_eq_vSeg]

/-! ## E3 — the split, integrated -/

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

/-! ## E4 — THE ASSEMBLY (contour form) -/

/-- **Lemma 14, the assembly (contour form).**  With `T₀ = (log X)^{1/45}`, `W = X/h₁` and the
forced truncation `Tcut = 2X/h₁` (see the file docstring), the `x`-averaged mean square of the
weighted difference of the truncated Perron objects obeys the three-term frozen bound

`(1/X)∫_X^{2X} ‖(1/h₁)P₁(x) − (1/h₂)P₂(x)‖² dx`
`  ≤ 2000·(log X)^{−14/45} + 820π·∫_{T₀ ≤ |t| ≤ X/h₁} ‖A(1+it)‖² dt + 820π·Msup`,

with `Pⱼ(x) = uSlab (dpolyA a s0) x hⱼ (2X/h₁)` (`ParsevalAsm`'s `I·∫` normalization) and
`Msup` the weighted max-term datum of the frozen statement.  Chain: five-way frequency split
→ `‖·‖² ≤ 5∑‖·‖²` → S-B on the slab (`x`-uniform), S-C on the four `V`-segments, and `hMsup`
at `T = X/h₁` on the two far blocks.  Constants absolute (`∑_{m∈s0} 1/m ≤ 5`). -/
theorem lemma14_contour (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ h₂ Msup : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
      ≤ 2000 * (Real.log X) ^ (-(14 / 45 : ℝ))
        + 820 * Real.pi * ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁),
              ‖dpolyA a s0 t‖ ^ 2)
            + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
        + 820 * Real.pi * Msup := by
  -- E4.0 — the arithmetic environment
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
  have hT0pos : (0 : ℝ) < (Real.log X) ^ (1 / 45 : ℝ) := Real.rpow_pos_of_pos hLp _
  -- E4.1 — `T₀ ≤ W = X/h₁`
  have hT0W : (Real.log X) ^ (1 / 45 : ℝ) ≤ X / h₁ := by
    have hstep1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h₂ := by
      rw [le_div_iff₀ hh2']
      have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
      calc (Real.log X) ^ (1 / 5 : ℝ) * h₂
          ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hh2X hL5
        _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
        _ = X := by rw [← Real.rpow_add hLp]; norm_num
    have hstep3 : X / h₂ ≤ X / h₁ := by gcongr
    linarith
  -- E4.2 — the two far blocks are paid by `Msup` (the single affordable dyadic instance)
  have hMsupW := hMsup (X / h₁) le_rfl
  rw [div_self hWpos.ne', one_mul] at hMsupW
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  -- E4.3 — S-C: every `V`-segment
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
  -- E4.4 — S-B: the slab, `x`-uniform
  have hSB : 1 / X * (∫ x in X..(2 * X),
      ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
        ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2) ≤ 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by
    have hs5 : (∑ m ∈ s0, 1 / (m : ℝ)) ≤ 5 := coeff_sum_inv_le (by linarith) s0 hrange
    have hs0 : (0 : ℝ) ≤ ∑ m ∈ s0, 1 / (m : ℝ) := Finset.sum_nonneg fun m _ => by positivity
    have hsq25 : (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 ≤ 25 := by nlinarith
    have hLnn : (0 : ℝ) ≤ (Real.log X) ^ (-(14 / 45 : ℝ)) := Real.rpow_nonneg hLp.le _
    have hpt : ∀ x ∈ Set.Icc X (2 * X),
        ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
          ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2
          ≤ 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le, ← uSlab_eq_vSeg, ← uSlab_eq_vSeg]
      refine le_trans (uSlab_taylor_main_sq a s0 hX1 hx.1 hh1 hh12 hh2X hpos ha) ?_
      calc 16 * (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 * (Real.log X) ^ (-(14 / 45 : ℝ))
          ≤ 16 * 25 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by gcongr
        _ = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by norm_num
    have hmono := intervalIntegral.integral_mono_on (by linarith : X ≤ 2 * X)
      (((vdiffR_continuous hAc hXpos h₁ h₂ _ _).norm).pow 2 |>.intervalIntegrable _ _)
      (_root_.intervalIntegrable_const (μ := volume)) hpt
    have heval : (∫ _x in X..(2 * X), (400 * (Real.log X) ^ (-(14 / 45 : ℝ))))
        = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) * X := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [heval] at hmono
    calc 1 / X * (∫ x in X..(2 * X),
          ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
            ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2)
        ≤ 1 / X * (400 * (Real.log X) ^ (-(14 / 45 : ℝ)) * X) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by field_simp
  -- E4.5 — assemble
  have hstep := five_split_integral_bound hAc hXpos hh1' hh2'
    ((Real.log X) ^ (1 / 45 : ℝ)) (X / h₁) (2 * (X / h₁))
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / X)
  have hb1 := hSC (-(2 * (X / h₁))) (-(X / h₁)) (by linarith)
  have hb2 := hSC (-(X / h₁)) (-((Real.log X) ^ (1 / 45 : ℝ))) (by linarith)
  have hb4 := hSC ((Real.log X) ^ (1 / 45 : ℝ)) (X / h₁) hT0W
  have hb5 := hSC (X / h₁) (2 * (X / h₁)) (by linarith)
  have hfar : 820 * Real.pi * ((∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2)
      ≤ 820 * Real.pi * Msup :=
    mul_le_mul_of_nonneg_left hMsupW (by positivity)
  nlinarith [hmul, hb1, hb2, hb4, hb5, hSB, hfar]

/-- **Lemma 14, the assembly — grouped (`≪`) form.**  The same bound with a single absolute
constant `C = 2000 + 820π`, matching the frozen right-hand side's shape. -/
theorem lemma14_contour_grouped (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ h₂ Msup : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
      ≤ (2000 + 820 * Real.pi) * ((Real.log X) ^ (-(14 / 45 : ℝ))
          + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + Msup) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hWpos : (0 : ℝ) < X / h₁ := div_pos hXpos hh1'
  have hLnn : (0 : ℝ) ≤ (Real.log X) ^ (-(14 / 45 : ℝ)) := Real.rpow_nonneg hLp.le _
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hT0pos : (0 : ℝ) < (Real.log X) ^ (1 / 45 : ℝ) := Real.rpow_pos_of_pos hLp _
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hT0W : (Real.log X) ^ (1 / 45 : ℝ) ≤ X / h₁ := by
    have hstep1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
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
  have hmid1 : (0 : ℝ) ≤ ∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁),
      ‖dpolyA a s0 t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT0W (fun t _ => by positivity)
  have hmid2 : (0 : ℝ) ≤ ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))),
      ‖dpolyA a s0 t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hMsupW := hMsup (X / h₁) le_rfl
  rw [div_self hWpos.ne', one_mul] at hMsupW
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  have hmain := lemma14_contour a s0 hX hh1 hh12 hh2X ha hrange hMsup
  nlinarith [hmain, Real.pi_pos, hLnn, hmid1, hmid2, hMnn]

/-! ## E5 — the `Sⱼ` form, modulo the Perron defect -/

/-- The **half-open short-interval sum** `Sⱼ(x) = ∑_{x < m ≤ x+h} aₘ` — `Lemma14Bridge`'s
boundary convention (`residue_diff_eq_shortInterval`); under the guards `(m:ℝ) ≠ x`,
`(m:ℝ) ≠ x+h` it agrees with MR's printed closed convention. -/
def shortSum (a : ℕ → ℂ) (s0 : Finset ℕ) (x h : ℝ) : ℂ :=
  ∑ m ∈ s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h), a m

/-- **The Perron defect of the weighted difference, explicit at finite `T`.**  Combining
`Aperron_short_interval_collapsed` (both `hⱼ`) with `residue_diff_eq_shortInterval`, and using
`1/hⱼ ≤ 1`:
`‖(1/h₁)P₁ − (1/h₂)P₂ − 2πi·((1/h₁)S₁ − (1/h₂)S₂)‖ ≤ 4·(12(π+2log(1+T)) + (32X/T)(1+log 3X))`.
This is the *honest* discharge of `lemma14_shortInterval_of_perron`'s hypothesis; note the
bound does **not** tend to `0` in `T` (see the file docstring: the exact Perron representation
`A3a-R1` is un-landed). -/
theorem perron_gap_collapsed (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h₁ h₂ T : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hT : 0 < T)
    (hx : X ≤ x) (hxh1 : x + h₁ ≤ 2 * X) (hxh2 : x + h₂ ≤ 2 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
      ≤ 4 * (12 * (Real.pi + 2 * Real.log (1 + T))
          + (32 * X / T) * (1 + Real.log (3 * X))) := by
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hobj : ∀ h : ℝ, uSlab (dpolyA a s0) x h T
      = I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
              - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)) / ((1 : ℂ) + (v : ℂ) * I) := by
    intro h
    rw [uSlab]
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    simp only [dpolyA, uKernel]
    rw [mul_div_assoc]
  have hgap : ∀ h : ℝ, 1 ≤ h → x + h ≤ 2 * X → (∀ m ∈ s0, (m : ℝ) ≠ x + h) →
      ‖uSlab (dpolyA a s0) x h T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h‖
        ≤ 2 * (12 * (Real.pi + 2 * Real.log (1 + T))
            + (32 * X / T) * (1 + Real.log (3 * X))) := by
    intro h hh hxh hne
    have hh0 : (0 : ℝ) < h := by linarith
    have hcol := Aperron_short_interval_collapsed a s0 hX hh0 hT hx hxh ha hrange hne_x hne
    rw [hobj h]
    simp only [shortSum]
    rw [← residue_diff_eq_shortInterval a s0 hh0 hpos hne_x hne]
    exact hcol
  have hg1 := hgap h₁ hh1 hxh1 hne_1
  have hg2 := hgap h₂ hh2 hxh2 hne_2
  have hkey : ((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
      = ((1 / h₁ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₁ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₁)
        - ((1 / h₂ : ℝ) : ℂ)
          * (uSlab (dpolyA a s0) x h₂ T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h₂) := by
    ring
  rw [hkey]
  have hn1 : ‖((1 / h₁ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₁),
      div_le_one (by linarith)]
    linarith
  have hn2 : ‖((1 / h₂ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₂),
      div_le_one (by linarith)]
    linarith
  have hmulle : ∀ (c g : ℂ) (B : ℝ), ‖c‖ ≤ 1 → ‖g‖ ≤ B → ‖c * g‖ ≤ B := by
    intro c g B hc hg
    rw [norm_mul]
    calc ‖c‖ * ‖g‖ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖g‖ := one_mul _
      _ ≤ B := hg
  refine le_trans (norm_sub_le _ _) ?_
  have p1 := hmulle _ _ _ hn1 hg1
  have p2 := hmulle _ _ _ hn2 hg2
  linarith

/-! ## E6 — the short-interval sum is a bounded step function -/

/-- `x ↦ Sⱼ(x)` is measurable: it is the finite sum of the indicators of the windows
`[m − h, m)` weighted by `aₘ`. -/
private lemma shortSum_measurable (a : ℕ → ℂ) (s0 : Finset ℕ) (h : ℝ) :
    Measurable (fun x : ℝ => shortSum a s0 x h) := by
  have hset : ∀ m : ℕ, {x : ℝ | x < (m : ℝ) ∧ (m : ℝ) ≤ x + h}
      = Set.Ico ((m : ℝ) - h) (m : ℝ) := by
    intro m
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  simp only [shortSum, Finset.sum_filter]
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Measurable.ite (by rw [hset m]; exact measurableSet_Ico) measurable_const
    measurable_const

/-- The trivial uniform bound `‖Sⱼ(x)‖ ≤ ∑_{m ∈ s0} ‖aₘ‖`. -/
private lemma shortSum_norm_le (a : ℕ → ℂ) (s0 : Finset ℕ) (x h : ℝ) :
    ‖shortSum a s0 x h‖ ≤ ∑ m ∈ s0, ‖a m‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m _ _ => norm_nonneg _)

/-- A bounded measurable real function is interval-integrable. -/
private lemma bounded_measurable_intervalIntegrable {f : ℝ → ℝ} {C : ℝ} (p q : ℝ)
    (hm : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable f volume p q :=
  ⟨MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).1
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb),
   MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).2
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)⟩

/-- **The boundary guards are null.**  `Aperron_short_interval`'s guards `(m:ℝ) ≠ x`,
`(m:ℝ) ≠ x + hⱼ` (`m ∈ s0`) hold for almost every `x` under any atomless measure — they fail
only on the finite set `⋃_{m ∈ s0} {m, m − h₁, m − h₂}`.  This is what lets
`perron_gap_collapsed` feed `lemma14_shortInterval_of_perron`'s a.e. hypothesis. -/
theorem perron_guards_ae (s0 : Finset ℕ) (h₁ h₂ : ℝ) (μ : Measure ℝ) [NoAtoms μ] :
    ∀ᵐ x ∂μ, (∀ m ∈ s0, (m : ℝ) ≠ x) ∧ (∀ m ∈ s0, (m : ℝ) ≠ x + h₁)
      ∧ ∀ m ∈ s0, (m : ℝ) ≠ x + h₂ := by
  have hpt : ∀ c : ℝ, ∀ᵐ x ∂μ, c ≠ x := by
    intro c
    rw [MeasureTheory.ae_iff]
    have hs : {x : ℝ | ¬ c ≠ x} = {c} := by ext x; simp [eq_comm]
    rw [hs, measure_singleton]
  have hshift : ∀ (c d : ℝ), ∀ᵐ x ∂μ, c ≠ x + d := by
    intro c d
    filter_upwards [hpt (c - d)] with x hx
    intro hc
    exact hx (by linarith [hc])
  have h0 : ∀ᵐ x ∂μ, ∀ m ∈ s0, (m : ℝ) ≠ x := by
    rw [Filter.eventually_all_finset]
    exact fun m _ => hpt (m : ℝ)
  have h1 : ∀ᵐ x ∂μ, ∀ m ∈ s0, (m : ℝ) ≠ x + h₁ := by
    rw [Filter.eventually_all_finset]
    exact fun m _ => hshift (m : ℝ) h₁
  have h2 : ∀ᵐ x ∂μ, ∀ m ∈ s0, (m : ℝ) ≠ x + h₂ := by
    rw [Filter.eventually_all_finset]
    exact fun m _ => hshift (m : ℝ) h₂
  filter_upwards [h0, h1, h2] with x g0 g1 g2
  exact ⟨g0, g1, g2⟩

/-- **The `Sⱼ` side condition, discharged.**  The squared weighted short-interval difference is
interval-integrable on every interval: it is a bounded measurable step function. -/
theorem shortSum_diff_sq_intervalIntegrable (a : ℕ → ℂ) (s0 : Finset ℕ) {h₁ h₂ : ℝ}
    (hh1 : 0 < h₁) (hh2 : 0 < h₂) (p q : ℝ) :
    IntervalIntegrable (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) volume p q := by
  have hm : Measurable (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
      - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) :=
    ((((shortSum_measurable a s0 h₁).const_mul _).sub
      ((shortSum_measurable a s0 h₂).const_mul _)).norm).pow_const 2
  have hSnn : (0 : ℝ) ≤ ∑ m ∈ s0, ‖a m‖ := Finset.sum_nonneg fun m _ => norm_nonneg _
  have hb : ∀ x : ℝ, ‖‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
      - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2‖
      ≤ ((1 / h₁ + 1 / h₂) * ∑ m ∈ s0, ‖a m‖) ^ 2 := by
    intro x
    have hc1 : ‖((1 / h₁ : ℝ) : ℂ)‖ = 1 / h₁ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₁)]
    have hc2 : ‖((1 / h₂ : ℝ) : ℂ)‖ = 1 / h₂ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h₂)]
    have hd : ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖
        ≤ (1 / h₁ + 1 / h₂) * ∑ m ∈ s0, ‖a m‖ := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul, hc1, hc2]
      have b1 := shortSum_norm_le a s0 x h₁
      have b2 := shortSum_norm_le a s0 x h₂
      have p1 : (0 : ℝ) < 1 / h₁ := by positivity
      have p2 : (0 : ℝ) < 1 / h₂ := by positivity
      nlinarith [b1, b2, p1, p2]
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  exact bounded_measurable_intervalIntegrable p q hm hb

/-- **Lemma 14 in the frozen `Sⱼ` form, modulo the Perron defect.**  Given the Perron gap
datum `Eper` (discharged at finite `T` by `perron_gap_collapsed`; `Eper = 0` exactly when the
un-landed exact representation `A3a-R1` is supplied),

`(1/X)∫_X^{2X} |(1/h₁)S₁(x) − (1/h₂)S₂(x)|² dx`
`  ≤ (1/2π²)·( C·((log X)^{−14/45} + ∫_{T₀ ≤ |t| ≤ X/h₁}|A(1+it)|² + Msup) + Eper² )`,
`C = 2000 + 820π`.  The Perron datum is required only **almost everywhere** on `[X, 2X]`,
which is exactly what `perron_gap_collapsed` supplies: its boundary guards `(m:ℝ) ≠ x`,
`(m:ℝ) ≠ x + hⱼ` fail only on the finite set `⋃_{m ∈ s0} {m, m−h₁, m−h₂}`.  (A pointwise
hypothesis converts with `ae_restrict_of_forall_mem measurableSet_Icc`.) -/
theorem lemma14_shortInterval_of_perron (a : ℕ → ℂ) (s0 : Finset ℕ)
    {X h₁ h₂ Msup Eper : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup)
    (hPerron : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))),
      ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖ ≤ Eper) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * ((2000 + 820 * Real.pi) * ((Real.log X) ^ (-(14 / 45 : ℝ))
          + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + Msup) + Eper ^ 2) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  -- the pointwise transfer `2π‖ΔS‖ ≤ ‖ΔP‖ + Eper`
  have hnormI : ∀ z : ℂ, ‖2 * (Real.pi : ℂ) * I * z‖ = 2 * Real.pi * ‖z‖ := by
    intro z
    have hre : 2 * (Real.pi : ℂ) * I * z = ((2 * Real.pi : ℝ) : ℂ) * (I * z) := by
      push_cast; ring
    rw [hre, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hpt : (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] fun x : ℝ => 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2
          + Eper ^ 2) := by
    filter_upwards [hPerron] with x hgap
    have hsplit : 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
        = (((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁)))
          - (((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))
              - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
                  - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)) := by ring
    have htri : 2 * Real.pi * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖
        ≤ ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ + Eper := by
      rw [← hnormI, hsplit]
      exact le_trans (norm_sub_le _ _) (by linarith [hgap])
    have hSnn : (0 : ℝ) ≤ ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ := norm_nonneg _
    have hPnn : (0 : ℝ) ≤ ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.pi
      * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖) htri 2
    rw [show (1 : ℝ) / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + Eper ^ 2)
        = (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + Eper ^ 2)
          / (2 * Real.pi ^ 2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)]
    nlinarith [hsq, hpi, sq_nonneg (‖((1 / h₁ : ℝ) : ℂ)
      * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
      - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ - Eper)]
  -- integrate the pointwise transfer
  have hPint := uSlab_diff_sq_integrable hAc hXpos hh1' hh2' (2 * (X / h₁))
  have hRint : IntervalIntegrable (fun x : ℝ => 1 / (2 * Real.pi ^ 2)
      * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + Eper ^ 2))
      volume X (2 * X) := (hPint.add _root_.intervalIntegrable_const).const_mul _
  have hSint := shortSum_diff_sq_intervalIntegrable a s0 hh1' hh2' X (2 * X)
  have hmono := intervalIntegral.integral_mono_ae_restrict (by linarith : X ≤ 2 * X)
    hSint hRint hpt
  have heval : (∫ x in X..(2 * X), 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + Eper ^ 2))
      = 1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
        + Eper ^ 2 * X) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hPint _root_.intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heval] at hmono
  have hXne : X ≠ 0 := hXpos.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hstep1 : 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2) + Eper ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / X)
    calc 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
        ≤ 1 / X * (1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
          + Eper ^ 2 * X)) := h1
      _ = 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
          + Eper ^ 2) := by field_simp
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith [lemma14_contour_grouped a s0 hX hh1 hh12 hh2X ha hrange hMsup]

end Salt.MR
