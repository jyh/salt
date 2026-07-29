/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronLimit

/-!
# S8 MR-CORE, node A3a-R1 — the Perron gap in MEAN SQUARE (the `x`-uniform exit)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7, pp. 21–23.

`Salt.MR.PerronLimit` landed the *per-point* Perron limit (`perron_gap_le_of_T`: the Lemma-14
gap at fixed `x` is `≤ C(x)/T → 0`) and named the residual it could not reach: the constant
`C(x) = ∑ₘ ‖aₘ‖·2(x/m)/|log(x/m)|` blows up as `x` approaches a support integer, so no single
`T` serves a.e. `x ∈ [X,2X]` at once.  This file supplies the `x`-uniform version **in mean
square**, which is what the Lemma-14 consumer actually needs.

## The trap (banked by R1-LIMIT, and it is real)

Squaring `perron_gap_le_of_T` and integrating **diverges**: near a support integer `m₀`,
`C(x) ≍ 2X/|x − m₀|`, so `C(x)²` is not locally integrable.  The correct route keeps the
`min`-device *inside* the `x`-integral, and pays the near-diagonal `BIG` branch as a **mass**
rather than as a pointwise supremum.

## The mean-square page (worked first; the honest exponents)

Write `BIG = π + 2log(1+T)` and `M(y) = ∑_{m ∈ s0} min(BIG, 1/(T|log(y/m)|))`.  The Lemma-14
gap at `x` is `≤ 6·(M(x+h₁) + M(x+h₂) + 2M(x))` (`perron_gap_le_minDev`; the `2(y/m) ≤ 6`
rescale of the wide range, `1/hⱼ ≤ 1`).

Split each `M(y)` at a **free width** `0 < δ ≤ 1` (`zone_min_sum_split`):

| band | count | cost per term | total |
|---|---|---|---|
| `\|y−m\| < δ` | ≤ 3 | `BIG` | the bump `nearBump m δ BIG y` |
| `δ ≤ \|y−m\| < 1` | ≤ 3 | `(4X/T)/δ` | `12X/(Tδ)` |
| `\|y−m\| ≥ 1` | harmonic | `(4X/T)/dist` | `(8X/T)(1 + log 3X)` |

The first band is the whole point: as a function of `y` it is a bump of height `BIG` and width
`2δ`, so its **mass** is `2δ·BIG` per index — and shifting `y = x + hⱼ` only moves the centre
(`nearBump_shift`), so the same mass bound survives the three shifts with no change of
variables.  With `|s0| ≤ 4X + 1` and `K := 12X/(Tδ) + (8X/T)(1 + log 3X)`:

`(1/X)∫_X^{2X} gapMaj(x)² dx ≤ 34560·δ·BIG² + 1152·K²`   (`gapMaj_meansq_le`),

using `(6Q + 24K)² ≤ 72Q² + 1152K²` and `Q ≤ 12·BIG` pointwise, so `Q² ≤ 12·BIG·Q` and only
the *first* power of `Q` is integrated.

**Rates.**  With `T = X·(log X)^B`, `δ = (log X)^{−a}` and `BIG ≍ log X =: L`, the bound is
`≍ L^{2−a} + L^{2(a−B)} + L^{2(1−B)}`; balancing `2 − a = 2(a − B)` gives `a = (2+2B)/3` and
the value `L^{(4−2B)/3}`, which is `≤ L^{−A}` exactly when `B ≥ 2 + 3A/2`.  Lemma 14's main
term is `L^{−14/45}`, so `B ≥ 2 + 1/5` suffices.  The parameter-free version is
`gapMaj_meansq_sqrt` (`δ = √(X/T)`, admissible for `T ≥ X`), whose right-hand side
`34560·√(X/T)·BIG² + 1152·(12√(X/T) + (8X/T)(1+log 3X))²` **tends to `0` as `T → ∞`**.

## What lands here

* `nearBump`, `nearBump_shift`, `nearBump_integral_le` — the bump and its mass `2δB`.
* `zone_min_sum_far_le` (X2) — the `|y−m| ≥ 1` band, extracted standalone from
  `zone_min_sum_le_wide`'s internal `hfar`.
* `zone_min_sum_split` (X1) — the three-band split at the free width `δ`.
* `perron_gap_le_minDev` — the Lemma-14 gap, uncollapsed.
* `gapMaj`, `perron_gap_le_gapMaj`, `gapMaj_meansq_le` (X3) — **THE STONE**: the explicit
  majorant and its `x`-mean square, at general `T` and general `δ`.
* `gapMaj_meansq_sqrt` — the shrinking instance `δ = √(X/T)`.
* `lemma14_shortInterval_meansq` (X4) — the consumer exit: Lemma 14's frozen `Sⱼ`
  conclusion with the Perron defect entering as `Egap ≥ (1/X)∫G²` instead of as a pointwise
  `Eper²`.  Setting `G ≡ Eper` recovers `lemma14_shortInterval_of_perron`.
* `lemma14_shortInterval_meansq_concrete` — every hypothesis discharged, at the pinned
  `T = 2X/h₁` and any `0 < δ ≤ 1`.

## The `T`-pin finding (the residual this file *cannot* remove)

At the truncation `lemma14_contour` forces (`Tcut = 2X/h₁ ≤ 2X`, see that file's truncation
page) one has `X/T = h₁/2`, so the far-band cost is `K ≥ 4h₁(1 + log 3X)` — **independent of
`δ`, and irreducible**.  Hence `lemma14_shortInterval_meansq_concrete`'s `Egap` is of grade
`h₁²·log²X`, the same as `lemma14_shortInterval_concrete`'s `Eper²`: the mean-square device
kills the near-diagonal `log T` term for free, but the Perron defect can only be made to
*shrink* once the consumer admits `T ≫ X·(log X)²`.  That is now the sole obstruction, and it
lives in `lemma14_contour` (node `A3a-R3`, the kernel-weighted separation), not in the Perron
layer.  `gapMaj_meansq_le` / `gapMaj_meansq_sqrt` are stated at general `T` and are ready for
it.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## Part A — the near bump -/

/-- The height-`B` bump of half-width `δ` centred at `c`. -/
def nearBump (c δ B y : ℝ) : ℝ := if |y - c| < δ then B else 0

lemma nearBump_nonneg {c δ B y : ℝ} (hB : 0 ≤ B) : 0 ≤ nearBump c δ B y := by
  rw [nearBump]; split <;> [exact hB; exact le_rfl]

lemma nearBump_le {c δ B y : ℝ} (hB : 0 ≤ B) : nearBump c δ B y ≤ B := by
  rw [nearBump]; split <;> [exact le_rfl; exact hB]

/-- The bump is the indicator of the open interval `(c − δ, c + δ)`. -/
lemma nearBump_eq_indicator (c δ B : ℝ) :
    nearBump c δ B = Set.indicator (Set.Ioo (c - δ) (c + δ)) (fun _ => B) := by
  funext y
  rw [nearBump]
  by_cases hy : |y - c| < δ
  · rw [if_pos hy, Set.indicator_of_mem]
    rw [Set.mem_Ioo]
    rw [abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · rw [if_neg hy, Set.indicator_of_notMem]
    rw [Set.mem_Ioo]
    intro hc
    exact hy (abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩)

/-- Shifting the argument shifts the centre: `nearBump c δ B (x + h) = nearBump (c − h) δ B x`. -/
lemma nearBump_shift (c δ B h x : ℝ) :
    nearBump c δ B (x + h) = nearBump (c - h) δ B x := by
  rw [nearBump, nearBump]
  congr 2
  rw [show x + h - c = x - (c - h) by ring]

lemma nearBump_measurable (c δ B : ℝ) : Measurable (nearBump c δ B) := by
  rw [nearBump_eq_indicator]
  exact (measurable_const.indicator measurableSet_Ioo)

/-- A bounded measurable real function is interval-integrable (the `Lemma14` device, re-derived
here because that file's copy is `private`). -/
lemma bdd_meas_intervalIntegrable {f : ℝ → ℝ} {C : ℝ} (p q : ℝ)
    (hm : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable f volume p q :=
  ⟨MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).1
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb),
   MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).2
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)⟩

lemma nearBump_intervalIntegrable {c δ B : ℝ} (hB : 0 ≤ B) (p q : ℝ) :
    IntervalIntegrable (nearBump c δ B) volume p q := by
  refine bdd_meas_intervalIntegrable (C := B) p q (nearBump_measurable c δ B) (fun y => ?_)
  rw [Real.norm_of_nonneg (nearBump_nonneg hB)]
  exact nearBump_le hB

/-- **The bump's mass**: `∫_p^q nearBump c δ B ≤ 2δB`. -/
lemma nearBump_integral_le {c δ B p q : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hpq : p ≤ q) :
    (∫ y in p..q, nearBump c δ B y) ≤ 2 * δ * B := by
  rw [intervalIntegral.integral_of_le hpq, nearBump_eq_indicator,
    MeasureTheory.setIntegral_indicator measurableSet_Ioo, MeasureTheory.setIntegral_const,
    smul_eq_mul]
  have hvol : volume (Set.Ioc p q ∩ Set.Ioo (c - δ) (c + δ)) ≤ ENNReal.ofReal (2 * δ) := by
    refine le_trans (measure_mono Set.inter_subset_right) ?_
    rw [Real.volume_Ioo]
    exact le_of_eq (by rw [show c + δ - (c - δ) = 2 * δ by ring])
  have h2 : (volume (Set.Ioc p q ∩ Set.Ioo (c - δ) (c + δ))).toReal ≤ 2 * δ := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol) ?_
    rw [ENNReal.toReal_ofReal (by linarith)]
  exact mul_le_mul_of_nonneg_right h2 hB

/-! ## Part B — the far band, standalone -/

/-- **X2 — the far band of the `min`-device sum**, extracted from `zone_min_sum_le_wide`'s
internal `hfar` step so that it can be re-used against a *finer* near/middle split.  For
`X ≤ x ≤ 4X` and an `[X,4X]`-supported index set,
`∑_{m : |x−m| ≥ 1} min(BIG, 1/(T|log(x/m)|)) ≤ (8X/T)(1 + log⌊3X⌋)`.
Two injective harmonic reindexings (`m − ⌈x⌉₊` on the right, `⌊x⌋₊ − m` on the left) into
`[1, ⌊3X⌋]`, each closed by `far_side_bound`. -/
theorem zone_min_sum_far_le (s0 : Finset ℕ) {X x T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hx : X ≤ x) (hx4 : x ≤ 4 * X)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
  rw [← Finset.sum_filter_add_sum_filter_not
      (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)) (fun m : ℕ => x + 1 ≤ (m : ℝ))]
  have hfpos : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
        (fun m : ℕ => x + 1 ≤ (m : ℝ)),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
    refine far_side_bound hX0 hT _ hN1 (fun m => m - ⌈x⌉₊) ?_ ?_ ?_ ?_
    · intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb
      have hca : ⌈x⌉₊ < a := by
        have := Nat.ceil_lt_add_one hx0.le
        have h' : (↑⌈x⌉₊ : ℝ) < ↑a := by linarith [ha.2]
        exact_mod_cast h'
      have hcb : ⌈x⌉₊ < b := by
        have := Nat.ceil_lt_add_one hx0.le
        have h' : (↑⌈x⌉₊ : ℝ) < ↑b := by linarith [hb.2]
        exact_mod_cast h'
      omega
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have := Nat.ceil_lt_add_one hx0.le
      have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
      have : ⌈x⌉₊ < m := by exact_mod_cast h'
      omega
    · intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
      have hc := Nat.ceil_lt_add_one hx0.le
      have hcm : ⌈x⌉₊ < m := by
        have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
        exact_mod_cast h'
      have hcast : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ 3 * X := by
        rw [Nat.cast_sub hcm.le]
        have := Nat.le_ceil x
        linarith
      exact Nat.le_floor hcast
    · intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
      have hm0 : (0 : ℝ) < m := by linarith
      have hcm : ⌈x⌉₊ < m := by
        have := Nat.ceil_lt_add_one hx0.le
        have h' : (↑⌈x⌉₊ : ℝ) < ↑m := by linarith [hm.2]
        exact_mod_cast h'
      have hD0 : (0 : ℝ) < ((m - ⌈x⌉₊ : ℕ) : ℝ) := by
        have : 0 < m - ⌈x⌉₊ := by omega
        exact_mod_cast this
      have hDdist : ((m - ⌈x⌉₊ : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
        rw [Nat.cast_sub hcm.le, abs_sub_comm, abs_of_nonneg (by linarith [hm.2])]
        have := Nat.le_ceil x
        linarith
      exact (min_le_right _ _).trans
        (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
  have hfneg : ∑ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (x / m)|))
      ≤ (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by
    have hle1 : ∀ m ∈ (s0.filter (fun m : ℕ => ¬ |x - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ (x + 1 ≤ (m : ℝ))), (m : ℝ) ≤ x - 1 := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      have hlt : (m : ℝ) < x + 1 := not_le.mp hm.2
      have hge : (1 : ℝ) ≤ |x - (m : ℝ)| := not_lt.mp hm.1.2
      have hxm1 : (1 : ℝ) ≤ x - (m : ℝ) := by
        by_contra hc
        have hlt2 : x - (m : ℝ) < 1 := not_le.mp hc
        have : |x - (m : ℝ)| < 1 := abs_lt.mpr ⟨by linarith, hlt2⟩
        linarith
      linarith
    refine far_side_bound hX0 hT _ hN1 (fun m => ⌊x⌋₊ - m) ?_ ?_ ?_ ?_
    · intro a ha b hb hab
      have hma : (a : ℝ) ≤ x - 1 := hle1 a ha
      have hmb : (b : ℝ) ≤ x - 1 := hle1 b hb
      have ha' : a + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hb' : b + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    · intro m hm
      have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
      have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    · intro m hm
      have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
      have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hcast : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ 3 * X := by
        rw [Nat.cast_sub (by omega)]
        have := Nat.floor_le hx0.le
        linarith
      exact Nat.le_floor hcast
    · intro m hm
      have hmx : (m : ℝ) ≤ x - 1 := hle1 m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
      have hm0 : (0 : ℝ) < m := by linarith
      have hm' : m + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      have hD0 : (0 : ℝ) < ((⌊x⌋₊ - m : ℕ) : ℝ) := by
        have : 0 < ⌊x⌋₊ - m := by omega
        exact_mod_cast this
      have hDdist : ((⌊x⌋₊ - m : ℕ) : ℝ) ≤ |x - (m : ℝ)| := by
        rw [Nat.cast_sub (by omega), abs_of_nonneg (by linarith)]
        have := Nat.floor_le hx0.le
        linarith
      exact (min_le_right _ _).trans
        (decay_le_of_dist hX0 hT hm0 hmhi hx0 (by linarith) hD0 hDdist)
  have heq8 : (8 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
      = (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ))
        + (4 * X / T) * (1 + Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ)) := by ring
  linarith [hfpos, hfneg, heq8]

/-! ## Part C — X1: the `δ`-split of the `min`-device sum -/

/-- **X1 — the near/middle/far split at threshold `δ`.**  For `X ≤ y ≤ 4X`, `0 < δ ≤ 1` and an
`[X,4X]`-supported index set,

`∑_{m ∈ s0} min(BIG, 1/(T|log(y/m)|)) ≤ ∑_{m ∈ s0} nearBump m δ BIG y + 12X/(Tδ)
  + (8X/T)(1 + log 3X)`.

Three bands: `|y−m| < δ` pays `BIG`, but only through the *bump* `nearBump m δ BIG`, whose
`y`-mass is `2δ·BIG` (this is what the mean square exploits); `δ ≤ |y−m| < 1` has at most
three integers, each `≤ (4X/T)/δ`; `|y−m| ≥ 1` is `zone_min_sum_far_le`.  Contrast
`zone_min_sum_le_wide`, which pays a *pointwise* `3·BIG` on the whole range — the term that
grows like `log T` and can never be made small at fixed `x`. -/
theorem zone_min_sum_split (s0 : Finset ℕ) {X y T δ : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hy : X ≤ y) (hy4 : y ≤ 4 * X)
    (hδ0 : 0 < δ)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
      ≤ (∑ m ∈ s0, nearBump (m : ℝ) δ (Real.pi + 2 * Real.log (1 + T)) y)
        + (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  -- the far band
  have hlogfloor : Real.log ((⌊3 * X⌋₊ : ℕ) : ℝ) ≤ Real.log (3 * X) := by
    have hfp : 1 ≤ ⌊3 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊3 * X⌋₊))
      (Nat.floor_le (by linarith))
  have hfar : ∑ m ∈ s0.filter (fun m : ℕ => ¬ |y - (m : ℝ)| < 1),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
      ≤ (8 * X / T) * (1 + Real.log (3 * X)) := by
    refine (zone_min_sum_far_le s0 hX hT hy hy4 hrange).trans ?_
    have h8 : (0 : ℝ) ≤ 8 * X / T := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h8
  -- the near band, split again at δ
  rw [← Finset.sum_filter_add_sum_filter_not s0 (fun m : ℕ => |y - (m : ℝ)| < 1),
    ← Finset.sum_filter_add_sum_filter_not (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1))
      (fun m : ℕ => |y - (m : ℝ)| < δ)]
  -- inner near: the bump dominates termwise
  have hnear : ∑ m ∈ (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
        (fun m : ℕ => |y - (m : ℝ)| < δ),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
      ≤ ∑ m ∈ s0, nearBump (m : ℝ) δ (Real.pi + 2 * Real.log (1 + T)) y := by
    have hstep : ∑ m ∈ (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
          (fun m : ℕ => |y - (m : ℝ)| < δ),
          min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
        ≤ ∑ m ∈ (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
          (fun m : ℕ => |y - (m : ℝ)| < δ),
          nearBump (m : ℝ) δ (Real.pi + 2 * Real.log (1 + T)) y := by
      refine Finset.sum_le_sum fun m hm => ?_
      simp only [Finset.mem_filter] at hm
      rw [nearBump, if_pos hm.2]
      exact min_le_left _ _
    refine hstep.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · exact fun m _ _ => nearBump_nonneg hBIG_nn
  -- inner middle: at most three integers, each with the decay branch at distance ≥ δ
  have hmid : ∑ m ∈ (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ |y - (m : ℝ)| < δ),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
      ≤ 12 * X / (T * δ) := by
    have hterm : ∀ m ∈ (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ |y - (m : ℝ)| < δ),
        min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))
          ≤ (4 * X / T) / δ := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨hmlo, hmhi⟩ := hrange m hm.1.1
      have hm0 : (0 : ℝ) < m := by linarith
      exact (min_le_right _ _).trans
        (decay_le_of_dist hX0 hT hm0 hmhi hy0 hy4 hδ0 (not_lt.mp hm.2))
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard : (((s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ |y - (m : ℝ)| < δ)).card : ℝ) ≤ 3 := by
      have hsub : (s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ |y - (m : ℝ)| < δ)
          ⊆ s0.filter (fun m : ℕ => |y - (m : ℝ)| ≤ 1) := by
        intro m hm
        simp only [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1.1, le_of_lt hm.1.2⟩
      have h1 : (((s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
          (fun m : ℕ => ¬ |y - (m : ℝ)| < δ)).card : ℝ)
          ≤ ((s0.filter (fun m : ℕ => |y - (m : ℝ)| ≤ 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 := zone_count_crossover s0 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ y)
      linarith
    have hpos4 : (0 : ℝ) ≤ (4 * X / T) / δ := by positivity
    have hfin : (((s0.filter (fun m : ℕ => |y - (m : ℝ)| < 1)).filter
        (fun m : ℕ => ¬ |y - (m : ℝ)| < δ)).card : ℝ) * ((4 * X / T) / δ)
        ≤ 3 * ((4 * X / T) / δ) := mul_le_mul_of_nonneg_right hcard hpos4
    have heq : (3 : ℝ) * ((4 * X / T) / δ) = 12 * X / (T * δ) := by
      field_simp; ring
    linarith
  linarith [hnear, hmid, hfar]

/-! ## Part D — the `min`-device gap, uncollapsed -/

/-- The per-point `min`-device sum `M(y) = ∑_{m ∈ s0} min(BIG, 1/(T|log(y/m)|))`. -/
def minDev (s0 : Finset ℕ) (T y : ℝ) : ℝ :=
  ∑ m ∈ s0, min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / (m : ℝ))|))

lemma minDev_nonneg (s0 : Finset ℕ) {T y : ℝ} (hT : 0 < T) : 0 ≤ minDev s0 T y := by
  refine Finset.sum_nonneg fun m _ => le_min ?_ (by positivity)
  have h1 := Real.pi_pos
  have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
  linarith

/-- The coefficient-weighted `min`-sum is `≤ 6·M(y)` on the wide range (`y/m ≤ 3`,
`‖aₘ‖ ≤ 1`) — the `hstepA` of `zone_sum_collapsed_wide`, kept *uncollapsed*. -/
lemma weighted_minSum_le (a : ℕ → ℂ) (s0 : Finset ℕ) {X y T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T) (hy : X ≤ y) (hy3 : y ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    ∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ))
        * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / (m : ℝ))|)))
      ≤ 6 * minDev s0 T y := by
  have hBIG_nn : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  rw [minDev, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨hmlo, hmhi⟩ := hrange m hm
  have hm0 : (0 : ℝ) < m := by linarith
  set M := min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / (m : ℝ))|)) with hMdef
  have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; exact le_min hBIG_nn (by positivity)
  have hym3 : y / (m : ℝ) ≤ 3 := by rw [div_le_iff₀ hm0]; linarith
  calc ‖a m‖ * (2 * (y / (m : ℝ)) * M)
      ≤ 1 * (6 * M) := by
        refine mul_le_mul (ha m hm) ?_ ?_ zero_le_one
        · nlinarith [hym3, hMnn]
        · exact mul_nonneg (mul_nonneg (by norm_num)
            (div_nonneg (by linarith) hm0.le)) hMnn
    _ = 6 * M := one_mul _

/-- **The short-interval Perron gap, uncollapsed**: `≤ 6·(M(x+h) + M(x))`. -/
theorem uSlab_gap_le_minDev (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hT : 0 < T) (hx : X ≤ x) (hxh3 : x + h ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖uSlab (dpolyA a s0) x h T - 2 * (Real.pi : ℂ) * I * shortSum a s0 x h‖
      ≤ 6 * minDev s0 T (x + h) + 6 * minDev s0 T x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : ∀ m ∈ s0, 0 < m := fun m hm => by
    exact_mod_cast (show (0 : ℝ) < m by linarith [(hrange m hm).1])
  have hobj : uSlab (dpolyA a s0) x h T
      = I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
              - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)) / ((1 : ℂ) + (v : ℂ) * I) := by
    rw [uSlab]
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    simp only [dpolyA, uKernel]
    rw [mul_div_assoc]
  have hmain := Aperron_short_interval a s0 (c := 1) hx0 hh one_pos hT hpos hne_x hne_xh
  rw [hobj]
  simp only [shortSum]
  rw [← residue_diff_eq_shortInterval a s0 hh hpos hne_x hne_xh]
  refine hmain.trans ?_
  have hrw : ∀ z : ℝ, (∑ m ∈ s0, ‖a m‖ * (2 * (z / (m : ℝ)) ^ (1 : ℝ)
          * min (Real.pi + 2 * Real.log (1 + T / 1)) (1 / (T * |Real.log (z / (m : ℝ))|))))
        = ∑ m ∈ s0, ‖a m‖ * (2 * (z / (m : ℝ))
          * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (z / (m : ℝ))|))) := by
    intro z
    exact Finset.sum_congr rfl fun m _ => by rw [Real.rpow_one, div_one]
  rw [hrw (x + h), hrw x]
  have h1 := weighted_minSum_le a s0 hX hT (by linarith : X ≤ x + h) hxh3 ha hrange
  have h2 := weighted_minSum_le a s0 hX hT hx (by linarith : x ≤ 3 * X) ha hrange
  linarith

/-- **The Lemma-14 Perron gap, uncollapsed**: `≤ 6·(M(x+h₁) + M(x+h₂) + 2M(x))`.  The
uncollapsed analogue of `perron_gap_collapsed_wide`: the `x`-dependence is kept inside the
`min`-device, which is exactly what the mean square needs. -/
theorem perron_gap_le_minDev (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h₁ h₂ T : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hT : 0 < T)
    (hx : X ≤ x) (hxh1 : x + h₁ ≤ 3 * X) (hxh2 : x + h₂ ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
      ≤ 6 * (minDev s0 T (x + h₁) + minDev s0 T (x + h₂) + 2 * minDev s0 T x) := by
  have hg1 := uSlab_gap_le_minDev a s0 hX (by linarith : (0 : ℝ) < h₁) hT hx hxh1 ha hrange
    hne_x hne_1
  have hg2 := uSlab_gap_le_minDev a s0 hX (by linarith : (0 : ℝ) < h₂) hT hx hxh2 ha hrange
    hne_x hne_2
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

/-! ## Part E — the bump sum and its mass -/

/-- The near-band majorant of `M(x + c)`: the bumps of `s0` re-centred at `m − c`. -/
def bumpSum (s0 : Finset ℕ) (δ B c y : ℝ) : ℝ :=
  ∑ m ∈ s0, nearBump ((m : ℝ) - c) δ B y

lemma bumpSum_nonneg (s0 : Finset ℕ) {δ B c y : ℝ} (hB : 0 ≤ B) :
    0 ≤ bumpSum s0 δ B c y :=
  Finset.sum_nonneg fun _ _ => nearBump_nonneg hB

lemma bumpSum_le_card (s0 : Finset ℕ) {δ B c y : ℝ} (hB : 0 ≤ B) :
    bumpSum s0 δ B c y ≤ (s0.card : ℝ) * B := by
  have h := Finset.sum_le_sum (fun m (_ : m ∈ s0) => nearBump_le (c := (m : ℝ) - c)
    (δ := δ) (y := y) hB)
  rw [Finset.sum_const, nsmul_eq_mul] at h
  exact h

lemma bumpSum_measurable (s0 : Finset ℕ) (δ B c : ℝ) : Measurable (bumpSum s0 δ B c) :=
  Finset.measurable_sum _ (fun _ _ => nearBump_measurable _ _ _)

/-- **The pointwise cap**: at most three integers sit within `δ ≤ 1` of a point, so
`bumpSum ≤ 3B`. -/
lemma bumpSum_cap (s0 : Finset ℕ) {δ B c y : ℝ} (hB : 0 ≤ B) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hy : 1 ≤ y + c) : bumpSum s0 δ B c y ≤ 3 * B := by
  have hrw : bumpSum s0 δ B c y
      = ∑ m ∈ s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| < δ), B := by
    rw [bumpSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nearBump, show y - ((m : ℝ) - c) = (y + c) - (m : ℝ) by ring]
  rw [hrw, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| < δ)).card : ℝ) ≤ 3 := by
    have hsub : s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| < δ)
        ⊆ s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| ≤ δ) := by
      intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, le_of_lt hm.2⟩
    have h1 : ((s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| < δ)).card : ℝ)
        ≤ ((s0.filter (fun m : ℕ => |(y + c) - (m : ℝ)| ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := zone_count_crossover s0 hδ0 (by linarith : δ ≤ y + c)
    linarith
  exact mul_le_mul_of_nonneg_right hcard hB

lemma bumpSum_intervalIntegrable (s0 : Finset ℕ) {δ B : ℝ} (hB : 0 ≤ B) (c p q : ℝ) :
    IntervalIntegrable (bumpSum s0 δ B c) volume p q := by
  refine bdd_meas_intervalIntegrable (C := (s0.card : ℝ) * B) p q
    (bumpSum_measurable s0 δ B c) (fun y => ?_)
  rw [Real.norm_of_nonneg (bumpSum_nonneg s0 hB)]
  exact bumpSum_le_card s0 hB

/-- **The bump sum's mass** — the heart of the mean-square gain: however the `BIG` branch is
paid, it is paid on a set of measure `≤ |s0|·2δ`. -/
lemma bumpSum_integral_le (s0 : Finset ℕ) {δ B c p q : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hpq : p ≤ q) :
    (∫ y in p..q, bumpSum s0 δ B c y) ≤ (s0.card : ℝ) * (2 * δ * B) := by
  have hint : (∫ y in p..q, bumpSum s0 δ B c y)
      = ∑ m ∈ s0, ∫ y in p..q, nearBump ((m : ℝ) - c) δ B y := by
    simp only [bumpSum]
    exact intervalIntegral.integral_finsetSum
      (fun m _ => nearBump_intervalIntegrable hB p q)
  rw [hint]
  have h := Finset.sum_le_sum
    (fun m (_ : m ∈ s0) => nearBump_integral_le (c := (m : ℝ) - c) hB hδ hpq)
  rw [Finset.sum_const, nsmul_eq_mul] at h
  exact h

/-- The index count of an `[X,4X]`-supported set: `|s0| ≤ 4X + 1`. -/
lemma card_le_of_range {X : ℝ} (hX : 1 ≤ X) (s0 : Finset ℕ)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) : (s0.card : ℝ) ≤ 4 * X + 1 := by
  have hsub : s0 ⊆ Finset.Icc 0 ⌊4 * X⌋₊ := by
    intro m hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.le_floor (hrange m hm).2⟩
  have h1 : s0.card ≤ ⌊4 * X⌋₊ + 1 := by
    have h2 := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.sub_zero] at h2
  have h3 : ((⌊4 * X⌋₊ : ℕ) : ℝ) ≤ 4 * X := Nat.floor_le (by linarith)
  have h4 : (s0.card : ℝ) ≤ ((⌊4 * X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_add, Nat.cast_one] at h4
  linarith

/-- **X1, shifted form** — `M(x + c) ≤ bumpSum(x) + K`. -/
lemma minDev_shift_le (s0 : Finset ℕ) {X x c y T δ : ℝ} (hy : y = x + c)
    (hX : 1 ≤ X) (hT : 0 < T) (hδ0 : 0 < δ) (hlo : X ≤ y) (hhi : y ≤ 4 * X)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    minDev s0 T y
      ≤ bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) c x
        + (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) := by
  refine (zone_min_sum_split s0 hX hT hlo hhi hδ0 hrange).trans ?_
  have heq : (∑ m ∈ s0, nearBump (m : ℝ) δ (Real.pi + 2 * Real.log (1 + T)) y)
      = bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) c x := by
    simp only [bumpSum]
    rw [hy]
    exact Finset.sum_congr rfl fun m _ => nearBump_shift _ _ _ _ _
  rw [heq]

/-! ## Part F — X3: the mean-square majorant -/

/-- **The explicit majorant of the Lemma-14 Perron gap.**  Three re-centred bump sums (the
`BIG` branch, paid only on a set of measure `≤ |s0|·2δ` per shift) plus a *constant*
`24·(12X/(Tδ) + (8X/T)(1+log 3X))` (the middle and far bands). -/
def gapMaj (s0 : Finset ℕ) (X T δ h₁ h₂ x : ℝ) : ℝ :=
  6 * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
      + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
      + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
    + 24 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)))

/-- **The pointwise gap bound**: the Lemma-14 Perron gap at `x` is `≤ gapMaj x`. -/
theorem perron_gap_le_gapMaj (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h₁ h₂ T δ : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂) (hT : 0 < T) (hδ0 : 0 < δ)
    (hx : X ≤ x) (hxh1 : x + h₁ ≤ 3 * X) (hxh2 : x + h₂ ≤ 3 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x)
    (hne_1 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₁) (hne_2 : ∀ m ∈ s0, (m : ℝ) ≠ x + h₂) :
    ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ T
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ T
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖
      ≤ gapMaj s0 X T δ h₁ h₂ x := by
  have hmain := perron_gap_le_minDev a s0 hX hh1 hh2 hT hx hxh1 hxh2 ha hrange
    hne_x hne_1 hne_2
  refine hmain.trans ?_
  have s1 := minDev_shift_le s0 (x := x) (c := h₁) (y := x + h₁) rfl hX hT hδ0
    (by linarith) (by linarith) hrange
  have s2 := minDev_shift_le s0 (x := x) (c := h₂) (y := x + h₂) rfl hX hT hδ0
    (by linarith) (by linarith) hrange
  have s0' := minDev_shift_le s0 (x := x) (c := 0) (y := x) (add_zero x).symm hX hT hδ0
    hx (by linarith) hrange
  rw [gapMaj]
  linarith

lemma gapMaj_measurable (s0 : Finset ℕ) (X T δ h₁ h₂ : ℝ) :
    Measurable (gapMaj s0 X T δ h₁ h₂) := by
  change Measurable fun x : ℝ =>
    6 * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
        + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
        + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
      + 24 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)))
  exact ((((bumpSum_measurable s0 δ _ h₁).add (bumpSum_measurable s0 δ _ h₂)).add
    ((bumpSum_measurable s0 δ _ 0).const_mul 2)).const_mul 6).add_const _

lemma gapMaj_nonneg (s0 : Finset ℕ) {X T δ h₁ h₂ x : ℝ} (hX : 1 ≤ X) (hT : 0 < T)
    (hδ0 : 0 < δ) : 0 ≤ gapMaj s0 X T δ h₁ h₂ x := by
  have hB : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hlog : (0 : ℝ) ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have b1 := bumpSum_nonneg s0 (δ := δ) (c := h₁) (y := x) hB
  have b2 := bumpSum_nonneg s0 (δ := δ) (c := h₂) (y := x) hB
  have b0 := bumpSum_nonneg s0 (δ := δ) (c := 0) (y := x) hB
  have hk1 : (0 : ℝ) ≤ 12 * X / (T * δ) := by positivity
  have hk2 : (0 : ℝ) ≤ (8 * X / T) * (1 + Real.log (3 * X)) := by
    have : (0 : ℝ) ≤ 8 * X / T := by positivity
    nlinarith
  rw [gapMaj]
  linarith

lemma gapMaj_le_const (s0 : Finset ℕ) {X T δ h₁ h₂ x : ℝ} (hT : 0 < T) :
    gapMaj s0 X T δ h₁ h₂ x
      ≤ 24 * (s0.card : ℝ) * (Real.pi + 2 * Real.log (1 + T))
        + 24 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) := by
  have hB : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have b1 := bumpSum_le_card s0 (δ := δ) (c := h₁) (y := x) hB
  have b2 := bumpSum_le_card s0 (δ := δ) (c := h₂) (y := x) hB
  have b0 := bumpSum_le_card s0 (δ := δ) (c := 0) (y := x) hB
  rw [gapMaj]
  linarith

lemma gapMaj_sq_intervalIntegrable (s0 : Finset ℕ) {X T δ : ℝ} (hX : 1 ≤ X) (hT : 0 < T)
    (hδ0 : 0 < δ) (h₁ h₂ p q : ℝ) :
    IntervalIntegrable (fun x : ℝ => gapMaj s0 X T δ h₁ h₂ x ^ 2) volume p q := by
  refine bdd_meas_intervalIntegrable
    (C := (24 * (s0.card : ℝ) * (Real.pi + 2 * Real.log (1 + T))
      + 24 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)))) ^ 2) p q
    ((gapMaj_measurable s0 X T δ h₁ h₂).pow_const 2) (fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (gapMaj_nonneg s0 hX hT hδ0) (gapMaj_le_const s0 hT) 2

/-- **X3 — THE MEAN-SQUARE BOUND.**  The `x`-average of the squared gap majorant on `[X,2X]`:

`(1/X)∫_X^{2X} gapMaj(x)² dx ≤ 34560·δ·BIG² + 1152·(12X/(Tδ) + (8X/T)(1+log 3X))²`,
`BIG = π + 2log(1+T)`.

This is the exit the naive route cannot reach: squaring the *pointwise* bound
`perron_gap_le_of_T` and integrating diverges (its `C(x)²` behaves like `4X²/|x−m₀|²` near a
support integer).  Keeping the `min`-device inside the `x`-integral converts the `BIG` branch
from a pointwise cost into a *mass* cost `|s0|·2δ·BIG` per shift, and `δ` is free.  As
`T → ∞` with `δ = δ(T) → 0` slowly enough (e.g. `δ = √(X/T)`, so that `δ·BIG² → 0` and
`X/(Tδ) = √(X/T) → 0`), the whole right-hand side tends to `0` — the `x`-uniform Perron
limit, in mean square. -/
theorem gapMaj_meansq_le (s0 : Finset ℕ) {X T δ h₁ h₂ : ℝ} (hX : 1 ≤ X) (hT : 0 < T)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    1 / X * (∫ x in X..(2 * X), gapMaj s0 X T δ h₁ h₂ x ^ 2)
      ≤ 34560 * δ * (Real.pi + 2 * Real.log (1 + T)) ^ 2
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX2 : X ≤ 2 * X := by linarith
  have hB : (0 : ℝ) ≤ Real.pi + 2 * Real.log (1 + T) := by
    have h1 := Real.pi_pos
    have h2 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
    linarith
  have hlog : (0 : ℝ) ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ 12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)) := by
    have hk1 : (0 : ℝ) ≤ 12 * X / (T * δ) := by positivity
    have h8 : (0 : ℝ) ≤ 8 * X / T := by positivity
    nlinarith
  -- the pointwise square bound on `[X, 2X]`
  have hptwise : ∀ x ∈ Set.Icc X (2 * X), gapMaj s0 X T δ h₁ h₂ x ^ 2
      ≤ 864 * (Real.pi + 2 * Real.log (1 + T))
          * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
            + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
            + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 := by
    intro x hxm
    rw [Set.mem_Icc] at hxm
    have b1 := bumpSum_cap s0 (δ := δ) (c := h₁) (y := x) hB hδ0.le hδ1 (by linarith [hxm.1])
    have b2 := bumpSum_cap s0 (δ := δ) (c := h₂) (y := x) hB hδ0.le hδ1 (by linarith [hxm.1])
    have b0 := bumpSum_cap s0 (δ := δ) (c := 0) (y := x) hB hδ0.le hδ1 (by linarith [hxm.1])
    have n1 := bumpSum_nonneg s0 (δ := δ) (c := h₁) (y := x) hB
    have n2 := bumpSum_nonneg s0 (δ := δ) (c := h₂) (y := x) hB
    have n0 := bumpSum_nonneg s0 (δ := δ) (c := 0) (y := x) hB
    rw [gapMaj]
    nlinarith [sq_nonneg (6 * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
        + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
        + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
      - 24 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X)))), hB, hK,
      mul_nonneg hB hK]
  -- integrability of both sides
  have hBint : ∀ c : ℝ, IntervalIntegrable
      (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) c) volume X (2 * X) :=
    fun c => bumpSum_intervalIntegrable s0 hB c X (2 * X)
  have hQint : IntervalIntegrable (fun x : ℝ =>
      bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
        + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
        + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x) volume X (2 * X) :=
    ((hBint h₁).add (hBint h₂)).add ((hBint 0).const_mul 2)
  have hRint : IntervalIntegrable (fun x : ℝ =>
      864 * (Real.pi + 2 * Real.log (1 + T))
          * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
            + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
            + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2)
      volume X (2 * X) := (hQint.const_mul _).add _root_.intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hX2
    (gapMaj_sq_intervalIntegrable s0 hX hT hδ0 h₁ h₂ X (2 * X)) hRint hptwise
  -- evaluate the right-hand integral
  have heval : (∫ x in X..(2 * X),
        (864 * (Real.pi + 2 * Real.log (1 + T))
            * (bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x
              + bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x
              + 2 * bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
          + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2))
      = 864 * (Real.pi + 2 * Real.log (1 + T))
          * ((∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x)
            + (∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x)
            + 2 * ∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 * X := by
    rw [intervalIntegral.integral_add (hQint.const_mul _) _root_.intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((hBint h₁).add (hBint h₂)) ((hBint 0).const_mul 2),
      intervalIntegral.integral_add (hBint h₁) (hBint h₂),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heval] at hmono
  -- the three bump masses
  have m1 := bumpSum_integral_le s0 (δ := δ) (B := Real.pi + 2 * Real.log (1 + T)) (c := h₁)
    (p := X) (q := 2 * X) hB hδ0.le hX2
  have m2 := bumpSum_integral_le s0 (δ := δ) (B := Real.pi + 2 * Real.log (1 + T)) (c := h₂)
    (p := X) (q := 2 * X) hB hδ0.le hX2
  have m0 := bumpSum_integral_le s0 (δ := δ) (B := Real.pi + 2 * Real.log (1 + T)) (c := 0)
    (p := X) (q := 2 * X) hB hδ0.le hX2
  have hcard := card_le_of_range hX s0 hrange
  have hcard0 : (0 : ℝ) ≤ (s0.card : ℝ) := Nat.cast_nonneg _
  -- assemble
  have hstep : (∫ x in X..(2 * X), gapMaj s0 X T δ h₁ h₂ x ^ 2)
      ≤ 6912 * (s0.card : ℝ) * δ * (Real.pi + 2 * Real.log (1 + T)) ^ 2
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 * X := by
    refine hmono.trans ?_
    have hsum : (∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₁ x)
        + (∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) h₂ x)
        + 2 * (∫ x in X..(2 * X), bumpSum s0 δ (Real.pi + 2 * Real.log (1 + T)) 0 x)
        ≤ 4 * ((s0.card : ℝ) * (2 * δ * (Real.pi + 2 * Real.log (1 + T)))) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum
      (by positivity : (0 : ℝ) ≤ 864 * (Real.pi + 2 * Real.log (1 + T)))]
  -- divide by X
  have hfin := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / X)
  refine hfin.trans ?_
  have hcx : (s0.card : ℝ) ≤ 5 * X := by linarith
  have hexp : 1 / X * (6912 * (s0.card : ℝ) * δ * (Real.pi + 2 * Real.log (1 + T)) ^ 2
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 * X)
      = 6912 * ((s0.card : ℝ) / X) * δ * (Real.pi + 2 * Real.log (1 + T)) ^ 2
        + 1152 * (12 * X / (T * δ) + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 := by
    field_simp
  rw [hexp]
  have hratio : (s0.card : ℝ) / X ≤ 5 := by
    rw [div_le_iff₀ hX0]; linarith
  have hpos : (0 : ℝ) ≤ δ * (Real.pi + 2 * Real.log (1 + T)) ^ 2 := by positivity
  nlinarith [hratio, hpos, div_nonneg hcard0 hX0.le]

/-- **The shrinking instance** — `gapMaj_meansq_le` at the balanced width `δ = √(X/T)`
(admissible as soon as `T ≥ X`):

`(1/X)∫_X^{2X} gapMaj² ≤ 34560·√(X/T)·(π + 2log(1+T))²
    + 1152·(12√(X/T) + (8X/T)(1 + log 3X))²`.

Every summand carries a **negative power of `T`** against at most `log²T`, so the whole
right-hand side tends to `0` as `T → ∞` at fixed `X`: this is the honest `x`-uniform Perron
limit that `perron_gap_le_of_T` could only supply per point.  (The `T`-pin of
`lemma14_contour` — `Tcut = 2X/h₁ ≤ 2X` — is what stops the Lemma-14 consumer from using it;
see `lemma14_shortInterval_meansq_concrete`.) -/
theorem gapMaj_meansq_sqrt (s0 : Finset ℕ) {X T h₁ h₂ : ℝ} (hX : 1 ≤ X) (hT : X ≤ T)
    (hh1 : 1 ≤ h₁) (hh2 : 1 ≤ h₂)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    1 / X * (∫ x in X..(2 * X), gapMaj s0 X T (Real.sqrt (X / T)) h₁ h₂ x ^ 2)
      ≤ 34560 * Real.sqrt (X / T) * (Real.pi + 2 * Real.log (1 + T)) ^ 2
        + 1152 * (12 * Real.sqrt (X / T)
            + (8 * X / T) * (1 + Real.log (3 * X))) ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hXT : (0 : ℝ) < X / T := div_pos hX0 hT0
  have hδ0 : (0 : ℝ) < Real.sqrt (X / T) := Real.sqrt_pos.mpr hXT
  have hδ1 : Real.sqrt (X / T) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by rw [div_le_one hT0]; exact hT)
  refine (gapMaj_meansq_le s0 hX hT0 hδ0 hδ1 hh1 hh2 hrange).trans (le_of_eq ?_)
  have hk : 12 * X / (T * Real.sqrt (X / T)) = 12 * Real.sqrt (X / T) := by
    rw [eq_comm, eq_div_iff (by positivity)]
    have hsq : Real.sqrt (X / T) * Real.sqrt (X / T) = X / T :=
      Real.mul_self_sqrt hXT.le
    calc 12 * Real.sqrt (X / T) * (T * Real.sqrt (X / T))
        = 12 * T * (Real.sqrt (X / T) * Real.sqrt (X / T)) := by ring
      _ = 12 * T * (X / T) := by rw [hsq]
      _ = 12 * X := by field_simp
  rw [hk]

/-! ## Part G — X4: the consumer exit, with the gap entering in mean square -/

/-- The `max`-regularized weighted `V`-difference (`Lemma14`'s `vdiffR`, re-derived here
because that file's copy is `private`).  Globally continuous in `x`, and equal to the honest
weighted difference for `x ≥ X`. -/
private def vdiffQ (A : ℝ → ℂ) (X h₁ h₂ α β x : ℝ) : ℂ :=
  ((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
    - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)

private lemma vdiffQ_continuous {A : ℝ → ℂ} (hA : Continuous A) {X : ℝ} (hX : 0 < X)
    (h₁ h₂ α β : ℝ) : Continuous (fun x : ℝ => vdiffQ A X h₁ h₂ α β x) := by
  have hFr : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  simp only [vdiffQ]
  exact (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₁))).sub
    (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₂)))

private lemma vdiffQ_eq {A : ℝ → ℂ} (hA : Continuous A) {X x h₁ h₂ : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh1 : 0 ≤ h₁) (hh2 : 0 ≤ h₂) {α β : ℝ} :
    vdiffQ A X h₁ h₂ α β x
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
  simp only [vdiffQ]
  rw [key h₁ hh1, key h₂ hh2]

/-- `x`-integrability of the squared weighted Perron difference. -/
private lemma uSlab_diff_sq_intervalIntegrable {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (T : ℝ) :
    IntervalIntegrable (fun x : ℝ =>
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ T - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ T‖ ^ 2)
      volume X (2 * X) := by
  have hc : Continuous (fun x : ℝ => ‖vdiffQ A X h₁ h₂ (-T) T x‖ ^ 2) :=
    ((vdiffQ_continuous hA hX h₁ h₂ (-T) T).norm).pow 2
  refine (hc.intervalIntegrable X (2 * X)).congr (fun x hx => ?_)
  rw [Set.uIoc_of_le (by linarith : X ≤ 2 * X), Set.mem_Ioc] at hx
  rw [vdiffQ_eq hA hX hx.1.le hh1.le hh2.le]
  rfl

/-- **X4 — Lemma 14 in the frozen `Sⱼ` form, with the Perron defect entering in MEAN SQUARE.**

The consumer-side restatement of `lemma14_shortInterval_of_perron`: instead of a single
constant `Eper` dominating the Perron gap *pointwise* a.e., the gap is dominated a.e. by a
function `G`, and only the **mean square** `(1/X)∫_X^{2X} G² ≤ Egap` enters the conclusion:

`(1/X)∫_X^{2X} |(1/h₁)S₁ − (1/h₂)S₂|² ≤ (1/2π²)·( C·((log X)^{−14/45} + ∫ + Msup) + Egap )`,
`C = 2000 + 820π`.

The transfer is the same `(a+b)² ≤ 2a² + 2b²` used pointwise inside the `x`-integral; what
changes is that the gap's cost is now an *average*, so a majorant that is large only on a
small set (exactly `gapMaj`: `BIG` on a set of measure `|s0|·2δ`) costs almost nothing.
Setting `G ≡ Eper` recovers `lemma14_shortInterval_of_perron` (`Egap = Eper²`). -/
theorem lemma14_shortInterval_meansq (a : ℕ → ℂ) (s0 : Finset ℕ)
    {X h₁ h₂ Msup Egap : ℝ} (G : ℝ → ℝ)
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup)
    (hGint : IntervalIntegrable (fun x : ℝ => G x ^ 2) volume X (2 * X))
    (hPerron : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))),
      ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
        - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))
        - 2 * (Real.pi : ℂ) * I * (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)‖ ≤ G x)
    (hGsq : 1 / X * (∫ x in X..(2 * X), G x ^ 2) ≤ Egap) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * ((2000 + 820 * Real.pi) * ((Real.log X) ^ (-(14 / 45 : ℝ))
          + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + Msup) + Egap) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hnormI : ∀ z : ℂ, ‖2 * (Real.pi : ℂ) * I * z‖ = 2 * Real.pi * ‖z‖ := by
    intro z
    have hre : 2 * (Real.pi : ℂ) * I * z = ((2 * Real.pi : ℝ) : ℂ) * (I * z) := by
      push_cast; ring
    rw [hre, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  -- the pointwise transfer, with the gap kept as a function of `x`
  have hpt : (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] fun x : ℝ => 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2
          + G x ^ 2) := by
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
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ + G x := by
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
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + G x ^ 2)
        = (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + G x ^ 2)
          / (2 * Real.pi ^ 2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2)]
    nlinarith [hsq, hpi, sq_nonneg (‖((1 / h₁ : ℝ) : ℂ)
      * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
      - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ - G x)]
  -- integrate the pointwise transfer
  have hPint := uSlab_diff_sq_intervalIntegrable hAc hXpos hh1' hh2' (2 * (X / h₁))
  have hRint : IntervalIntegrable (fun x : ℝ => 1 / (2 * Real.pi ^ 2)
      * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + G x ^ 2))
      volume X (2 * X) := (hPint.add hGint).const_mul _
  have hSint := shortSum_diff_sq_intervalIntegrable a s0 hh1' hh2' X (2 * X)
  have hmono := intervalIntegral.integral_mono_ae_restrict (by linarith : X ≤ 2 * X)
    hSint hRint hpt
  have heval : (∫ x in X..(2 * X), 1 / (2 * Real.pi ^ 2)
        * (‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2 + G x ^ 2))
      = 1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
        + ∫ x in X..(2 * X), G x ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hPint hGint]
  rw [heval] at hmono
  have hstep1 : 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
          ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
            - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
        + 1 / X * ∫ x in X..(2 * X), G x ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / X)
    calc 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)
        ≤ 1 / X * (1 / (2 * Real.pi ^ 2) * ((∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
          + ∫ x in X..(2 * X), G x ^ 2)) := h1
      _ = 1 / (2 * Real.pi ^ 2) * (1 / X * (∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
          + 1 / X * ∫ x in X..(2 * X), G x ^ 2) := by ring
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith [lemma14_contour_grouped a s0 hX hh1 hh12 hh2X ha hrange hMsup, hGsq]

/-- **Lemma 14 in the frozen `Sⱼ` form with the Perron defect discharged IN MEAN SQUARE.**
Every hypothesis discharged internally (as in `lemma14_shortInterval_concrete`), but the
Perron cost is now an `x`-average rather than an `x`-supremum, at the pinned truncation
`T = 2X/h₁` and any bump width `0 < δ ≤ 1`:

`Egap(δ) = 34560·δ·(π + 2·log(1 + 2X/h₁))² + 1152·(6h₁/δ + 4h₁·(1 + log 3X))²`.

**Honest size at the pinned `T`.**  The first summand is the near-diagonal `BIG` cost, and it
is now *free*: `δ` may be taken as small as one likes.  The second is the far-band cost
`(8X/T)·log`-grade, which at `T = 2X/h₁` is `4h₁·(1 + log 3X)` — **irreducible**, because the
truncation is pinned.  So the honest grade of this instance is still `h₁²·log²X`, the same as
`lemma14_shortInterval_concrete`; the mean-square device removes the `log T` near-diagonal
term but cannot touch the `X/T` far-band term.  Making the Perron defect *shrink* requires
`T ≫ X·(log X)^B`, i.e. relaxing `lemma14_contour`'s forced `Tcut = 2X/h₁` — see
`gapMaj_meansq_le`, which is stated at general `T` and does tend to `0`. -/
theorem lemma14_shortInterval_meansq_concrete (a : ℕ → ℂ) (s0 : Finset ℕ)
    {X h₁ h₂ Msup δ : ℝ}
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
      ≤ 1 / (2 * Real.pi ^ 2) * ((2000 + 820 * Real.pi) * ((Real.log X) ^ (-(14 / 45 : ℝ))
          + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁), ‖dpolyA a s0 t‖ ^ 2)
              + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
          + Msup)
        + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 * (X / h₁))) ^ 2
          + 1152 * (6 * h₁ / δ + 4 * h₁ * (1 + Real.log (3 * X))) ^ 2)) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2 : (1 : ℝ) ≤ h₂ := le_trans hh1 hh12
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hh2XX : h₂ ≤ X := by nlinarith [hh2X, hLinv1, hXpos]
  have hTpos : (0 : ℝ) < 2 * (X / h₁) := by positivity
  refine lemma14_shortInterval_meansq a s0 (gapMaj s0 X (2 * (X / h₁)) δ h₁ h₂)
    hX hh1 hh12 hh2X ha hrange hMsup
    (gapMaj_sq_intervalIntegrable s0 hX1 hTpos hδ0 h₁ h₂ X (2 * X)) ?_ ?_
  · have hguards := perron_guards_ae s0 h₁ h₂ (volume.restrict (Set.Icc X (2 * X)))
    have hmem : ∀ᵐ x ∂(volume.restrict (Set.Icc X (2 * X))), x ∈ Set.Icc X (2 * X) :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hguards, hmem] with x hg hxmem
    obtain ⟨g0, g1, g2⟩ := hg
    rw [Set.mem_Icc] at hxmem
    exact perron_gap_le_gapMaj a s0 hX1 hh1 hh2 hTpos hδ0 hxmem.1
      (by linarith [hxmem.2]) (by linarith [hxmem.2]) ha hrange g0 g1 g2
  · refine (gapMaj_meansq_le s0 hX1 hTpos hδ0 hδ1 hh1 hh2 hrange).trans (le_of_eq ?_)
    have hk1 : 12 * X / (2 * (X / h₁) * δ) = 6 * h₁ / δ := by
      field_simp
      ring
    have hk2 : 8 * X / (2 * (X / h₁)) = 4 * h₁ := by
      field_simp
      ring
    rw [hk1, hk2]

end Salt.MR
