/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronZones

/-!
# S8 MR-CORE, node A3a — the Lemma-14 completion bridge (stones S-A, S-D)

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 21–23 (Lemma 14; frozen statement transcribed verbatim in `Salt.MR.ParsevalSL`).

This file lands two stones of PARSEVAL-SCOPE's Lemma-14 completion ladder on top of the
landed truncated-Perron representation (`Salt.MR.Aperron_representation`, `ParsevalAsm.lean`)
and its zone-collapse (`Salt.MR.perron_sum_error_collapsed`, `PerronZones.lean`).

## S-A — the Perron → `Sⱼ` bridge (`Aperron_short_interval`)

Applying the landed representation at `y = x + h` and at `y = x` and subtracting realises
MR's short-interval Perron identity at finite `T`:
`I·∫_{−T}^T A(1+it)·((x+h)^s − x^s)/s dt − 2πi·Sⱼ(x) = E(x+h) − E(x)` (bounded).
The residue difference `∑ₘ aₘ·(𝟙((x+h)/m>1) − 𝟙(x/m>1))` is exactly the short-interval
sum `Sⱼ(x)` (`residue_diff_eq_shortInterval`).

**Boundary convention (the S-A finding).**  The landed `Aperron_representation` carries the
*strict* residue indicator `𝟙(1 < y/m)` (i.e. `𝟙(m < y)`) and the hypothesis `(m:ℝ) ≠ y`.
Consequently the natural interval convention produced here is the **half-open**
`Sⱼ(x) = ∑_{x < m ≤ x+h} aₘ`, *not* the closed `∑_{x ≤ m ≤ x+h}` printed in MR's text
(`ParsevalSL` docstring).  The two conventions differ only at the single endpoint `m = x`,
which the guard `(m:ℝ) ≠ x` excludes anyway; under the honest guards `(m:ℝ) ≠ x` and
`(m:ℝ) ≠ x+h` (i.e. `x`, `x+h` non-integers, or carrying no coefficient mass), all of
`x ≤ m ≤ x+h`, `x < m ≤ x+h`, `x < m < x+h` coincide, so the bridge matches MR.

The normalization is **byte-followed** from `Aperron_representation`: the un-normalized
contour value `I·∫_{−T}^T (∑ aₘ/mˢ)·yˢ/s dv` (`= 2πi` times the `(1/2πi)∫` of Perron), and
the residue term `2πi·∑ aₘ·𝟙(1 < y/m)`.

## S-D — the weighted max-term tail (`dyadic_tail_block`, `dyadic_tail_proper`)

The far-tail dyadic bound.  With `G(t) = ‖A(1+it)‖²` (nonneg, continuous) and the smoothed
kernel capped at `min(b, 2/t)` (`b = hⱼ/x`, from `sv_smooth_kernel_bound`), each dyadic block
`[T, 2T]` obeys `∫_T^{2T} G·(min b (2/t))² ≤ 4·Msup/(W·T)`, where `W = X/h₁` and `Msup` is
any upper bound for the weighted sup `(W/T)·∫_T^{2T} G` over `T ≥ Tmax` (`dyadic_tail_block`).
Summing the geometric series over the dyadic tiling of `[Tmax, 2^N·Tmax]` gives the uniform
`∫_{Tmax}^{2^N Tmax} G·(min b (2/t))² ≤ 8·Msup/(W·Tmax)` (`dyadic_tail_proper`).

The bound is stated for the **positive** tail `t > 0`; the two-sided `|t| ≥ Tmax` tail is the
sum of the two half-tails (apply to each).  The improper `∫_{Tmax}^∞` limit is the monotone
limit of the uniform truncated bound and is left to the consumer (the `V`-object join, S-C).

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`,
no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## S-A — the Perron → `Sⱼ` bridge -/

/-- Continuity of the critical-line integrand `v ↦ (∑ₘ aₘ/mˢ)·yˢ/s` (`s = c + vi`) for
`y > 0`, `c > 0` and positive indices — the interval-integrability input to the subtraction
`J(x+h) − J(x)`.  Each `mˢ` is nonzero (`cpow_ne_zero_iff`), so the finite sum, the factor
`yˢ`, and the division by `s ≠ 0` (`SW.s_ne_zero`) are all continuous. -/
private lemma Aline_cont (a : ℕ → ℂ) (s0 : Finset ℕ) {y c : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hpos : ∀ m ∈ s0, 0 < m) :
    Continuous (fun v : ℝ => (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
        * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I)) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hs_cont : Continuous (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) := by fun_prop
  have hs_ne : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) ≠ 0 := fun v => Salt.SW.s_ne_zero hc v
  have hys : Continuous (fun v : ℝ => (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) :=
    (continuous_id.const_cpow (Or.inl hyC)).comp hs_cont
  have hsum : Continuous (fun v : ℝ => ∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) := by
    apply continuous_finsetSum
    intro m hm
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (hpos m hm).ne'
    exact Continuous.div continuous_const
      ((continuous_id.const_cpow (Or.inl hmC)).comp hs_cont)
      (fun v => Complex.cpow_ne_zero_iff.mpr (Or.inl hmC))
  exact (hsum.mul hys).div hs_cont hs_ne

/-- **S-A — the Perron → short-interval bridge.**  Subtracting the landed truncated-Perron
representation (`Aperron_representation`) at `y = x + h` and `y = x`: the short-interval
contour integral (kernel `((x+h)ˢ − xˢ)/s`, un-normalized as in `Aperron_representation`)
differs from `2πi` times the residue difference by at most the sum of the two collapsed
Perron errors.  The residue difference is `Sⱼ(x)` (see `residue_diff_eq_shortInterval`).

Guards: `(m:ℝ) ≠ x` and `(m:ℝ) ≠ x + h` for every index (the honest boundary convention). -/
theorem Aperron_short_interval (a : ℕ → ℂ) (s0 : Finset ℕ) {x h c T : ℝ}
    (hx : 0 < x) (hh : 0 < h) (hc : 0 < c) (hT : 0 < T)
    (hpos : ∀ m ∈ s0, 0 < m)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖(I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)
               - ((x : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
            / ((c : ℂ) + (v : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I
            * ∑ m ∈ s0, a m
                * ((if 1 < (x + h) / m then (1 : ℂ) else 0)
                   - (if 1 < x / m then (1 : ℂ) else 0))‖
      ≤ (∑ m ∈ s0, ‖a m‖ * (2 * ((x + h) / m) ^ c
            * min (Real.pi + 2 * Real.log (1 + T / c))
                (1 / (T * |Real.log ((x + h) / m)|))))
        + (∑ m ∈ s0, ‖a m‖ * (2 * (x / m) ^ c
            * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log (x / m)|)))) := by
  have hxh : (0 : ℝ) < x + h := by linarith
  -- interval-integrability of the two per-point integrands
  have hPint : IntervalIntegrable
      (fun v : ℝ => (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
        * ((x + h : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
      volume (-T) T :=
    (Aline_cont a s0 hxh hc hpos).intervalIntegrable _ _
  have hQint : IntervalIntegrable
      (fun v : ℝ => (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
        * ((x : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
      volume (-T) T :=
    (Aline_cont a s0 hx hc hpos).intervalIntegrable _ _
  -- (1) split the combined kernel integral into the two per-point contour values
  have hcomb : (I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)
               - ((x : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
            / ((c : ℂ) + (v : ℂ) * I))
        = (I * ∫ v in (-T)..T,
              (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
                * ((x + h : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
          - (I * ∫ v in (-T)..T,
              (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
                * ((x : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I)) := by
    rw [← mul_sub, ← intervalIntegral.integral_sub hPint hQint]
    congr 1
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [mul_sub, sub_div]
  -- (2) the two landed representations
  have hA1 := Aperron_representation a s0 hxh hc hT hpos hne_xh
  have hA2 := Aperron_representation a s0 hx hc hT hpos hne_x
  -- (3) split the residue difference over the sum
  have hinner : (∑ m ∈ s0, a m
          * ((if 1 < (x + h) / m then (1 : ℂ) else 0) - (if 1 < x / m then (1 : ℂ) else 0)))
        = (∑ m ∈ s0, a m * (if 1 < (x + h) / m then (1 : ℂ) else 0))
          - ∑ m ∈ s0, a m * (if 1 < x / m then (1 : ℂ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_sub]
  -- assemble
  rw [hcomb, hinner, mul_sub, sub_sub_sub_comm]
  exact (norm_sub_le _ _).trans (add_le_add hA1 hA2)

/-- **S-A residue identification — the `Sⱼ(x)` identity.**  Under the boundary guards
`(m:ℝ) ≠ x`, `(m:ℝ) ≠ x + h`, the residue difference produced by `Aperron_short_interval`
is exactly the (half-open) short-interval sum `Sⱼ(x) = ∑_{x < m ≤ x+h} aₘ`.  The strict
indicator `𝟙(1 < y/m) = 𝟙(m < y)` gives `x < m ≤ x + h`; the guards make it agree with MR's
closed convention. -/
theorem residue_diff_eq_shortInterval (a : ℕ → ℂ) (s0 : Finset ℕ) {x h : ℝ}
    (hh : 0 < h) (hpos : ∀ m ∈ s0, 0 < m)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    (∑ m ∈ s0, a m
        * ((if 1 < (x + h) / m then (1 : ℂ) else 0) - (if 1 < x / m then (1 : ℂ) else 0)))
      = ∑ m ∈ s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h), a m := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hpos m hm
  have key : ((if 1 < (x + h) / (m : ℝ) then (1 : ℂ) else 0)
        - (if 1 < x / (m : ℝ) then (1 : ℂ) else 0))
      = if (x < (m : ℝ) ∧ (m : ℝ) ≤ x + h) then (1 : ℂ) else 0 := by
    simp only [one_lt_div hmpos]
    by_cases h1 : (m : ℝ) < x + h
    · by_cases h2 : (m : ℝ) < x
      · rw [if_pos h1, if_pos h2,
          if_neg (fun hc => absurd hc.1 (not_lt.mpr h2.le))]; ring
      · have hxm : x < (m : ℝ) := lt_of_le_of_ne (not_lt.mp h2) (hne_x m hm).symm
        rw [if_pos h1, if_neg h2, if_pos ⟨hxm, h1.le⟩]; ring
    · have hxhm : x + h ≤ (m : ℝ) := not_lt.mp h1
      have h2 : ¬ (m : ℝ) < x := not_lt.mpr (by linarith)
      rw [if_neg h1, if_neg h2,
        if_neg (fun hc => hne_xh m hm (le_antisymm hc.2 hxhm))]; ring
  rw [key]
  by_cases hc : x < (m : ℝ) ∧ (m : ℝ) ≤ x + h
  · rw [if_pos hc, if_pos hc, mul_one]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- **S-A collapsed (the explicit `2·collapsed` target).**  The `c = 1`, MR-range
specialization of `Aperron_short_interval`: on `‖aₘ‖ ≤ 1`, `X ≤ m ≤ 4X`, `X ≤ x`,
`x + h ≤ 2X`, the short-interval Perron bridge lands the explicit
`(x/T)·(log T + log X)`-grade constant `2·(12·(π+2·log(1+T)) + (32X/T)·(1+log(3X)))`.
Chains `Aperron_short_interval` (at `c = 1`) with `zone_sum_collapsed` (the zone arithmetic
of `PerronZones.lean`) at both endpoints `x + h` and `x`.

The hypothesis `x + h ≤ 2X` is the honest scope: `zone_sum_collapsed`'s `x ≤ 2X` step must
hold at the *upper* endpoint `x + h`.  For `x` near `2X` (where `x + h > 2X`) the caller uses
the general `Aperron_short_interval` (the collapse constant grows only by `h/X = o(1)`). -/
theorem Aperron_short_interval_collapsed (a : ℕ → ℂ) (s0 : Finset ℕ) {X x h T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hT : 0 < T) (hx : X ≤ x) (hxh2 : x + h ≤ 2 * X)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hne_x : ∀ m ∈ s0, (m : ℝ) ≠ x) (hne_xh : ∀ m ∈ s0, (m : ℝ) ≠ x + h) :
    ‖(I * ∫ v in (-T)..T,
          (∑ m ∈ s0, a m / (m : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            * (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)
               - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I))
            / ((1 : ℂ) + (v : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I
            * ∑ m ∈ s0, a m
                * ((if 1 < (x + h) / m then (1 : ℂ) else 0)
                   - (if 1 < x / m then (1 : ℂ) else 0))‖
      ≤ 2 * (12 * (Real.pi + 2 * Real.log (1 + T)) + (32 * X / T) * (1 + Real.log (3 * X))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : ∀ m ∈ s0, 0 < m := fun m hm => by
    exact_mod_cast (show (0 : ℝ) < m by linarith [(hrange m hm).1])
  have hmain := Aperron_short_interval a s0 (c := 1) hx0 hh one_pos hT hpos hne_x hne_xh
  refine hmain.trans ?_
  -- normalize the `c = 1` powers/`T/1` to `zone_sum_collapsed`'s shape at each endpoint
  have hrw : ∀ y : ℝ, (∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ)) ^ (1 : ℝ)
          * min (Real.pi + 2 * Real.log (1 + T / 1)) (1 / (T * |Real.log (y / m)|))))
        = ∑ m ∈ s0, ‖a m‖ * (2 * (y / (m : ℝ))
          * min (Real.pi + 2 * Real.log (1 + T)) (1 / (T * |Real.log (y / m)|))) := by
    intro y
    exact Finset.sum_congr rfl fun m _ => by rw [Real.rpow_one, div_one]
  rw [hrw (x + h), hrw x]
  have h1 := zone_sum_collapsed a s0 hX hT (by linarith : X ≤ x + h) hxh2 ha hrange
  have h2 := zone_sum_collapsed a s0 hX hT hx (by linarith : x ≤ 2 * X) ha hrange
  linarith [h1, h2]

/-! ## S-D — the weighted max-term tail -/

/-- The exact geometric partial sum `∑_{k<N} 2^{−k} = 2 − 2·2^{−N}`. -/
private lemma geom_half_sum_eq (N : ℕ) :
    ∑ k ∈ Finset.range N, ((2 : ℝ) ^ k)⁻¹ = 2 - 2 * ((2 : ℝ) ^ N)⁻¹ := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ, mul_inv]; ring

/-- **S-D per-block bound.**  On a dyadic block `[T, 2T]` (`T > 0`) the smoothed-kernel tail
integral is controlled by the weighted mean-square `Msup`:
`∫_T^{2T} G(t)·(min b (2/t))² dt ≤ 4·Msup/(W·T)`.
Uses `min b (2/t) ≤ 2/t ≤ 2/T` on the block (so `(min …)² ≤ (2/T)²`), then the weight
hypothesis `(W/T)·∫_T^{2T} G ≤ Msup`.  `G ≥ 0`, `G` continuous, `b ≥ 0`, `W > 0`. -/
theorem dyadic_tail_block {G : ℝ → ℝ} {b W Msup T : ℝ}
    (hT : 0 < T) (hW : 0 < W) (hb : 0 ≤ b) (hGnn : ∀ t, 0 ≤ G t) (hGc : Continuous G)
    (hMsup : (W / T) * (∫ t in T..2 * T, G t) ≤ Msup) :
    (∫ t in T..2 * T, G t * (min b (2 / t)) ^ 2) ≤ 4 * Msup / (W * T) := by
  have hT2 : T ≤ 2 * T := by linarith
  have hne : ∀ t ∈ uIcc T (2 * T), (t : ℝ) ≠ 0 := by
    intro t ht; rw [uIcc_of_le hT2, mem_Icc] at ht; linarith [ht.1]
  have hker : ContinuousOn (fun t : ℝ => min b (2 / t)) (uIcc T (2 * T)) :=
    continuousOn_const.inf (continuousOn_const.div continuousOn_id hne)
  have hint1 : IntervalIntegrable (fun t => G t * (min b (2 / t)) ^ 2) volume T (2 * T) :=
    (hGc.continuousOn.mul (hker.pow 2)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t => G t * (2 / T) ^ 2) volume T (2 * T) :=
    (hGc.mul continuous_const).intervalIntegrable T (2 * T)
  -- pointwise kernel cap
  have hmono : (∫ t in T..2 * T, G t * (min b (2 / t)) ^ 2)
      ≤ ∫ t in T..2 * T, G t * (2 / T) ^ 2 := by
    refine intervalIntegral.integral_mono_on hT2 hint1 hint2 (fun t ht => ?_)
    rw [mem_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hcap : (min b (2 / t)) ^ 2 ≤ (2 / T) ^ 2 := by
      have h1 : 0 ≤ min b (2 / t) := le_min hb (by positivity)
      have h2 : min b (2 / t) ≤ 2 / T :=
        le_trans (min_le_right _ _)
          (div_le_div_of_nonneg_left (by norm_num) hT ht.1)
      exact pow_le_pow_left₀ h1 h2 2
    exact mul_le_mul_of_nonneg_left hcap (hGnn t)
  -- turn the weight hypothesis into `∫ G ≤ Msup·T/W`
  have hIG : (∫ t in T..2 * T, G t) ≤ Msup * (T / W) := by
    have hmul := mul_le_mul_of_nonneg_right hMsup (div_pos hT hW).le
    rwa [show (W / T) * (∫ t in T..2 * T, G t) * (T / W) = (∫ t in T..2 * T, G t) by
      field_simp] at hmul
  calc (∫ t in T..2 * T, G t * (min b (2 / t)) ^ 2)
      ≤ ∫ t in T..2 * T, G t * (2 / T) ^ 2 := hmono
    _ = (∫ t in T..2 * T, G t) * (2 / T) ^ 2 := by rw [intervalIntegral.integral_mul_const]
    _ ≤ (Msup * (T / W)) * (2 / T) ^ 2 := by
        apply mul_le_mul_of_nonneg_right hIG (by positivity)
    _ = 4 * Msup / (W * T) := by field_simp; ring

/-- **S-D dyadic tail (proper, uniform in `N`).**  Summing `dyadic_tail_block` over the
geometric tiling of `[Tmax, 2^N·Tmax]`: for every `N`,
`∫_{Tmax}^{2^N·Tmax} G(t)·(min b (2/t))² dt ≤ 8·Msup/(W·Tmax)`.
The `8` is `4·∑_k 2^{−k}` (geometric, `< 4·2`).  `Msup` is any uniform bound for the weighted
mean-square `(W/T)·∫_T^{2T} G` over `T ≥ Tmax`; `G ≥ 0` continuous, `b, Msup ≥ 0`, `W, Tmax > 0`. -/
theorem dyadic_tail_proper {G : ℝ → ℝ} {b W Msup Tmax : ℝ}
    (hTmax : 0 < Tmax) (hW : 0 < W) (hb : 0 ≤ b) (hMsup0 : 0 ≤ Msup)
    (hGnn : ∀ t, 0 ≤ G t) (hGc : Continuous G)
    (hMsup : ∀ T : ℝ, Tmax ≤ T → (W / T) * (∫ t in T..2 * T, G t) ≤ Msup)
    (N : ℕ) :
    (∫ t in Tmax..(2 ^ N * Tmax), G t * (min b (2 / t)) ^ 2) ≤ 8 * Msup / (W * Tmax) := by
  have hApos : ∀ k : ℕ, (0 : ℝ) < 2 ^ k * Tmax := fun k => mul_pos (pow_pos (by norm_num) k) hTmax
  have hArec : ∀ k : ℕ, (2 : ℝ) ^ (k + 1) * Tmax = 2 * (2 ^ k * Tmax) := fun k => by
    rw [pow_succ]; ring
  have hTle : ∀ k : ℕ, Tmax ≤ 2 ^ k * Tmax := fun k =>
    le_mul_of_one_le_left hTmax.le (one_le_pow₀ (by norm_num))
  -- block integrability, for the telescope
  have hInt : ∀ S : ℝ, 0 < S →
      IntervalIntegrable (fun t => G t * (min b (2 / t)) ^ 2) volume S (2 * S) := by
    intro S hS
    have hS2 : S ≤ 2 * S := by linarith
    have hne : ∀ t ∈ uIcc S (2 * S), (t : ℝ) ≠ 0 := by
      intro t ht; rw [uIcc_of_le hS2, mem_Icc] at ht; linarith [ht.1]
    have hker : ContinuousOn (fun t : ℝ => min b (2 / t)) (uIcc S (2 * S)) :=
      continuousOn_const.inf (continuousOn_const.div continuousOn_id hne)
    exact (hGc.continuousOn.mul (hker.pow 2)).intervalIntegrable
  -- telescope the dyadic blocks
  have htel : ∑ k ∈ Finset.range N,
        ∫ t in (2 ^ k * Tmax)..(2 ^ (k + 1) * Tmax), G t * (min b (2 / t)) ^ 2
      = ∫ t in (2 ^ 0 * Tmax)..(2 ^ N * Tmax), G t * (min b (2 / t)) ^ 2 := by
    refine intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k => (2 : ℝ) ^ k * Tmax) (fun k _ => ?_)
    rw [hArec k]; exact hInt _ (hApos k)
  -- per-block bound
  have hblock : ∀ k ∈ Finset.range N,
      (∫ t in (2 ^ k * Tmax)..(2 ^ (k + 1) * Tmax), G t * (min b (2 / t)) ^ 2)
        ≤ 4 * Msup / (W * (2 ^ k * Tmax)) := by
    intro k _
    rw [hArec k]
    exact dyadic_tail_block (hApos k) hW hb hGnn hGc (hMsup _ (hTle k))
  -- geometric sum of the block bounds
  have hlast : ∑ k ∈ Finset.range N, 4 * Msup / (W * (2 ^ k * Tmax)) ≤ 8 * Msup / (W * Tmax) := by
    have hfac : ∀ k, 4 * Msup / (W * (2 ^ k * Tmax))
        = (4 * Msup / (W * Tmax)) * ((2 : ℝ) ^ k)⁻¹ := by
      intro k
      rw [show W * (2 ^ k * Tmax) = W * Tmax * 2 ^ k by ring, ← div_div, div_eq_mul_inv]
    have hsum_eq : ∑ k ∈ Finset.range N, 4 * Msup / (W * (2 ^ k * Tmax))
        = (4 * Msup / (W * Tmax)) * ∑ k ∈ Finset.range N, ((2 : ℝ) ^ k)⁻¹ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hfac k
    have hC0 : 0 ≤ 4 * Msup / (W * Tmax) := div_nonneg (by linarith) (by positivity)
    rw [hsum_eq]
    calc (4 * Msup / (W * Tmax)) * ∑ k ∈ Finset.range N, ((2 : ℝ) ^ k)⁻¹
        ≤ (4 * Msup / (W * Tmax)) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [geom_half_sum_eq]
          have : (0 : ℝ) ≤ ((2 : ℝ) ^ N)⁻¹ := by positivity
          linarith
      _ = 8 * Msup / (W * Tmax) := by ring
  calc (∫ t in Tmax..(2 ^ N * Tmax), G t * (min b (2 / t)) ^ 2)
      = ∫ t in (2 ^ 0 * Tmax)..(2 ^ N * Tmax), G t * (min b (2 / t)) ^ 2 := by
        rw [pow_zero, one_mul]
    _ = ∑ k ∈ Finset.range N,
          ∫ t in (2 ^ k * Tmax)..(2 ^ (k + 1) * Tmax), G t * (min b (2 / t)) ^ 2 := htel.symm
    _ ≤ ∑ k ∈ Finset.range N, 4 * Msup / (W * (2 ^ k * Tmax)) := Finset.sum_le_sum hblock
    _ ≤ 8 * Msup / (W * Tmax) := hlast

end Salt.MR
