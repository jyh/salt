/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZetaPartialFractions

/-!
# The SW rung, node A1-ab — the half-box zero count `N(T)`-local

Design: `docs/exploration/s2-trackA-design.md` (node A1-ab). This module lands the
half-box zero count for `ζ`: the number of zeros `ρ` of `riemannZeta` with
`1/2 ≤ Re ρ < 1` and `|Im ρ − t| ≤ 1`, counted with multiplicity, is
`≤ C·log(|t|+2)` with an explicit `C`.

## The route (the landed disk-Jensen apparatus)

The entire function `Zc s = (s−1)·ζ(s)` (`Salt/SW/ZetaPartialFractions.lean`) has exactly
the zeros of `ζ` off `s = 1` (with `Zc(1) = 1 ≠ 0`), so counting zeros of `Zc` in a disk
counts zeros of `ζ`. The pole of `ζ` at `s = 1` is therefore a non-issue — `Zc` is entire,
and the fixed-radius Jensen count `entire_zero_count_le` applies **uniformly in `t`**, with
no small-`t`/large-`t` split (the `s = 1` disk-membership contributes `divisor = 0` since
`Zc(1) ≠ 0`).

The half-box `{Re ∈ [1/2,1), |Im−t| ≤ 1}` sits inside `closedBall (2 + t·i) (37/20)`
(its farthest corner `(1/2, t±1)` is at distance `√(9/4+1) = √(13/4) ≈ 1.803 < 37/20`),
uniformly in `t`. We take the Jensen sphere at the **wider** radius `R = 39/20 = 1.95`
(reaching `Re ≈ 1/20 > 0`, still in the `Zc_growth` half-plane), re-deriving the growth
quantity `M0box` there (the `M0zeta`-style estimate at the wider disk). With `r = 37/20`,
`R = 39/20`, `R/r = 39/37`, the count is `≤ log(4·M0box)/log(39/37) ≤ C·log(|t|+2)` with
`C = 11/log(39/37)`.

## III.3″ witness

At `T = 10⁶` the constant `C = 11/log(39/37) ≈ 209` gives `≈ 209·log(10⁶+2) ≈ 2886`; the
true local zero count is `≈ 4.4` — the constant is loose (~45× before the `log`), but the
**rate** `O(log(|t|+2))` is correct, which is what the `ζ′/ζ` zero-sum wall consumes.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The wide growth quantity `M0box` and its logarithmic collapse -/

/-- The wide growth-sphere quantity at height `t`: `M0box(t) = 1 + 21(99/20+|t|)(79/20+|t|)`,
an `O((|t|+2)²)` bound on `‖Zc‖` valid on the sphere `|z − (2+t·i)| = 39/20` (which reaches
`Re z ≥ 1/20`, so `1 + 1/Re z ≤ 21`). Wider analogue of `M0zeta`. -/
noncomputable def M0box (t : ℝ) : ℝ := 1 + 21 * (99 / 20 + |t|) * (79 / 20 + |t|)

lemma one_le_M0box (t : ℝ) : 1 ≤ M0box t := by
  rw [M0box]
  have h1 : (0 : ℝ) ≤ 99 / 20 + |t| := by have := abs_nonneg t; linarith
  have h2 : (0 : ℝ) ≤ 79 / 20 + |t| := by have := abs_nonneg t; linarith
  nlinarith [mul_nonneg h1 h2]

/-- `log(4·M0box(t)) ≤ 11·log(|t|+2)` — the `O(log(|t|+2))` collapse of the wide growth
quantity (`4·M0box(t) ≤ 412(|t|+2)²`, `log 412 ≤ 9 log 2 ≤ 9 log(|t|+2)`). -/
lemma log_4M0box_le (t : ℝ) : Real.log (4 * M0box t) ≤ 11 * Real.log (|t| + 2) := by
  have hx : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hbnd : 4 * M0box t ≤ 412 * (|t| + 2) ^ 2 := by rw [M0box]; nlinarith [hx]
  have hpos : (0 : ℝ) < 4 * M0box t := by have := one_le_M0box t; linarith
  have hlog412 : Real.log 412 ≤ 9 * Real.log (|t| + 2) := by
    have h9 : Real.log 412 ≤ 9 * Real.log 2 := by
      rw [show (9 : ℝ) * Real.log 2 = Real.log (2 ^ (9 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hlog2 : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  calc Real.log (4 * M0box t) ≤ Real.log (412 * (|t| + 2) ^ 2) := Real.log_le_log hpos hbnd
    _ = Real.log 412 + 2 * Real.log (|t| + 2) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ 11 * Real.log (|t| + 2) := by linarith [hlog412]

/-! ## 2. The wide sphere growth bound for `Zc` -/

/-- **The wide sphere growth bound for `Zc`.** On the sphere `|z − (2+t·i)| = 39/20`
(so `Re z ≥ 1/20 > 0`), `‖Zc z‖ ≤ M0box t`. Wider analogue of `Zc_sphere_bound`
(there capped at `R ≤ 7/4`), from `Zc_growth`. -/
lemma Zc_sphere_bound_wide (t : ℝ) {z : ℂ} (hz : ‖z - (2 + (t : ℂ) * I)‖ = 39 / 20) :
    ‖Zc z‖ ≤ M0box t := by
  have hcre : (2 + (t : ℂ) * I).re = 2 := by simp
  have hzc_re : (1 : ℝ) / 20 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * I))
    rw [Complex.sub_re, hcre, hz] at h
    have := abs_le.mp h; linarith [this.1]
  have hre_pos : 0 < z.re := by linarith
  have hcnorm : ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ 2 + |t| := by
    calc ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hznorm : ‖z‖ ≤ 79 / 20 + |t| := by
    calc ‖z‖ = ‖(2 + (t : ℂ) * I) + (z - (2 + (t : ℂ) * I))‖ := by ring_nf
      _ ≤ ‖(2 : ℂ) + (t : ℂ) * I‖ + ‖z - (2 + (t : ℂ) * I)‖ := norm_add_le _ _
      _ ≤ (2 + |t|) + 39 / 20 := by rw [hz]; linarith [hcnorm]
      _ = 79 / 20 + |t| := by ring
  have hz1norm : ‖z - 1‖ ≤ 99 / 20 + |t| := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖z‖ + 1 := by rw [norm_one]
      _ ≤ 99 / 20 + |t| := by linarith [hznorm]
  have h1re : (0 : ℝ) ≤ 1 / z.re := div_nonneg zero_le_one hre_pos.le
  have hinv : 1 + 1 / z.re ≤ 21 := by
    have h20 : 1 / z.re ≤ 20 := by rw [div_le_iff₀ hre_pos]; linarith [hzc_re]
    linarith
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hA : ‖z‖ * (1 + 1 / z.re) ≤ (79 / 20 + |t|) * 21 :=
    mul_le_mul hznorm hinv (by linarith [h1re]) (by linarith [habs])
  have hAnn : (0 : ℝ) ≤ ‖z‖ * (1 + 1 / z.re) := mul_nonneg (norm_nonneg _) (by linarith [h1re])
  have hB : ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) ≤ (99 / 20 + |t|) * ((79 / 20 + |t|) * 21) :=
    mul_le_mul hz1norm hA hAnn (by linarith [habs])
  rw [M0box]
  calc ‖Zc z‖ ≤ 1 + ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) := Zc_growth hre_pos
    _ ≤ 1 + (99 / 20 + |t|) * ((79 / 20 + |t|) * 21) := by linarith [hB]
    _ = 1 + 21 * (99 / 20 + |t|) * (79 / 20 + |t|) := by ring

/-! ## 3. The primary divisor-sum count (with multiplicity) -/

/-- The half-box zero-count constant: `C = 11/log(39/37) ≈ 209`. -/
noncomputable def zetaBoxConst : ℝ := 11 / Real.log (39 / 37)

lemma zetaBoxConst_pos : 0 < zetaBoxConst :=
  div_pos (by norm_num) (Real.log_pos (by norm_num))

/-- **A1-ab, the divisor form.** The zeros of `Zc` (equivalently of `ζ` off `s = 1`) in the
disk `closedBall (2+t·i) (37/20)` — which contains the half-box `{Re ∈ [1/2,1), |Im−t| ≤ 1}`
— counted with multiplicity (the finsupp divisor sum), number `≤ C·log(|t|+2)`,
`C = 11/log(39/37)`, uniformly in `t`. -/
theorem zeta_box_divisor_le (t : ℝ) :
    ((∑ᶠ u, divisor Zc (closedBall (2 + (t : ℂ) * I) (37 / 20)) u : ℤ) : ℝ)
      ≤ zetaBoxConst * Real.log (|t| + 2) := by
  have hbnd : ∀ z ∈ sphere (2 + (t : ℂ) * I) (39 / 20), ‖Zc z‖ ≤ M0box t := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact Zc_sphere_bound_wide t hz
  have hcount := entire_zero_count_le Zc_differentiable (Zc_center_lower t)
    (show (0 : ℝ) < 37 / 20 by norm_num) (show (37 / 20 : ℝ) < 39 / 20 by norm_num)
    (one_le_M0box t) hbnd
  rw [show (39 / 20 : ℝ) / (37 / 20) = 39 / 37 by norm_num] at hcount
  have hlogpos : 0 < Real.log (39 / 37) := Real.log_pos (by norm_num)
  calc ((∑ᶠ u, divisor Zc (closedBall (2 + (t : ℂ) * I) (37 / 20)) u : ℤ) : ℝ)
      ≤ Real.log (4 * M0box t) / Real.log (39 / 37) := hcount
    _ ≤ 11 * Real.log (|t| + 2) / Real.log (39 / 37) :=
        (div_le_div_iff_of_pos_right hlogpos).mpr (log_4M0box_le t)
    _ = zetaBoxConst * Real.log (|t| + 2) := by unfold zetaBoxConst; ring

/-! ## 4. The cardinality corollary (multiplicity `≥ 1`) -/

/-- `Zc` is entire and not identically zero (`Zc 1 = 1`), so its analytic order is finite
everywhere: the identity theorem forbids a whole-neighborhood of zeros. -/
lemma Zc_analyticOrderAt_ne_top (ρ : ℂ) : analyticOrderAt Zc ρ ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ z in 𝓝 ρ, Zc z = 0 := analyticOrderAt_eq_top.mp htop
  have hana : AnalyticOnNhd ℂ Zc (Set.univ : Set ℂ) :=
    Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have heq : Set.EqOn Zc 0 Set.univ :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ)
      (by filter_upwards [hev] with z hz; simpa using hz)
  have h1 : Zc 1 = 0 := heq (Set.mem_univ 1)
  rw [Zc_one] at h1; exact one_ne_zero h1

/-- **Multiplicity `≥ 1` at a zero.** For `Zc` analytic on `U`, a zero `ρ ∈ U` of `Zc`
contributes `≥ 1` to the divisor. -/
lemma one_le_divisor_Zc {ρ : ℂ} {U : Set ℂ} (hana : AnalyticOnNhd ℂ Zc U)
    (hρU : ρ ∈ U) (hZcρ : Zc ρ = 0) : (1 : ℤ) ≤ divisor Zc U ρ := by
  have hne0 : analyticOrderAt Zc ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hana ρ hρU, hZcρ⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Zc_analyticOrderAt_ne_top ρ)
  have hk0 : k ≠ 0 := by rintro rfl; exact hne0 (by rw [← hk]; simp)
  have hval : divisor Zc U ρ = (k : ℤ) := by rw [hana.divisor_apply hρU, ← hk]; simp
  rw [hval]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0

/-- **A1-ab, the cardinality corollary.** Any finite set `S` of distinct zeros of `ζ` in the
half-box `{Re ∈ [1/2,1), |Im−t| ≤ 1}` has `#S ≤ C·log(|t|+2)`, `C = 11/log(39/37)`, uniformly
in `t`. (The box lies in `closedBall (2+t·i) (37/20)`; each zero contributes multiplicity `≥ 1`
to the divisor sum bounded by `zeta_box_divisor_le`.) -/
theorem zeta_box_count_half (t : ℝ) {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1) :
    (S.card : ℝ) ≤ zetaBoxConst * Real.log (|t| + 2) := by
  set U : Set ℂ := closedBall (2 + (t : ℂ) * I) (37 / 20) with hU
  have hana : AnalyticOnNhd ℂ Zc U :=
    (Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hone : ∀ ρ ∈ S, (1 : ℤ) ≤ divisor Zc U ρ := by
    intro ρ hρ
    obtain ⟨hζ, hlo, hhi, him⟩ := hS ρ hρ
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
    have hZcρ : Zc ρ = 0 := by rw [Zc_eq_of_ne hρ1, hζ, mul_zero]
    have hρU : ρ ∈ U := by
      rw [hU, mem_closedBall, dist_eq_norm]
      have hdecomp : ρ - (2 + (t : ℂ) * I)
          = ((ρ.re - 2 : ℝ) : ℂ) + ((ρ.im - t : ℝ) : ℂ) * I := by
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
            Complex.mul_re, Complex.mul_im]
      rw [hdecomp, Complex.norm_add_mul_I]
      have hsq : (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 ≤ (37 / 20) ^ 2 := by
        nlinarith [abs_le.mp him, hlo, hhi]
      calc Real.sqrt ((ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2)
          ≤ Real.sqrt ((37 / 20) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 37 / 20 := Real.sqrt_sq (by norm_num)
    exact one_le_divisor_Zc hana hρU hZcρ
  have hnn : ∀ u, (0 : ℤ) ≤ divisor Zc U u := hana.divisor_nonneg
  have hfin : (Function.support (fun u => divisor Zc U u)).Finite :=
    (divisor Zc U).finiteSupport (by rw [hU]; exact isCompact_closedBall _ _)
  have hSsub : S ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hone ρ hρ; omega
  have heq : (∑ᶠ u, divisor Zc U u) = ∑ u ∈ hfin.toFinset, divisor Zc U u :=
    finsum_eq_finsetSum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
  have hcard_le : (S.card : ℤ) ≤ ∑ᶠ u, divisor Zc U u := by
    rw [heq]
    calc (S.card : ℤ) = ∑ _ρ ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ ρ ∈ S, divisor Zc U ρ := Finset.sum_le_sum hone
      _ ≤ ∑ ρ ∈ hfin.toFinset, divisor Zc U ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun i _ _ => hnn i)
  have hbound := zeta_box_divisor_le t
  rw [← hU] at hbound
  calc (S.card : ℝ) ≤ ((∑ᶠ u, divisor Zc U u : ℤ) : ℝ) := by exact_mod_cast hcard_le
    _ ≤ zetaBoxConst * Real.log (|t| + 2) := hbound

end Salt.SW
