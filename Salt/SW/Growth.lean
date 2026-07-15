/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BV.PolyaVinogradov

/-!
# The SW rung, node S2-Z1 — the L-function growth bound

Design: `docs/blueprints/sw.md`, wave S2 (the L'/L zero-counting cluster). This module
supplies the `M`-hypothesis of `Salt.SW.LFunction_zero_count_le` (see
`Salt/SW/ZeroCount.lean`): a polynomial growth bound for the Dirichlet L-function of a
primitive character, valid in the strip that the Jensen disks reach.

## Route (Abel/partial summation + the identity theorem)

For a primitive `χ` mod `f ≥ 2` (hence `χ ≠ 1`) set `Sχ(n) = ∑_{k < n} χ(k)`, bounded by
`√f·(1+log f)` uniformly in `n` (the landed `Salt.BV.polya_vinogradov`). Partial summation
of the Dirichlet series gives, for `Re s > 1`,
`L(s,χ) = ∑' i, Sχ(i+1)·(i^{-s} − (i+1)^{-s})`  (`growthSum`).
The right-hand side is analytic on the whole half-plane `Re s > 0` (a locally-uniform limit
of holomorphic terms, `differentiableOn_tsum_of_summable_norm`), and mathlib's `LFunction χ`
is entire; by the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`)
the two agree on all of `Re s > 0`. Bounding the series termwise
(`‖i^{-s} − (i+1)^{-s}‖ ≤ ‖s‖·i^{−Re s−1}` by the mean-value inequality, then a
`p`-series/integral comparison `∑ i^{−Re s−1} ≤ 1 + 1/Re s`) yields
`‖L(s,χ)‖ ≤ (1 + 1/Re s)·‖s‖·√f·(1+log f)`.

## Main results

* `LFunction_growth` — the stated S2 target: for `1/2 ≤ Re s ≤ 4`,
  `‖L(s,χ)‖ ≤ 3·(1+‖s‖)·√f·(1+log f)`.
* `LFunction_growth_sphere` — the disk-sup corollary in exactly the `hbnd` shape that
  `LFunction_zero_count_le` consumes: on the sphere `|z − (2+it₀)| = 7/4`,
  `‖L(z,χ)‖ ≤ 5·(4+|t₀|)·√f·(1+log f)`.
-/

namespace Salt.SW

open Complex Metric Filter Finset MeasureTheory DirichletCharacter Salt.BV
open scoped LSeries.notation Topology

/-! ## The partial-summation series -/

/-- The `i`-th term of the Abel-summation representation of the L-function:
`Sχ(i+1)·(i^{-s} − (i+1)^{-s})` with `Sχ(m) = ∑_{k < m} χ(k)`. -/
noncomputable def growthTerm {f : ℕ} (χ : DirichletCharacter ℂ f) (s : ℂ) (i : ℕ) : ℂ :=
  (∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)) * ((i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s))

/-- `√f·(1+log f) ≥ 0` for `f ≥ 2` (the Pólya–Vinogradov bound is nonnegative). -/
lemma sqrtlog_nonneg {f : ℕ} (hf : 2 ≤ f) : (0 : ℝ) ≤ Real.sqrt f * (1 + Real.log f) := by
  have hlog : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)

variable {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)

/-! ### The termwise difference bound (mean-value inequality) -/

/-- `‖i^{-s} − (i+1)^{-s}‖ ≤ ‖s‖·i^{−Re s−1}` for `i ≥ 1`, via the mean value inequality
applied to `t ↦ t^{-s}` on `[i, i+1]` (derivative `−s·t^{−s−1}`, norm `≤ ‖s‖·i^{−Re s−1}`). -/
lemma cpow_diff_bound (s : ℂ) (hσ : 0 < s.re) {i : ℕ} (hi : 1 ≤ i) :
    ‖(i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hs0 : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have hsne : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  set φ : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hφ
  have hderiv : ∀ t ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
      HasDerivWithinAt φ ((-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (i : ℝ) ((i : ℝ) + 1)) t := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hi0 (Set.mem_Icc.mp ht).1
    exact (hasDerivAt_ofReal_cpow_const htpos.ne' hsne).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hi0 (Set.mem_Icc.mp ht).1
    have hti : (i : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-s - 1).re = -(s.re + 1) := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hi0 hti (by linarith)
  have hmvt := (convex_Icc (i : ℝ) ((i : ℝ) + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  have e1 : φ ((i : ℝ) + 1) = ((i : ℂ) + 1) ^ (-s) := by
    change ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = ((i : ℂ) + 1) ^ (-s)
    push_cast; ring_nf
  have e2 : φ (i : ℝ) = (i : ℂ) ^ (-s) := by
    change (((i : ℝ) : ℝ) : ℂ) ^ (-s) = (i : ℂ) ^ (-s)
    rw [Complex.ofReal_natCast]
  rw [e1, e2] at hmvt
  simp only [show ((i : ℝ) + 1) - (i : ℝ) = 1 from by ring, norm_one, mul_one] at hmvt
  rw [norm_sub_rev]
  exact hmvt

/-! ### The per-term norm bound -/

/-- `‖growthTerm χ s i‖ ≤ √f·(1+log f)·‖s‖·i^{−Re s−1}` (the `i = 0` term vanishes because
`Sχ(1) = χ(0) = 0`). -/
lemma growthTerm_norm_le (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (s : ℂ) (hσ : 0 < s.re) (i : ℕ) :
    ‖growthTerm χ s i‖ ≤ Real.sqrt f * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : (∑ k ∈ Finset.range (0 + 1), χ (k : ZMod f)) = 0 := by
      have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
      simp [hchi0]
    have hRHS : Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖
        * ((0 : ℕ) : ℝ) ^ (-(s.re + 1)) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by intro h; nlinarith [hσ]), mul_zero]
    rw [hRHS]
    simp only [growthTerm, h0, zero_mul, norm_zero, le_refl]
  · have hb := cpow_diff_bound s hσ hi
    have hpc := polya_vinogradov χ hχ hf (i + 1)
    rw [growthTerm, norm_mul]
    calc ‖∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)‖
            * ‖(i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s)‖
        ≤ (Real.sqrt f * (1 + Real.log f)) * (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
          mul_le_mul hpc hb (norm_nonneg _) (sqrtlog_nonneg hf)
      _ = Real.sqrt f * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by ring

/-- The dominating series is summable, hence `growthTerm χ s` is summable, for `Re s > 0`. -/
lemma growthTerm_summable (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (s : ℂ) (hσ : 0 < s.re) :
    Summable (growthTerm χ s) := by
  have hdom : Summable
      (fun i : ℕ => Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hns : Summable (fun i => ‖growthTerm χ s i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => growthTerm_norm_le χ hχ hf s hσ i) hdom
  exact hns.of_norm

/-! ### The `p`-series/integral bound -/

/-- `∑' i, i^{−Re s−1} ≤ 1 + 1/Re s` for `Re s > 0`, by splitting off `i = 0, 1` and comparing
the tail with `∫_1^∞ x^{−Re s−1} dx = 1/Re s`. -/
lemma dser_tsum_le (s : ℂ) (hσ : 0 < s.re) :
    ∑' (i : ℕ), (i : ℝ) ^ (-(s.re + 1)) ≤ 1 + 1 / s.re := by
  set σ := s.re with hσdef
  set g : ℕ → ℝ := fun i => (i : ℝ) ^ (-(σ + 1)) with hg
  have hexp : -(σ + 1) < -1 := by linarith
  have hsummable : Summable g := Real.summable_nat_rpow.mpr hexp
  have hshift := hsummable.sum_add_tsum_nat_add 2
  have hr2 : (∑ i ∈ Finset.range 2, g i) = 1 := by
    rw [hg]
    rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
      Real.zero_rpow (by linarith), Real.one_rpow]
    ring
  have hpartial : ∀ n : ℕ, ∑ i ∈ Finset.range n, g (i + 2) ≤ 1 / σ := by
    intro n
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-(σ + 1))) (Set.Icc (1 : ℝ) (1 + (n : ℝ))) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono (by
        intro x hx; exact lt_of_lt_of_le one_pos (Set.mem_Icc.mp hx).1)
    have hcmp := hanti.sum_le_integral
    have hL : (∑ i ∈ Finset.range n, g (i + 2))
        = ∑ i ∈ Finset.range n, (fun x : ℝ => x ^ (-(σ + 1))) (1 + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _
      change ((i + 2 : ℕ) : ℝ) ^ (-(σ + 1)) = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(σ + 1))
      congr 1; push_cast; ring
    rw [hL]
    refine le_trans hcmp ?_
    have h1n : (1 : ℝ) ≤ 1 + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    rw [intervalIntegral.integral_of_le h1n]
    have hIoi : IntegrableOn (fun x : ℝ => x ^ (-(σ + 1))) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hexp one_pos
    have hmono : ∫ x in Set.Ioc (1 : ℝ) (1 + (n : ℝ)), x ^ (-(σ + 1))
        ≤ ∫ x in Set.Ioi (1 : ℝ), x ^ (-(σ + 1)) := by
      apply setIntegral_mono_set hIoi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (le_of_lt (lt_trans one_pos hx)) _
      · exact Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx)
    refine le_trans hmono (le_of_eq ?_)
    rw [integral_Ioi_rpow_of_lt hexp one_pos, show -(σ + 1) + 1 = -σ from by ring, Real.one_rpow]
    field_simp
  have htail : ∑' (i : ℕ), g (i + 2) ≤ 1 / σ :=
    Real.tsum_le_of_sum_range_le (fun i => Real.rpow_nonneg (by positivity) _) hpartial
  rw [hr2] at hshift
  rw [← hshift]
  linarith [htail]

/-! ### The norm bound on the series -/

/-- `‖growthSum χ s‖ ≤ √f·(1+log f)·‖s‖·(1 + 1/Re s)` for `Re s > 0`. -/
lemma norm_growthSum_le (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (s : ℂ) (hσ : 0 < s.re) :
    ‖∑' i, growthTerm χ s i‖ ≤ Real.sqrt f * (1 + Real.log f) * ‖s‖ * (1 + 1 / s.re) := by
  have hdom : Summable
      (fun i : ℕ => Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hns : Summable (fun i => ‖growthTerm χ s i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => growthTerm_norm_le χ hχ hf s hσ i) hdom
  have hBnn : (0 : ℝ) ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) := sqrtlog_nonneg hf
  calc ‖∑' i, growthTerm χ s i‖
      ≤ ∑' i, ‖growthTerm χ s i‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' (i : ℕ), Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) :=
        hns.tsum_le_tsum (fun i => growthTerm_norm_le χ hχ hf s hσ i) hdom
    _ = Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * ∑' (i : ℕ), (i : ℝ) ^ (-(s.re + 1)) :=
        tsum_mul_left
    _ ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖s‖ * (1 + 1 / s.re) :=
        mul_le_mul_of_nonneg_left (dser_tsum_le s hσ) (mul_nonneg hBnn (norm_nonneg s))

/-! ### Analyticity of the series on the right half-plane -/

/-- `growthSum χ` is differentiable on the open right half-plane `Re s > 0`. -/
lemma growthSum_differentiableOn (hχ : χ.IsPrimitive) (hf : 2 ≤ f) :
    DifferentiableOn ℂ (fun s => ∑' i, growthTerm χ s i) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hσ0 : 0 < s₀.re := hs₀
  set d := s₀.re / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hballsub : ∀ w ∈ Metric.ball s₀ d, d < w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |w.re - s₀.re| ≤ ‖w - s₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s₀)
    have h2 : -‖w - s₀‖ ≤ w.re - s₀.re := neg_le_of_abs_le h1
    linarith [hw, h2, hd]
  have hwne : ∀ w ∈ Metric.ball s₀ d, w ≠ 0 := by
    intro w hw h
    have hb := hballsub w hw
    rw [h] at hb; simp only [Complex.zero_re] at hb; linarith [hdpos]
  have huniform : DifferentiableOn ℂ (fun s => ∑' i, growthTerm χ s i) (Metric.ball s₀ d) := by
    apply differentiableOn_tsum_of_summable_norm
      (F := fun i w => growthTerm χ w i)
      (u := fun i => Real.sqrt (f : ℝ) * (1 + Real.log f) * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1)))
    · exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
    · intro i
      change DifferentiableOn ℂ (fun w : ℂ =>
        (∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)) * ((i : ℂ) ^ (-w) - ((i : ℂ) + 1) ^ (-w)))
        (Metric.ball s₀ d)
      have hneg : DifferentiableOn ℂ (fun w : ℂ => -w) (Metric.ball s₀ d) :=
        (differentiable_id.neg).differentiableOn
      have hd1 : DifferentiableOn ℂ (fun w : ℂ => (i : ℂ) ^ (-w)) (Metric.ball s₀ d) :=
        hneg.const_cpow (Or.inr (fun w hw => neg_ne_zero.mpr (hwne w hw)))
      have hd2 : DifferentiableOn ℂ (fun w : ℂ => ((i : ℂ) + 1) ^ (-w)) (Metric.ball s₀ d) :=
        hneg.const_cpow (Or.inr (fun w hw => neg_ne_zero.mpr (hwne w hw)))
      exact (hd1.sub hd2).const_mul _
    · exact Metric.isOpen_ball
    · intro i w hw
      have hwre : d < w.re := hballsub w hw
      have hσw : 0 < w.re := lt_trans hdpos hwre
      have hwnorm : ‖w‖ ≤ ‖s₀‖ + d := by
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
          _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + d := by linarith [hw.le]
      have hpow : (i : ℝ) ^ (-(w.re + 1)) ≤ (i : ℝ) ^ (-(d + 1)) := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi; rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
        · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hi) (by linarith)
      calc ‖growthTerm χ w i‖
          ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖w‖ * (i : ℝ) ^ (-(w.re + 1)) :=
            growthTerm_norm_le χ hχ hf w hσw i
        _ ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1)) := by
            have hBnn : (0 : ℝ) ≤ Real.sqrt (f : ℝ) * (1 + Real.log f) := sqrtlog_nonneg hf
            have e1 : Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖w‖ * (i : ℝ) ^ (-(w.re + 1))
                = (Real.sqrt (f : ℝ) * (1 + Real.log f) * ‖w‖) * (i : ℝ) ^ (-(w.re + 1)) := by ring
            have e2 : Real.sqrt (f : ℝ) * (1 + Real.log f) * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1))
                = (Real.sqrt (f : ℝ) * (1 + Real.log f) * (‖s₀‖ + d)) * (i : ℝ) ^ (-(d + 1)) := by
              ring
            rw [e1, e2]
            apply mul_le_mul _ hpow (Real.rpow_nonneg (Nat.cast_nonneg i) _) (by positivity)
            exact mul_le_mul_of_nonneg_left hwnorm hBnn
  exact (huniform.differentiableAt (Metric.ball_mem_nhds s₀ hdpos)).differentiableWithinAt

/-! ### The identity: `L = growthSum` on `Re s > 0` -/

/-- `χ ≠ 1` for a primitive character of level `≥ 2`. -/
lemma ne_one_of_isPrimitive (hχ : χ.IsPrimitive) (hf : 2 ≤ f) : χ ≠ 1 := by
  intro h
  have h1 : conductor χ = 1 := h ▸ conductor_one
  have h2 : conductor χ = f := hχ
  omega

/-- The partial-summation identity on the region of absolute convergence `Re s > 1`. -/
lemma LFunction_eq_growthSum_of_one_lt (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (s : ℂ) (hs1 : 1 < s.re) :
    LFunction χ s = ∑' i, growthTerm χ s i := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  have hσ : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
  -- term identity: `i^{-s}·χ(i) = LSeries.term ↗χ s i`
  have hterm_eq : ∀ i : ℕ, (i : ℂ) ^ (-s) * χ (i : ZMod f) = LSeries.term ↗χ s i := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp [LSeries.term_zero, hchi0]
    · rw [LSeries.term_of_ne_zero hi.ne' ↗χ s, Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  -- L-series convergence and partial-sum tendsto
  have hLsum : Summable (LSeries.term ↗χ s) := LSeriesSummable_of_one_lt_re χ hs1
  have hLFeq : LFunction χ s = LSeries ↗χ s := LFunction_eq_LSeries χ hs1
  have hAtendsto : Tendsto (fun n => ∑ i ∈ Finset.range n, LSeries.term ↗χ s i)
      atTop (𝓝 (LFunction χ s)) := by
    rw [hLFeq]; exact hLsum.hasSum.tendsto_sum_nat
  -- summation by parts, evaluated at `n+1` to avoid `n-1`
  have hSBP : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
      = (n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))
        + ∑ i ∈ Finset.range n, growthTerm χ s i := by
    intro n
    have hbp := Finset.sum_range_by_parts (fun i => (i : ℂ) ^ (-s))
      (fun i => χ (i : ZMod f)) (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hbp
    have hpt : ∀ i : ℕ, ((↑(i + 1) : ℂ) ^ (-s) - (i : ℂ) ^ (-s))
        * (∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)) = -growthTerm χ s i := by
      intro i; simp only [growthTerm]; push_cast; ring
    have hdiffsum : (∑ i ∈ Finset.range n, ((↑(i + 1) : ℂ) ^ (-s) - (i : ℂ) ^ (-s))
        * (∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)))
        = -∑ i ∈ Finset.range n, growthTerm χ s i := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i)]
      exact Finset.sum_neg_distrib _
    calc (∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
        = ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ (-s) * χ (i : ZMod f) :=
          Finset.sum_congr rfl (fun i _ => (hterm_eq i).symm)
      _ = (n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))
          - ∑ i ∈ Finset.range n, ((↑(i + 1) : ℂ) ^ (-s) - (i : ℂ) ^ (-s))
            * (∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)) := hbp
      _ = (n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))
          + ∑ i ∈ Finset.range n, growthTerm χ s i := by rw [hdiffsum, sub_neg_eq_add]
  -- the boundary term vanishes in the limit
  have hnormcpow : ∀ n : ℕ, ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow (neg_ne_zero.mpr hs0), norm_zero,
        Real.zero_rpow (neg_ne_zero.mpr hσ.ne')]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
  have hbdry : Tendsto
      (fun n : ℕ => (n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f)))
      atTop (𝓝 0) := by
    have hg_tendsto : Tendsto
        (fun n : ℕ => (n : ℝ) ^ (-s.re) * (Real.sqrt (f : ℝ) * (1 + Real.log f)))
        atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
      simpa using h0.mul_const (Real.sqrt (f : ℝ) * (1 + Real.log f))
    have hbnd : ∀ n : ℕ,
        ‖(n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))‖
          ≤ (n : ℝ) ^ (-s.re) * (Real.sqrt (f : ℝ) * (1 + Real.log f)) := by
      intro n
      rw [norm_mul, hnormcpow n]
      exact mul_le_mul_of_nonneg_left (polya_vinogradov χ hχ hf (n + 1))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact squeeze_zero_norm hbnd hg_tendsto
  -- assemble the three limits
  have hpart : Tendsto (fun n => ∑ i ∈ Finset.range n, growthTerm χ s i)
      atTop (𝓝 (∑' i, growthTerm χ s i)) :=
    (growthTerm_summable χ hχ hf s hσ).hasSum.tendsto_sum_nat
  have hshift_tendsto : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
      atTop (𝓝 (LFunction χ s)) := hAtendsto.comp (tendsto_add_atTop_nat 1)
  have hcombined : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
      atTop (𝓝 (0 + ∑' i, growthTerm χ s i)) :=
    (hbdry.add hpart).congr (fun n => (hSBP n).symm)
  have huniq := tendsto_nhds_unique hshift_tendsto hcombined
  rwa [zero_add] at huniq

/-- The identity `L(s,χ) = growthSum χ s` extended to all of `Re s > 0` by the identity theorem. -/
lemma LFunction_eq_growthSum (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (s : ℂ) (hσ : 0 < s.re) :
    LFunction χ s = ∑' i, growthTerm χ s i := by
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
    have hm : (0 : ℝ) < min x.re y.re := lt_min hx hy
    calc (0 : ℝ) < min x.re y.re := hm
      _ = (a + b) * min x.re y.re := by rw [hab, one_mul]
      _ = a * min x.re y.re + b * min x.re y.re := by ring
      _ ≤ a * x.re + b * y.re := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (min_le_left _ _) ha
          · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hb
  have hana_L : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hne).differentiableOn.analyticOnNhd hopen
  have hana_G : AnalyticOnNhd ℂ (fun z => ∑' i, growthTerm χ z i) {z : ℂ | 0 < z.re} :=
    (growthSum_differentiableOn χ hχ hf).analyticOnNhd hopen
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), LFunction χ z = ∑' i, growthTerm χ z i := by
    have hgt : ∀ᶠ z in 𝓝 (2 : ℂ), LFunction χ z = ∑' i, growthTerm χ z i := by
      have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
        simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
      filter_upwards [hopen1.mem_nhds h2'] with z hz
      exact LFunction_eq_growthSum_of_one_lt χ hχ hf z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have heqOn := hana_L.eqOn_of_preconnected_of_frequently_eq hana_G hconv.isPreconnected h2 hfreq
  exact heqOn hσ

/-! ## The growth bound -/

/-- **S2-Z1 — the L-function growth bound.** For a primitive Dirichlet character `χ` mod `f ≥ 2`
and `1/2 ≤ Re s ≤ 4`,
`‖L(s,χ)‖ ≤ 3·(1+‖s‖)·√f·(1+log f)`.

Route: `L = growthSum` on `Re s > 0` (`LFunction_eq_growthSum`), then the series bound
`‖growthSum‖ ≤ √f(1+log f)·‖s‖·(1+1/Re s)` (`norm_growthSum_le`); for `Re s ≥ 1/2`,
`1 + 1/Re s ≤ 3`. -/
theorem LFunction_growth (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) (_hs2 : s.re ≤ 4) :
    ‖LFunction χ s‖ ≤ 3 * (1 + ‖s‖) * Real.sqrt f * (1 + Real.log f) := by
  have hσ : 0 < s.re := by linarith
  rw [LFunction_eq_growthSum χ hχ hf s hσ]
  have hbound := norm_growthSum_le χ hχ hf s hσ
  set P := Real.sqrt (f : ℝ) * (1 + Real.log f) with hP
  have hPnn : (0 : ℝ) ≤ P := by rw [hP]; exact sqrtlog_nonneg hf
  have h1 : 1 + 1 / s.re ≤ 3 := by
    have : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hσ]; linarith
    linarith
  rw [show (3 : ℝ) * (1 + ‖s‖) * Real.sqrt f * (1 + Real.log f) = 3 * (1 + ‖s‖) * P from by
    rw [hP]; ring]
  refine le_trans hbound ?_
  have hSr : ‖s‖ * (1 + 1 / s.re) ≤ 3 * (1 + ‖s‖) := by nlinarith [h1, norm_nonneg s]
  calc P * ‖s‖ * (1 + 1 / s.re) = P * (‖s‖ * (1 + 1 / s.re)) := by ring
    _ ≤ P * (3 * (1 + ‖s‖)) := mul_le_mul_of_nonneg_left hSr hPnn
    _ = 3 * (1 + ‖s‖) * P := by ring

/-- **The disk-sup corollary** (exactly the `hbnd` shape `LFunction_zero_count_le` consumes).
On the sphere `|z − (2+it₀)| = 7/4` (whose real parts lie in `[1/4, 15/4]`),
`‖L(z,χ)‖ ≤ 5·(4+|t₀|)·√f·(1+log f)`. -/
theorem LFunction_growth_sphere (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t₀ : ℝ) :
    ∀ z ∈ Metric.sphere (2 + (t₀ : ℂ) * I) (7 / 4),
      ‖LFunction χ z‖ ≤ 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) := by
  intro z hz
  rw [Metric.mem_sphere, Complex.dist_eq] at hz
  have hcre : (2 + (t₀ : ℂ) * I).re = 2 := by simp
  have hzc : |z.re - 2| ≤ 7 / 4 := by
    have := Complex.abs_re_le_norm (z - (2 + (t₀ : ℂ) * I))
    rw [Complex.sub_re, hcre, hz] at this
    exact this
  have hzre : (1 : ℝ) / 4 ≤ z.re := by
    have := abs_le.mp hzc; linarith [this.1]
  have hσ : 0 < z.re := by linarith
  rw [LFunction_eq_growthSum χ hχ hf z hσ]
  have hbound := norm_growthSum_le χ hχ hf z hσ
  set P := Real.sqrt (f : ℝ) * (1 + Real.log f) with hP
  have hPnn : (0 : ℝ) ≤ P := by rw [hP]; exact sqrtlog_nonneg hf
  -- `1 + 1/Re z ≤ 5`
  have h1 : 1 + 1 / z.re ≤ 5 := by
    have : 1 / z.re ≤ 4 := by rw [div_le_iff₀ hσ]; linarith
    linarith
  -- `‖z‖ ≤ 4 + |t₀|`
  have hznorm : ‖z‖ ≤ 4 + |t₀| := by
    have hcnorm : ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ 2 + |t₀| := by
      calc ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t₀ : ℂ) * I‖ := norm_add_le _ _
        _ = 2 + |t₀| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            norm_num
    calc ‖z‖ = ‖(2 + (t₀ : ℂ) * I) + (z - (2 + (t₀ : ℂ) * I))‖ := by ring_nf
      _ ≤ ‖(2 + (t₀ : ℂ) * I)‖ + ‖z - (2 + (t₀ : ℂ) * I)‖ := norm_add_le _ _
      _ ≤ (2 + |t₀|) + 7 / 4 := by rw [hz]; linarith [hcnorm]
      _ ≤ 4 + |t₀| := by linarith
  rw [show (5 : ℝ) * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) = 5 * (4 + |t₀|) * P from by
    rw [hP]; ring]
  refine le_trans hbound ?_
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsr : ‖z‖ * (1 + 1 / z.re) ≤ (4 + |t₀|) * 5 :=
    mul_le_mul hznorm h1 (by positivity) (by positivity)
  calc P * ‖z‖ * (1 + 1 / z.re) = P * (‖z‖ * (1 + 1 / z.re)) := by ring
    _ ≤ P * ((4 + |t₀|) * 5) := mul_le_mul_of_nonneg_left hsr hPnn
    _ = 5 * (4 + |t₀|) * P := by ring

end Salt.SW
