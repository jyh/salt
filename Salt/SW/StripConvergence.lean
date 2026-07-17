/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Growth

/-!
# Strip convergence for Dirichlet L-series (HB-ENGINE / WP2, node DH-STRIP)

For a non-principal Dirichlet character `χ` mod `f` the ordered partial sums of the naive
Dirichlet series converge to the analytic continuation `LFunction χ` throughout the open right
half-plane `Re s > 0` — a range on which the series is *not* absolutely convergent, so mathlib's
`LFunction_eq_LSeries` (valid only for `Re s > 1`) does not apply. This is a genuine mathlib gap
on the critical path of the Deuring–Heilbronn detector (`DHDetector`).

## Route (Abel summation + the identity theorem, parametric in the character-sum bound)

Everything is stated *parametrically* in a bound `M` on the partial character sums
`‖∑_{k<u} χ(k)‖ ≤ M` (any such bound works; the corpus supplies `√f·(1+log f)` via
`Salt.BV.polya_vinogradov` for primitive `χ`, the "√q log q" grade the DH-2a probe used).

The heart is the summation-by-parts identity
`∑_{n=1}^{N} χ(n) n^{-s} = N^{-s}·(∑_{k≤N} χ(k)) + ∑_{i<N} growthTerm χ s i`
(`partial_eq`, `growthTerm` from `Salt/SW/Growth.lean`). As `N → ∞`:

* the boundary term `N^{-s}·(∑_{k≤N} χ(k))` tends to `0` (its norm is `≤ M·N^{-Re s}`);
* the growth-series partial sums tend to `∑' i, growthTerm χ s i`, which equals `LFunction χ s`
  on all of `Re s > 0` (`LFunction_eq_growthSum'`, re-derived parametrically by the identity
  theorem exactly as in `Growth.lean`).

## Main results

* `tendsto_partialLSeries` — the qualitative convergence `∑_{n≤N} χ(n) n^{-s} → LFunction χ s`.
* `norm_LFunction_sub_partial_le` — the quantitative tail bound (the shape DH-2b consumes):
  `‖LFunction χ s − ∑_{n≤N} χ(n) n^{-s}‖ ≤ M·(1 + ‖s‖·(1 + 1/Re s))·N^{-Re s}`.
* `norm_LFunction_sub_partial_le_strip` — the exact `C·(1 + ‖s‖/Re s)·N^{-Re s}` shape on the
  interesting strip `0 < Re s ≤ 1`, with `C = 3M`.
* Primitive-character instantiations (`tendsto_partialLSeries_primitive`, …) with
  `M = √f·(1+log f)`.
-/

namespace Salt.SW

open Complex Filter Finset MeasureTheory DirichletCharacter Salt.BV
open scoped LSeries.notation Topology

/-! ## A p-series tail estimate (pure real analysis) -/

/-- **Shifted p-series tail bound.** For `σ > 0` and `N ≥ 1`,
`∑_{i≥0} (i+N)^{−σ−1} ≤ N^{−σ}·(1 + 1/σ)` (integral comparison, base `N`). This is the
`Growth.dser_tsum_le` estimate refined to a decaying tail. -/
lemma tail_dser_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∑' i : ℕ, ((i + N : ℕ) : ℝ) ^ (-(σ + 1)) ≤ (N : ℝ) ^ (-σ) * (1 + 1 / σ) := by
  have hexp : -(σ + 1) < -1 := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set φ : ℝ → ℝ := fun x => x ^ (-(σ + 1)) with hφ
  have hsummable : Summable (fun i : ℕ => ((i + N : ℕ) : ℝ) ^ (-(σ + 1))) :=
    (summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr hexp)
  -- the tail past the first term, bounded by `∫_N^∞ x^{−σ−1} = N^{−σ}/σ`
  have htail : ∑' i : ℕ, ((i + 1 + N : ℕ) : ℝ) ^ (-(σ + 1)) ≤ (N : ℝ) ^ (-σ) / σ := by
    refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun n => ?_)
    · positivity
    have hanti : AntitoneOn φ (Set.Icc (N : ℝ) ((N : ℝ) + n)) := by
      apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -(σ + 1) ≤ 0)).mono
      intro x hx; exact lt_of_lt_of_le hNpos (Set.mem_Icc.mp hx).1
    have hcmp := hanti.sum_le_integral
    have hL : (∑ i ∈ Finset.range n, ((i + 1 + N : ℕ) : ℝ) ^ (-(σ + 1)))
        = ∑ i ∈ Finset.range n, φ ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _
      change ((i + 1 + N : ℕ) : ℝ) ^ (-(σ + 1)) = ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-(σ + 1))
      congr 1; push_cast; ring
    rw [hL]
    refine le_trans hcmp ?_
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg n))]
    have hIoi : IntegrableOn φ (Set.Ioi (N : ℝ)) := integrableOn_Ioi_rpow_of_lt hexp hNpos
    have hmono : ∫ x in Set.Ioc (N : ℝ) ((N : ℝ) + n), φ x ≤ ∫ x in Set.Ioi (N : ℝ), φ x := by
      apply setIntegral_mono_set hIoi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (le_of_lt (lt_trans hNpos hx)) _
      · exact Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx)
    refine le_trans hmono (le_of_eq ?_)
    rw [integral_Ioi_rpow_of_lt hexp hNpos]
    rw [show -(σ + 1) + 1 = -σ from by ring, neg_div_neg_eq]
  -- assemble: peel the first term, then compare
  rw [hsummable.tsum_eq_zero_add]
  simp only [Nat.zero_add]
  have h1 : (N : ℝ) ^ (-(σ + 1)) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  rw [mul_add, mul_one, mul_one_div]
  linarith [htail, h1]

/-! ## Norm of a complex power at a natural (matches `Growth`'s inline `hnormcpow`) -/

/-- `‖(n : ℂ)^{−s}‖ = n^{−Re s}` (real), valid at `n = 0` too since `0 < Re s`. -/
lemma norm_natCast_cpow_neg {s : ℂ} (hσ : 0 < s.re) (n : ℕ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (neg_ne_zero.mpr hs0), norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr hσ.ne')]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]

/-! ## Parametric growth-series machinery (mirrors `Growth`, with `M` for `√f·(1+log f)`) -/

variable {f : ℕ} (χ : DirichletCharacter ℂ f)

/-- Parametric per-term bound: `‖growthTerm χ s i‖ ≤ M·‖s‖·i^{−Re s−1}`, where `M` bounds the
partial character sums. Mirror of `Growth.growthTerm_norm_le` with `M` in place of the
Pólya–Vinogradov constant. -/
lemma growthTerm_norm_le' (hf : 2 ≤ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M)
    (s : ℂ) (hσ : 0 < s.re) (i : ℕ) :
    ‖growthTerm χ s i‖ ≤ M * ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : (∑ k ∈ Finset.range (0 + 1), χ (k : ZMod f)) = 0 := by
      have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
      simp [hchi0]
    have hRHS : M * ‖s‖ * ((0 : ℕ) : ℝ) ^ (-(s.re + 1)) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by intro h; nlinarith [hσ]), mul_zero]
    rw [hRHS]
    simp only [growthTerm, h0, zero_mul, norm_zero, le_refl]
  · have hb := cpow_diff_bound s hσ hi
    have hpc := hM (i + 1)
    rw [growthTerm, norm_mul]
    calc ‖∑ k ∈ Finset.range (i + 1), χ (k : ZMod f)‖
            * ‖(i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s)‖
        ≤ M * (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) := mul_le_mul hpc hb (norm_nonneg _) hM0
      _ = M * ‖s‖ * (i : ℝ) ^ (-(s.re + 1)) := by ring

/-- Parametric summability of `growthTerm χ s` for `Re s > 0`. -/
lemma growthTerm_summable' (hf : 2 ≤ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M)
    (s : ℂ) (hσ : 0 < s.re) : Summable (growthTerm χ s) := by
  have hdom : Summable (fun i : ℕ => M * ‖s‖ * (i : ℝ) ^ (-(s.re + 1))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hns : Summable (fun i => ‖growthTerm χ s i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => growthTerm_norm_le' χ hf hM0 hM s hσ i) hdom
  exact hns.of_norm

/-- Parametric differentiability of `growthSum χ` on the open right half-plane `Re s > 0`
(locally-uniform limit of the entire terms). Mirror of `Growth.growthSum_differentiableOn`. -/
lemma growthSum_differentiableOn' (hf : 2 ≤ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M) :
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
      (u := fun i => M * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1)))
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
          ≤ M * ‖w‖ * (i : ℝ) ^ (-(w.re + 1)) := growthTerm_norm_le' χ hf hM0 hM w hσw i
        _ ≤ M * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1)) := by
            have e1 : M * ‖w‖ * (i : ℝ) ^ (-(w.re + 1))
                = (M * ‖w‖) * (i : ℝ) ^ (-(w.re + 1)) := by ring
            have e2 : M * (‖s₀‖ + d) * (i : ℝ) ^ (-(d + 1))
                = (M * (‖s₀‖ + d)) * (i : ℝ) ^ (-(d + 1)) := by ring
            rw [e1, e2]
            apply mul_le_mul _ hpow (Real.rpow_nonneg (Nat.cast_nonneg i) _) (by positivity)
            exact mul_le_mul_of_nonneg_left hwnorm hM0
  exact (huniform.differentiableAt (Metric.ball_mem_nhds s₀ hdpos)).differentiableWithinAt

/-! ## Summation by parts for the ordered partial sum -/

/-- **Abel summation.** `∑_{i≤N} i^{−s}·χ(i) = N^{−s}·(∑_{i≤N} χ(i)) + ∑_{i<N} growthTerm χ s i`.
Pure algebra (character/`s`-agnostic); the `growthTerm` telescoping of `Growth.hSBP`. -/
lemma partial_summation (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (i : ℂ) ^ (-s) * χ (i : ZMod f)
      = (N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f))
        + ∑ i ∈ Finset.range N, growthTerm χ s i := by
  have hbp := Finset.sum_range_by_parts (fun i => (i : ℂ) ^ (-s))
    (fun i => χ (i : ZMod f)) (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hbp
  have hpt : ∀ i : ℕ, ((↑(i + 1) : ℂ) ^ (-s) - (i : ℂ) ^ (-s))
      * (∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)) = -growthTerm χ s i := by
    intro i; simp only [growthTerm]; push_cast; ring
  have hdiffsum : (∑ i ∈ Finset.range N, ((↑(i + 1) : ℂ) ^ (-s) - (i : ℂ) ^ (-s))
      * (∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)))
      = -∑ i ∈ Finset.range N, growthTerm χ s i := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact Finset.sum_neg_distrib _
  rw [hbp, hdiffsum, sub_neg_eq_add]

/-- Reindex the `Finset.Icc 1 N` partial sum to the `Finset.range (N+1)` form (the `i = 0` term
vanishes since `χ 0 = 0`), matching the order-flipped `Growth` product `i^{−s}·χ(i)`. -/
lemma icc_sum_eq_range (hf : 2 ≤ f) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s)
      = ∑ i ∈ Finset.range (N + 1), (i : ℂ) ^ (-s) * χ (i : ZMod f) := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
  rw [Finset.sum_range_succ' (fun i => (i : ℂ) ^ (-s) * χ (i : ZMod f)) N]
  simp only [Nat.cast_zero, hchi0, mul_zero, add_zero]
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) from by ext x; simp,
      Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.add_comm 1 i]; ring

/-- The boundary term `N^{−s}·(∑_{i≤N} χ(i))` tends to `0` as `N → ∞` (its norm is `≤ M·N^{−Re s}`
and `Re s > 0`). Mirror of `Growth.hbdry`, parametric in `M`. -/
lemma boundary_tendsto_zero {M : ℝ}
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M) {s : ℂ} (hσ : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f)))
      Filter.atTop (𝓝 0) := by
  have hg_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-s.re) * M) Filter.atTop (𝓝 0) := by
    have h0 := (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
    simpa using h0.mul_const M
  have hbnd : ∀ n : ℕ,
      ‖(n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))‖ ≤ (n : ℝ) ^ (-s.re) * M := by
    intro n
    rw [norm_mul, norm_natCast_cpow_neg hσ n]
    exact mul_le_mul_of_nonneg_left (hM (n + 1)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact squeeze_zero_norm hbnd hg_tendsto

/-! ## The identity `L = growthSum` (parametric, non-principal `χ`) -/

section Identity

variable [NeZero f]

/-- Parametric partial-summation identity on `Re s > 1`. Mirror of
`Growth.LFunction_eq_growthSum_of_one_lt`, with `hM` in place of Pólya–Vinogradov. -/
lemma LFunction_eq_growthSum_of_one_lt' (hf : 2 ≤ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M)
    (s : ℂ) (hs1 : 1 < s.re) : LFunction χ s = ∑' i, growthTerm χ s i := by
  haveI : Fact (1 < f) := ⟨by omega⟩
  have hσ : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have hchi0 : χ (0 : ZMod f) = 0 := MulChar.map_nonunit χ not_isUnit_zero
  have hterm_eq : ∀ i : ℕ, (i : ℂ) ^ (-s) * χ (i : ZMod f) = LSeries.term ↗χ s i := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp [LSeries.term_zero, hchi0]
    · rw [LSeries.term_of_ne_zero hi.ne' ↗χ s, Complex.cpow_neg, div_eq_mul_inv, mul_comm]
  have hLsum : Summable (LSeries.term ↗χ s) := LSeriesSummable_of_one_lt_re χ hs1
  have hLFeq : LFunction χ s = LSeries ↗χ s := LFunction_eq_LSeries χ hs1
  have hAtendsto : Tendsto (fun n => ∑ i ∈ Finset.range n, LSeries.term ↗χ s i)
      atTop (𝓝 (LFunction χ s)) := by
    rw [hLFeq]; exact hLsum.hasSum.tendsto_sum_nat
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
  have hbdry : Tendsto
      (fun n : ℕ => (n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f)))
      atTop (𝓝 0) := by
    have hg_tendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ (-s.re) * M) atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
      simpa using h0.mul_const M
    have hbnd : ∀ n : ℕ,
        ‖(n : ℂ) ^ (-s) * (∑ i ∈ Finset.range (n + 1), χ (i : ZMod f))‖
          ≤ (n : ℝ) ^ (-s.re) * M := by
      intro n
      rw [norm_mul, norm_natCast_cpow_neg hσ n]
      exact mul_le_mul_of_nonneg_left (hM (n + 1)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact squeeze_zero_norm hbnd hg_tendsto
  have hpart : Tendsto (fun n => ∑ i ∈ Finset.range n, growthTerm χ s i)
      atTop (𝓝 (∑' i, growthTerm χ s i)) :=
    (growthTerm_summable' χ hf hM0 hM s hσ).hasSum.tendsto_sum_nat
  have hshift_tendsto : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
      atTop (𝓝 (LFunction χ s)) := hAtendsto.comp (tendsto_add_atTop_nat 1)
  have hcombined : Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), LSeries.term ↗χ s i)
      atTop (𝓝 (0 + ∑' i, growthTerm χ s i)) :=
    (hbdry.add hpart).congr (fun n => (hSBP n).symm)
  have huniq := tendsto_nhds_unique hshift_tendsto hcombined
  rwa [zero_add] at huniq

/-- Parametric identity `L(s,χ) = ∑' growthTerm χ s` on all of `Re s > 0`, by the identity
theorem. Mirror of `Growth.LFunction_eq_growthSum` for non-principal `χ`. -/
lemma LFunction_eq_growthSum' (hne : χ ≠ 1) (hf : 2 ≤ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M)
    (s : ℂ) (hσ : 0 < s.re) : LFunction χ s = ∑' i, growthTerm χ s i := by
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
    (growthSum_differentiableOn' χ hf hM0 hM).analyticOnNhd hopen
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), LFunction χ z = ∑' i, growthTerm χ z i := by
    have hgt : ∀ᶠ z in 𝓝 (2 : ℂ), LFunction χ z = ∑' i, growthTerm χ z i := by
      have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
        simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
      filter_upwards [hopen1.mem_nhds h2'] with z hz
      exact LFunction_eq_growthSum_of_one_lt' χ hf hM0 hM z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have heqOn := hana_L.eqOn_of_preconnected_of_frequently_eq hana_G hconv.isPreconnected h2 hfreq
  exact heqOn hσ

/-! ## Main results: strip convergence of the ordered partial sums -/

/-- **Strip convergence (qualitative).** For a non-principal Dirichlet character `χ` mod `f ≥ 2`
whose partial character sums are bounded by `M`, the ordered partial sums of the naive Dirichlet
series converge to the analytic continuation `LFunction χ s` throughout `Re s > 0` — including the
critical strip `0 < Re s < 1`, where the series is *not* absolutely convergent. -/
theorem tendsto_partialLSeries (hne : χ ≠ 1) (hf : 2 ≤ f) {M : ℝ}
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s))
      Filter.atTop (𝓝 (LFunction χ s)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hrw : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s))
      = (N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f))
        + ∑ i ∈ Finset.range N, growthTerm χ s i :=
    fun N => by rw [icc_sum_eq_range χ hf s N, partial_summation χ s N]
  have hpart : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, growthTerm χ s i) Filter.atTop
      (𝓝 (∑' i, growthTerm χ s i)) := (growthTerm_summable' χ hf hM0 hM s hs).hasSum.tendsto_sum_nat
  rw [LFunction_eq_growthSum' χ hne hf hM0 hM s hs]
  have hcomb := ((boundary_tendsto_zero χ hM hs).add hpart).congr (fun N => (hrw N).symm)
  simpa using hcomb

/-- **Strip convergence (quantitative tail).** The general-`Re s > 0` bound
`‖L(s,χ) − ∑_{n≤N} χ(n) n^{−s}‖ ≤ M·(1 + ‖s‖·(1 + 1/Re s))·N^{−Re s}`. -/
theorem norm_LFunction_sub_partial_le (hne : χ ≠ 1) (hf : 2 ≤ f) {M : ℝ}
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M) {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s)‖
      ≤ M * (1 + ‖s‖ * (1 + 1 / s.re)) * (N : ℝ) ^ (-s.re) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hsummable : Summable (growthTerm χ s) := growthTerm_summable' χ hf hM0 hM s hs
  have hrw : (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s))
      = (N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f))
        + ∑ i ∈ Finset.range N, growthTerm χ s i := by
    rw [icc_sum_eq_range χ hf s N, partial_summation χ s N]
  have htaileq : ∑' i, growthTerm χ s i - ∑ i ∈ Finset.range N, growthTerm χ s i
      = ∑' i, growthTerm χ s (i + N) := by
    have h := hsummable.sum_add_tsum_nat_add N; rw [← h]; abel
  rw [LFunction_eq_growthSum' χ hne hf hM0 hM s hs, hrw]
  have hsplit : ∑' i, growthTerm χ s i
        - ((N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f))
          + ∑ i ∈ Finset.range N, growthTerm χ s i)
      = ∑' i, growthTerm χ s (i + N)
        - (N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f)) := by
    rw [← htaileq]; abel
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  -- tail bound
  have htail_summable : Summable (fun i => growthTerm χ s (i + N)) :=
    (summable_nat_add_iff N).mpr hsummable
  have hdom : Summable (fun i : ℕ => M * ‖s‖ * ((i + N : ℕ) : ℝ) ^ (-(s.re + 1))) :=
    ((summable_nat_add_iff N).mpr (Real.summable_nat_rpow.mpr (by linarith))).mul_left _
  have htail_norm : ‖∑' i, growthTerm χ s (i + N)‖
      ≤ M * ‖s‖ * ((N : ℝ) ^ (-s.re) * (1 + 1 / s.re)) := by
    calc ‖∑' i, growthTerm χ s (i + N)‖
        ≤ ∑' i, ‖growthTerm χ s (i + N)‖ := norm_tsum_le_tsum_norm htail_summable.norm
      _ ≤ ∑' i, M * ‖s‖ * ((i + N : ℕ) : ℝ) ^ (-(s.re + 1)) :=
          htail_summable.norm.tsum_le_tsum
            (fun i => growthTerm_norm_le' χ hf hM0 hM s hs (i + N)) hdom
      _ = M * ‖s‖ * ∑' i, ((i + N : ℕ) : ℝ) ^ (-(s.re + 1)) := tsum_mul_left
      _ ≤ M * ‖s‖ * ((N : ℝ) ^ (-s.re) * (1 + 1 / s.re)) :=
          mul_le_mul_of_nonneg_left (tail_dser_le hs hN) (by positivity)
  -- boundary bound
  have hbdry_norm : ‖(N : ℂ) ^ (-s) * (∑ i ∈ Finset.range (N + 1), χ (i : ZMod f))‖
      ≤ (N : ℝ) ^ (-s.re) * M := by
    rw [norm_mul, norm_natCast_cpow_neg hs N]
    exact mul_le_mul_of_nonneg_left (hM (N + 1)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hcombine : M * ‖s‖ * ((N : ℝ) ^ (-s.re) * (1 + 1 / s.re)) + (N : ℝ) ^ (-s.re) * M
      = M * (1 + ‖s‖ * (1 + 1 / s.re)) * (N : ℝ) ^ (-s.re) := by ring
  linarith [htail_norm, hbdry_norm, hcombine]

/-- **Quantitative tail on the interesting strip** `0 < Re s ≤ 1`, in the exact
`C·(1 + ‖s‖/Re s)·N^{−Re s}` shape DH-2b consumes, with `C = 3M`. -/
theorem norm_LFunction_sub_partial_le_strip (hne : χ ≠ 1) (hf : 2 ≤ f) {M : ℝ}
    (hM : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod f)‖ ≤ M) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s)‖
      ≤ 3 * M * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine le_trans (norm_LFunction_sub_partial_le χ hne hf hM hs hN) ?_
  have hPnn : (0 : ℝ) ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine mul_le_mul_of_nonneg_right ?_ hPnn
  rw [show 3 * M * (1 + ‖s‖ / s.re) = M * (3 * (1 + ‖s‖ / s.re)) from by ring]
  refine mul_le_mul_of_nonneg_left ?_ hM0
  have hrs : ‖s‖ ≤ ‖s‖ / s.re :=
    (le_div_iff₀ hs).mpr (mul_le_of_le_one_right (norm_nonneg s) hs1)
  have hrσ : (0 : ℝ) ≤ ‖s‖ / s.re := by positivity
  rw [mul_add, mul_one, mul_one_div]
  linarith [hrs, hrσ]

/-! ## Primitive-character instantiations (`M = √f·(1+log f)` via Pólya–Vinogradov) -/

/-- Qualitative strip convergence for a **primitive** character, instantiating `M` with the
Pólya–Vinogradov bound `√f·(1+log f)` (the "√q log q" grade the DH-2a probe used). -/
theorem tendsto_partialLSeries_primitive (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {s : ℂ}
    (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s))
      Filter.atTop (𝓝 (LFunction χ s)) :=
  tendsto_partialLSeries χ (ne_one_of_isPrimitive χ hχ hf) hf
    (fun u => polya_vinogradov χ hχ hf u) hs

/-- Quantitative strip tail for a **primitive** character, `M = √f·(1+log f)`. -/
theorem norm_LFunction_sub_partial_le_primitive (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {s : ℂ}
    (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod f) * (n : ℂ) ^ (-s)‖
      ≤ Real.sqrt f * (1 + Real.log f) * (1 + ‖s‖ * (1 + 1 / s.re)) * (N : ℝ) ^ (-s.re) :=
  norm_LFunction_sub_partial_le χ (ne_one_of_isPrimitive χ hχ hf) hf
    (fun u => polya_vinogradov χ hχ hf u) hs hN

end Identity

end Salt.SW
