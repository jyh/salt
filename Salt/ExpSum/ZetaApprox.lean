/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaGrowth
import Salt.SW.DHContour

/-!
# The Hardy–Littlewood approximate formula and the σ-weighted growth bound (LITTLEWOOD F5)

This file turns the landed phase-sum machinery (`Salt/ExpSum/ZetaGrowth.lean`) into a genuine
`‖ζ(σ+it)‖` growth bound on the closed strip up to `σ = 1` — the region-conversion input.

## F5-1 — the approximate formula (the stone)

The classical Hardy–Littlewood approximation: for `s = σ+it` with `0 < σ` and `N ≥ 1`,
`ζ(s) = ∑_{n≤N} n^{−s} + N^{1−s}/(s−1) − s·∫_N^∞ {u} u^{−s−1} du`, with the fractional-part
tail integral `zetaFracInt N s := ∫_{u>N} {u} u^{−s−1} du` bounded by `N^{−σ}/σ`.  This is a
mathlib-absent classic (the search confirmed: no approximate functional equation, no
`Int.fract`-in-integral form for ζ).

Route (the honest one recorded in the design):
* `zetaFracInt_bound` — `‖zetaFracInt N s‖ ≤ N^{−σ}/σ` (`0 < σ`), a direct integral estimate.
* `zetaFracInt_differentiableAt` — the tail integral is holomorphic on `Re s > 0`
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the `MellinTransform` pattern: `fract` is
  measurable so the continuity hypothesis of mathlib's `mellin` holomorphy is *not* needed).
* `zetaApprox_gt_one` — the identity on `Re s > 1` where everything converges absolutely, by the
  **finite Euler–Maclaurin** identity `(k+1)^{−s} = ∫_k^{k+1} u^{−s} − s∫_k^{k+1} {u} u^{−s−1}`
  (per-unit-interval FTC, antiderivative `g(u) = (u−k) u^{−s}`), summed and taken to the limit.
* `zetaApprox` — the identity on all of `Re s > 0` by the identity theorem (the `StripConvergence`
  pattern), using the corpus `zetaHol` to carry ζ across its pole `s = 1`.
* `norm_zeta_sub_approx_le` (**F5-1**) — the bound form `‖ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1)‖
  ≤ ‖s‖·N^{−σ}/σ`.

## F5-2 — the σ-weighted balance (the node, checkpoint form)

`zeta_growth_strip` — for `σ ∈ [1/2, 1]` and `t ≥ t₀`, choosing `X = ⌊t⌋`,
`‖ζ(σ+it)‖ ≤ C·t^{1−σ}·(1 + log t)`, whence `‖ζ(1+it)‖ ≤ C·(1 + log t) = O(log t)` — a genuine
power saving at `σ = 1`, the classical de la Vallée-Poussin input.  This uses the **trivial**
partial-sum bound `‖∑_{n≤N} n^{−s}‖ ≤ N^{1−σ}(1+log N)`; with `X = ⌊t⌋` the error term
`‖s‖·N^{−σ} ≍ t^{1−σ}` is the exponent bottleneck, so improving the partial sum below `t^{1−σ}`
via the phase-sum power saving (`zeta_partial_growth`) does **not** improve the total at a fixed
truncation — the honest refinement to a sub-`t^{1−σ}` bound in the *open* strip needs the global
window coverage from a single `t`, the recorded residual **LITT-COVER** (the next rung).  The
phase bridge `natCast_cpow_eq_rpow_mul_eR` is provided for that refinement.

## Honesty

`zeta_growth_strip` delivers the checkpoint (a power saving at `σ = 1`).  The Littlewood
`log t / log log t` refinement is LITT-COVER's business; documented, not claimed.
-/

namespace Salt.ExpSum

open Complex Finset MeasureTheory
open scoped Real

/-! ## Section 0 — elementary σ-weighted partial-sum bounds -/

/-- **The trivial partial-sum bound.**  For `σ ≤ 1` and `N ≥ 1`, the σ-weighted head sum obeys
`∑_{1≤n≤N} n^{−σ} ≤ N^{1−σ}·(1 + log N)`.  Route: `n^{−σ} = n^{−1}·n^{1−σ} ≤ n^{−1}·N^{1−σ}`
(monotone `n^{1−σ}` since `1−σ ≥ 0`), then the harmonic bound `∑ n^{−1} ≤ 1 + log N`. -/
lemma sum_Icc_rpow_neg_le {σ : ℝ} (hσ : σ ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) * (1 + Real.log N) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1σ : (0 : ℝ) ≤ 1 - σ := by linarith
  -- termwise: n^{-σ} ≤ N^{1-σ} · n⁻¹
  have hterm : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1
    have hnN : n ≤ N := hn.2
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hpow : (n : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow (le_of_lt hnR) (by exact_mod_cast hnN) h1σ
    calc (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ) ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hnR]; ring_nf
      _ = (n : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
      _ ≤ (N : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
    simp only [Rat.cast_inv, Rat.cast_natCast] at h
    exact h
  exact mul_le_mul_of_nonneg_left hharm (Real.rpow_nonneg (le_of_lt hNR) _)

/-! ## Section 1 — the fractional-part tail integral, its bound and holomorphy -/

/-- The Euler–Maclaurin fractional-part tail `∫_{u>N} {u}·u^{−s−1} du`.  `F5-1` identifies
`ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1)` with `−s` times this. -/
noncomputable def zetaFracInt (N : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (N : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- The integrand's pointwise norm: `‖{u}·u^{−s−1}‖ = {u}·u^{−σ−1} ≤ u^{−σ−1}` on `u > 0`. -/
lemma norm_fracIntegrand_le {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real, Real.norm_eq_abs,
    Complex.sub_re, Complex.neg_re, Complex.one_re]
  have hfr : |Int.fract u| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg u)]; exact le_of_lt (Int.fract_lt_one u)
  calc |Int.fract u| * u ^ (-s.re - 1) ≤ 1 * u ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right hfr (Real.rpow_nonneg (le_of_lt hu) _)
    _ = u ^ (-s.re - 1) := one_mul _

/-- The integrand is `AEStronglyMeasurable` on `Ioi N` (`fract` measurable, `cpow` continuous). -/
lemma fracIntegrand_aesm (N : ℕ) (s : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (lt_of_le_of_lt
      (by exact_mod_cast Nat.zero_le N) hu)))

/-- Integrability of the tail integrand on `Ioi N` (`0 < σ`), dominated by `u^{−σ−1}`. -/
lemma fracIntegrand_integrableOn {s : ℂ} (hσ : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  refine Integrable.mono' hdom (fracIntegrand_aesm N s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_fracIntegrand_le (lt_trans hNpos hu)

/-- **F5-1, the tail bound.**  For `0 < σ = s.re` and `N ≥ 1`,
`‖∫_{u>N} {u}·u^{−s−1} du‖ ≤ N^{−σ}/σ`. -/
lemma zetaFracInt_bound {s : ℂ} (hσ : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖zetaFracInt N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hint := fracIntegrand_integrableOn hσ hN
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  calc ‖zetaFracInt N s‖
      ≤ ∫ u in Set.Ioi (N : ℝ), ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi (N : ℝ), u ^ (-s.re - 1) := by
        refine setIntegral_mono_on hint.norm hdom measurableSet_Ioi (fun u hu => ?_)
        exact norm_fracIntegrand_le (lt_of_lt_of_le hNpos (le_of_lt hu))
    _ = (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hNpos]
        rw [show -s.re - 1 + 1 = -s.re from by ring]
        rw [neg_div, div_neg, neg_neg]

/-- **F5-1, holomorphy of the tail.**  `zetaFracInt N` is complex-differentiable at every
`s₀` with `Re s₀ > 0`.  Route: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the
ball of radius `σ₀/2`, with the `s`-derivative `−log u·{u}·u^{−s−1}` dominated (via
`Real.log_le_rpow_div`) by the integrable `(4/σ₀)·u^{−σ₀/4−1}`. -/
lemma zetaFracInt_differentiableAt (N : ℕ) (hN : 1 ≤ N) {s₀ : ℂ} (hσ₀ : 0 < s₀.re) :
    DifferentiableAt ℂ (zetaFracInt N) s₀ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set σ₀ : ℝ := s₀.re with hσdef
  set v : ℝ := σ₀ / 2 with hvdef
  have hv : 0 < v := by rw [hvdef]; linarith
  set F : ℂ → ℝ → ℂ := fun z u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1) with hF
  set F' : ℂ → ℝ → ℂ :=
    fun z u => ((Int.fract u : ℝ) : ℂ) * ((u : ℂ) ^ (-z - 1) * (Real.log u : ℂ) * (-1)) with hF'
  set μ := volume.restrict (Set.Ioi (N : ℝ)) with hμ
  set bound : ℝ → ℝ := fun u => (4 / σ₀) * u ^ (-σ₀ / 4 - 1) with hbound
  -- ball membership ⟹ `σ₀/2 < Re z`
  have hballre : ∀ z ∈ Metric.ball s₀ v, σ₀ / 2 < z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |z.re - σ₀| ≤ ‖z - s₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - s₀)
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hz)
    linarith [h2.1]
  -- the six hypotheses
  have h1 : ∀ᶠ z in nhds s₀, AEStronglyMeasurable (F z) μ :=
    Filter.Eventually.of_forall (fun z => fracIntegrand_aesm N z)
  have h2 : Integrable (F s₀) μ := fracIntegrand_integrableOn hσ₀ hN
  have h3 : AEStronglyMeasurable (F' s₀) μ := by
    refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_)
      aestronglyMeasurable_const)
    · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact continuousOn_of_forall_continuousAt (fun u hu =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (lt_trans hNpos hu))))
    · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
  have h4 : ∀ᵐ u ∂μ, ∀ z ∈ Metric.ball s₀ v, ‖F' z u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hu0 : (0 : ℝ) < u := lt_trans hNpos hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt (lt_of_le_of_lt hN1 hu)
    have hzre : σ₀ / 2 < z.re := hballre z hz
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    -- ‖F' z u‖ = |fract u| · u^{-Re z - 1} · |log u|
    have hnorm : ‖F' z u‖ = |Int.fract u| * u ^ (-z.re - 1) * |Real.log u| := by
      simp only [hF', norm_mul, norm_neg, norm_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re,
        Complex.neg_re, Complex.one_re]
      ring
    rw [hnorm, abs_of_nonneg (Int.fract_nonneg u), abs_of_nonneg hlog0]
    have hfr1 : Int.fract u ≤ 1 := le_of_lt (Int.fract_lt_one u)
    -- bound the power and the log
    have hpow : u ^ (-z.re - 1) ≤ u ^ (-σ₀ / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by linarith [hzre])
    have hlogle : Real.log u ≤ u ^ (σ₀ / 4) / (σ₀ / 4) :=
      Real.log_le_rpow_div (le_of_lt hu0) (by linarith)
    have he : u ^ (-σ₀ / 2 - 1) * u ^ (σ₀ / 4) = u ^ (-σ₀ / 4 - 1) := by
      rw [← Real.rpow_add hu0]; congr 1; ring
    have key : ∀ A : ℝ, A / (σ₀ / 4) = 4 / σ₀ * A := by
      intro A; rw [div_div_eq_mul_div, div_eq_mul_inv, div_eq_mul_inv]; ring
    calc Int.fract u * u ^ (-z.re - 1) * Real.log u
        ≤ 1 * u ^ (-σ₀ / 2 - 1) * (u ^ (σ₀ / 4) / (σ₀ / 4)) := by
          gcongr
      _ = (4 / σ₀) * u ^ (-σ₀ / 4 - 1) := by
          rw [one_mul, ← mul_div_assoc, he, key]
  have h5 : Integrable bound μ := by
    have hi : IntegrableOn (fun u : ℝ => u ^ (-σ₀ / 4 - 1)) (Set.Ioi (N : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
    exact hi.const_mul (4 / σ₀)
  have h6 : ∀ᵐ u ∂μ, ∀ z ∈ Metric.ball s₀ v, HasDerivAt (fun z => F z u) (F' z u) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z _
    have hu0 : (0 : ℝ) < u := lt_trans hNpos hu
    have ht' : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu0)
    have hlin : HasDerivAt (fun z : ℂ => -z - 1) (-1) z := by
      simpa using (hasDerivAt_id z).neg.sub_const 1
    have hcpow := hlin.const_cpow (Or.inl ht')
    rw [← Complex.ofReal_log (le_of_lt hu0)] at hcpow
    simpa only [hF, hF'] using hcpow.const_mul (((Int.fract u : ℝ) : ℂ))
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hv) h1 h2 h3 h4 h5 h6
  exact main.2.differentiableAt

/-- Holomorphy on the open right half-plane `{Re s > 0}`. -/
lemma zetaFracInt_differentiableOn (N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ (zetaFracInt N) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (zetaFracInt_differentiableAt N hN hs).differentiableWithinAt

/-! ## Section 2 — the finite Euler–Maclaurin identity and the value on `Re s > 1` -/

/-- Interval integrability of `u ↦ (u:ℂ)^r` on `[k,k+1]` for `k ≥ 1` (continuity, `0 ∉ [k,k+1]`). -/
lemma cpow_intervalIntegrable {r : ℂ} {k : ℕ} (hk : 1 ≤ k) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ r) volume (k : ℝ) ((k : ℝ) + 1) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine (ContinuousOn.intervalIntegrable ?_)
  refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
  have hupos : 0 < u := lt_of_lt_of_le hkR (by
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hu; exact hu.1)
  exact continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hupos))

/-- The `(u−k)`-weighted interval integrand is interval-integrable on `[k,k+1]`. -/
lemma sub_cpow_intervalIntegrable {r : ℂ} {k : ℕ} (hk : 1 ≤ k) :
    IntervalIntegrable (fun u : ℝ => ((u : ℂ) - (k : ℂ)) * (u : ℂ) ^ r) volume
      (k : ℝ) ((k : ℝ) + 1) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine (ContinuousOn.intervalIntegrable ?_)
  refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
  have hupos : 0 < u := lt_of_lt_of_le hkR (by
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hu; exact hu.1)
  exact ((continuous_ofReal.continuousAt).sub continuousAt_const).mul
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hupos)))

/-- The `fract`-weighted interval integrand is interval-integrable on `[k,k+1]` (`k ≥ 1`),
via domination of the bounded measurable integrand by the continuous `u ↦ |u^{−σ−1}|`. -/
lemma frac_cpow_intervalIntegrable {s : ℂ} {k : ℕ} (hk : 1 ≤ k) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume
      (k : ℝ) ((k : ℝ) + 1) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioc (k : ℝ) ((k : ℝ) + 1))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact continuousOn_of_forall_continuousAt (fun u hu =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (lt_of_lt_of_le hkR
          (le_of_lt hu.1)))))
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
    exact Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (lt_of_lt_of_le hkR
      (Set.mem_Icc.mp hu).1)))
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact norm_fracIntegrand_le (lt_of_lt_of_le hkR (le_of_lt hu.1))

/-- **The per-unit-interval Euler–Maclaurin identity.**  For `s ≠ 0` and `k ≥ 1`,
`(k+1)^{−s} = ∫_k^{k+1} u^{−s} du − s·∫_k^{k+1} {u}·u^{−s−1} du`, by the FTC with
antiderivative `g(u) = (u−k)·u^{−s}`. -/
lemma zeta_per_interval {s : ℂ} (hs0 : s ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    (∫ u in (k : ℝ)..((k : ℝ) + 1), (u : ℂ) ^ (-s))
      - s * ∫ u in (k : ℝ)..((k : ℝ) + 1), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
      = ((k + 1 : ℕ) : ℂ) ^ (-s) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set g : ℝ → ℂ := fun u => ((u : ℂ) - (k : ℂ)) * (u : ℂ) ^ (-s) with hg
  set g' : ℝ → ℂ := fun u => (u : ℂ) ^ (-s) - s * (((u : ℂ) - (k : ℂ)) * (u : ℂ) ^ (-s - 1))
    with hg'
  -- derivative of the antiderivative on `[k, k+1]`
  have hderiv : ∀ u ∈ Set.uIcc (k : ℝ) ((k : ℝ) + 1), HasDerivAt g (g' u) u := by
    intro u hu
    have hupos : 0 < u := lt_of_lt_of_le hkR (by
      rw [Set.uIcc_of_le (by linarith)] at hu; exact (Set.mem_Icc.mp hu).1)
    have hcoe : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
    have hd1 : HasDerivAt (fun u : ℝ => (u : ℂ) - (k : ℂ)) 1 u := hcoe.sub_const _
    have hd2 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (u : ℂ) ^ (-s - 1)) u :=
      hasDerivAt_ofReal_cpow_const (ne_of_gt hupos) (neg_ne_zero.mpr hs0)
    have hmul := hd1.mul hd2
    have hderiv_eq : g' u
        = 1 * (u : ℂ) ^ (-s) + ((u : ℂ) - (k : ℂ)) * ((-s) * (u : ℂ) ^ (-s - 1)) := by
      simp only [hg']; ring
    rw [hderiv_eq]; exact hmul
  -- interval integrability of `g'`
  have hint : IntervalIntegrable g' volume (k : ℝ) ((k : ℝ) + 1) := by
    simp only [hg']
    exact (cpow_intervalIntegrable hk).sub ((sub_cpow_intervalIntegrable hk).const_mul s)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the boundary value `g(k+1) − g(k) = (k+1)^{−s}`
  have hgval : g ((k : ℝ) + 1) - g (k : ℝ) = ((k + 1 : ℕ) : ℂ) ^ (-s) := by
    simp only [hg]; push_cast; ring
  -- split the `g'` integral and swap `(u−k)` for `{u}` on the open interval
  have hsplit : (∫ u in (k : ℝ)..((k : ℝ) + 1), g' u)
      = (∫ u in (k : ℝ)..((k : ℝ) + 1), (u : ℂ) ^ (-s))
        - s * ∫ u in (k : ℝ)..((k : ℝ) + 1), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    simp only [hg']
    rw [intervalIntegral.integral_sub (cpow_intervalIntegrable hk)
      ((sub_cpow_intervalIntegrable hk).const_mul s), intervalIntegral.integral_const_mul]
    congr 2
    rw [intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_of_le (by linarith),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
    have hfl : ⌊u⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]
      refine ⟨by exact_mod_cast le_of_lt hu.1, by exact_mod_cast hu.2⟩
    have hfr : Int.fract u = u - (k : ℝ) := by rw [← Int.self_sub_floor, hfl]; push_cast; ring
    rw [hfr]; push_cast; ring
  rw [hsplit] at hftc
  rw [hftc]; exact hgval

/-- Interval integrability of `u ↦ (u:ℂ)^r` on `[a,b]` for `0 < a ≤ b`. -/
lemma cpow_ii {r : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ r) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
  exact continuousAt_ofReal_cpow_const _ _
    (Or.inr (ne_of_gt (lt_of_lt_of_le ha (Set.mem_Icc.mp hu).1)))

/-- Interval integrability of the `fract`-weighted integrand on `[a,b]` for `0 < a ≤ b`. -/
lemma frac_ii {s : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ioc a b)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact continuousOn_of_forall_continuousAt (fun u hu =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (lt_of_lt_of_le ha (le_of_lt hu.1)))))
  have hdom : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Set.Ioc a b) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine continuousOn_of_forall_continuousAt (fun u hu => ?_)
    exact Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (lt_of_lt_of_le ha
      (Set.mem_Icc.mp hu).1)))
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact norm_fracIntegrand_le (lt_of_lt_of_le ha (le_of_lt hu.1))

/-- **The finite Euler–Maclaurin identity.**  For `s ≠ 0`, `1 ≤ N ≤ M`,
`∑_{N<n≤M} n^{−s} = ∫_N^M u^{−s} du − s·∫_N^M {u}·u^{−s−1} du` (sum of the per-interval
identities `zeta_per_interval`, by `Nat.le_induction`). -/
lemma finite_EM {s : ℂ} (hs0 : s ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    ∀ M : ℕ, N ≤ M →
      ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-s)
        = (∫ u in (N : ℝ)..(M : ℝ), (u : ℂ) ^ (-s))
          - s * ∫ u in (N : ℝ)..(M : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hM0 : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hN0 hNM
      have hMM1 : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
      have e1 := intervalIntegral.integral_add_adjacent_intervals
        (cpow_ii (r := -s) hN0 hNM) (cpow_ii (r := -s) hM0 hMM1)
      have e2 := intervalIntegral.integral_add_adjacent_intervals
        (frac_ii (s := s) hN0 hNM) (frac_ii (s := s) hM0 hMM1)
      rw [Finset.sum_Ioc_succ_top hM, ih, ← zeta_per_interval hs0 (le_trans hN hM)]
      push_cast
      rw [← e1, ← e2]
      ring

open Filter Topology in
/-- **F5-1 on `Re s > 1` (the everything-converges regime).**  The Hardy–Littlewood identity
`ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1) = −s·∫_N^∞ {u} u^{−s−1} du`, obtained from `finite_EM`
by letting the upper cut `M → ∞` (partial sums → ζ, `∫_N^M u^{−s} → N^{1−s}/(s−1)` via
`integral_Ioi_cpow_of_lt`, `∫_N^M {u}u^{−s−1} → zetaFracInt` via improper convergence). -/
lemma zetaApprox_gt_one {s : ℂ} (hs1 : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)
      = -s * zetaFracInt N s := by
  have hσ : 0 < s.re := by linarith
  have hsne1 : s ≠ 1 := by rintro rfl; rw [Complex.one_re] at hs1; linarith
  have hs0 : s ≠ 0 := by rintro rfl; rw [Complex.zero_re] at hσ; linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- ζ as an ordered sum
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs1
  have hfeq : (fun n : ℕ => (n : ℂ) ^ (-s)) = (fun n : ℕ => 1 / (n : ℂ) ^ s) := by
    funext n; rw [Complex.cpow_neg, ← one_div]
  have hsum_zeta : HasSum (fun n : ℕ => (n : ℂ) ^ (-s)) (riemannZeta s) := by
    rw [hfeq, zeta_eq_tsum_one_div_nat_cpow hs1]; exact hsummable.hasSum
  have hrange_eq : ∀ K : ℕ, ∑ n ∈ Finset.range (K + 1), (n : ℂ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s) := by
    intro K
    have hset : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp), Nat.cast_zero,
      Complex.zero_cpow (neg_ne_zero.mpr hs0), zero_add]
  -- (a) the sum side
  have hpartial : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := hsum_zeta.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hL : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))) := by
    refine (hpartial.sub_const _).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hsplit_sum : ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s)
        = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-s) := by
      rw [← Finset.sum_union]
      · congr 1
        ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
      · rw [Finset.disjoint_left]; intro x hx hx'
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'; omega
    rw [hrange_eq M, hsplit_sum]; ring
  -- (b) the main integral
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hsne1
  have gen : ∀ A : ℂ, -A / (1 - s) = A / (s - 1) := fun A => by field_simp; ring
  have hb_val : ∫ u in Set.Ioi (N : ℝ), (u : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (show (-s).re < -1 by rw [Complex.neg_re]; linarith) hN0,
      show (-s) + 1 = 1 - s from by ring]
    exact gen _
  have hb : Tendsto (fun M : ℕ => ∫ u in (N : ℝ)..(M : ℝ), (u : ℂ) ^ (-s)) atTop
      (𝓝 ((N : ℂ) ^ (1 - s) / (s - 1))) := by
    rw [← hb_val]
    exact intervalIntegral_tendsto_integral_Ioi _
      (integrableOn_Ioi_cpow_of_lt (show (-s).re < -1 by rw [Complex.neg_re]; linarith) hN0)
      tendsto_natCast_atTop_atTop
  -- (c) the fractional-part integral
  have hc : Tendsto (fun M : ℕ =>
      ∫ u in (N : ℝ)..(M : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (zetaFracInt N s)) :=
    intervalIntegral_tendsto_integral_Ioi _ (fracIntegrand_integrableOn hσ hN)
      tendsto_natCast_atTop_atTop
  -- (RHS) combine via finite_EM
  have hR : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ioc N M, (n : ℂ) ^ (-s)) atTop
      (𝓝 ((N : ℂ) ^ (1 - s) / (s - 1) - s * zetaFracInt N s)) := by
    refine (hb.sub (hc.const_mul s)).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    exact (finite_EM hs0 hN M hM).symm
  have huniq := tendsto_nhds_unique hL hR
  linear_combination huniq

open Filter Topology in
/-- **F5-1, the approximate formula (the stone).**  On the convex region `{0 < Re s, 0 < Im s}`
(which contains the whole growth region `t > 0` and avoids the pole `s = 1`), the
Hardy–Littlewood identity `ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1) = −s·∫_N^∞ {u} u^{−s−1} du`
holds, by analytic continuation (the identity theorem, `StripConvergence` pattern) from the
`Re s > 1` identity `zetaApprox_gt_one`.  (The identity extends to the full punctured half-plane
`{0 < Re s} ∖ {1}` by conjugation symmetry + preconnectedness; the convex upper region suffices
for the region conversion.) -/
lemma zetaApprox {s : ℂ} (hσ : 0 < s.re) (him : 0 < s.im) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)
      = -s * zetaFracInt N s := by
  set W : Set ℂ := {z | 0 < z.re ∧ 0 < z.im} with hW
  set P : ℂ → ℂ := fun z => riemannZeta z - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
    - (N : ℂ) ^ (1 - z) / (z - 1) with hP
  set Q : ℂ → ℂ := fun z => -z * zetaFracInt N z with hQ
  have hzne1 : ∀ z ∈ W, z ≠ 1 := by
    rintro z ⟨_, hz2⟩ rfl; simp only [Complex.one_im] at hz2; exact lt_irrefl 0 hz2
  have hopen : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hconv : Convex ℝ W := by
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      calc (0 : ℝ) < min x.re y.re := lt_min hx1 hy1
        _ = (a + b) * min x.re y.re := by rw [hab, one_mul]
        _ = a * min x.re y.re + b * min x.re y.re := by ring
        _ ≤ a * x.re + b * y.re := add_le_add
              (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
              (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      calc (0 : ℝ) < min x.im y.im := lt_min hx2 hy2
        _ = (a + b) * min x.im y.im := by rw [hab, one_mul]
        _ = a * min x.im y.im + b * min x.im y.im := by ring
        _ ≤ a * x.im + b * y.im := add_le_add
              (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
              (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
  have hterm_diff : ∀ z ∈ W, DifferentiableAt ℂ (fun z => (N : ℂ) ^ (1 - z) / (z - 1)) z := by
    intro z hz
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine DifferentiableAt.div ?_ (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hzne1 z hz))
    exact (differentiableAt_const (1 : ℂ) |>.sub differentiableAt_id).const_cpow (Or.inl hNne)
  have hsum_diff : ∀ z : ℂ,
      DifferentiableAt ℂ (fun z => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) z := by
    intro z
    have hrw : (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
        = ∑ n ∈ Finset.Icc 1 N, (fun z : ℂ => (n : ℂ) ^ (-z)) := by
      funext w; rw [Finset.sum_apply]
    rw [hrw]
    apply DifferentiableAt.sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Icc] at hn; exact Nat.cast_ne_zero.mpr (by omega)
    exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
  have hPana : AnalyticOnNhd ℂ P W := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    exact (((differentiableAt_riemannZeta (hzne1 z hz)).sub (hsum_diff z)).sub
      (hterm_diff z hz)).differentiableWithinAt
  have hQana : AnalyticOnNhd ℂ Q W := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    exact ((differentiableAt_id.neg).mul
      (zetaFracInt_differentiableAt N hN hz.1)).differentiableWithinAt
  have hz0 : (2 + Complex.I) ∈ W := by
    refine ⟨?_, ?_⟩ <;> simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 + Complex.I), P z = Q z := by
    have hev : ∀ᶠ z in 𝓝 (2 + Complex.I), P z = Q z := by
      have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hmem : (2 + Complex.I) ∈ {z : ℂ | 1 < z.re} := by
        simp only [Set.mem_setOf_eq, Complex.add_re, Complex.I_re, Complex.re_ofNat]; norm_num
      filter_upwards [hopen1.mem_nhds hmem] with z hz
      exact zetaApprox_gt_one hz hN
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hPana.eqOn_of_preconnected_of_frequently_eq hQana hconv.isPreconnected hz0 hfreq
    ⟨hσ, him⟩

/-- **F5-1, the bound form.**  On `{0 < Re s, 0 < Im s}` and for `N ≥ 1`,
`‖ζ(s) − ∑_{n≤N} n^{−s} − N^{1−s}/(s−1)‖ ≤ ‖s‖·N^{−σ}/σ` — the classical
`O((1+|s|)·X^{−σ})` approximation error. -/
lemma norm_zeta_sub_approx_le {s : ℂ} (hσ : 0 < s.re) (him : 0 < s.im) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  rw [zetaApprox hσ him hN, norm_mul, norm_neg, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (zetaFracInt_bound hσ hN) (norm_nonneg s)

/-! ## Section 3 — F5-2, the σ-weighted growth bound on the strip -/

/-- **F5-2 (the node, checkpoint form).**  There are constants `C, t₀ > 0` such that for every
`σ ∈ [1/2, 1]` and `t ≥ t₀`,
`‖ζ(σ + it)‖ ≤ C·t^{1−σ}·(1 + log t)`.  At `σ = 1` this is `‖ζ(1+it)‖ ≤ C·(1+log t) = O(log t)`
— a genuine power saving at `σ = 1` (the classical de la Vallée-Poussin input).

Route: the approximate formula `norm_zeta_sub_approx_le` at `X = ⌊t⌋` (so `t/2 < N ≤ t`), a
triangle inequality `‖ζ‖ ≤ ‖ζ−Σ−pole‖ + ‖Σ‖ + ‖pole‖`, the trivial partial-sum bound
`sum_Icc_rpow_neg_le` (`‖Σ‖ ≤ N^{1−σ}(1+log N)`), and `‖pole‖ = N^{1−σ}/‖s−1‖ ≤ t^{1−σ}/t`.
With `X = ⌊t⌋` the error term `‖s‖N^{−σ} ≍ t^{1−σ}` is the exponent bottleneck; improving `‖Σ‖`
below `t^{1−σ}` via the phase-sum power saving (`zeta_partial_growth`) does not lower the total
at a fixed truncation, so a sub-`t^{1−σ}` bound in the *open* strip is the residual **LITT-COVER**
(global window coverage from a single `t`). -/
theorem zeta_growth_strip : ∃ C t₀ : ℝ, 0 < t₀ ∧
    ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → t₀ ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ (1 - σ) * (1 + Real.log t) := by
  refine ⟨10, 2, by norm_num, fun σ t hσlo hσhi ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htlog : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hσ0 : 0 < s.re := by rw [hsre]; linarith
  have him : 0 < s.im := by rw [hsim]; linarith
  -- the truncation N = ⌊t⌋, so t/2 < N ≤ t
  set N : ℕ := ⌊t⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast ht1)
  have hNle : (N : ℝ) ≤ t := Nat.floor_le (le_of_lt ht0)
  have htlt : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hthalf : t / 2 < (N : ℝ) := by
    have : t < 2 * (N : ℝ) := by
      have h1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith [hNpos]
      linarith [htlt, h1]
    linarith
  -- rpow abbreviations
  have hTnn : (0 : ℝ) ≤ t ^ (1 - σ) := Real.rpow_nonneg (le_of_lt ht0) _
  have h1σ : (0 : ℝ) ≤ 1 - σ := by linarith
  -- (A) the approximation error ‖ζ − Σ − pole‖ ≤ 8·t^{1−σ}
  have hNsig : (N : ℝ) ^ (-σ) ≤ 2 * t ^ (-σ) := by
    have hstep : (N : ℝ) ^ (-σ) ≤ (t / 2) ^ (-σ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) (le_of_lt hthalf) (by linarith))
    have hval : (t / 2) ^ (-σ) ≤ 2 * t ^ (-σ) := by
      rw [Real.div_rpow (le_of_lt ht0) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt ht0) _)
      calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hσhi
        _ = 2 := Real.rpow_one 2
    linarith [hstep, hval]
  have hsnorm : ‖s‖ ≤ 1 + t := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im s) ?_
    rw [hsre, hsim, abs_of_pos (by linarith : (0:ℝ) < σ), abs_of_pos ht0]
    linarith
  have hA : ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      - (N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 8 * t ^ (1 - σ) := by
    refine le_trans (norm_zeta_sub_approx_le hσ0 him hN1) ?_
    rw [hsre]
    have hσinv : (1 : ℝ) / σ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hstep1 : ‖s‖ * (N : ℝ) ^ (-σ) / σ ≤ (1 + t) * (2 * t ^ (-σ)) * 2 := by
      rw [div_eq_mul_inv]
      refine mul_le_mul (mul_le_mul hsnorm hNsig (Real.rpow_nonneg (le_of_lt hNpos) _)
        (by linarith)) ?_ (by positivity) (by positivity)
      rw [← one_div]; exact hσinv
    refine le_trans hstep1 ?_
    have hta : t ^ (1 - σ) = t ^ (-σ) * t := by
      rw [show (1:ℝ) - σ = -σ + 1 from by ring, Real.rpow_add ht0, Real.rpow_one]
    nlinarith [hta, hTnn, Real.rpow_nonneg (le_of_lt ht0) (-σ), ht1,
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht0) (-σ)) (le_of_lt ht0)]
  -- (B) the head sum ‖Σ‖ ≤ t^{1−σ}(1 + log t)
  have hB : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ t ^ (1 - σ) * (1 + Real.log t) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-σ) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re, hsre]
    rw [Finset.sum_congr rfl hterm]
    refine le_trans (sum_Icc_rpow_neg_le hσhi hN1) ?_
    have hNt : (N : ℝ) ^ (1 - σ) ≤ t ^ (1 - σ) :=
      Real.rpow_le_rpow (le_of_lt hNpos) hNle h1σ
    have hlogNt : (1 : ℝ) + Real.log N ≤ 1 + Real.log t :=
      by linarith [Real.log_le_log hNpos hNle]
    exact mul_le_mul hNt hlogNt (by positivity) hTnn
  -- (C) the pole term ‖N^{1−s}/(s−1)‖ ≤ t^{1−σ}
  have hC : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ t ^ (1 - σ) := by
    rw [norm_div]
    have hpole_norm : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
      rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.sub_re, Complex.one_re, hsre]
    have hden : t ≤ ‖s - 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm (s - 1))
      rw [Complex.sub_im, Complex.one_im, hsim, sub_zero, abs_of_pos ht0]
    rw [hpole_norm]
    have hNt : (N : ℝ) ^ (1 - σ) ≤ t ^ (1 - σ) :=
      Real.rpow_le_rpow (le_of_lt hNpos) hNle h1σ
    rw [div_le_iff₀ (lt_of_lt_of_le ht0 hden)]
    exact le_trans hNt (le_mul_of_one_le_right hTnn (le_trans ht1 hden))
  -- combine via the triangle inequality
  have heq : riemannZeta s
      = (riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1))
        + (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) := by ring
  have htri : ‖riemannZeta s‖ ≤ 8 * t ^ (1 - σ) + t ^ (1 - σ) * (1 + Real.log t) + t ^ (1 - σ) := by
    rw [heq]
    exact le_trans norm_add₃_le (add_le_add (add_le_add hA hB) hC)
  refine le_trans htri ?_
  nlinarith [mul_nonneg hTnn htlog, hTnn, htlog]

end Salt.ExpSum
