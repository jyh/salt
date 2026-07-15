/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Defs
import Salt.SW.ZeroFree
import Salt.SW.ZetaPole
import Salt.SW.LandauPage
import Salt.SW.MaxModulus
import Salt.SW.ZeroCount
import Salt.SW.Growth
import Salt.SW.BCBound
import Salt.SW.Kernel
import Salt.SW.Psi1Identity
import Salt.SW.ContourShift

/-!
# The SW rung, wave S5b — the contour-shift assembly

Design: `docs/blueprints/sw.md`, wave S5. This module assembles the landed residues-lite core
(`Salt/SW/ContourShift.lean`) with the S1b line identity (`Salt/SW/Psi1Identity.lean`), the S2
partial-fraction numeric (`Salt/SW/MaxModulus.lean`), and the S3 zero-free region into the
`ψ₁(x,χ)` contour-shift bound.

## Progress note (SESSION IN PROGRESS — persisted before an outage)

**Landed here (all sorry-free, axiom-clean, build-verified):**
* `norm_logDeriv_le_of_re` — the c-line norm bound `‖L'/L(s,χ)‖ ≤ 1/(Re s − 1) + 1`
  (`1 < Re s ≤ 2`); the termwise triangle inequality on `−L'/L = LSeries(χΛ)` majorized by the
  `ζ`-quantity `−ζ'/ζ(Re s)`. **This is the tail-bound input.**
* `norm_neg_logDeriv_le_shifted` — the shifted-contour `−L'/L` **norm** bound on the left/horizontal
  edges, under the widened zero-free hypothesis `hzf` (no zeros in `[σ₀−w,1] × [−(T+2),T+2]`); the
  S2 partial-fraction numeric `120·log(4M₀)` plus the Jensen zero-count `log(4M₀)/log(7/6)` divided
  by the margin `w`. Includes a **from-scratch re-derivation of the endpoint zero-count** (the
  `LFunction_norm_logDeriv_sub_sum'` endpoint does not expose it) via
  `analyticOrderAt_eq_of_factorization` + `divisor_apply` + the Jensen `LFunction_zero_count_le`.
  **This is the left/horizontal edge input.**
* `rectBI_right_split` — the Goursat rearrangement: `rectBI = 0` re-solved for the right edge
  (right = horizontals + left). **The algebraic heart of the shift.**
* `integral_inv_sq_add` — the Lorentzian `∫_ℝ (c²+v²)⁻¹ = π/c`. **The left-edge kernel mass.**
* `psi1_eq_contour_integral` — the S1b → contour bridge: `ψ₁(x,χ) = (1/2π)·∫_ℝ F(c+it) dt`,
  `F(s) = x^{s+1}/(s(s+1))·(−L'/L)(s,χ)` (extra `x` folded into the exponent; `LSeries` log-deriv
  rewritten to `LFunction` log-deriv on `Re s = c > 1`). **The interface.**
* `tail_lorentzian_le` — `∫_{|v| ≥ T} (c²+v²)⁻¹ ≤ 2/T` (comparison with `v^{-2}` on each half-tail
  via `integral_Ioi_rpow_of_lt` + `integral_comp_neg_Iic` reflection). **The tail kernel mass.**
* `contour_integrand_integrable` — `F(c+·I)` is `ℝ`-integrable (dominated by the Lorentzian
  `(1/(c−1)+1)·x^{c+1}·(c²+v²)⁻¹`, using continuity on the line). **The truncation input.**

**The verified design** (contour `[σ₀,c] × [−T,T]`, `c = 1 + 1/log x`):
* `T' := T` (no `∃-T'` pigeonhole needed);
* the zero-free hypothesis is **widened** to `Im`-range `T+2` and `Re`-range `[σ₀−w, 1]`, so that
  every zero in a boundary disk `ball(2+it₀, 3/2)` (`|t₀| ≤ T`, reaching `|Im| < T+3/2 < T+2`) has
  `Re ρ ≤ σ₀−w`, giving `dist(edge, ρ) ≥ w` uniformly — **all `∃-σ₀'`/`∃-T'` spacing dodges
  dissolve**;
* the constraint `σ₀ ≥ 9/10` (from `σ₀ − w ≥ 9/10`, `w > 0`) keeps the left edge inside the
  partial-fraction `23/20`-region (`2 − σ₀ < 11/10 < 23/20`) and off the kernel poles `s=0,−1`.
  S6 sanity: `w = c₀/(2 log(f(T+2)))` gives `1/w = 2 log(f(T+2))/c₀` — a log-power, and
  `σ₀ = 1 − c₀/log(fT) ≥ 9/10` at scale (`log(fT) ≥ 10 c₀`). ✓

**The assembly `psi1_contour_shift`** (landed below) glues these: `F`-analyticity + `L≠0` on the
rectangle, the truncation split (`integral_add_compl` + `intervalIntegral.integral_of_le`), the
three edge-integral estimates (left via `integral_inv_sq_add`, horizontals via
`intervalIntegral.norm_integral_le_of_norm_le_const`, tail via `tail_lorentzian_le`), and the final
`E`-arithmetic — see the theorem's own docstring for the explicit bound `E`.

The explicit error `E` (shape reported to S6): with
`B := 120·log(4M₀T) + (log(4M₀T)/log(7/6))/w`, `M₀T := 5(4+T)√f(1+log f)`, `c := 1+1/log x`,
`E = (1/2π)·( B·x^{1+σ₀}·(π/σ₀)  +  2(c−σ₀)·B·x^{c+1}/T²  +  (log x + 1)·x^{c+1}·(2/T) )`.
At `T = e^{√log x}`, `σ₀ = 1 − c'/√log x`, `w = c₀/(2 log(f(T+2)))`, `f ≤ (log x)^C`: `B` and `1/w`
are `log`-powers, `x^{1+σ₀} = x²·e^{−c'√log x}`, and `x^{c+1}/T = x²·e·e^{−√log x}` — so
`E ≪ x²·e^{−c''√log x}`, as S6 requires. ✓

All landed results axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no
new axioms, no `sorry`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set Metric MeromorphicOn Function
  MeasureTheory
open scoped LSeries.notation Topology

namespace Salt.SW

/-- The `n`-th term of `L(↗Λ)` at real `σ` is the real `Λ(n)·n^{−σ}`. -/
private lemma term_vonMangoldt_eq' (σ : ℝ) (n : ℕ) :
    LSeries.term ↗vonMangoldt (σ : ℂ) n = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

/-- **The c-line norm bound.** For `1 < Re s ≤ 2`,
`‖L'/L(s,χ)‖ ≤ 1/(Re s − 1) + 1`. The termwise triangle inequality on
`−L'/L = LSeries(χ·Λ)` majorizes by the real `ζ`-quantity `−ζ'/ζ(Re s)`,
bounded by the S3c pole bound. -/
lemma norm_logDeriv_le_of_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    ‖logDeriv (LFunction χ) s‖ ≤ 1 / (s.re - 1) + 1 := by
  set σ : ℝ := s.re with hσ
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact h1
  have hbridge : -logDeriv (LFunction χ) s = LSeries (↗χ * ↗vonMangoldt) s :=
    (neg_logDeriv_LSeries_eq χ h1).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist χ h1)
  rw [← norm_neg, hbridge]
  have hSχ : Summable (fun n => ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ h1)
  have hSΛ : Summable (LSeries.term ↗vonMangoldt (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσC
  have hΛre : ∀ n, ‖LSeries.term ↗vonMangoldt (σ : ℂ) n‖
      = (LSeries.term ↗vonMangoldt (σ : ℂ) n).re := by
    intro n
    rw [term_vonMangoldt_eq' σ n, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))]
  have hSΛnorm : Summable (fun n => ‖LSeries.term ↗vonMangoldt (σ : ℂ) n‖) :=
    summable_norm_iff.mpr hSΛ
  have hterm_le : ∀ n, ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖
      ≤ ‖LSeries.term ↗vonMangoldt (σ : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.ofReal_re, ← hσ]
      have hχn : ‖(↗χ * ↗vonMangoldt) n‖ ≤ ‖(↗vonMangoldt) n‖ := by
        rw [Pi.mul_apply, norm_mul]
        have h := DirichletCharacter.norm_le_one χ (n : ZMod q)
        have hΛnn : (0 : ℝ) ≤ ‖(↗vonMangoldt) n‖ := norm_nonneg _
        nlinarith [hΛnn]
      gcongr
  calc ‖LSeries (↗χ * ↗vonMangoldt) s‖
      ≤ ∑' n, ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖ := norm_tsum_le_tsum_norm hSχ
    _ ≤ ∑' n, ‖LSeries.term ↗vonMangoldt (σ : ℂ) n‖ := hSχ.tsum_le_tsum hterm_le hSΛnorm
    _ = (LSeries ↗vonMangoldt (σ : ℂ)).re := by
        rw [show LSeries ↗vonMangoldt (σ : ℂ) = ∑' n, LSeries.term ↗vonMangoldt (σ : ℂ) n from rfl,
          Complex.re_tsum hSΛ]
        exact tsum_congr hΛre
    _ ≤ 1 / (σ - 1) + 1 := by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσC]
        exact neg_logDeriv_zeta_le h1 h2

/-- **The shifted-contour `−L'/L` norm bound.** Under the widened zero-free hypothesis `hzf`
(no zeros of `L(·,χ)` in the box `[σ₀−w, 1] × [−(T+2), T+2]`), for a point `s` on (or between)
the shifted-contour left edge / horizontal edges (`σ₀ ≤ Re s ≤ 2`, `|Im s| ≤ T`), with
`L s ≠ 0`, the logarithmic derivative is bounded by the S2 partial-fraction numeric plus the
Blaschke-count divided by the margin `w`. -/
lemma norm_neg_logDeriv_le_shifted {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {T σ₀ w : ℝ}
    (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w)
    (hzf : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False)
    {s : ℂ} (hslb : σ₀ ≤ s.re) (hsub : s.re ≤ 2) (hsim : |s.im| ≤ T)
    (hLs : LFunction χ s ≠ 0) :
    ‖logDeriv (LFunction χ) s‖
      ≤ 120 * Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f)))
        + (Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6))
          / w := by
  classical
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set c₀ : ℂ := 2 + (s.im : ℂ) * I with hc₀
  set M₀ : ℝ := 5 * (4 + |s.im|) * Real.sqrt f * (1 + Real.log f) with hM₀
  set M₀T : ℝ := 5 * (4 + T) * Real.sqrt f * (1 + Real.log f) with hM₀T
  have hlogf : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrtf : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrtfnn : (0 : ℝ) ≤ Real.sqrt f := by linarith
  have hM₀1 : 1 ≤ M₀ := by
    have ha : (4 : ℝ) ≤ 4 + |s.im| := by linarith [abs_nonneg s.im]
    have hp1nn : (0 : ℝ) ≤ 5 * (4 + |s.im|) := by linarith
    have p2 : (20 : ℝ) ≤ 5 * (4 + |s.im|) * Real.sqrt f := by
      nlinarith [mul_nonneg hp1nn (by linarith [hsqrtf] : (0 : ℝ) ≤ Real.sqrt f - 1)]
    have hp2nn : (0 : ℝ) ≤ 5 * (4 + |s.im|) * Real.sqrt f := by linarith
    have p3 : (20 : ℝ) ≤ 5 * (4 + |s.im|) * Real.sqrt f * (1 + Real.log f) := by
      nlinarith [mul_nonneg hp2nn (by linarith [hlogf] : (0 : ℝ) ≤ (1 + Real.log f) - 1)]
    rw [hM₀]; linarith [p3]
  have hM₀TgeM₀ : M₀ ≤ M₀T := by
    rw [hM₀, hM₀T]
    have : |s.im| ≤ T := hsim
    gcongr
  have hM₀T1 : 1 ≤ M₀T := le_trans hM₀1 hM₀TgeM₀
  have hlog4M₀pos : 0 < Real.log (4 * M₀) := Real.log_pos (by linarith)
  have hlog4M₀Tpos : 0 < Real.log (4 * M₀T) := Real.log_pos (by linarith)
  have hlog4mono : Real.log (4 * M₀) ≤ Real.log (4 * M₀T) :=
    Real.log_le_log (by linarith) (by linarith)
  obtain ⟨Z, m, h, hZmem, hana_h, hne_h, hEqOn, hident, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' χ hχ hf s.im
  have hsc : ‖s - c₀‖ ≤ 23 / 20 := by
    have hre : (s - c₀).re = s.re - 2 := by rw [hc₀]; simp
    have him : (s - c₀).im = 0 := by rw [hc₀]; simp
    have hnorm : ‖s - c₀‖ = |s.re - 2| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, show (0 : ℝ) ^ 2 = 0 by ring, add_zero,
        Real.sqrt_sq_eq_abs]
    rw [hnorm, abs_of_nonpos (by linarith : s.re - 2 ≤ 0)]
    have : (9 : ℝ) / 10 ≤ σ₀ := by linarith [hw]
    linarith
  have hana_univ : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hana32 : AnalyticOnNhd ℂ (LFunction χ) (ball c₀ (3 / 2)) := hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ (LFunction χ) (closedBall c₀ (3 / 2)) :=
    hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z, (divisor (LFunction χ) (ball c₀ (3 / 2))) ρ = (m ρ : ℤ) := by
    intro ρ hρ
    have hρball := (hZmem ρ hρ).1
    have horder : analyticOrderAt (LFunction χ) ρ = (m ρ : ℕ∞) :=
      analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρ hρball
    rw [hana32.divisor_apply hρball, horder]; simp
  have hsupp : (Function.support (fun u => divisor (LFunction χ) (ball c₀ (3 / 2)) u)) ⊆ ↑Z := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρball : ρ ∈ ball c₀ (3 / 2) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hρ0 : LFunction χ ρ = 0 := by
      by_contra hne0
      apply hρ
      rw [hana32.divisor_apply hρball, (hana32 ρ hρball).analyticOrderAt_eq_zero.mpr hne0]; simp
    exact (mem_zeros_of_factorization hne_h hEqOn hρball hρ0).1
  have hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z, (m ρ : ℤ)) = ∑ ρ ∈ Z, divisor (LFunction χ) (ball c₀ (3 / 2)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ; rw [hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z, divisor (LFunction χ) (ball c₀ (3 / 2)) ρ)
        = ∑ᶠ u, divisor (LFunction χ) (ball c₀ (3 / 2)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp).symm
    have hdle : ∀ u : ℂ, divisor (LFunction χ) (ball c₀ (3 / 2)) u
        ≤ divisor (LFunction χ) (closedBall c₀ (3 / 2)) u := by
      intro u
      by_cases hu : u ∈ ball c₀ (3 / 2)
      · exact le_of_eq
          (by rw [hana32.divisor_apply hu, hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball :
        (Function.support (fun u => divisor (LFunction χ) (ball c₀ (3 / 2)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb :
        (Function.support (fun u => divisor (LFunction χ) (closedBall c₀ (3 / 2)) u)).Finite :=
      (divisor (LFunction χ) (closedBall c₀ (3 / 2))).finiteSupport (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor (LFunction χ) (ball c₀ (3 / 2)) u
        ≤ ∑ᶠ u, divisor (LFunction χ) (closedBall c₀ (3 / 2)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hsphere := LFunction_growth_sphere χ hχ hf s.im
    have hcountJ := LFunction_zero_count_le χ hχ1 s.im (r := 3 / 2) (R := 7 / 4) (M := M₀)
      (by norm_num) (by norm_num) hM₀1 hsphere
    calc (∑ ρ ∈ Z, (m ρ : ℝ))
        = ((∑ ρ ∈ Z, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor (LFunction χ) (ball c₀ (3 / 2)) u : ℤ) : ℝ) := by rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor (LFunction χ) (closedBall c₀ (3 / 2)) u : ℤ) : ℝ) := by
          exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 / (3 / 2)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 / (3 / 2) = 7 / 6 by norm_num]
  have hdist : ∀ ρ ∈ Z, w ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have hρball := (hZmem ρ hρ).1
    have hρ0 := (hZmem ρ hρ).2
    have hρre1 : ρ.re < 1 := by
      by_contra hc; exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hc) hρ0
    have hρim : |ρ.im| ≤ T + 2 := by
      have himdist : |ρ.im - s.im| ≤ 3 / 2 := by
        have h := Complex.abs_im_le_norm (ρ - c₀)
        have hival : (ρ - c₀).im = ρ.im - s.im := by
          rw [hc₀]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        rw [hival] at h
        have hb : ‖ρ - c₀‖ < 3 / 2 := by rw [← dist_eq_norm]; exact hρball
        linarith
      have hh1 := abs_le.mp himdist
      have hh2 := abs_le.mp hsim
      rw [abs_le]; constructor <;> linarith
    have hρre2 : ρ.re ≤ σ₀ - w := by
      by_contra hc
      exact hzf ρ hρ0 (le_of_lt (not_le.mp hc)) hρre1.le hρim
    have hre := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at hre
    have hgap : w ≤ s.re - ρ.re := by linarith
    calc w ≤ s.re - ρ.re := hgap
      _ = |s.re - ρ.re| := (abs_of_nonneg (by linarith)).symm
      _ ≤ ‖s - ρ‖ := hre
  have hnumbound := hnum s hsc hLs
  have hSumNorm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / w := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist ρ hρ
          have hdpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hw hd
          rw [div_le_div_iff₀ hdpos hw]
          nlinarith [Nat.cast_nonneg (α := ℝ) (m ρ), hd]
      _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by rw [Finset.sum_div]
  have hsplit : ‖logDeriv (LFunction χ) s‖
      ≤ ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
    calc ‖logDeriv (LFunction χ) s‖
        = ‖(logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hcount' : (∑ ρ ∈ Z, (m ρ : ℝ)) / w ≤ (Real.log (4 * M₀T) / Real.log (7 / 6)) / w := by
    rw [div_le_div_iff_of_pos_right hw]
    apply le_trans hcount
    rw [div_le_div_iff_of_pos_right h76]
    exact hlog4mono
  have hnum' : ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
      ≤ 120 * Real.log (4 * M₀T) := by
    calc ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ 120 * Real.log (4 * M₀) := hnumbound
      _ ≤ 120 * Real.log (4 * M₀T) := by linarith [hlog4mono]
  calc ‖logDeriv (LFunction χ) s‖
      ≤ 120 * Real.log (4 * M₀T) + (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
        linarith [hsplit, hnum', hSumNorm]
    _ ≤ 120 * Real.log (4 * M₀T) + (Real.log (4 * M₀T) / Real.log (7 / 6)) / w := by
        linarith [hcount']

/-- **The Goursat rearrangement** (the contour-shift plumbing). For `F` analytic on the closed
rectangle with corners `z` (lower-left) and `w` (upper-right), the right-edge vertical integral
equals the two horizontal edges plus the left-edge vertical integral. This is
`rectBI z w F = 0` re-solved for the right edge — the algebraic heart of the contour shift. -/
lemma rectBI_right_split {z w : ℂ} {F : ℂ → ℂ}
    (H : DifferentiableOn ℂ F (closedRect z w)) :
    I * (∫ v in z.im..w.im, F (w.re + v * I))
      = (∫ u in z.re..w.re, F (u + w.im * I)) - (∫ u in z.re..w.re, F (u + z.im * I))
        + I * (∫ v in z.im..w.im, F (z.re + v * I)) := by
  have h0 := rectBI_eq_zero_of_differentiableOn H
  rw [rectBI] at h0
  linear_combination h0

/-- The full-line Lorentzian integral `∫_ℝ (c² + v²)⁻¹ dv = π/c` for `c > 0`. -/
lemma integral_inv_sq_add {c : ℝ} (hc : 0 < c) :
    ∫ v : ℝ, (c ^ 2 + v ^ 2)⁻¹ = Real.pi / c := by
  have hcne : c ≠ 0 := hc.ne'
  have hpt : (fun v : ℝ => (c ^ 2 + v ^ 2)⁻¹) = fun v : ℝ => (c ^ 2)⁻¹ * (1 + (v / c) ^ 2)⁻¹ := by
    funext v
    rw [div_pow, ← mul_inv]
    congr 1
    field_simp
  have hcomp : (∫ v : ℝ, (1 + (v / c) ^ 2)⁻¹) = |c| • ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
    MeasureTheory.Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) c
  rw [hpt, MeasureTheory.integral_const_mul, hcomp, integral_univ_inv_one_add_sq,
    smul_eq_mul, abs_of_pos hc]
  field_simp

/-- **The S1b → contour bridge.** The S1b line identity, repackaged with the extra `x` folded
into the kernel exponent (`x·x^{c+it} = x^{(c+it)+1}`) and the `LSeries` log-derivative rewritten
as the `LFunction` log-derivative (they agree on `Re s = c > 1`): `ψ₁(x,χ) = (1/2π)·∫_ℝ F(c+it) dt`
where `F(s) = x^{s+1}/(s(s+1))·(−L'/L)(s,χ)` is the contour integrand. -/
lemma psi1_eq_contour_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) {c : ℝ} (hc : 1 < c) :
    psi1Chi x χ = (1 / (2 * Real.pi)) • ∫ v : ℝ,
      (x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
        * (-logDeriv (LFunction χ) ((c : ℂ) + v * I)) := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (0 : ℝ) < x).ne'
  rw [psi1_eq_integral_logDeriv χ hx hc]
  simp only [Complex.real_smul]
  rw [show (x : ℂ) * (↑(1 / (2 * Real.pi)) * ∫ t : ℝ,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))
          * (-deriv (LSeries ↗χ) ((c : ℂ) + (t : ℂ) * I) / LSeries ↗χ ((c : ℂ) + (t : ℂ) * I)))
      = ↑(1 / (2 * Real.pi)) * ((x : ℂ) * ∫ t : ℝ,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))
          * (-deriv (LSeries ↗χ) ((c : ℂ) + (t : ℂ) * I) / LSeries ↗χ ((c : ℂ) + (t : ℂ) * I))) by
      ring]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  have hre : (1 : ℝ) < ((c : ℂ) + (v : ℂ) * I).re := by simp; linarith
  rw [neg_logDeriv_LSeries_eq χ hre]
  rw [Complex.cpow_add ((c : ℂ) + (v : ℂ) * I) 1 hxC, Complex.cpow_one]
  ring

/-- The Lorentzian tail integral bound: for `c, T > 0`,
`∫_{|v| ≥ T} (c² + v²)⁻¹ dv ≤ 2/T` (comparison with `v^{-2}` on each half-tail). -/
lemma tail_lorentzian_le {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ ≤ 2 / T := by
  have hcompl : (Set.Ioc (-T) T)ᶜ = Set.Iic (-T) ∪ Set.Ioi T := by
    ext v; simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    constructor
    · intro h; rw [not_and_or, not_lt, not_le] at h; exact h
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  have hdisj : Disjoint (Set.Iic (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]; intro v hv hv'; simp only [Set.mem_Iic] at hv
    simp only [Set.mem_Ioi] at hv'; linarith
  have hInt : IntegrableOn (fun v : ℝ => (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
    (integrable_inv_c_sq_add_sq hc).integrableOn
  have hInt_Ioi : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hsubR : Set.Ioi T ⊆ (Set.Ioc (-T) T)ᶜ := by rw [hcompl]; exact Set.subset_union_right
  have hsubL : Set.Iic (-T) ⊆ (Set.Ioc (-T) T)ᶜ := by rw [hcompl]; exact Set.subset_union_left
  have hle_Ioi : ∫ v in Set.Ioi T, (c ^ 2 + v ^ 2)⁻¹ ≤ 1 / T := by
    calc ∫ v in Set.Ioi T, (c ^ 2 + v ^ 2)⁻¹
        ≤ ∫ v in Set.Ioi T, v ^ (-2 : ℝ) := by
          refine setIntegral_mono_on (hInt.mono_set hsubR) hInt_Ioi measurableSet_Ioi ?_
          intro v hv
          simp only [Set.mem_Ioi] at hv
          have hvpos : 0 < v := by linarith
          rw [Real.rpow_neg hvpos.le, Real.rpow_two, inv_le_inv₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg c]
      _ = 1 / T := by
          rw [integral_Ioi_rpow_of_lt (by norm_num) hT, show (-2 : ℝ) + 1 = -1 by norm_num,
            Real.rpow_neg_one]
          field_simp
  have hle_Iic : ∫ v in Set.Iic (-T), (c ^ 2 + v ^ 2)⁻¹ ≤ 1 / T := by
    have href : ∫ v in Set.Iic (-T), (c ^ 2 + v ^ 2)⁻¹
        = ∫ v in Set.Ioi T, (c ^ 2 + v ^ 2)⁻¹ := by
      have h1 : ∫ v in Set.Iic (-T), (c ^ 2 + v ^ 2)⁻¹
          = ∫ v in Set.Iic (-T), (fun u => (c ^ 2 + u ^ 2)⁻¹) (-v) := by
        refine setIntegral_congr_fun measurableSet_Iic (fun v _ => ?_)
        change (c ^ 2 + v ^ 2)⁻¹ = (c ^ 2 + (-v) ^ 2)⁻¹; rw [neg_sq]
      rw [h1, integral_comp_neg_Iic (-T) (fun u => (c ^ 2 + u ^ 2)⁻¹)]
      simp only [neg_neg]
    rw [href]; exact hle_Ioi
  calc ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹
      = ∫ v in Set.Iic (-T) ∪ Set.Ioi T, (c ^ 2 + v ^ 2)⁻¹ := by rw [hcompl]
    _ = (∫ v in Set.Iic (-T), (c ^ 2 + v ^ 2)⁻¹) + ∫ v in Set.Ioi T, (c ^ 2 + v ^ 2)⁻¹ := by
        rw [setIntegral_union hdisj measurableSet_Ioi (hInt.mono_set hsubL) (hInt.mono_set hsubR)]
    _ ≤ 1 / T + 1 / T := add_le_add hle_Iic hle_Ioi
    _ = 2 / T := by ring

/-- The contour integrand `F(c+v·I)` is integrable on the `c`-line (`1 < c ≤ 2`): dominated by
`(1/(c−1)+1)·x^{c+1}·(c²+v²)⁻¹` (kernel `1/|s|²`-decay × the c-line norm bound). -/
lemma contour_integrand_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) :
    Integrable (fun v : ℝ =>
      (x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
        * (-logDeriv (LFunction χ) ((c : ℂ) + v * I))) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hcpos : (0 : ℝ) < c := by linarith
  have hLcont : Continuous (LFunction χ) := (differentiable_LFunction hχ1).continuous
  have hdL_ana : AnalyticOnNhd ℂ (deriv (LFunction χ)) univ :=
    ((differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ).deriv
  have hdLcont : Continuous (deriv (LFunction χ)) := continuousOn_univ.mp hdL_ana.continuousOn
  have hline : Continuous (fun v : ℝ => (c : ℂ) + v * I) := by fun_prop
  have hLne : ∀ v : ℝ, LFunction χ ((c : ℂ) + v * I) ≠ 0 := fun v =>
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; linarith)
  have hdenne : ∀ v : ℝ, ((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1) ≠ 0 := fun v =>
    mul_ne_zero (s_ne_zero hcpos v) (s1_ne_zero hcpos v)
  have hFcont : Continuous (fun v : ℝ =>
      (x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
        * (-logDeriv (LFunction χ) ((c : ℂ) + v * I))) := by
    apply Continuous.mul
    · apply Continuous.div
      · exact (by fun_prop : Continuous fun v : ℝ => ((c : ℂ) + v * I) + 1).const_cpow (Or.inl hxC)
      · fun_prop
      · exact hdenne
    · have hrw : (fun v : ℝ => -logDeriv (LFunction χ) ((c : ℂ) + v * I))
          = fun v : ℝ =>
            -(deriv (LFunction χ) ((c : ℂ) + v * I) / LFunction χ ((c : ℂ) + v * I)) := by
        funext v; rw [logDeriv_apply]
      rw [hrw]
      exact ((hdLcont.comp hline).div (hLcont.comp hline) hLne).neg
  refine (Integrable.mono'
    ((integrable_inv_c_sq_add_sq hcpos).const_mul (x ^ (c + 1) * (1 / (c - 1) + 1)))
    hFcont.aestronglyMeasurable ?_)
  filter_upwards with v
  have h1 : ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1)‖ = x ^ (c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]; congr 1; simp
  have h2 : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
    norm_inv_denom_le hcpos v
  have hre_v : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
  have h3 : ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖ ≤ 1 / (c - 1) + 1 := by
    have hh := norm_logDeriv_le_of_re χ (s := (c : ℂ) + v * I)
      (by rw [hre_v]; linarith) (by rw [hre_v]; linarith)
    rwa [hre_v] at hh
  have h3nn : (0 : ℝ) ≤ 1 / (c - 1) + 1 := by positivity
  have hxc1nn : (0 : ℝ) ≤ x ^ (c + 1) := by positivity
  calc ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
          * (-logDeriv (LFunction χ) ((c : ℂ) + v * I))‖
      = ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1)‖ * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
          * ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖ := by
        rw [norm_mul, norm_neg, norm_div, norm_inv, div_eq_mul_inv]
    _ ≤ x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ * (1 / (c - 1) + 1) := by rw [h1]; gcongr
    _ = x ^ (c + 1) * (1 / (c - 1) + 1) * (c ^ 2 + v ^ 2)⁻¹ := by ring

set_option maxHeartbeats 1600000 in
-- The assembly threads the Perron identity, the Goursat split, four edge/tail integral estimates
-- and the `E`-arithmetic through one `set`-heavy proof term; the elaborator needs headroom past
-- the 200000 default to check it in a single pass.
/-- **S5b — the contour-shift bound (clean, no-exceptional variant).** -/
theorem psi1_contour_shift {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {x : ℝ} (hx : 3 ≤ x) {T σ₀ w : ℝ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hzf : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False) :
    ‖psi1Chi x χ‖ ≤ (1 / (2 * Real.pi)) *
      (2 * ((1 + 1 / Real.log x) - σ₀)
          * (120 * Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f)))
             + Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6) / w)
          * x ^ ((1 + 1 / Real.log x) + 1) / T ^ 2
        + (120 * Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f)))
             + Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) / Real.log (7 / 6) / w)
          * x ^ (σ₀ + 1) * (Real.pi / σ₀)
        + (Real.log x + 1) * x ^ ((1 + 1 / Real.log x) + 1) * (2 / T)) := by
  classical
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hlogx1 : (1 : ℝ) < Real.log x := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1)
          (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hc1 : 1 < c := by
    have h : (0 : ℝ) < 1 / Real.log x := by positivity
    rw [hcdef]; linarith
  have hc2 : c < 2 := by
    have h : 1 / Real.log x < 1 := by rw [div_lt_one hlogxpos]; linarith
    rw [hcdef]; linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hc_sub : c - 1 = 1 / Real.log x := by rw [hcdef]; ring
  have hσ₀gt : (9 : ℝ) / 10 < σ₀ := by linarith
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  have hσ₀c : σ₀ < c := by linarith
  -- the edge bound constant `B`
  set L4 : ℝ := Real.log (4 * (5 * (4 + T) * Real.sqrt f * (1 + Real.log f))) with hL4
  set B : ℝ := 120 * L4 + L4 / Real.log (7 / 6) / w with hBdef
  have hlogf : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrtf1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ f))
  have hM₀T1 : (1 : ℝ) ≤ 5 * (4 + T) * Real.sqrt f * (1 + Real.log f) := by
    have hp1 : (30 : ℝ) ≤ 5 * (4 + T) := by linarith
    have hp2 : (30 : ℝ) ≤ 5 * (4 + T) * Real.sqrt f := by
      calc (30 : ℝ) = 30 * 1 := by ring
        _ ≤ 5 * (4 + T) * Real.sqrt f := mul_le_mul hp1 hsqrtf1 (by norm_num) (by linarith)
    calc (1 : ℝ) ≤ 30 * 1 := by norm_num
      _ ≤ 5 * (4 + T) * Real.sqrt f * (1 + Real.log f) :=
          mul_le_mul hp2 (by linarith) (by norm_num) (by linarith)
  have hL4nn : (0 : ℝ) ≤ L4 := by rw [hL4]; exact Real.log_nonneg (by nlinarith [hM₀T1])
  have h76 : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  -- `L ≠ 0` on the contour box
  have hLne_box : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → LFunction χ s ≠ 0 := by
    intro s hsl hsu hsi
    by_cases h1 : 1 ≤ s.re
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1
    · intro hs0; exact hzf s hs0 (by linarith) (not_le.mp h1).le (by linarith)
  -- the contour integrand and its norm
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s) with hF
  have hFnorm : ∀ s : ℂ, ‖F s‖
      = x ^ (s.re + 1) * ‖(s * (s + 1))⁻¹‖ * ‖logDeriv (LFunction χ) s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re,
      Complex.one_re, div_eq_mul_inv, ← norm_inv]
  -- differentiability of `deriv L` and of `-logDeriv L` where `L ≠ 0`
  have hana_univ : AnalyticOnNhd ℂ (LFunction χ) univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hdL_diff : Differentiable ℂ (deriv (LFunction χ)) :=
    differentiableOn_univ.mp hana_univ.deriv.differentiableOn
  have hlogD_diff : ∀ s : ℂ, LFunction χ s ≠ 0 →
      DifferentiableAt ℂ (fun z => -logDeriv (LFunction χ) z) s := by
    intro s hs
    have hrw : (fun z => -logDeriv (LFunction χ) z)
        = fun z => -(deriv (LFunction χ) z / LFunction χ z) := by
      funext z; rw [logDeriv_apply]
    rw [hrw]
    exact (((hdL_diff s).div ((differentiable_LFunction hχ1) s) hs)).neg
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  have hFana : DifferentiableOn ℂ F (closedRect zc wc) := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm] at hs
    rw [Set.uIcc_of_le hσ₀c.le] at hs
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsim' : |s.im| ≤ T := by rw [abs_le]; exact ⟨hsim.1, hsim.2⟩
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith [hsre.1]
    have hs1 : s + 1 ≠ 0 := fun h => by
      have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1]
    have hLs : LFunction χ s ≠ 0 := hLne_box s hsre.1 hsre.2 hsim'
    have hker : DifferentiableAt ℂ (fun z => (x : ℂ) ^ (z + 1) / (z * (z + 1))) s := by
      apply DifferentiableAt.div
      · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
      · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
      · exact mul_ne_zero hs0 hs1
    have hFs : DifferentiableAt ℂ F s := by
      rw [hF]; exact hker.mul (hlogD_diff s hLs)
    exact hFs.differentiableWithinAt
  -- Goursat rearrangement
  have hgour := rectBI_right_split hFana
  rw [hzc_re, hzc_im, hwc_re, hwc_im] at hgour
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  -- ‖RIGHT‖ ≤ ‖TOP‖ + ‖BOT‖ + ‖LEFT‖
  have hRnorm : ‖RIGHT‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- integrability and bridge
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + v * I)) := by
    simp only [hF]; exact contour_integrand_integrable χ hχ1 hx1 hc1 hc2.le
  have hbridge : psi1Chi x χ = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + v * I) := by
    rw [psi1_eq_contour_integral χ hx1 hc1]
  -- truncation split
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + v * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  -- edge bound constant
  set Cbnd : ℝ := x ^ (c + 1) * B / T ^ 2 with hCbnd
  have hTpos : (0 : ℝ) < T := by linarith
  have hxc1pos : (0 : ℝ) < x ^ (c + 1) := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  -- pointwise F-norm bound on a horizontal edge (Im = ±T)
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c, ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀gt]
    have hLs : LFunction χ ((u : ℂ) + (τ : ℂ) * I) ≠ 0 :=
      hLne_box _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2]) (by rw [hsim, hτ])
    have hlogb : ‖logDeriv (LFunction χ) ((u : ℂ) + (τ : ℂ) * I)‖ ≤ B := by
      rw [hBdef, hL4]
      exact norm_neg_logDeriv_le_shifted χ hχ hf hw hσ₀w hzf (s := (u : ℂ) + (τ : ℂ) * I)
        (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2]) (by rw [hsim, hτ]) hLs
    have hden : ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖ ≤ (u ^ 2 + τ ^ 2)⁻¹ :=
      norm_inv_denom_le hupos τ
    have hττ : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    have hxexp : x ^ (u + 1) ≤ x ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hu.2])
    have hinvle : (u ^ 2 + τ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg u])
    rw [hFnorm, hsre]
    calc x ^ (u + 1) * ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
            * ‖logDeriv (LFunction χ) ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ x ^ (u + 1) * (u ^ 2 + τ ^ 2)⁻¹ * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
            (norm_nonneg _) (by positivity)
      _ ≤ x ^ (c + 1) * (T ^ 2)⁻¹ * B :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hxexp hinvle (by positivity) (by positivity)) hBnn
      _ = Cbnd := by rw [hCbnd]; ring
  -- horizontal integral bounds
  have hTOPb : ‖TOPI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hTOPI]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz T (abs_of_pos hTpos))
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hBOTb : ‖BOTI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hBOTI]
    have hnegT : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hTpos]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz (-T) hnegT)
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  -- left edge bound.  The edge log-derivative bound only holds for |Im| ≤ T, so the
  -- pointwise estimate is proved only on `[-T, T]` (where the interval integral lives) and
  -- the *dominating* Lorentzian — nonnegative and integrable on all of ℝ — is used to pass
  -- from the interval integral to the full-line integral `π/σ₀`.
  have hLEFTb : ‖LEFT‖ ≤ B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hre : ∀ v : ℝ, ((σ₀ : ℂ) + v * I).re = σ₀ := fun v => by simp
    have him : ∀ v : ℝ, ((σ₀ : ℂ) + v * I).im = v := fun v => by simp
    -- interval-integrability of `F` on the left edge is by continuity (no Re > 1 needed)
    have hmapsto : Set.MapsTo (fun v : ℝ => (σ₀ : ℂ) + v * I) (Set.uIcc (-T) T)
        (closedRect zc wc) := by
      intro v hv
      rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T), Set.mem_Icc] at hv
      rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm,
        Set.uIcc_of_le hσ₀c.le, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc, hre v]; exact ⟨le_refl σ₀, hσ₀c.le⟩
      · rw [Set.mem_Icc, him v]; exact hv
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + v * I)) volume (-T) T :=
      (hFana.continuousOn.comp
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
        hmapsto).intervalIntegrable
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hBnn (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + v * I)‖ ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
      have hLs : LFunction χ ((σ₀ : ℂ) + v * I) ≠ 0 :=
        hLne_box _ hsre.ge (by rw [hsre]; linarith) (by rw [hsim]; exact hvT)
      have hlogb : ‖logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I)‖ ≤ B := by
        rw [hBdef, hL4]
        exact norm_neg_logDeriv_le_shifted χ hχ hf hw hσ₀w hzf (s := (σ₀ : ℂ) + v * I)
          hsre.ge (by rw [hsre]; linarith) (by rw [hsim]; exact hvT) hLs
      have hden : ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖ ≤ (σ₀ ^ 2 + v ^ 2)⁻¹ :=
        norm_inv_denom_le hσ₀pos v
      rw [hFnorm, hsre]
      calc x ^ (σ₀ + 1) * ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖
              * ‖logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I)‖
          ≤ x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ * B :=
            mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
              (norm_nonneg _) (by positivity)
        _ = B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    calc ‖∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I)‖
        ≤ ∫ v in (-T)..T, ‖F ((σ₀ : ℂ) + v * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-T)..T, B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith)
            hFleft_ii.norm hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [integral_const_mul, integral_inv_sq_add hσ₀pos]
  -- tail bound on the vertical `Re = c` line (the truncation remainder)
  have hcompl_meas : MeasurableSet (Set.Ioc (-T) T)ᶜ := measurableSet_Ioc.compl
  have hTAILb : ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
    have hFint_on : IntegrableOn (fun v : ℝ => F ((c : ℂ) + v * I)) (Set.Ioc (-T) T)ᶜ :=
      hFint.integrableOn
    have hg_int : IntegrableOn
        (fun v : ℝ => (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
      ((integrable_inv_c_sq_add_sq hcpos).const_mul _).integrableOn
    calc ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
        ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, ‖F ((c : ℂ) + v * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by
          refine setIntegral_mono_on hFint_on.norm hg_int hcompl_meas ?_
          intro v _
          have hsre : ((c : ℂ) + v * I).re = c := by simp
          have hLs : LFunction χ ((c : ℂ) + v * I) ≠ 0 :=
            LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hsre]; linarith)
          have hlogb : ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖ ≤ Real.log x + 1 := by
            have hle := norm_logDeriv_le_of_re χ (s := (c : ℂ) + v * I)
              (by rw [hsre]; exact hc1) (by rw [hsre]; linarith)
            rw [hsre, hc_sub, one_div_one_div] at hle
            exact hle
          have hden : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
            norm_inv_denom_le hcpos v
          rw [hFnorm, hsre]
          calc x ^ (c + 1) * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
                  * ‖logDeriv (LFunction χ) ((c : ℂ) + v * I)‖
              ≤ x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ * (Real.log x + 1) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
                  (norm_nonneg _) (by positivity)
            _ = (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by ring
      _ = (Real.log x + 1) * x ^ (c + 1) * ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ := by
          rw [integral_const_mul]
      _ ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) :=
          mul_le_mul_of_nonneg_left (tail_lorentzian_le hcpos hTpos)
            (by positivity)
  -- assemble: ‖TOP‖+‖BOT‖+‖LEFT‖ into the two edge terms of `E`
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  -- final combine through the `ψ₁ = (1/2π)·∫` bridge
  rw [hbridge, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [htrunc]
  calc ‖RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ ‖RIGHT‖ + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀))
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
        have h1 : ‖RIGHT‖
            ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀)
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by ring


end Salt.SW
