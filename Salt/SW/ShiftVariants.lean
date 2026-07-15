/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ShiftAssembly

/-!
# The SW rung, wave S5c — the exceptional and χ₀ contour-shift variants

Design: `docs/blueprints/sw.md`, wave S5. This module extends the clean contour-shift bound
`Salt.SW.psi1_contour_shift` (S5b) to the two variants that pick up a residue:

* `psi1_contour_shift_exceptional` — the box is allowed to contain **one simple real zero** `β₁`
  of `L(·,χ)`, carved out by a widened hypothesis. The contour shift then picks up the residue
  `x^{β₁+1}/(β₁(β₁+1))` at `β₁` (via `kernel_residue`), so the bound reads
  `‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ E`, with `E` **identical** to S5b's clean bound.

The mechanism (resolving the S5b executor's obstructions (1)+(2)): work with the de-singularized
integrand `A(s) := ker(s)·G(s)`, `G(s) := (−L'/L)(s) + 1/(s−β₁)`. From the simplicity hypothesis
`analyticOrderAt L β₁ = 1`, `L = (·−β₁)·h` locally with `h(β₁) ≠ 0`, so `G = −h'/h` is analytic
through `β₁`; hence `A` is differentiable on the whole box and Goursat gives `rectBI A = 0`. Since
`F = A − ker/(·−β₁)` off `β₁`, linearity plus `kernel_residue` give `rectBI F = −2πi·ker(β₁)`, i.e.
the clean Goursat split with the extra residue term. The edge bound `‖−L'/L‖ ≤ B` still holds on the
box edges because the exceptional zero's partial-fraction term `1/(s−β₁)` is `≤ 1/w` there (the
separation hypothesis `hβsep`), no larger than the other kept terms.

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no new
axioms, no `sorry`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set Metric MeromorphicOn Function
  MeasureTheory
open scoped LSeries.notation Topology

namespace Salt.SW

/-- **The shifted-contour `−L'/L` norm bound, distance form.** A variant of
`norm_neg_logDeriv_le_shifted` where the zero-free hypothesis is replaced by the direct distance
bound `hdist`: every zero `ρ` of `L(·,χ)` in the Borel–Carathéodory ball `ball (2+iγ) (3/2)`
(`γ = Im s`) satisfies `w ≤ ‖s − ρ‖`. The conclusion — the S2 partial-fraction numeric plus the
Blaschke-count divided by `w` — is identical to the clean lemma. This form lets the exceptional
variant supply its own distance argument (carving `β₁` via the separation hypothesis). -/
lemma norm_logDeriv_le_of_ball_dist {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {T σ₀ w : ℝ}
    (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w)
    {s : ℂ} (hslb : σ₀ ≤ s.re) (hsub : s.re ≤ 2) (hsim : |s.im| ≤ T)
    (hLs : LFunction χ s ≠ 0)
    (hdist : ∀ ρ : ℂ, LFunction χ ρ = 0 →
      ρ ∈ Metric.ball (2 + (s.im : ℂ) * I) (3 / 2) → w ≤ ‖s - ρ‖) :
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
  have hdist' : ∀ ρ ∈ Z, w ≤ ‖s - ρ‖ :=
    fun ρ hρ => hdist ρ (hZmem ρ hρ).2 (hZmem ρ hρ).1
  have hnumbound := hnum s hsc hLs
  have hSumNorm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / w := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist' ρ hρ
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

/-- **Edge-wise linearity of `rectBI`.** If `F = A − B` pointwise on the four edges of the
rectangle (with `A`, `B` interval-integrable on each edge), then
`rectBI z w F = rectBI z w A − rectBI z w B`. The residue-carrying variant splits the shifted
integrand `F = ker·(−L'/L)` into the analytic `A = ker·G` and the residue kernel
`B = ker/(·−β₁)` this way. -/
lemma rectBI_sub_of_edge_eq {z w : ℂ} {F A B : ℂ → ℂ}
    (hA_bot : IntervalIntegrable (fun x : ℝ => A (↑x + ↑z.im * I)) volume z.re w.re)
    (hA_top : IntervalIntegrable (fun x : ℝ => A (↑x + ↑w.im * I)) volume z.re w.re)
    (hA_rgt : IntervalIntegrable (fun y : ℝ => A (↑w.re + ↑y * I)) volume z.im w.im)
    (hA_lft : IntervalIntegrable (fun y : ℝ => A (↑z.re + ↑y * I)) volume z.im w.im)
    (hB_bot : IntervalIntegrable (fun x : ℝ => B (↑x + ↑z.im * I)) volume z.re w.re)
    (hB_top : IntervalIntegrable (fun x : ℝ => B (↑x + ↑w.im * I)) volume z.re w.re)
    (hB_rgt : IntervalIntegrable (fun y : ℝ => B (↑w.re + ↑y * I)) volume z.im w.im)
    (hB_lft : IntervalIntegrable (fun y : ℝ => B (↑z.re + ↑y * I)) volume z.im w.im)
    (hbot : Set.EqOn (fun x : ℝ => F (↑x + ↑z.im * I))
      (fun x : ℝ => A (↑x + ↑z.im * I) - B (↑x + ↑z.im * I)) (Set.uIcc z.re w.re))
    (htop : Set.EqOn (fun x : ℝ => F (↑x + ↑w.im * I))
      (fun x : ℝ => A (↑x + ↑w.im * I) - B (↑x + ↑w.im * I)) (Set.uIcc z.re w.re))
    (hrgt : Set.EqOn (fun y : ℝ => F (↑w.re + ↑y * I))
      (fun y : ℝ => A (↑w.re + ↑y * I) - B (↑w.re + ↑y * I)) (Set.uIcc z.im w.im))
    (hlft : Set.EqOn (fun y : ℝ => F (↑z.re + ↑y * I))
      (fun y : ℝ => A (↑z.re + ↑y * I) - B (↑z.re + ↑y * I)) (Set.uIcc z.im w.im)) :
    rectBI z w F = rectBI z w A - rectBI z w B := by
  simp only [rectBI]
  rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr htop,
      intervalIntegral.integral_congr hrgt, intervalIntegral.integral_congr hlft,
      intervalIntegral.integral_sub hA_bot hB_bot, intervalIntegral.integral_sub hA_top hB_top,
      intervalIntegral.integral_sub hA_rgt hB_rgt, intervalIntegral.integral_sub hA_lft hB_lft]
  ring

set_option maxHeartbeats 1600000 in
-- The exceptional assembly runs the S5b contour-shift argument on the de-singularized integrand
-- `A = ker·G` (Goursat-clean on the box) and re-attaches the exceptional residue via
-- `kernel_residue`; the copied edge/tail estimates plus the `E`-arithmetic need headroom.
/-- **S5c — the contour-shift bound, exceptional-zero variant.** Same box and hypotheses as the
clean `psi1_contour_shift` (S5b), but the box is allowed to contain **one simple real zero** `β₁`
of `L(·,χ)` (`analyticOrderAt L β₁ = 1`), carved out by the widened hypothesis `hzf` (every zero
in the box region is `β₁`). The separation hypothesis `hβsep : σ₀ + w ≤ β₁` keeps `β₁` off the
left edge (discharged by S6, where `β₁` is the Siegel zero, far to the right of the edge). The
contour shift then picks up the residue at `β₁`:
`‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ E`, with `E` **identical** to the clean S5b bound. -/
theorem psi1_contour_shift_exceptional {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {x : ℝ} (hx : 3 ≤ x) {T σ₀ w β₁ : ℝ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hβsep : σ₀ + w ≤ β₁) (hβ1 : β₁ < 1)
    (hβ_simple : analyticOrderAt (LFunction χ) (β₁ : ℂ) = 1)
    (hzf : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
      ρ = (β₁ : ℂ)) :
    ‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ ≤ (1 / (2 * Real.pi)) *
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
  have hσ₀c : σ₀ < c := lt_trans hσ₀1 hc1
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
  have hwT : w ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  -- the local factorization `L = (·−β₁)·hfac` at the simple zero β₁
  have hana_β : AnalyticAt ℂ (LFunction χ) (β₁ : ℂ) :=
    ((differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ) _ (mem_univ _)
  obtain ⟨hfac, hfac_ana, hfac_ne, hfac_eq⟩ :=
    (hana_β.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast hβ_simple)
  -- the de-singularized log-derivative `Gtrue` (analytic through β₁)
  set G : ℂ → ℂ := fun s => -logDeriv (LFunction χ) s + 1 / (s - (β₁ : ℂ)) with hG
  set Gtrue : ℂ → ℂ := Function.update G (β₁ : ℂ) (-logDeriv hfac (β₁ : ℂ)) with hGtrue
  have hGtrue_β : DifferentiableAt ℂ Gtrue (β₁ : ℂ) := by
    have hh_diff : DifferentiableAt ℂ (fun s => -logDeriv hfac s) (β₁ : ℂ) := by
      simp only [logDeriv_apply]
      exact ((hfac_ana.deriv.differentiableAt).div hfac_ana.differentiableAt hfac_ne).neg
    have hpunct : ∀ᶠ z in 𝓝 (β₁ : ℂ), z ≠ (β₁ : ℂ) → G z = -logDeriv hfac z := by
      obtain ⟨U, hU_eq, hU_open, hβU⟩ := _root_.eventually_nhds_iff.mp hfac_eq
      have hh_ne_nhds : ∀ᶠ z in 𝓝 (β₁ : ℂ), hfac z ≠ 0 :=
        hfac_ana.continuousAt.eventually_ne hfac_ne
      obtain ⟨V, hV_ne, hV_open, hβV⟩ := _root_.eventually_nhds_iff.mp hh_ne_nhds
      obtain ⟨W, hW_ana, hW_open, hβW⟩ :=
        _root_.eventually_nhds_iff.mp hfac_ana.eventually_analyticAt
      refine _root_.eventually_nhds_iff.mpr
        ⟨U ∩ V ∩ W, ?_, (hU_open.inter hV_open).inter hW_open, ⟨⟨hβU, hβV⟩, hβW⟩⟩
      intro z hz hzβ
      have hz_ne : hfac z ≠ 0 := hV_ne z hz.1.2
      have hz_diff : DifferentiableAt ℂ hfac z := (hW_ana z hz.2).differentiableAt
      have hzβ' : z - (β₁ : ℂ) ≠ 0 := sub_ne_zero.mpr hzβ
      have hlocal : LFunction χ =ᶠ[𝓝 z] (fun w => (w - (β₁ : ℂ)) * hfac w) := by
        filter_upwards [((hU_open.inter hV_open).inter hW_open).mem_nhds hz] with w hw
        have := hU_eq w hw.1.1; rw [this, pow_one, smul_eq_mul]
      have hlogL : logDeriv (LFunction χ) z = logDeriv (fun w => (w - (β₁ : ℂ)) * hfac w) z := by
        rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - (β₁ : ℂ)) z := differentiableAt_id.sub_const _
      have hmul : logDeriv (fun w => (w - (β₁ : ℂ)) * hfac w) z
          = logDeriv (fun w : ℂ => w - (β₁ : ℂ)) z + logDeriv hfac z :=
        logDeriv_mul z hzβ' hz_ne hd1 hz_diff
      have hlin : logDeriv (fun w : ℂ => w - (β₁ : ℂ)) z = 1 / (z - (β₁ : ℂ)) := by
        rw [logDeriv_apply, deriv_sub_const]; simp
      rw [hG]; simp only; rw [hlogL, hmul, hlin]; ring
    have hev : Gtrue =ᶠ[𝓝 (β₁ : ℂ)] (fun s => -logDeriv hfac s) := by
      filter_upwards [hpunct] with z hz
      by_cases hzβ : z = (β₁ : ℂ)
      · rw [hzβ, hGtrue, Function.update_self]
      · rw [hGtrue, Function.update_of_ne hzβ]; exact hz hzβ
    exact hh_diff.congr_of_eventuallyEq hev
  -- box non-vanishing away from β₁
  have hLne_box_exc : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → s ≠ (β₁ : ℂ) →
      LFunction χ s ≠ 0 := by
    intro s hsl hsu hsi hsβ
    by_cases h1 : 1 ≤ s.re
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1
    · intro hs0; exact hsβ (hzf s hs0 (by linarith) (not_le.mp h1).le (by linarith))
  -- differentiability infrastructure
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
  have hkerAt : ∀ s : ℂ, s ≠ 0 → s + 1 ≠ 0 →
      DifferentiableAt ℂ (fun z => (x : ℂ) ^ (z + 1) / (z * (z + 1))) s := by
    intro s hs0 hs1
    apply DifferentiableAt.div
    · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
    · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
    · exact mul_ne_zero hs0 hs1
  have hGtrue_diff : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T →
      DifferentiableAt ℂ Gtrue s := by
    intro s hsl hsu hsi
    by_cases hsβ : s = (β₁ : ℂ)
    · rw [hsβ]; exact hGtrue_β
    · have hGeq : Gtrue =ᶠ[𝓝 s] G := by
        filter_upwards [compl_singleton_mem_nhds hsβ] with z hz
        rw [hGtrue, Function.update_of_ne (show z ≠ (β₁ : ℂ) from by simpa using hz)]
      have hLs : LFunction χ s ≠ 0 := hLne_box_exc s hsl hsu hsi hsβ
      have hGd : DifferentiableAt ℂ G s := by
        rw [hG]
        exact (hlogD_diff s hLs).add
          ((differentiableAt_const 1).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hsβ))
      exact hGd.congr_of_eventuallyEq hGeq
  -- the integrands
  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv (LFunction χ) s) with hF
  set A : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * Gtrue s with hA
  set Bfun : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - (β₁ : ℂ)) with hBfun
  set κ : ℂ := (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1)) with hκ
  have hFnorm : ∀ s : ℂ, ‖F s‖
      = x ^ (s.re + 1) * ‖(s * (s + 1))⁻¹‖ * ‖logDeriv (LFunction χ) s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re,
      Complex.one_re, div_eq_mul_inv, ← norm_inv]
  -- pointwise splitting F = A − Bfun off β₁
  have hAFB : ∀ s : ℂ, s ≠ (β₁ : ℂ) → F s = A s - Bfun s := by
    intro s hsβ
    have hGt : Gtrue s = -logDeriv (LFunction χ) s + 1 / (s - (β₁ : ℂ)) := by
      rw [hGtrue, Function.update_of_ne hsβ, hG]
    simp only [hF, hA, hBfun]
    rw [hGt]; ring
  -- `≠ β₁` facts for edge points
  have him_ne : ∀ (a τ : ℝ), τ ≠ 0 → ((a : ℂ) + (τ : ℂ) * I) ≠ (β₁ : ℂ) :=
    fun a τ hτ h => hτ (by simpa using congrArg Complex.im h)
  have hre_ne : ∀ (a b : ℝ), a ≠ β₁ → ((a : ℂ) + (b : ℂ) * I) ≠ (β₁ : ℂ) :=
    fun a b ha h => ha (by simpa using congrArg Complex.re h)
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  -- A is differentiable on the whole box
  have hA_diff : DifferentiableOn ℂ A (closedRect zc wc) := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm] at hs
    rw [Set.uIcc_of_le hσ₀c.le] at hs
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsim' : |s.im| ≤ T := by rw [abs_le]; exact ⟨hsim.1, hsim.2⟩
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hsre; linarith [hsre.1, hσ₀pos]
    have hs1 : s + 1 ≠ 0 := by
      intro h; have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1, hσ₀pos]
    have hAs : DifferentiableAt ℂ A s := by
      rw [hA]; exact (hkerAt s hs0 hs1).mul (hGtrue_diff s hsre.1 hsre.2 hsim')
    exact hAs.differentiableWithinAt
  have hA0 : rectBI zc wc A = 0 := rectBI_eq_zero_of_differentiableOn hA_diff
  -- the residue via kernel_residue
  have hBres : rectBI zc wc Bfun = 2 * ↑Real.pi * I * κ := by
    have hres := kernel_residue (z := zc) (w := wc) (x := x) hxpos (β := (β₁ : ℂ))
      (by rw [hzc_re]; exact hσ₀pos)
      (by rw [hzc_re, hwc_re]; exact hσ₀c)
      (by rw [hzc_im, hwc_im]; linarith)
      ⟨show zc.re < (β₁ : ℂ).re by rw [hzc_re, Complex.ofReal_re]; linarith,
        show (β₁ : ℂ).re < wc.re by rw [hwc_re, Complex.ofReal_re]; linarith⟩
      ⟨show zc.im < (β₁ : ℂ).im by rw [hzc_im, Complex.ofReal_im]; linarith,
        show (β₁ : ℂ).im < wc.im by rw [hwc_im, Complex.ofReal_im]; linarith⟩
    rw [hBfun, hκ]; exact hres
  -- rectBI F = − 2πi κ (Goursat on A + residue of Bfun; F = A − Bfun on the edges)
  have hedge_int : ∀ (γ : ℝ → ℂ) (a b : ℝ), Continuous γ →
      Set.MapsTo γ (Set.uIcc a b) (closedRect zc wc) →
      (∀ t ∈ Set.uIcc a b, γ t ≠ (β₁ : ℂ)) →
      IntervalIntegrable (fun t => A (γ t)) volume a b ∧
        IntervalIntegrable (fun t => Bfun (γ t)) volume a b := by
    intro γ a b hγ hmaps hne
    refine ⟨(hA_diff.continuousOn.comp hγ.continuousOn hmaps).intervalIntegrable, ?_⟩
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hmem := hmaps ht
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm, Set.uIcc_of_le hσ₀c.le,
        Set.uIcc_of_le (by linarith : -T ≤ T)] at hmem
    obtain ⟨hre, _⟩ := hmem
    simp only [Set.mem_Icc] at hre
    have h0 : γ t ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre; linarith [hre.1, hσ₀pos]
    have h1 : γ t + 1 ≠ 0 := by
      intro h; have : (γ t + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hre.1, hσ₀pos]
    have hβ : γ t ≠ (β₁ : ℂ) := hne t ht
    have hBd : DifferentiableAt ℂ Bfun (γ t) := by
      rw [hBfun]
      exact (hkerAt (γ t) h0 h1).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hβ)
    exact ((hBd.continuousAt).comp hγ.continuousAt).continuousWithinAt
  -- the four MapsTo (edges into the box)
  have hmaps_bot : Set.MapsTo (fun x : ℝ => (↑x + ↑zc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑zc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑zc.im * I : ℂ).im = zc.im by simp]; exact left_mem_uIcc
  have hmaps_top : Set.MapsTo (fun x : ℝ => (↑x + ↑wc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑wc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑wc.im * I : ℂ).im = wc.im by simp]; exact right_mem_uIcc
  have hmaps_rgt : Set.MapsTo (fun y : ℝ => (↑wc.re + ↑y * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑wc.re + ↑v * I : ℂ).re = wc.re by simp]; exact right_mem_uIcc
    · rw [show (↑wc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hmaps_lft : Set.MapsTo (fun y : ℝ => (↑zc.re + ↑y * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv
    rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑zc.re + ↑v * I : ℂ).re = zc.re by simp]; exact left_mem_uIcc
    · rw [show (↑zc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hne_bot : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑zc.im * I : ℂ) ≠ (β₁ : ℂ) :=
    fun t _ => him_ne t zc.im (by rw [hzc_im]; linarith)
  have hne_top : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑wc.im * I : ℂ) ≠ (β₁ : ℂ) :=
    fun t _ => him_ne t wc.im (by rw [hwc_im]; linarith)
  have hne_rgt : ∀ t ∈ Set.uIcc zc.im wc.im, (↑wc.re + ↑t * I : ℂ) ≠ (β₁ : ℂ) :=
    fun t _ => hre_ne wc.re t (by rw [hwc_re]; linarith)
  have hne_lft : ∀ t ∈ Set.uIcc zc.im wc.im, (↑zc.re + ↑t * I : ℂ) ≠ (β₁ : ℂ) :=
    fun t _ => hre_ne zc.re t (by rw [hzc_re]; linarith)
  obtain ⟨hA_bot, hB_bot⟩ :=
    hedge_int _ zc.re wc.re (by fun_prop) hmaps_bot hne_bot
  obtain ⟨hA_top, hB_top⟩ :=
    hedge_int _ zc.re wc.re (by fun_prop) hmaps_top hne_top
  obtain ⟨hA_rgt, hB_rgt⟩ :=
    hedge_int _ zc.im wc.im (by fun_prop) hmaps_rgt hne_rgt
  obtain ⟨hA_lft, hB_lft⟩ :=
    hedge_int _ zc.im wc.im (by fun_prop) hmaps_lft hne_lft
  have hlin : rectBI zc wc F = rectBI zc wc A - rectBI zc wc Bfun :=
    rectBI_sub_of_edge_eq hA_bot hA_top hA_rgt hA_lft hB_bot hB_top hB_rgt hB_lft
      (fun t ht => hAFB _ (hne_bot t ht)) (fun t ht => hAFB _ (hne_top t ht))
      (fun t ht => hAFB _ (hne_rgt t ht)) (fun t ht => hAFB _ (hne_lft t ht))
  have hrectF : rectBI zc wc F = -(2 * ↑Real.pi * I) * κ := by
    rw [hlin, hA0, hBres]; ring
  rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im] at hrectF
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  have hgour2 : I * (RIGHT + (2 * ↑Real.pi : ℂ) * κ) = TOPI - BOTI + I * LEFT := by
    linear_combination hrectF
  have hRnorm : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour2, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- the c-line integrability and the Perron bridge
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + v * I)) := by
    simp only [hF]; exact contour_integrand_integrable χ hχ1 hx1 hc1 hc2.le
  have hbridge : psi1Chi x χ = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + v * I) := by
    rw [psi1_eq_contour_integral χ hx1 hc1]
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + v * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  -- the distance argument on the edges (carving β₁)
  have hdist_edge : ∀ (s : ℂ), (s.re = σ₀ ∨ |s.im| = T) → σ₀ ≤ s.re → |s.im| ≤ T →
      ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ ∈ Metric.ball (2 + (s.im : ℂ) * I) (3 / 2) →
        w ≤ ‖s - ρ‖ := by
    intro s hedge hsl hsi ρ hρ0 hρball
    have hρre1 : ρ.re < 1 := by
      by_contra hc; exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hc) hρ0
    have hρim : |ρ.im| ≤ T + 2 := by
      have himdist : |ρ.im - s.im| ≤ 3 / 2 := by
        have h := Complex.abs_im_le_norm (ρ - (2 + (s.im : ℂ) * I))
        have hival : (ρ - (2 + (s.im : ℂ) * I)).im = ρ.im - s.im := by simp
        rw [hival] at h
        have hb : ‖ρ - (2 + (s.im : ℂ) * I)‖ < 3 / 2 := by rw [← dist_eq_norm]; exact hρball
        linarith
      have hh1 := abs_le.mp himdist
      have hh2 := abs_le.mp hsi
      rw [abs_le]; constructor <;> linarith
    by_cases hρβ : ρ = (β₁ : ℂ)
    · subst hρβ
      rcases hedge with hre | him
      · have h := Complex.abs_re_le_norm (s - (β₁ : ℂ))
        rw [Complex.sub_re, hre, Complex.ofReal_re] at h
        have hb : |σ₀ - β₁| = β₁ - σ₀ := by rw [abs_of_nonpos (by linarith)]; ring
        rw [hb] at h; linarith
      · have h := Complex.abs_im_le_norm (s - (β₁ : ℂ))
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero, him] at h
        linarith
    · have hρre2 : ρ.re ≤ σ₀ - w := by
        by_contra hc
        exact hρβ (hzf ρ hρ0 (le_of_lt (not_le.mp hc)) hρre1.le hρim)
      have hre := Complex.abs_re_le_norm (s - ρ)
      rw [Complex.sub_re] at hre
      calc w ≤ s.re - ρ.re := by linarith
        _ = |s.re - ρ.re| := (abs_of_nonneg (by linarith)).symm
        _ ≤ ‖s - ρ‖ := hre
  -- edge bound constant and the horizontal pointwise estimate
  set Cbnd : ℝ := x ^ (c + 1) * B / T ^ 2 with hCbnd
  have hxc1pos : (0 : ℝ) < x ^ (c + 1) := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c, ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀gt]
    have hτ0 : τ ≠ 0 := by intro h; rw [h, abs_zero] at hτ; linarith
    have hsβ : ((u : ℂ) + (τ : ℂ) * I) ≠ (β₁ : ℂ) := him_ne u τ hτ0
    have hLs : LFunction χ ((u : ℂ) + (τ : ℂ) * I) ≠ 0 :=
      hLne_box_exc _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim]; exact le_of_eq hτ) hsβ
    have hlogb : ‖logDeriv (LFunction χ) ((u : ℂ) + (τ : ℂ) * I)‖ ≤ B := by
      rw [hBdef, hL4]
      exact norm_logDeriv_le_of_ball_dist χ hχ hf hw hσ₀w
        (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim]; exact le_of_eq hτ) hLs
        (hdist_edge _ (Or.inr (by rw [hsim]; exact hτ)) (by rw [hsre]; linarith [hu.1])
          (by rw [hsim]; exact le_of_eq hτ))
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
  have hLEFTb : ‖LEFT‖ ≤ B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + v * I)) volume (-T) T := by
      simp only [hF]
      apply ContinuousOn.intervalIntegrable
      have hLcont : Continuous (LFunction χ) := (differentiable_LFunction hχ1).continuous
      have hdLcont : Continuous (deriv (LFunction χ)) := hdL_diff.continuous
      have hline : Continuous (fun v : ℝ => (σ₀ : ℂ) + v * I) := by fun_prop
      have hLne : ∀ v ∈ Set.uIcc (-T) T, LFunction χ ((σ₀ : ℂ) + v * I) ≠ 0 := by
        intro v hv
        rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] at hv
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
        exact hLne_box_exc _ hsre.ge (by rw [hsre]; linarith)
          (by rw [hsim, abs_le]; exact ⟨hv.1, hv.2⟩) (hre_ne σ₀ v (by linarith))
      have hden : ∀ v ∈ Set.uIcc (-T) T,
          ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1) ≠ 0 := by
        intro v _
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        refine mul_ne_zero ?_ ?_
        · intro h; rw [h, Complex.zero_re] at hsre; linarith [hσ₀pos]
        · intro h; have : (((σ₀ : ℂ) + v * I) + 1).re = 0 := by rw [h]; simp
          rw [Complex.add_re, Complex.one_re, hsre] at this; linarith [hσ₀pos]
      apply ContinuousOn.mul
      · apply ContinuousOn.div
        · exact ((by fun_prop : Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) + 1).const_cpow
            (Or.inl hxC)).continuousOn
        · exact (by fun_prop :
            Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1)).continuousOn
        · exact hden
      · have hrw : (fun v : ℝ => -logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I))
            = fun v : ℝ =>
              -(deriv (LFunction χ) ((σ₀ : ℂ) + v * I) / LFunction χ ((σ₀ : ℂ) + v * I)) := by
          funext v; rw [logDeriv_apply]
        rw [hrw]
        exact (((hdLcont.comp hline).continuousOn.div (hLcont.comp hline).continuousOn hLne)).neg
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hBnn (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + v * I)‖ ≤ B * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
      have hsβ : ((σ₀ : ℂ) + v * I) ≠ (β₁ : ℂ) := hre_ne σ₀ v (by linarith)
      have hLs : LFunction χ ((σ₀ : ℂ) + v * I) ≠ 0 :=
        hLne_box_exc _ hsre.ge (by rw [hsre]; linarith) (by rw [hsim]; exact hvT) hsβ
      have hlogb : ‖logDeriv (LFunction χ) ((σ₀ : ℂ) + v * I)‖ ≤ B := by
        rw [hBdef, hL4]
        exact norm_logDeriv_le_of_ball_dist χ hχ hf hw hσ₀w hsre.ge (by rw [hsre]; linarith)
          (by rw [hsim]; exact hvT) hLs
          (hdist_edge _ (Or.inl hsre) hsre.ge (by rw [hsim]; exact hvT))
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
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  -- final assembly (κ absorbs the residue)
  have hπℂ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkappa : (1 / (2 * Real.pi) : ℝ) • ((2 * ↑Real.pi : ℂ) * κ) = κ := by
    rw [Complex.real_smul]; push_cast; field_simp
  have hcollect : psi1Chi x χ + κ
      = (1 / (2 * Real.pi)) • ((RIGHT + (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)) := by
    have e1 : (1 / (2 * Real.pi) : ℝ) • ((RIGHT + (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
        = (1 / (2 * Real.pi)) • (RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
          + (1 / (2 * Real.pi)) • ((2 * ↑Real.pi : ℂ) * κ) := by
      simp only [Complex.real_smul]; ring
    rw [e1, hkappa, ← htrunc, ← hbridge]
  rw [hcollect, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖(RIGHT + (2 * ↑Real.pi : ℂ) * κ) + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖
          + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀))
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
        have h1 : ‖RIGHT + (2 * ↑Real.pi : ℂ) * κ‖
            ≤ 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * B * x ^ (c + 1) / T ^ 2 + B * x ^ (σ₀ + 1) * (Real.pi / σ₀)
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by ring

end Salt.SW
