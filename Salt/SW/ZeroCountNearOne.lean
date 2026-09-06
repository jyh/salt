/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MaxModulus
import Salt.SW.ZetaPole
import Salt.SW.ZeroFree
import Salt.SW.LandauPage

/-!
# The radius-resolved Prachar zero count near `s = 1` (HB-ENGINE WP2)

For `χ` a nontrivial (here: primitive) Dirichlet character mod `q ≥ 2` and `0 < r < 1/2`,
the number of zeros `ρ` of `L(s,χ)` in `closedBall (1 : ℂ) r`, counted with multiplicity
(the `MeromorphicOn.divisor` finsum, matching `Salt/SW/ZeroCount.lean`'s idiom), is
`≤ C · (1 + r · log (q + 2))` for an absolute constant `C`.

## Route — Landau partial fractions, NOT Jensen

The house-drawn sketch proposed a Jensen re-centering. That route yields only
`count ≪ log q + log(1/r)`, which does **not** imply the paper-sufficient guarded shape
`r ≥ 1/log q → count ≤ C·r·log q` (the `1/r` cancellation is missing). The correct route is
the classical Landau argument, mirroring the corpus zero-free-region machinery
(`zeta_neg_re_logDeriv_le`): evaluate the log-derivative partial fraction at `σ = 1 + r` on
the real axis. Each zero `ρ ∈ closedBall (1) r` contributes
`Re (1/(σ − ρ)) ≥ 1/(5r)` (since `Re ρ ≤ 1`, `|σ − ρ|² ≤ 5r²`); the remaining zeros'
partial-fraction terms are `≥ 0` and are kept; and the whole sum is
`≤ B + Re(L'/L(σ,χ)) ≤ B + (1/r + 1)` where `B = 120 log(4 M₀)` is the landed
Borel–Carathéodory numeric (`LFunction_norm_logDeriv_sub_sum'`) and
`Re(L'/L(σ,χ)) ≤ −ζ'/ζ(σ) ≤ 1/(σ−1) + 1` (`neg_logDeriv_zeta_le`). Multiplying by `5r`:
`(count) ≤ 5r·B + 5 + 5r ≤ C(1 + r log(q+2))`.

The `1 +` absorbs the `1/r` pole (an isolated/Siegel zero costs `O(1)`); the `r log q` is the
genuine density. Scope `r < 1/2` keeps `closedBall (1) r ⊆ ball (2) (3/2)` by the triangle
inequality, so every zero counted lives comfortably in `Re ∈ (1/2, 1)` — no low-`Re` critical
or trivial zeros to chase. This covers all downstream uses (Heath-Brown needs the count at the
`r ≈ 1/log q` scale, far below `1/2`).

## Mathlib / corpus consumed
* `LFunction_norm_logDeriv_sub_sum'` (the Blaschke numeric), `neg_re_logDeriv_le`,
  `neg_logDeriv_zeta_le`, `neg_logDeriv_LSeries_eq`, `neg_logDeriv_LSeries_eq_LSeries_twist`,
  `log_four_M0_le`.
* `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (zeros have `Re < 1`),
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `LSeriesSummable_vonMangoldt`.
* `MeromorphicOn.divisor_congr_codiscreteWithin`, `divisor_fun_mul`, `divisor_fun_prod`,
  `divisor_pow`, `divisor_sub_const_self`/`_of_ne`, `AnalyticOnNhd.divisor_apply`.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The per-zero lower bound `Re (1/(σ − ρ)) ≥ 1/(5r)` -/

/-- For a point `ρ` in `closedBall (1 : ℂ) r` with `Re ρ ≤ 1`, and `σ = 1 + r` on the real
axis, the partial-fraction term has real part `≥ 1/(5r)`. Geometry: `σ − Re ρ ∈ [r, 2r]` and
`|σ − ρ|² = (σ − Re ρ)² + (Im ρ)² ≤ (2r)² + r² = 5r²`. -/
lemma re_one_div_sub_ge {ρ : ℂ} {r : ℝ} (hr : 0 < r) (hmem : ρ ∈ closedBall (1 : ℂ) r)
    (hre : ρ.re ≤ 1) : 1 / (5 * r) ≤ (1 / (((1 : ℂ) + (r : ℂ)) - ρ)).re := by
  rw [mem_closedBall, dist_eq_norm] at hmem
  -- the coordinate constraint `(Re ρ − 1)² + (Im ρ)² ≤ r²`
  have hdecomp : ρ - 1 = ((ρ.re - 1 : ℝ) : ℂ) + ((ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hns : (ρ.re - 1) ^ 2 + ρ.im ^ 2 ≤ r ^ 2 := by
    have h2 : ‖ρ - 1‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (ρ - 1), hmem]
    rw [hdecomp, Complex.norm_add_mul_I] at h2
    rwa [Real.sq_sqrt (by positivity)] at h2
  set a := ρ.re with ha
  set b := ρ.im with hb
  set d : ℝ := 1 + r - a with hd
  have hdr : r ≤ d := by rw [hd]; linarith
  have hden : d ^ 2 + b ^ 2 ≤ 5 * r ^ 2 := by nlinarith [hns, hdr, hr]
  have hdpos : 0 < d := by linarith
  -- the real part as `d / (d² + b²)`
  have hwre : (((1 : ℂ) + (r : ℂ)) - ρ).re = d := by
    rw [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re, hd, ha]
  have hwim : (((1 : ℂ) + (r : ℂ)) - ρ).im = -b := by
    rw [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_im, hb]; ring
  have hDpos : (0 : ℝ) < d * d + (-b) * (-b) := by nlinarith [hdpos, sq_nonneg b]
  have hval : (1 / (((1 : ℂ) + (r : ℂ)) - ρ)).re = d / (d * d + (-b) * (-b)) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hwre, hwim]
  rw [hval, le_div_iff₀ hDpos, div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by positivity : (0 : ℝ) < 5 * r)]
  nlinarith [hden, hdr, hr, hdpos, mul_pos hr hdpos]

/-! ## 2. The main count -/

open scoped LSeries.notation in
/-- **The radius-resolved Prachar count near `s = 1`.** For a primitive Dirichlet character `χ`
mod `q ≥ 2` and `0 < r < 1/2`, the zeros of `L(·,χ)` in `closedBall (1 : ℂ) r`, counted with
multiplicity (the `MeromorphicOn.divisor` finsum, exactly the `LFunction_zero_count_le` idiom),
number `≤ C·(1 + r·log (q + 2))` for the absolute constant `C = 7200`.

Route: the Landau partial-fraction argument at `σ = 1 + r` (see the module docstring). -/
theorem LFunction_zero_count_near_one :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2 ≤ q → ∀ {r : ℝ}, 0 < r → r < 1 / 2 →
        ((∑ᶠ u, divisor (LFunction χ) (closedBall (1 : ℂ) r) u : ℤ) : ℝ)
          ≤ C * (1 + r * Real.log ((q : ℝ) + 2)) := by
  refine ⟨7200, by norm_num, ?_⟩
  intro q hNe χ hχ hq2 r hr0 hr
  classical
  have hne1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq2
  obtain ⟨Z, m, h, hmemZ, hana_h, hne_h, hEqOn, hident, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' χ hχ hq2 0
  set c : ℂ := 2 + ((0 : ℝ) : ℂ) * I with hcdef
  have hc2 : c = 2 := by rw [hcdef]; simp
  set σ : ℂ := (1 : ℂ) + (r : ℂ) with hσdef
  have hσre : σ.re = 1 + r := by rw [hσdef]; simp
  set V : Set ℂ := closedBall (1 : ℂ) r with hVdef
  -- geometry: the count-ball sits inside the frozen disk
  have hsub : V ⊆ ball c (3 / 2) := by
    rw [hVdef, hc2]
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖z - 2‖ ≤ ‖z - 1‖ + ‖(1 : ℂ) - 2‖ := by
      have := norm_add_le (z - 1) ((1 : ℂ) - 2)
      rwa [show (z - 1) + ((1 : ℂ) - 2) = z - 2 by ring] at this
    have h2 : ‖(1 : ℂ) - 2‖ = 1 := by norm_num
    rw [h2] at h1; linarith
  -- `L` analytic on the count-ball
  have hanaV : AnalyticOnNhd ℂ (LFunction χ) V :=
    ((differentiable_LFunction hne1).differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ _)
  -- zeros of `L` have `Re < 1`
  have hzero_re : ∀ ρ ∈ Z, ρ.re < 1 := by
    intro ρ hρ
    by_contra hcn
    exact (LFunction_ne_zero_of_one_le_re χ (Or.inl hne1) (not_lt.mp hcn)) (hmemZ ρ hρ).2
  -- the filtered zero set
  set Zr : Finset ℂ := Z.filter (fun ρ => ρ ∈ V) with hZrdef
  -- === the divisor bridge: finsum = filtered finset sum of multiplicities ===
  have hdiv_eq : ∀ ρ ∈ Zr, divisor (LFunction χ) V ρ = (m ρ : ℤ) := by
    intro ρ hρ
    rw [hZrdef, Finset.mem_filter] at hρ
    obtain ⟨hρZ, hρV⟩ := hρ
    have horder := analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρZ (hmemZ ρ hρZ).1
    rw [hanaV.divisor_apply hρV, horder]; simp
  have hsupp : Function.support (fun u => divisor (LFunction χ) V u) ⊆ ↑Zr := by
    intro u hu
    rw [Function.mem_support] at hu
    have huV : u ∈ V := by
      by_contra hnV
      exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnV)
    have hLu : LFunction χ u = 0 := by
      by_contra hne0
      apply hu
      rw [hanaV.divisor_apply huV, (hanaV u huV).analyticOrderAt_eq_zero.mpr hne0]; simp
    have huball : u ∈ ball c (3 / 2) := hsub huV
    have huZ : u ∈ Z := by
      by_contra hnZ
      have heqv : LFunction χ u = (∏ ρ ∈ Z, (u - ρ) ^ (m ρ)) * h u := hEqOn huball
      rw [heqv] at hLu
      exact (mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr (by rintro rfl; exact hnZ hρ)))
        (hne_h u huball)) hLu
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨huZ, huV⟩)
  have hZr_val : (((∑ᶠ u, divisor (LFunction χ) V u : ℤ)) : ℝ) = ∑ ρ ∈ Zr, (m ρ : ℝ) := by
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ; rw [hdiv_eq ρ hρ]; push_cast; ring
  -- === the analytic Landau bound (staged) ===
  have hTbound : ∑ ρ ∈ Zr, (m ρ : ℝ)
      ≤ 5 * r * (120 * Real.log (4 *
          (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))) + 5 + 5 * r := by
    set Blit : ℝ := 120 * Real.log (4 *
      (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) with hBlit
    -- the numeric at `σ = 1 + r`
    have hσC : (1 : ℝ) < σ.re := by rw [hσre]; linarith
    have hL_ne : LFunction χ σ ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl hne1) (le_of_lt hσC)
    have hscnorm : ‖σ - c‖ ≤ 23 / 20 := by
      rw [hc2, hσdef]
      have hsub2 : (1 : ℂ) + (r : ℂ) - 2 = ((r - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : r - 1 ≤ 0)]
      linarith
    have hbnd := hnum σ hscnorm hL_ne
    have hre := neg_re_logDeriv_le hbnd
    -- the Landau lower bound on `Re(−L'/L(σ))`
    have h1r : (1 : ℝ) < 1 + r := by linarith
    have h2r : (1 : ℝ) + r ≤ 2 := by linarith
    have hlandau := landau_neg_logDeriv_re_lower χ h1r h2r
    have hσeq : ((1 + r : ℝ) : ℂ) = σ := by rw [hσdef]; push_cast; ring
    rw [hσeq, show (1 + r - 1 : ℝ) = r by ring] at hlandau
    -- combine: `S ≤ Blit + 1/r + 1`
    have hS : (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) ≤ Blit + 1 / r + 1 := by
      linarith [hre, hlandau]
    -- positivity of every partial-fraction term
    have hpos : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / (σ - ρ)).re := by
      intro ρ hρ
      refine mul_nonneg (by positivity) ?_
      rw [one_div, Complex.inv_re]
      refine div_nonneg ?_ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hσre]
      linarith [hzero_re ρ hρ, hr0]
    -- keep the near-`1` terms, lower-bound each by `1/(5r)`
    have hTle : ∑ ρ ∈ Zr, (m ρ : ℝ) ≤ 5 * r * (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
      · intro ρ hρ
        rw [hZrdef, Finset.mem_filter] at hρ
        obtain ⟨hρZ, hρV⟩ := hρ
        have hlow := re_one_div_sub_ge hr0 hρV (le_of_lt (hzero_re ρ hρZ))
        rw [← hσdef] at hlow
        have h1le : (1 : ℝ) ≤ 5 * r * (1 / (σ - ρ)).re := by
          have hstep := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 5 * r)
          rwa [mul_one_div, div_self (by positivity : (5 : ℝ) * r ≠ 0)] at hstep
        calc (m ρ : ℝ) = (m ρ : ℝ) * 1 := (mul_one _).symm
          _ ≤ (m ρ : ℝ) * (5 * r * (1 / (σ - ρ)).re) :=
              mul_le_mul_of_nonneg_left h1le (by positivity)
          _ = 5 * r * ((m ρ : ℝ) * (1 / (σ - ρ)).re) := by ring
      · intro ρ hρZ _
        exact mul_nonneg (by positivity) (hpos ρ hρZ)
    -- assemble
    have hrinv : r * (1 / r) = 1 := by rw [mul_one_div, div_self hr0.ne']
    calc ∑ ρ ∈ Zr, (m ρ : ℝ)
        ≤ 5 * r * (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) := hTle
      _ ≤ 5 * r * (Blit + 1 / r + 1) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 5 * r * Blit + 5 + 5 * r := by linear_combination 5 * hrinv
  -- === constant collapse ===
  set B : ℝ := 120 * Real.log (4 *
      (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) with hBdef
  have hlogq : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith)
  have hBcollapse : B ≤ 720 * Real.log (2 * (q : ℝ)) := by
    have hlfm := log_four_M0_le (f := q) (q := q) (t := (0 : ℝ)) (γ := (0 : ℝ))
      hq2 le_rfl hq2 (by simp)
    rw [hBdef]
    have hmul : (q : ℝ) * (|(0:ℝ)| + 2) = 2 * (q : ℝ) := by rw [abs_zero]; ring
    rw [hmul] at hlfm
    linarith [hlfm]
  have hlog2q : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log ((q : ℝ) + 2) := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h2q0 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      linarith
    have h2q : (2 : ℝ) * (q : ℝ) ≤ ((q : ℝ) + 2) ^ 2 := by nlinarith [hq2, hqpos]
    calc Real.log (2 * (q : ℝ)) ≤ Real.log (((q : ℝ) + 2) ^ 2) :=
          Real.log_le_log (by linarith) h2q
      _ = 2 * Real.log ((q : ℝ) + 2) := by
          rw [Real.log_pow]; push_cast; ring
  calc (((∑ᶠ u, divisor (LFunction χ) V u : ℤ)) : ℝ)
      = ∑ ρ ∈ Zr, (m ρ : ℝ) := hZr_val
    _ ≤ 5 * r * B + 5 + 5 * r := hTbound
    _ ≤ 7200 * (1 + r * Real.log ((q : ℝ) + 2)) := by
        have hB2 : B ≤ 1440 * Real.log ((q : ℝ) + 2) := by linarith [hBcollapse, hlog2q]
        have hrpos : 0 ≤ r := le_of_lt hr0
        nlinarith [mul_le_mul_of_nonneg_left hB2 (by positivity : (0:ℝ) ≤ 5 * r),
          hlogq, hr, hr0, mul_nonneg hrpos hlogq]

/-- **The guarded (density) form.** In the regime `r ≥ 1/log(q+2)` — all Heath-Brown's WP2
consumers use — the `1 +` is absorbed and the count is the pure density shape
`≤ C·r·log(q+2)`. Immediate from `LFunction_zero_count_near_one` since `r·log(q+2) ≥ 1` there. -/
theorem LFunction_zero_count_near_one_guarded :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2 ≤ q → ∀ {r : ℝ}, 0 < r → r < 1 / 2 →
        1 / Real.log ((q : ℝ) + 2) ≤ r →
        ((∑ᶠ u, divisor (LFunction χ) (closedBall (1 : ℂ) r) u : ℤ) : ℝ)
          ≤ C * (r * Real.log ((q : ℝ) + 2)) := by
  obtain ⟨C, hC, hmain⟩ := LFunction_zero_count_near_one
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hNe χ hχ hq2 r hr0 hr hrge
  have hlogpos : 0 < Real.log ((q : ℝ) + 2) := by
    apply Real.log_pos
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have h1 : (1 : ℝ) ≤ r * Real.log ((q : ℝ) + 2) := (div_le_iff₀ hlogpos).mp hrge
  calc ((∑ᶠ u, divisor (LFunction χ) (closedBall (1 : ℂ) r) u : ℤ) : ℝ)
      ≤ C * (1 + r * Real.log ((q : ℝ) + 2)) := hmain χ hχ hq2 hr0 hr
    _ ≤ 2 * C * (r * Real.log ((q : ℝ) + 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hC)]

/-! ## 3. The count at height (B2 W1 — Jutila's Lemma 8, Linnik's density lemma)

Jutila 1977, p.51, Lemma 8 (Prachar p.331): the zeros of `L(s,χ)` in `α ≤ σ ≤ 1`,
`|t − T| ≤ (1 − α)/2` number `≪ (1 − α)·log(q(T + 1)) + 1`. The corpus form is the
radius-resolved count of §2 moved to the centre `1 + it₀`: for a primitive `χ` mod `q ≥ 2`,
every real `t₀` and `0 < r < 1/2`, the zeros in `closedBall (1 + t₀·I) r` (with multiplicity)
number `≤ 7200·(1 + r·log(q + |t₀| + 2))` (`LFunction_zero_count_near_one_at_height`). The
route is §2's Landau argument VERBATIM at the point `σ = 1 + r + t₀·I`: the Blaschke numeric
`LFunction_norm_logDeriv_sub_sum'` is already stated at an arbitrary centre `2 + t₀·I` with
`M₀ = 5(4 + |t₀|)√q(1 + log q)`; the per-zero geometry is translation-invariant
(`re_one_div_sub_ge_at_height`); the termwise ζ-majorant `−(1/(σ − 1) + 1) ≤ Re(−L'/L(s, χ))`
holds at every `s` with `Re s = σ` since `‖χ(n) n^{−s}‖ = n^{−σ}`
(`landau_neg_logDeriv_re_lower_of_re`); and the constant collapses through `log_four_M0_le` at
`t = γ = t₀`, `B ≤ 720·log(q(|t₀| + 2)) ≤ 1440·log(q + |t₀| + 2)` (from
`q(|t₀| + 2) ≤ (q + |t₀| + 2)²`), so the SAME `C = 7200` closes: `5r·B + 5 + 5r ≤ 7200(1 + rL)`
needs only `5 + 5r ≤ 7200`. The design (v2 §2 L8, #5) retains `7200` so that the height form at
`t₀ = 0` IS `LFunction_zero_count_near_one` after `simp` — the exit `example` below.

## The honest label

Lemma 8 is an INPUT to the density theorem's assembly (design v2 §4, W9e: one
`closedBall (1 + (k + ½)Δ·I) r` per `Δ`-box with `r = Δ√(λ² + 1/4)`, `Δ = 1/log D`; since
`√(λ² + 1/4) ≤ λ + 1/2` and `log(q + |t₀| + 2) ≤ (3/2)·log(qT)` for `q ≥ 3`, `T ≥ 2`,
`|t₀| ≤ T + 1`, the count per box is `≤ 7200·(1.75 + 1.5λ) = O(λ + 1)` — F6's log-free shape).
Nothing here bears on twin primes or on the crown's conditions. `7200` is the corpus's constant,
not Prachar's; nothing consumes it sharply. The measured receipts (`h2c-desk/w1w5_receipts.py`):
`q(|t₀| + 2)/(q + |t₀| + 2)² ≤ 1/4`; the assembly's slack `7192.5` — in the ADDITIVE term only:
the `r·log` coefficient is `5 × 1440 = 7200` exactly and is TIGHT for this chain; the exact
minimum of
`Re(1/(σ − ρ))` over the disc is `1/(2r)` (the row's `1/(5r)` is 2.5× crude, as in §1);
`7200(1 + ¼·log 7) = 10,702.6`; at `t₀ = 0` the bound is `:98`'s verbatim. The zero level:
`0 < r` is load-bearing (at `r = −1` the ball is empty and the right side is
`7200(1 − log(q + |t₀| + 2)) < 0`); `r < 1/2`, `2 ≤ q` and `IsPrimitive` are the route's
(the statement stays true at `r = 1`, at `q = 1`, and for an imprimitive `χ`, but the Blaschke
numeric is stated for primitive `χ` mod `q ≥ 2` and the ball must sit in `ball (2 + t₀·I) (3/2)`);
`q = 2` is vacuous (`three_le_of_ne_one`). -/

open ArithmeticFunction in
open scoped LSeries.notation in
/-- At real `σ`, the real part of the `↗Λ` L-series term is `Λ(n)·n^{−σ}` (the private
`term_vonMangoldt_eq` of `LandauPage.lean` re-derived at the real part, the form the
at-height majorant needs when the term's own exponent is complex). -/
private lemma term_vonMangoldt_re (σ : ℝ) (n : ℕ) :
    (LSeries.term ↗vonMangoldt (σ : ℂ) n).re = vonMangoldt n / (n : ℝ) ^ σ := by
  have hval : LSeries.term ↗vonMangoldt (σ : ℂ) n
      = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hval, Complex.ofReal_re]

open ArithmeticFunction in
open scoped LSeries.notation in
/-- **The termwise ζ-majorant at any height.** For any Dirichlet character `χ` mod `q` and
`s` with `1 < Re s ≤ 2`, `−(1/(Re s − 1) + 1) ≤ Re(−L'/L(s, χ))`: `§2`'s
`landau_neg_logDeriv_re_lower` off the real axis, by `‖χ(n) n^{−s}‖ ≤ n^{−Re s}`
(`Complex.norm_natCast_cpow_of_pos`) against the real-axis majorant `−ζ'/ζ(Re s)`. -/
theorem landau_neg_logDeriv_re_lower_of_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    -(1 / (s.re - 1) + 1) ≤ (-logDeriv (LFunction χ) s).re := by
  have hbridge : -logDeriv (LFunction χ) s = LSeries (↗χ * ↗vonMangoldt) s :=
    (neg_logDeriv_LSeries_eq χ h1).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist χ h1)
  rw [hbridge]
  have hreC : (1 : ℝ) < ((s.re : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact h1
  -- summabilities: the twist at `s`, the real-axis majorant at `Re s`
  have hSχ : Summable (LSeries.term (↗χ * ↗vonMangoldt) s) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1
  have hSΛ : Summable (LSeries.term ↗vonMangoldt ((s.re : ℝ) : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hreC
  -- the termwise comparison `−(term Λ at Re s).re ≤ (term χΛ at s).re`
  have hterm : ∀ n : ℕ, -(LSeries.term ↗vonMangoldt ((s.re : ℝ) : ℂ) n).re
      ≤ (LSeries.term (↗χ * ↗vonMangoldt) s n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hd : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
      have hΛ0 : (0 : ℝ) ≤ vonMangoldt n := vonMangoldt_nonneg
      have hΛre : (LSeries.term ↗vonMangoldt ((s.re : ℝ) : ℂ) n).re
          = vonMangoldt n / (n : ℝ) ^ s.re := term_vonMangoldt_re s.re n
      have hnorm : ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖
          ≤ vonMangoldt n / (n : ℝ) ^ s.re := by
        have hkey : ‖(χ (n : ZMod q) : ℂ)‖ * ‖((vonMangoldt n : ℝ) : ℂ)‖
            ≤ vonMangoldt n := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
          nlinarith [DirichletCharacter.norm_le_one χ (n : ZMod q),
            norm_nonneg (χ (n : ZMod q)), hΛ0]
        rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, norm_div, norm_mul,
          Complex.norm_natCast_cpow_of_pos hnpos s]
        exact div_le_div_of_nonneg_right hkey (le_of_lt hd)
      have habs := abs_le.mp (le_trans
        (Complex.abs_re_le_norm (LSeries.term (↗χ * ↗vonMangoldt) s n)) hnorm)
      rw [hΛre]
      linarith [habs.1]
  -- sum the comparison
  have hre₁ : (LSeries (↗χ * ↗vonMangoldt) s).re
      = ∑' n, (LSeries.term (↗χ * ↗vonMangoldt) s n).re := Complex.re_tsum hSχ
  have hre₀ : (LSeries ↗vonMangoldt ((s.re : ℝ) : ℂ)).re
      = ∑' n, (LSeries.term ↗vonMangoldt ((s.re : ℝ) : ℂ) n).re := Complex.re_tsum hSΛ
  have hs₁ := (Complex.hasSum_re hSχ.hasSum).summable
  have hs₀ := (Complex.hasSum_re hSΛ.hasSum).summable
  have hcmp : -(LSeries ↗vonMangoldt ((s.re : ℝ) : ℂ)).re
      ≤ (LSeries (↗χ * ↗vonMangoldt) s).re := by
    rw [hre₀, hre₁, ← tsum_neg]
    exact hs₀.neg.tsum_le_tsum hterm hs₁
  -- the ζ pole bound (S3c) on the real axis at `Re s`
  have hζ : (LSeries ↗vonMangoldt ((s.re : ℝ) : ℂ)).re ≤ 1 / (s.re - 1) + 1 := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hreC]
    exact neg_logDeriv_zeta_le h1 h2
  linarith [hcmp, hζ]

/-- `re_one_div_sub_ge` translated to the centre `1 + t₀·I`: for `ρ` in
`closedBall (1 + t₀·I) r` with `Re ρ ≤ 1` and `σ = 1 + r + t₀·I`, `Re(1/(σ − ρ)) ≥ 1/(5r)`
(the exact minimum is `1/(2r)`). -/
theorem re_one_div_sub_ge_at_height {ρ : ℂ} {r t₀ : ℝ} (hr : 0 < r)
    (hmem : ρ ∈ closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) (hre : ρ.re ≤ 1) :
    1 / (5 * r) ≤ (1 / (((1 : ℂ) + (r : ℂ) + (t₀ : ℂ) * I) - ρ)).re := by
  -- translation invariance of the disc
  have hmem' : ρ - (t₀ : ℂ) * I ∈ closedBall (1 : ℂ) r := by
    rw [mem_closedBall, dist_eq_norm] at hmem ⊢
    convert hmem using 2
    ring
  have hre' : (ρ - (t₀ : ℂ) * I).re ≤ 1 := by
    simpa [Complex.sub_re, Complex.mul_I_re, Complex.ofReal_im] using hre
  have hbase := re_one_div_sub_ge hr hmem' hre'
  convert hbase using 3
  ring

open scoped LSeries.notation in
/-- **Jutila's Lemma 8 (Linnik's density lemma) at height.** For a primitive Dirichlet
character `χ` mod `q ≥ 2`, every real `t₀` and `0 < r < 1/2`, the zeros of `L(·,χ)` in
`closedBall (1 + t₀·I) r`, counted with multiplicity (the `MeromorphicOn.divisor` finsum, the
`LFunction_zero_count_near_one` idiom), number `≤ C·(1 + r·log(q + |t₀| + 2))` for the absolute
constant `C = 7200` — §2's constant, so that `t₀ = 0` recovers `:98` verbatim.

Route: §2's Landau partial-fraction argument at `σ = 1 + r + t₀·I` inside the Blaschke disk
`ball (2 + t₀·I) (3/2)` of `LFunction_norm_logDeriv_sub_sum' χ hχ hq t₀`. -/
theorem LFunction_zero_count_near_one_at_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2 ≤ q → ∀ (t₀ : ℝ) {r : ℝ}, 0 < r → r < 1 / 2 →
        ((∑ᶠ u, divisor (LFunction χ) (closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) u : ℤ) : ℝ)
          ≤ C * (1 + r * Real.log ((q : ℝ) + |t₀| + 2)) := by
  refine ⟨7200, by norm_num, ?_⟩
  intro q hNe χ hχ hq2 t₀ r hr0 hr
  classical
  have hne1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq2
  obtain ⟨Z, m, h, hmemZ, hana_h, hne_h, hEqOn, hident, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' χ hχ hq2 t₀
  set c : ℂ := 2 + (t₀ : ℂ) * I with hcdef
  set σ : ℂ := (1 : ℂ) + (r : ℂ) + (t₀ : ℂ) * I with hσdef
  have hσre : σ.re = 1 + r := by rw [hσdef]; simp
  set V : Set ℂ := closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r with hVdef
  -- geometry: the count-ball sits inside the frozen disk at the same height
  have hcnorm : ‖((1 : ℂ) + (t₀ : ℂ) * I) - c‖ = 1 := by
    rw [hcdef, show (1 : ℂ) + (t₀ : ℂ) * I - (2 + (t₀ : ℂ) * I) = -1 by ring, norm_neg, norm_one]
  have hsub : V ⊆ ball c (3 / 2) := by
    intro z hz
    rw [hVdef, mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖z - c‖ ≤ ‖z - ((1 : ℂ) + (t₀ : ℂ) * I)‖ + ‖((1 : ℂ) + (t₀ : ℂ) * I) - c‖ := by
      have hadd := norm_add_le (z - ((1 : ℂ) + (t₀ : ℂ) * I)) (((1 : ℂ) + (t₀ : ℂ) * I) - c)
      rwa [show z - ((1 : ℂ) + (t₀ : ℂ) * I) + (((1 : ℂ) + (t₀ : ℂ) * I) - c) = z - c by ring]
        at hadd
    rw [hcnorm] at h1
    linarith
  -- `L` analytic on the count-ball
  have hanaV : AnalyticOnNhd ℂ (LFunction χ) V :=
    ((differentiable_LFunction hne1).differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ _)
  -- zeros of `L` have `Re < 1`
  have hzero_re : ∀ ρ ∈ Z, ρ.re < 1 := by
    intro ρ hρ
    by_contra hcn
    exact (LFunction_ne_zero_of_one_le_re χ (Or.inl hne1) (not_lt.mp hcn)) (hmemZ ρ hρ).2
  -- the filtered zero set
  set Zr : Finset ℂ := Z.filter (fun ρ => ρ ∈ V) with hZrdef
  -- === the divisor bridge: finsum = filtered finset sum of multiplicities ===
  have hdiv_eq : ∀ ρ ∈ Zr, divisor (LFunction χ) V ρ = (m ρ : ℤ) := by
    intro ρ hρ
    rw [hZrdef, Finset.mem_filter] at hρ
    obtain ⟨hρZ, hρV⟩ := hρ
    have horder := analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρZ (hmemZ ρ hρZ).1
    rw [hanaV.divisor_apply hρV, horder]; simp
  have hsupp : Function.support (fun u => divisor (LFunction χ) V u) ⊆ ↑Zr := by
    intro u hu
    rw [Function.mem_support] at hu
    have huV : u ∈ V := by
      by_contra hnV
      exact hu (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnV)
    have hLu : LFunction χ u = 0 := by
      by_contra hne0
      apply hu
      rw [hanaV.divisor_apply huV, (hanaV u huV).analyticOrderAt_eq_zero.mpr hne0]; simp
    have huball : u ∈ ball c (3 / 2) := hsub huV
    have huZ : u ∈ Z := by
      by_contra hnZ
      have heqv : LFunction χ u = (∏ ρ ∈ Z, (u - ρ) ^ (m ρ)) * h u := hEqOn huball
      rw [heqv] at hLu
      exact (mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr (by rintro rfl; exact hnZ hρ)))
        (hne_h u huball)) hLu
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨huZ, huV⟩)
  have hZr_val : (((∑ᶠ u, divisor (LFunction χ) V u : ℤ)) : ℝ) = ∑ ρ ∈ Zr, (m ρ : ℝ) := by
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ; rw [hdiv_eq ρ hρ]; push_cast; ring
  -- === the analytic Landau bound (staged) ===
  have hTbound : ∑ ρ ∈ Zr, (m ρ : ℝ)
      ≤ 5 * r * (120 * Real.log (4 *
          (5 * (4 + |t₀|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))) + 5 + 5 * r := by
    set Blit : ℝ := 120 * Real.log (4 *
      (5 * (4 + |t₀|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) with hBlit
    -- the numeric at `σ = 1 + r + t₀·I`
    have hσC : (1 : ℝ) < σ.re := by rw [hσre]; linarith
    have hL_ne : LFunction χ σ ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl hne1) (le_of_lt hσC)
    have hscnorm : ‖σ - c‖ ≤ 23 / 20 := by
      rw [hσdef, hcdef]
      have hsub2 : (1 : ℂ) + (r : ℂ) + (t₀ : ℂ) * I - (2 + (t₀ : ℂ) * I) = ((r - 1 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsub2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : r - 1 ≤ 0)]
      linarith
    have hbnd := hnum σ hscnorm hL_ne
    have hre := neg_re_logDeriv_le hbnd
    -- the Landau lower bound on `Re(−L'/L(σ))`, now at height
    have hlandau := landau_neg_logDeriv_re_lower_of_re χ (s := σ)
      (by rw [hσre]; linarith) (by rw [hσre]; linarith)
    rw [hσre, show (1 + r - 1 : ℝ) = r by ring] at hlandau
    -- combine: `S ≤ Blit + 1/r + 1`
    have hS : (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) ≤ Blit + 1 / r + 1 := by
      linarith [hre, hlandau]
    -- positivity of every partial-fraction term
    have hpos : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / (σ - ρ)).re := by
      intro ρ hρ
      refine mul_nonneg (by positivity) ?_
      rw [one_div, Complex.inv_re]
      refine div_nonneg ?_ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hσre]
      linarith [hzero_re ρ hρ, hr0]
    -- keep the near-`1 + it₀` terms, lower-bound each by `1/(5r)`
    have hTle : ∑ ρ ∈ Zr, (m ρ : ℝ) ≤ 5 * r * (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
      · intro ρ hρ
        rw [hZrdef, Finset.mem_filter] at hρ
        obtain ⟨hρZ, hρV⟩ := hρ
        have hlow := re_one_div_sub_ge_at_height hr0 hρV (le_of_lt (hzero_re ρ hρZ))
        rw [← hσdef] at hlow
        have h1le : (1 : ℝ) ≤ 5 * r * (1 / (σ - ρ)).re := by
          have hstep := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 5 * r)
          rwa [mul_one_div, div_self (by positivity : (5 : ℝ) * r ≠ 0)] at hstep
        calc (m ρ : ℝ) = (m ρ : ℝ) * 1 := (mul_one _).symm
          _ ≤ (m ρ : ℝ) * (5 * r * (1 / (σ - ρ)).re) :=
              mul_le_mul_of_nonneg_left h1le (by positivity)
          _ = 5 * r * ((m ρ : ℝ) * (1 / (σ - ρ)).re) := by ring
      · intro ρ hρZ _
        exact mul_nonneg (by positivity) (hpos ρ hρZ)
    -- assemble
    have hrinv : r * (1 / r) = 1 := by rw [mul_one_div, div_self hr0.ne']
    calc ∑ ρ ∈ Zr, (m ρ : ℝ)
        ≤ 5 * r * (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (σ - ρ)).re) := hTle
      _ ≤ 5 * r * (Blit + 1 / r + 1) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 5 * r * Blit + 5 + 5 * r := by linear_combination 5 * hrinv
  -- === constant collapse at height ===
  set B : ℝ := 120 * Real.log (4 *
      (5 * (4 + |t₀|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) with hBdef
  have habs0 : (0 : ℝ) ≤ |t₀| := abs_nonneg t₀
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq : 0 ≤ Real.log ((q : ℝ) + |t₀| + 2) := Real.log_nonneg (by linarith)
  have hBcollapse : B ≤ 720 * Real.log ((q : ℝ) * (|t₀| + 2)) := by
    have hlfm := log_four_M0_le (f := q) (q := q) (t := t₀) (γ := t₀)
      hq2 le_rfl hq2 (by linarith)
    rw [hBdef]
    linarith [hlfm]
  have hlog2q : Real.log ((q : ℝ) * (|t₀| + 2)) ≤ 2 * Real.log ((q : ℝ) + |t₀| + 2) := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
    have hqa : (q : ℝ) * (|t₀| + 2) ≤ ((q : ℝ) + |t₀| + 2) ^ 2 := by
      nlinarith [habs0, hq2R, hq0, mul_nonneg hq0 habs0, sq_nonneg ((q : ℝ) + |t₀|)]
    calc Real.log ((q : ℝ) * (|t₀| + 2))
        ≤ Real.log (((q : ℝ) + |t₀| + 2) ^ 2) :=
          Real.log_le_log (by nlinarith [habs0, hq2R]) hqa
      _ = 2 * Real.log ((q : ℝ) + |t₀| + 2) := by
          rw [Real.log_pow]; push_cast; ring
  calc (((∑ᶠ u, divisor (LFunction χ) V u : ℤ)) : ℝ)
      = ∑ ρ ∈ Zr, (m ρ : ℝ) := hZr_val
    _ ≤ 5 * r * B + 5 + 5 * r := hTbound
    _ ≤ 7200 * (1 + r * Real.log ((q : ℝ) + |t₀| + 2)) := by
        have hB2 : B ≤ 1440 * Real.log ((q : ℝ) + |t₀| + 2) := by
          linarith [hBcollapse, hlog2q]
        have hrpos : 0 ≤ r := le_of_lt hr0
        nlinarith [mul_le_mul_of_nonneg_left hB2 (by positivity : (0 : ℝ) ≤ 5 * r),
          hlogq, hr, hr0, mul_nonneg hrpos hlogq]

/-- **The guarded (density) form at height.** In the regime `r ≥ 1/log(q + |t₀| + 2)` the
`1 +` is absorbed: `≤ C·r·log(q + |t₀| + 2)`. Immediate from the height count, as
`LFunction_zero_count_near_one_guarded` is from `:98`. -/
theorem LFunction_zero_count_near_one_at_height_guarded :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2 ≤ q → ∀ (t₀ : ℝ) {r : ℝ}, 0 < r → r < 1 / 2 →
        1 / Real.log ((q : ℝ) + |t₀| + 2) ≤ r →
        ((∑ᶠ u, divisor (LFunction χ) (closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) u : ℤ) : ℝ)
          ≤ C * (r * Real.log ((q : ℝ) + |t₀| + 2)) := by
  obtain ⟨C, hC, hmain⟩ := LFunction_zero_count_near_one_at_height
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hNe χ hχ hq2 t₀ r hr0 hr hrge
  have hlogpos : 0 < Real.log ((q : ℝ) + |t₀| + 2) := by
    apply Real.log_pos
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith [abs_nonneg t₀]
  have h1 : (1 : ℝ) ≤ r * Real.log ((q : ℝ) + |t₀| + 2) := (div_le_iff₀ hlogpos).mp hrge
  calc ((∑ᶠ u, divisor (LFunction χ) (closedBall ((1 : ℂ) + (t₀ : ℂ) * I) r) u : ℤ) : ℝ)
      ≤ C * (1 + r * Real.log ((q : ℝ) + |t₀| + 2)) := hmain χ hχ hq2 t₀ hr0 hr
    _ ≤ 2 * C * (r * Real.log ((q : ℝ) + |t₀| + 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hC)]

/-- **The W1 exit row** (design v2 §4, W1): at `t₀ = 0` the height form IS the statement of
`LFunction_zero_count_near_one` (`(0 : ℝ)·I = 0`, `|0| = 0`). It INVOKES the frozen row. The
centre is transported by `rw`, not `simp`: the divisor's TYPE depends on the ball, so a
subterm rewrite has no type-correct motive while `rw`'s whole-goal abstraction does. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2 ≤ q → ∀ {r : ℝ}, 0 < r → r < 1 / 2 →
        ((∑ᶠ u, divisor (LFunction χ) (closedBall (1 : ℂ) r) u : ℤ) : ℝ)
          ≤ C * (1 + r * Real.log ((q : ℝ) + 2)) := by
  obtain ⟨C, hC, h⟩ := LFunction_zero_count_near_one_at_height
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ hq r hr0 hr
  have h0 := h χ hχ hq 0 hr0 hr
  have e : ((1 : ℂ) + ((0 : ℝ) : ℂ) * I) = 1 := by simp
  have e' : ((q : ℝ) + |(0 : ℝ)| + 2) = (q : ℝ) + 2 := by simp
  first
    | (rw [e', e] at h0; exact h0)
    | (convert h0 <;> simp)

end Salt.SW
