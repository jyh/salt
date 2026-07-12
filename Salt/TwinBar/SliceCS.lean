/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Defs
import Salt.TwinBar.LogWeight

/-!
# T3 — the per-slice Cauchy–Schwarz bound

Design: `docs/blueprints/twinbar.md`, node `T3` and proof-chain step (ii). Per
`t₂`-slice with `a := 1 − t₂ ≥ 0`,

  `(∫₀^a F)² ≤ (∫₀^a (a + t)⁻¹) · (∫₀^a (a + t)·F²) = log 2 · ∫₀^a w₁·F²`,

and the mirror in the `t₁` direction with weight `w₂`. The Maynard weights are
SIGNED (`Fstar` has negative coefficients), so the nonnegative-`Lᵖ`/`Lᵍ` route
does not apply raw; instead we land the sign-agnostic two-function interval
Cauchy–Schwarz `interval_CS` once, via the quadratic-discriminant trick
(`0 ≤ ∫ (λ·f + g)²` for all `λ` ⇒ nonpositive discriminant), and instantiate it
with `f := √((a+t)⁻¹)`, `g := √(a+t)·F` so that `f·g = F`, `f² = (a+t)⁻¹`,
`g² = w₁·F²`. The normalization `∫₀^a (a+t)⁻¹ = log 2` is `logWeight` (node T2).

`interval_CS` is landed PUBLIC (kernel-visibility doctrine): it is a clean,
self-contained interval Cauchy–Schwarz that downstream rungs can reuse.
-/

namespace Salt.TwinBar

open MeasureTheory Set

/-- **Two-function interval Cauchy–Schwarz.** For real `f`, `g` on `a..b`
(`a ≤ b`) with `f²`, `g²`, `f·g` interval-integrable,
`(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. Sign-agnostic (no nonnegativity on `f`, `g`),
proved by the quadratic-discriminant trick: `0 ≤ ∫ (λ·f + g)²` expands to a
nonnegative quadratic in `λ`, whose discriminant `4(∫ f·g)² − 4(∫ f²)(∫ g²)` is
therefore `≤ 0`. -/
theorem interval_CS {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a b)
    (hg2 : IntervalIntegrable (fun x => (g x) ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume a b) :
    (∫ x in a..b, f x * g x) ^ 2
      ≤ (∫ x in a..b, (f x) ^ 2) * (∫ x in a..b, (g x) ^ 2) := by
  -- The quadratic `λ ↦ (∫ f²)·λ² + (2 ∫ f·g)·λ + (∫ g²)` is nonnegative.
  have key : ∀ lam : ℝ, 0 ≤ (∫ x in a..b, (f x) ^ 2) * (lam * lam)
      + (2 * ∫ x in a..b, f x * g x) * lam + (∫ x in a..b, (g x) ^ 2) := by
    intro lam
    have hnn : 0 ≤ ∫ x in a..b, (lam * f x + g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : (∫ x in a..b, (lam * f x + g x) ^ 2)
        = (∫ x in a..b, (f x) ^ 2) * (lam * lam)
          + (2 * ∫ x in a..b, f x * g x) * lam + (∫ x in a..b, (g x) ^ 2) := by
      have hfun : (fun x => (lam * f x + g x) ^ 2)
          = (fun x => ((lam * lam) * (f x) ^ 2 + (2 * lam) * (f x * g x)) + (g x) ^ 2) := by
        funext x; ring
      rw [hfun,
        intervalIntegral.integral_add
          ((hf2.const_mul (lam * lam)).add (hfg.const_mul (2 * lam))) hg2,
        intervalIntegral.integral_add (hf2.const_mul (lam * lam)) (hfg.const_mul (2 * lam)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [hexp] at hnn
    exact hnn
  have hdisc := discrim_le_zero key
  simp only [discrim] at hdisc
  nlinarith [hdisc]

/-- **T3, the `J₁` direction.** Per `t₂`-slice (`a := 1 − t₂`):
`(∫₀^a F)² ≤ log 2 · ∫₀^a w₁·F²`. The `a = 0` slice (`t₂ = 1`) is `0 ≤ 0`; for
`a > 0` this is `interval_CS` with `f := √((a+t)⁻¹)`, `g := √(a+t)·F`, whose
`∫ f²` is `logWeight`. -/
theorem sliceCS₁ (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂)
    {t₂ : ℝ} (h0 : 0 ≤ t₂) (h1 : t₂ ≤ 1) :
    (∫ t₁ in (0:ℝ)..(1 - t₂), F t₁ t₂) ^ 2
      ≤ Real.log 2 * ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2 := by
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ 1 - t₂) with ha0 | ha
  · -- `a = 0`: both integrals collapse to `0`.
    rw [← ha0]; simp
  -- `a := 1 − t₂ > 0`. Strict positivity of `a + x` on both interval flavours
  -- (`x ≥ 0` on `uIcc`, `x > 0` on `uIoc`, and `a > 0` in either case).
  have hpos_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) (1 - t₂), 0 < 1 - t₂ + x := by
    intro x hx; rw [Set.uIcc_of_le ha.le] at hx; have := hx.1; linarith
  have hpos_uIoc : ∀ x ∈ Set.uIoc (0:ℝ) (1 - t₂), 0 < 1 - t₂ + x := by
    intro x hx; rw [Set.uIoc_of_le ha.le] at hx; have := hx.1; linarith
  -- Integrability of the reciprocal weight `(a + x)⁻¹`.
  have hinv_ii : IntervalIntegrable (fun x => (1 - t₂ + x)⁻¹) volume 0 (1 - t₂) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ha.le]
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by
      have : (0:ℝ) < 1 - t₂ + x := by have := hx.1; linarith
      exact this.ne')
  -- Integrability of the three `interval_CS` ingredients, via `.congr` from the
  -- "nice" forms `(a+x)⁻¹`, `w₁·F²`, `F`.
  have hf2ii : IntervalIntegrable (fun x => Real.sqrt ((1 - t₂ + x)⁻¹) ^ 2) volume 0 (1 - t₂) :=
    hinv_ii.congr (fun x hx =>
      (Real.sq_sqrt (inv_nonneg.mpr (hpos_uIoc x hx).le)).symm)
  have hg2ii : IntervalIntegrable
      (fun x => (Real.sqrt (1 - t₂ + x) * F x t₂) ^ 2) volume 0 (1 - t₂) :=
    (slice₁_weight_sq_intervalIntegrable hF h0 h1 (w₁_slice_continuous t₂)).congr (by
      intro x hx
      have : (Real.sqrt (1 - t₂ + x) * F x t₂) ^ 2 = w₁ x t₂ * (F x t₂) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIoc x hx).le]; simp only [w₁]
      exact this.symm)
  have hfgii : IntervalIntegrable
      (fun x => Real.sqrt ((1 - t₂ + x)⁻¹) * (Real.sqrt (1 - t₂ + x) * F x t₂))
      volume 0 (1 - t₂) :=
    (slice₁_intervalIntegrable hF h0 h1).congr (by
      intro x hx
      have hne : Real.sqrt (1 - t₂ + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIoc x hx)).ne'
      have : Real.sqrt ((1 - t₂ + x)⁻¹) * (Real.sqrt (1 - t₂ + x) * F x t₂) = F x t₂ := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this.symm)
  -- The value rewrites: `∫ f² = log 2`, `∫ g² = ∫ w₁·F²`, `∫ f·g = ∫ F`.
  have hf2val : (∫ x in (0:ℝ)..(1 - t₂), Real.sqrt ((1 - t₂ + x)⁻¹) ^ 2) = Real.log 2 := by
    rw [intervalIntegral.integral_congr
          (fun x hx => Real.sq_sqrt (inv_nonneg.mpr (hpos_uIcc x hx).le))]
    exact logWeight ha
  have hg2val : (∫ x in (0:ℝ)..(1 - t₂), (Real.sqrt (1 - t₂ + x) * F x t₂) ^ 2)
      = ∫ x in (0:ℝ)..(1 - t₂), w₁ x t₂ * (F x t₂) ^ 2 :=
    intervalIntegral.integral_congr (by
      intro x hx
      have : (Real.sqrt (1 - t₂ + x) * F x t₂) ^ 2 = w₁ x t₂ * (F x t₂) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIcc x hx).le]; simp only [w₁]
      exact this)
  have hfgval : (∫ x in (0:ℝ)..(1 - t₂),
        Real.sqrt ((1 - t₂ + x)⁻¹) * (Real.sqrt (1 - t₂ + x) * F x t₂))
      = ∫ x in (0:ℝ)..(1 - t₂), F x t₂ :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hne : Real.sqrt (1 - t₂ + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIcc x hx)).ne'
      have : Real.sqrt ((1 - t₂ + x)⁻¹) * (Real.sqrt (1 - t₂ + x) * F x t₂) = F x t₂ := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this)
  -- Assemble via `interval_CS`.
  have hCS : (∫ x in (0:ℝ)..(1 - t₂),
        Real.sqrt ((1 - t₂ + x)⁻¹) * (Real.sqrt (1 - t₂ + x) * F x t₂)) ^ 2
      ≤ (∫ x in (0:ℝ)..(1 - t₂), Real.sqrt ((1 - t₂ + x)⁻¹) ^ 2)
        * (∫ x in (0:ℝ)..(1 - t₂), (Real.sqrt (1 - t₂ + x) * F x t₂) ^ 2) :=
    interval_CS (f := fun t => Real.sqrt ((1 - t₂ + t)⁻¹))
      (g := fun t => Real.sqrt (1 - t₂ + t) * F t t₂) ha.le hf2ii hg2ii hfgii
  rw [hfgval, hf2val, hg2val] at hCS
  exact hCS

/-- **T3, the `J₂` direction (mirror).** Per `t₁`-slice (`a := 1 − t₁`):
`(∫₀^a F)² ≤ log 2 · ∫₀^a w₂·F²`. The `t₂` integration variable carries the
weight `w₂ = 1 − t₁ + t₂ = a + t₂`. -/
theorem sliceCS₂ (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂)
    {t₁ : ℝ} (h0 : 0 ≤ t₁) (h1 : t₁ ≤ 1) :
    (∫ t₂ in (0:ℝ)..(1 - t₁), F t₁ t₂) ^ 2
      ≤ Real.log 2 * ∫ t₂ in (0:ℝ)..(1 - t₁), w₂ t₁ t₂ * (F t₁ t₂) ^ 2 := by
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ 1 - t₁) with ha0 | ha
  · rw [← ha0]; simp
  have hpos_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) (1 - t₁), 0 < 1 - t₁ + x := by
    intro x hx; rw [Set.uIcc_of_le ha.le] at hx; have := hx.1; linarith
  have hpos_uIoc : ∀ x ∈ Set.uIoc (0:ℝ) (1 - t₁), 0 < 1 - t₁ + x := by
    intro x hx; rw [Set.uIoc_of_le ha.le] at hx; have := hx.1; linarith
  have hinv_ii : IntervalIntegrable (fun x => (1 - t₁ + x)⁻¹) volume 0 (1 - t₁) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ha.le]
    exact ContinuousOn.inv₀ (by fun_prop) (fun x hx => by
      have : (0:ℝ) < 1 - t₁ + x := by have := hx.1; linarith
      exact this.ne')
  have hf2ii : IntervalIntegrable (fun x => Real.sqrt ((1 - t₁ + x)⁻¹) ^ 2) volume 0 (1 - t₁) :=
    hinv_ii.congr (fun x hx =>
      (Real.sq_sqrt (inv_nonneg.mpr (hpos_uIoc x hx).le)).symm)
  have hg2ii : IntervalIntegrable
      (fun x => (Real.sqrt (1 - t₁ + x) * F t₁ x) ^ 2) volume 0 (1 - t₁) :=
    (slice₂_weight_sq_intervalIntegrable hF h0 h1 (w₂_slice_continuous t₁)).congr (by
      intro x hx
      have : (Real.sqrt (1 - t₁ + x) * F t₁ x) ^ 2 = w₂ t₁ x * (F t₁ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIoc x hx).le]; simp only [w₂]
      exact this.symm)
  have hfgii : IntervalIntegrable
      (fun x => Real.sqrt ((1 - t₁ + x)⁻¹) * (Real.sqrt (1 - t₁ + x) * F t₁ x))
      volume 0 (1 - t₁) :=
    (slice₂_intervalIntegrable hF h0 h1).congr (by
      intro x hx
      have hne : Real.sqrt (1 - t₁ + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIoc x hx)).ne'
      have : Real.sqrt ((1 - t₁ + x)⁻¹) * (Real.sqrt (1 - t₁ + x) * F t₁ x) = F t₁ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this.symm)
  have hf2val : (∫ x in (0:ℝ)..(1 - t₁), Real.sqrt ((1 - t₁ + x)⁻¹) ^ 2) = Real.log 2 := by
    rw [intervalIntegral.integral_congr
          (fun x hx => Real.sq_sqrt (inv_nonneg.mpr (hpos_uIcc x hx).le))]
    exact logWeight ha
  have hg2val : (∫ x in (0:ℝ)..(1 - t₁), (Real.sqrt (1 - t₁ + x) * F t₁ x) ^ 2)
      = ∫ x in (0:ℝ)..(1 - t₁), w₂ t₁ x * (F t₁ x) ^ 2 :=
    intervalIntegral.integral_congr (by
      intro x hx
      have : (Real.sqrt (1 - t₁ + x) * F t₁ x) ^ 2 = w₂ t₁ x * (F t₁ x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (hpos_uIcc x hx).le]; simp only [w₂]
      exact this)
  have hfgval : (∫ x in (0:ℝ)..(1 - t₁),
        Real.sqrt ((1 - t₁ + x)⁻¹) * (Real.sqrt (1 - t₁ + x) * F t₁ x))
      = ∫ x in (0:ℝ)..(1 - t₁), F t₁ x :=
    intervalIntegral.integral_congr (by
      intro x hx
      have hne : Real.sqrt (1 - t₁ + x) ≠ 0 := (Real.sqrt_pos.mpr (hpos_uIcc x hx)).ne'
      have : Real.sqrt ((1 - t₁ + x)⁻¹) * (Real.sqrt (1 - t₁ + x) * F t₁ x) = F t₁ x := by
        rw [Real.sqrt_inv, inv_mul_cancel_left₀ hne]
      exact this)
  have hCS : (∫ x in (0:ℝ)..(1 - t₁),
        Real.sqrt ((1 - t₁ + x)⁻¹) * (Real.sqrt (1 - t₁ + x) * F t₁ x)) ^ 2
      ≤ (∫ x in (0:ℝ)..(1 - t₁), Real.sqrt ((1 - t₁ + x)⁻¹) ^ 2)
        * (∫ x in (0:ℝ)..(1 - t₁), (Real.sqrt (1 - t₁ + x) * F t₁ x) ^ 2) :=
    interval_CS (f := fun t => Real.sqrt ((1 - t₁ + t)⁻¹))
      (g := fun t => Real.sqrt (1 - t₁ + t) * F t₁ t) ha.le hf2ii hg2ii hfgii
  rw [hfgval, hf2val, hg2val] at hCS
  exact hCS

end Salt.TwinBar
