/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The twin-bar rung (`twinbar`) — carriers + trivia (node T1)

Design: `docs/blueprints/twinbar.md`, node T1. This module lands the four
Fable-frozen carriers of the Maynard–Selberg variational functional at `k = 2`
(the twin tuple `{0, 2}`), together with the elementary side-conditions that the
downstream analytic nodes (T2–T5) consume: nonnegativity of the quadratic
carriers, the two weights `w₁`, `w₂` with `w₁ + w₂ ≡ 2`, and the
`ContinuousOn`-to-`IntervalIntegrable` slice plumbing.

**Honesty contract (compressed; full text in the blueprint).** The rung will
certify that the UNMODIFIED Maynard–Selberg gate is unsatisfiable for the twin
tuple at every level of distribution — a NEGATIVE result about a specific sieve
functional over continuous weights. It does NOT claim "sieves cannot prove twin
primes": parity-breaking (type-II / bilinear) inputs modify the functional and
lie outside this bound. See `Salt.TwinBar.All` for the full statement.

## Carriers (Fable-frozen; nested-1D formulation matching corpus idioms)

Matching Polymath8b eq. (31)–(33) at `k = 2`. The regularity hypothesis for the
downstream theorems is `ContinuousOn (Function.uncurry F) R₂`; `F` outside `R₂`
never enters any carrier because every integration range sits inside the simplex
slice.
-/

namespace Salt.TwinBar

open MeasureTheory Set

/-- `I₂ F = ∬_{R₂} F²`, in nested-1D form: `∫₀¹ (∫₀^{1−t₂} (F t₁ t₂)²) dt₂`.
The `L²`-mass carrier (Polymath8b eq. 33 at `k = 2`). -/
noncomputable def I₂ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2

/-- `J₁ F = ∫₀¹ (∫₀^{1−t₂} F dt₁)² dt₂` — the first `contractAt` peel (eq. 31). -/
noncomputable def J₁ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..1, (∫ t₁ in (0:ℝ)..(1 - t₂), F t₁ t₂) ^ 2

/-- `J₂ F = ∫₀¹ (∫₀^{1−t₁} F dt₂)² dt₁` — the symmetric peel (eq. 32). -/
noncomputable def J₂ (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..1, (∫ t₂ in (0:ℝ)..(1 - t₁), F t₁ t₂) ^ 2

/-- The closed simplex `R₂ = {(t₁,t₂) | 0 ≤ t₁, 0 ≤ t₂, t₁ + t₂ ≤ 1}`. Every
carrier's integration range is a slice of `R₂`. -/
def R₂ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-! ## Nonnegativity of the quadratic carriers (H2/H3 trivia) -/

/-- `0 ≤ I₂ F`. The inner integrand `(F t₁ t₂)²` is nonneg, and on the outer
domain `t₂ ∈ [0,1]` the inner range `0..(1−t₂)` is correctly oriented
(`0 ≤ 1 − t₂`), so both `integral_nonneg` applications go through. No
integrability side-condition is needed. -/
theorem I₂_nonneg (F : ℝ → ℝ → ℝ) : 0 ≤ I₂ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₂ ht₂
  apply intervalIntegral.integral_nonneg (by have := ht₂.2; linarith : (0:ℝ) ≤ 1 - t₂)
  intro t₁ _
  positivity

/-- `0 ≤ J₁ F`. The outer integrand is a square. -/
theorem J₁_nonneg (F : ℝ → ℝ → ℝ) : 0 ≤ J₁ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₂ _
  positivity

/-- `0 ≤ J₂ F`. The outer integrand is a square. -/
theorem J₂_nonneg (F : ℝ → ℝ → ℝ) : 0 ≤ J₂ F := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro t₁ _
  positivity

/-! ## The Cauchy–Schwarz weights `w₁`, `w₂`

`w₁ (t₁,t₂) := 1 − t₂ + t₁`, `w₂ := 1 − t₁ + t₂`. On `R₂` both lie in `[0,2]` and
`w₁ + w₂ ≡ 2` — the pointwise identity driving the T5 combine. -/

/-- The first Cauchy–Schwarz weight `w₁ (t₁,t₂) = 1 − t₂ + t₁`. -/
def w₁ (t₁ t₂ : ℝ) : ℝ := 1 - t₂ + t₁

/-- The second Cauchy–Schwarz weight `w₂ (t₁,t₂) = 1 − t₁ + t₂`. -/
def w₂ (t₁ t₂ : ℝ) : ℝ := 1 - t₁ + t₂

/-- **The magic identity.** `w₁ + w₂ ≡ 2` pointwise. -/
theorem w₁_add_w₂ (t₁ t₂ : ℝ) : w₁ t₁ t₂ + w₂ t₁ t₂ = 2 := by
  unfold w₁ w₂; ring

/-- `0 ≤ w₁` when `0 ≤ t₁` and `t₂ ≤ 1` (the J₁-slice range). -/
theorem w₁_nonneg {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h2 : t₂ ≤ 1) : 0 ≤ w₁ t₁ t₂ := by
  unfold w₁; linarith

/-- `0 ≤ w₂` when `t₁ ≤ 1` and `0 ≤ t₂` (the J₂-slice range). -/
theorem w₂_nonneg {t₁ t₂ : ℝ} (h1 : t₁ ≤ 1) (h2 : 0 ≤ t₂) : 0 ≤ w₂ t₁ t₂ := by
  unfold w₂; linarith

/-- `w₁ ≤ 2` on a J₁-slice: `0 ≤ t₂` and `t₁ ≤ 1 − t₂`. -/
theorem w₁_le_two {t₁ t₂ : ℝ} (h0 : 0 ≤ t₂) (h : t₁ ≤ 1 - t₂) : w₁ t₁ t₂ ≤ 2 := by
  unfold w₁; linarith

/-- `w₂ ≤ 2` on a J₂-slice: `0 ≤ t₁` and `t₂ ≤ 1 − t₁`. -/
theorem w₂_le_two {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h : t₂ ≤ 1 - t₁) : w₂ t₁ t₂ ≤ 2 := by
  unfold w₂; linarith

/-- `w₁` is jointly continuous (the 2-D form, for the T4 `lintegral` step). -/
theorem w₁_continuous : Continuous (Function.uncurry w₁) := by
  have h : Function.uncurry w₁ = fun p : ℝ × ℝ => 1 - p.2 + p.1 := by
    funext p; rfl
  rw [h]; fun_prop

/-- `w₂` is jointly continuous (the 2-D form, for the T4 `lintegral` step). -/
theorem w₂_continuous : Continuous (Function.uncurry w₂) := by
  have h : Function.uncurry w₂ = fun p : ℝ × ℝ => 1 - p.1 + p.2 := by
    funext p; rfl
  rw [h]; fun_prop

/-- The J₁-slice `t₁ ↦ w₁ t₁ t₂` (t₂ fixed) is continuous. Feed as the weight to
`slice₁_weight_sq_intervalIntegrable`. -/
theorem w₁_slice_continuous (t₂ : ℝ) : Continuous (fun t₁ => w₁ t₁ t₂) := by
  unfold w₁; fun_prop

/-- The J₂-slice `t₂ ↦ w₂ t₁ t₂` (t₁ fixed) is continuous. Feed as the weight to
`slice₂_weight_sq_intervalIntegrable`. -/
theorem w₂_slice_continuous (t₁ : ℝ) : Continuous (fun t₂ => w₂ t₁ t₂) := by
  unfold w₂; fun_prop

/-! ## Slice continuity and integrability from `ContinuousOn (uncurry F) R₂`

The J₁/I₂ inner integral fixes `t₂` and runs `t₁ ∈ [0, 1−t₂]` (`slice₁_*`); the
J₂ inner integral fixes `t₁` and runs `t₂ ∈ [0, 1−t₁]` (`slice₂_*`). For each
direction we provide the four shapes T3/T4 consume: slice continuity, plain slice
integrability, square-slice integrability, and `w·F²`-slice integrability for a
continuous weight `w`. -/

/-- **J₁-slice continuity.** For `t₂ ∈ [0,1]`, the slice `t₁ ↦ F t₁ t₂` is
`ContinuousOn (Set.Icc 0 (1 − t₂))`, because `t₁ ↦ (t₁, t₂)` maps that interval
into `R₂` (`t₁ ≤ 1 − t₂ ⇒ t₁ + t₂ ≤ 1`) and `F` is continuous on `R₂`. -/
theorem slice₁_continuousOn {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₂ : ℝ} (h0 : 0 ≤ t₂) (_h1 : t₂ ≤ 1) :
    ContinuousOn (fun t₁ => F t₁ t₂) (Set.Icc 0 (1 - t₂)) := by
  have hmap : Set.MapsTo (fun t₁ : ℝ => (t₁, t₂)) (Set.Icc 0 (1 - t₂)) R₂ := by
    intro t₁ ht₁
    exact ⟨ht₁.1, h0, by have := ht₁.2; linarith⟩
  have hcont : Continuous (fun t₁ : ℝ => (t₁, t₂)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- **J₂-slice continuity.** For `t₁ ∈ [0,1]`, the slice `t₂ ↦ F t₁ t₂` is
`ContinuousOn (Set.Icc 0 (1 − t₁))`. -/
theorem slice₂_continuousOn {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₁ : ℝ} (h0 : 0 ≤ t₁) (_h1 : t₁ ≤ 1) :
    ContinuousOn (fun t₂ => F t₁ t₂) (Set.Icc 0 (1 - t₁)) := by
  have hmap : Set.MapsTo (fun t₂ : ℝ => (t₁, t₂)) (Set.Icc 0 (1 - t₁)) R₂ := by
    intro t₂ ht₂
    exact ⟨h0, ht₂.1, by have := ht₂.2; linarith⟩
  have hcont : Continuous (fun t₂ : ℝ => (t₁, t₂)) := by fun_prop
  exact hF.comp hcont.continuousOn hmap

/-- **J₁-slice integrability.** `t₁ ↦ F t₁ t₂` is `IntervalIntegrable` on
`0..(1 − t₂)`. -/
theorem slice₁_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₂ : ℝ} (h0 : 0 ≤ t₂) (h1 : t₂ ≤ 1) :
    IntervalIntegrable (fun t₁ => F t₁ t₂) volume 0 (1 - t₂) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₂)]
  exact slice₁_continuousOn hF h0 h1

/-- **J₂-slice integrability.** `t₂ ↦ F t₁ t₂` is `IntervalIntegrable` on
`0..(1 − t₁)`. -/
theorem slice₂_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₁ : ℝ} (h0 : 0 ≤ t₁) (h1 : t₁ ≤ 1) :
    IntervalIntegrable (fun t₂ => F t₁ t₂) volume 0 (1 - t₁) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]
  exact slice₂_continuousOn hF h0 h1

/-- **J₁ square-slice integrability.** `t₁ ↦ (F t₁ t₂)²` on `0..(1 − t₂)` — the
`I₂` inner integrand. -/
theorem slice₁_sq_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₂ : ℝ} (h0 : 0 ≤ t₂) (h1 : t₂ ≤ 1) :
    IntervalIntegrable (fun t₁ => (F t₁ t₂) ^ 2) volume 0 (1 - t₂) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₂)]
  exact (slice₁_continuousOn hF h0 h1).pow 2

/-- **J₂ square-slice integrability.** `t₂ ↦ (F t₁ t₂)²` on `0..(1 − t₁)`. -/
theorem slice₂_sq_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₁ : ℝ} (h0 : 0 ≤ t₁) (h1 : t₁ ≤ 1) :
    IntervalIntegrable (fun t₂ => (F t₁ t₂) ^ 2) volume 0 (1 - t₁) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]
  exact (slice₂_continuousOn hF h0 h1).pow 2

/-- **J₁ weighted-square-slice integrability.** For any continuous `w : ℝ → ℝ`,
`t₁ ↦ w t₁ · (F t₁ t₂)²` is integrable on `0..(1 − t₂)`. Instantiate `w` with
`fun t₁ => w₁ t₁ t₂` (`w₁_slice_continuous`) for the T3 Cauchy–Schwarz RHS. -/
theorem slice₁_weight_sq_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₂ : ℝ} (h0 : 0 ≤ t₂) (h1 : t₂ ≤ 1)
    {w : ℝ → ℝ} (hw : Continuous w) :
    IntervalIntegrable (fun t₁ => w t₁ * (F t₁ t₂) ^ 2) volume 0 (1 - t₂) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₂)]
  exact hw.continuousOn.mul ((slice₁_continuousOn hF h0 h1).pow 2)

/-- **J₂ weighted-square-slice integrability.** For any continuous `w : ℝ → ℝ`,
`t₂ ↦ w t₂ · (F t₁ t₂)²` is integrable on `0..(1 − t₁)`. Instantiate `w` with
`fun t₂ => w₂ t₁ t₂` (`w₂_slice_continuous`). -/
theorem slice₂_weight_sq_intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) R₂) {t₁ : ℝ} (h0 : 0 ≤ t₁) (h1 : t₁ ≤ 1)
    {w : ℝ → ℝ} (hw : Continuous w) :
    IntervalIntegrable (fun t₂ => w t₂ * (F t₁ t₂) ^ 2) volume 0 (1 - t₁) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]
  exact hw.continuousOn.mul ((slice₂_continuousOn hF h0 h1).pow 2)

end Salt.TwinBar
