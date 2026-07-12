/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.Defs

/-!
# The twin-bar rung (`twinbar`) — the simplex Tonelli swap (node T4)

Design: `docs/blueprints/twinbar.md`, node T4 (proof-chain step (iv)). This is the
one genuinely 2-D step of the rung: the corpus has no prior 2-D integration, so
this module is greenfield over mathlib's `MeasureTheory.Measure.Prod` /
`Integral.Prod` Fubini API.

The deliverable is the iterated-order swap over the closed simplex `R₂`, for a
continuous nonnegative integrand:

```
∫ t₂ in 0..1, ∫ t₁ in 0..(1 - t₂), G t₁ t₂ = ∫ t₁ in 0..1, ∫ t₂ in 0..(1 - t₁), G t₁ t₂
```

T5 instantiates this at `G = w₂ · F²` (continuous as a product of continuous
functions, nonnegative on `R₂` by `w₂_nonneg` and a square) to convert the
`J₂`-order region bound into the `J₁` order, so that `w₁F² + w₂F² = 2F²` can be
combined under one iterated integral.

**Route (Bochner Fubini, not the ℝ≥0∞ lever).** Both frames were assessed. The
`lintegral`-first route swaps side-condition-free but pays a round-trip through
`ℝ≥0∞` (an `ofReal`/`toReal` descent on both ends that itself needs
integrability). The Bochner route via `integral_prod` / `integral_prod_symm`
threads the swap through the single 2-D integral `∫_{ℝ²} R₂.indicator (uncurry G)`
and needs exactly one side fact: joint integrability of that indicator-extended
`G`. On the *compact* simplex `R₂` a `ContinuousOn` integrand is integrable
(`ContinuousOn.integrableOn_compact'`), and `integrable_indicator_iff` turns that
into integrability of the extension over all of `ℝ²`. This is strictly less
plumbing than the `ℝ≥0∞` descent, so it is the route taken; nonnegativity of `G`
is therefore not consumed (kept in the signature for the T5 interface).

**Boundary bookkeeping.** The integrand extension is `R₂.indicator (uncurry G)`,
using the *closed* simplex `R₂` (already compact — good for integrability). Each
inner interval integral `∫ t₁ in 0..(1 - t₂)` with `t₂ ∈ [0,1]` is recovered from
the plane slice by `indicator_comp_right` (the slice's `R₂`-preimage is
`Icc 0 (1 - t₂)`) followed by `integral_indicator`, `integral_Icc_eq_integral_Ioc`
(the `{0}` boundary is null), and the `Ioc` interval-integral convention. Off
`[0,1]` the slice preimage is empty, so the marginal vanishes and the outer
`∫_ℝ` collapses onto `Icc 0 1` via `setIntegral_eq_integral_of_forall_compl_eq_zero`.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-- The closed simplex `R₂` is closed: an intersection of three closed half-spaces. -/
private theorem R₂_isClosed : IsClosed R₂ := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  exact isClosed_le (continuous_fst.add continuous_snd) continuous_const

/-- The closed simplex `R₂` is compact: closed and contained in `Icc (0,0) (1,1)`. -/
private theorem R₂_isCompact : IsCompact R₂ := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := ((0:ℝ), (0:ℝ))) (b := ((1:ℝ), (1:ℝ))))
    R₂_isClosed
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> simp <;> linarith

/-- The closed simplex `R₂` is measurable. -/
private theorem R₂_measurableSet : MeasurableSet R₂ := R₂_isClosed.measurableSet

/-- **The simplex Tonelli swap** (node T4). For a jointly continuous integrand on
the closed simplex `R₂`, the two iterated (nested-1D) integrals over `R₂` agree:

```
∫ t₂ in 0..1, ∫ t₁ in 0..(1 - t₂), G t₁ t₂ = ∫ t₁ in 0..1, ∫ t₂ in 0..(1 - t₁), G t₁ t₂.
```

Both orders equal the single 2-D integral of `R₂.indicator (uncurry G)` over
`volume.prod volume`, so the equality is `integral_prod_symm` and `integral_prod`
applied to that common middle term. No nonnegativity is needed — Fubini
requires only joint integrability, so the swap holds for every continuous G. -/
theorem simplex_swap (G : ℝ → ℝ → ℝ) (hG : ContinuousOn (Function.uncurry G) R₂) :
    ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), G t₁ t₂
      = ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), G t₁ t₂ := by
  -- The indicator-extended integrand on the plane, and its joint integrability.
  set H : ℝ × ℝ → ℝ := R₂.indicator (Function.uncurry G) with hH
  have hInt : Integrable H (volume.prod volume) := by
    rw [hH, integrable_indicator_iff R₂_measurableSet]
    exact ContinuousOn.integrableOn_compact' R₂_isCompact R₂_measurableSet hG
  -- Marginal in `t₁`: the plane slice is an `R₂`-preimage indicator.
  have hcol1 : ∀ t₂ : ℝ, (∫ t₁, H (t₁, t₂)) = ∫ t₁ in ((fun t₁ => (t₁, t₂)) ⁻¹' R₂), G t₁ t₂ := by
    intro t₂
    have hmeas : MeasurableSet ((fun t₁ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) :=
      R₂_measurableSet.preimage (by fun_prop)
    have hrw : (fun t₁ => H (t₁, t₂))
        = ((fun t₁ => (t₁, t₂)) ⁻¹' R₂).indicator (fun t₁ => G t₁ t₂) := by
      funext t₁
      rw [hH, ← Set.indicator_comp_right (fun t₁ => ((t₁ : ℝ), t₂))]
      rfl
    rw [hrw, integral_indicator hmeas]
  -- Marginal in `t₂`: the mirror.
  have hcol2 : ∀ t₁ : ℝ, (∫ t₂, H (t₁, t₂)) = ∫ t₂ in ((fun t₂ => (t₁, t₂)) ⁻¹' R₂), G t₁ t₂ := by
    intro t₁
    have hmeas : MeasurableSet ((fun t₂ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) :=
      R₂_measurableSet.preimage (by fun_prop)
    have hrw : (fun t₂ => H (t₁, t₂))
        = ((fun t₂ => (t₁, t₂)) ⁻¹' R₂).indicator (fun t₂ => G t₁ t₂) := by
      funext t₂
      rw [hH, ← Set.indicator_comp_right (fun t₂ => ((t₁ : ℝ), t₂))]
      rfl
    rw [hrw, integral_indicator hmeas]
  -- On `[0,1]` the slice preimage is the interval `Icc 0 (1 - ·)`.
  have hslice1 : ∀ t₂ ∈ Icc (0:ℝ) 1,
      (∫ t₁, H (t₁, t₂)) = ∫ t₁ in (0:ℝ)..(1 - t₂), G t₁ t₂ := by
    intro t₂ ht₂
    obtain ⟨h0, h1⟩ := ht₂
    have hpre : ((fun t₁ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = Icc 0 (1 - t₂) := by
      ext t₁
      simp only [mem_preimage, R₂, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨ha, _, hc⟩; exact ⟨ha, by linarith⟩
      · rintro ⟨ha, hb⟩; exact ⟨ha, h0, by linarith⟩
    rw [hcol1 t₂, hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₂)]
  have hslice2 : ∀ t₁ ∈ Icc (0:ℝ) 1,
      (∫ t₂, H (t₁, t₂)) = ∫ t₂ in (0:ℝ)..(1 - t₁), G t₁ t₂ := by
    intro t₁ ht₁
    obtain ⟨h0, h1⟩ := ht₁
    have hpre : ((fun t₂ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = Icc 0 (1 - t₁) := by
      ext t₂
      simp only [mem_preimage, R₂, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨_, hb, hc⟩; exact ⟨hb, by linarith⟩
      · rintro ⟨ha, hb⟩; exact ⟨h0, ha, by linarith⟩
    rw [hcol2 t₁, hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]
  -- Off `[0,1]` the slice preimage is empty, so the marginal vanishes.
  have hzero1 : ∀ t₂ ∉ Icc (0:ℝ) 1, (∫ t₁, H (t₁, t₂)) = 0 := by
    intro t₂ ht₂
    have hpre : ((fun t₁ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t₁ ⟨ha, hb, hc⟩
      exact absurd (mem_Icc.mpr ⟨hb, by linarith⟩) ht₂
    rw [hcol1 t₂, hpre, setIntegral_empty]
  have hzero2 : ∀ t₁ ∉ Icc (0:ℝ) 1, (∫ t₂, H (t₁, t₂)) = 0 := by
    intro t₁ ht₁
    have hpre : ((fun t₂ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t₂ ⟨ha, hb, hc⟩
      exact absurd (mem_Icc.mpr ⟨ha, by linarith⟩) ht₁
    rw [hcol2 t₁, hpre, setIntegral_empty]
  -- The `t₂`-outer order equals the 2-D integral.
  have hP1 : (∫ p, H p ∂(volume.prod volume))
      = ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), G t₁ t₂ := by
    rw [integral_prod_symm H hInt,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1) hzero1,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact intervalIntegral.integral_congr fun t₂ ht₂ =>
      hslice1 t₂ (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ ht₂)
  -- The `t₁`-outer order equals the same 2-D integral.
  have hP2 : (∫ p, H p ∂(volume.prod volume))
      = ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), G t₁ t₂ := by
    rw [integral_prod H hInt,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1) hzero2,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact intervalIntegral.integral_congr fun t₁ ht₁ =>
      hslice2 t₁ (uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ ht₁)
  exact hP1.symm.trans hP2

end Salt.TwinBar
