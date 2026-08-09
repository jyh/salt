/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Sawtooth

/-!
# WEIL-TRIO W5(S2) — **(7.3)**, the Fourier expansion of the sawtooth majorant

Source math: `docs/sources/hb1983-notes.md:815`, which states (7.3) as

    Min(1/(K‖θ‖),1) = Σ_{m=−∞}^{∞} a_m e(mθ)   (K ≥ 2).

Governing design: `docs/exploration/weil-trio-design-0806.md` v2 §D5 (the degenerate-case
discipline).  Consumer: N7 (Lemma 10), which does **not** live here.

## PRECONDITION PREAMBLE — the assumed world, validated against the live tree

This module assembles; it proves no new estimate.  Every input below was read off the tree
before a line of proof was written, and each is quoted here in the shape it actually has.

**From `Salt/Weil/Sawtooth.lean` (all landed 2026-08-06/08, all at
`[propext, Classical.choice, Quot.sound]`):**

* `sawtoothMajorant (K : ℕ) (θ : ℝ) : ℝ :=`
  `if dist₁ θ 0 = 0 then 1 else min (((K:ℝ) * dist₁ θ 0)⁻¹) 1`
  (`:99`) — HB's `Min(1/(K‖θ‖),1)` in the §D5 degenerate-split form.
* `sawtoothMajorant_eq_inv_max {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :`
  `sawtoothMajorant K θ = (max ((K : ℝ) * dist₁ θ 0) 1)⁻¹` (`:521`).
* `majorantCoeff (K : ℕ) (m : ℤ) : ℂ :=`
  `∫ θ in (0:ℝ)..1, (sawtoothMajorant K θ : ℂ) * e (-((m:ℝ) * θ))`
  (`:659`) — HB's `a_m`.
* `summable_norm_majorantCoeff {K : ℕ} (hK : 2 ≤ K) : Summable (fun m : ℤ => ‖majorantCoeff K m‖)`
  (`:1428`).

**From `Salt/LS/Dist.lean:29`:** `dist₁ (x y : ℝ) : ℝ := |x - y - round (x - y)|`.

**From mathlib:** `has_pointwise_sum_fourier_series_of_summable`
(`Mathlib/Analysis/Fourier/AddCircle.lean:503`, root namespace),
`fourierCoeff_eq_intervalIntegral` (`:302`), `fourier_coe_apply` (`:132`) and
`UnitAddCircle.norm_eq` (`Mathlib/Analysis/Normed/Group/AddCircle.lean:223`).

**The flags anchors this discharges, quoted:**

* `docs/blueprints/flags.md:21325` — *"(7.3), the expansion itself.  It is **downstream of #1, not
  independent**: with `|a_m| ≤ CK/m²` the coefficients are summable and mathlib's
  `AddCircle.hasSum_fourier_series_of_summable` applies to the continuous 1-periodic lift of the
  majorant (continuity is exactly `sawtoothMajorant_eq_inv_max` + continuity of `dist₁`)."*
* `docs/blueprints/flags.md:22150` — *"(7.3) IS NOW UNBLOCKED, NOT DONE … Nobody has assembled it."*
* `docs/blueprints/flags.md:22259` — *"`summable_norm_majorantCoeff` **is** the last missing input
  to (7.3) … It is load-bearing here for an independent reason — in Lean `∑' m, f m = 0` when `f`
  is not summable, so without it the two `tsum` rows would be true and **vacuous**."*
  ⇒ that trap is why the headline row below is stated as a `HasSum` first and the `∑'` equation is
  read off it: `hasSum_majorantCoeff` is *not* vacuous even in principle.

**NO DRIFT FOUND.** Every name and statement above matches the tree at the time of writing.

## What is new here, and what is not

Nothing analytic is new.  The one small bridge is `dist₁_zero_eq_norm_unitAddCircle`:
`dist₁ θ 0` **is** `‖(θ : ℝ/ℤ)‖`.  That single identification does three jobs at once —
1-periodicity, continuity, and the change of variable into mathlib's `AddCircle 1` — so the
majorant's circle lift `majorantCircle` can be *defined directly on `ℝ/ℤ`* by the closed form
`sawtoothMajorant_eq_inv_max` supplies, instead of being descended from `ℝ` with a periodicity
side condition.  `round` is not continuous; `‖·‖` on `ℝ/ℤ` is, and it is the same function.
-/

namespace Salt.Weil

open Salt.LS

/-- mathlib's Fourier API on `AddCircle T` is gated on `Fact (0 < T)`, and `T = 1` here.
Declared `local` on purpose: no statement exported from this file mentions `AddCircle`, so the
instance does not escape. -/
local instance factZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-! ### The bridge — `dist₁ · 0` is the `ℝ/ℤ` norm -/

/-- **`dist₁ θ 0` is the circle norm of `θ`.**  Both sides are `|θ − round θ|`.

This is the whole reason the assembly is short: the corpus's `dist₁ · 0` is defined through
`round`, which is *not* continuous, while mathlib's `‖·‖ : ℝ/ℤ → ℝ` is continuous by construction
— and they are the same function. -/
theorem dist₁_zero_eq_norm_unitAddCircle (θ : ℝ) :
    dist₁ θ 0 = ‖(θ : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  unfold dist₁
  rw [sub_zero]

/-! ### The majorant as a continuous function on `ℝ/ℤ` -/

/-- The (7.3) majorant `Min(1/(K‖θ‖),1)` as a **continuous** function on the circle `ℝ/ℤ`,
written in the closed form of `sawtoothMajorant_eq_inv_max`.  Continuity needs no case split and
no `a.e.` plumbing: `max (K‖x‖) 1 ≥ 1 > 0`, so `Continuous.inv₀` applies everywhere. -/
noncomputable def majorantCircle (K : ℕ) : C(UnitAddCircle, ℂ) where
  toFun x := (((max ((K : ℝ) * ‖x‖) 1)⁻¹ : ℝ) : ℂ)
  continuous_toFun := by
    have hc : Continuous fun x : UnitAddCircle => (max ((K : ℝ) * ‖x‖) 1)⁻¹ := by
      refine Continuous.inv₀ ((continuous_const.mul continuous_norm).max continuous_const)
        (fun x => ?_)
      have h1 : (1 : ℝ) ≤ max ((K : ℝ) * ‖x‖) 1 := le_max_right _ _
      exact ne_of_gt (by linarith)
    exact Complex.continuous_ofReal.comp hc

/-- The circle lift agrees with `sawtoothMajorant` on every real point. -/
theorem majorantCircle_coe {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :
    majorantCircle K (θ : UnitAddCircle) = (sawtoothMajorant K θ : ℂ) := by
  rw [sawtoothMajorant_eq_inv_max hK, dist₁_zero_eq_norm_unitAddCircle]
  rfl

/-- mathlib's Fourier coefficient of the circle lift **is** `majorantCoeff`.  The two differ only
by the order of the two factors and by the `T = 1` normalisation `(1/T) • ·`. -/
theorem fourierCoeff_majorantCircle {K : ℕ} (hK : 1 ≤ K) (m : ℤ) :
    fourierCoeff (⇑(majorantCircle K)) m = majorantCoeff K m := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, one_div_one, one_smul]
  unfold majorantCoeff
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [majorantCircle_coe hK, fourier_coe_apply, smul_eq_mul, mul_comm]
  congr 1
  unfold Salt.LS.e
  congr 1
  push_cast
  ring

/-- Summability of the Fourier coefficients of the circle lift — the last input to (7.3),
transported from `summable_norm_majorantCoeff`. -/
theorem summable_fourierCoeff_majorantCircle {K : ℕ} (hK : 2 ≤ K) :
    Summable (fourierCoeff (⇑(majorantCircle K))) := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  refine Summable.of_norm ?_
  refine (summable_norm_majorantCoeff hK).congr (fun m => ?_)
  rw [fourierCoeff_majorantCircle hK1]

/-! ### (7.3) -/

/-- **(7.3), the convergent form.**  For `K ≥ 2` and every real `θ`, the two-sided Fourier series
`∑_{m ∈ ℤ} a_m e(mθ)` **converges** to the majorant `Min(1/(K‖θ‖),1)`.

This is the row to quote, not the `∑'` restatement below: a Lean `∑'` of a non-summable family is
`0`, so only a `HasSum` carries the convergence assertion HB's `=` intends. -/
theorem hasSum_majorantCoeff {K : ℕ} (hK : 2 ≤ K) (θ : ℝ) :
    HasSum (fun m : ℤ => majorantCoeff K m * e ((m : ℝ) * θ))
      (sawtoothMajorant K θ : ℂ) := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have h := has_pointwise_sum_fourier_series_of_summable
    (summable_fourierCoeff_majorantCircle hK) (θ : UnitAddCircle)
  rw [majorantCircle_coe hK1] at h
  have hfun : (fun m : ℤ => majorantCoeff K m * e ((m : ℝ) * θ))
      = fun m : ℤ => fourierCoeff (⇑(majorantCircle K)) m • fourier m (θ : UnitAddCircle) := by
    funext m
    rw [fourierCoeff_majorantCircle hK1, smul_eq_mul, fourier_coe_apply]
    congr 1
    unfold Salt.LS.e
    congr 1
    push_cast
    ring
  rw [hfun]
  exact h

/-- **(7.3), in the source's literal shape** (`hb1983-notes.md:815`):
`Min(1/(K‖θ‖),1) = Σ_{m=−∞}^{∞} a_m e(mθ)` for `K ≥ 2`.

`K ≥ 2` is HB's own hypothesis and is what forces the final choice `K = 2 + k^{1/4}` in Lemma 10
(`n7-prep-dossier-0806.md:55`); it enters here only through `summable_norm_majorantCoeff`. -/
theorem sawtoothMajorant_fourier_expansion {K : ℕ} (hK : 2 ≤ K) (θ : ℝ) :
    (sawtoothMajorant K θ : ℂ) = ∑' m : ℤ, majorantCoeff K m * e ((m : ℝ) * θ) :=
  (hasSum_majorantCoeff hK θ).tsum_eq.symm

/-- The expansion's terms are summable — the non-vacuity certificate a consumer can quote directly
without re-deriving it from `hasSum_majorantCoeff`. -/
theorem summable_majorantCoeff_mul_e {K : ℕ} (hK : 2 ≤ K) (θ : ℝ) :
    Summable (fun m : ℤ => majorantCoeff K m * e ((m : ℝ) * θ)) :=
  (hasSum_majorantCoeff hK θ).summable

end Salt.Weil
