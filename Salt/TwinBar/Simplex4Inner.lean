/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Simplex4

/-!
# Sprint Q2(b) — N4-ASM-b2: the 4-D Fubini assembly, peel-INNER half

**Exploration sprint work item** (`docs/exploration/q2b-asm-design.md`, node `N4-ASM-b`,
the peel-INNER half). This file adds the two *inner-peel* region↔iterated reductions of the
`k = 4` Selberg assembly — the analogues of `ThreeBarAsm.canonical_eq_region`, one dimension
up — consuming node `b1`'s size-`1` 4-simplex interface (`Salt/TwinBar/Simplex4.lean`: `Δ₄`,
`region_integrable₄`, `psi₄`) and node `a`'s size-`s` 3-D reduction layer
(`Salt/TwinBar/SimplexS.lean`: `Δ₃`, `psi_eq₃`, `slice_fix₄_snd`, `simplex_swap_param`,
`reduce2_outerSnd`). It adds NEW work only; nothing landed is touched.

Scope (the peel-INNER routes; the peel-OUTER `j4order`/`j3order` are landed by node `b1`):

* `psi_eq₄` — the `t₁`-*marginal* identity (NOT b1's slice-form `psi₄`): integrating the
  innermost coordinate `t₁` out of the `Δ₄`-indicator leaves the `Δ₃ 1`-indicator of the
  `t₁`-marginal `Φ(t₂,t₃,t₄) = ∫ t₁, g`. The level-4 mirror of node a's `psi_eq₃`.
* `reduce3_canonical_int` — the size-`1` canonical 3-D region↔iterated taking *integrability*
  (not continuity) of the `Δ₃ 1`-indicator. This is `canonical_eq_region₃ 1` with its
  continuity hypothesis replaced by the Fubini-marginal integrability, so the (non-continuous)
  `t₁`-marginal `Φ` can be reduced without an unbudgeted marginal-continuity lemma — exactly as
  `canonical_eq_region₃`'s own body bottoms out at the integrability-based `reduce2_outerSnd`.
* **`canonical4_eq_region`** (`J₁₄`'s route): peel `t₁` inner (`integral_prod_symm`) via the
  marginal `psi_eq₄`, then `reduce3_canonical_int`. The level-4 mirror of `canonical_eq_region`.
* **`j2order_eq_region`** (`J₂₄`'s route): one plain inner-two swap `(t₁,t₂)` at size
  `1 − t₃ − t₄` (`simplex_swap_param` via `slice_fix₄_snd`, per `(t₃,t₄)`-slice) turns the
  `J₂₄` order into the canonical order, then `canonical4_eq_region` closes it. This factors
  through `canonical4_eq_region` the way `b1`'s `j3order` factored through `j4order`.

Everything is sorry-free, `native_decide`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-! ## The `t₁`-marginal identity `psi_eq₄` (the peel-INNER entry point) -/

/-- **The `t₁`-marginal identity.** Integrating the innermost coordinate `t₁` out of the
`Δ₄`-indicator gives the `Δ₃ 1`-indicator of the `t₁`-marginal
`Φ(t₂,t₃,t₄) = ∫₀^{1−t₄−t₃−t₂} g`. This is the marginal form (the level-4 mirror of node a's
`psi_eq₃`), distinct from `b1`'s slice-form `psi₄`; the peel-INNER reductions consume it. -/
theorem psi_eq₄ {g : ℝ → ℝ → ℝ → ℝ → ℝ} :
    (fun r : ℝ × ℝ × ℝ => ∫ t₁,
        (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r) ∂volume)
      = (Δ₃ 1).indicator
          (fun r : ℝ × ℝ × ℝ =>
            ∫ t₁ in (0:ℝ)..(1 - r.2.2 - r.2.1 - r.1), g t₁ r.1 r.2.1 r.2.2) := by
  funext r
  have hmeas : MeasurableSet ((fun t₁ => (t₁, r)) ⁻¹' Δ₄) :=
    Δ₄_measurableSet.preimage (by fun_prop)
  have hval : (∫ t₁,
        (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r) ∂volume)
      = ∫ t₁ in ((fun t₁ => (t₁, r)) ⁻¹' Δ₄), g t₁ r.1 r.2.1 r.2.2 := by
    have hrw : (fun t₁ =>
          (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r))
        = ((fun t₁ => (t₁, r)) ⁻¹' Δ₄).indicator (fun t₁ => g t₁ r.1 r.2.1 r.2.2) := by
      funext t₁
      by_cases h : (t₁, r) ∈ Δ₄
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show t₁ ∈ (fun t₁ => (t₁, r)) ⁻¹' Δ₄ from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show t₁ ∉ (fun t₁ => (t₁, r)) ⁻¹' Δ₄ from h)]
    rw [hrw, integral_indicator hmeas]
  rw [hval]
  by_cases hr : r ∈ Δ₃ 1
  · have ⟨hr1, hr2, hr3, _⟩ := hr
    have hpre : ((fun t₁ => (t₁, r)) ⁻¹' Δ₄) = Icc 0 (1 - r.2.2 - r.2.1 - r.1) := by
      ext t₁
      simp only [mem_preimage, Δ₄, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨ht, _, _, _, hsum⟩; exact ⟨ht, by linarith⟩
      · rintro ⟨ht, hle⟩; exact ⟨ht, hr1, hr2, hr3, by linarith⟩
    rw [hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - r.2.2 - r.2.1 - r.1),
      Set.indicator_of_mem hr]
  · have hpre : ((fun t₁ => (t₁, r)) ⁻¹' Δ₄) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t₁ ⟨_, hr1, hr2, hr3, hsum⟩
      exact hr ⟨hr1, hr2, hr3, by linarith⟩
    rw [hpre, setIntegral_empty, Set.indicator_of_notMem hr]

/-! ## The integrability-form size-`1` canonical 3-D reduction -/

/-- **Size-`1` canonical 3-D region↔iterated, integrability form.** `∫_{Δ₃ 1} f` (as the
region integral of the `Δ₃ 1`-indicator) equals the canonical iterated integral `∫ t₄ ∫ t₃ ∫ t₂`.
This is `canonical_eq_region₃ 1` with its *continuity* hypothesis replaced by the Fubini-marginal
*integrability* of the `Δ₃ 1`-indicator, so the non-continuous `t₁`-marginal of `canonical4`
can be reduced without an unbudgeted marginal-continuity lemma. Its body mirrors
`canonical_eq_region₃`'s: peel `t₂` inner (`integral_prod_symm`), rewrite via `psi_eq₃ 1`, then
the integrability-based `reduce2_outerSnd`. -/
theorem reduce3_canonical_int {f : ℝ → ℝ → ℝ → ℝ}
    (hInt : Integrable ((Δ₃ 1).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume))) :
    ∫ p, ((Δ₃ 1).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) p
        ∂(volume.prod (volume.prod volume))
      = ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄ := by
  have hΦint : Integrable ((Δ 1).indicator
      (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄)))
      (volume.prod volume) := by
    rw [← psi_eq₃ 1 (by norm_num)]; exact hInt.integral_prod_right
  rw [integral_prod_symm _ hInt, psi_eq₃ 1 (by norm_num)]
  exact reduce2_outerSnd (by norm_num : (0:ℝ) ≤ 1) _ hΦint

/-- **Size-`1` last-coordinate outer marginal, integrability form.** For a `Δ₃ 1`-indicator
that is integrable, the canonical last-coordinate (`t₄`) outer marginal
`t₄ ↦ ∫ t₃ ∫ t₂ f` is integrable on `Ioc 0 1`. This is node a's `outer_marg₃_lst 1` with its
continuity hypothesis replaced by the Fubini-marginal integrability (so a non-continuous
`t₁`-marginal integrand can be threaded); its body mirrors `outer_marg₃_lst`. -/
theorem outer_marg₃_lst_int {f : ℝ → ℝ → ℝ → ℝ}
    (hInt : Integrable ((Δ₃ 1).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume))) :
    IntegrableOn
      (fun t₄ => ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄)
      (Set.Ioc 0 1) volume := by
  have hΨint : Integrable ((Δ 1).indicator
      (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄)))
      (volume.prod volume) := by
    rw [← psi_eq₃ 1 (by norm_num)]; exact hInt.integral_prod_right
  have hm : IntegrableOn (fun t₄ => ∫ t₃,
      ((Δ 1).indicator (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄)))
        (t₃, t₄) ∂volume) (Set.Ioc 0 1) volume := hΨint.integral_prod_right.integrableOn
  refine hm.congr_fun (fun t₄ ht₄ => ?_) measurableSet_Ioc
  obtain ⟨h0, _⟩ := ht₄
  have hΔmeas : MeasurableSet (Δ (1:ℝ)) := by
    refine IsClosed.measurableSet (IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (IsClosed.inter (isClosed_le continuous_const continuous_snd)
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const)))
  have hmeas : MeasurableSet ((fun t₃ => (t₃, t₄)) ⁻¹' Δ 1) := hΔmeas.preimage (by fun_prop)
  have hrw : (fun t₃ => ((Δ 1).indicator
        (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄))) (t₃, t₄))
      = ((fun t₃ => (t₃, t₄)) ⁻¹' Δ 1).indicator
          (fun t₃ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄) := by
    funext t₃
    by_cases h : (t₃, t₄) ∈ Δ 1
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show t₃ ∈ (fun t₃ => (t₃, t₄)) ⁻¹' Δ 1 from h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show t₃ ∉ (fun t₃ => (t₃, t₄)) ⁻¹' Δ 1 from h)]
  have hpre : ((fun t₃ => (t₃, t₄)) ⁻¹' Δ 1) = Icc 0 (1 - t₄) := by
    ext t₃
    simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨ht, _, hc⟩; exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hc⟩; exact ⟨ht, le_of_lt h0, by linarith⟩
  change (∫ t₃, ((Δ 1).indicator
      (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄))) (t₃, t₄) ∂volume)
      = ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), f t₂ t₃ t₄
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₄)]

/-! ## The peel-INNER region↔iterated reductions -/

/-- **`J₁₄`'s route (`canonical4_eq_region`).** `∫ t₄ ∫ t₃ ∫ t₂ ∫ t₁` (the canonical `I₄`
order, `t₁` innermost) of a `Δ₄`-continuous integrand equals `∫_{Δ₄} g`. Peels `t₁` innermost
(`integral_prod_symm`), rewrites the resulting full `t₁`-marginal via `psi_eq₄`, then reduces
the residual `Δ₃ 1`-region through the integrability-form `reduce3_canonical_int` (the
`t₁`-marginal `Φ` need not be continuous — its `Δ₃ 1`-indicator integrability comes from Fubini).
The level-4 mirror of `canonical_eq_region`. -/
theorem canonical4_eq_region {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    (∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), g t₁ t₂ t₃ t₄)
      = ∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) p
          ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hInt := region_integrable₄ hg
  have hΦint : Integrable ((Δ₃ 1).indicator
      (fun r : ℝ × ℝ × ℝ => ∫ t₁ in (0:ℝ)..(1 - r.2.2 - r.2.1 - r.1), g t₁ r.1 r.2.1 r.2.2))
      (volume.prod (volume.prod volume)) := by
    rw [← psi_eq₄]; exact hInt.integral_prod_right
  rw [integral_prod_symm _ hInt, psi_eq₄]
  exact (reduce3_canonical_int (f := fun t₂ t₃ t₄ => ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂),
    g t₁ t₂ t₃ t₄) hΦint).symm

/-- **`J₁₄`'s outer marginal (`outer_marg₄_lst`).** The `t₄`-outermost single-variable marginal
of the canonical `J₁₄` order, `t₄ ↦ ∫ t₃ ∫ t₂ ∫ t₁ g`, is integrable on `Ioc 0 1` — the
dominating outer integrand node `c` needs for `J₁₄`'s outer `integral_mono`. Peels `t₁` out
(`psi_eq₄`) then routes through the integrability-form `outer_marg₃_lst_int`. The `t₄`-outer
analogue of `b1`'s (`t₁`-outer) `outer_marg₄_fst`. -/
theorem outer_marg₄_lst {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    IntegrableOn
      (fun t₄ => ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), g t₁ t₂ t₃ t₄)
      (Set.Ioc 0 1) volume := by
  have hInt := region_integrable₄ hg
  have hΦint : Integrable ((Δ₃ 1).indicator
      (fun r : ℝ × ℝ × ℝ => ∫ t₁ in (0:ℝ)..(1 - r.2.2 - r.2.1 - r.1), g t₁ r.1 r.2.1 r.2.2))
      (volume.prod (volume.prod volume)) := by
    rw [← psi_eq₄]; exact hInt.integral_prod_right
  exact outer_marg₃_lst_int (f := fun t₂ t₃ t₄ => ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂),
    g t₁ t₂ t₃ t₄) hΦint

/-- **`J₂₄`'s route (`j2order_eq_region`).** `∫ t₄ ∫ t₃ ∫ t₁ ∫ t₂` (the `J₂₄` peel order,
`t₂` innermost) of a `Δ₄`-continuous integrand equals `∫_{Δ₄} g`. The one plain inner-two swap
`(t₁,t₂)` at size `1 − t₃ − t₄` (`simplex_swap_param` via `slice_fix₄_snd`, per `(t₃,t₄)`-slice)
turns the `J₂₄` order into the canonical order, then `canonical4_eq_region` closes it — the
peel-INNER analogue of `b1`'s `j3order` factoring through `j4order`. -/
theorem j2order_eq_region {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    (∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), g t₁ t₂ t₃ t₄)
      = ∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) p
          ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hswap : (∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), g t₁ t₂ t₃ t₄)
      = ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
          ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), g t₁ t₂ t₃ t₄ := by
    refine intervalIntegral.integral_congr (fun t₄ ht₄ => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₄
    obtain ⟨h0, _⟩ := ht₄
    refine intervalIntegral.integral_congr (fun t₃ ht₃ => ?_)
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₄)] at ht₃
    obtain ⟨h0₃, _⟩ := ht₃
    have hcont := slice_fix₄_snd hg h0₃ h0
    rw [show (1:ℝ) - t₃ - t₄ = 1 - t₄ - t₃ from by ring] at hcont
    exact simplex_swap_param (by linarith : (0:ℝ) ≤ 1 - t₄ - t₃) hcont
  rw [hswap]; exact canonical4_eq_region hg

/-- **`J₂₄`'s outer marginal (`outer_marg₄_lst_swap`).** The `t₄`-outermost single-variable
marginal of the `J₂₄` order, `t₄ ↦ ∫ t₃ ∫ t₁ ∫ t₂ g`, is integrable on `Ioc 0 1` — the inner
two `(t₁,t₂)` of each `(t₃,t₄)`-slice are swapped from `outer_marg₄_lst` (`simplex_swap_param`
via `slice_fix₄_snd`, at size `1 − t₃ − t₄`). The `J₂₄` analogue of `b1`'s `outer_marg₄_swap`,
supplying `J₂₄`'s outer `integral_mono` dominating integrand for node `c`. -/
theorem outer_marg₄_lst_swap {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    IntegrableOn
      (fun t₄ => ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), g t₁ t₂ t₃ t₄)
      (Set.Ioc 0 1) volume := by
  refine (outer_marg₄_lst hg).congr_fun (fun t₄ ht₄ => ?_) measurableSet_Ioc
  obtain ⟨h0, _⟩ := ht₄
  refine intervalIntegral.integral_congr (fun t₃ ht₃ => ?_)
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₄)] at ht₃
  obtain ⟨h0₃, _⟩ := ht₃
  have hcont := slice_fix₄_snd hg h0₃ (le_of_lt h0)
  rw [show (1:ℝ) - t₃ - t₄ = 1 - t₄ - t₃ from by ring] at hcont
  exact (simplex_swap_param (by linarith : (0:ℝ) ≤ 1 - t₄ - t₃) hcont).symm

end Salt.TwinBar
