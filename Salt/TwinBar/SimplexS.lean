/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.ThreeBarAsm
import Salt.TwinBar.FourBar

/-!
# Sprint Q2(b) — N4-ASM-a: the size-`s` 3-D reduction layer

**Exploration sprint work item** (`docs/exploration/q2b-asm-design.md`, node
`N4-ASM-a`, the risk node of the k = 4 Fubini assembly). This file lifts the entire
3-D reduction layer of `Salt/TwinBar/ThreeBarAsm.lean` — hardwired there to size `1`
(the simplex `R₃`) — to an arbitrary size `s`, so the 4-simplex's size-`(1−t₁)`
3-slice can be reduced by node `b`. It adds NEW work only; nothing landed is touched.

The 2-D layer (`reduce2_outerFst/Snd`, `Δ_indicator_integrable`, `simplex_swap_param`,
`marginal_scaled`) is ALREADY size-parametrised in `ThreeBarAsm.lean` and is reused
verbatim. Every lemma below is the mechanical `1 ↦ s`, `R₃ ↦ Δ₃ s`, `Δ 1 ↦ Δ s`
transcription of its size-`1` original (variables relabelled `t₁ ↦ t₂`, `t₂ ↦ t₃`,
`t₃ ↦ t₄` to match the 4-D residual `(t₂, t₃, t₄)`), threading the `0 ≤ s` and
`0 ≤ s − a` side-conditions. At `s = 1` each statement instantiates back to the landed
size-`1` shape (the regression `example`s at the end consume the landed declarations).

Everything is sorry-free, `native_decide`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-! ## Layer 0 — geometry of the size-`s` 3-simplex `Δ₃ s` -/

/-- The closed size-`s` 3-simplex
`Δ₃ s = {(a,b,c) | 0 ≤ a, 0 ≤ b, 0 ≤ c, a + b + c ≤ s}`. At `s = 1` this is the
landed `R₃`; the `s`-parameter carries the scaled `(t₂,t₃,t₄)`-slice of `R₄`. -/
def Δ₃ (s : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 ≤ s}

/-- **The `s = 1` regression anchor.** `Δ₃ 1 = R₃` definitionally (gate correction 4);
the landed `three_bar` is NOT refactored to consume the size-`s` layer. -/
theorem Δ₃_one_eq_R₃ : Δ₃ 1 = R₃ := rfl

/-- `Δ₃ s` is closed: an intersection of four closed half-spaces. -/
theorem Δ₃_isClosed (s : ℝ) : IsClosed (Δ₃ s) := by
  have hrw : Δ₃ s = {p : ℝ × ℝ × ℝ | 0 ≤ p.1} ∩ {p | 0 ≤ p.2.1} ∩ {p | 0 ≤ p.2.2}
      ∩ {p | p.1 + p.2.1 + p.2.2 ≤ s} := by
    ext p; simp only [Δ₃, mem_setOf_eq, mem_inter_iff]; tauto
  rw [hrw]
  exact (((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const (continuous_fst.comp continuous_snd))).inter
    (isClosed_le continuous_const (continuous_snd.comp continuous_snd))).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- `Δ₃ s` is compact: closed and inside `Icc (0,0,0) (s,s,s)` (the box bound follows
from the simplex constraints, no sign hypothesis on `s` needed). -/
theorem Δ₃_isCompact (s : ℝ) : IsCompact (Δ₃ s) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := ((0:ℝ), (0:ℝ), (0:ℝ))) (b := (s, s, s))) (Δ₃_isClosed s)
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨⟨h1, h2, h3⟩, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-- `Δ₃ s` is measurable. -/
theorem Δ₃_measurableSet (s : ℝ) : MeasurableSet (Δ₃ s) := (Δ₃_isClosed s).measurableSet

/-- `Δ s` (the 2-D simplex) is measurable — a local re-derivation, since
`ThreeBarAsm.Δ_measurableSet` is private there. -/
private theorem Δ_measurableSet' (s : ℝ) : MeasurableSet (Δ s) := by
  have hcl : IsClosed (Δ s) := by
    apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
    apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
    exact isClosed_le (continuous_fst.add continuous_snd) continuous_const
  exact hcl.measurableSet

/-! ## Slice continuity — the size-`s` engine (`Δ₃ s`-fixing) and the `R₄`-mirrors

`slice_fix_fst₃` fixes the FIRST coordinate of a `Δ₃ s`-continuous integrand, giving a
`Δ (s − x)`-continuous 2-slice (the engine both keystones/marginals consume, and the
`(t₄,t₃)`-swap slice of node `b`'s J₃₄ route). `slice_fix₄_fst`/`slice_fix₄_snd` are the
gate-correction-3 `MapsTo`-into-`R₄` mirrors of the landed `slice_fix_t1/t3`, feeding
node `b`'s t₁-peel and J₂₄ swap. -/

/-- Fix the first coordinate `x ≥ 0` of a `Δ₃ s`-continuous integrand; the
`(t₃,t₄)`-slice is continuous on `Δ (s − x)`. -/
theorem slice_fix_fst₃ {s : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousOn (Function.uncurry (fun t₃ t₄ => f x t₃ t₄)) (Δ (s - x)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (x, q.1, q.2)) (Δ (s - x)) (Δ₃ s) := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨hx, ha, hb, by linarith⟩
  have he : Function.uncurry (fun t₃ t₄ => f x t₃ t₄)
      = (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) ∘ (fun q : ℝ × ℝ => (x, q.1, q.2)) := by
    funext q; rfl
  rw [he]
  exact hF.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (x, q.1, q.2))).continuousOn hmap

/-- **Gate correction 3, fix-one-var.** Fix `t₁ ≥ 0` of an `R₄`-continuous integrand;
the `(t₂,t₃,t₄)`-slice is continuous on `Δ₃ (1 − t₁)` — exactly the hypothesis shape the
size-`s` keystones (`canonical_eq_region₃`/`w3order_eq_region₃`) consume. -/
theorem slice_fix₄_fst {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₁ : ℝ} (h1 : 0 ≤ t₁) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => g t₁ p.1 p.2.1 p.2.2) (Δ₃ (1 - t₁)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ × ℝ => (t₁, q.1, q.2.1, q.2.2)) (Δ₃ (1 - t₁)) R₄ := by
    rintro q ⟨ha, hb, hc, hd⟩; exact ⟨h1, ha, hb, hc, by linarith⟩
  have he : (fun p : ℝ × ℝ × ℝ => g t₁ p.1 p.2.1 p.2.2)
      = (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)
        ∘ (fun q : ℝ × ℝ × ℝ => (t₁, q.1, q.2.1, q.2.2)) := by
    funext q; rfl
  rw [he]
  exact hg.comp
    (by fun_prop : Continuous (fun q : ℝ × ℝ × ℝ => (t₁, q.1, q.2.1, q.2.2))).continuousOn hmap

/-- **Gate correction 3, fix-two-var.** Fix `t₃ ≥ 0`, `t₄ ≥ 0` of an `R₄`-continuous
integrand; the `(t₁,t₂)`-slice is continuous on `Δ (1 − t₃ − t₄)` — the hypothesis shape
node `b`'s J₂₄ inner-two `simplex_swap_param` consumes. -/
theorem slice_fix₄_snd {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₃ t₄ : ℝ} (h3 : 0 ≤ t₃) (h4 : 0 ≤ t₄) :
    ContinuousOn (Function.uncurry (fun t₁ t₂ => g t₁ t₂ t₃ t₄)) (Δ (1 - t₃ - t₄)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1, q.2, t₃, t₄)) (Δ (1 - t₃ - t₄)) R₄ := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨ha, hb, h3, h4, by linarith⟩
  have he : Function.uncurry (fun t₁ t₂ => g t₁ t₂ t₃ t₄)
      = (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)
        ∘ (fun q : ℝ × ℝ => (q.1, q.2, t₃, t₄)) := by
    funext q; rfl
  rw [he]
  exact hg.comp
    (by fun_prop : Continuous (fun q : ℝ × ℝ => (q.1, q.2, t₃, t₄))).continuousOn hmap

/-! ## Layer 3 (part) — the size-`s` first-coordinate marginal identity `psi_eq₃` -/

/-- **The size-`s` `t₂`-marginal identity.** Integrating the first coordinate out of the
`Δ₃ s`-indicator gives the `Δ s`-indicator of the marginal
`Φ(t₃,t₄) = ∫₀^{s−t₄−t₃} f`. Size-`s` mirror of the landed `psi_eq` (`hs` threads the
interface uniformly; the nonnegativity is carried by `Δ s`-membership). -/
theorem psi_eq₃ (s : ℝ) (_hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ} :
    (fun r : ℝ × ℝ =>
        ∫ t₂, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r) ∂volume)
      = (Δ s).indicator
          (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄)) := by
  funext r
  have hmeas : MeasurableSet ((fun t₂ => (t₂, r)) ⁻¹' Δ₃ s) :=
    (Δ₃_measurableSet s).preimage (by fun_prop)
  have hval : (∫ t₂, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r) ∂volume)
      = ∫ t₂ in ((fun t₂ => (t₂, r)) ⁻¹' Δ₃ s), f t₂ r.1 r.2 := by
    have hrw : (fun t₂ => ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r))
        = ((fun t₂ => (t₂, r)) ⁻¹' Δ₃ s).indicator (fun t₂ => f t₂ r.1 r.2) := by
      funext t₂
      by_cases h : (t₂, r) ∈ Δ₃ s
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show t₂ ∈ (fun t₂ => (t₂, r)) ⁻¹' Δ₃ s from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show t₂ ∉ (fun t₂ => (t₂, r)) ⁻¹' Δ₃ s from h)]
    rw [hrw, integral_indicator hmeas]
  rw [hval]
  by_cases hr : r ∈ Δ s
  · have ⟨hr1, hr2, hr3⟩ := hr
    have hpre : ((fun t₂ => (t₂, r)) ⁻¹' Δ₃ s) = Icc 0 (s - r.2 - r.1) := by
      ext t₂
      simp only [mem_preimage, Δ₃, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨ht, _, _, hsum⟩; exact ⟨ht, by linarith⟩
      · rintro ⟨ht, hle⟩; exact ⟨ht, hr1, hr2, by linarith⟩
    rw [hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ s - r.2 - r.1),
      Set.indicator_of_mem hr]
    rfl
  · have hpre : ((fun t₂ => (t₂, r)) ⁻¹' Δ₃ s) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t₂ ⟨ht, hr1, hr2, hsum⟩
      exact hr ⟨hr1, hr2, by linarith⟩
    rw [hpre, setIntegral_empty, Set.indicator_of_notMem hr]

/-! ## Layer 3 — the size-`s` region↔iterated reorderings (the two keystones) -/

/-- The size-`s` 3-D indicator of a continuous integrand is integrable
(`Δ₃ s` compact). Size-`s` mirror of `region_integrable`. -/
theorem region_integrable₃ (s : ℝ) (_hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) :
    Integrable ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := by
  rw [integrable_indicator_iff (Δ₃_measurableSet s)]
  exact ContinuousOn.integrableOn_compact' (Δ₃_isCompact s) (Δ₃_measurableSet s) hF

/-- **Keystone 1 — canonical order = region integral (size `s`).**
`∫ t₄ ∫ t₃ ∫ t₂` of a `Δ₃ s`-continuous integrand equals `∫_{Δ₃ s} f`. Peels the first
coordinate innermost (`integral_prod_symm`), rewrites via `psi_eq₃`, then applies
`reduce2_outerSnd` at size `s`. Size-`s` mirror of `canonical_eq_region`. -/
theorem canonical_eq_region₃ (s : ℝ) (hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) :
    (∫ t₄ in (0:ℝ)..s, ∫ t₃ in (0:ℝ)..(s - t₄), ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄)
      = ∫ p, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have hInt : Integrable ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := region_integrable₃ s hs hF
  have hΦint : Integrable ((Δ s).indicator
      (Function.uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄)))
      (volume.prod volume) := by
    rw [← psi_eq₃ s hs]; exact hInt.integral_prod_right
  rw [integral_prod_symm _ hInt, psi_eq₃ s hs]
  exact (reduce2_outerSnd hs _ hΦint).symm

/-- **Keystone 2 — `w3order` = region integral (size `s`).**
`∫ t₂ ∫ t₃ ∫ t₄` (first coordinate outermost) of a `Δ₃ s`-continuous integrand equals
`∫_{Δ₃ s} f`. Peels the first coordinate outermost (`integral_prod`), collapses the outer
domain to `[0,s]`, and reduces each slice via `reduce2_outerFst` at size `s − t₂`.
Size-`s` mirror of `w3order_eq_region`. -/
theorem w3order_eq_region₃ (s : ℝ) (hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) :
    (∫ t₂ in (0:ℝ)..s, ∫ t₃ in (0:ℝ)..(s - t₂), ∫ t₄ in (0:ℝ)..(s - t₂ - t₃), f t₂ t₃ t₄)
      = ∫ p, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have hInt : Integrable ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := region_integrable₃ s hs hF
  have hzero : ∀ t₂ ∉ Icc (0:ℝ) s,
      (∫ r, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r)
        ∂(volume.prod volume)) = 0 := by
    intro t₂ ht₂
    have hz : (fun r : ℝ × ℝ =>
          ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r))
        = fun _ => 0 := by
      funext r
      have hnm : (t₂, r) ∉ Δ₃ s := by
        rintro ⟨hh1, hh2, hh3, hh4⟩
        exact ht₂ (mem_Icc.mpr ⟨hh1, by linarith⟩)
      exact Set.indicator_of_notMem hnm _
    rw [hz]; simp
  rw [integral_prod _ hInt,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) s) hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  refine intervalIntegral.integral_congr (fun t₂ ht₂ => ?_)
  rw [Set.uIcc_of_le hs] at ht₂
  obtain ⟨h0, h1⟩ := ht₂
  have hsl : (fun r : ℝ × ℝ =>
        ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r))
      = (Δ (s - t₂)).indicator (Function.uncurry (fun t₃ t₄ => f t₂ t₃ t₄)) := by
    funext r
    by_cases hr : r ∈ Δ (s - t₂)
    · have ⟨hr1, hr2, hr3⟩ := hr
      rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (show (t₂, r) ∈ Δ₃ s from ⟨h0, hr1, hr2, by linarith⟩)]
      rfl
    · rw [Set.indicator_of_notMem hr]
      have hnm : (t₂, r) ∉ Δ₃ s := fun h => hr ⟨h.2.1, h.2.2.1, by have := h.2.2.2; linarith⟩
      exact Set.indicator_of_notMem hnm _
  calc (∫ t₃ in (0:ℝ)..(s - t₂), ∫ t₄ in (0:ℝ)..(s - t₂ - t₃), f t₂ t₃ t₄)
      = ∫ p, (Δ (s - t₂)).indicator (Function.uncurry (fun t₃ t₄ => f t₂ t₃ t₄)) p
          ∂(volume.prod volume) :=
        (reduce2_outerFst (by linarith : (0:ℝ) ≤ s - t₂) _
          (Δ_indicator_integrable (slice_fix_fst₃ hF h0))).symm
    _ = ∫ r, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r)
          ∂(volume.prod volume) := by rw [hsl]

/-! ## Layer 2 — the size-`s` outer-marginal integrabilities

For a `Δ₃ s`-continuous integrand, the outer (single-variable) marginal of the region
function is integrable on `Ioc 0 s`. `outer_marg₃_fst` (first coordinate outer) comes
from the first-coordinate Fubini marginal directly; `outer_marg₃_lst` (last coordinate
outer, canonical) goes through the `ψ` two-step marginal (`psi_eq₃`). Size-`s` mirrors
of `outer_marg_t1`/`outer_marg_t3`. -/

/-- The first-coordinate outer marginal `t₂ ↦ ∫ t₃ ∫ t₄ f` is integrable on `Ioc 0 s`. -/
theorem outer_marg₃_fst (s : ℝ) (hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) :
    IntegrableOn
      (fun t₂ => ∫ t₃ in (0:ℝ)..(s - t₂), ∫ t₄ in (0:ℝ)..(s - t₂ - t₃), f t₂ t₃ t₄)
      (Set.Ioc 0 s) volume := by
  have hInt := region_integrable₃ s hs hF
  have hm : IntegrableOn (fun t₂ => ∫ r,
      ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r) ∂(volume.prod volume))
      (Set.Ioc 0 s) volume := hInt.integral_prod_left.integrableOn
  refine hm.congr_fun (fun t₂ ht₂ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₂
  have hsl : (fun r : ℝ × ℝ =>
        ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r))
      = (Δ (s - t₂)).indicator (uncurry (fun t₃ t₄ => f t₂ t₃ t₄)) := by
    funext r
    by_cases hr : r ∈ Δ (s - t₂)
    · have ⟨hr1, hr2, hr3⟩ := hr
      rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (show (t₂, r) ∈ Δ₃ s from ⟨le_of_lt h0, hr1, hr2, by linarith⟩)]
      rfl
    · rw [Set.indicator_of_notMem hr]
      have hnm : (t₂, r) ∉ Δ₃ s := fun h => hr ⟨h.2.1, h.2.2.1, by have := h.2.2.2; linarith⟩
      exact Set.indicator_of_notMem hnm _
  change (∫ r, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r)
      ∂(volume.prod volume))
      = ∫ t₃ in (0:ℝ)..(s - t₂), ∫ t₄ in (0:ℝ)..(s - t₂ - t₃), f t₂ t₃ t₄
  rw [show (∫ r, ((Δ₃ s).indicator (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (t₂, r)
        ∂(volume.prod volume))
      = ∫ p, (Δ (s - t₂)).indicator (uncurry (fun t₃ t₄ => f t₂ t₃ t₄)) p ∂(volume.prod volume)
      from by rw [hsl]]
  exact reduce2_outerFst (by linarith : (0:ℝ) ≤ s - t₂) _
    (Δ_indicator_integrable (slice_fix_fst₃ hF (le_of_lt h0)))

/-- The last-coordinate outer marginal `t₄ ↦ ∫ t₃ ∫ t₂ f` (canonical order) is
integrable on `Ioc 0 s`. -/
theorem outer_marg₃_lst (s : ℝ) (hs : 0 ≤ s) {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) :
    IntegrableOn
      (fun t₄ => ∫ t₃ in (0:ℝ)..(s - t₄), ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄)
      (Set.Ioc 0 s) volume := by
  have hΦint : Integrable ((Δ s).indicator
      (uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄))) (volume.prod volume) := by
    rw [← psi_eq₃ s hs]; exact (region_integrable₃ s hs hF).integral_prod_right
  have hm : IntegrableOn (fun t₄ => ∫ t₃,
      ((Δ s).indicator (uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄)))
        (t₃, t₄) ∂volume) (Set.Ioc 0 s) volume := hΦint.integral_prod_right.integrableOn
  refine hm.congr_fun (fun t₄ ht₄ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₄
  have hmeas : MeasurableSet ((fun t₃ => (t₃, t₄)) ⁻¹' Δ s) :=
    (Δ_measurableSet' s).preimage (by fun_prop)
  have hrw : (fun t₃ => ((Δ s).indicator
        (uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄))) (t₃, t₄))
      = ((fun t₃ => (t₃, t₄)) ⁻¹' Δ s).indicator
          (fun t₃ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄) := by
    funext t₃
    by_cases h : (t₃, t₄) ∈ Δ s
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show t₃ ∈ (fun t₃ => (t₃, t₄)) ⁻¹' Δ s from h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show t₃ ∉ (fun t₃ => (t₃, t₄)) ⁻¹' Δ s from h)]
  have hpre : ((fun t₃ => (t₃, t₄)) ⁻¹' Δ s) = Icc 0 (s - t₄) := by
    ext t₃
    simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨ht, _, hc⟩; exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hc⟩; exact ⟨ht, le_of_lt h0, by linarith⟩
  change (∫ t₃, ((Δ s).indicator
      (uncurry (fun t₃ t₄ => ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄))) (t₃, t₄) ∂volume)
      = ∫ t₃ in (0:ℝ)..(s - t₄), ∫ t₂ in (0:ℝ)..(s - t₄ - t₃), f t₂ t₃ t₄
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ s - t₄)]

/-! ## `s = 1` regression — the size-`s` layer recovers the landed size-`1` shapes

Anti-vacuity obligation (design node `N4-ASM-a`): instantiating `s = 1` must recover the
landed lemmas. These `example`s state the landed size-`1` shapes and discharge them from
the size-`s` lemmas at `s = 1`, using `Δ₃_one_eq_R₃`. Nothing landed is refactored. -/

/-- `region_integrable₃ 1` recovers the landed `region_integrable`. -/
example {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    Integrable (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := by
  have h := region_integrable₃ 1 (by norm_num) (f := g) (by rw [Δ₃_one_eq_R₃]; exact hg)
  rw [Δ₃_one_eq_R₃] at h; exact h

/-- `canonical_eq_region₃ 1` recovers the landed `canonical_eq_region`. -/
example {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    (∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)
      = ∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have h := canonical_eq_region₃ 1 (by norm_num) (f := g) (by rw [Δ₃_one_eq_R₃]; exact hg)
  rw [Δ₃_one_eq_R₃] at h; exact h

/-- `w3order_eq_region₃ 1` recovers the landed `w3order_eq_region`. -/
example {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    (∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), g t₁ t₂ t₃)
      = ∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have h := w3order_eq_region₃ 1 (by norm_num) (f := g) (by rw [Δ₃_one_eq_R₃]; exact hg)
  rw [Δ₃_one_eq_R₃] at h; exact h

/-- `Δ₃ 0` is the degenerate simplex `{(0,0,0)}` (non-pathological: the s = 0 boundary
is a single point, not a false side-condition). The size-`s` lemmas hold at `s = 0` with
`hs := le_refl 0`; e.g. `region_integrable₃ 0` is a genuine (zero-mass) statement. -/
example {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Δ₃ 0)) :
    Integrable ((Δ₃ 0).indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) :=
  region_integrable₃ 0 (le_refl 0) hg

end Salt.TwinBar
