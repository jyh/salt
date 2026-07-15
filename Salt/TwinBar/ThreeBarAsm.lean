/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.ThreeBar

/-!
# Sprint Q2(a) — TB3-ASM: the 3-D Fubini assembly → `M₃ < 2` unconditional

**Exploration sprint work item** (`docs/exploration/preregistration.md` Q2(a);
pilot `docs/exploration/pilot.md`, probe P-C, node TB3-ASM). This file adds NEW
work only: it discharges the single deferred gap of `Salt/TwinBar/ThreeBar.lean`
— the 3-D integration assembly — and thereby lands

* `three_bar`  : `J₁₃ F + J₂₃ F + J₃₃ F ≤ (3/2)·log 3 · I₃ F`   (`TripleBar`, PROVED), and
* `no_triple_weight` : `M₃ < 2` unconditionally (the atlas's second delimitation).

Everything is sorry-free, `native_decide`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## Constraint store (Part III opener)

The frozen target is `three_bar`/`no_triple_weight` exactly as scoped in
`ThreeBar.lean` (`TripleBar`, `no_triple_weight_of_tripleBar`). The analytic heart
(`sliceCS₁₃/₂₃/₃₃`, `w_sum_three ≡ 3/2`, `logWeight_half`, `three_halves_log_three_lt_two`)
is LANDED there and is reused verbatim; this file supplies ONLY the measure-theoretic
assembly. No blueprint statement is altered.

## Route (the swap architecture chosen)

The k = 2 assembly (`Salt/TwinBar/{Tonelli,Impossibility}.lean`) is the structural
template one dimension up. The three Selberg peels are each written with their
marginal variable *innermost*, so their weighted masses `W_m := ∭ w_m·F²` sit in
three different nesting orders. The combine `W₁ + W₂ + W₃ = (3/2)·I₃` needs all
three in a common order; we choose the canonical order (`t₃` outer, `t₂` mid, `t₁`
inner, matching `I₃`). Reconciliation:

* **`W₁`** is already canonical — no work.
* **`W₂`** (order `t₃,t₁,t₂`) → canonical differs only by swapping the inner two
  variables with `t₃` fixed outer: a *parametrised* 2-D simplex swap
  (`simplex_swap_param`, the size-`s` generalisation of the landed `simplex_swap`),
  applied slice-by-slice under the outer `∫ t₃`. No 3-D machinery, and the integrand
  `w₂₃·F²` is directly continuous.
* **`W₃`** (order `t₁,t₂,t₃`, `t₃` innermost) → canonical is a genuine 3-D reversal;
  it is the ONE place a real 3-D Fubini step is unavoidable (`t₃` must move from
  innermost to outermost, which no single fixed-variable 2-D swap can achieve).
  We route it through the 3-D indicator `R₃.indicator(G)` — exactly as `simplex_swap`
  routes its 2-D swap through `R₂.indicator` — associating `ℝ×ℝ×ℝ` as `ℝ×(ℝ×ℝ)`.
  Both endpoint orders (`t₁` outer / `t₁` inner) are reachable through this
  association WITHOUT re-associating, because in each `t₁` sits at an extreme; the
  awkward `t₁`-in-the-middle order (`W₂`'s) is precisely the one we handle by the
  cheap 2-D route above, so the association wall is never hit.

The 2-D workhorse `reduce2_outerFst`/`reduce2_outerSnd` (region-integral = iterated
in either order, over the size-`s` simplex `Δ s`) is the size-`s` factoring of the
landed `simplex_swap`; taking joint integrability as a hypothesis lets it serve both
the continuous case (via compactness) and the `t₁`-marginal case (via Fubini
integrability) inside the 3-D swap.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-! ## Layer 0 — geometry of the size-`s` simplex `Δ s` -/

/-- The closed size-`s` planar simplex `Δ s = {(a,b) | 0 ≤ a, 0 ≤ b, a + b ≤ s}`.
`Δ 1` is the landed `R₂`; the `s`-parameter carries the scaled `t₃`- and
`t₁`-slices of `R₃`. -/
def Δ (s : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ s}

/-- `Δ s` is closed: an intersection of three closed half-spaces. -/
private theorem Δ_isClosed (s : ℝ) : IsClosed (Δ s) := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  exact isClosed_le (continuous_fst.add continuous_snd) continuous_const

/-- `Δ s` is compact: closed and inside `Icc (0,0) (s,s)` (the box bound follows
from the simplex constraints, no sign hypothesis on `s` needed). -/
private theorem Δ_isCompact (s : ℝ) : IsCompact (Δ s) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := ((0:ℝ), (0:ℝ))) (b := (s, s))) (Δ_isClosed s)
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> simp <;> linarith

/-- `Δ s` is measurable. -/
private theorem Δ_measurableSet (s : ℝ) : MeasurableSet (Δ s) := (Δ_isClosed s).measurableSet

/-! ## Layer 1 — the size-`s` 2-D region↔iterated reductions

`reduce2_outerFst`/`reduce2_outerSnd` are the size-`s` generalisations of the two
halves of the landed `simplex_swap`: both express the 2-D integral of the
`Δ s`-indicator as an iterated interval integral, one with each variable outermost.
They take joint integrability as a hypothesis (so they serve both the continuous and
the Fubini-marginal cases). -/

/-- **`a`-outer reduction.** With the first coordinate outermost:
`∫_{ℝ²} (Δ s).indicator(uncurry G) = ∫ a in 0..s, ∫ b in 0..(s−a), G a b`. This is
the `t₁`-outer half of `simplex_swap` at size `s`. -/
theorem reduce2_outerFst {s : ℝ} (hs : 0 ≤ s) (G : ℝ → ℝ → ℝ)
    (hInt : Integrable ((Δ s).indicator (Function.uncurry G)) (volume.prod volume)) :
    ∫ p, (Δ s).indicator (Function.uncurry G) p ∂(volume.prod volume)
      = ∫ a in (0:ℝ)..s, ∫ b in (0:ℝ)..(s - a), G a b := by
  set H : ℝ × ℝ → ℝ := (Δ s).indicator (Function.uncurry G) with hH
  have hcol : ∀ a : ℝ, (∫ b, H (a, b)) = ∫ b in ((fun b => (a, b)) ⁻¹' Δ s), G a b := by
    intro a
    have hmeas : MeasurableSet ((fun b => ((a : ℝ), b)) ⁻¹' Δ s) :=
      (Δ_measurableSet s).preimage (by fun_prop)
    have hrw : (fun b => H (a, b))
        = ((fun b => (a, b)) ⁻¹' Δ s).indicator (fun b => G a b) := by
      funext b
      rw [hH, ← Set.indicator_comp_right (fun b => ((a : ℝ), b))]
      rfl
    rw [hrw, integral_indicator hmeas]
  have hslice : ∀ a ∈ Icc (0:ℝ) s, (∫ b, H (a, b)) = ∫ b in (0:ℝ)..(s - a), G a b := by
    intro a ha
    obtain ⟨h0, h1⟩ := ha
    have hpre : ((fun b => ((a : ℝ), b)) ⁻¹' Δ s) = Icc 0 (s - a) := by
      ext b
      simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨_, hb, hc⟩; exact ⟨hb, by linarith⟩
      · rintro ⟨hb, hc⟩; exact ⟨h0, hb, by linarith⟩
    rw [hcol a, hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ s - a)]
  have hzero : ∀ a ∉ Icc (0:ℝ) s, (∫ b, H (a, b)) = 0 := by
    intro a ha
    have hpre : ((fun b => ((a : ℝ), b)) ⁻¹' Δ s) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨hx, hb, hc⟩
      exact absurd (mem_Icc.mpr ⟨hx, by linarith⟩) ha
    rw [hcol a, hpre, setIntegral_empty]
  rw [integral_prod H hInt,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) s) hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  exact intervalIntegral.integral_congr fun a ha => hslice a (uIcc_of_le hs ▸ ha)

/-- **`b`-outer reduction.** With the second coordinate outermost:
`∫_{ℝ²} (Δ s).indicator(uncurry G) = ∫ b in 0..s, ∫ a in 0..(s−b), G a b`. This is
the `t₂`-outer half of `simplex_swap` at size `s`. -/
theorem reduce2_outerSnd {s : ℝ} (hs : 0 ≤ s) (G : ℝ → ℝ → ℝ)
    (hInt : Integrable ((Δ s).indicator (Function.uncurry G)) (volume.prod volume)) :
    ∫ p, (Δ s).indicator (Function.uncurry G) p ∂(volume.prod volume)
      = ∫ b in (0:ℝ)..s, ∫ a in (0:ℝ)..(s - b), G a b := by
  set H : ℝ × ℝ → ℝ := (Δ s).indicator (Function.uncurry G) with hH
  have hcol : ∀ b : ℝ, (∫ a, H (a, b)) = ∫ a in ((fun a => (a, b)) ⁻¹' Δ s), G a b := by
    intro b
    have hmeas : MeasurableSet ((fun a => ((a : ℝ), b)) ⁻¹' Δ s) :=
      (Δ_measurableSet s).preimage (by fun_prop)
    have hrw : (fun a => H (a, b))
        = ((fun a => (a, b)) ⁻¹' Δ s).indicator (fun a => G a b) := by
      funext a
      rw [hH, ← Set.indicator_comp_right (fun a => ((a : ℝ), b))]
      rfl
    rw [hrw, integral_indicator hmeas]
  have hslice : ∀ b ∈ Icc (0:ℝ) s, (∫ a, H (a, b)) = ∫ a in (0:ℝ)..(s - b), G a b := by
    intro b hb
    obtain ⟨h0, h1⟩ := hb
    have hpre : ((fun a => ((a : ℝ), b)) ⁻¹' Δ s) = Icc 0 (s - b) := by
      ext a
      simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨ha, _, hc⟩; exact ⟨ha, by linarith⟩
      · rintro ⟨ha, hc⟩; exact ⟨ha, h0, by linarith⟩
    rw [hcol b, hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ s - b)]
  have hzero : ∀ b ∉ Icc (0:ℝ) s, (∫ a, H (a, b)) = 0 := by
    intro b hb
    have hpre : ((fun a => ((a : ℝ), b)) ⁻¹' Δ s) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro a ⟨ha, hx, hc⟩
      exact absurd (mem_Icc.mpr ⟨hx, by linarith⟩) hb
    rw [hcol b, hpre, setIntegral_empty]
  rw [integral_prod_symm H hInt,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) s) hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  exact intervalIntegral.integral_congr fun b hb => hslice b (uIcc_of_le hs ▸ hb)

/-- Joint integrability of the `Δ s`-indicator of a continuous integrand, from
compactness of `Δ s` (`s ≥ 0`). Mirrors the k = 2 `simplex_swap` integrability step. -/
theorem Δ_indicator_integrable {s : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) (Δ s)) :
    Integrable ((Δ s).indicator (Function.uncurry G)) (volume.prod volume) := by
  rw [integrable_indicator_iff (Δ_measurableSet s)]
  exact ContinuousOn.integrableOn_compact' (Δ_isCompact s) (Δ_measurableSet s) hG

/-- **The parametrised simplex swap** (the size-`s` `simplex_swap`). For `G`
continuous on `Δ s`, the two inner-order iterated integrals agree:
`∫ a in 0..s, ∫ b in 0..(s−a), G a b = ∫ b in 0..s, ∫ a in 0..(s−b), G a b`. Both
equal the 2-D region integral. This reconciles `W₂`'s inner two variables to the
canonical order slice-by-slice in `t₃`. -/
theorem simplex_swap_param {s : ℝ} (hs : 0 ≤ s) {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) (Δ s)) :
    (∫ a in (0:ℝ)..s, ∫ b in (0:ℝ)..(s - a), G a b)
      = ∫ b in (0:ℝ)..s, ∫ a in (0:ℝ)..(s - b), G a b :=
  (reduce2_outerFst hs G (Δ_indicator_integrable hG)).symm.trans
    (reduce2_outerSnd hs G (Δ_indicator_integrable hG))

/-! ## Layer 0′ — geometry of the closed 3-simplex `R₃` -/

/-- `R₃` is closed: an intersection of four closed half-spaces. -/
private theorem R₃_isClosed : IsClosed R₃ := by
  have hrw : R₃ = {p : ℝ × ℝ × ℝ | 0 ≤ p.1} ∩ {p | 0 ≤ p.2.1} ∩ {p | 0 ≤ p.2.2}
      ∩ {p | p.1 + p.2.1 + p.2.2 ≤ 1} := by
    ext p; simp only [R₃, mem_setOf_eq, mem_inter_iff]; tauto
  rw [hrw]
  exact (((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const (continuous_fst.comp continuous_snd))).inter
    (isClosed_le continuous_const (continuous_snd.comp continuous_snd))).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- `R₃` is compact: closed and inside `Icc (0,0,0) (1,1,1)`. -/
private theorem R₃_isCompact : IsCompact R₃ := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := ((0:ℝ), (0:ℝ), (0:ℝ))) (b := ((1:ℝ), (1:ℝ), (1:ℝ)))) R₃_isClosed
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨⟨h1, h2, h3⟩, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-- `R₃` is measurable. -/
private theorem R₃_measurableSet : MeasurableSet R₃ := R₃_isClosed.measurableSet

/-! ## Continuity of the weights and the weighted squares on `R₃` -/

theorem w₁₃_continuous : Continuous (fun p : ℝ × ℝ × ℝ => w₁₃ p.1 p.2.1 p.2.2) := by
  unfold w₁₃; fun_prop

theorem w₂₃_continuous : Continuous (fun p : ℝ × ℝ × ℝ => w₂₃ p.1 p.2.1 p.2.2) := by
  unfold w₂₃; fun_prop

theorem w₃₃_continuous : Continuous (fun p : ℝ × ℝ × ℝ => w₃₃ p.1 p.2.1 p.2.2) := by
  unfold w₃₃; fun_prop

/-- The weighted square `w · F²` is continuous on `R₃` when `F` is (and `w` is a
continuous weight). -/
theorem wsq_continuousOn {w : ℝ → ℝ → ℝ → ℝ}
    (hw : Continuous (fun p : ℝ × ℝ × ℝ => w p.1 p.2.1 p.2.2)) {F : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => w p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) R₃ :=
  hw.continuousOn.mul (hF.pow 2)

/-! ## Slice continuity of a continuous-on-`R₃` integrand

Restricting a continuous-on-`R₃` function to a `t₁`- or `t₃`-slice gives a
continuous-on-`Δ (1 − fixed)` function (via the slice embedding + `MapsTo`). The
`_swap` variant carries the reordered slice `J₁₃`'s inner marginal needs. -/

/-- Fix `t₁ ≥ 0`; the `(t₂,t₃)`-slice is continuous on `Δ (1 − t₁)`. -/
theorem slice_fix_t1 {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) {t₁ : ℝ} (h1 : 0 ≤ t₁) :
    ContinuousOn (Function.uncurry (fun t₂ t₃ => g t₁ t₂ t₃)) (Δ (1 - t₁)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (t₁, q.1, q.2)) (Δ (1 - t₁)) R₃ := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨h1, ha, hb, by linarith⟩
  have he : Function.uncurry (fun t₂ t₃ => g t₁ t₂ t₃)
      = (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) ∘ (fun q : ℝ × ℝ => (t₁, q.1, q.2)) := by
    funext q; rfl
  rw [he]
  exact hg.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (t₁, q.1, q.2))).continuousOn hmap

/-- Fix `t₃ ≥ 0`; the `(t₁,t₂)`-slice is continuous on `Δ (1 − t₃)`. -/
theorem slice_fix_t3 {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) {t₃ : ℝ} (h3 : 0 ≤ t₃) :
    ContinuousOn (Function.uncurry (fun t₁ t₂ => g t₁ t₂ t₃)) (Δ (1 - t₃)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1, q.2, t₃)) (Δ (1 - t₃)) R₃ := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨ha, hb, h3, by linarith⟩
  have he : Function.uncurry (fun t₁ t₂ => g t₁ t₂ t₃)
      = (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) ∘ (fun q : ℝ × ℝ => (q.1, q.2, t₃)) := by
    funext q; rfl
  rw [he]
  exact hg.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (q.1, q.2, t₃))).continuousOn hmap

/-- Fix `t₃ ≥ 0`; the reordered `(t₂,t₁)`-slice is continuous on `Δ (1 − t₃)`
(`J₁₃`'s inner marginal has `t₂` outer, `t₁` inner). -/
theorem slice_fix_t3_swap {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) {t₃ : ℝ} (h3 : 0 ≤ t₃) :
    ContinuousOn (Function.uncurry (fun t₂ t₁ => g t₁ t₂ t₃)) (Δ (1 - t₃)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.2, q.1, t₃)) (Δ (1 - t₃)) R₃ := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨hb, ha, h3, by linarith⟩
  have he : Function.uncurry (fun t₂ t₁ => g t₁ t₂ t₃)
      = (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) ∘ (fun q : ℝ × ℝ => (q.2, q.1, t₃)) := by
    funext q; rfl
  rw [he]
  exact hg.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (q.2, q.1, t₃))).continuousOn hmap

/-! ## Scaled inner-marginal integrability (Layer 2's inner-integrability engine)

The size-`s` analogue of the landed `marginal₁_integrableOn`: for `G` continuous on
`Δ s`, the inner interval integral is integrable in the outer variable over `Ioc 0 s`.
Routed through the 2-D indicator's Fubini marginal (`Integrable.integral_prod_left`),
whose value on `Ioc 0 s` equals the interval integral (slice preimage = `Icc 0 (s−a)`). -/
theorem marginal_scaled {s : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) (Δ s)) :
    IntegrableOn (fun a => ∫ b in (0:ℝ)..(s - a), G a b) (Set.Ioc 0 s) volume := by
  set H : ℝ × ℝ → ℝ := (Δ s).indicator (Function.uncurry G) with hH
  have hInt : Integrable H (volume.prod volume) := Δ_indicator_integrable hG
  have hm : IntegrableOn (fun a => ∫ b, H (a, b)) (Set.Ioc 0 s) volume :=
    hInt.integral_prod_left.integrableOn
  refine hm.congr_fun (fun a ha => ?_) measurableSet_Ioc
  obtain ⟨ha0, ha1⟩ := ha
  have hmeas : MeasurableSet ((fun b => ((a : ℝ), b)) ⁻¹' Δ s) :=
    (Δ_measurableSet s).preimage (by fun_prop)
  have hrw : (fun b => H (a, b)) = ((fun b => (a, b)) ⁻¹' Δ s).indicator (fun b => G a b) := by
    funext b; rw [hH, ← Set.indicator_comp_right (fun b => ((a : ℝ), b))]; rfl
  have hpre : ((fun b => ((a : ℝ), b)) ⁻¹' Δ s) = Icc 0 (s - a) := by
    ext b
    simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨_, hb, hc⟩; exact ⟨hb, by linarith⟩
    · rintro ⟨hb, hc⟩; exact ⟨le_of_lt ha0, hb, by linarith⟩
  change (∫ b, H (a, b)) = ∫ b in (0:ℝ)..(s - a), G a b
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ s - a)]

/-! ## Layer 3 — the 3-D reorderings

Both endpoint orders of the triple integral of a continuous-on-`R₃` integrand equal
the single 3-D integral of `R₃.indicator(g)` over `μ₃ := volume.prod (volume.prod
volume)`. This is the direct 3-D analogue of `simplex_swap`; `t₁` is peeled at an
extreme in each order, so no `ℝ×ℝ×ℝ` re-association is needed. -/

/-- The 3-D indicator of `g` is integrable on `μ₃` (compactness of `R₃`). -/
theorem region_integrable {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    Integrable (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := by
  rw [integrable_indicator_iff R₃_measurableSet]
  exact ContinuousOn.integrableOn_compact' R₃_isCompact R₃_measurableSet hg

/-- **The `t₁`-marginal identity.** Integrating `t₁` out of the 3-D indicator gives
the `Δ 1`-indicator of the `t₁`-marginal `Φ(t₂,t₃) = ∫₀^{1−t₃−t₂} g`. This is the
`ψ = indicator(Φ)` bridge feeding both the canonical reduction and the `t₃`-outer
marginal integrability. -/
theorem psi_eq {g : ℝ → ℝ → ℝ → ℝ} :
    (fun r : ℝ × ℝ => ∫ t₁, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r) ∂volume)
      = (Δ 1).indicator
          (Function.uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)) := by
  funext r
  have hmeas : MeasurableSet ((fun t₁ => (t₁, r)) ⁻¹' R₃) := R₃_measurableSet.preimage (by fun_prop)
  have hval : (∫ t₁, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r) ∂volume)
      = ∫ t₁ in ((fun t₁ => (t₁, r)) ⁻¹' R₃), g t₁ r.1 r.2 := by
    have hrw : (fun t₁ => (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r))
        = ((fun t₁ => (t₁, r)) ⁻¹' R₃).indicator (fun t₁ => g t₁ r.1 r.2) := by
      funext t₁
      by_cases h : (t₁, r) ∈ R₃
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show t₁ ∈ (fun t₁ => (t₁, r)) ⁻¹' R₃ from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show t₁ ∉ (fun t₁ => (t₁, r)) ⁻¹' R₃ from h)]
    rw [hrw, integral_indicator hmeas]
  rw [hval]
  by_cases hr : r ∈ Δ 1
  · have ⟨hr1, hr2, hr3⟩ := hr
    have hpre : ((fun t₁ => (t₁, r)) ⁻¹' R₃) = Icc 0 (1 - r.2 - r.1) := by
      ext t₁
      simp only [mem_preimage, R₃, mem_setOf_eq, mem_Icc]
      constructor
      · rintro ⟨ht, _, _, hsum⟩; exact ⟨ht, by linarith⟩
      · rintro ⟨ht, hle⟩; exact ⟨ht, hr1, hr2, by linarith⟩
    rw [hpre, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - r.2 - r.1),
      Set.indicator_of_mem hr]
    rfl
  · have hpre : ((fun t₁ => (t₁, r)) ⁻¹' R₃) = (∅ : Set ℝ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t₁ ⟨ht, hr1, hr2, hsum⟩
      exact hr ⟨hr1, hr2, by linarith⟩
    rw [hpre, setIntegral_empty, Set.indicator_of_notMem hr]

/-- **Canonical order = region integral.** `∫ t₃ ∫ t₂ ∫ t₁` (the `I₃` order) of a
continuous-on-`R₃` integrand equals `∫_{R₃} g`. Peels `t₁` innermost
(`integral_prod_symm`), rewrites via `psi_eq`, then applies `reduce2_outerSnd` at
`s = 1`. -/
theorem canonical_eq_region {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    (∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)
      = ∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have hInt : Integrable (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := region_integrable hg
  have hΦint : Integrable ((Δ 1).indicator
      (Function.uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)))
      (volume.prod volume) := by
    rw [← psi_eq]; exact hInt.integral_prod_right
  rw [integral_prod_symm _ hInt, psi_eq]
  exact (reduce2_outerSnd (by norm_num : (0:ℝ) ≤ 1) _ hΦint).symm

/-- **`W₃`-order = region integral.** `∫ t₁ ∫ t₂ ∫ t₃` (the `J₃₃`/`W₃` order) of a
continuous-on-`R₃` integrand equals `∫_{R₃} g`. Peels `t₁` outermost
(`integral_prod`), collapses the outer domain to `[0,1]`, and reduces each `t₁`-slice
via `reduce2_outerFst` at `s = 1 − t₁`. -/
theorem w3order_eq_region {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    (∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), g t₁ t₂ t₃)
      = ∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) p
          ∂(volume.prod (volume.prod volume)) := by
  have hInt : Integrable (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
      (volume.prod (volume.prod volume)) := region_integrable hg
  have hzero : ∀ t₁ ∉ Icc (0:ℝ) 1,
      (∫ r, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r)
        ∂(volume.prod volume)) = 0 := by
    intro t₁ ht₁
    have hz : (fun r : ℝ × ℝ => (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r))
        = fun _ => 0 := by
      funext r
      have hnm : (t₁, r) ∉ R₃ := by
        rintro ⟨hh1, hh2, hh3, hh4⟩
        exact ht₁ (mem_Icc.mpr ⟨hh1, by linarith⟩)
      exact Set.indicator_of_notMem hnm _
    rw [hz]; simp
  rw [integral_prod _ hInt,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1) hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine intervalIntegral.integral_congr (fun t₁ ht₁ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₁
  obtain ⟨h0, h1⟩ := ht₁
  have hsl : (fun r : ℝ × ℝ => (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r))
      = (Δ (1 - t₁)).indicator (Function.uncurry (fun t₂ t₃ => g t₁ t₂ t₃)) := by
    funext r
    by_cases hr : r ∈ Δ (1 - t₁)
    · have ⟨hr1, hr2, hr3⟩ := hr
      rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (show (t₁, r) ∈ R₃ from ⟨h0, hr1, hr2, by linarith⟩)]
      rfl
    · rw [Set.indicator_of_notMem hr]
      have hnm : (t₁, r) ∉ R₃ := fun h => hr ⟨h.2.1, h.2.2.1, by have := h.2.2.2; linarith⟩
      exact Set.indicator_of_notMem hnm _
  calc (∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), g t₁ t₂ t₃)
      = ∫ p, (Δ (1 - t₁)).indicator (Function.uncurry (fun t₂ t₃ => g t₁ t₂ t₃)) p
          ∂(volume.prod volume) :=
        (reduce2_outerFst (by linarith : (0:ℝ) ≤ 1 - t₁) _
          (Δ_indicator_integrable (slice_fix_t1 hg h0))).symm
    _ = ∫ r, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r)
          ∂(volume.prod volume) := by rw [hsl]

/-! ## Layer 2 — outer-marginal integrability (the dominating outer integrands)

For a continuous-on-`R₃` integrand, the outer (single-variable) marginal of the
region function is integrable on `[0,1]`. `outer_marg_t1` (the `W₃`/`J₃₃` outer `t₁`)
comes from the first-coordinate Fubini marginal directly; `outer_marg_t3` (the
`W₁`/`J₁₃` outer `t₃`) goes through the `ψ` two-step marginal (`psi_eq`). -/

/-- The `t₁`-outer marginal `t₁ ↦ ∫∫ g` is integrable on `Ioc 0 1`. -/
theorem outer_marg_t1 {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    IntegrableOn (fun t₁ => ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), g t₁ t₂ t₃)
      (Set.Ioc 0 1) volume := by
  have hInt := region_integrable hg
  have hm : IntegrableOn (fun t₁ => ∫ r,
      (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r) ∂(volume.prod volume))
      (Set.Ioc 0 1) volume := hInt.integral_prod_left.integrableOn
  refine hm.congr_fun (fun t₁ ht₁ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₁
  have hsl : (fun r : ℝ × ℝ => (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r))
      = (Δ (1 - t₁)).indicator (uncurry (fun t₂ t₃ => g t₁ t₂ t₃)) := by
    funext r
    by_cases hr : r ∈ Δ (1 - t₁)
    · have ⟨hr1, hr2, hr3⟩ := hr
      rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (show (t₁, r) ∈ R₃ from ⟨le_of_lt h0, hr1, hr2, by linarith⟩)]
      rfl
    · rw [Set.indicator_of_notMem hr]
      have hnm : (t₁, r) ∉ R₃ := fun h => hr ⟨h.2.1, h.2.2.1, by have := h.2.2.2; linarith⟩
      exact Set.indicator_of_notMem hnm _
  change (∫ r, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r)
      ∂(volume.prod volume)) = ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), g t₁ t₂ t₃
  rw [show (∫ r, (R₃.indicator (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)) (t₁, r)
        ∂(volume.prod volume))
      = ∫ p, (Δ (1 - t₁)).indicator (uncurry (fun t₂ t₃ => g t₁ t₂ t₃)) p ∂(volume.prod volume)
      from by rw [hsl]]
  exact reduce2_outerFst (by linarith : (0:ℝ) ≤ 1 - t₁) _
    (Δ_indicator_integrable (slice_fix_t1 hg (le_of_lt h0)))

/-- The `t₃`-outer marginal `t₃ ↦ ∫ t₂ ∫ t₁ g` (canonical order) is integrable on
`Ioc 0 1`. -/
theorem outer_marg_t3 {g : ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) R₃) :
    IntegrableOn (fun t₃ => ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)
      (Set.Ioc 0 1) volume := by
  have hΦint : Integrable ((Δ 1).indicator
      (uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃))) (volume.prod volume) := by
    rw [← psi_eq]; exact (region_integrable hg).integral_prod_right
  have hm : IntegrableOn (fun t₃ => ∫ t₂,
      ((Δ 1).indicator (uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃)))
        (t₂, t₃) ∂volume) (Set.Ioc 0 1) volume := hΦint.integral_prod_right.integrableOn
  refine hm.congr_fun (fun t₃ ht₃ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₃
  have hmeas : MeasurableSet ((fun t₂ => (t₂, t₃)) ⁻¹' Δ 1) :=
    (Δ_measurableSet 1).preimage (by fun_prop)
  have hrw : (fun t₂ => ((Δ 1).indicator
        (uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃))) (t₂, t₃))
      = ((fun t₂ => (t₂, t₃)) ⁻¹' Δ 1).indicator
          (fun t₂ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃) := by
    funext t₂
    by_cases h : (t₂, t₃) ∈ Δ 1
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show t₂ ∈ (fun t₂ => (t₂, t₃)) ⁻¹' Δ 1 from h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show t₂ ∉ (fun t₂ => (t₂, t₃)) ⁻¹' Δ 1 from h)]
  have hpre : ((fun t₂ => (t₂, t₃)) ⁻¹' Δ 1) = Icc 0 (1 - t₃) := by
    ext t₂
    simp only [mem_preimage, Δ, mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨ht, _, hc⟩; exact ⟨ht, by linarith⟩
    · rintro ⟨ht, hc⟩; exact ⟨ht, le_of_lt h0, by linarith⟩
  change (∫ t₂, ((Δ 1).indicator
      (uncurry (fun t₂ t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃))) (t₂, t₃) ∂volume)
      = ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), g t₁ t₂ t₃
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₃)]

/-! ## Layer 2 — the three per-peel bounds `J_m ≤ log 3 · ∫_{R₃} w_m·F²`

Each Selberg peel is bounded by `log 3` times the region integral of its weighted
square, via a doubly-nested `integral_mono_of_nonneg` (the `k = 2` `twin_bar`
structure, one dimension up): the inner mono uses the per-slice `sliceCS_m3` with the
scaled inner-marginal integrability (`marginal_scaled`); the outer mono uses the
outer-marginal integrability (`outer_marg_*`); the resulting iterated weighted mass
is identified with the region integral by the Layer-3 reordering. -/

/-- **`J₃₃` bound.** `J₃₃ F ≤ log 3 · ∫_{R₃} w₃₃·F²` (its `W₃` order is `t₁,t₂,t₃`). -/
theorem J₃₃_bound (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃) :
    J₃₃ F ≤ Real.log 3 * ∫ p,
      (R₃.indicator (fun p : ℝ × ℝ × ℝ => w₃₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod volume)) := by
  have hg₃ : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => w₃₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) R₃ :=
    wsq_continuousOn w₃₃_continuous hF
  have hinner : ∀ t₁ ∈ Ioc (0:ℝ) 1,
      (∫ t₂ in (0:ℝ)..(1 - t₁), (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), F t₁ t₂ t₃) ^ 2)
        ≤ Real.log 3 * ∫ t₂ in (0:ℝ)..(1 - t₁),
            ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    intro t₁ ht₁
    obtain ⟨h0, h1⟩ := ht₁
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₁),
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₂ => sq_nonneg _)
    · exact (marginal_scaled
        (slice_fix_t1 (g := fun t₁ t₂ t₃ => w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₃
          (le_of_lt h0))).const_mul (Real.log 3)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₂ ht₂ => sliceCS₃₃ hF (le_of_lt h0) (le_of_lt ht₂.1) (by linarith [ht₂.2]))
  have hbound : J₃₃ F ≤ Real.log 3 * ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁),
      ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₃₃
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₁ ht₁ => intervalIntegral.integral_nonneg
          (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁) (fun t₂ _ => sq_nonneg _))
    · exact (outer_marg_t1 hg₃).const_mul (Real.log 3)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hinner
  rwa [w3order_eq_region (g := fun t₁ t₂ t₃ => w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₃] at hbound

/-- **`J₁₃` bound.** `J₁₃ F ≤ log 3 · ∫_{R₃} w₁₃·F²` (its order is the canonical
`t₃,t₂,t₁`). The per-slice `sliceCS₁₃` carries the range `1−t₂−t₃`, reindexed to the
carrier's `1−t₃−t₂`. -/
theorem J₁₃_bound (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃) :
    J₁₃ F ≤ Real.log 3 * ∫ p,
      (R₃.indicator (fun p : ℝ × ℝ × ℝ => w₁₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod volume)) := by
  have hg₁ : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => w₁₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) R₃ :=
    wsq_continuousOn w₁₃_continuous hF
  have hinner : ∀ t₃ ∈ Ioc (0:ℝ) 1,
      (∫ t₂ in (0:ℝ)..(1 - t₃), (∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), F t₁ t₂ t₃) ^ 2)
        ≤ Real.log 3 * ∫ t₂ in (0:ℝ)..(1 - t₃),
            ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    intro t₃ ht₃
    obtain ⟨h0, h1⟩ := ht₃
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₃),
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₃)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₂ => sq_nonneg _)
    · exact (marginal_scaled
        (slice_fix_t3_swap (g := fun t₁ t₂ t₃ => w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₁
          (le_of_lt h0))).const_mul (Real.log 3)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ => ?_)
      have hb := sliceCS₁₃ hF (le_of_lt ht₂.1) (le_of_lt h0) (by linarith [ht₂.2])
      rwa [show (1:ℝ) - t₂ - t₃ = 1 - t₃ - t₂ from by ring] at hb
  have hbound : J₁₃ F ≤ Real.log 3 * ∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃),
      ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₁₃
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₃ ht₃ => intervalIntegral.integral_nonneg
          (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₃) (fun t₂ _ => sq_nonneg _))
    · exact (outer_marg_t3 hg₁).const_mul (Real.log 3)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hinner
  rwa [canonical_eq_region (g := fun t₁ t₂ t₃ => w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₁] at hbound

/-- **`J₂₃` bound.** `J₂₃ F ≤ log 3 · ∫_{R₃} w₂₃·F²` (its `W₂` order is `t₃,t₁,t₂`).
The dominating outer marginal (`t₁` outer, `t₂` inner) is reconciled to the canonical
`t₂`-outer order slice-by-slice via `simplex_swap_param`, both for its integrability
and for the region identification. -/
theorem J₂₃_bound (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃) :
    J₂₃ F ≤ Real.log 3 * ∫ p,
      (R₃.indicator (fun p : ℝ × ℝ × ℝ => w₂₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod volume)) := by
  have hg₂ : ContinuousOn
      (fun p : ℝ × ℝ × ℝ => w₂₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) R₃ :=
    wsq_continuousOn w₂₃_continuous hF
  -- the `t₁`-outer inner-double integral equals the `t₂`-outer canonical one, per `t₃`
  have hswap : ∀ t₃ : ℝ, 0 ≤ t₃ → t₃ ≤ 1 →
      (∫ t₁ in (0:ℝ)..(1 - t₃), ∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2)
        = ∫ t₂ in (0:ℝ)..(1 - t₃),
            ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    intro t₃ h0 _h1
    exact simplex_swap_param (by linarith : (0:ℝ) ≤ 1 - t₃)
      (slice_fix_t3 (g := fun t₁ t₂ t₃ => w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₂ h0)
  have hinner : ∀ t₃ ∈ Ioc (0:ℝ) 1,
      (∫ t₁ in (0:ℝ)..(1 - t₃), (∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), F t₁ t₂ t₃) ^ 2)
        ≤ Real.log 3 * ∫ t₁ in (0:ℝ)..(1 - t₃),
            ∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    intro t₃ ht₃
    obtain ⟨h0, h1⟩ := ht₃
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₃),
      intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₃)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₁ => sq_nonneg _)
    · exact (marginal_scaled
        (slice_fix_t3 (g := fun t₁ t₂ t₃ => w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₂
          (le_of_lt h0))).const_mul (Real.log 3)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t₁ ht₁ => ?_)
      have hb := sliceCS₂₃ hF (le_of_lt ht₁.1) (le_of_lt h0) (by linarith [ht₁.2])
      rwa [show (1:ℝ) - t₁ - t₃ = 1 - t₃ - t₁ from by ring] at hb
  -- the `t₁`-outer dominating marginal is integrable on `Ioc 0 1` (via the swap)
  have hV2int : IntegrableOn (fun t₃ => ∫ t₁ in (0:ℝ)..(1 - t₃),
      ∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) (Ioc 0 1) volume :=
    (outer_marg_t3 hg₂).congr_fun
      (fun t₃ ht₃ => (hswap t₃ (le_of_lt ht₃.1) ht₃.2).symm) measurableSet_Ioc
  have hbound : J₂₃ F ≤ Real.log 3 * ∫ t₃ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₃),
      ∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₂₃
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₃ ht₃ => intervalIntegral.integral_nonneg
          (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₃) (fun t₁ _ => sq_nonneg _))
    · exact hV2int.const_mul (Real.log 3)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hinner
  -- reorder the `t₁`-outer mass to canonical, then identify with the region integral
  rw [show (∫ t₃ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₃),
        ∫ t₂ in (0:ℝ)..(1 - t₃ - t₁), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2)
      = ∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃),
          ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2 from
      intervalIntegral.integral_congr (fun t₃ ht₃ => by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₃
        exact hswap t₃ ht₃.1 ht₃.2)] at hbound
  rwa [canonical_eq_region (g := fun t₁ t₂ t₃ => w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2) hg₂] at hbound

/-! ## Layer 4 — the combine and the headliners

The three region masses add (linearity of the region integral) and collapse via
`w_sum_three ≡ 3/2` to `(3/2)·I₃`, giving `three_bar` (`TripleBar`, now PROVED).
`no_triple_weight` then follows unconditionally from the landed
`no_triple_weight_of_tripleBar`. -/

/-- **`three_bar` (`TripleBar`, PROVED).** For every continuous weight `F` on `R₃`,
`J₁₃ F + J₂₃ F + J₃₃ F ≤ (3/2)·log 3 · I₃ F` — the sharp `k = 3` Selberg bound. This
discharges the 3-D Fubini assembly deferred in `ThreeBar.lean`. -/
theorem three_bar (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃) :
    J₁₃ F + J₂₃ F + J₃₃ F ≤ (3 / 2) * Real.log 3 * I₃ F := by
  have hr1 := J₁₃_bound F hF
  have hr2 := J₂₃_bound F hF
  have hr3 := J₃₃_bound F hF
  set r1 := ∫ p, (R₃.indicator
      (fun p : ℝ × ℝ × ℝ => w₁₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod volume)) with hr1def
  set r2 := ∫ p, (R₃.indicator
      (fun p : ℝ × ℝ × ℝ => w₂₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod volume)) with hr2def
  set r3 := ∫ p, (R₃.indicator
      (fun p : ℝ × ℝ × ℝ => w₃₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod volume)) with hr3def
  have he1 := region_integrable (g := fun t₁ t₂ t₃ => w₁₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2)
    (wsq_continuousOn w₁₃_continuous hF)
  have he2 := region_integrable (g := fun t₁ t₂ t₃ => w₂₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2)
    (wsq_continuousOn w₂₃_continuous hF)
  have he3 := region_integrable (g := fun t₁ t₂ t₃ => w₃₃ t₁ t₂ t₃ * (F t₁ t₂ t₃) ^ 2)
    (wsq_continuousOn w₃₃_continuous hF)
  have hIF : (∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => (F p.1 p.2.1 p.2.2) ^ 2)) p
      ∂(volume.prod (volume.prod volume))) = I₃ F := by
    change (∫ p, (R₃.indicator (fun p : ℝ × ℝ × ℝ => (F p.1 p.2.1 p.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod volume)))
      = ∫ t₃ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₃), ∫ t₁ in (0:ℝ)..(1 - t₃ - t₂), (F t₁ t₂ t₃) ^ 2
    exact (canonical_eq_region (g := fun t₁ t₂ t₃ => (F t₁ t₂ t₃) ^ 2) (hF.pow 2)).symm
  have h12 : Integrable (fun p : ℝ × ℝ × ℝ =>
      R₃.indicator (fun p => w₁₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) p
      + R₃.indicator (fun p => w₂₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) p)
      (volume.prod (volume.prod volume)) := he1.add he2
  have hcomb : r1 + r2 + r3 = (3 / 2) * I₃ F := by
    rw [hr1def, hr2def, hr3def, ← integral_add he1 he2, ← integral_add h12 he3]
    rw [show (fun p : ℝ × ℝ × ℝ =>
          (R₃.indicator (fun p => w₁₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) p
            + R₃.indicator (fun p => w₂₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) p)
          + R₃.indicator (fun p => w₃₃ p.1 p.2.1 p.2.2 * (F p.1 p.2.1 p.2.2) ^ 2) p)
        = fun p : ℝ × ℝ × ℝ => (3 / 2) * R₃.indicator (fun p => (F p.1 p.2.1 p.2.2) ^ 2) p from by
      funext p
      by_cases hp : p ∈ R₃
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp,
          Set.indicator_of_mem hp]
        linear_combination (F p.1 p.2.1 p.2.2) ^ 2 * (w_sum_three p.1 p.2.1 p.2.2)
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hp]; ring]
    rw [integral_const_mul, hIF]
  have hsum : Real.log 3 * r1 + Real.log 3 * r2 + Real.log 3 * r3
      = (3 / 2) * Real.log 3 * I₃ F := by
    linear_combination Real.log 3 * hcomb
  linarith [hr1, hr2, hr3, hsum]

/-- `TripleBar` (the citable `k = 3` target from `ThreeBar.lean`) holds. -/
theorem tripleBar_holds : TripleBar := fun F hF => three_bar F hF

/-- **`no_triple_weight` (`M₃ < 2`, unconditional).** No continuous weight `F` on
`R₃` with positive `L²`-mass crosses the `k = 3` twin gate `2·I₃ F < J₁₃ + J₂₃ + J₃₃`.
The atlas's second delimitation theorem, now unconditional (the deferred assembly
discharged). -/
theorem no_triple_weight :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ ∧
      0 < I₃ F ∧ 2 * I₃ F < J₁₃ F + J₂₃ F + J₃₃ F :=
  no_triple_weight_of_tripleBar tripleBar_holds

end Salt.TwinBar

