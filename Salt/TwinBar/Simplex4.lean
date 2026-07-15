/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SimplexS

/-!
# Sprint Q2(b) — N4-ASM-b1: the 4-D Fubini assembly, peel-OUTER half

**Exploration sprint work item** (`docs/exploration/q2b-asm-design.md`, node `N4-ASM-b`,
the peel-OUTER half). This file lifts the size-`1` 4-simplex geometry and the two
*outer-peel* region↔iterated reductions of the `k = 4` Selberg assembly (the analogues of
`ThreeBarAsm.w3order_eq_region`, one dimension up), consuming node `a`'s size-`s` 3-D
reduction layer (`Salt/TwinBar/SimplexS.lean`: `w3order_eq_region₃`, `slice_fix₄_fst`,
`slice_fix_fst₃`, `simplex_swap_param`). It adds NEW work only; nothing landed is touched.

Scope (the peel-OUTER routes; the peel-inner `canonical4`/`j2order` belong to node `b2`):

* `Δ₄` — the closed size-`1` 4-simplex (`= R₄` definitionally, the regression anchor for
  node `c`), with closed/compact/measurable geometry.
* `psi₄` — the `t₁`-slice identity: the `r`-slice of `Δ₄` at fixed `t₁ ≥ 0` is the
  `Δ₃ (1 − t₁)`-indicator (the size-`s` entry point both outer reductions consume).
* `region_integrable₄` and the two outer-marginal integrabilities (`outer_marg₄_fst` for
  `J₄₄`'s order, `outer_marg₄_swap` for `J₃₄`'s order).
* **`j4order_eq_region`** (`J₄₄`'s route): peel `t₁` outer via `psi₄` → `w3order_eq_region₃
  (1 − t₁)`, no swap.
* **`j3order_eq_region`** (`J₃₄`'s route): peel `t₁` outer → one plain inner-two swap
  `(t₄, t₃)` at size `1 − t₁ − t₂` (`simplex_swap_param` via `slice_fix_fst₃`) → the
  `J₄₄` order → `j4order_eq_region`.

Everything is sorry-free, `native_decide`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-! ## Layer 0 — geometry of the size-`1` 4-simplex `Δ₄` -/

/-- The closed size-`1` 4-simplex
`Δ₄ = {(a,b,c,d) | 0 ≤ a, 0 ≤ b, 0 ≤ c, 0 ≤ d, a + b + c + d ≤ 1}` — the mirror of `Δ₃`'s
`setOf` shape, one coordinate up. It is `R₄` definitionally; `Δ₄` is the region-integral
carrier the four `k = 4` reorderings share. -/
def Δ₄ : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧ p.1 + p.2.1 + p.2.2.1 + p.2.2.2 ≤ 1}

/-- **The regression anchor.** `Δ₄ = R₄` definitionally; node `c` bridges the region masses
to the landed `four_bar`/`I₄` carrier through this `rfl`. -/
theorem Δ₄_eq_R₄ : Δ₄ = R₄ := rfl

/-- `Δ₄` is closed: an intersection of five closed half-spaces. -/
theorem Δ₄_isClosed : IsClosed Δ₄ := by
  have hrw : Δ₄ = {p : ℝ × ℝ × ℝ × ℝ | 0 ≤ p.1} ∩ {p | 0 ≤ p.2.1} ∩ {p | 0 ≤ p.2.2.1}
      ∩ {p | 0 ≤ p.2.2.2} ∩ {p | p.1 + p.2.1 + p.2.2.1 + p.2.2.2 ≤ 1} := by
    ext p; simp only [Δ₄, mem_setOf_eq, mem_inter_iff]; tauto
  rw [hrw]
  exact ((((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const (continuous_fst.comp continuous_snd))).inter
    (isClosed_le continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd)))).inter
    (isClosed_le continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd)))).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- `Δ₄` is compact: closed and inside `Icc (0,0,0,0) (1,1,1,1)`. -/
theorem Δ₄_isCompact : IsCompact Δ₄ := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := ((0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ))) (b := ((1:ℝ), (1:ℝ), (1:ℝ), (1:ℝ))))
    Δ₄_isClosed
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨⟨h1, h2, h3, h4⟩, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-- `Δ₄` is measurable. -/
theorem Δ₄_measurableSet : MeasurableSet Δ₄ := Δ₄_isClosed.measurableSet

/-! ## The `t₁`-slice identity `psi₄` (the size-`s` entry point) -/

/-- **The `t₁`-slice identity.** Slicing `Δ₄` at a fixed `t₁ ≥ 0` leaves the size-`(1 − t₁)`
3-simplex: the `r`-slice of the `Δ₄`-indicator equals the `Δ₃ (1 − t₁)`-indicator of the
`(t₂,t₃,t₄)`-restriction `fun p => g t₁ p.1 p.2.1 p.2.2`. This is the geometric decomposition
of `Δ₄` by `t₁` that both outer reductions (`j4order`/`j3order`) consume — the level-4 mirror
of `w3order_eq_region`'s inner slice step, factored out. -/
theorem psi₄ {g : ℝ → ℝ → ℝ → ℝ → ℝ} {t₁ : ℝ} (h0 : 0 ≤ t₁) :
    (fun r : ℝ × ℝ × ℝ =>
        (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r))
      = (Δ₃ (1 - t₁)).indicator (fun p : ℝ × ℝ × ℝ => g t₁ p.1 p.2.1 p.2.2) := by
  funext r
  by_cases hr : r ∈ Δ₃ (1 - t₁)
  · have ⟨hr1, hr2, hr3, hr4⟩ := hr
    rw [Set.indicator_of_mem hr,
      Set.indicator_of_mem (show (t₁, r) ∈ Δ₄ from ⟨h0, hr1, hr2, hr3, by linarith⟩)]
  · rw [Set.indicator_of_notMem hr]
    have hnm : (t₁, r) ∉ Δ₄ :=
      fun h => hr ⟨h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2.2.2.2; linarith⟩
    exact Set.indicator_of_notMem hnm _

/-! ## `region_integrable₄` and the outer-marginal integrabilities

For a `Δ₄`-continuous integrand, the single-variable `t₁`-outer marginal of the region
function is integrable on `Ioc 0 1`. `outer_marg₄_fst` (the `J₄₄` order `t₂,t₃,t₄`) comes
from the first-coordinate Fubini marginal + `psi₄` + `w3order_eq_region₃`; `outer_marg₄_swap`
(the `J₃₄` order `t₂,t₄,t₃`) is its per-`(t₁,t₂)`-slice inner-two swap
(`simplex_swap_param`). -/

/-- The `Δ₄`-indicator of a `Δ₄`-continuous integrand is integrable (`Δ₄` compact). -/
theorem region_integrable₄ {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    Integrable (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2))
      (volume.prod (volume.prod (volume.prod volume))) := by
  rw [integrable_indicator_iff Δ₄_measurableSet]
  exact ContinuousOn.integrableOn_compact' Δ₄_isCompact Δ₄_measurableSet hg

/-- The `t₁`-outer marginal in the `J₄₄` order `t₂ ↦ t₃ ↦ t₄` is integrable on `Ioc 0 1`. -/
theorem outer_marg₄_fst {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    IntegrableOn
      (fun t₁ => ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), g t₁ t₂ t₃ t₄)
      (Set.Ioc 0 1) volume := by
  have hInt := region_integrable₄ hg
  have hm : IntegrableOn (fun t₁ => ∫ r,
      (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r)
        ∂(volume.prod (volume.prod volume))) (Set.Ioc 0 1) volume :=
    hInt.integral_prod_left.integrableOn
  refine hm.congr_fun (fun t₁ ht₁ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₁
  change (∫ r, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r)
      ∂(volume.prod (volume.prod volume)))
      = ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
          ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), g t₁ t₂ t₃ t₄
  rw [show (∫ r, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r)
        ∂(volume.prod (volume.prod volume)))
      = ∫ p, (Δ₃ (1 - t₁)).indicator (fun p : ℝ × ℝ × ℝ => g t₁ p.1 p.2.1 p.2.2) p
          ∂(volume.prod (volume.prod volume)) from by rw [psi₄ (le_of_lt h0)]]
  exact (w3order_eq_region₃ (1 - t₁) (by linarith)
    (f := fun t₂ t₃ t₄ => g t₁ t₂ t₃ t₄) (slice_fix₄_fst hg (le_of_lt h0))).symm

/-- The `t₁`-outer marginal in the `J₃₄` order `t₂ ↦ t₄ ↦ t₃` is integrable on `Ioc 0 1`:
the inner two `(t₄,t₃)` of each `(t₁,t₂)`-slice are swapped from `outer_marg₄_fst`. -/
theorem outer_marg₄_swap {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    IntegrableOn
      (fun t₁ => ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), g t₁ t₂ t₃ t₄)
      (Set.Ioc 0 1) volume := by
  refine (outer_marg₄_fst hg).congr_fun (fun t₁ ht₁ => ?_) measurableSet_Ioc
  obtain ⟨h0, h1⟩ := ht₁
  refine intervalIntegral.integral_congr (fun t₂ ht₂ => ?_)
  rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)] at ht₂
  obtain ⟨h0₂, h1₂⟩ := ht₂
  exact simplex_swap_param (by linarith : (0:ℝ) ≤ 1 - t₁ - t₂)
    (slice_fix_fst₃ (slice_fix₄_fst hg (le_of_lt h0)) h0₂)

/-! ## The peel-OUTER region↔iterated reductions -/

/-- **`J₄₄`'s route (`j4order_eq_region`).** `∫ t₁ ∫ t₂ ∫ t₃ ∫ t₄` (first coordinate
outermost, canonical residual) of a `Δ₄`-continuous integrand equals `∫_{Δ₄} g`. Peels `t₁`
outermost (`integral_prod`), collapses the outer domain to `[0,1]`, and reduces each
`t₁`-slice via `w3order_eq_region₃ (1 − t₁)` through the slice identity `psi₄` — no swap. The
level-4 mirror of `w3order_eq_region`. -/
theorem j4order_eq_region {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    (∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), g t₁ t₂ t₃ t₄)
      = ∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) p
          ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hInt : Integrable (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2))
      (volume.prod (volume.prod (volume.prod volume))) := region_integrable₄ hg
  have hzero : ∀ t₁ ∉ Icc (0:ℝ) 1,
      (∫ r, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r)
        ∂(volume.prod (volume.prod volume))) = 0 := by
    intro t₁ ht₁
    have hz : (fun r : ℝ × ℝ × ℝ =>
          (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r))
        = fun _ => 0 := by
      funext r
      have hnm : (t₁, r) ∉ Δ₄ := by
        rintro ⟨hh1, hh2, hh3, hh4, hh5⟩
        exact ht₁ (mem_Icc.mpr ⟨hh1, by linarith⟩)
      exact Set.indicator_of_notMem hnm _
    rw [hz]; simp
  rw [integral_prod _ hInt,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1) hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine intervalIntegral.integral_congr (fun t₁ ht₁ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₁
  obtain ⟨h0, h1⟩ := ht₁
  calc (∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
          ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), g t₁ t₂ t₃ t₄)
      = ∫ p, (Δ₃ (1 - t₁)).indicator (fun p : ℝ × ℝ × ℝ => g t₁ p.1 p.2.1 p.2.2) p
          ∂(volume.prod (volume.prod volume)) :=
        w3order_eq_region₃ (1 - t₁) (by linarith)
          (f := fun t₂ t₃ t₄ => g t₁ t₂ t₃ t₄) (slice_fix₄_fst hg h0)
    _ = ∫ r, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) (t₁, r)
          ∂(volume.prod (volume.prod volume)) := by rw [psi₄ h0]

/-- **`J₃₄`'s route (`j3order_eq_region`).** `∫ t₁ ∫ t₂ ∫ t₄ ∫ t₃` (the `J₃₄` peel order,
`t₃` innermost) of a `Δ₄`-continuous integrand equals `∫_{Δ₄} g`. The one plain inner-two
swap `(t₄,t₃)` at size `1 − t₁ − t₂` (`simplex_swap_param`, per `(t₁,t₂)`-slice) turns the
`J₃₄` order into the `J₄₄` order, then `j4order_eq_region` closes it. This route has no 3-D
mirror (it stays in node `b`). -/
theorem j3order_eq_region {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) Δ₄) :
    (∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), g t₁ t₂ t₃ t₄)
      = ∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)) p
          ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hswap : (∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), g t₁ t₂ t₃ t₄)
      = ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
          ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), g t₁ t₂ t₃ t₄ := by
    refine intervalIntegral.integral_congr (fun t₁ ht₁ => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₁
    obtain ⟨h0, h1⟩ := ht₁
    refine intervalIntegral.integral_congr (fun t₂ ht₂ => ?_)
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)] at ht₂
    obtain ⟨h0₂, h1₂⟩ := ht₂
    exact (simplex_swap_param (by linarith : (0:ℝ) ≤ 1 - t₁ - t₂)
      (slice_fix_fst₃ (slice_fix₄_fst hg h0) h0₂)).symm
  rw [hswap]; exact j4order_eq_region hg

end Salt.TwinBar
