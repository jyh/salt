/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Simplex4Inner

/-!
# Sprint Q2(b) — N4-ASM-c: the 4-D Fubini assembly finale → `four_bar` + `no_quad_weight`

**Exploration sprint work item** (`docs/exploration/q2b-asm-design.md`, node `N4-ASM-c`).
This file is the finale of the `k = 4` Selberg assembly: it discharges the four per-peel
bounds `J_m4 F ≤ log 4 · W_m` (each a triple-nested `integral_mono_of_nonneg` over the
landed `sliceCS_m4`, plus the node-a/b region↔iterated reductions), combines the four
weighted masses through the magic identity `w₁₄+w₂₄+w₃₄+w₄₄ ≡ 4/3` (`w_sum_four`) into
`(4/3)·I₄`, and thereby lands

* `four_bar` : `J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F ≤ (4/3)·log 4 · I₄ F`  (`FourBar`, PROVED), and
* `no_quad_weight` : `M₄ < 2` unconditionally (the atlas's third delimitation).

It consumes node `a`'s size-`s` 3-D layer (`Salt/TwinBar/SimplexS.lean`) and node `b`'s
4-D reorderings (`Salt/TwinBar/Simplex4{,Inner}.lean`); it adds NEW work only and touches
nothing landed. Everything is sorry-free, `native_decide`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## The four peel routes (carrier order → node-b reduction + outer marginal)

* `J₁₄` (canonical, `t₁` inner): `canonical4_eq_region` + `outer_marg₄_lst`.
* `J₂₄` (`t₂` inner, inner-two swap): `j2order_eq_region` + `outer_marg₄_lst_swap`.
* `J₃₄` (`t₁` outer, `t₃` inner, inner-two swap): `j3order_eq_region` + `outer_marg₄_swap`.
* `J₄₄` (`t₁` outer, `t₄` inner): `j4order_eq_region` + `outer_marg₄_fst`.

The middle/inner marginal integrabilities come from node a's `outer_marg₃_fst`/`_lst`
(+ a per-slice `simplex_swap_param` for the two swapped orders) and `marginal_scaled`.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function intervalIntegral

/-! ## Continuity plumbing for the `k = 4` weights and the weighted squares -/

theorem w₁₄_continuous : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold w₁₄; fun_prop

theorem w₂₄_continuous : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold w₂₄; fun_prop

theorem w₃₄_continuous : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold w₃₄; fun_prop

theorem w₄₄_continuous : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold w₄₄; fun_prop

/-- The weighted square `w · F²` is continuous on `R₄` when `F` is. Level-4 mirror of
`wsq_continuousOn`. -/
theorem wsq_continuousOn₄ {w : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hw : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => w p.1 p.2.1 p.2.2.1 p.2.2.2))
    {F : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    ContinuousOn
      (fun p : ℝ × ℝ × ℝ × ℝ => w p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)
      R₄ :=
  hw.continuousOn.mul (hF.pow 2)

/-! ## Two extra slice-continuity mirrors (fix `t₄`; fix the last `Δ₃` coordinate; swap) -/

/-- Swap-symmetry of a `Δ s`-continuous 2-slice: the coordinate flip is continuous because
`Δ s` is symmetric. Consumed by the two inner-two-swapped inner marginals (`J₁₄`/`J₃₄`). -/
theorem slice_swap {h : ℝ → ℝ → ℝ} {s : ℝ}
    (hh : ContinuousOn (Function.uncurry h) (Δ s)) :
    ContinuousOn (Function.uncurry (fun b a => h a b)) (Δ s) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.2, q.1)) (Δ s) (Δ s) := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨hb, ha, by linarith⟩
  have he : Function.uncurry (fun b a => h a b)
      = Function.uncurry h ∘ (fun q : ℝ × ℝ => (q.2, q.1)) := by
    funext q; rfl
  rw [he]
  exact hh.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (q.2, q.1))).continuousOn hmap

/-- **Fix the last coordinate `t₄ ≥ 0`** of an `R₄`-continuous integrand; the
`(t₁,t₂,t₃)`-slice is continuous on `Δ₃ (1 − t₄)`. The `t₄`-mirror of `slice_fix₄_fst`,
feeding `J₁₄`/`J₂₄`'s canonical residual. -/
theorem slice_fix₄_lst {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2) R₄)
    {t₄ : ℝ} (h4 : 0 ≤ t₄) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2 t₄) (Δ₃ (1 - t₄)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1, q.2.2, t₄)) (Δ₃ (1 - t₄)) R₄ := by
    rintro q ⟨ha, hb, hc, hd⟩; exact ⟨ha, hb, hc, h4, by linarith⟩
  have he : (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2 t₄)
      = (fun p : ℝ × ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2.1 p.2.2.2)
        ∘ (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1, q.2.2, t₄)) := by
    funext q; rfl
  rw [he]
  exact hg.comp
    (by fun_prop : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1, q.2.2, t₄))).continuousOn hmap

/-- **Fix the last coordinate `x ≥ 0`** of a `Δ₃ s`-continuous integrand; the `(t₁,t₂)`-slice
is continuous on `Δ (s − x)`. The last-coordinate analogue of `slice_fix_fst₃`, feeding
`J₁₄`/`J₂₄`'s inner marginals. -/
theorem slice_fix_lst₃ {s : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) (Δ₃ s)) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousOn (Function.uncurry (fun t₁ t₂ => f t₁ t₂ x)) (Δ (s - x)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1, q.2, x)) (Δ (s - x)) (Δ₃ s) := by
    rintro q ⟨ha, hb, hc⟩; exact ⟨ha, hb, hx, by linarith⟩
  have he : Function.uncurry (fun t₁ t₂ => f t₁ t₂ x)
      = (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2) ∘ (fun q : ℝ × ℝ => (q.1, q.2, x)) := by
    funext q; rfl
  rw [he]
  exact hF.comp (by fun_prop : Continuous (fun q : ℝ × ℝ => (q.1, q.2, x))).continuousOn hmap

/-! ## The four per-peel bounds `J_m4 F ≤ log 4 · W_m` (region form)

Each Selberg peel is bounded by `log 4` times the region integral of its weighted square,
via a TRIPLY-nested `integral_mono_of_nonneg` (the `three_bar` structure, one dimension up):
the innermost mono uses the per-slice `sliceCS_m4`; the two intermediate monos use the
node-a size-`s` marginal integrabilities; the outer mono uses node b's outer marginal; and
the resulting iterated weighted mass is identified with the region integral by the matching
node-b reordering. -/

/-- **`J₄₄` bound.** `J₄₄ F ≤ log 4 · ∫_{Δ₄} w₄₄·F²` (its order is `t₁,t₂,t₃,t₄`, `t₄`
inner — the pure first-coordinate-outer route via `j4order_eq_region`). -/
theorem J₄₄_bound (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    J₄₄ F ≤ Real.log 4 * ∫ p,
      (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hg₄R : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) R₄ :=
    wsq_continuousOn₄ w₄₄_continuous hF
  have hg₄ : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) Δ₄ := hg₄R
  have hinner : ∀ t₁ ∈ Ioc (0:ℝ) 1, ∀ t₂ ∈ Ioc (0:ℝ) (1 - t₁),
      (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
            ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₁ ht₁ t₂ ht₂
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂),
      intervalIntegral.integral_of_le (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₃ => sq_nonneg _)
    · exact (marginal_scaled (slice_fix_fst₃
        (f := fun a b c => w₄₄ t₁ a b c * (F t₁ a b c) ^ 2)
        (slice_fix₄_fst (g := fun a b c d => w₄₄ a b c d * (F a b c d) ^ 2) hg₄R ht₁.1.le)
        ht₂.1.le)).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₃ ht₃ =>
        sliceCS₄₄ hF ht₁.1.le ht₂.1.le ht₃.1.le (by linarith [ht₃.2]))
  have hmid : ∀ t₁ ∈ Ioc (0:ℝ) 1,
      (∫ t₂ in (0:ℝ)..(1 - t₁),
        ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂), (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
            ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₁ ht₁
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁),
      intervalIntegral.integral_of_le (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ =>
        intervalIntegral.integral_nonneg (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂)
          (fun t₃ _ => sq_nonneg _))
    · exact (outer_marg₃_fst (1 - t₁) (by linarith [ht₁.2])
        (slice_fix₄_fst (g := fun a b c d => w₄₄ a b c d * (F a b c d) ^ 2)
          hg₄R ht₁.1.le)).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ => hinner t₁ ht₁ t₂ ht₂)
  have hbound : J₄₄ F ≤ Real.log 4 * ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁),
      ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂ - t₃), w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₄₄
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₁ ht₁ =>
        intervalIntegral.integral_nonneg (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁)
          (fun t₂ ht₂ => intervalIntegral.integral_nonneg
            (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂) (fun t₃ _ => sq_nonneg _)))
    · exact (outer_marg₄_fst hg₄).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hmid
  rwa [j4order_eq_region (g := fun t₁ t₂ t₃ t₄ => w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2) hg₄]
    at hbound

/-- **`J₁₄` bound.** `J₁₄ F ≤ log 4 · ∫_{Δ₄} w₁₄·F²` (its order is the canonical `t₄,t₃,t₂,t₁`,
`t₁` inner — the last-coordinate-outer route via `canonical4_eq_region`). The per-slice
`sliceCS₁₄` carries range `1−t₂−t₃−t₄`, reindexed to the carrier's `1−t₄−t₃−t₂`. -/
theorem J₁₄_bound (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    J₁₄ F ≤ Real.log 4 * ∫ p,
      (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hg₁R : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) R₄ :=
    wsq_continuousOn₄ w₁₄_continuous hF
  have hg₁ : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) Δ₄ := hg₁R
  have hinner : ∀ t₄ ∈ Ioc (0:ℝ) 1, ∀ t₃ ∈ Ioc (0:ℝ) (1 - t₄),
      (∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), (∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
            ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₄ ht₄ t₃ ht₃
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃),
      intervalIntegral.integral_of_le (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₂ => sq_nonneg _)
    · exact (marginal_scaled (slice_swap (slice_fix_lst₃
        (f := fun a b c => w₁₄ a b c t₄ * (F a b c t₄) ^ 2)
        (slice_fix₄_lst (g := fun a b c d => w₁₄ a b c d * (F a b c d) ^ 2) hg₁R ht₄.1.le)
        ht₃.1.le))).const_mul (Real.log 4)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ => ?_)
      have hb := sliceCS₁₄ hF ht₂.1.le ht₃.1.le ht₄.1.le (by linarith [ht₂.2])
      rwa [show (1:ℝ) - t₂ - t₃ - t₄ = 1 - t₄ - t₃ - t₂ from by ring] at hb
  have hmid : ∀ t₄ ∈ Ioc (0:ℝ) 1,
      (∫ t₃ in (0:ℝ)..(1 - t₄),
        ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃), (∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
            ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₄ ht₄
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄),
      intervalIntegral.integral_of_le (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₃ ht₃ =>
        intervalIntegral.integral_nonneg (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃)
          (fun t₂ _ => sq_nonneg _))
    · exact (outer_marg₃_lst (1 - t₄) (by linarith [ht₄.2])
        (slice_fix₄_lst (g := fun a b c d => w₁₄ a b c d * (F a b c d) ^ 2)
          hg₁R ht₄.1.le)).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₃ ht₃ => hinner t₄ ht₄ t₃ ht₃)
  have hbound : J₁₄ F ≤ Real.log 4 * ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄),
      ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₁₄
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₄ ht₄ =>
        intervalIntegral.integral_nonneg (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄)
          (fun t₃ ht₃ => intervalIntegral.integral_nonneg
            (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃) (fun t₂ _ => sq_nonneg _)))
    · exact (outer_marg₄_lst hg₁).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hmid
  rwa [canonical4_eq_region (g := fun t₁ t₂ t₃ t₄ => w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2) hg₁]
    at hbound

/-- **`J₃₄` bound.** `J₃₄ F ≤ log 4 · ∫_{Δ₄} w₃₄·F²` (its order is `t₁,t₂,t₄,t₃`, `t₃` inner —
the first-coordinate-outer route with the inner-two `(t₄,t₃)` swap, via `j3order_eq_region`).
The mid marginal is the `(t₃,t₄)`-swap of `outer_marg₃_fst` (per-slice `simplex_swap_param`). -/
theorem J₃₄_bound (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    J₃₄ F ≤ Real.log 4 * ∫ p,
      (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hg₃R : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) R₄ :=
    wsq_continuousOn₄ w₃₄_continuous hF
  have hg₃ : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) Δ₄ := hg₃R
  have hinner : ∀ t₁ ∈ Ioc (0:ℝ) 1, ∀ t₂ ∈ Ioc (0:ℝ) (1 - t₁),
      (∫ t₄ in (0:ℝ)..(1 - t₁ - t₂), (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
            ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₁ ht₁ t₂ ht₂
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂),
      intervalIntegral.integral_of_le (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₄ => sq_nonneg _)
    · exact (marginal_scaled (slice_swap (slice_fix_fst₃
        (f := fun a b c => w₃₄ t₁ a b c * (F t₁ a b c) ^ 2)
        (slice_fix₄_fst (g := fun a b c d => w₃₄ a b c d * (F a b c d) ^ 2) hg₃R ht₁.1.le)
        ht₂.1.le))).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₄ ht₄ =>
        sliceCS₃₄ hF ht₁.1.le ht₂.1.le ht₄.1.le (by linarith [ht₄.2]))
  have hmid : ∀ t₁ ∈ Ioc (0:ℝ) 1,
      (∫ t₂ in (0:ℝ)..(1 - t₁),
        ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂), (∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₂ in (0:ℝ)..(1 - t₁), ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
            ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₁ ht₁
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁),
      intervalIntegral.integral_of_le (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ =>
        intervalIntegral.integral_nonneg (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂)
          (fun t₄ _ => sq_nonneg _))
    · have hV : IntegrableOn (fun t₂ => ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
          ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
          (Ioc 0 (1 - t₁)) volume := by
        refine (outer_marg₃_fst (1 - t₁) (by linarith [ht₁.2])
          (f := fun a b c => w₃₄ t₁ a b c * (F t₁ a b c) ^ 2)
          (slice_fix₄_fst (g := fun a b c d => w₃₄ a b c d * (F a b c d) ^ 2)
            hg₃R ht₁.1.le)).congr_fun (fun t₂ ht₂ => ?_) measurableSet_Ioc
        exact simplex_swap_param (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂)
          (slice_fix_fst₃ (f := fun a b c => w₃₄ t₁ a b c * (F t₁ a b c) ^ 2)
            (slice_fix₄_fst (g := fun a b c d => w₃₄ a b c d * (F a b c d) ^ 2) hg₃R ht₁.1.le)
            ht₂.1.le)
      exact hV.const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₂ ht₂ => hinner t₁ ht₁ t₂ ht₂)
  have hbound : J₃₄ F ≤ Real.log 4 * ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁),
      ∫ t₄ in (0:ℝ)..(1 - t₁ - t₂),
        ∫ t₃ in (0:ℝ)..(1 - t₁ - t₂ - t₄), w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₃₄
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₁ ht₁ =>
        intervalIntegral.integral_nonneg (by linarith [ht₁.2] : (0:ℝ) ≤ 1 - t₁)
          (fun t₂ ht₂ => intervalIntegral.integral_nonneg
            (by linarith [ht₂.2] : (0:ℝ) ≤ 1 - t₁ - t₂) (fun t₄ _ => sq_nonneg _)))
    · exact (outer_marg₄_swap hg₃).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hmid
  rwa [j3order_eq_region (g := fun t₁ t₂ t₃ t₄ => w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2) hg₃]
    at hbound

/-- **`J₂₄` bound.** `J₂₄ F ≤ log 4 · ∫_{Δ₄} w₂₄·F²` (its order is `t₄,t₃,t₁,t₂`, `t₂` inner —
the last-coordinate-outer route with the inner-two `(t₁,t₂)` swap, via `j2order_eq_region`).
The mid marginal is the `(t₁,t₂)`-swap of `outer_marg₃_lst`; `sliceCS₂₄` carries range
`1−t₁−t₃−t₄`, reindexed to the carrier's `1−t₄−t₃−t₁`. -/
theorem J₂₄_bound (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    J₂₄ F ≤ Real.log 4 * ∫ p,
      (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod (volume.prod volume))) := by
  have hg₂R : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) R₄ :=
    wsq_continuousOn₄ w₂₄_continuous hF
  have hg₂ : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) Δ₄ := hg₂R
  have hinner : ∀ t₄ ∈ Ioc (0:ℝ) 1, ∀ t₃ ∈ Ioc (0:ℝ) (1 - t₄),
      (∫ t₁ in (0:ℝ)..(1 - t₄ - t₃), (∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
            ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₄ ht₄ t₃ ht₃
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃),
      intervalIntegral.integral_of_le (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₁ => sq_nonneg _)
    · exact (marginal_scaled (slice_fix_lst₃
        (f := fun a b c => w₂₄ a b c t₄ * (F a b c t₄) ^ 2)
        (slice_fix₄_lst (g := fun a b c d => w₂₄ a b c d * (F a b c d) ^ 2) hg₂R ht₄.1.le)
        ht₃.1.le)).const_mul (Real.log 4)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t₁ ht₁ => ?_)
      have hb := sliceCS₂₄ hF ht₁.1.le ht₃.1.le ht₄.1.le (by linarith [ht₁.2])
      rwa [show (1:ℝ) - t₁ - t₃ - t₄ = 1 - t₄ - t₃ - t₁ from by ring] at hb
  have hmid : ∀ t₄ ∈ Ioc (0:ℝ) 1,
      (∫ t₃ in (0:ℝ)..(1 - t₄),
        ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃), (∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), F t₁ t₂ t₃ t₄) ^ 2)
        ≤ Real.log 4 * ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
            ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    intro t₄ ht₄
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄),
      intervalIntegral.integral_of_le (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₃ ht₃ =>
        intervalIntegral.integral_nonneg (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃)
          (fun t₁ _ => sq_nonneg _))
    · have hV : IntegrableOn (fun t₃ => ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
          ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
          (Ioc 0 (1 - t₄)) volume := by
        refine (outer_marg₃_lst (1 - t₄) (by linarith [ht₄.2])
          (f := fun a b c => w₂₄ a b c t₄ * (F a b c t₄) ^ 2)
          (slice_fix₄_lst (g := fun a b c d => w₂₄ a b c d * (F a b c d) ^ 2)
            hg₂R ht₄.1.le)).congr_fun (fun t₃ ht₃ => ?_) measurableSet_Ioc
        exact simplex_swap_param (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃)
          (slice_swap (slice_fix_lst₃ (f := fun a b c => w₂₄ a b c t₄ * (F a b c t₄) ^ 2)
            (slice_fix₄_lst (g := fun a b c d => w₂₄ a b c d * (F a b c d) ^ 2) hg₂R ht₄.1.le)
            ht₃.1.le))
      exact hV.const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₃ ht₃ => hinner t₄ ht₄ t₃ ht₃)
  have hbound : J₂₄ F ≤ Real.log 4 * ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄),
      ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃),
        ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃ - t₁), w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₂₄
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t₄ ht₄ =>
        intervalIntegral.integral_nonneg (by linarith [ht₄.2] : (0:ℝ) ≤ 1 - t₄)
          (fun t₃ ht₃ => intervalIntegral.integral_nonneg
            (by linarith [ht₃.2] : (0:ℝ) ≤ 1 - t₄ - t₃) (fun t₁ _ => sq_nonneg _)))
    · exact (outer_marg₄_lst_swap hg₂).const_mul (Real.log 4)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hmid
  rwa [j2order_eq_region (g := fun t₁ t₂ t₃ t₄ => w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2) hg₂]
    at hbound

/-! ## The combine and the headliners

The four region masses add (linearity of the region integral) and collapse via
`w_sum_four ≡ 4/3` to `(4/3)·I₄`, giving `four_bar` (`FourBar`, now PROVED). `no_quad_weight`
then follows unconditionally from the landed `no_quad_weight_of_fourBar`. -/

/-- **`four_bar` (`FourBar`, PROVED).** For every continuous weight `F` on `R₄`,
`J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F ≤ (4/3)·log 4 · I₄ F` — the sharp `k = 4` Selberg bound. This
discharges the 4-D Fubini assembly deferred in `FourBar.lean`. -/
theorem four_bar (F : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄) :
    J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F ≤ (4 / 3) * Real.log 4 * I₄ F := by
  have hr1 := J₁₄_bound F hF
  have hr2 := J₂₄_bound F hF
  have hr3 := J₃₄_bound F hF
  have hr4 := J₄₄_bound F hF
  set r1 := ∫ p, (Δ₄.indicator
      (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod (volume.prod volume))) with hr1def
  set r2 := ∫ p, (Δ₄.indicator
      (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod (volume.prod volume))) with hr2def
  set r3 := ∫ p, (Δ₄.indicator
      (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod (volume.prod volume))) with hr3def
  set r4 := ∫ p, (Δ₄.indicator
      (fun p : ℝ × ℝ × ℝ × ℝ =>
        w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
    ∂(volume.prod (volume.prod (volume.prod volume))) with hr4def
  have he1 := region_integrable₄ (g := fun t₁ t₂ t₃ t₄ => w₁₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
    (wsq_continuousOn₄ w₁₄_continuous hF)
  have he2 := region_integrable₄ (g := fun t₁ t₂ t₃ t₄ => w₂₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
    (wsq_continuousOn₄ w₂₄_continuous hF)
  have he3 := region_integrable₄ (g := fun t₁ t₂ t₃ t₄ => w₃₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
    (wsq_continuousOn₄ w₃₄_continuous hF)
  have he4 := region_integrable₄ (g := fun t₁ t₂ t₃ t₄ => w₄₄ t₁ t₂ t₃ t₄ * (F t₁ t₂ t₃ t₄) ^ 2)
    (wsq_continuousOn₄ w₄₄_continuous hF)
  have hIF : (∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
      ∂(volume.prod (volume.prod (volume.prod volume)))) = I₄ F := by
    change (∫ p, (Δ₄.indicator (fun p : ℝ × ℝ × ℝ × ℝ => (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2)) p
        ∂(volume.prod (volume.prod (volume.prod volume))))
      = ∫ t₄ in (0:ℝ)..1, ∫ t₃ in (0:ℝ)..(1 - t₄), ∫ t₂ in (0:ℝ)..(1 - t₄ - t₃),
          ∫ t₁ in (0:ℝ)..(1 - t₄ - t₃ - t₂), (F t₁ t₂ t₃ t₄) ^ 2
    exact (canonical4_eq_region (g := fun t₁ t₂ t₃ t₄ => (F t₁ t₂ t₃ t₄) ^ 2) (hF.pow 2)).symm
  have h12 : Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
      Δ₄.indicator (fun p => w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p
      + Δ₄.indicator (fun p => w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
      (volume.prod (volume.prod (volume.prod volume))) := he1.add he2
  have h123 : Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
      (Δ₄.indicator (fun p => w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p
      + Δ₄.indicator (fun p => w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
      + Δ₄.indicator (fun p => w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
      (volume.prod (volume.prod (volume.prod volume))) := h12.add he3
  have hcomb : r1 + r2 + r3 + r4 = (4 / 3) * I₄ F := by
    rw [hr1def, hr2def, hr3def, hr4def, ← integral_add he1 he2, ← integral_add h12 he3,
      ← integral_add h123 he4]
    rw [show (fun p : ℝ × ℝ × ℝ × ℝ =>
          ((Δ₄.indicator (fun p => w₁₄ p.1 p.2.1 p.2.2.1 p.2.2.2
                * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p
              + Δ₄.indicator (fun p => w₂₄ p.1 p.2.1 p.2.2.1 p.2.2.2
                * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
              + Δ₄.indicator (fun p => w₃₄ p.1 p.2.1 p.2.2.1 p.2.2.2
                * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
            + Δ₄.indicator (fun p => w₄₄ p.1 p.2.1 p.2.2.1 p.2.2.2
                * (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p)
        = fun p : ℝ × ℝ × ℝ × ℝ =>
          (4 / 3) * Δ₄.indicator (fun p => (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2) p from by
      funext p
      by_cases hp : p ∈ Δ₄
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp,
          Set.indicator_of_mem hp, Set.indicator_of_mem hp]
        linear_combination
          (F p.1 p.2.1 p.2.2.1 p.2.2.2) ^ 2 * (w_sum_four p.1 p.2.1 p.2.2.1 p.2.2.2)
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; ring]
    rw [MeasureTheory.integral_const_mul, hIF]
  have hsum : Real.log 4 * r1 + Real.log 4 * r2 + Real.log 4 * r3 + Real.log 4 * r4
      = (4 / 3) * Real.log 4 * I₄ F := by
    linear_combination Real.log 4 * hcomb
  linarith [hr1, hr2, hr3, hr4, hsum]

/-- `FourBar` (the citable `k = 4` target from `FourBar.lean`) holds. -/
theorem fourBar_holds : FourBar := fun F hF => four_bar F hF

/-- **`no_quad_weight` (`M₄ < 2`, unconditional).** No continuous weight `F` on `R₄` with
positive `L²`-mass crosses the `k = 4` twin gate `2·I₄ F < J₁₄ + J₂₄ + J₃₄ + J₄₄`. The atlas's
third delimitation theorem, now unconditional (the deferred 4-D assembly discharged). -/
theorem no_quad_weight :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ ∧
      0 < I₄ F ∧ 2 * I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F :=
  no_quad_weight_of_fourBar fourBar_holds

/-- Regression spot-check: the assembled `four_bar` applies to a concrete continuous weight
(the constant weight, `fun_prop`-continuous on `R₄`), confirming the bound is well-typed and
usable end-to-end. -/
example : J₁₄ (fun _ _ _ _ => (1 : ℝ)) + J₂₄ (fun _ _ _ _ => 1) + J₃₄ (fun _ _ _ _ => 1)
    + J₄₄ (fun _ _ _ _ => 1) ≤ (4 / 3) * Real.log 4 * I₄ (fun _ _ _ _ => 1) :=
  four_bar (fun _ _ _ _ => 1) (by fun_prop)

end Salt.TwinBar
