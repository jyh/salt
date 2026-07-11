/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Dist

/-!
# Large sieve track, nodes L5.1 + L5.2 (fused): periodic unfolding of δ-spaced windows

Blueprint: `docs/blueprints/largesieve.md`.

* `Spaced δ α` — the frozen carrier: the points `α : Fin R → ℝ` are `δ`-separated
  on the circle `ℝ/ℤ` (`∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)`).
* **L5.1 + L5.2** (`sum_integral_le_period`): for a nonnegative, continuous,
  1-periodic `g : ℝ → ℝ` and a `δ`-spaced system with `0 < δ ≤ 1/2`,
  `∑ r, ∫_{α r − δ/2}^{α r + δ/2} g ≤ ∫₀¹ g`.

Route (no sorting): reduce each center to `β r = Int.fract (α r) ∈ [0,1)` (the
integral is unchanged by the integer shift, since `g` is 1-periodic). The reduced
half-open intervals `Ioc (β r − δ/2) (β r + δ/2)` are **pairwise disjoint** (an
overlap forces `|β r − β s| < δ` hence `dist₁ (β r) (β s) < δ`, contradicting
spacing) and all sit inside the length-1 window `Ioc a (a+1)` where
`a = (min_r β r) − δ/2` (the left ends dominate `a`; the right ends are bounded by
`a+1` via the wraparound gap `dist₁ ≤ |β r − β_min − 1|`). A disjoint-union
integral plus monotonicity (`g ≥ 0`) and one periodic window shift finish it.
-/

namespace Salt.LS

open scoped BigOperators
open MeasureTheory intervalIntegral Set

/-- **Carrier (Fable-frozen).** `α : Fin R → ℝ` is `δ`-spaced on the circle. -/
def Spaced {R : ℕ} (δ : ℝ) (α : Fin R → ℝ) : Prop :=
  ∀ r s, r ≠ s → δ ≤ dist₁ (α r) (α s)

/-- `g (t + n) = g t` for integer `n`, from 1-periodicity. -/
theorem periodic_add_int {g : ℝ → ℝ} (hper : ∀ x, g (x + 1) = g x) (n : ℤ) (t : ℝ) :
    g (t + (n : ℝ)) = g t := by
  refine Int.induction_on n ?_ ?_ ?_
  · simp
  · intro k ih
    push_cast at ih ⊢
    rw [show t + ((k : ℝ) + 1) = (t + (k : ℝ)) + 1 by ring, hper]
    exact ih
  · intro k ih
    push_cast at ih ⊢
    have hh := hper (t + (-(k : ℝ)) - 1)
    rw [show t + (-(k : ℝ)) - 1 + 1 = t + (-(k : ℝ)) by ring] at hh
    rw [show t + (-(k : ℝ) - 1) = t + (-(k : ℝ)) - 1 by ring, ← hh]
    exact ih

/-- Interval integral of a 1-periodic function is invariant under an integer shift
of both endpoints. -/
theorem intervalIntegral_add_intCast {g : ℝ → ℝ} (hper : ∀ x, g (x + 1) = g x)
    (n : ℤ) (x y : ℝ) :
    (∫ t in (x + (n : ℝ))..(y + (n : ℝ)), g t) = ∫ t in x..y, g t := by
  rw [← intervalIntegral.integral_comp_add_right g (n : ℝ)]
  exact intervalIntegral.integral_congr (fun t _ => periodic_add_int hper n t)

/-- `dist₁` is invariant under reducing both arguments mod 1 via `Int.fract`. -/
theorem dist₁_fract (x y : ℝ) : dist₁ (Int.fract x) (Int.fract y) = dist₁ x y := by
  have hx : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor x; push_cast; linarith
  have hy : Int.fract y = y + ((-⌊y⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor y; push_cast; linarith
  rw [hx, hy, dist₁_add_int_left, dist₁_add_int_right]

/-- `dist₁ x y` underestimates the distance from `x − y` to any integer. -/
theorem dist₁_le_sub_int (x y : ℝ) (k : ℤ) : dist₁ x y ≤ |x - y - (k : ℝ)| := by
  unfold dist₁
  exact round_le (x - y) k

/-- **L5.1 + L5.2 (fused) — periodic unfolding (CONSUMER-FROZEN).** -/
theorem sum_integral_le_period {R : ℕ} {δ : ℝ} {α : Fin R → ℝ} (g : ℝ → ℝ)
    (hper : ∀ x, g (x + 1) = g x) (hg : ∀ x, 0 ≤ g x) (hcont : Continuous g)
    (hsp : Spaced δ α) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), g t ≤ ∫ t in (0:ℝ)..1, g t := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hg t)
  -- The reduced centers.
  set β : Fin R → ℝ := fun r => Int.fract (α r) with hβ
  have hβr : ∀ r, β r = Int.fract (α r) := fun r => rfl
  have hβ_nonneg : ∀ r, 0 ≤ β r := fun r => by rw [hβr]; exact Int.fract_nonneg _
  have hβ_lt : ∀ r, β r < 1 := fun r => by rw [hβr]; exact Int.fract_lt_one _
  -- The window base point `a = (min β) − δ/2`.
  have hne : (Finset.univ : Finset (Fin R)).Nonempty := ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  obtain ⟨r₀, -, hm0⟩ := Finset.exists_mem_eq_inf' hne β
  set m : ℝ := Finset.univ.inf' hne β with hm
  set a : ℝ := m - δ / 2 with ha
  have hm_le : ∀ r, m ≤ β r := fun r => Finset.inf'_le β (Finset.mem_univ r)
  have hm_nonneg : 0 ≤ m := by rw [hm0]; exact hβ_nonneg r₀
  -- Step 1: reduce each interval to the β-window.
  have hstep1 : ∀ r, (∫ t in (α r - δ / 2)..(α r + δ / 2), g t)
      = ∫ t in (β r - δ / 2)..(β r + δ / 2), g t := by
    intro r
    have hfr := Int.fract_add_floor (α r)
    have e1 : α r - δ / 2 = (β r - δ / 2) + ((⌊α r⌋ : ℤ) : ℝ) := by rw [hβr]; linarith
    have e2 : α r + δ / 2 = (β r + δ / 2) + ((⌊α r⌋ : ℤ) : ℝ) := by rw [hβr]; linarith
    rw [e1, e2, intervalIntegral_add_intCast hper ⌊α r⌋]
  -- Step 2: interval integral = set integral over Ioc.
  have hle_int : ∀ r, β r - δ / 2 ≤ β r + δ / 2 := fun r => by linarith
  have hstep2 : ∀ r, (∫ t in (β r - δ / 2)..(β r + δ / 2), g t)
      = ∫ t in Ioc (β r - δ / 2) (β r + δ / 2), g t := fun r =>
    intervalIntegral.integral_of_le (hle_int r)
  -- Disjointness of the reduced intervals.
  have hdisj : Pairwise (Function.onFun Disjoint (fun r => Ioc (β r - δ / 2) (β r + δ / 2))) := by
    intro r s hrs
    rw [Function.onFun, Set.disjoint_left]
    intro x hxr hxs
    have habs : |β r - β s| < δ := by
      rw [abs_lt]
      exact ⟨by have := hxs.1; have := hxr.2; linarith,
             by have := hxr.1; have := hxs.2; linarith⟩
    have hd1 : dist₁ (β r) (β s) < δ := lt_of_le_of_lt (dist₁_le_abs _ _) habs
    have heq : dist₁ (β r) (β s) = dist₁ (α r) (α s) := by rw [hβr, hβr]; exact dist₁_fract _ _
    have := hsp r s hrs
    linarith [heq ▸ hd1]
  -- Containment: each reduced interval sits inside `Ioc a (a+1)`.
  have hsub : ∀ r, Ioc (β r - δ / 2) (β r + δ / 2) ⊆ Ioc a (a + 1) := by
    intro r
    have hbr : β r ≤ m + 1 - δ := by
      by_cases hr : r = r₀
      · subst hr; rw [← hm0]; linarith
      · have hβr0 : β r₀ = m := hm0.symm
        have hd : δ ≤ dist₁ (β r) (β r₀) := by
          rw [hβr, hβr, dist₁_fract]; exact hsp r r₀ hr
        have hle : dist₁ (β r) (β r₀) ≤ |β r - β r₀ - 1| := by
          simpa using dist₁_le_sub_int (β r) (β r₀) 1
        have hneg : β r - β r₀ - 1 ≤ 0 := by
          rw [hβr0]; have := hβ_lt r; linarith [hm_nonneg]
        rw [abs_of_nonpos hneg] at hle
        have hcomb : δ ≤ -(β r - β r₀ - 1) := le_trans hd hle
        rw [hβr0] at hcomb
        linarith
    apply Ioc_subset_Ioc
    · rw [ha]; linarith [hm_le r]
    · rw [ha]; linarith
  -- Integrability of `g` on the window and its subunion.
  have hint_win : IntegrableOn g (Ioc a (a + 1)) := hcont.integrableOn_Ioc
  have hint_union : IntegrableOn g (⋃ r, Ioc (β r - δ / 2) (β r + δ / 2)) :=
    hint_win.mono_set (iUnion_subset hsub)
  -- Assemble.
  calc ∑ r, ∫ t in (α r - δ / 2)..(α r + δ / 2), g t
      = ∑ r, ∫ t in Ioc (β r - δ / 2) (β r + δ / 2), g t := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hstep1 r, hstep2 r]
    _ = ∫ t in ⋃ r, Ioc (β r - δ / 2) (β r + δ / 2), g t := by
        rw [MeasureTheory.integral_iUnion (fun r => measurableSet_Ioc) hdisj hint_union,
          tsum_fintype]
    _ ≤ ∫ t in Ioc a (a + 1), g t := by
        refine setIntegral_mono_set hint_win ?_ (iUnion_subset hsub).eventuallyLE
        exact Filter.Eventually.of_forall (fun t => hg t)
    _ = ∫ t in a..(a + 1), g t := (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ t in (0:ℝ)..1, g t := by
        have hp : Function.Periodic g 1 := hper
        simpa using hp.intervalIntegral_add_eq a 0

end Salt.LS
