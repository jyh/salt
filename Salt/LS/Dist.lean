/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# L0.2 — the mod-1 circle distance `dist₁`

Design: `docs/blueprints/largesieve.md`, "Carrier choices" and node `L0.2`.

`dist₁ x y` is the distance from `x - y` to the nearest integer, i.e. the
distance between `x` and `y` on the circle `ℝ / ℤ`. We implement it via
mathlib's `round` function rather than the `AddCircle` norm: `AddCircle`
carries its own quotient-type coercions (`UnitAddCircle.norm_eq` unfolds to
exactly `|x - round x|`, but only after passing through `(· : UnitAddCircle)`),
whereas the spec lemmas below all consume `x y : ℝ` directly, so the bare
`round`-based definition avoids coercion overhead. The key mathlib facts
driving every lemma here are `abs_sub_round` (`|t - round t| ≤ 1/2`) and
`round_le` (`round` minimizes `|t - m|` over `m : ℤ`, i.e.
`|t - round t| ≤ |t - m|` for every integer `m`).

The lemmas: `dist₁_self` and `dist₁_eq_zero_iff` (zero exactly at integer
differences), `dist₁_nonneg`, `dist₁_le_half`, `dist₁_le_abs`, `dist₁_comm`,
`dist₁_triangle`, and invariance under an integer shift of either argument
(`dist₁_add_int_left`, `dist₁_add_int_right`).
-/

namespace Salt.LS

/-- The mod-1 circle distance: the distance from `x - y` to the nearest
integer. -/
noncomputable def dist₁ (x y : ℝ) : ℝ := |x - y - round (x - y)|

/-- `dist₁ x x = 0`. -/
@[simp]
theorem dist₁_self (x : ℝ) : dist₁ x x = 0 := by simp [dist₁]

/-- `0 ≤ dist₁ x y`. -/
theorem dist₁_nonneg (x y : ℝ) : 0 ≤ dist₁ x y := abs_nonneg _

/-- `dist₁ x y ≤ 1 / 2`: the distance to the nearest integer is at most a half
(mathlib's `abs_sub_round`). -/
theorem dist₁_le_half (x y : ℝ) : dist₁ x y ≤ 1 / 2 := abs_sub_round (x - y)

/-- `dist₁ x y ≤ |x - y|`: the circle distance is at most the real distance. -/
theorem dist₁_le_abs (x y : ℝ) : dist₁ x y ≤ |x - y| := by
  unfold dist₁
  simpa using round_le (x - y) 0

/-- `dist₁ x y = dist₁ y x`. -/
theorem dist₁_comm (x y : ℝ) : dist₁ x y = dist₁ y x := by
  have h1 : dist₁ x y ≤ dist₁ y x := by
    have := round_le (x - y) (-round (y - x))
    have he : x - y - ((-round (y - x) : ℤ) : ℝ) = -(y - x - round (y - x)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  have h2 : dist₁ y x ≤ dist₁ x y := by
    have := round_le (y - x) (-round (x - y))
    have he : y - x - ((-round (x - y) : ℤ) : ℝ) = -(x - y - round (x - y)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  exact le_antisymm h1 h2

/-- `dist₁ (x + n) y = dist₁ x y` for every integer `n`. -/
theorem dist₁_add_int_left (x y : ℝ) (n : ℤ) : dist₁ (x + n) y = dist₁ x y := by
  unfold dist₁
  have hxy : x + (n : ℝ) - y = (x - y) + (n : ℝ) := by ring
  rw [hxy, round_add_intCast]
  congr 1
  push_cast
  ring

/-- `dist₁ x (y + n) = dist₁ x y` for every integer `n`. -/
theorem dist₁_add_int_right (x y : ℝ) (n : ℤ) : dist₁ x (y + n) = dist₁ x y := by
  rw [dist₁_comm x (y + n), dist₁_add_int_left y x n, dist₁_comm]

/-- The triangle inequality `dist₁ x z ≤ dist₁ x y + dist₁ y z`. -/
theorem dist₁_triangle (x y z : ℝ) : dist₁ x z ≤ dist₁ x y + dist₁ y z := by
  unfold dist₁
  have h1 : |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| :=
    round_le (x - z) (round (x - y) + round (y - z))
  have h2 : x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)
      = (x - y - round (x - y)) + (y - z - round (y - z)) := by push_cast; ring
  calc |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| := h1
    _ = |(x - y - round (x - y)) + (y - z - round (y - z))| := by rw [h2]
    _ ≤ |x - y - round (x - y)| + |y - z - round (y - z)| := abs_add_le _ _

/-- `dist₁ x y = 0 ↔ ∃ n : ℤ, x - y = n`: the circle distance vanishes exactly when
`x - y` is an integer. -/
theorem dist₁_eq_zero_iff (x y : ℝ) : dist₁ x y = 0 ↔ ∃ n : ℤ, x - y = n := by
  unfold dist₁
  rw [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round (x - y), h⟩
  · rintro ⟨n, hn⟩
    rw [hn, round_intCast]

end Salt.LS
