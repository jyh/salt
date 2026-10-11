/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.EHLevelTheta

/-!
# C1 · B4.4b — the level range at θ = 1/2 with window exponent `9999/40000`

`Salt.Maynard.EH_range_theta` with `1999/4000 → 9999/40000`, `3999/4000 → 1/2` and the exponent
slack `1/4000 → 1/20000` (`1/2 − 2·9999/40000 = 1/20000`).
-/

namespace Salt.MaynardK

open Salt.Maynard

open Finset Filter

lemma R_sq_le_half (N' : ℕ) (hN' : 1 ≤ N') :
    (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ (19998 / 40000 : ℝ) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ (9999 / 40000 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hRle : (⌊x ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ≤ x ^ (9999 / 40000 : ℝ) := Nat.floor_le hx5pos.le
  have hRnn : (0 : ℝ) ≤ (⌊x ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by positivity
  calc (⌊x ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (x ^ (9999 / 40000 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hRnn hRle 2
    _ = x ^ (19998 / 40000 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (9999 / 40000 : ℝ)) 2, ← Real.rpow_mul hxpos.le]; norm_num

theorem level_range_half (W' : ℕ) (hW' : 0 < W') (B' : ℝ) (hB'0 : 0 ≤ B') :
    ∃ Nr : ℕ, ∀ N' : ℕ, Nr ≤ N' →
      W' * (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊) ^ 2
        ≤ ⌊(N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B'⌋₊ := by
  have hWpos : (0 : ℝ) < (W' : ℝ) := by exact_mod_cast hW'
  have hev := eventually_poly_beats_polylog ⌈B'⌉₊ ((1 : ℝ) / 20000) (W' : ℝ) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  obtain ⟨Nr0, hNr0⟩ := eventually_atTop.mp hevN
  refine ⟨max Nr0 3, fun N' hN' => ?_⟩
  have hNr0le : Nr0 ≤ N' := le_trans (le_max_left _ _) hN'
  have hN3 : 3 ≤ N' := le_trans (le_max_right _ _) hN'
  have hpoly : (W' : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ ≤ (N' : ℝ) ^ ((1 : ℝ) / 20000) :=
    hNr0 N' hNr0le
  have hx1 : (1 : ℝ) < (N' : ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hxpos : (0 : ℝ) < (N' : ℝ) := by linarith
  have hlogx : 0 < Real.log N' := Real.log_pos hx1
  have hdom : (Real.log N') ^ B' ≤ (1 + Real.log N') ^ ⌈B'⌉₊ := by
    calc (Real.log N') ^ B' ≤ (1 + Real.log N') ^ B' :=
          Real.rpow_le_rpow hlogx.le (by linarith) hB'0
      _ ≤ (1 + Real.log N') ^ (⌈B'⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil B')
      _ = (1 + Real.log N') ^ ⌈B'⌉₊ := Real.rpow_natCast _ _
  have hWlog : (W' : ℝ) * (Real.log N') ^ B' ≤ (N' : ℝ) ^ ((1 : ℝ) / 20000) := by
    calc (W' : ℝ) * (Real.log N') ^ B'
        ≤ (W' : ℝ) * (1 + Real.log N') ^ ⌈B'⌉₊ :=
          mul_le_mul_of_nonneg_left hdom hWpos.le
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 20000) := hpoly
  have hR2 : (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ (19998 / 40000 : ℝ) :=
    R_sq_le_half N' (by omega)
  have hmul : (W' : ℝ) * (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2
      ≤ (N' : ℝ) ^ (1 / 2 : ℝ) / (Real.log N') ^ B' := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogx B')]
    calc (W' : ℝ) * (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2 * (Real.log N') ^ B'
        = (W' : ℝ) * (Real.log N') ^ B' * (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2 := by ring
      _ ≤ (N' : ℝ) ^ ((1 : ℝ) / 20000) * (N' : ℝ) ^ (19998 / 40000 : ℝ) :=
          mul_le_mul hWlog hR2 (by positivity) (by positivity)
      _ = (N' : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
  apply Nat.le_floor
  push_cast
  exact hmul

/-! ## Eventual range-monotonicity at θ★ (`range_haircut_mono_theta`) -/

end Salt.MaynardK
