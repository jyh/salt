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
variable [Salt.Maynard.TupleChoice]

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

/-! ## B4.4c — the ρ-helpers at `ρ = 9999/40000` -/

/-- `log R ≤ (9999/40000)·log N'` (ρ-version of `logR_upper_theta`). -/
lemma logR_upper_rho (N' : ℕ) (hN' : 1 ≤ N') :
    Real.log (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ≤ (9999 / 40000 : ℝ) * Real.log N' := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ (9999 / 40000 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hx5ge1 : (1 : ℝ) ≤ x ^ (9999 / 40000 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hRle : (⌊x ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ≤ x ^ (9999 / 40000 : ℝ) := Nat.floor_le hx5pos.le
  have hRpos : (0 : ℝ) < (⌊x ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x ^ (9999 / 40000 : ℝ)⌋₊ := Nat.le_floor (by exact_mod_cast hx5ge1)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlog := Real.log_le_log hRpos hRle
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- `ρ·log N' ≤ log R` once `N'^{9999/40000 − ρ} ≥ 2` (ρ-version of `logR_lower_theta`). -/
lemma logR_lower_rho (ρ : ℝ) (hρ0 : 0 ≤ ρ) (N' : ℕ) (hN1 : 1 ≤ N')
    (hrest : (2 : ℝ) ≤ (N' : ℝ) ^ (9999 / 40000 - ρ : ℝ)) :
    ρ * Real.log N' ≤ Real.log (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN1
  have hxpos : (0 : ℝ) < x := by linarith
  set R := ⌊x ^ (9999 / 40000 : ℝ)⌋₊ with hR
  have hexp : ρ + (9999 / 40000 - ρ) = (9999 / 40000 : ℝ) := by ring
  have hsplit : x ^ (9999 / 40000 : ℝ) = x ^ (ρ : ℝ) * x ^ (9999 / 40000 - ρ : ℝ) := by
    rw [← Real.rpow_add hxpos, hexp]
  have hxρpos : (0 : ℝ) < x ^ (ρ : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hxρge1 : (1 : ℝ) ≤ x ^ (ρ : ℝ) := Real.one_le_rpow hx1 hρ0
  have hbig : 2 * x ^ (ρ : ℝ) ≤ x ^ (9999 / 40000 : ℝ) := by
    rw [hsplit]; nlinarith only [hrest, hxρpos]
  have hfloor : x ^ (9999 / 40000 : ℝ) - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one (x ^ (9999 / 40000 : ℝ)); rw [← hR] at this; linarith
  have hRge : x ^ (ρ : ℝ) ≤ (R : ℝ) := by linarith only [hfloor, hbig, hxρge1]
  have hlog := Real.log_le_log hxρpos hRge
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- eventually `ρ·log N' ≤ log R`, for any fixed `0 ≤ ρ < 9999/40000`. -/
lemma eventually_logR_lower_rho (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 9999 / 40000) :
    ∀ᶠ N' : ℕ in atTop,
      ρ * Real.log N' ≤ Real.log (⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by
  have hpos : (0 : ℝ) < 9999 / 40000 - ρ := by linarith
  have htend := tendsto_rpow_atTop hpos
  have hev := tendsto_natCast_atTop_atTop.eventually (htend.eventually_ge_atTop 2)
  filter_upwards [hev, eventually_ge_atTop 1] with N' h2 hN1
  exact logR_lower_rho ρ hρ0 N' hN1 h2

/-- `2 ≤ R = ⌊N'^{9999/40000}⌋` for `N' ≥ 32 = 2⁵` (`5·9999/40000 ≥ 1`). `N' ≥ 17` already suffices;
the θ-chain's threshold `8` does NOT (`16^{9999/40000} < 2`). -/
lemma R_ge_two_rho (N' : ℕ) (hN' : (32 : ℝ) ≤ (N' : ℝ)) :
    2 ≤ ⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ := by
  set x := (N' : ℝ) with hx
  have hge : (2 : ℝ) ≤ x ^ (9999 / 40000 : ℝ) := by
    have h2 : ((32 : ℝ)) ^ (9999 / 40000 : ℝ) ≤ x ^ (9999 / 40000 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hN' (by norm_num)
    have he : (2 : ℝ) ≤ ((32 : ℝ)) ^ (9999 / 40000 : ℝ) := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast 2 5,
        ← Real.rpow_mul (by norm_num)]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ ((5 : ℝ) * (9999 / 40000)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith [h2, he]
  exact Nat.le_floor (by exact_mod_cast hge)

/-- `R ≤ N'` for `N' ≥ 1`. -/
lemma R_le_N'_rho (N' : ℕ) (hN' : 1 ≤ N') :
    ⌊(N' : ℝ) ^ (9999 / 40000 : ℝ)⌋₊ ≤ N' := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hle : x ^ (9999 / 40000 : ℝ) ≤ x := by
    calc x ^ (9999 / 40000 : ℝ) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one _
  calc ⌊x ^ (9999 / 40000 : ℝ)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hle
    _ = N' := by rw [hx, Nat.floor_natCast]

end Salt.MaynardK
