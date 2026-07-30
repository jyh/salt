/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Spine

/-!
# ⟦S1-ARC36⟧ — the second road's window floor `128·(arcDen 12 H)³ ≤ H`

`M4SecondRoad.m4_second_road`'s ⟦gate 7⟧ is

  `128·(arcDen 12 H)^3 ≤ H`,   i.e.   `128·(log H)^{36} ≤ H`,

the ONE `H`-LOWER of the register (every other `H`-conjunct is an upper or an envelope floor
on witnessed data).  `M4Spine` §1 already carries the twelfth-power version
(`eight_arcDen_le_of_arcFloor`, at `m4ArcFloor = 10^36`); this file is that page transplanted
at the 36th power, which is what the road's `harc3` binder actually asks.

⟦THE ROUTE⟧ one application of `log u ≤ u − 1` at `u = t^{1/72}` gives `log t ≤ 72·t^{1/72}`;
raised to the 36th power, `(log t)^{36} ≤ 72^{36}·√t`; and the floor is where
`128·72^{36} ≤ √t`.  `128·72^{36} ≈ 9.36·10^{68}`, so the route costs `≈ 8.76·10^{137}` and
`arcFloor36 = 10^{138}` clears it with a factor `1.14`.

PURELY ADDITIVE: no landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-- One application of `log u ≤ u − 1` at `u = t^{1/72}`: `log t ≤ 72·t^{1/72}`.  The
`log_le_rpow_inv_24` of `M4Spine` §1 at the exponent the 36th power needs. -/
private lemma log_le_rpow_inv_72 {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 72 * t ^ ((1 : ℝ) / 72) := by
  have hp : (0 : ℝ) < t ^ ((1 : ℝ) / 72) := Real.rpow_pos_of_pos ht _
  have h1 : Real.log (t ^ ((1 : ℝ) / 72)) ≤ t ^ ((1 : ℝ) / 72) - 1 :=
    Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow ht] at h1
  linarith

/-- **THE 36th-POWER ARC FLOOR** — `10^138`, the window length past which
`128·(log H)^{36} ≤ H`.  SHAPE, not a claim of optimality: `(128·72^{36})² ≈ 8.76·10^{137}`
is what the route costs, and `10^{138}` clears it with a factor `1.14`. -/
def arcFloor36 : ℕ := 10 ^ 138

/-- **⟦gate 7⟧ AT THE FLOOR** (`arc36_of_floor`) — `M4SecondRoad.m4_second_road`'s `harc3`
binder, for every window length past `arcFloor36`. -/
theorem arc36_of_floor {H : ℕ} (hH : arcFloor36 ≤ H) :
    128 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
  have hHR : ((10 : ℝ) ^ (138 : ℕ)) ≤ (H : ℝ) := by
    have h : (10 : ℕ) ^ (138 : ℕ) ≤ H := hH
    exact_mod_cast h
  have h10 : (0 : ℝ) < (10 : ℝ) ^ (138 : ℕ) := by positivity
  have ht : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le h10 hHR
  have ht1 : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
  have hL0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg ht1
  have hstep : Real.log (H : ℝ) ≤ 72 * (H : ℝ) ^ ((1 : ℝ) / 72) := log_le_rpow_inv_72 ht
  have hhalf : ((H : ℝ) ^ ((1 : ℝ) / 72)) ^ (36 : ℕ) = Real.sqrt (H : ℝ) := by
    rw [← Real.rpow_natCast ((H : ℝ) ^ ((1 : ℝ) / 72)) 36, ← Real.rpow_mul ht.le,
      Real.sqrt_eq_rpow]
    norm_num
  have hA : Real.log (H : ℝ) ^ (36 : ℕ) ≤ 72 ^ (36 : ℕ) * Real.sqrt (H : ℝ) := by
    calc Real.log (H : ℝ) ^ (36 : ℕ) ≤ (72 * (H : ℝ) ^ ((1 : ℝ) / 72)) ^ (36 : ℕ) := by
          gcongr
      _ = 72 ^ (36 : ℕ) * ((H : ℝ) ^ ((1 : ℝ) / 72)) ^ (36 : ℕ) := by rw [mul_pow]
      _ = 72 ^ (36 : ℕ) * Real.sqrt (H : ℝ) := by rw [hhalf]
  have hsq : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) := Real.mul_self_sqrt ht.le
  have hs0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hbig : (128 : ℝ) * 72 ^ (36 : ℕ) ≤ Real.sqrt (H : ℝ) := by
    have hval : (128 : ℝ) * 72 ^ (36 : ℕ)
        = 935793105480040924823351433001552287293685885912463639574246785548288 := by
      norm_num
    rw [hval]
    have hle : (935793105480040924823351433001552287293685885912463639574246785548288 : ℝ)
        ^ (2 : ℕ) ≤ (H : ℝ) := by
      refine le_trans ?_ hHR
      norm_num
    calc (935793105480040924823351433001552287293685885912463639574246785548288 : ℝ)
        = Real.sqrt ((935793105480040924823351433001552287293685885912463639574246785548288 : ℝ)
            ^ (2 : ℕ)) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (H : ℝ) := Real.sqrt_le_sqrt hle
  have hcube : arcDen 12 H ^ 3 = Real.log (H : ℝ) ^ (36 : ℕ) := by
    rw [arcDen_twelve_eq_pow]; ring
  rw [hcube]
  nlinarith [hA, hbig, hsq, hs0]

/-- ⟦gate 7⟧ in the shape the register's binder reads it: a floor on `R.Hlo` discharges the
whole window range. -/
theorem arc36_of_regime {R : ChowlaRegime} (hfloor : arcFloor36 ≤ R.Hlo) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ) :=
  fun _ hlo _ => arc36_of_floor (le_trans hfloor hlo)

end Salt.MR

end
