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

/-- **⟦gate 7 AT THE INFLATED CAP⟧** (`arc36_of_floor_h`) — `arc36_of_floor` with the arc read
at `h · arcDen 12 H`.

⛔ **`arcFloor36` CANNOT CARRY THIS.** The landed floor `10^138` clears `(128·72^36)² ≈
8.76·10^137` by a factor of only **1.14**, so the `h³` the inflated cap introduces breaks it at
`h = 2`. The route here is the same one, at the constant `128·1096³·72^36 ≈ 1.23·10^78`, whose
square `≈ 1.52·10^156` needs a floor of `10^157` — which `loglogFloor50 = ⌈e^{e^50}⌉₊` supplies
with room that is not a factor but a tower. -/
theorem arc36_of_floor_h {h H : ℕ} (hcb : (h : ℝ) ^ 3 ≤ 1316532736)
    (hH : (10 : ℕ) ^ 157 ≤ H) :
    128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
  have hHR : ((10 : ℝ) ^ (157 : ℕ)) ≤ (H : ℝ) := by exact_mod_cast hH
  have h10 : (0 : ℝ) < (10 : ℝ) ^ (157 : ℕ) := by positivity
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
  have hC0 : (0 : ℝ) ≤ 128 * 1316532736 * 72 ^ (36 : ℕ) := by positivity
  have hbig : (128 : ℝ) * 1316532736 * 72 ^ (36 : ℕ) ≤ Real.sqrt (H : ℝ) := by
    have hCsq : ((128 : ℝ) * 1316532736 * 72 ^ (36 : ℕ)) ^ (2 : ℕ) ≤ (H : ℝ) := by
      refine le_trans ?_ hHR
      norm_num
    calc (128 : ℝ) * 1316532736 * 72 ^ (36 : ℕ)
        = Real.sqrt (((128 : ℝ) * 1316532736 * 72 ^ (36 : ℕ)) ^ (2 : ℕ)) :=
          (Real.sqrt_sq hC0).symm
      _ ≤ Real.sqrt (H : ℝ) := Real.sqrt_le_sqrt hCsq
  have hcube : ((h : ℝ) * arcDen 12 H) ^ 3 = (h : ℝ) ^ 3 * Real.log (H : ℝ) ^ (36 : ℕ) := by
    rw [arcDen_twelve_eq_pow]; ring
  have hL36 : (0 : ℝ) ≤ Real.log (H : ℝ) ^ (36 : ℕ) := by positivity
  rw [hcube]
  calc (128 : ℝ) * ((h : ℝ) ^ 3 * Real.log (H : ℝ) ^ (36 : ℕ))
      ≤ 128 * (1316532736 * (72 ^ (36 : ℕ) * Real.sqrt (H : ℝ))) := by
        have := mul_le_mul hcb hA hL36 (by norm_num : (0 : ℝ) ≤ 1316532736)
        linarith [this]
    _ = ((128 : ℝ) * 1316532736 * 72 ^ (36 : ℕ)) * Real.sqrt (H : ℝ) := by ring
    _ ≤ Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) := mul_le_mul_of_nonneg_right hbig hs0
    _ = (H : ℝ) := hsq

/-- ⟦gate 7⟧ in the shape the register's binder reads it: a floor on `R.Hlo` discharges the
whole window range. -/
theorem arc36_of_regime {R : ChowlaRegime} (hfloor : arcFloor36 ≤ R.Hlo) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ) :=
  fun _ hlo _ => arc36_of_floor (le_trans hfloor hlo)

/-- **⟦gate 7 AT THE RAISED CAP⟧** (`arc36_of_floor_h_14`) — `arc36_of_floor_h` at
`log h ≤ 14`, i.e. `h ≤ 1202604 = ⌊e^{14}⌋`.  BODY: the sibling's, with the two SIGNATURE
numerals lifted and NOTHING else touched.

⛔ **BOTH numerals move and only ONE of them is forced.**  The cube bound is forced:
`1202604³ = 1 739 273 708 594 844 864` against the landed `1096³ = 1 316 532 736`.  The floor is
**CHOSEN**: `(128·1202604³·72^{36})² ≈ 2.649·10^{174}`, so `10^{175}` is the smallest round power
that clears it — and `10^{174}` genuinely REFUSES (kernel-checked in both directions).
⭐ **THE LIFT IS FREE.**  `arc36_of_regime_h_14` pays this floor off `loglogFloor50` through the
same `e³ ≥ 10` step the landed lane uses; at `10^{175}` the exponent it needs is `525` against
`e^{50} ≈ 5.18·10^{21}`.  *Ask of every numeral: chosen, or forced?*  `10^{157}` was chosen, and
the landed sibling's own docstring said why — **the room is a tower, not a factor.**

📌 **THE PLACEMENT IS PINNED, NOT PREFERRED.**  The body calls `log_le_rpow_inv_72`, which is
`private` to this module and therefore invisible outside it, so the twin cannot live beside its
consumer without de-privatising a landed lemma.  Recorded because a cost model that counts
DECLARATIONS does not model where a twin may LIVE. -/
theorem arc36_of_floor_h_14 {h H : ℕ} (hcb : (h : ℝ) ^ 3 ≤ 1739273708594844864)
    (hH : (10 : ℕ) ^ 175 ≤ H) :
    128 * ((h : ℝ) * arcDen 12 H) ^ 3 ≤ (H : ℝ) := by
  have hHR : ((10 : ℝ) ^ (175 : ℕ)) ≤ (H : ℝ) := by exact_mod_cast hH
  have h10 : (0 : ℝ) < (10 : ℝ) ^ (175 : ℕ) := by positivity
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
  have hC0 : (0 : ℝ) ≤ 128 * 1739273708594844864 * 72 ^ (36 : ℕ) := by positivity
  have hbig : (128 : ℝ) * 1739273708594844864 * 72 ^ (36 : ℕ) ≤ Real.sqrt (H : ℝ) := by
    have hCsq : ((128 : ℝ) * 1739273708594844864 * 72 ^ (36 : ℕ)) ^ (2 : ℕ) ≤ (H : ℝ) := by
      refine le_trans ?_ hHR
      norm_num
    calc (128 : ℝ) * 1739273708594844864 * 72 ^ (36 : ℕ)
        = Real.sqrt (((128 : ℝ) * 1739273708594844864 * 72 ^ (36 : ℕ)) ^ (2 : ℕ)) :=
          (Real.sqrt_sq hC0).symm
      _ ≤ Real.sqrt (H : ℝ) := Real.sqrt_le_sqrt hCsq
  have hcube : ((h : ℝ) * arcDen 12 H) ^ 3 = (h : ℝ) ^ 3 * Real.log (H : ℝ) ^ (36 : ℕ) := by
    rw [arcDen_twelve_eq_pow]; ring
  have hL36 : (0 : ℝ) ≤ Real.log (H : ℝ) ^ (36 : ℕ) := by positivity
  rw [hcube]
  calc (128 : ℝ) * ((h : ℝ) ^ 3 * Real.log (H : ℝ) ^ (36 : ℕ))
      ≤ 128 * (1739273708594844864 * (72 ^ (36 : ℕ) * Real.sqrt (H : ℝ))) := by
        have := mul_le_mul hcb hA hL36 (by norm_num : (0 : ℝ) ≤ 1739273708594844864)
        linarith [this]
    _ = ((128 : ℝ) * 1739273708594844864 * 72 ^ (36 : ℕ)) * Real.sqrt (H : ℝ) := by ring
    _ ≤ Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) := mul_le_mul_of_nonneg_right hbig hs0
    _ = (H : ℝ) := hsq

end Salt.MR

end
