/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.OpPlumb
import Salt.Goldbach.D0Win2
import Salt.Chen.AssembleA3b

/-!
# G-KERRY — the Y-variant sym-band price at the single middle piece (Goldbach A₃ sym leg)

The sym-band leg (`gold_band_hsym`, `BandPrice.lean`) prices each survivor against
`blockPrimeInd (max (opY N) (pieceN k'))`.  On the ONE middle piece `k'` where
`2^{k'} ≤ opY N < 2^{k'+1}`, the `max` does NOT collapse to `pieceN k'` — it is `opY N` — so the
landed `gold_box_rows_wide` collapse (which prices at `blockPrimeInd (pieceN k')`, `log 2^{k'}`)
does not apply.  This file supplies the missing middle-piece supplier, the Goldbach mirror of the
twin's `boxPriceKerrY` chain (`Salt.Chen.middle_medium_box_price_at_y` / `boxPriceKerrY`,
`AssembleA3b.lean`) at the Goldbach band geometry.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* **`goldBoxPriceKerrY`** — the Y-variant closed box price, the twin's `boxPriceKerrY` (the Kerr
  price at `log (opY N)` instead of `log 2^{k'}`), reused at the Goldbach band scale.
* **`gold_kerrY_engine`** — the two-cutoff (`T₂ = goldCut N (ka+1)`, `T₁ = goldCut N ka`) box price
  at the middle-piece sym survivor (indicator `blockPrimeInd (max (opY N) (pieceN k'))`, collapsed
  to `blockPrimeInd (opY N)`), `≤ goldBoxPriceKerrY Kc (opY N) k' i`.  The Goldbach mirror of
  `gold_box_rows_wide`: the geometry rows re-derived at the transferred `pieceN`-boundary, the band
  `D0`-window from `gold_d0_window_z` at `Nb := opY N`, the SW couplings at `logN := log (opY N)`,
  the generic pricer `medium_survivor_price_sqrtD` applied at `N := opY N` (NO `pieceN → 2^{k'}`
  bridge — the sum is already `blockPrimeInd (opY N)`).
* **`gold_boxPriceKerrY_geo` / `gold_boxPriceKerrY_geoN` / `gold_kerrY_hbox_geoN`** — the geometric
  conversion, the Y-mirror of `gold_boxPriceKerr_geo` / `gold_boxPriceKerr_geoN` /
  `gold_box_hbox_geoN`: `goldBoxPriceKerrY Kc (opY N) k' i ≤ (3^{12}·gboxConst)·Kc·goldCut N (ka+1)/
  (log N)^{12}` on wide (LIVE-HIGH) middle-piece survivors — the crumb-free `hgeo` grade the sym
  band's `gold_band_hsym` consumes.  (The firing / LIVE-LOW branch adds the min-form crumb
  `goldBtailMin`, routed by G-SURV-2 exactly as the box leg's `goldBtailMinSlot` — see the
  byte-lock.)

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. The numeric engine (local mirrors of `RowsWide §0`'s `private` toolkit) -/

/-- `(27/10)^n ≤ N^c` whenever `n ≤ c·10⁹` (`c > 0`), at `log N ≥ 10⁹`.  Mirror of
`gold_const_le_rpow_w`. -/
private theorem kerrY_const_le_rpow {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hn : (n : ℝ) ≤ c * 10 ^ 9) : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ c := by
  have hmul : c * (10 ^ 9 : ℝ) ≤ c * Real.log N := mul_le_mul_of_nonneg_left hlogN hc.le
  calc ((27 : ℝ) / 10) ^ n ≤ Real.exp (n : ℝ) := a12_pow27_le_exp n
    _ ≤ Real.exp (c * Real.log N) := Real.exp_le_exp.mpr (by linarith [hn, hmul])
    _ = (N : ℝ) ^ c := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

/-- `C·N^a ≤ N^b` for `a < b`, `C ≤ (27/10)^n ≤ N^{b−a}`.  Mirror of `gold_mono_close_w`. -/
private theorem kerrY_mono_close {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {a b C : ℝ} {n : ℕ} (hab : a < b)
    (hC : C ≤ ((27 : ℝ) / 10) ^ n) (hnc : (n : ℝ) ≤ (b - a) * 10 ^ 9) :
    C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have hstep : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ (b - a) :=
    kerrY_const_le_rpow hNpos hlogN (by linarith) n hnc
  have hann : (0 : ℝ) ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
  calc C * (N : ℝ) ^ a ≤ ((27 : ℝ) / 10) ^ n * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hC hann
    _ ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hstep hann
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- `L^E ≤ 262144·N^{1/2000}` for `0 ≤ E ≤ 18`, `0 ≤ L ≤ 2·log N`.  Mirror of `gold_Lpow_le_w`. -/
private theorem kerrY_Lpow_le {N : ℕ} {L : ℝ} (hlogN1 : 1 ≤ Real.log N)
    (hL0 : 0 ≤ L) (hLle : L ≤ 2 * Real.log N)
    (hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000))
    {E : ℝ} (hE0 : 0 ≤ E) (hE18 : E ≤ 18) :
    L ^ E ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
  have h218 : (2 : ℝ) ^ (18 : ℝ) = 262144 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc L ^ E ≤ (2 * Real.log N) ^ E := Real.rpow_le_rpow hL0 hLle hE0
    _ = (2 : ℝ) ^ E * (Real.log N) ^ E := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ (18 : ℝ) * (Real.log N) ^ (18 : ℝ) := by
        refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE18)
          (Real.rpow_le_rpow_of_exponent_le hlogN1 hE18)
          (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
        rw [h218]; exact mul_le_mul_of_nonneg_left hpl (by norm_num)

/-! ## 1. The Y-variant closed box price -/

/-- **`goldBoxPriceKerrY`** — the Y-variant closed box price at the single middle piece.  The twin's
`boxPriceKerrY` (the Kerr price at `log y` in place of `log 2^{k'}`), reused verbatim at the
Goldbach band scale (`X_sub = 2^{i+1}−1`, `M = pieceM k'`).  Priced against `blockPrimeInd y` where
`y := opY N` sits inside the piece (`pieceN k' < y ≤ pieceM k'`). -/
noncomputable def goldBoxPriceKerrY (Kc : ℝ) (y kp i : ℕ) : ℝ := boxPriceKerrY Kc y kp i

/-- `goldBoxPriceKerrY` is nonnegative when `Kc ≥ 0` and `1 ≤ y`. -/
theorem goldBoxPriceKerrY_nonneg {Kc : ℝ} (hKc : 0 ≤ Kc) (y kp i : ℕ) (hy : 1 ≤ y) :
    0 ≤ goldBoxPriceKerrY Kc y kp i := boxPriceKerrY_nonneg hKc y kp i hy

/-! ## 2. The geometric conversion (the crumb-free `hgeo` grade for `gold_band_hsym`)

The Y-mirror of `GeoSum.gold_boxPriceKerr_geo` / `GeoSum2.gold_boxPriceKerr_geoN` /
`OpPlumb.gold_box_hbox_geoN`.  Because `boxPriceKerrY` differs from `boxPriceKerr` ONLY by
`Real.log (2^{k'})` ↦ `Real.log y`, the worst-c ratio bound `kerr_ratio_term_le` (at
`hratio : (10/31)·L ≤ log y`) applies unchanged, so the whole `/L^{12}` grade transfers verbatim. -/

set_option maxHeartbeats 1600000 in
-- the `boxPriceKerrY` unfold carries a long rpow-bearing bracket; the Kerr-minima bounds
-- (`kerr_ratio_term_le`), the bracket fold, and the `field_simp`/`ring` closes need headroom.
/-- **`gold_boxPriceKerrY_geo` (the local `/L^{12}` grade).**  Mirror of `gold_boxPriceKerr_geo` at
the `y`-indicator: at a Goldbach annulus box (`X·M ≤ 4·goldCut N (ka+1)`) with `Kc ≥ 1`, `1 ≤ L`,
and the worst-c ratio `(10/31)·L ≤ log y`, `goldBoxPriceKerrY Kc y kp i ≤ gboxConst·Kc·goldCut
N (ka+1)/
L^{12}` (`L := log(X·M)`). -/
theorem gold_boxPriceKerrY_geo {N z yb K y kp ka i : ℕ} {Kc : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (z * yb) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log (y : ℝ)) :
    goldBoxPriceKerrY Kc y kp i
      ≤ gboxConst * Kc * (goldCut N (ka + 1) : ℝ)
          / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (12 : ℝ) := by
  have hXM4gN : (2 ^ (i + 1) - 1 : ℕ) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi).2
  unfold goldBoxPriceKerrY boxPriceKerrY gboxConst
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) with hXMdef
  set L : ℝ := Real.log XM with hLdef
  set logN : ℝ := Real.log (y : ℝ) with hlogNdef
  have hXM4x : XM ≤ 4 * (goldCut N (ka + 1) : ℝ) := by
    rw [hXMdef]; exact_mod_cast hXM4gN
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXM1 : (1 : ℝ) ≤ XM := by
    have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM1 : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp
      have : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [hXMdef]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) :=
          mul_le_mul (by exact_mod_cast hX1) (by exact_mod_cast hM1) (by norm_num) (by positivity)
  have hXM0 : (0 : ℝ) ≤ XM := le_trans (by norm_num) hXM1
  have hKc0 : (0 : ℝ) ≤ Kc := by linarith
  set S : ℝ := Kc * (((31 : ℝ) / 10) ^ (50 : ℝ) * L) with hSdef
  have hterm : ∀ a e : ℝ, a ≤ 1 + e → 0 ≤ e → e ≤ 50 →
      Kc * (L ^ a / logN ^ e) ≤ S := by
    intro a e hae he0 he50
    rw [hSdef]
    exact mul_le_mul_of_nonneg_left (kerr_ratio_term_le hL1 hratio hae he0 he50) hKc0
  have hkb : Kbeta_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkm : Km_min Kc L logN 13 18 ≤ S := by
    rw [Km_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkb' : Kbeta'_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta'_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hrpow1 : (1 : ℝ) ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hrL : (1 : ℝ) ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) * L := by nlinarith [hrpow1, hL1]
  have hSge1 : (1 : ℝ) ≤ S := by rw [hSdef]; nlinarith [hKc, hrL]
  have h26 : 32 * Real.sqrt 26 ≤ 192 := by
    have hs : Real.sqrt 26 ≤ 6 := by
      have h1 : Real.sqrt 26 ≤ Real.sqrt 36 := Real.sqrt_le_sqrt (by norm_num)
      have h2 : Real.sqrt 36 = 6 := by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith [h1, h2]
    linarith [hs]
  have h218 : (2 : ℝ) ^ ((13 : ℝ) + 5) = 262144 := by
    rw [show (13 : ℝ) + 5 = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hbracket : Kbeta_min Kc L logN 13 18
        + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1))
      ≤ 281352 * S := by
    rw [h218]; nlinarith [hkb, hkm, hkb', h26, hSge1]
  set BR : ℝ := Kbeta_min Kc L logN 13 18
      + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
        + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1)) with hBRdef
  have hL13pos : (0 : ℝ) < L ^ (13 : ℝ) := Real.rpow_pos_of_pos hLpos 13
  have hL12pos : (0 : ℝ) < L ^ (12 : ℝ) := Real.rpow_pos_of_pos hLpos 12
  have hL13 : L ^ (13 : ℝ) = L ^ (12 : ℝ) * L := by
    rw [show (13 : ℝ) = 12 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  have hstep1 : 2 * (BR * XM / L ^ (13 : ℝ)) ≤ (2 * (281352 * S)) * XM / L ^ (13 : ℝ) := by
    rw [show 2 * (BR * XM / L ^ (13 : ℝ)) = ((2 * BR) * XM) / L ^ (13 : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hL13pos).mpr
      (mul_le_mul_of_nonneg_right (by linarith [hbracket]) hXM0)
  have hLHSeq : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
      = 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ) := by
    rw [hSdef, hL13]; field_simp; ring
  have hc0 : (0 : ℝ) ≤ 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc := by positivity
  have hstep2 : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
      ≤ 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ) := by
    rw [hLHSeq]
    calc 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ)
        = (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc) * (XM / L ^ (12 : ℝ)) := by ring
      _ ≤ (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc)
            * (4 * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hL12pos).mpr hXM4x) hc0
      _ = 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ) := by
          ring
  exact le_trans hstep1 hstep2

set_option maxHeartbeats 1600000 in
-- the `gold_boxPriceKerrY_geo` application + the rpow→Nat-pow bridge + the denominator
-- monotonicity close carry a long rpow chain; headroom above the default heartbeat budget.
/-- **`gold_boxPriceKerrY_geoN` (the outer `/(log N)^{12}` grade).**  Mirror of
`gold_boxPriceKerr_geoN`: from `gold_boxPriceKerrY_geo` and the live-box outer ratio
`log N ≤ cr·log(X·M)`, `goldBoxPriceKerrY Kc y kp i ≤ (cr^{12}·gboxConst)·Kc·goldCut N (ka+1)/
(log N)^{12}`. -/
theorem gold_boxPriceKerrY_geoN {N z yb K y kp ka i : ℕ} {Kc cr : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (z * yb) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log (y : ℝ))
    (hlogN0 : 0 < Real.log N) (_hcr : 1 ≤ cr)
    (hNXM : Real.log N ≤ cr * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) :
    goldBoxPriceKerrY Kc y kp i
      ≤ (cr ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) with hXMdef
  have h1 := gold_boxPriceKerrY_geo (N := N) (z := z) (yb := yb) (K := K) (y := y) hKc hi hL1 hratio
  have hconv : (Real.log XM) ^ (12 : ℝ) = (Real.log XM) ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← hXMdef, hconv] at h1
  have hlogXMpos : (0 : ℝ) < Real.log XM := lt_of_lt_of_le one_pos hL1
  have hA : (0 : ℝ) ≤ gboxConst * Kc * (goldCut N (ka + 1) : ℝ) :=
    mul_nonneg (mul_nonneg gboxConst_nonneg (by linarith)) (Nat.cast_nonneg _)
  have hbridge : gboxConst * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log XM) ^ 12
      ≤ (cr ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmono : (Real.log N) ^ 12 ≤ (cr * Real.log XM) ^ 12 :=
      pow_le_pow_left₀ hlogN0.le hNXM 12
    calc gboxConst * Kc * (goldCut N (ka + 1) : ℝ) * (Real.log N) ^ 12
        ≤ gboxConst * Kc * (goldCut N (ka + 1) : ℝ) * (cr * Real.log XM) ^ 12 :=
          mul_le_mul_of_nonneg_left hmono hA
      _ = cr ^ 12 * gboxConst * Kc * (goldCut N (ka + 1) : ℝ) * (Real.log XM) ^ 12 := by
          rw [mul_pow]; ring
  exact le_trans h1 hbridge

/-- **`gold_kerrY_hbox_geoN`** — the composed op-scale grade.  At a LIVE middle-piece box
(`2^{k'} ≤ opY N`, so `log 2^{k'} ≤ log (opY N)`), `goldBoxPriceKerrY Kc (opY N) k' i ≤
(3^{12}·gboxConst)·Kc·goldCut N (ka+1)/(log N)^{12}` — the exact crumb-free `hgeo` summand of the
sym band's `gold_band_hsym` (`Cgeo := 3^{12}·gboxConst`, `Btail := 0`).  `gold_box_live_ratios`
supplies
the box ratio `(10/31)·L ≤ log 2^{k'}`, lifted to `log (opY N)` by `2^{k'} ≤ opY N`. -/
theorem gold_kerrY_hbox_geoN {Kc : ℝ} (hKc : 1 ≤ Kc) : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K : ℕ),
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka)
        (goldCut N (ka + 1)) (opZ N * opY N) K →
      2 ^ i < opZ N * pieceN kp + 1 →
      2 ^ kp ≤ opY N →
      goldBoxPriceKerrY Kc (opY N) kp i
        ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  obtain ⟨xs, hs⟩ := gold_box_live_ratios
  obtain ⟨xt, ht⟩ := gold_op_scales
  refine ⟨max xs xt, fun N hN kp ka i K hi hlive hlo => ?_⟩
  have hxs : xs ≤ N := le_trans (le_max_left _ _) hN
  have hxt : xt ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hL1, hratio2kp, hNXM⟩ := hs N hxs kp ka i K hi hlive
  have hlogN0 : 0 < Real.log N := by have := (ht N hxt).2.2.2.2.2.2.1; linarith
  -- lift the box ratio `(10/31)·L ≤ log 2^{k'}` to `log (opY N)` via `2^{k'} ≤ opY N`
  have hloglift : Real.log ((2 ^ kp : ℕ) : ℝ) ≤ Real.log (opY N : ℝ) := by
    have h2kppos : (0 : ℝ) < ((2 ^ kp : ℕ) : ℝ) := by positivity
    exact Real.log_le_log h2kppos (by exact_mod_cast hlo)
  have hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
      ≤ Real.log (opY N : ℝ) := le_trans hratio2kp hloglift
  exact gold_boxPriceKerrY_geoN (z := opZ N) (yb := opY N) hKc hi hL1 hratio hlogN0
    (by norm_num) hNXM

/-! ## 3. The Y-variant two-cutoff engine (the middle-piece sym survivor price) -/

set_option maxHeartbeats 4000000 in
-- the ~24-row wide-geometry discharge (mirror of `gold_box_rows_wide`) plus the band `D0`-window,
-- the SW couplings, and the 43-hypothesis generic pricer applied twice elaborate a long rpow/sqrt-
-- bearing chain; the whnf/defeq checks need headroom well above the default heartbeat budget.
/-- **`gold_kerrY_engine`.**  The Goldbach mirror of `gold_box_rows_wide` at the single middle piece
`kp` (`2^{kp} ≤ opY N < 2^{kp+1}`, so `max (opY N) (pieceN kp) = opY N`).  For a LIVE annulus box at
a WIDE per-annulus level (`w ≤ D`, `D·L^{18} ≤ √(X·M)`, `L := log(X·M)`, `X := 2^{i+1}−1`,
`M := pieceM kp`), the two-cutoff sym survivor price against
`blockPrimeInd (max (opY N) (pieceN kp))` is `≤ goldBoxPriceKerrY Kc (opY N) kp i`.  The geometry
rows are re-derived at the transferred `pieceN`-boundary (`gold_box_*` floors); the band `D0`-window
is `gold_d0_window_z` at `Nb := opY N`; the SW couplings are at `logN := log (opY N)`
(`Kbeta_min_coupling` &c.); the generic pricer `medium_survivor_price_sqrtD` is applied at
`N := opY N` (NO `pieceN → 2^{kp}` bridge — the sum is already `blockPrimeInd (opY N)`).  Only the
carrier/`Dset` rows (`hβ`/`hd1`/`hcop2`/`hDsetD`) remain, supplied by the assembly (G-SURV-2). -/
theorem gold_kerrY_engine : ∃ (Kc : ℝ) (x₁ : ℕ), 0 < Kc ∧
    ∀ (N : ℕ), x₁ ≤ N →
      ∀ (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (T₁ T₂ ka i K : ℕ),
        i ∈ dyadicBoundary (max (opY N) (pieceN kp)) (pieceM kp) (goldCut N ka)
          (goldCut N (ka + 1)) (opZ N * opY N) K →
        2 ^ kp ≤ opY N →
        opY N < 2 ^ (kp + 1) →
        2 ^ i < opZ N * pieceN kp + 1 →
        ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
        (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
        (∀ m, ‖β m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) → (∀ d ∈ Dset, d ≤ D) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (max (opY N) (pieceN kp)))
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (max (opY N) (pieceN kp)))
                (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
          ≤ goldBoxPriceKerrY Kc (opY N) kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ :=
    medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num) (by norm_num)
  obtain ⟨xs, hs⟩ := gold_op_scales
  obtain ⟨xz, hzrows⟩ := gold_box_zx_rows
  obtain ⟨xp, hp⟩ := a12_logpow_le_rpow 18 (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨Kc, max (max (max xs xz) xp) ((16 * N₀) ^ 3 + 1), hKc, ?_⟩
  intro N hN β kp D Dset r T₁ T₂ ka i K hi hlo hhi hlive hDge hDwide hβ hd1 hcop2 hDsetD
  -- collapse `max (opY N) (pieceN kp) = opY N` (in the goal and the boundary membership)
  have hpNle : pieceN kp ≤ opY N := by unfold pieceN; omega
  rw [max_eq_left hpNle] at hi ⊢
  -- transfer the `opY N`-boundary to the `pieceN kp`-boundary (corner monotone in `Ne`)
  have hi' : i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
      (opZ N * opY N) K := by
    rw [dyadicBoundary, Finset.mem_filter] at hi ⊢
    obtain ⟨hmem, hcorner, hfl, hcut⟩ := hi
    refine ⟨hmem, ?_, hfl, hcut⟩
    exact le_trans (Nat.mul_le_mul (le_refl (2 ^ i)) (by omega : pieceN kp + 1 ≤ opY N + 1)) hcorner
  have hxs : xs ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxz : xz ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxp : xp ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hbigN : (16 * N₀) ^ 3 + 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩ := hs N hxs
  obtain ⟨_, hz_ratio, hx⟩ := hzrows N hxz kp ka i K hi' hlive
  have hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := hp N hxp
  -- basic positivity + tower facts
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by linarith [hlogN]
  have hlogN9 : (10 : ℝ) ^ 9 ≤ Real.log N := by linarith [hlogN]
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  have h8zpos : (0 : ℝ) < 8 * (opZ N : ℝ) := by positivity
  have hgc1 : 1 ≤ goldCut N (ka + 1) := one_le_goldCut hN2 (ka + 1)
  have hgcPos : (0 : ℝ) < (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < goldCut N (ka + 1))
  -- `w := (goldCut/(8z))^{1/2}`, `w² = goldCut/(8z)`, `N^{1/3}/16 ≤ w ≤ 2^kp`
  set w : ℝ := ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) with hwdef
  have hwnn : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hwkf : w ≤ ((2 ^ kp : ℕ) : ℝ) := gold_kfloor_live_z hN2 hi' hlive
  have hwge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ w := gold_box_wge hN2 hZ1 hi' hlive hYhalf
  -- box-scale geometry
  have hXMlo_nat : goldCut N ka < (2 ^ (i + 1) - 1) * pieceM kp := (gold_box_XM_scale hi').1
  have hXMhi_nat : (2 ^ (i + 1) - 1) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi').2
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  have hXge : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
    gold_box_Xfloor (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hexp4000) hi'
  have hMfloor : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ (pieceM kp : ℝ) :=
    gold_box_Mfloor hN2 hZ1 hi' hlive hYhalf
  -- `X·M ≤ 2N`, real bounds
  have hXM2N : (2 ^ (i + 1) - 1) * pieceM kp ≤ 2 * N := by
    have := goldCut_le_half N (ka + 1); omega
  have hMge1 : (1 : ℝ) ≤ (pieceM kp : ℝ) := by
    have : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp; have := Nat.one_le_pow kp 2 (by norm_num); omega
    exact_mod_cast this
  have hXMpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hXpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by positivity
      linarith [hXge]
    positivity
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  -- `L` window: `2 ≤ L ≤ 2·log N`
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hXMloR : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    calc (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hXge
      _ = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
          apply mul_le_mul_of_nonneg_left hMge1; positivity
  have hlogval : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4)
      = 11 / 24 * Real.log N - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
  have hLlow : 11 / 24 * Real.log N - Real.log 4 ≤ L := by
    have hle : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4) ≤ L :=
      Real.log_le_log (by positivity) hXMloR
    rwa [hlogval] at hle
  have hL2 : (2 : ℝ) ≤ L := by linarith [hlogN, hlog4, hLlow]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hXMhiR : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 2 * (N : ℝ) := by
    have : ((2 ^ (i + 1) - 1) * pieceM kp : ℕ) ≤ 2 * N := hXM2N
    have hc : (((2 ^ (i + 1) - 1) * pieceM kp : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc ⊢; linarith [hc]
  have hLle : L ≤ 2 * Real.log N := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    have hlog : L ≤ Real.log (4 * (N : ℝ)) := Real.log_le_log hXMpos h4N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at hlog
    linarith [hlog, hlog4, hlogN1]
  have hLbb : L ≤ Real.log (4 * (N : ℝ)) := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    exact Real.log_le_log hXMpos h4N
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  -- `hk : 2 ≤ kp`
  have h2kp4 : (4 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
    linarith [hwge, hwkf]
  have hk : 2 ≤ kp := by
    by_contra hk2
    have : (2 : ℕ) ^ kp ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcast : ((2 ^ kp : ℕ) : ℝ) ≤ 2 := by
      have : ((2 ^ kp : ℕ) : ℝ) ≤ ((2 ^ 1 : ℕ) : ℝ) := by exact_mod_cast this
      simpa using this
    linarith [h2kp4, hcast]
  -- `hN₀ : N₀ ≤ 2^kp`
  have hN₀ : N₀ ≤ 2 ^ kp := by
    have hbigR : ((16 * N₀ : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hle : ((16 * N₀) ^ 3 : ℕ) ≤ N := by omega
      calc ((16 * N₀ : ℕ) : ℝ) ^ 3 = (((16 * N₀) ^ 3 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (N : ℝ) := by exact_mod_cast hle
    have hcube : ((16 * N₀ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have hmono := Real.rpow_le_rpow (by positivity) hbigR (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast ((16 * N₀ : ℕ) : ℝ) 3, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hmono
    have hchain : ((16 * N₀ : ℕ) : ℝ) ≤ 16 * ((2 ^ kp : ℕ) : ℝ) :=
      le_trans hcube (by linarith [hwge, hwkf])
    have hfin : ((N₀ : ℕ) : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
      have heq : ((16 * N₀ : ℕ) : ℝ) = 16 * ((N₀ : ℕ) : ℝ) := by push_cast; ring
      rw [heq] at hchain; linarith [hchain]
    exact_mod_cast hfin
  -- structural rows
  have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := by
    have h8 : (8 : ℝ) ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := by
      have h813 : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith [hN13_16]
      calc (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := h813
        _ ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have : (2 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by linarith [hXge, h8]
    exact_mod_cast this
  have hM2 : 2 ≤ pieceM kp := by
    have : (2 : ℝ) ≤ (pieceM kp : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
      linarith [hMfloor]
    exact_mod_cast this
  have hFX : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := by
    have := gold_box_Ffloor hi'; omega
  -- polylog rows (√X, √M floors)
  have hsqrtX : (N : ℝ) ^ ((11 : ℝ) / 48) / 2 ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    rw [show (N : ℝ) ^ ((11 : ℝ) / 48) / 2
        = Real.sqrt (((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h48 : ((N : ℝ) ^ ((11 : ℝ) / 48)) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((11 : ℝ) / 48)) 2, ← Real.rpow_mul hNpos.le,
        show (11 : ℝ) / 48 * ((2 : ℕ) : ℝ) = 11 / 24 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
      rw [div_pow, h48]; norm_num
    rw [hsq]; exact hXge
  have hsqrtM : (N : ℝ) ^ ((1 : ℝ) / 6) / 4 ≤ Real.sqrt (pieceM kp : ℝ) := by
    rw [show (N : ℝ) ^ ((1 : ℝ) / 6) / 4
        = Real.sqrt (((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h6 : ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 6)) 2, ← Real.rpow_mul hNpos.le,
        show (1 : ℝ) / 6 * ((2 : ℕ) : ℝ) = 1 / 3 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by
      rw [div_pow, h6]; norm_num
    rw [hsq]; exact hMfloor
  have hXsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    have hLpow : L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      kerrY_Lpow_le hlogN1 hL0 hLle hpl (by norm_num) (by norm_num)
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := by
      have hm := kerrY_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 11 / 48) (C := 524288)
        (n := 14) (by norm_num) (by norm_num) (by norm_num)
      linarith
    calc L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
      _ ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := htail
      _ ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hsqrtX
  have hMrow : ∀ E : ℝ, 0 ≤ E → E ≤ 18 → L ^ E ≤ Real.sqrt (pieceM kp : ℝ) := by
    intro E hE0 hE18
    have hLpow : L ^ E ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      kerrY_Lpow_le hlogN1 hL0 hLle hpl hE0 hE18
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / 4 := by
      have hm := kerrY_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 1 / 6) (C := 1048576)
        (n := 15) (by norm_num) (by norm_num) (by norm_num)
      linarith
    linarith [hLpow, htail, hsqrtM]
  have hMsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  have herr_Mlev : L ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  -- `hfloor`
  have hfloor : ((3 : ℝ) / Real.log 2) ^ 8 * (N : ℝ) ^ ((1 : ℝ) / 6)
      * (Real.log (4 * (N : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt ((opZ N * opY N : ℕ) : ℝ) :=
    row_hfloor hexp4000 rfl rfl
  -- ================= the SIX wide D-upper rows =================
  have h2kpge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ ((2 ^ kp : ℕ) : ℝ) := le_trans hwge hwkf
  have herr_lev : (D : ℝ) * L ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := hDwide
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hDscale : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
      / L ^ (15 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have h1518 : L ^ (15 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    calc (D : ℝ) * L ^ (15 : ℝ) ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) :=
          mul_le_mul_of_nonneg_left h1518 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  have hL18ge1 : (1 : ℝ) ≤ L ^ ((13 : ℝ) + 5) := by
    rw [show (1 : ℝ) = L ^ (0 : ℝ) from (Real.rpow_zero L).symm]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hDsqrtXM : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) := mul_le_mul_of_nonneg_left hL18ge1 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hXMge1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have hX2R : (2 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX2
      nlinarith [hX2R, hMge1]
    have hsqrtself : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h1 : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          ≤ Real.sqrt ((((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
              * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) :=
        Real.sqrt_le_sqrt (by nlinarith [hXMge1])
      rwa [Real.sqrt_mul_self hXMpos.le] at h1
    linarith [hDsqrtXM, hsqrtself]
  have hDx : (D : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hsqle : ((D : ℝ) * L ^ ((13 : ℝ) + 5)) * ((D : ℝ) * L ^ ((13 : ℝ) + 5))
        ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h := mul_le_mul herr_lev herr_lev (by positivity) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt hXMpos.le] at h
    have hL18ge2 : (2 : ℝ) ≤ L ^ ((13 : ℝ) + 5) * L ^ ((13 : ℝ) + 5) := by
      have h1le : L ^ (1 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      rw [Real.rpow_one] at h1le
      nlinarith [le_trans hL2 h1le, hL18ge1]
    have hDDN : (D : ℝ) * (D : ℝ) ≤ (N : ℝ) := by
      have hexp : ((D : ℝ) * L ^ ((13 : ℝ) + 5)) * ((D : ℝ) * L ^ ((13 : ℝ) + 5))
          = ((D : ℝ) * (D : ℝ)) * (L ^ ((13 : ℝ) + 5) * L ^ ((13 : ℝ) + 5)) := by ring
      rw [hexp] at hsqle
      nlinarith [hsqle, hL18ge2, hXMhiR, mul_nonneg hDnn hDnn]
    rw [show (D : ℝ) = Real.sqrt ((D : ℝ) * (D : ℝ)) from (Real.sqrt_mul_self hDnn).symm]
    exact Real.sqrt_le_sqrt hDDN
  have hDsq : D < (2 ^ kp + 1) * (2 ^ kp + 1) := by
    have hsqrt2N : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.sqrt (2 * (N : ℝ)) := Real.sqrt_le_sqrt hXMhiR
    have hkpnn : (0 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by positivity
    have hkpsq_lo : (N : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by
      have h13sq : ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16)
          = (N : ℝ) ^ ((2 : ℝ) / 3) / 256 := by
        rw [show (N : ℝ) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) by
          rw [← Real.rpow_add hNpos]; norm_num]; ring
      have h13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by positivity
      calc (N : ℝ) ^ ((2 : ℝ) / 3) / 256
          = ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) := h13sq.symm
        _ ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) :=
            mul_le_mul h2kpge h2kpge h13nn hkpnn
    have h2N_le : 2 * (N : ℝ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
        * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) := by
      have hstep : (134217728 : ℝ) * (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
        have := kerrY_mono_close hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 134217728)
          (n := 19) (by norm_num) (by norm_num) (by norm_num)
        exact this
      rw [Real.rpow_one] at hstep
      have h43 : (N : ℝ) ^ ((4 : ℝ) / 3)
          = ((N : ℝ) ^ ((2 : ℝ) / 3)) * ((N : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [← Real.rpow_add hNpos]; norm_num
      have hexp : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
          = (N : ℝ) ^ ((4 : ℝ) / 3) / 65536 := by rw [h43]; ring
      rw [hexp]; linarith [hstep]
    have hsqrt2N_le : Real.sqrt (2 * (N : ℝ)) ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by
      have h1 : Real.sqrt (2 * (N : ℝ))
          ≤ Real.sqrt (((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)) :=
        Real.sqrt_le_sqrt h2N_le
      rw [Real.sqrt_mul_self (by positivity)] at h1
      linarith [h1, hkpsq_lo]
    have hDreal : (D : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) :=
      le_trans hDsqrtXM (le_trans hsqrt2N hsqrt2N_le)
    have hDnat : D ≤ 2 ^ kp * 2 ^ kp := by exact_mod_cast hDreal
    have hm : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
    nlinarith [hDnat, hm]
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ (D : ℝ) := by
      have h1w : (1 : ℝ) ≤ w := by
        have : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
        linarith [hwge]
      linarith [hDge, h1w]
    exact_mod_cast this
  have hDleN : (D : ℝ) ≤ (N : ℝ) := by
    have hself : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * (N : ℝ)) :=
        Real.sqrt_le_sqrt (by nlinarith [hN1R])
      rwa [Real.sqrt_mul_self hNpos.le] at h1
    linarith [hDx, hself]
  have hlogD : Real.log D ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [hlogN1]
    · exact Real.log_le_log (by exact_mod_cast hDpos) hDleN
  have hlogNle7L : Real.log N ≤ 7 * L := by nlinarith [hLlow, hlog4, hL2, hlogN1]
  have habs : 4 * (1 + Real.log D) * (D : ℝ)
      ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have h14le18 : L ^ (14 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hDL14 : (D : ℝ) * L ^ (14 : ℝ)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left h14le18 hDnn) herr_lev
    have hL14eq : L ^ (14 : ℝ) = L * L ^ (13 : ℝ) := by
      rw [show (14 : ℝ) = 1 + 13 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
    have hcoef : 4 * (1 + Real.log D) ≤ 32 * L := by nlinarith [hlogD, hlogNle7L, hL1]
    have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
    have hstep1 : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
        ≤ 32 * ((D : ℝ) * L ^ (14 : ℝ)) := by
      rw [hL14eq]
      nlinarith [hcoef, hDnn, hL13nn, mul_nonneg hDnn hL13nn]
    have hMnn : (0 : ℝ) ≤ (pieceM kp : ℝ) := by positivity
    have hBnn : (0 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by positivity
    have hAnn : (0 : ℝ) ≤ 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
      positivity
    have hkpMlo : (N : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h13sq : ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16)
          = (N : ℝ) ^ ((2 : ℝ) / 3) / 256 := by
        rw [show (N : ℝ) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) by
          rw [← Real.rpow_add hNpos]; norm_num]; ring
      have h13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by positivity
      calc (N : ℝ) ^ ((2 : ℝ) / 3) / 256
          = ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) := h13sq.symm
        _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := mul_le_mul h2kpge hMfloor h13nn (by positivity)
    have hAAle : (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
        * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
        ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
      have hAAeq : (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
          * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
          = 1024 * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
        rw [show (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
            * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
            = 1024 * (Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
                * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) by ring,
          Real.mul_self_sqrt hXMpos.le]
      rw [hAAeq]
      have hBBlo : 2048 * (N : ℝ)
          ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
        have hkpMlo2 : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
            ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
          mul_le_mul hkpMlo hkpMlo (by positivity) hBnn
        have h2N_le : 2048 * (N : ℝ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
            * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) := by
          have hstep : (137438953472 : ℝ) * (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
            have := kerrY_mono_close hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 137438953472)
              (n := 27) (by norm_num) (by norm_num) (by norm_num)
            exact this
          rw [Real.rpow_one] at hstep
          have h43 : (N : ℝ) ^ ((4 : ℝ) / 3)
              = ((N : ℝ) ^ ((2 : ℝ) / 3)) * ((N : ℝ) ^ ((2 : ℝ) / 3)) := by
            rw [← Real.rpow_add hNpos]; norm_num
          have hexp : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
              = (N : ℝ) ^ ((4 : ℝ) / 3) / 65536 := by rw [h43]; ring
          rw [hexp]; linarith [hstep]
        linarith [hkpMlo2, h2N_le]
      nlinarith [hXMhiR, hBBlo]
    have hAle : 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h1 := Real.sqrt_le_sqrt hAAle
      rwa [Real.sqrt_mul_self hAnn, Real.sqrt_mul_self hBnn] at h1
    calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
        ≤ 32 * ((D : ℝ) * L ^ (14 : ℝ)) := hstep1
      _ ≤ 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
          mul_le_mul_of_nonneg_left hDL14 (by norm_num)
      _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := hAle
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      L ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) := by
    intro e he2 heD heX
    linarith [herr_scale e he2 heD heX, hL2]
  -- ================= the middle-piece Y-indicator specialisations =================
  -- the band `D0`-window at `Nb := opY N`
  have hfloorN : ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (opY N : ℝ) :=
    le_trans hwkf (by exact_mod_cast hlo)
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_z (Ne := N) (Nb := opY N) (M := pieceM kp) (X := 2 ^ (i + 1) - 1) (k := ka)
      (z := opZ N) hx hZ1 hz_ratio hfloorN hXMlo_nat hXMhi_nat
  have hD0lo_main : L ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : L ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_lo
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      (D0 : ℝ) ≤ (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_scale hDge)
  -- the indicator-specific rows at `N := opY N`
  have hy1R : (1 : ℝ) < (opY N : ℝ) := by exact_mod_cast (by omega : 1 < opY N)
  have hlogYpos : (0 : ℝ) < Real.log (opY N : ℝ) := Real.log_pos hy1R
  have hN₀Y : N₀ ≤ opY N := le_trans hN₀ hlo
  have hM2NY : pieceM kp ≤ 2 * opY N := by
    have h1 : pieceM kp ≤ 2 * 2 ^ kp := pieceM_le_two_pow kp
    omega
  have hNM : (opY N : ℝ) ≤ (pieceM kp : ℝ) := by
    have : opY N ≤ pieceM kp := by unfold pieceM; omega
    exact_mod_cast this
  have hDsqY : D < (opY N + 1) * (opY N + 1) := hDsq_of_carrier_floor hlo hDsq
  have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
  have habsY : 4 * (1 + Real.log D) * (D : ℝ)
      ≤ (opY N : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
    refine le_trans habs ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have h2kyR : ((2 ^ kp : ℕ) : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hlo
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2kyR (Nat.cast_nonneg _)) (inv_nonneg.mpr hL13nn)
  -- the SW couplings at `logN := log (opY N)`
  have hcoupG : Kc * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min Kc L (Real.log (opY N : ℝ)) 13 18
          * (Real.log (opY N : ℝ)) ^ ((13 : ℝ) + 2 * 18) := Kbeta_min_coupling hlogYpos
  have hcoup3 : Kc * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min Kc L (Real.log (opY N : ℝ)) 13 18
          * (Real.log (opY N : ℝ)) ^ ((13 : ℝ) + 2 * 18) := Km_min_coupling hlogYpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      Kc * (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)))
            ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min Kc L (Real.log (opY N : ℝ)) 13 18
            * (Real.log (opY N : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18) := fun e _ _ =>
    Kbeta'_min_coupling hKc.le hlogYpos (log_efold_nonneg (2 ^ (i + 1) - 1) (pieceM kp) e)
      (log_efold_le (2 ^ (i + 1) - 1) (pieceM kp) e) (by norm_num)
  -- the nonneg minima
  have hKβnn : 0 ≤ Kbeta_min Kc L (Real.log (opY N : ℝ)) 13 18 :=
    Kbeta_min_nonneg hKc.le hL0 hlogYpos.le
  have hKmnn : 0 ≤ Km_min Kc L (Real.log (opY N : ℝ)) 13 18 :=
    Km_min_nonneg hKc.le hL0 hlogYpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min Kc L (Real.log (opY N : ℝ)) 13 18 :=
    Kbeta'_min_nonneg hKc.le hL0 hlogYpos.le
  -- the single-cutoff price at `N := opY N` (NO `pieceN → 2^kp` bridge)
  have hone : ∀ T : ℕ,
      (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (opY N))
            (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T‖)
        ≤ (Kbeta_min Kc L (Real.log (opY N : ℝ)) 13 18
              + (6 * (Km_min Kc L (Real.log (opY N : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L (Real.log (opY N : ℝ)) 13 18
                    + 15360 + 1)))
            * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) / L ^ (13 : ℝ) := fun T =>
    hbody (N : ℝ) (Real.log (4 * (N : ℝ))) (opZ N * opY N) β (2 ^ (i + 1) - 1) (opY N) (pieceM kp)
      T D0 D k0 (Nat.log 2 D) Dset r (Kbeta_min Kc L (Real.log (opY N : ℝ)) 13 18)
      (Km_min Kc L (Real.log (opY N : ℝ)) 13 18) (Kbeta'_min Kc L (Real.log (opY N : ℝ)) 13 18) 15
      hβ hKβnn hKmnn hKβ'nn hN₀Y hM2NY hd_N hd1 hcop2 hL1 hd_hi hd_N' hNM hD1 hDsetD hDsqY habsY
      hX2 hM2 (by norm_num) (by norm_num) hd_eq hd_2 hD0D rfl hDscale hD0lo_main hXsqrt hMsqrt
      herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM herr_scale hcoupG
      hcoup3 herr_book4
  -- the two-cutoff sum = `2 · (single)` = `goldBoxPriceKerrY Kc (opY N) kp i`
  unfold goldBoxPriceKerrY boxPriceKerrY
  rw [two_mul]
  exact add_le_add (hone T₂) (hone T₁)

/-! ## 4. Byte-lock — the middle-piece slot shape (the G-SURV-2 handoff) -/

section ByteLock

-- THIS FILE's deliverables
#check @Salt.Goldbach.goldBoxPriceKerrY
#check @Salt.Goldbach.gold_kerrY_engine
#check @Salt.Goldbach.gold_boxPriceKerrY_geo
#check @Salt.Goldbach.gold_boxPriceKerrY_geoN
#check @Salt.Goldbach.gold_kerrY_hbox_geoN
-- The consumer slot (`BandPrice.goldSymSurvSum`, owned by the concurrent band executor; NOT
-- imported here to avoid a cross-dependency): on the middle piece it carries
-- `blockPrimeInd (max (opY N) (pieceN k'))` at reduced top `2^{i+1}−1`, cutoffs
-- `goldCut N (k+1)` / `goldCut N k` — EXACTLY `gold_kerrY_engine`'s two-cutoff LHS, at
-- `β := goldSymSub …`, `r := crtClassG Q (·/Q) N a`, `T₂ := goldCut N (k+1)`, `T₁ := goldCut N k`.
-- The `gold_band_hsym` `hgeo` grade `goldSymSurvSum ≤ Cgeo·Kc·goldCut N (k+1)/(log N)^{12}` is
-- discharged, on the wide middle-piece survivors, by `gold_kerrY_engine` then
-- `gold_kerrY_hbox_geoN` (`Cgeo := 3^{12}·gboxConst`).  The firing (LIVE-LOW, non-wide) branch: it
-- routes into a separate additive `Final.goldBtailMinSlot`-analog term, exactly as the box leg's
-- `Final.goldPriceMin` / `Final.gold_box_hprice_at_min` handle their LIVE-LOW boxes.
-- the box-leg pattern this mirrors (LIVE-HIGH wide price + the `/(log N)^{12}` grade)
#check @Salt.Goldbach.gold_box_rows_wide
#check @Salt.Goldbach.gold_box_hbox_geoN

end ByteLock

end Salt.Goldbach
