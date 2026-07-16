/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.GeoSum
import Salt.Goldbach.RowsWide

/-!
# G-GEOSUM — the geometric-sum final pricing (Goldbach), part II: (iv) the hprice composition

Design: the adjudicated redesign, deliverables (iv)+(v).  Part I (`GeoSum.lean`) landed the three
geometric keystones (i) `gold_boxPriceKerr_geo` (`boxPriceKerr ≤ gboxConst·Kc·goldCut/(logX·M)^12`),
(ii) `gold_goldCut_geosum` (`Σ_k goldCut N (k+1) ≤ 8·N`), (iii) `gold_hSum_geo` (the geometric
`hSum` slot at `(48·Cgeo + Ctail + 3·Ccon_band + Ccon_diag/2)·Kc·N/(log N)^{11}`).

This file lands **(iv) the hprice→aggregate bridge**, the concrete content that connects (i) to
(iii):

* **`gold_boxPriceKerr_geoN`** — the OUTER-scale conversion: `boxPriceKerr Kc kp i ≤
  Cgeo·Kc·goldCut N (ka+1)/(log N)^{12}` with `Cgeo := cr^{12}·gboxConst`, from (i) plus the
  live-box outer ratio `log N ≤ cr·log(X·M)` (`gold_box_rows_wide` establishes
  `11/24·log N − log 4 ≤ L` at op, so `cr ≈ 24/11` works).  EXACTLY the aggregate `hbox` summand.
  Chained after a box's `disc-sum ≤ boxPriceKerr` (from `gold_box_rows_wide` at LIVE-high /
  `gold_box_price_dead_kerr` at DEAD) it discharges `gold_hSum_geo`'s `hbox` slot at `Btail := 0`.
* **`gold_hSum_geo_slot`** — the byte-lock: `gold_hSum_geo`'s conclusion IS the terminal's `hSum`
  slot (`gold_hBVblocksW_discharge'`, `PDiag.lean:552`), character-for-character.

The LIVE-LOW trivial tail (the `Btail` crumb) and the full terminal instantiation (v) remain the
honest residual — see the report / flags.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## (iv) The outer-scale bridge: `boxPriceKerr` → the aggregate `hbox` summand -/

set_option maxHeartbeats 1600000 in
-- the (i) application + the rpow→Nat-pow bridge + the denominator monotonicity close carry a long
-- rpow chain; headroom above the default heartbeat budget.
/-- **`gold_boxPriceKerr_geoN` (iv) — the outer-scale per-annulus price.**  From the local-scale (i)
`boxPriceKerr Kc kp i ≤ gboxConst·Kc·goldCut N (ka+1)/(log X·M)^{12}` and the live-box OUTER ratio
`log N ≤ cr·log(X·M)` (with `cr ≥ 1`; at op `gold_box_rows_wide` gives `L ≥ 11/24·log N − log 4`, so
`cr ≈ 24/11`), the price is bounded at the OUTER scale:
`boxPriceKerr Kc kp i ≤ (cr^{12}·gboxConst)·Kc·goldCut N (ka+1)/(log N)^{12}` — the exact summand
`gold_hSum_geo`'s `hbox` slot consumes (`Cgeo := cr^{12}·gboxConst`). -/
theorem gold_boxPriceKerr_geoN {N z y K kp ka i : ℕ} {Kc cr : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (z * y) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log ((2 ^ kp : ℕ) : ℝ))
    (hlogN0 : 0 < Real.log N) (_hcr : 1 ≤ cr)
    (hNXM : Real.log N ≤ cr * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) :
    boxPriceKerr Kc kp i
      ≤ (cr ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) with hXMdef
  have h1 := gold_boxPriceKerr_geo (N := N) (z := z) (y := y) (K := K) hKc hi hL1 hratio
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

/-! ## (v-structural) The `hSum`-slot byte-lock -/

section ByteLock

/-- **`gold_hSum_geo_slot` — the byte-lock.**  `gold_hSum_geo`'s conclusion is, character-for-
character, the `hSum` slot `gold_hBVblocksW_discharge'` consumes (`PDiag.lean:552-559`): the box
quadruple sum + the band single sums + `(1/2)·Pdiag`, per block `j`.  This `example` restates that
slot VERBATIM as its goal and closes it with `gold_hSum_geo` — so the geometric aggregate drops into
the terminal's `hSum` position with `RHD := (48·Cgeo + Ctail + 3·Ccon_band + Ccon_diag/2)·Kc·N/
(log N)^{11}`. -/
example (N z y K : ℕ) (ε₀ : ℝ) (Kc : ℝ)
    (Price : ℕ → ℕ → ℕ → ℕ → ℝ) (PsymK PlowK : ℕ → ℕ → ℝ) (Btail : ℕ → ℕ → ℕ → ℝ)
    (Pdiag Wband Cgeo Ctail Ccon_band Ccon_diag : ℝ)
    (hmax : maxBlock N z ε₀ = 0)
    (hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log N)
    (hWband0 : 0 ≤ Wband) (hCgeo0 : 0 ≤ Cgeo) (hCband0 : 0 ≤ Ccon_band)
    (hgeosum : (∑ k ∈ Finset.range (Nat.log 2 N + 1), (goldCut N (k + 1) : ℝ)) ≤ 8 * (N : ℝ))
    (hbox : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K,
          Price 0 k' k i ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k' k i)
    (htail : (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Btail k' k i)
        ≤ Ctail * Kc * (N : ℝ) / (Real.log N) ^ 11)
    (hsym : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k' ≤ Wband)
    (hlow : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k' ≤ Wband)
    (hWband : Wband ≤ Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
    (hPdiag : Pdiag ≤ Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11)
    (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N) :
    (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        ((∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price j k' k i)
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK j k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK j k')
             + (1 / 2) * Pdiag)))
      ≤ (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / (Real.log N) ^ 11 :=
  gold_hSum_geo N z y K ε₀ Kc Price PsymK PlowK Btail Pdiag Wband Cgeo Ctail Ccon_band Ccon_diag
    hmax hKc0 hlogpos hWband0 hCgeo0 hCband0 hgeosum hbox htail hsym hlow hWband hPdiag hcount

-- the geometric keystones (Part I) the bridge feeds
#check @Salt.Goldbach.gold_boxPriceKerr_geo
#check @Salt.Goldbach.gold_goldCut_geosum
#check @Salt.Goldbach.gold_hSum_geo
-- the box-price suppliers the bridge chains after (LIVE-high / DEAD)
#check @Salt.Goldbach.gold_box_rows_wide
#check @Salt.Goldbach.gold_box_price_dead_kerr
-- THIS FILE's bridge
#check @Salt.Goldbach.gold_boxPriceKerr_geoN
-- the terminal whose `hSum` slot `gold_hSum_geo` fills (byte-locked above)
#check @Salt.Goldbach.gold_hBVblocksW_discharge'

end ByteLock

end Salt.Goldbach
