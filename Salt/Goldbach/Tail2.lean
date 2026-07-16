/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Tail

/-!
# G-TAIL — the LIVE-LOW carrier bridge (Goldbach terminal, part II)

Part I (`Tail.lean`) landed the elementary count content: the per-modulus trivial bound
`gold_box_disc_trivial` (item 1) and the `QImage` harmonic sum `gold_box_tail_le` (item 2).

This file lands the **carrier bridge** — the plug of items 1+2 into the EXACT two-cutoff box carrier
that the terminal `gold_hBVblocksW_discharge'` (`PDiag.lean:511`) names in its `hprice` slot:

* **`gold_box_carrier_tail`** — for a LIVE-LOW box at the operating point (where the wide window
  `√(X·M)/L^18` fell below the conductor, so `gold_box_rows_wide`'s `hDwide` is unavailable and the
  smooth-divisor route is closed), the one-sided windowed carrier sum over the `QImage` moduli is
  bounded by the crude harmonic tail.  The coefficient norms `‖restrictAlpha (restrictAlpha
  (blockAlpha ..) ..) ..‖ ≤ 1` and `‖blockPrimeInd ..‖ ≤ 1` feed `gold_box_disc_trivial` per
  modulus; the `crtClassG` coprimality (`gold_crtClassG_coprime_of_mem`) supplies the `R`-unit
  hypothesis; `gold_box_tail_le` closes the `QImage` sum.
* **`gold_box_price_tail`** — the two-cutoff (`goldCut N (k+1)` and `goldCut N k`) sum, the EXACT
  `hprice`-slot LHS, bounded by `2×` the single-cutoff tail.  This is the LIVE-LOW branch value the
  piecewise `Btail` of `gold_hSum_geo`'s `htail` slot consumes.

## Residual (flagged) — the full terminal wiring

The full terminal `gold_hBVblocksW_at_op` (item 3) — the piecewise `hprice`/`hSum` composition
(`gold_box_hprice_op` on DEAD/LIVE-HIGH + this bridge on LIVE-LOW), the `htail` margin close (the
`¬hDwide ⟹ X·M < opD²·L^36 ≤ N^{1−2ε}·L^36` annulus-size derivation summed over the `O(log N)`
annuli against `N/(log N)^{11}` at the tower margins `e^{180000}`, `N^{1/16}`), and the slot wiring
(`hiX`, the band `hpriceSym`/`hpriceLow` via `gold_band_hsym_slot`, `hCE := gold_op_hCE`,
`hNum := gold_hNum_close_of_tower`) — is the remaining integration.  See `docs/blueprints/flags.md`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## The LIVE-LOW carrier bridge -/

open Classical in
set_option maxHeartbeats 800000 in
-- The per-modulus `gold_box_disc_trivial` application (two `restrictAlpha` norm folds + the
-- `crtClassG` coprimality row) and the `gold_box_tail_le` close elaborate a long carrier chain;
-- headroom above the default.
/-- **`gold_box_carrier_tail`.**  The one-sided windowed carrier sum over the `QImage` moduli
`m = Q·d` (`d ∣ Ps`, `d < QR·Dlev`) is bounded by the crude harmonic tail — the LIVE-LOW branch
that `gold_box_rows_wide` cannot cover.  Character-for-character the summand shape of the terminal
`hprice` slot (`gold_hBVblocksW_discharge'`) at one cutoff `T`. -/
theorem gold_box_carrier_tail (N z y : ℕ) (ε₀ : ℝ) (j k' Q a Ps : ℕ) (QR : ℝ) (Dlev T : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) (i : ℕ) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m T‖)
      ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * (pieceM k' : ℝ) * (QR * Dlev) := by
  have hinner : ∀ m, ‖restrictAlpha (blockAlpha z y ε₀ j) 0
      (min (z * pieceN k' + 1) (N / 2 + 1)) m‖ ≤ 1 :=
    fun m => norm_restrictAlpha_le_one (fun m' => norm_blockAlpha_le_one z y ε₀ j m') 0 _ m
  have halpha : ∀ m, ‖restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
      (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)) m‖ ≤ 1 :=
    fun m => norm_restrictAlpha_le_one hinner (2 ^ i) (2 ^ (i + 1)) m
  have hbeta : ∀ n, ‖blockPrimeInd (pieceN k') n‖ ≤ 1 := blockPrimeInd_norm_le_one (pieceN k')
  refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
    (gold_box_tail_le (2 ^ (i + 1) - 1) (pieceM k') Q Ps (QR * Dlev) hQ1 hb)
  have hcop : Nat.Coprime (crtClassG Q (m / Q) N a) m :=
    gold_crtClassG_coprime_of_mem (QR * Dlev) hQ1 hQPs hQNa hPsN hm
  have hm1 : 1 ≤ m := by
    obtain ⟨d, hd, hmd⟩ := Finset.mem_image.mp hm
    have hdp : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hpos : 0 < Q * d := Nat.mul_pos (by omega) hdp
    rw [← hmd]; exact hpos
  exact gold_box_disc_trivial halpha hbeta hm1 hcop

open Classical in
set_option maxHeartbeats 800000 in
-- Two applications of `gold_box_carrier_tail` (one per cutoff) plus the additive combine.
/-- **`gold_box_price_tail`.**  The two-cutoff carrier sum — the EXACT `hprice`-slot LHS of
`gold_hBVblocksW_discharge'` — at a LIVE-LOW box, bounded by `2×` the single-cutoff harmonic tail.
This is the value the piecewise `Btail k' k i` of `gold_hSum_geo`'s `htail` slot takes on LIVE-LOW
boxes; on DEAD / LIVE-HIGH boxes `gold_box_hprice_op` supplies `≤ boxPriceKerr` instead. -/
theorem gold_box_price_tail (N z y : ℕ) (ε₀ : ℝ) (j k' k Q a Ps : ℕ) (QR : ℝ) (Dlev i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ 2 * (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * (pieceM k' : ℝ) * (QR * Dlev)) := by
  have h1 := gold_box_carrier_tail N z y ε₀ j k' Q a Ps QR Dlev (goldCut N (k + 1))
    hQPs hQNa hPsN hQ1 hb i
  have h2 := gold_box_carrier_tail N z y ε₀ j k' Q a Ps QR Dlev (goldCut N k)
    hQPs hQNa hPsN hQ1 hb i
  linarith [h1, h2]

/-! ## Byte-locks: the bridge matches the terminal carrier -/

section ByteLock

-- item 1 / item 2 — the elementary count content
#check @Salt.Goldbach.gold_box_disc_trivial
#check @Salt.Goldbach.gold_box_tail_le
-- the LIVE-LOW carrier bridge (this file)
#check @Salt.Goldbach.gold_box_carrier_tail
#check @Salt.Goldbach.gold_box_price_tail
-- the DEAD / LIVE-HIGH branch this composes against (OpPlumb, landed)
#check @Salt.Goldbach.gold_box_hprice_op
-- the geometric `hSum` slot whose `htail` the piecewise `Btail` feeds
#check @Salt.Goldbach.gold_hSum_geo
-- the terminal whose `hprice` slot the piecewise composition fills
#check @Salt.Goldbach.gold_hBVblocksW_discharge'

end ByteLock

end Salt.Goldbach
