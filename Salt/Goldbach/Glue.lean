/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.OpPlumb
import Salt.Goldbach.Tail2
import Salt.Goldbach.DSplit

/-!
# G-GLUE — the terminal-glue composition (Goldbach terminal, part I)

The piecewise per-box price `goldPrice` and the two slots of `gold_hBVblocksW_discharge'`
(`PDiag.lean:511`) it fills:

* **`goldPrice`** — the piecewise price mirroring the twin's FIN-A3c: `0` on a DEAD box
  (empty carrier, `min (opZ N·pieceN k'+1) (N/2+1) ≤ 2^i`), `boxPriceKerr` on a LIVE-HIGH box
  (the wide window `D·L^18 ≤ √(X·M)` holds), and `boxPriceKerr + goldBtail` on a LIVE-LOW box
  (the wide window fails; the trivial harmonic tail).
* **`gold_box_hprice_at`** — the terminal's `hprice` slot at `Price := goldPrice`, the 3-way case
  split compiled: DEAD via `gold_box_price_vanish`, LIVE-HIGH via `gold_box_hprice_op`, LIVE-LOW
  via `gold_box_price_tail` (+ `boxPriceKerr_nonneg`).
* **`gold_box_hbox_at`** — the `hbox` summand of `gold_hSum_geo`: `goldPrice 0 k' k i ≤
  Cgeo·Kc·goldCut N (k+1)/(log N)^12 + Btail k' k i` (via `gold_box_hbox_geoN` on LIVE boxes; the
  Kerr-nonneg trivial fill on DEAD boxes).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The piecewise per-box price -/

/-- **`goldBtail`** — the LIVE-LOW branch value: `gold_box_price_tail`'s RHS, the crude two-cutoff
harmonic tail `2·(2·X·M/Q·(1+log bnd) + 2·M·bnd)` (`X := 2^{i+1}−1`, `M := pieceM k'`, `bnd :=
QR·Dlev`). -/
noncomputable def goldBtail (Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  2 * (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
      + 2 * (pieceM k' : ℝ) * bnd)

open Classical in
/-- **`goldPrice`** — the piecewise per-box price (`j`-independent).  DEAD → `0`; LIVE-HIGH (wide
window `D·L^18 ≤ √(X·M)`) → `boxPriceKerr Kc k' i`; LIVE-LOW (wide fails) →
`boxPriceKerr Kc k' i + goldBtail Q bnd k' i`. -/
noncomputable def goldPrice (Kc : ℝ) (N D Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  if min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i then 0
  else boxPriceKerr Kc k' i
    + (if (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
       then 0
       else goldBtail Q bnd k' i)

/-! ## 2. The per-box `hprice` discharge (the terminal's `hprice` slot at `goldPrice`) -/

set_option maxHeartbeats 800000 in
-- the LIVE-HIGH branch applies the QImage-specialized `gold_box_hprice_op` (whose carrier defeq
-- check is heavy) and the LIVE-LOW branch the `gold_box_price_tail` unfold; headroom above default.
/-- **`gold_box_hprice_at` (item 1).**  The terminal's `hprice` slot (`gold_hBVblocksW_discharge'`,
`PDiag.lean:511`) at `Price j k' k i := goldPrice Kc N D Q (QR·Dlev) k' i`, the 3-way case split
compiled.  DEAD (`min (opZ N·pieceN k'+1) (N/2+1) ≤ 2^i`): the carrier vanishes
(`gold_box_price_vanish`), `Price = 0`.  LIVE-HIGH (the wide window `D·L^18 ≤ √(X·M)` holds):
`gold_box_hprice_op` at level `D` (with `hDge`/`hDsetD` supplied), `Price = boxPriceKerr`.  LIVE-LOW
(wide fails): `gold_box_price_tail`, `Price = boxPriceKerr + goldBtail ≥ goldBtail`.  `Kc := max Kc₀
1 ≥ 1` (the `gold_box_hprice_op` constant). -/
theorem gold_box_hprice_at : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (j k' k i K Q a D Ps Dlev : ℕ) (QR : ℝ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      1 ≤ QR * Dlev →
      i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K →
      ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
      (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), d ≤ D) →
      (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
              (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
        + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
        ≤ goldPrice Kc N D Q (QR * Dlev) k' i := by
  classical
  obtain ⟨Kc, x₁, hKc, hop⟩ := gold_box_hprice_op
  refine ⟨Kc, x₁, hKc, ?_⟩
  intro N hN ε₀ j k' k i K Q a D Ps Dlev QR hQPs hQNa hPsN hQ1 hb hi hDge hDsetD
  unfold goldPrice
  by_cases hcap : min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i
  · rw [if_pos hcap]
    exact le_of_eq (gold_box_price_vanish hcap _)
  · rw [if_neg hcap]
    by_cases hwide : (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
        ^ ((13 : ℝ) + 5) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
    · rw [if_pos hwide, add_zero]
      exact hop N hN ε₀ j k' k i K Q a D Ps Dlev QR k
        hQPs hQNa hPsN hQ1 hi hDge hwide hDsetD
    · rw [if_neg hwide]
      have htail := gold_box_price_tail N (opZ N) (opY N) ε₀ j k' k Q a Ps QR Dlev i
        hQPs hQNa hPsN hQ1 hb
      have hnn : (0 : ℝ) ≤ boxPriceKerr Kc k' i :=
        boxPriceKerr_nonneg (le_trans zero_le_one hKc) k' i
      unfold goldBtail
      linarith [htail]

/-! ## 3. The `hbox` threading (the `hbox` summand of `gold_hSum_geo`) -/

open Classical in
/-- **`goldBtailSlot`** — the tail contribution `gold_hSum_geo`'s `htail` slot consumes: `0` on DEAD
and LIVE-HIGH boxes, `goldBtail Q bnd k' i` on LIVE-LOW boxes.  This is exactly the additive term
`goldPrice` carries above `boxPriceKerr`, so the `hbox` summand `goldPrice ≤ Cgeo·Kc·goldCut/L^12 +
goldBtailSlot` reduces to `boxPriceKerr ≤ Cgeo·Kc·goldCut/L^12` (LIVE) / `0 ≤ …` (DEAD). -/
noncomputable def goldBtailSlot (N D Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  if min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i then 0
  else if (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
     then 0
     else goldBtail Q bnd k' i

/-- **`gold_box_hbox_at` (item 2, `hbox`).**  The `hbox` summand of `gold_hSum_geo` at `Price 0 k' k
i := goldPrice Kc N D Q bnd k' i` and `Btail k' k i := goldBtailSlot N D Q bnd k' i`, with
`Cgeo := 3^12·gboxConst`.  DEAD: `goldPrice = 0 ≤ Cgeo·Kc·goldCut/L^12 + 0`.  LIVE (high or low):
`boxPriceKerr Kc k' i ≤ Cgeo·Kc·goldCut/L^12` via `gold_box_hbox_geoN`, the `goldBtailSlot` term
cancelling the `goldPrice` tail term. -/
theorem gold_box_hbox_at {Kc : ℝ} (hKc : 1 ≤ Kc) : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (D Q : ℕ) (bnd : ℝ) (k' k i K : ℕ),
      i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K →
      goldPrice Kc N D Q bnd k' i
        ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
          + goldBtailSlot N D Q bnd k' i := by
  obtain ⟨x₁, hbox⟩ := gold_box_hbox_geoN hKc
  refine ⟨x₁, fun N hN D Q bnd k' k i K hi => ?_⟩
  have hgeo0 : (0 : ℝ)
      ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by
    have : (0 : ℝ) ≤ gboxConst := gboxConst_nonneg
    positivity
  have hlive_of : ¬ (min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) →
      2 ^ i < opZ N * pieceN k' + 1 :=
    fun h => lt_of_lt_of_le (not_le.mp h) (min_le_left _ _)
  unfold goldPrice goldBtailSlot
  split_ifs with hcap hwide
  · linarith
  · have hkerr := hbox N hN k' k i K hi (hlive_of hcap); linarith
  · have hkerr := hbox N hN k' k i K hi (hlive_of hcap); linarith

/-! ## 4. Byte-locks — the landed pieces fill the terminal's slots -/

section ByteLock

-- item 1 — the terminal's `hprice` slot (`gold_hBVblocksW_discharge'`, `PDiag.lean:511`) at
-- `Price j k' k i := goldPrice Kc N D Q (QR·Dlev) k' i`; the DEAD / LIVE-HIGH / LIVE-LOW split.
#check @Salt.Goldbach.gold_box_hprice_at
-- item 2 (`hbox`) — the `hbox` summand of `gold_hSum_geo` at that `Price`, with tail term
-- `Btail k' k i := goldBtailSlot N D Q (QR·Dlev) k' i`.
#check @Salt.Goldbach.gold_box_hbox_at
-- the suppliers this composes (all landed)
#check @Salt.Goldbach.gold_box_hprice_op         -- DEAD / LIVE-HIGH branch value `boxPriceKerr`
#check @Salt.Goldbach.gold_box_price_tail        -- LIVE-LOW branch value `goldBtail`
#check @Salt.Goldbach.gold_box_price_vanish      -- the DEAD carrier collapse (`= 0`)
#check @Salt.Goldbach.gold_box_hbox_geoN         -- `boxPriceKerr ≤ Cgeo·Kc·goldCut/L^12` (LIVE)
-- the consumers whose slots these fill
#check @Salt.Goldbach.gold_hSum_geo              -- consumes `hbox` (item 2) + `htail` (residual)
#check @Salt.Goldbach.gold_hBVblocksW_discharge' -- consumes `hprice` (item 1) + `hSum`

/-- **Byte-lock (item 1).**  `gold_box_hprice_at` IS the terminal's `hprice` slot at
`Price := goldPrice`, character-for-character: fixing the operating witnesses and supplying the
per-box `hDge`/`hDsetD`, the terminal's `∀ j k' k i ∈ boundary, carrier ≤ Price j k' k i` holds with
`Price j k' k i := goldPrice Kc N D Q (QR·Dlev) k' i`. -/
example : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (Q a D Ps Dlev K : ℕ) (QR : ℝ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      1 ≤ QR * Dlev →
      (∀ k' k i, i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K →
        ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) ∧
        (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
            (fun d => Q * d), d ≤ D)) →
      ∀ (j k' : ℕ), ∀ (k : ℕ), ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                  (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                  (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
          ≤ goldPrice Kc N D Q (QR * Dlev) k' i := by
  obtain ⟨Kc, x₁, hKc, hat⟩ := gold_box_hprice_at
  refine ⟨Kc, x₁, hKc, ?_⟩
  intro N hN ε₀ Q a D Ps Dlev K QR hQPs hQNa hPsN hQ1 hb hbox j k' k i hi
  exact hat N hN ε₀ j k' k i K Q a D Ps Dlev QR hQPs hQNa hPsN hQ1 hb hi
    (hbox k' k i hi).1 (hbox k' k i hi).2

end ByteLock

end Salt.Goldbach
