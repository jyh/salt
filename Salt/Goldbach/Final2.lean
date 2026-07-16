/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Final
import Salt.Goldbach.GeoSum
import Salt.Goldbach.PDiag

/-!
# G-FINAL — the terminal composition skeleton (Goldbach terminal, part III: item 3)

This file composes the terminal `gold_hBVblocksW_discharge'` (`PDiag.lean:502`) with the min-form
box slots landed in `Final.lean`, filling — character-for-character — the two box legs it names:

* its **`hprice`** slot is filled by `gold_box_hprice_at_min` (the min-form piecewise price
  `goldPriceMin`, DEAD / LIVE-HIGH / LIVE-LOW compiled), at `z := opZ N`, `y := opY N`;
* the **`hbox`** summand of its **`hSum`** slot (routed through `gold_hSum_geo`) is filled by
  `gold_box_hbox_at_min` (`goldPriceMin ≤ Cgeo·Kc·goldCut/L^{12} + goldBtailMinSlot`), and its
  `hgeosum` by `gold_goldCut_geosum`.

`gold_hBVblocksW_at_op` therefore reduces the A₃ analytic chain — `Σ_j rosserRemainder ≤ N/(log
N)^{10}` — to a residual list that is **exactly** the structural operating-point rows plus the
analytic bridge that G-ASM (or item 2, the band pricer, and the `htail` tower close) supplies.  The
composition itself is kernel-verified here; the residuals are named in the theorem statement.

## Residual list (exposed, per item 4 — the G-ASM byte-lock)

* **structural op rows** — `hz`, `hN2`, `hNX`, `hK`, `hw'2`, `hPw'`, `hiX` (the terminal's own
  structural rows), `hQNa` (the residue coprimality `Coprime Q (N−a)`, from the CRT witness),
  `hb` (`1 ≤ QR·Dlev`), and `hDrows` (the per-box wide level `hDge` + modulus cap `hDsetD`).
* **the `hSum` analytic bridge** — `htail` (the `htail` tower close, `Σ goldBtailMinSlot ≤
  Ctail·Kc·N/L^{11}`; the min-side Term B against the live-low cap and the tower — see the report),
  `hsym` / `hlow` (the band `PsymK 0 k' ≤ Wband` / `PlowK 0 k' ≤ Wband`, from item 2's band pricer
  via `gold_band_hsym_slot`), `hWband`, `hPdiag`, `hcount`, `hmax`, `hlogpos`, `hWband0`, `hCband0`.
* **the terminal's remaining legs** — `hpriceSym` / `hpriceLow` (the band-rect `|·|` sums, item 2),
  `hdiag` (the honest diagonal row), `hCE` (`gold_op_hCE`), `hNum` (`gold_hNum_close_of_tower`).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-- **`gold_hBVblocksW_at_op` (item 3).**  The compiled terminal: `gold_hBVblocksW_discharge'` with
its two box legs filled by the min-form slots of `Final.lean` — `hprice := gold_box_hprice_at_min`,
and the `hSum`'s `hbox` summand `:= gold_box_hbox_at_min` (routed through `gold_hSum_geo`, `hgeosum
:= gold_goldCut_geosum`).  Emits the EXACT A₃ chain `Σ_j rosserRemainder ≤ N/(log N)^{10}` with
residual hypotheses ONLY the structural operating-point rows and the analytic bridge (the `htail`
tower close, the band `hsym`/`hlow`/`hpriceSym`/`hpriceLow`, `hCE`, `hdiag`, `hNum`).  `Kc` and `x₁`
are the `gold_box_hprice_at_min` constants; `Cgeo := 3^{12}·gboxConst`. -/
theorem gold_hBVblocksW_at_op : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (Q a Ps w' : ℕ)
      (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps)
      (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
      (hQ1 : 1 ≤ Q) (haN : a ≤ N)
      (QR : ℝ) (Dlev D X K : ℕ)
      (hb : 1 ≤ QR * Dlev)
      (hz : 1 ≤ opZ N) (hN2 : 2 ≤ N) (hNX : N / 2 ≤ X) (hK : Nat.log 2 X ≤ K)
      (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
      (hiX : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, 2 ^ (i + 1) ≤ X + 1)
      (hDrows : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
        ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) ∧
        (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
            (fun d => Q * d), d ≤ D))
      (PsymK PlowK : ℕ → ℕ → ℝ)
      (hpriceSym : ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
          (∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k'))
                  (blockPrimeInd (max (opY N) (pieceN k'))) X (pieceM k')
                  (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))
                - apDiscBilinCutoff (blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k'))
                  (blockPrimeInd (max (opY N) (pieceN k'))) X (pieceM k')
                  (crtClassG Q (m / Q) N a) m (goldCut N k)‖) ≤ PsymK j k')
      (hpriceLow : ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
          (∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k'))
                    (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                  (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N (k + 1))
                - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k'))
                    (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                  (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N k)‖) ≤ PlowK j k')
      (Pdiag Wband Ctail Ccon_band Ccon_diag RCE : ℝ)
      (hmax : maxBlock N (opZ N) ε₀ = 0) (hlogpos : 0 < Real.log N)
      (hWband0 : 0 ≤ Wband) (hCband0 : 0 ≤ Ccon_band)
      (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N)
      (hsym : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k' ≤ Wband)
      (hlow : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k' ≤ Wband)
      (hWband : Wband ≤ Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
      (hPdiag : Pdiag ≤ Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11)
      (htail : (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            goldBtailMinSlot N D Q (QR * Dlev) k' i)
          ≤ Ctail * Kc * (N : ℝ) / (Real.log N) ^ 11)
      (hdiag : (opY N : ℝ) * (Nat.sqrt N : ℝ)
          * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
      (hCE : (∑ j ∈ Finset.range (maxBlock N (opZ N) ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then goldBlockConvErrW N (opZ N) (opY N) ε₀ j Q d else 0) ≤ RCE)
      (hNum : (48 * (3 ^ 12 * gboxConst) + Ctail + 3 * Ccon_band + Ccon_diag / 2)
              * Kc * (N : ℝ) / (Real.log N) ^ 11 + RCE ≤ (N : ℝ) / (Real.log N) ^ 10),
    (∑ j ∈ Finset.range (maxBlock N (opZ N) ε₀ + 1),
        rosserRemainder (goldBlockSwitchSieveW N (opZ N) (opY N) ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  classical
  obtain ⟨Kc0, x₁, hKc0, hpr⟩ := gold_box_hprice_at_min
  obtain ⟨x₂, hbx⟩ := gold_box_hbox_at_min (Kc := Kc0) hKc0
  refine ⟨Kc0, max x₁ x₂, hKc0, ?_⟩
  intro N hN ε₀ Q a Ps w' hPs hPodd hQPs hQNa hPsN hQ1 haN QR Dlev D X K hb hz hN2 hNX hK hw'2 hPw'
    hiX hDrows PsymK PlowK hpriceSym hpriceLow Pdiag Wband Ctail Ccon_band Ccon_diag RCE hmax
    hlogpos hWband0 hCband0 hcount hsym hlow hWband hPdiag htail hdiag hCE hNum
  have hN1 : x₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2' : x₂ ≤ N := le_trans (le_max_right _ _) hN
  -- the min-form piecewise price (`j`-independent) fills the `Price` slot
  set Price : ℕ → ℕ → ℕ → ℕ → ℝ :=
    fun _ k' _ i => goldPriceMin Kc0 N D Q (QR * Dlev) k' i with hPricedef
  set Btail : ℕ → ℕ → ℕ → ℝ := fun k' _ i => goldBtailMinSlot N D Q (QR * Dlev) k' i with hBtaildef
  -- `hprice` — the min-form per-box price at the QImage
  have hprice : ∀ j k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
      (∑ m ∈ ((Nat.divisors Ps).filter
            (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
              (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
        + (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
        ≤ Price j k' k i := by
    intro j k' k i hi
    exact hpr N hN1 ε₀ j k' k i K Q a D Ps Dlev QR hQPs hQNa hPsN hQ1 hb hi
      (hDrows k' k i hi).1 (hDrows k' k i hi).2
  -- `hbox` — the `hSum`'s box summand, via the geometric per-annulus price
  have hbox : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
      ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
        Price 0 k' k i ≤ (3 ^ 12 * gboxConst) * Kc0 * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
          + Btail k' k i :=
    fun k' _ k _ i hi => hbx N hN2' D Q (QR * Dlev) k' k i K hi
  -- `hSum` — the geometric aggregate
  have hSum := gold_hSum_geo N (opZ N) (opY N) K ε₀ Kc0 Price PsymK PlowK Btail Pdiag Wband
    (3 ^ 12 * gboxConst) Ctail Ccon_band Ccon_diag hmax (le_trans zero_le_one hKc0) hlogpos
    hWband0 (by have := gboxConst_nonneg; positivity) hCband0 (gold_goldCut_geosum (by omega)) hbox
    htail hsym hlow hWband hPdiag hcount
  -- compose the terminal
  exact gold_hBVblocksW_discharge' N (opZ N) (opY N) ε₀ Q a Ps w' hPs hPodd hQPs hQ1 haN QR Dlev X K
    hz hN2 hNX hK hw'2 hPw' hiX Price hprice PsymK PlowK hpriceSym hpriceLow Pdiag
    ((48 * (3 ^ 12 * gboxConst) + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc0 * (N : ℝ)
      / (Real.log N) ^ 11) RCE hdiag hSum hCE hNum

/-! ## Byte-lock — the composed terminal + the residual list (item 4) -/

section ByteLock

-- the compiled terminal (item 3)
#check @Salt.Goldbach.gold_hBVblocksW_at_op
-- the min-form box slots it fills the terminal with (Final.lean)
#check @Salt.Goldbach.gold_box_hprice_at_min       -- the `hprice` slot
#check @Salt.Goldbach.gold_box_hbox_at_min         -- the `hbox` summand of `hSum`
#check @Salt.Goldbach.gold_goldCut_geosum          -- the `hgeosum` of `hSum`
-- the consumers filled
#check @Salt.Goldbach.gold_hSum_geo                -- the `hSum` slot
#check @Salt.Goldbach.gold_hBVblocksW_discharge'   -- the terminal

end ByteLock

end Salt.Goldbach
