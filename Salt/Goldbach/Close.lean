/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandRows2
import Salt.Goldbach.KerrY
import Salt.Goldbach.Surv

/-!
# G-CLOSE — the band-leg per-survivor geo-grade discharges (A₃ terminal, items 1–2)

The two `hwide` inputs that `Surv.gold_band_hlow_tail_discharge` / `gold_band_hsym_tail_discharge`
consume — the per-survivor WIDE geo grade on the high-pass band, discharged at the operating point
by the y-floor engines.

* **`gold_band_hlow_wide_at_op` (item 1, low leg — clean, definitional).**  `goldLowSurvSum`
  prices against `blockPrimeInd (pieceN k')`, exactly `gold_band_wide_price_at_op`'s carrier.  On
  a non-vanishing low survivor (`opY N < pieceN k'` via `gold_band_low_kp_floor`) the engine
  (`gold_band_wide_price_at_op` → `gold_band_survsum_geoN_floored`) grades it to
  `(4^{12}·gboxConst)·Kc·goldCut N (k+1)/(log N)^{12}`; the vanishing survivors
  (`pieceN k' ≤ opY N`) are `0` (`gold_band_low_vanish`).

* **`gold_band_hsym_wide_at_op` (item 2, sym leg — the max-collapse boundary argument).**
  `goldSymSurvSum` prices against `blockPrimeInd (max (opY N) (pieceN k'))`; the engine fixes
  `blockPrimeInd (pieceN kp)`.  On a non-vanishing sym survivor (`opY N < pieceM k'` via
  `gold_band_sym_kp_floor`) the trichotomy: VANISH (`pieceM k' ≤ opY N`, `0`); COLLAPSE
  (`opY N < pieceN k'`, `max = pieceN k'`, engine applies directly); MIDDLE (`pieceN k' < opY N`,
  the straddle `2^{k'} ≤ opY N < 2^{k'+1}`, price at `log (opY N)` via `gold_kerrY_engine` /
  `gold_kerrY_hbox_geoN`).

Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-- The low-band survivor carrier has norm `≤ 1` (two `restrictAlpha` over `blockAlphaLow`). -/
theorem gold_norm_goldLowSub_le_one (N : ℕ) (ε₀ : ℝ) (j k' i : ℕ) :
    ∀ m, ‖goldLowSub N ε₀ j k' i m‖ ≤ 1 := by
  unfold goldLowSub
  exact norm_restrictAlpha_le_one
    (norm_restrictAlpha_le_one (norm_blockAlphaLow_le_one (opZ N) (opY N) ε₀ j (pieceN k'))
      (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1)) (2 ^ i) (2 ^ (i + 1))

/-- **`gold_band_hlow_wide_at_op` (item 1, the low leg's `hwide`).**  For every dyadic-boundary low
survivor at op, on the WIDE per-annulus level the low band price is graded to
`(4^{12}·gboxConst)·Kc·goldCut N (k+1)/(log N)^{12}` — the exact `hwide` input of
`gold_band_hlow_tail_discharge`.  `hDband` is the band wide floor `goldCut^{11/24}/8 ≤ D`;
`hDbnd` the modulus cap `Q·(QR·Dlev) ≤ D`. -/
theorem gold_band_hlow_wide_at_op : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (D : ℝ)
                * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
                    * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
              ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
            goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ)
                  / (Real.log N) ^ 12 := by
  obtain ⟨Kce, xe, hKce, hengine⟩ := gold_band_wide_price_at_op
  obtain ⟨xf, hfloored⟩ := gold_band_survsum_geoN_floored
  refine ⟨max Kce 1, max xe xf, le_max_right _ _, ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband k' hk' k hk i hi hDwide
  have hxe : xe ≤ N := le_trans (le_max_left _ _) hN
  have hxf : xf ≤ N := le_trans (le_max_right _ _) hN
  have hKc1 : (1 : ℝ) ≤ max Kce 1 := le_max_right _ _
  have hgrade0 : (0 : ℝ) ≤ ((4 : ℝ) ^ 12 * gboxConst) * (max Kce 1)
      * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by
    have := gboxConst_nonneg; positivity
  by_cases hvan : pieceN k' ≤ opY N
  · -- VANISH
    rw [gold_band_low_vanish N Q a Ps ε₀ (QR * Dlev) 0 k' k i hvan]
    exact hgrade0
  · -- NON-VANISH: `opY N < pieceN k'`
    rw [not_le] at hvan
    have hDge := hDband k hk
    -- QImage carrier rows
    have hd1 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => Q * d), 1 ≤ d := fun d hd => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hd
    have hcop2 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => Q * d), Nat.Coprime (crtClassG Q (d / Q) N a) d :=
      fun d hd => gold_crtClassG_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQNa hPsN hd
    have hDsetD : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => Q * d), d ≤ D := fun d hd => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hd
    -- the engine price at `blockPrimeInd (pieceN k')`
    have hbox := hengine N hxe (goldLowSub N ε₀ 0 k' i) k' D
      (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d))
      (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) k i K
      hi hvan hDge hDwide (gold_norm_goldLowSub_le_one N ε₀ 0 k' i) hd1 hcop2 hDsetD
    -- `goldLowSurvSum` IS the engine LHS
    have hbox' : goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
        ≤ boxPriceKerr (max Kce 1) k' i := by
      refine le_trans ?_ (boxPriceKerr_mono (le_max_left _ _) k' i)
      unfold goldLowSurvSum
      exact hbox
    exact hfloored N hxf k' k i K (max Kce 1)
      (goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i) hKc1 hi hvan hbox'

/-- The sym-band survivor carrier has norm `≤ 1` (one `restrictAlpha` over `blockAlphaSym`). -/
theorem gold_norm_goldSymSub_le_one (N : ℕ) (ε₀ : ℝ) (j k' i : ℕ) :
    ∀ m, ‖goldSymSub N ε₀ j k' i m‖ ≤ 1 := by
  unfold goldSymSub
  exact norm_restrictAlpha_le_one
    (norm_blockAlphaSym_le_one (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k'))
    (2 ^ i) (2 ^ (i + 1))

/-- **`gold_band_hsym_wide_at_op` (item 2, the sym leg's `hwide`).**  For every dyadic-boundary sym
survivor at op, on the WIDE per-annulus level the sym band price is graded to
`(4^{12}·gboxConst)·Kc·goldCut N (k+1)/(log N)^{12}` — the `hwide` input of
`gold_band_hsym_tail_discharge`.  Two of the three max-collapse regimes are discharged inline:
VANISH (`pieceM k' ≤ opY N`, `0` via `gold_band_sym_vanish`) and COLLAPSE (`opY N < pieceN k'`, so
`max = pieceN k'`, the y-floor engine `gold_band_wide_price_at_op` →
`gold_band_survsum_geoN_floored` applies against `blockPrimeInd (pieceN k')` directly).  The
MIDDLE+boundary regime (`pieceN k' ≤ opY N < pieceM k'`, `max = opY N`, price against
`blockPrimeInd (opY N)`) is supplied
as the hypothesis `hmid` — see FLAG **G-CLOSE-1** (`flags.md`): the only landed Y-indicator engine
`gold_kerrY_engine` requires liveness `2^i < opZ N·pieceN k' + 1`, but the WIDE condition forces
`2^i ≳ N^{2/3} > opZ N·pieceN k'`, so the WIDE middle survivors are non-live; discharging `hmid`
needs a NON-LIVE (y-floor) Y-indicator engine (a `gold_band_wide_price_at_op` variant priced at
`blockPrimeInd (opY N)`), which is not landed. -/
theorem gold_band_hsym_wide_at_op : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      -- MIDDLE+boundary residual (FLAG G-CLOSE-1): `max = opY N`, needs a non-live Y-engine.
      (∀ k' ∈ Finset.range (Nat.log 2 N + 1), pieceN k' ≤ opY N → opY N < pieceM k' →
        ∀ k ∈ Finset.range (Nat.log 2 N + 1),
          ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            (D : ℝ)
                  * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
                      * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
                ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
              goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
                ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ)
                    / (Real.log N) ^ 12) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (D : ℝ)
                * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
                    * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
              ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
            goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ)
                  / (Real.log N) ^ 12 := by
  obtain ⟨Kce, xe, hKce, hengine⟩ := gold_band_wide_price_at_op
  obtain ⟨xf, hfloored⟩ := gold_band_survsum_geoN_floored
  refine ⟨max Kce 1, max xe xf, le_max_right _ _, ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband hmid k' hk' k hk i hi hDwide
  have hxe : xe ≤ N := le_trans (le_max_left _ _) hN
  have hxf : xf ≤ N := le_trans (le_max_right _ _) hN
  have hKc1 : (1 : ℝ) ≤ max Kce 1 := le_max_right _ _
  have hgrade0 : (0 : ℝ) ≤ ((4 : ℝ) ^ 12 * gboxConst) * (max Kce 1)
      * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by
    have := gboxConst_nonneg; positivity
  by_cases hvan : pieceM k' ≤ opY N
  · -- VANISH
    rw [gold_band_sym_vanish N Q a Ps ε₀ (QR * Dlev) 0 k' k i hvan]
    exact hgrade0
  · rw [not_le] at hvan
    by_cases hcol : opY N < pieceN k'
    · -- COLLAPSE: `max (opY N) (pieceN k') = pieceN k'`
      have hmaxc : max (opY N) (pieceN k') = pieceN k' := max_eq_right (le_of_lt hcol)
      have hi' : i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K := by rw [← hmaxc]; exact hi
      have hDge := hDband k hk
      have hd1 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), 1 ≤ d := fun d hd => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hd
      have hcop2 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), Nat.Coprime (crtClassG Q (d / Q) N a) d :=
        fun d hd => gold_crtClassG_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQNa hPsN hd
      have hDsetD : ∀ d ∈ ((Nat.divisors Ps).filter
          (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d), d ≤ D :=
        fun d hd => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hd
      have hbox := hengine N hxe (goldSymSub N ε₀ 0 k' i) k' D
        (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d))
        (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) k i K
        hi' hcol hDge hDwide (gold_norm_goldSymSub_le_one N ε₀ 0 k' i) hd1 hcop2 hDsetD
      have hsurv_eq : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          = (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (goldSymSub N ε₀ 0 k' i) (blockPrimeInd (pieceN k'))
                  (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
            + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                  (fun d => Q * d),
                ‖apDiscBilinCutoff (goldSymSub N ε₀ 0 k' i) (blockPrimeInd (pieceN k'))
                    (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m
                    (goldCut N k)‖) := by
        unfold goldSymSurvSum; rw [hmaxc]
      have hbox' : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          ≤ boxPriceKerr (max Kce 1) k' i := by
        rw [hsurv_eq]; exact le_trans hbox (boxPriceKerr_mono (le_max_left _ _) k' i)
      exact hfloored N hxf k' k i K (max Kce 1)
        (goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i) hKc1 hi' hcol hbox'
    · -- MIDDLE+boundary: `pieceN k' ≤ opY N`, `max = opY N` — routed to `hmid` (G-CLOSE-1)
      rw [not_lt] at hcol
      exact hmid k' hk' hcol hvan k hk i hi hDwide

/-- **`gold_band_hlow_slot_at_op` (item 1 → the `hlow` slot).**  The LOW-leg `hwide`
(`gold_band_hlow_wide_at_op`) fed to `Surv.gold_band_hlow_tail_discharge`: the low band leg
`goldPlowK` absorbs to `Wband + BTlow k'`, `Wband := 24·(4^{12}·gboxConst)·Kc·N/(log N)^{12}`,
`BTlow k' := Σ_k Σ_i goldBandBtailSlot D Q (QR·Dlev) k' i` — exactly the `hlow` input of
`BandClose2.gold_hSum_geo_band`.  The full item-1 chain, end to end. -/
theorem gold_band_hlow_slot_at_op : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      1 ≤ QR * Dlev → (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        goldPlowK N K Q a Ps ε₀ (QR * Dlev) 0 k'
          ≤ 24 * ((4 : ℝ) ^ 12 * gboxConst) * Kc * (N : ℝ) / (Real.log N) ^ 12
            + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
                ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                  (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
                  goldBandBtailSlot D Q (QR * Dlev) k' i := by
  obtain ⟨Kc, x₁, hKc, hlow⟩ := gold_band_hlow_wide_at_op
  refine ⟨Kc, max x₁ 1, hKc, ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hb hDbnd hDband
  have hx₁ : x₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  exact gold_band_hlow_tail_discharge (K := K) ε₀ QR Dlev D hQPs hQNa hPsN hQ1 hb
    (by have := gboxConst_nonneg; positivity) (le_trans zero_le_one hKc) hN1
    (hlow N hx₁ Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband)

end Salt.Goldbach
