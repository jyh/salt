/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandWin2

/-!
# G-SURV-2 — the per-survivor band discharge + the band firing crumb (A₃ band leg)

The band-composition layer above `BandWin2.lean` (the WIDE geo pricer + the FIRING min tail).  This
file lands the SOUND compositional core that both band legs share:

* **`gold_band_low_survsum_discharge` / `gold_band_sym_survsum_discharge`** — the per-survivor
  two-case discharge `goldLowSurvSum / goldSymSurvSum ≤ (geo grade) + goldBandBtailSlot`: WIDE
  (`√(X_sub·M) ≥ D·L^{18}`) via the caller's geo grade `hwide`; FIRING via the min harmonic tail
  `goldBtailMin` (`gold_band_low_price_tail_min` / `gold_band_sym_price_tail_min`) added to the
  nonnegative geo grade.  These are the exact `hgeo` inputs `gold_band_hlow_tail` /
  `gold_band_hsym_tail` consume with `Btail k' k i := goldBandBtailSlot D Q bnd k' i`.
* **`gold_band_btail_slot_nonneg` / `gold_band_btail_slot_le_min`** — the band firing crumb is
  nonnegative and dominated by the carrier-agnostic min crumb `goldBtailMin` (the WIDE branch drops
  to `0`).
* **`gold_band_btail_slot_firing_le`** — the per-box band-crumb conversion (item 3, per-box heart):
  on the FIRING branch the crumb is bounded by `2·(2·(D·L^{18})²/Q·(1+log bnd) + 2·(D·L^{18})·bnd)`
  via `min(X, M) ≤ √(X·M) < D·L^{18}`; the WIDE branch is `0 ≤` the RHS.  The band mirror of
  `BandPrice2.gold_btail_slot_firing_le` (no box-cap DEAD branch — the high-pass band has none).
* **`gold_band_hlow_tail_discharge` / `gold_band_hsym_tail_discharge`** — the leg-level composition:
  fed the per-survivor `hwide`, the annulus/survivor double sum `goldPlowK`/`goldPsymK` absorbs to
  `24·Cgeo·Kc·N/(log N)^{12}` PLUS the routed band crumb sum, via the landed tail variants.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.

## Flagged residuals (NOT closed here — see the G-SURV-2 report / `flags.md`)

* **item 2** (the high-pass geoN ratios): `gold_band_survsum_geoN`'s `hratio`/`hNXM` are NOT
  uniformly derivable on the band.  `gold_box_live_ratios` (OpPlumb) requires the LIVE gate
  `2^i < opZ N·pieceN kp + 1`, which the high-pass band survivors FAIL; and the ratio
  `(10/31)·log(X·M) ≤ log 2^{kp}` provably FAILS on low-`kp`/high-`i` survivors.  The `hwide`
  branch below is left as a caller hypothesis: discharging it needs a NEW high-pass floor plus the
  band-carrier vanishing on the ratio-failing annuli (no band analog of `gold_box_carrier_vanish`).
* **item 4** (the band-crumb terminal re-wire): the landed `gold_hSum_geo` routes the band legs
  `PsymK 0 k'`/`PlowK 0 k'` STRICTLY into `Wband ≤ Ccon_band·Kc·N/L^{12}` — there is NO additive
  `Btail` slot on the band legs (only the box `Price` slot carries `+ Btail`).  The band crumb
  is order `N/L^{11}` and lands exactly where the box crumb `goldBtailMinSlot` is `0` (high-pass =
  box-DEAD), so it cannot be folded into the box `htail`.  Routing it needs an edit to the LANDED
  `gold_hSum_geo`/`gold_hBVblocksW_discharge'`.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The per-survivor two-case discharge (WIDE ∪ FIRING) -/

/-- **`gold_band_low_survsum_discharge` (item 1, low leg).**  On a survivor the low band price is
`≤ (geo grade) + goldBandBtailSlot`: WIDE (`√(X_sub·M) ≥ D·L^{18}`) via the caller's geo grade
`hwide` with crumb `0`; FIRING via `gold_band_low_price_tail_min` (the min tail `goldBtailMin`)
added to the nonnegative geo grade. -/
theorem gold_band_low_survsum_discharge (N Q a Ps : ℕ) (ε₀ : ℝ) (k' k : ℕ) (QR : ℝ) (Dlev i D : ℕ)
    {Kc Cgeo : ℝ}
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev)
    (hgeo0 : 0 ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
    (hwide : (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
        goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
      ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
        + goldBandBtailSlot D Q (QR * Dlev) k' i := by
  unfold goldBandBtailSlot
  by_cases hw : (D : ℝ)
      * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
  · rw [if_pos hw, add_zero]; exact hwide hw
  · rw [if_neg hw]
    have htail := gold_band_low_price_tail_min N Q a Ps ε₀ 0 k' k QR Dlev i hQPs hQNa hPsN hQ1 hb
    linarith [htail, hgeo0]

/-- **`gold_band_sym_survsum_discharge` (item 1, sym leg).**  Sym mirror of
`gold_band_low_survsum_discharge` at the `max`-collapse carrier `goldSymSub` /
`blockPrimeInd (max (opY N) (pieceN k'))`, FIRING via `gold_band_sym_price_tail_min`. -/
theorem gold_band_sym_survsum_discharge (N Q a Ps : ℕ) (ε₀ : ℝ) (k' k : ℕ) (QR : ℝ) (Dlev i D : ℕ)
    {Kc Cgeo : ℝ}
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev)
    (hgeo0 : 0 ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
    (hwide : (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
        goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
      ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
        + goldBandBtailSlot D Q (QR * Dlev) k' i := by
  unfold goldBandBtailSlot
  by_cases hw : (D : ℝ)
      * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
  · rw [if_pos hw, add_zero]; exact hwide hw
  · rw [if_neg hw]
    have htail := gold_band_sym_price_tail_min N Q a Ps ε₀ 0 k' k QR Dlev i hQPs hQNa hPsN hQ1 hb
    linarith [htail, hgeo0]

/-! ## 2. The band firing crumb — nonnegativity, min-domination, the per-box conversion -/

/-- **`gold_band_btail_slot_nonneg`.**  The band firing crumb is nonnegative (`0` on WIDE, the
nonnegative `goldBtailMin` on FIRING). -/
theorem gold_band_btail_slot_nonneg {D Q : ℕ} {bnd : ℝ} (k' i : ℕ)
    (hQ1 : 1 ≤ Q) (hbnd : 1 ≤ bnd) :
    0 ≤ goldBandBtailSlot D Q bnd k' i := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlog0 : 0 ≤ Real.log bnd := Real.log_nonneg hbnd
  have hbnd0 : (0 : ℝ) ≤ bnd := by linarith
  have hX0 : (0 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by positivity
  have hM0 : (0 : ℝ) ≤ (pieceM k' : ℝ) := by positivity
  have hmin0 : (0 : ℝ) ≤ min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) := le_min hX0 hM0
  have hmin0' : 0 ≤ goldBtailMin Q bnd k' i := by
    unfold goldBtailMin
    have t1 : (0 : ℝ) ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q
        * (1 + Real.log bnd) := by positivity
    have t2 : (0 : ℝ) ≤ 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * bnd :=
      mul_nonneg (mul_nonneg (by norm_num) hmin0) hbnd0
    linarith
  unfold goldBandBtailSlot
  split_ifs with hw
  · linarith
  · exact hmin0'

/-- **`gold_band_btail_slot_le_min`.**  The band firing crumb is dominated by the carrier-agnostic
min crumb `goldBtailMin` (the WIDE branch drops to `0 ≤ goldBtailMin`). -/
theorem gold_band_btail_slot_le_min {D Q : ℕ} {bnd : ℝ} (k' i : ℕ)
    (hQ1 : 1 ≤ Q) (hbnd : 1 ≤ bnd) :
    goldBandBtailSlot D Q bnd k' i ≤ goldBtailMin Q bnd k' i := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlog0 : 0 ≤ Real.log bnd := Real.log_nonneg hbnd
  have hbnd0 : (0 : ℝ) ≤ bnd := by linarith
  have hX0 : (0 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by positivity
  have hM0 : (0 : ℝ) ≤ (pieceM k' : ℝ) := by positivity
  have hmin0 : 0 ≤ goldBtailMin Q bnd k' i := by
    unfold goldBtailMin
    have t1 : (0 : ℝ) ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q
        * (1 + Real.log bnd) := by positivity
    have t2 : (0 : ℝ) ≤ 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * bnd :=
      mul_nonneg (mul_nonneg (by norm_num) (le_min hX0 hM0)) hbnd0
    linarith
  unfold goldBandBtailSlot
  split_ifs with hw
  · exact hmin0
  · exact le_refl _

/-- **`gold_band_btail_slot_firing_le` (item 3, the per-box band-crumb conversion).**  On the FIRING
branch the band crumb is `≤ 2·(2·(D·L^{18})²/Q·(1+log bnd) + 2·(D·L^{18})·bnd)`
(`L := log((2^{i+1}−1)·pieceM k')`), via `min(X, M) ≤ √(X·M) < D·L^{18}` and `X·M < (D·L^{18})²`;
the WIDE branch is `0 ≤` the (nonneg) RHS.  The band mirror of
`BandPrice2.gold_btail_slot_firing_le` with NO box-cap DEAD branch (the high-pass band has none). -/
theorem gold_band_btail_slot_firing_le {D Q : ℕ} {bnd : ℝ} (k' i : ℕ)
    (hQ1 : 1 ≤ Q) (hbnd : 1 ≤ bnd) :
    goldBandBtailSlot D Q bnd k' i
      ≤ 2 * (2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
                    ^ ((13 : ℝ) + 5)) ^ 2 / Q * (1 + Real.log bnd)
          + 2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
                    ^ ((13 : ℝ) + 5)) * bnd) := by
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) with hXMdef
  set B : ℝ := (D : ℝ) * (Real.log XM) ^ ((13 : ℝ) + 5) with hBdef
  have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
    have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM1 : (1 : ℕ) ≤ pieceM k' :=
    le_trans (Nat.one_le_pow _ _ (by norm_num)) (two_pow_le_pieceM k')
  have hXM1 : (1 : ℝ) ≤ XM := by
    rw [hXMdef]
    have hxR : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
    have hmR : (1 : ℝ) ≤ (pieceM k' : ℝ) := by exact_mod_cast hM1
    nlinarith
  have hXM0 : 0 ≤ XM := by linarith
  have hlogXM0 : 0 ≤ Real.log XM := Real.log_nonneg hXM1
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (by positivity) (Real.rpow_nonneg hlogXM0 _)
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlog0 : 0 ≤ Real.log bnd := Real.log_nonneg hbnd
  have hbnd0 : 0 ≤ bnd := by linarith
  have h1L : (0 : ℝ) ≤ 1 + Real.log bnd := by linarith
  have hRHS0 : (0 : ℝ) ≤ 2 * (2 * B ^ 2 / Q * (1 + Real.log bnd) + 2 * B * bnd) := by
    have t1 : (0 : ℝ) ≤ 2 * B ^ 2 / Q * (1 + Real.log bnd) := mul_nonneg (by positivity) h1L
    have t2 : (0 : ℝ) ≤ 2 * B * bnd := mul_nonneg (mul_nonneg (by norm_num) hB0) hbnd0
    linarith
  unfold goldBandBtailSlot
  split_ifs with hw
  · exact hRHS0
  · -- firing branch: `√XM < B`
    have hfire : Real.sqrt XM < B := not_le.mp hw
    have hXMlt : XM < B ^ 2 := by
      have hsq : Real.sqrt XM * Real.sqrt XM = XM := Real.mul_self_sqrt hXM0
      nlinarith [hfire, Real.sqrt_nonneg XM, hB0]
    have hmin : min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) ≤ B := by
      have hle : min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) ≤ Real.sqrt XM := by
        rw [hXMdef]; exact min_le_sqrt_mul (by positivity) (by positivity)
      linarith [hfire]
    unfold goldBtailMin
    have hTA : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
        ≤ 2 * B ^ 2 / Q * (1 + Real.log bnd) := by
      have hnum : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) ≤ 2 * B ^ 2 := by
        have heq : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) = 2 * XM := by
          rw [hXMdef]; ring
        rw [heq]; linarith [hXMlt]
      have hfac : 0 ≤ (1 + Real.log bnd) / Q := div_nonneg h1L (le_of_lt hQ0)
      have := mul_le_mul_of_nonneg_right hnum hfac
      calc 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
          = (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) * ((1 + Real.log bnd) / Q) := by
            ring
        _ ≤ (2 * B ^ 2) * ((1 + Real.log bnd) / Q) := this
        _ = 2 * B ^ 2 / Q * (1 + Real.log bnd) := by ring
    have hTB : 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * bnd ≤ 2 * B * bnd := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin (by norm_num : (0:ℝ) ≤ 2))
        hbnd0
      linarith [this]
    linarith [hTA, hTB]

/-! ## 3. The leg-level composition — the band legs WITH the routed crumb sum

Fed the per-survivor `hwide`, the annulus/survivor double sum absorbs (via the landed tail variants
`gold_band_hlow_tail`/`gold_band_hsym_tail`) to `24·Cgeo·Kc·N/L^{12}` PLUS the routed band crumb sum
`Σ_k Σ_i goldBandBtailSlot D Q bnd k' i`.  This is the exact input the (flagged, item-4) terminal
re-wire would consume — modulo the missing band-`Btail` slot in the landed `gold_hSum_geo`. -/

/-- **`gold_band_hlow_tail_discharge`.**  The low band leg with the crumb routed: given the
per-survivor WIDE geo grade `hwide` (item 2's residual), `goldPlowK` absorbs to
`24·Cgeo·Kc·N/(log N)^{12} + Σ_k Σ_i goldBandBtailSlot D Q bnd k' i`. -/
theorem gold_band_hlow_tail_discharge {N K Q a Ps : ℕ} (ε₀ : ℝ) (QR : ℝ) (Dlev D : ℕ) {Kc Cgeo : ℝ}
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hwide : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
              ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
            goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPlowK N K Q a Ps ε₀ (QR * Dlev) 0 k'
        ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
          + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
                goldBandBtailSlot D Q (QR * Dlev) k' i := by
  refine gold_band_hlow_tail (K := K) ε₀ (QR * Dlev)
    (fun k' k i => goldBandBtailSlot D Q (QR * Dlev) k' i) hCgeo0 hKc0 hN1 ?_
  intro k' hk' k hk i hi
  have hgeo0 : 0 ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by positivity
  exact gold_band_low_survsum_discharge N Q a Ps ε₀ k' k QR Dlev i D hQPs hQNa hPsN hQ1 hb hgeo0
    (hwide k' hk' k hk i hi)

/-- **`gold_band_hsym_tail_discharge`.**  Sym mirror of `gold_band_hlow_tail_discharge` at the
`max`-collapse boundary. -/
theorem gold_band_hsym_tail_discharge {N K Q a Ps : ℕ} (ε₀ : ℝ) (QR : ℝ) (Dlev D : ℕ) {Kc Cgeo : ℝ}
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hwide : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
              ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
            goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPsymK N K Q a Ps ε₀ (QR * Dlev) 0 k'
        ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
          + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
                goldBandBtailSlot D Q (QR * Dlev) k' i := by
  refine gold_band_hsym_tail (K := K) ε₀ (QR * Dlev)
    (fun k' k i => goldBandBtailSlot D Q (QR * Dlev) k' i) hCgeo0 hKc0 hN1 ?_
  intro k' hk' k hk i hi
  have hgeo0 : 0 ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by positivity
  exact gold_band_sym_survsum_discharge N Q a Ps ε₀ k' k QR Dlev i D hQPs hQNa hPsN hQ1 hb hgeo0
    (hwide k' hk' k hk i hi)

end Salt.Goldbach
