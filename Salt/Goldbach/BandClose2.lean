/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandClose

/-!
# G-BANDCLOSE-2 — the aggregation supersession with a band-tail slot (A₃ band close, deliverable C)

`GeoSum.gold_hSum_geo` routes the band legs `PsymK 0 k'`/`PlowK 0 k'` STRICTLY into `Wband`, with NO
additive crumb slot (only the box `Price` leg carries `+ Btail`).  But the `Surv.lean` discharges
`gold_band_hsym_tail_discharge` / `gold_band_hlow_tail_discharge` deliver the band legs WITH a crumb
`+ Σ_k Σ_i goldBandBtailSlot` — order `N/L^{11}`, landing exactly where the box crumb is `0`
(high-pass = box-DEAD), so it cannot fold into the box `htail`.

This file lands (the `(C)` half of the `(C)+(D)+(5)` split):

* **`gold_hSum_geo_band`** — the `gold_hSum_geo` supersession: the band legs `hsym`/`hlow` carry
  per-leg crumbs `BTsym`/`BTlow` (`PsymK 0 k' ≤ Wband + BTsym k'`, `PlowK 0 k' ≤ Wband + BTlow k'`),
  and the routed sum `(1/2)·Σ BTsym + Σ BTlow` is discharged by an ENLARGED tail `hbandtail`
  (`≤ Ctail_band·Kc·N/L^{11}`).  SAME LHS aggregate as `gold_hSum_geo`; the conclusion constant
  gains `+ Ctail_band`.  The box legs (`hmain`, `hboxleg`) and diag are byte-for-byte the landed.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.

## Flagged (NOT closed here — see the G-BANDCLOSE report / `flags.md`)

* **(D) the tower close** — `Σ` of the per-box crumbs `goldBtailMinSlot` (box) + `goldBandBtailSlot`
  (band) over the `O(L²)` boxes × the annulus structure `≤ Ctail_total·Kc·N/(log N)^{11}`, via
  `Surv.gold_band_btail_slot_firing_le` and the firing criterion `X·M ≤ (D·L^{18})²`.  This is the
  `hbandtail`/`htail` input `gold_hSum_geo_band` consumes; the deficit-exponent estimate is a large
  standalone analytic obligation, NOT landed here.
* **(5) the terminal re-wire** — `gold_hBVblocksW_at_op_band`, the minimal-diff `Final2` terminal
  variant consuming (A)–(D): the band legs discharged via `gold_band_survsum_geoN_floored` (item 2)
  and `gold_hSum_geo_band` (this file); residuals: the op rows + hCE/hNum/hdiag + constants.
  This edits the LANDED terminal aggregation and is Fable/house tier.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-- **`gold_hSum_geo_band` (deliverable C).**  The `gold_hSum_geo` supersession with a band-tail
slot.  The band legs carry per-leg crumbs `BTsym`/`BTlow`; the routed `(1/2)·Σ BTsym + Σ BTlow` is
absorbed by the enlarged tail `hbandtail`.  Byte-for-byte the landed box-main / box-tail / diag
absorbs; the conclusion constant gains `+ Ctail_band`.  This is the terminal's `hSum` slot for the
high-pass band (item 4's re-wire target), with the band crumb now carried instead of dropped. -/
theorem gold_hSum_geo_band (N z y K : ℕ) (ε₀ : ℝ) (Kc : ℝ)
    (Price : ℕ → ℕ → ℕ → ℕ → ℝ) (PsymK PlowK : ℕ → ℕ → ℝ) (Btail : ℕ → ℕ → ℕ → ℝ)
    (BTsym BTlow : ℕ → ℝ)
    (Pdiag Wband Cgeo Ctail Ccon_band Ccon_diag Ctail_band : ℝ)
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
    (hsym : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k' ≤ Wband + BTsym k')
    (hlow : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k' ≤ Wband + BTlow k')
    (hbandtail : (1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTsym k')
        + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTlow k')
        ≤ Ctail_band * Kc * (N : ℝ) / (Real.log N) ^ 11)
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
      ≤ (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2 + Ctail_band)
          * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  classical
  set L : ℝ := Real.log N with hLdef
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hcnt0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by positivity
  have hMcard : ∀ k' : ℕ, pieceM k' ≤ 2 * (pieceN k' + 1) := by
    intro k'
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  -- BOX MAIN: the per-annulus geometric price, absorbed via `hgeosum` then the piece `log`.
  have hmain : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
        ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (z * y) K,
            Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
      ≤ 48 * Cgeo * Kc * (N : ℝ) / L ^ 11 := by
    have hcell : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (z * y) K,
            Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
          ≤ 3 * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12) := by
      intro k' _ k _
      have hcard : (dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K).card ≤ 3 :=
        dyadicBoundary_card_le_three (hMcard k') (goldCut_succ_le_two_mul N k)
      have hconst : (0 : ℝ) ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12 := by positivity
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hconst
    have hbk : ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (z * y) K,
            Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
          ≤ 24 * Cgeo * Kc * (N : ℝ) / L ^ 12 := by
      intro k' hk'
      calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K,
                Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
          ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              3 * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12) :=
            Finset.sum_le_sum (fun k hk => hcell k' hk' k hk)
        _ = (3 * Cgeo * Kc / L ^ 12)
              * (∑ k ∈ Finset.range (Nat.log 2 N + 1), (goldCut N (k + 1) : ℝ)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ (3 * Cgeo * Kc / L ^ 12) * (8 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hgeosum (by positivity)
        _ = 24 * Cgeo * Kc * (N : ℝ) / L ^ 12 := by ring
    have hstep : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
          ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K,
              Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (24 * Cgeo * Kc * (N : ℝ) / L ^ 12) := by
      calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), _)
          ≤ ∑ _k' ∈ Finset.range (Nat.log 2 N + 1), 24 * Cgeo * Kc * (N : ℝ) / L ^ 12 :=
            Finset.sum_le_sum hbk
        _ = ((Nat.log 2 N : ℝ) + 1) * (24 * Cgeo * Kc * (N : ℝ) / L ^ 12) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have habs := gold_log_absorb (L := L) (cnt := (Nat.log 2 N : ℝ) + 1)
      (C := 24 * Cgeo * Kc * (N : ℝ)) (val := 24 * Cgeo * Kc * (N : ℝ) / L ^ 12) (p := 11)
      hlogpos hcnt0 hcount (by positivity) (by positivity) (le_refl _)
    calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), _)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (24 * Cgeo * Kc * (N : ℝ) / L ^ 12) := hstep
      _ ≤ 2 * (24 * Cgeo * Kc * (N : ℝ)) / L ^ 11 := habs
      _ = 48 * Cgeo * Kc * (N : ℝ) / L ^ 11 := by ring
  -- BOX LEG: main + tail.
  have hboxleg : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
        ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
      ≤ 48 * Cgeo * Kc * (N : ℝ) / L ^ 11 + Ctail * Kc * (N : ℝ) / L ^ 11 := by
    have hA : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
          ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K,
                (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12 + Btail k' k i)) := by
      refine Finset.sum_le_sum (fun k' hk' => Finset.sum_le_sum (fun k hk =>
        Finset.sum_le_sum (fun i hi => ?_)))
      exact hbox k' hk' k hk i hi
    calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ _ := hA
      _ = (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K,
                Cgeo * Kc * (goldCut N (k + 1) : ℝ) / L ^ 12)
            + (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
                ∑ k ∈ Finset.range (Nat.log 2 N + 1),
                  ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                    (goldCut N k) (goldCut N (k + 1)) (z * y) K, Btail k' k i) := by
            simp only [Finset.sum_add_distrib]
      _ ≤ 48 * Cgeo * Kc * (N : ℝ) / L ^ 11 + Ctail * Kc * (N : ℝ) / L ^ 11 :=
            add_le_add hmain htail
  -- BAND legs WITH the routed crumb: one `log` each, PLUS the carried `Σ BT`.
  have hbandleg : ∀ (P BT : ℕ → ℝ),
      (∀ k' ∈ Finset.range (Nat.log 2 N + 1), P k' ≤ Wband + BT k') →
      (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k')
        ≤ 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
          + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BT k') := by
    intro P BT hP
    have hWabs : (∑ _k' ∈ Finset.range (Nat.log 2 N + 1), Wband)
        ≤ 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11 := by
      have habs := gold_log_absorb (L := L) (cnt := (Nat.log 2 N : ℝ) + 1)
        (C := Ccon_band * Kc * (N : ℝ)) (val := Wband) (p := 11)
        hlogpos hcnt0 hcount (by positivity) hWband0 hWband
      calc (∑ _k' ∈ Finset.range (Nat.log 2 N + 1), Wband)
          = ((Nat.log 2 N : ℝ) + 1) * Wband := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ 2 * (Ccon_band * Kc * (N : ℝ)) / L ^ 11 := habs
        _ = 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11 := by ring
    calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k')
        ≤ ∑ k' ∈ Finset.range (Nat.log 2 N + 1), (Wband + BT k') := Finset.sum_le_sum hP
      _ = (∑ _k' ∈ Finset.range (Nat.log 2 N + 1), Wband)
            + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BT k') := by
          rw [Finset.sum_add_distrib]
      _ ≤ 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
            + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BT k') := by linarith [hWabs]
  have hsigsym := hbandleg (fun k' => PsymK 0 k') BTsym hsym
  have hsiglow := hbandleg (fun k' => PlowK 0 k') BTlow hlow
  -- assemble the single-block aggregate
  simp only [hmax, Nat.zero_add, Finset.sum_range_one]
  have hhalfsym : (1 / 2 : ℝ) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k')
      ≤ (1 / 2) * (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
          + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTsym k')) :=
    mul_le_mul_of_nonneg_left hsigsym (by norm_num)
  have hhalfdiag : (1 / 2 : ℝ) * Pdiag ≤ (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / L ^ 11) :=
    mul_le_mul_of_nonneg_left hPdiag (by norm_num)
  calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k') + (1 / 2) * Pdiag)
      ≤ (48 * Cgeo * Kc * (N : ℝ) / L ^ 11 + Ctail * Kc * (N : ℝ) / L ^ 11)
          + ((1 / 2) * (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
                + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTsym k'))
             + (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
                + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTlow k'))
             + (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / L ^ 11)) :=
        add_le_add hboxleg (add_le_add (add_le_add hhalfsym hsiglow) hhalfdiag)
    _ = (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / L ^ 11
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTsym k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), BTlow k')) := by ring
    _ ≤ (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / L ^ 11
          + Ctail_band * Kc * (N : ℝ) / L ^ 11 := by linarith [hbandtail]
    _ = (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2 + Ctail_band)
          * Kc * (N : ℝ) / L ^ 11 := by ring

end Salt.Goldbach
