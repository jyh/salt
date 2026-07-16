/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandWin
import Salt.Goldbach.BandPrice2

/-!
# G-BANDWIN — the band firing branch + the tail-routed band legs (A₃ band leg, node 3+4)

Design: the G-SURV re-scope (ledger ~12:15), node 3.  `BandWin.lean` (node 1–2) prices a WIDE band
survivor at the geo grade `Cgeo·Kc·goldCut N (k+1)/(log N)^{12}` (via `gold_band_box_kerr` →
`gold_band_survsum_geoN`).  A FIRING survivor (`√(X_sub·M) < D·L^{18}`, `X_sub := 2^{i+1}−1`,
`M := pieceM k'`) fails the engine's `herr_lev` row, so it is priced by the **min-side trivial
tail**
instead — Final.lean's machinery (`gold_box_disc_trivial_min`, carrier-generic via
`apDiscBilinCutoff_symm`, so the min-side leg is free) at the BAND carriers
`goldLowSub`/`goldSymSub`.

This file lands (node 3+4):

* **`gold_band_low_price_tail_min` / `gold_band_sym_price_tail_min`** — the per-survivor two-cutoff
  band price bounded by the min harmonic tail `goldBtailMin Q bnd k' i` (carrier-agnostic crumb,
  reused from `Final.lean`).  Direct mirror of `gold_box_price_tail_min` at the band carriers.
* **`goldBandBtailSlot`** — the band firing crumb: `0` on WIDE survivors, `goldBtailMin` on FIRING
  survivors (no DEAD cap — the high-pass band has no box-cap branch).
* **`gold_band_geo_absorb_tail`** — the tail-routed geometric absorb: a per-`(k, i)` price
  bounded by
  `geo grade + Btail k i` absorbs to `24·Cgeo·Kc·N/(log N)^{12} + Σ Btail` — the pure
  `gold_band_geo_absorb` plus the routed crumb sum.
* **`gold_band_hlow_tail` / `gold_band_hsym_tail`** — the `hlow`/`hsym` band legs WITH a
  `Btail_band`
  term routed: `BandPrice`'s `gold_band_hlow`/`gold_band_hsym` conclusions plus the additive crumb
  `Σ_k Σ_i Btail k' k i`, so the band crumb joins the terminal's `htail` slot.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The band firing pricers — the min-side trivial tail at the band carriers -/

open Classical in
/-- **`gold_band_low_carrier_tail_min`.**  The one-cutoff low-band carrier sum over the `QImage`
moduli, bounded by the min-side crude harmonic tail — the band mirror of `gold_box_carrier_tail_min`
at `goldLowSub` (norm via `norm_low_leg_le_one`).  `gold_box_disc_trivial_min` per modulus
(carrier-generic, so the min-side leg is free), `gold_crtClassG_coprime_of_mem` for the `R`-unit,
`gold_box_tail_min` closes the `QImage` sum. -/
theorem gold_band_low_carrier_tail_min (N Q a Ps : ℕ) (ε₀ : ℝ) (j k' : ℕ) (QR : ℝ) (Dlev T i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (goldLowSub N ε₀ j k' i) (blockPrimeInd (pieceN k'))
            (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m T‖)
      ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * (QR * Dlev) := by
  have halpha : ∀ m, ‖goldLowSub N ε₀ j k' i m‖ ≤ 1 :=
    norm_low_leg_le_one (opZ N) (opY N) ε₀ j (pieceN k')
      (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1) i
  have hbeta : ∀ n, ‖blockPrimeInd (pieceN k') n‖ ≤ 1 := blockPrimeInd_norm_le_one (pieceN k')
  refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
    (gold_box_tail_min (2 ^ (i + 1) - 1) (pieceM k') Q Ps (QR * Dlev) hQ1 hb)
  have hcop : Nat.Coprime (crtClassG Q (m / Q) N a) m :=
    gold_crtClassG_coprime_of_mem (QR * Dlev) hQ1 hQPs hQNa hPsN hm
  have hm1 : 1 ≤ m := by
    obtain ⟨d, hd, hmd⟩ := Finset.mem_image.mp hm
    have hdp : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hpos : 0 < Q * d := Nat.mul_pos (by omega) hdp
    rw [← hmd]; exact hpos
  exact gold_box_disc_trivial_min halpha hbeta hm1 hcop

open Classical in
/-- **`gold_band_sym_carrier_tail_min`.**  The one-cutoff sym-band carrier sum over the `QImage`
moduli, bounded by the min-side crude harmonic tail — the sym mirror at `goldSymSub` (norm via
`norm_sym_leg_le_one`), indicator `blockPrimeInd (max (opY N) (pieceN k'))`. -/
theorem gold_band_sym_carrier_tail_min (N Q a Ps : ℕ) (ε₀ : ℝ) (j k' : ℕ) (QR : ℝ) (Dlev T i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (goldSymSub N ε₀ j k' i) (blockPrimeInd (max (opY N) (pieceN k')))
            (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m T‖)
      ≤ 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log (QR * Dlev))
          + 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * (QR * Dlev) := by
  have halpha : ∀ m, ‖goldSymSub N ε₀ j k' i m‖ ≤ 1 :=
    norm_sym_leg_le_one (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k') i
  have hbeta : ∀ n, ‖blockPrimeInd (max (opY N) (pieceN k')) n‖ ≤ 1 :=
    blockPrimeInd_norm_le_one (max (opY N) (pieceN k'))
  refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
    (gold_box_tail_min (2 ^ (i + 1) - 1) (pieceM k') Q Ps (QR * Dlev) hQ1 hb)
  have hcop : Nat.Coprime (crtClassG Q (m / Q) N a) m :=
    gold_crtClassG_coprime_of_mem (QR * Dlev) hQ1 hQPs hQNa hPsN hm
  have hm1 : 1 ≤ m := by
    obtain ⟨d, hd, hmd⟩ := Finset.mem_image.mp hm
    have hdp : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hpos : 0 < Q * d := Nat.mul_pos (by omega) hdp
    rw [← hmd]; exact hpos
  exact gold_box_disc_trivial_min halpha hbeta hm1 hcop

/-- **`gold_band_low_price_tail_min`.**  The two-cutoff low-band survivor sum `goldLowSurvSum`
bounded by the min harmonic tail crumb `goldBtailMin Q bnd k' i` — `2×` the single-cutoff min tail
(`gold_band_low_carrier_tail_min` at `T ∈ {goldCut N (k+1), goldCut N k}`).  The FIRING-branch value
the band routes into `htail`. -/
theorem gold_band_low_price_tail_min (N Q a Ps : ℕ) (ε₀ : ℝ) (j k' k : ℕ) (QR : ℝ) (Dlev i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) j k' k i ≤ goldBtailMin Q (QR * Dlev) k' i := by
  have h1 := gold_band_low_carrier_tail_min N Q a Ps ε₀ j k' QR Dlev (goldCut N (k + 1)) i
    hQPs hQNa hPsN hQ1 hb
  have h2 := gold_band_low_carrier_tail_min N Q a Ps ε₀ j k' QR Dlev (goldCut N k) i
    hQPs hQNa hPsN hQ1 hb
  unfold goldLowSurvSum goldBtailMin
  linarith [h1, h2]

/-- **`gold_band_sym_price_tail_min`.**  The two-cutoff sym-band survivor sum `goldSymSurvSum`
bounded by the min harmonic tail crumb `goldBtailMin Q bnd k' i`.  Sym mirror of
`gold_band_low_price_tail_min`. -/
theorem gold_band_sym_price_tail_min (N Q a Ps : ℕ) (ε₀ : ℝ) (j k' k : ℕ) (QR : ℝ) (Dlev i : ℕ)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    (hQ1 : 1 ≤ Q) (hb : 1 ≤ QR * Dlev) :
    goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) j k' k i ≤ goldBtailMin Q (QR * Dlev) k' i := by
  have h1 := gold_band_sym_carrier_tail_min N Q a Ps ε₀ j k' QR Dlev (goldCut N (k + 1)) i
    hQPs hQNa hPsN hQ1 hb
  have h2 := gold_band_sym_carrier_tail_min N Q a Ps ε₀ j k' QR Dlev (goldCut N k) i
    hQPs hQNa hPsN hQ1 hb
  unfold goldSymSurvSum goldBtailMin
  linarith [h1, h2]

/-! ## 2. The band firing crumb + the tail-routed geometric absorb -/

/-- **`goldBandBtailSlot`** — the band firing crumb: `0` on WIDE survivors
(`√(X_sub·M) ≥ D·L^{18}`), `goldBtailMin Q bnd k' i` on FIRING survivors.  Unlike the box's
`goldBtailMinSlot` there is NO DEAD-cap branch — the high-pass band survivors have no box-cap. -/
noncomputable def goldBandBtailSlot (D Q : ℕ) (bnd : ℝ) (k' i : ℕ) : ℝ :=
  if (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
     then 0
     else goldBtailMin Q bnd k' i

/-- **`gold_band_geo_absorb_tail`.**  The tail-routed geometric absorb: a per-`(k, i)` band price
bounded on each survivor by `geo grade + Btail k i` absorbs — over the `≤ 3` survivors and the
annuli — to `24·Cgeo·Kc·N/(log N)^{12} + Σ_k Σ_i Btail k i`.  `gold_band_geo_absorb` handles the geo
head; the crumb sum splits off additively (`Finset.sum_add_distrib`). -/
theorem gold_band_geo_absorb_tail {N K : ℕ} {Kc Cgeo : ℝ} (Ne Me : ℕ)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hMcard : Me ≤ 2 * (Ne + 1))
    (P : ℕ → ℕ → ℝ) (Btail : ℕ → ℕ → ℝ)
    (hP : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          P k i ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k i) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
      ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
        + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary Ne Me
              (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, Btail k i := by
  classical
  have hsplit : (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
      ≤ (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k i)) :=
    Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun i hi => hP k hk i hi))
  have hdist : (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k i))
      = (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
        + (∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary Ne Me
              (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, Btail k i) := by
    simp only [Finset.sum_add_distrib]
  have hgeo := gold_band_geo_absorb (N := N) (K := K) Ne Me hCgeo0 hKc0 hN1 hMcard
    (fun k i => Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
    (fun k _ i _ => le_refl _)
  calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
      ≤ _ := hsplit
    _ = _ := hdist
    _ ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
        + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary Ne Me
              (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, Btail k i := by
        linarith [hgeo]

/-! ## 3. The tail-routed band legs — `hlow`/`hsym` with the band crumb -/

/-- **`gold_band_hlow_tail`** — the terminal's `hlow` slot WITH a band crumb routed.
`gold_band_hlow`
(BandPrice) with the per-survivor grade allowed an additive tail `Btail k' k i` (the geo grade fails
on firing survivors; there the crumb `goldBtailMin` carries the price): the annulus/survivor double
sum `goldPlowK` absorbs to `Wband := 24·Cgeo·Kc·N/(log N)^{12}` PLUS the routed crumb sum
`Σ_k Σ_i Btail k' k i`.  The shape slots where the pure `gold_band_hlow` sat, with the band crumb
joining the terminal's `htail`. -/
theorem gold_band_hlow_tail {N K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ) {Kc Cgeo : ℝ}
    (Btail : ℕ → ℕ → ℕ → ℝ)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hgeo : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          goldLowSurvSum N Q a Ps ε₀ bound 0 k' k i
            ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k' k i) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPlowK N K Q a Ps ε₀ bound 0 k'
        ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
          + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, Btail k' k i := by
  intro k' hk'
  have hMcard : pieceM k' ≤ 2 * (pieceN k' + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  exact gold_band_geo_absorb_tail (pieceN k') (pieceM k') hCgeo0 hKc0 hN1 hMcard
    (fun k i => goldLowSurvSum N Q a Ps ε₀ bound 0 k' k i) (Btail k') (hgeo k' hk')

/-- **`gold_band_hsym_tail`** — the terminal's `hsym` slot WITH a band crumb routed.  Sym mirror of
`gold_band_hlow_tail` at the `max`-collapse boundary `dyadicBoundary (max (opY N) (pieceN k'))
(pieceM k')`. -/
theorem gold_band_hsym_tail {N K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ) {Kc Cgeo : ℝ}
    (Btail : ℕ → ℕ → ℕ → ℝ)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hgeo : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          goldSymSurvSum N Q a Ps ε₀ bound 0 k' k i
            ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 + Btail k' k i) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPsymK N K Q a Ps ε₀ bound 0 k'
        ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12
          + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, Btail k' k i := by
  intro k' hk'
  have hMcard : pieceM k' ≤ 2 * (max (opY N) (pieceN k') + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    have h3 : pieceN k' ≤ max (opY N) (pieceN k') := le_max_right _ _
    unfold pieceM pieceN at *; omega
  exact gold_band_geo_absorb_tail (max (opY N) (pieceN k')) (pieceM k') hCgeo0 hKc0 hN1 hMcard
    (fun k i => goldSymSurvSum N Q a Ps ε₀ bound 0 k' k i) (Btail k') (hgeo k' hk')

/-! ## 4. The handoff for G-SURV-2 — byte-locks

The composition G-SURV-2 assembles the per-survivor discharge `goldLowSurvSum ≤ geo + slot`
(`goldBandBtailSlot`) from the WIDE branch (node 1–2: `gold_band_box_kerr` →
`gold_band_survsum_geoN`
on the high annuli the high-pass band populates) and the FIRING branch (this file:
`gold_band_low_price_tail_min` → `goldBtailMin ≤ geo + goldBtailMin`), feeds `gold_band_hlow_tail` /
`gold_band_hsym_tail`, and routes the crumb sums into the terminal's `htail`.  The residual for
G-SURV-2 (the terminal `htail` re-wiring: the sym crumb boundary reconciliation `max (opY N)
(pieceN k') → pieceN k'` and the `goldBandBtailSlot` tower close) is recorded in the report. -/

section Handoff

-- node 1–2 (BandWin.lean): the liveness-free band price engine at the band floor
#check @Salt.Goldbach.gold_d0_window_band
#check @Salt.Goldbach.gold_box_price_engine_at_band
#check @Salt.Goldbach.gold_band_box_kerr
#check @Salt.Goldbach.gold_band_survsum_geoN
-- node 3 (this file): the firing pricers + the tail-routed band legs
#check @Salt.Goldbach.gold_band_low_price_tail_min
#check @Salt.Goldbach.gold_band_sym_price_tail_min
#check @Salt.Goldbach.gold_band_geo_absorb_tail
#check @Salt.Goldbach.gold_band_hlow_tail
#check @Salt.Goldbach.gold_band_hsym_tail
-- the landed suppliers this composes (min-side symmetry / trivial tail / geo absorb / crumb)
#check @Salt.Goldbach.apDiscBilinCutoff_symm
#check @Salt.Goldbach.gold_box_disc_trivial_min
#check @Salt.Goldbach.gold_box_tail_min
#check @Salt.Goldbach.min_le_sqrt_mul
#check @Salt.Goldbach.gold_band_geo_absorb
-- the pure band legs these tail variants supersede + the terminal whose slots they fill
#check @Salt.Goldbach.gold_band_hlow
#check @Salt.Goldbach.gold_band_hsym
#check @Salt.Goldbach.gold_hBVblocksW_at_op_band

/-- **The firing-branch per-survivor discharge (WIDE ∪ FIRING), low leg.**  On a survivor the low
band price is `≤ geo grade + goldBandBtailSlot`: WIDE (`√(X·M) ≥ D·L^{18}`) via the geo grade
`hwide`
(node 1–2) with the crumb `0`; FIRING via `gold_band_low_price_tail_min` (the min tail
`goldBtailMin`) added to the nonneg geo grade.  This is the `hgeo` input `gold_band_hlow_tail`
consumes, with `Btail k' k i := goldBandBtailSlot D Q bnd k' i`. -/
example (N Q a Ps : ℕ) (ε₀ : ℝ) (_j k' k : ℕ) (QR : ℝ) (Dlev i D : ℕ) {Kc Cgeo : ℝ}
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

end Handoff

end Salt.Goldbach
