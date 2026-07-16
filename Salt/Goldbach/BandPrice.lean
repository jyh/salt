/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandEng
import Salt.Goldbach.RowsWide
import Salt.Goldbach.GeoSum

/-!
# G-BANDPRICE — the Goldbach band price rows at top-grade (A₃ terminal, items 1–2)

The two band legs (`hpriceSym`/`hpriceLow` and `hsym`/`hlow`) of `gold_hBVblocksW_at_op`
(`Final2.lean`).  Per the twin-geometry census (mirrored here), the FULL-width band `T`-difference
over an annulus `(goldCut N k, goldCut N (k+1)]` is decomposed by `box_disc_three_way` (T₂ =
`goldCut N (k+1)`, T₁ = `goldCut N k`) into the `≤ 3` `dyadicBoundary` survivor sub-boxes; each
survivor has reduced top `X_sub = 2^{i+1}−1` with cutoff-scale area `X_sub·M ≤ 4·goldCut N (k+1)`
(never the `N²`-lossy full width), priced by `gold_box_rows_wide` (generic carrier) to
`boxPriceKerr Kc k' i`.  Summed over the `≤ 3` survivors and the annuli `Σ_k` (with the geometric
absorb `Σ_k goldCut N (k+1) ≤ 8N`), the per-piece band price lands at `Wband := 24·Cgeo·Kc·N/L^12`.

This file lands (item 1–2 split, `BandPrice.lean`):

* **`gold_band_geo_absorb`** — the per-piece geometric absorb: a per-`(k, i)` price bounded by the
  honest annulus grade `Cgeo·Kc·goldCut N (k+1)/(log N)^{12}`, summed over the `≤ 3` survivors and
  the annuli, is `≤ 24·Cgeo·Kc·N/(log N)^{12}` — the `Wband` grade that `gold_band_hsym_slot`'s
  `Wband` slot consumes.  Mirror of `gold_hSum_geo`'s box-main absorb at the single-piece scale.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The per-piece geometric absorb (the `Wband` grade) -/

/-- **`gold_band_geo_absorb`.**  At a fixed piece `k'`, a per-`(k, i)` band price `P k i` bounded on
each `dyadicBoundary` survivor of the annulus `(goldCut N k, goldCut N (k+1)]` by the annulus
grade `Cgeo·Kc·goldCut N (k+1)/(log N)^{12}` absorbs — over the `≤ 3` survivors
(`dyadicBoundary_card_le_three`) and the annuli `Σ_k` (`gold_goldCut_geosum`,
`Σ_k goldCut N (k+1) ≤ 8N`) — to `≤ 24·Cgeo·Kc·N/(log N)^{12}`.  This is the `hsym`/`hlow` value
`Wband := 24·Cgeo·Kc·N/L^{12}` feeding `gold_band_hsym_slot`.  Mirror of `gold_hSum_geo`'s box-main
geometric absorb specialised to a single piece (no box-`Σ_{k'}`, no piece `log`). -/
theorem gold_band_geo_absorb {N K : ℕ} {Kc Cgeo : ℝ} (Ne Me : ℕ)
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hMcard : Me ≤ 2 * (Ne + 1))
    (P : ℕ → ℕ → ℝ)
    (hP : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          P k i ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
      ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12 := by
  classical
  -- per annulus `k`: sum over the `≤ 3` survivors of the honest grade
  have hcell : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
      (∑ i ∈ dyadicBoundary Ne Me
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
        ≤ 3 * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) := by
    intro k hk
    have hconst : (0 : ℝ) ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by positivity
    have hcard : (dyadicBoundary Ne Me
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K).card ≤ 3 :=
      dyadicBoundary_card_le_three hMcard (goldCut_succ_le_two_mul N k)
    calc (∑ i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
        ≤ ∑ _i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 :=
          Finset.sum_le_sum (hP k hk)
      _ = (dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K).card
            * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hconst
  -- absorb over the annuli via the geometric series
  calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary Ne Me
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, P k i)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          3 * (Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :=
        Finset.sum_le_sum hcell
    _ = 3 * Cgeo * Kc / (Real.log N) ^ 12
          * (∑ k ∈ Finset.range (Nat.log 2 N + 1), (goldCut N (k + 1) : ℝ)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    _ ≤ 3 * Cgeo * Kc / (Real.log N) ^ 12 * (8 * (N : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (gold_goldCut_geosum hN1) ?_
        positivity
    _ = 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12 := by ring

/-! ## 2. The low-band leg — `box_disc_three_way` per annulus + the geo absorb

The terminal's `hpriceLow`/`hlow` slots.  The full-width low carrier
`restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k')) (min (opZ N·pieceN k'+1) (N/2+1))
(N/2+1)` telescopes over the annuli; each annulus difference is decomposed by `box_disc_three_way`
(support floor `medium_support_floor_low`, `F = opZ N·opY N`) into the `≤ 3` `dyadicBoundary`
survivors at reduced top `2^{i+1}−1`.  The one analytic input NOT landed here (terminal-owned, the
per-survivor cutoff-scale price via `gold_box_rows_wide` at the LIVE floor, `0` on DEAD): the geo
grade `goldLowSurvSum ≤ Cgeo·Kc·goldCut N (k+1)/(log N)^{12}`, taken as `hgeo`. -/

open Classical in
/-- The low-band survivor sub-carrier at dyadic index `i` (the `box_disc_three_way` sub-block). -/
noncomputable def goldLowSub (N : ℕ) (ε₀ : ℝ) (j k' i : ℕ) : ℕ → ℂ :=
  restrictAlpha (restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k'))
    (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1)) (2 ^ i) (2 ^ (i + 1))

open Classical in
/-- The low-band per-survivor two-cutoff price at annulus `(goldCut N k, goldCut N (k+1)]`. -/
noncomputable def goldLowSurvSum (N Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' k i : ℕ) : ℝ :=
  (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
      ‖apDiscBilinCutoff (goldLowSub N ε₀ j k' i) (blockPrimeInd (pieceN k'))
          (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
    + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (goldLowSub N ε₀ j k' i) (blockPrimeInd (pieceN k'))
            (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m (goldCut N k)‖)

open Classical in
/-- The concrete `PlowK` value: the annulus/survivor double sum of `goldLowSurvSum`. -/
noncomputable def goldPlowK (N K Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.log 2 N + 1),
    ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldLowSurvSum N Q a Ps ε₀ bound j k' k i

/-- **`gold_band_hpriceLow`** — the terminal's `hpriceLow` slot, at `PlowK := goldPlowK`.  Per piece
`k'`, the annulus telescope of the low carrier's cutoff-differences is decomposed annulus by annulus
by `box_disc_three_way` into the survivor prices `goldLowSurvSum`.  Character-for-character the
`Final2` `hpriceLow` binder. -/
theorem gold_band_hpriceLow {N X K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, 2 ^ (i + 1) ≤ X + 1) :
    ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ ((Nat.divisors Ps).filter
            (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k'))
                (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
              (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N (k + 1))
            - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k'))
                (min (opZ N * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
              (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N k)‖) ≤ goldPlowK N K Q a Ps ε₀ bound j k' := by
  classical
  intro j k' _
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact box_disc_three_way K hK (goldCut_mono N (Nat.le_succ k))
    (fun m hm => medium_support_floor_low hm)
    (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d))
    (fun m => crtClassG Q (m / Q) N a) (goldLowSurvSum N Q a Ps ε₀ bound j k' k)
    (hiX k' k) (fun i _ => le_of_eq (by unfold goldLowSurvSum goldLowSub; rfl))

/-- **`gold_band_hlow`** — the terminal's `hlow` slot, at `PlowK := goldPlowK`, block `0`.  The
annulus/survivor double sum of `goldLowSurvSum`, geo-graded per survivor (`hgeo`), absorbs to
`Wband := 24·Cgeo·Kc·N/(log N)^{12}` via `gold_band_geo_absorb`. -/
theorem gold_band_hlow {N K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ) {Kc Cgeo : ℝ}
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hgeo : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          goldLowSurvSum N Q a Ps ε₀ bound 0 k' k i
            ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPlowK N K Q a Ps ε₀ bound 0 k' ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12 := by
  intro k' hk'
  have hMcard : pieceM k' ≤ 2 * (pieceN k' + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  exact gold_band_geo_absorb (pieceN k') (pieceM k') hCgeo0 hKc0 hN1 hMcard
    (fun k i => goldLowSurvSum N Q a Ps ε₀ bound 0 k' k i) (hgeo k' hk')

/-! ## 3. The sym-band leg — `box_disc_three_way` at the `max`-collapse indicator

The terminal's `hpriceSym`/`hsym` slots.  The sym carrier `blockAlphaSym (opZ N) (opY N) ε₀ j
(pieceN k') (pieceM k')` prices against `blockPrimeInd (max (opY N) (pieceN k'))`, so its
`box_disc_three_way` split lives on `dyadicBoundary (max (opY N) (pieceN k')) (pieceM k') …`.
Its `hiX` (`2^{i+1} ≤ X+1`) is NOT the terminal's `pieceN k'` `hiX`; it is re-derived from the wide
window `N/2 ≤ X` and the corner `2^i·(max+1) ≤ goldCut N (k+1) ≤ N/2` (`gold_band_sym_hiX`).
Support floor `medium_support_floor_sym`, `F = opZ N·opY N`.  Same terminal-owned analytic residual
`hgeo` (the per-survivor cutoff-scale price) as the low leg. -/

/-- **`gold_band_sym_hiX`.**  For a sym survivor `i ∈ dyadicBoundary Ne (pieceM k') … (goldCut N
(k+1)) …`, the reduced top clears the wide window: `2^{i+1} ≤ X+1`.  From the boundary corner
`2^i·(Ne+1) ≤ goldCut N (k+1) ≤ N/2` (with `Ne ≥ 1`, so `2·2^{i+1} ≤ 2^{i+1}·(Ne+1) ≤ N`) and
`N/2 ≤ X`. -/
theorem gold_band_sym_hiX {N X K Ne k' k i : ℕ} (hNe1 : 1 ≤ Ne) (hNX : N / 2 ≤ X)
    (hi : i ∈ dyadicBoundary Ne (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K) :
    2 ^ (i + 1) ≤ X + 1 := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  have hcorner : 2 ^ i * (Ne + 1) ≤ goldCut N (k + 1) := hi.2.1
  have hgc : goldCut N (k + 1) ≤ N / 2 := goldCut_le_half N (k + 1)
  have hkey : 2 * 2 ^ (i + 1) ≤ N := by
    have h1 : 2 * 2 ^ (i + 1) ≤ 2 ^ (i + 1) * (Ne + 1) := by
      have : 2 ≤ Ne + 1 := by omega
      calc 2 * 2 ^ (i + 1) = 2 ^ (i + 1) * 2 := by ring
        _ ≤ 2 ^ (i + 1) * (Ne + 1) := Nat.mul_le_mul_left _ this
    have h2 : 2 ^ (i + 1) * (Ne + 1) ≤ 2 * (2 ^ i * (Ne + 1)) := by
      rw [pow_succ]; ring_nf; omega
    omega
  omega

open Classical in
/-- The sym-band survivor sub-carrier at dyadic index `i` (the `box_disc_three_way` sub-block). -/
noncomputable def goldSymSub (N : ℕ) (ε₀ : ℝ) (j k' i : ℕ) : ℕ → ℂ :=
  restrictAlpha (blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k')) (2 ^ i) (2 ^ (i + 1))

open Classical in
/-- The sym-band per-survivor two-cutoff price at annulus `(goldCut N k, goldCut N (k+1)]`. -/
noncomputable def goldSymSurvSum (N Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' k i : ℕ) : ℝ :=
  (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
      ‖apDiscBilinCutoff (goldSymSub N ε₀ j k' i) (blockPrimeInd (max (opY N) (pieceN k')))
          (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
    + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (goldSymSub N ε₀ j k' i) (blockPrimeInd (max (opY N) (pieceN k')))
            (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m (goldCut N k)‖)

open Classical in
/-- The concrete `PsymK` value: the annulus/survivor double sum of `goldSymSurvSum`. -/
noncomputable def goldPsymK (N K Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.log 2 N + 1),
    ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldSymSurvSum N Q a Ps ε₀ bound j k' k i

/-- **`gold_band_hpriceSym`** — the terminal's `hpriceSym` slot, at `PsymK := goldPsymK`.  The sym
annulus telescope decomposed annulus by annulus by `box_disc_three_way` at the `max`-collapse
indicator.  Character-for-character `Final2`'s `hpriceSym` binder. -/
theorem gold_band_hpriceSym {N X K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ)
    (hK : Nat.log 2 X ≤ K) (hN1 : 1 ≤ N) (hNX : N / 2 ≤ X) :
    ∀ j, ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ ((Nat.divisors Ps).filter
            (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k'))
              (blockPrimeInd (max (opY N) (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N (k + 1))
            - apDiscBilinCutoff (blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k'))
              (blockPrimeInd (max (opY N) (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N k)‖) ≤ goldPsymK N K Q a Ps ε₀ bound j k' := by
  classical
  intro j k' _
  have hNe1 : 1 ≤ max (opY N) (pieceN k') := by
    refine le_trans ?_ (le_max_left _ _)
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hr : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow h1N (by norm_num)
    rw [opY]; exact Nat.le_floor (by push_cast; exact hr)
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact box_disc_three_way K hK (goldCut_mono N (Nat.le_succ k))
    (fun m hm => medium_support_floor_sym hm)
    (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d))
    (fun m => crtClassG Q (m / Q) N a) (goldSymSurvSum N Q a Ps ε₀ bound j k' k)
    (fun i hi => gold_band_sym_hiX hNe1 hNX hi)
    (fun i _ => le_of_eq (by unfold goldSymSurvSum goldSymSub; rfl))

/-- **`gold_band_hsym`** — the terminal's `hsym` slot, at `PsymK := goldPsymK`, block `0`. -/
theorem gold_band_hsym {N K Q a Ps : ℕ} (ε₀ : ℝ) (bound : ℝ) {Kc Cgeo : ℝ}
    (hCgeo0 : 0 ≤ Cgeo) (hKc0 : 0 ≤ Kc) (hN1 : 1 ≤ N)
    (hgeo : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          goldSymSurvSum N Q a Ps ε₀ bound 0 k' k i
            ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      goldPsymK N K Q a Ps ε₀ bound 0 k' ≤ 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12 := by
  intro k' hk'
  have hMcard : pieceM k' ≤ 2 * (max (opY N) (pieceN k') + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    have h3 : pieceN k' ≤ max (opY N) (pieceN k') := le_max_right _ _
    unfold pieceM pieceN at *; omega
  exact gold_band_geo_absorb (max (opY N) (pieceN k')) (pieceM k') hCgeo0 hKc0 hN1 hMcard
    (fun k i => goldSymSurvSum N Q a Ps ε₀ bound 0 k' k i) (hgeo k' hk')

end Salt.Goldbach
