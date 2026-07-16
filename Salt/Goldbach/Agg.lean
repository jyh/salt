/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.PriceClose
import Salt.Chen.MediumFloor
import Salt.Chen.AggCE

/-!
# G-AGG (seam 1) — the per-annulus row aggregate `gold_hSum_at_op` (Goldbach)

Design: the twin's `Salt/Chen/AggSum.lean` (`hSum_at_op`) and `Salt/Chen/FinA3c.lean` (the
`hbox`/`hsym`/`hlow` worst-`W` assembly), reshaped to the OUTER DYADIC ANNULUS axis.  This is the
Goldbach mirror of the twin's `hSum` slot closure: the box/sym/low per-boundary prices — supplied
by `gold_box_price_engine` through the SW2 annulus telescopes (`gold_hNum_at_opW` /
`gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc`) — summed over the
blocks/pieces/annuli/boundaries close into the `Ccon·Kc·N/(log N)^{11}` shape that
`gold_hNum_close_of_tower` consumes and `gold_hBVblocksW_discharge'` names as its `hSum` slot.

## The annulus axis costs ONE extra `log`

Where the twin prices a SINGLE factor-2 window (`Σ_k Σ_i` = pieces × boundaries, one `log`), the
Goldbach box part is `Σ_{k'} Σ_k Σ_i` = pieces × annuli × boundaries — TWO `log`s.  So the box
per-boundary bound `Wbox` enters at `Ccon·Kc·N/(log N)^{13}` (one power deeper than the twin's
`^{12}`); the band per-piece bounds `Wband` (whose annulus `Σ_k` is already folded inside
`PsymK`/`PlowK` by the SW2 telescopes) enter at `^{12}`.  Both close to `^{11}`; the extra annulus
`log` is the `A+1` saving Opt-A pays (dwarfed by the tower `log N ≥ w'^{w'}`).

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* `gold_log_absorb` — the one-`log` numeric absorb `cnt·val ≤ 2C/L^p` (`cnt ≤ 2 log N`).
* **`gold_hSum_at_op`** — the exact `hSum` slot of `gold_hBVblocksW_discharge'` at the single-block
  operating point (`maxBlock N z ε₀ = 0`), from the uniform worst-`W` per-boundary / per-piece
  price bounds and the abstract diagonal budget row.  `RHD := (12·Ccon_box + 3·Ccon_band +
  Ccon_diag/2)·Kc·N/(log N)^{11}`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The one-`log` numeric absorb -/

/-- **`gold_log_absorb`.**  A single annulus/piece `Σ` (count `cnt ≤ 2 log N`) of a value
`val ≤ C/L^{p+1}` closes one power of `L`: `cnt·val ≤ 2C/L^p`.  Applied twice for the box
(pieces × annuli), once for each band leg. -/
theorem gold_log_absorb {L cnt C val : ℝ} {p : ℕ} (hL : 0 < L)
    (_hcnt0 : 0 ≤ cnt) (hcnt : cnt ≤ 2 * L) (_hC0 : 0 ≤ C) (hval0 : 0 ≤ val)
    (hval : val ≤ C / L ^ (p + 1)) :
    cnt * val ≤ 2 * C / L ^ p := by
  have hLp : (0 : ℝ) < L ^ p := pow_pos hL p
  have hLp1 : (0 : ℝ) < L ^ (p + 1) := pow_pos hL (p + 1)
  calc cnt * val ≤ (2 * L) * val := mul_le_mul_of_nonneg_right hcnt hval0
    _ ≤ (2 * L) * (C / L ^ (p + 1)) := mul_le_mul_of_nonneg_left hval (by positivity)
    _ = 2 * C / L ^ p := by
        rw [pow_succ]
        have hne : L ^ p ≠ 0 := hLp.ne'
        have hne1 : L ≠ 0 := hL.ne'
        field_simp

/-! ## 2. The `hSum` aggregate at the operating point -/

set_option maxHeartbeats 1000000 in
-- the nested annulus/piece `Σ`-closures elaborate a long product/division chain; the numeric
-- `gold_log_absorb` folds and the final `ring` need headroom above the default heartbeat budget.
/-- **`gold_hSum_at_op` — the `hSum` slot of `gold_hBVblocksW_discharge'`.**  At the single-block
operating point (`hmax : maxBlock N z ε₀ = 0`), the box quadruple sum `Σ_j Σ_{k'} Σ_k Σ_i` (each
per-boundary price `≤ Wbox`, ≤ 3 boundaries per annulus by `dyadicBoundary_card_le_three`) and the
band single sums `Σ_{k'} PsymK`/`PlowK` (each per-piece price `≤ Wband`, the annulus `Σ_k` folded
inside) plus the diagonal budget `Pdiag` close to `RHD := (12·Ccon_box + 3·Ccon_band +
Ccon_diag/2)·Kc·N/(log N)^{11}`.  Mirrors `Salt.Chen.hSum_at_op` at the annulus axis. -/
theorem gold_hSum_at_op (N z y K : ℕ) (ε₀ : ℝ) (Kc : ℝ)
    (Price : ℕ → ℕ → ℕ → ℕ → ℝ) (PsymK PlowK : ℕ → ℕ → ℝ)
    (Pdiag Wbox Wband Ccon_box Ccon_band Ccon_diag : ℝ)
    (hmax : maxBlock N z ε₀ = 0)
    (hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log N)
    (hWbox0 : 0 ≤ Wbox) (hWband0 : 0 ≤ Wband)
    (hCb0 : 0 ≤ Ccon_box) (hCband0 : 0 ≤ Ccon_band)
    (hbox : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i ≤ Wbox)
    (hsym : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k' ≤ Wband)
    (hlow : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k' ≤ Wband)
    (hWbox : Wbox ≤ Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13)
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
      ≤ (12 * Ccon_box + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  classical
  set L : ℝ := Real.log N with hLdef
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hcnt0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by positivity
  -- the counting facts for `dyadicBoundary_card_le_three`
  have hMcard : ∀ k' : ℕ, pieceM k' ≤ 2 * (pieceN k' + 1) := by
    intro k'
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  -- BOX leg: per (k', k) the ≤3 boundaries collapse to `3·Wbox`
  have hcell : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
      (∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i) ≤ 3 * Wbox := by
    intro k' hk' k hk
    have hcard : (dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (z * y) K).card ≤ 3 :=
      dyadicBoundary_card_le_three (hMcard k') (goldCut_succ_le_two_mul N k)
    calc (∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ (dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K).card • Wbox :=
          Finset.sum_le_card_nsmul _ _ _ (fun i hi => hbox k' hk' k hk i hi)
      _ = ((dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K).card : ℝ) * Wbox := nsmul_eq_mul _ _
      _ ≤ 3 * Wbox := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hWbox0
  -- BOX per-piece: absorb the annulus `Σ_k` (one `log`, `^{13} → ^{12}`)
  have hbk : ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ 6 * Ccon_box * Kc * (N : ℝ) / L ^ 12 := by
    intro k' hk'
    have hstep : (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (3 * Wbox) := by
      calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
          ≤ ∑ _k ∈ Finset.range (Nat.log 2 N + 1), 3 * Wbox :=
            Finset.sum_le_sum (fun k hk => hcell k' hk' k hk)
        _ = ((Nat.log 2 N : ℝ) + 1) * (3 * Wbox) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hval : (3 : ℝ) * Wbox ≤ 3 * Ccon_box * Kc * (N : ℝ) / L ^ 13 := by
      calc (3 : ℝ) * Wbox ≤ 3 * (Ccon_box * Kc * (N : ℝ) / L ^ 13) :=
            mul_le_mul_of_nonneg_left hWbox (by norm_num)
        _ = 3 * Ccon_box * Kc * (N : ℝ) / L ^ 13 := by ring
    have habs := gold_log_absorb (L := L) (cnt := (Nat.log 2 N : ℝ) + 1)
      (C := 3 * Ccon_box * Kc * (N : ℝ)) (val := 3 * Wbox) (p := 12)
      hlogpos hcnt0 hcount (by positivity) (by positivity) hval
    calc (∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (3 * Wbox) := hstep
      _ ≤ 2 * (3 * Ccon_box * Kc * (N : ℝ)) / L ^ 12 := habs
      _ = 6 * Ccon_box * Kc * (N : ℝ) / L ^ 12 := by ring
  -- BOX total: absorb the piece `Σ_{k'}` (one `log`, `^{12} → ^{11}`)
  have hboxtot : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
        ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
      ≤ 12 * Ccon_box * Kc * (N : ℝ) / L ^ 11 := by
    have hstep : (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
          ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (6 * Ccon_box * Kc * (N : ℝ) / L ^ 12) := by
      calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), _)
          ≤ ∑ _k' ∈ Finset.range (Nat.log 2 N + 1), 6 * Ccon_box * Kc * (N : ℝ) / L ^ 12 :=
            Finset.sum_le_sum hbk
        _ = ((Nat.log 2 N : ℝ) + 1) * (6 * Ccon_box * Kc * (N : ℝ) / L ^ 12) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have habs := gold_log_absorb (L := L) (cnt := (Nat.log 2 N : ℝ) + 1)
      (C := 6 * Ccon_box * Kc * (N : ℝ)) (val := 6 * Ccon_box * Kc * (N : ℝ) / L ^ 12) (p := 11)
      hlogpos hcnt0 hcount (by positivity) (by positivity) (le_refl _)
    calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), _)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (6 * Ccon_box * Kc * (N : ℝ) / L ^ 12) := hstep
      _ ≤ 2 * (6 * Ccon_box * Kc * (N : ℝ)) / L ^ 11 := habs
      _ = 12 * Ccon_box * Kc * (N : ℝ) / L ^ 11 := by ring
  -- BAND legs: one `log` each (the annulus `Σ_k` is already inside `PsymK`/`PlowK`)
  have hbandleg : ∀ (P : ℕ → ℝ), (∀ k' ∈ Finset.range (Nat.log 2 N + 1), P k' ≤ Wband) →
      (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k') ≤ 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11 := by
    intro P hP
    have hstep : (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k')
        ≤ ((Nat.log 2 N : ℝ) + 1) * Wband := by
      calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k')
          ≤ ∑ _k' ∈ Finset.range (Nat.log 2 N + 1), Wband := Finset.sum_le_sum hP
        _ = ((Nat.log 2 N : ℝ) + 1) * Wband := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have habs := gold_log_absorb (L := L) (cnt := (Nat.log 2 N : ℝ) + 1)
      (C := Ccon_band * Kc * (N : ℝ)) (val := Wband) (p := 11)
      hlogpos hcnt0 hcount (by positivity) hWband0 hWband
    calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1), P k')
        ≤ ((Nat.log 2 N : ℝ) + 1) * Wband := hstep
      _ ≤ 2 * (Ccon_band * Kc * (N : ℝ)) / L ^ 11 := habs
      _ = 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11 := by ring
  have hsigsym := hbandleg (fun k' => PsymK 0 k') hsym
  have hsiglow := hbandleg (fun k' => PlowK 0 k') hlow
  -- assemble the single-block aggregate
  simp only [hmax, Nat.zero_add, Finset.sum_range_one]
  have hhalfsym : (1 / 2 : ℝ) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k')
      ≤ (1 / 2) * (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11) :=
    mul_le_mul_of_nonneg_left hsigsym (by norm_num)
  have hhalfdiag : (1 / 2 : ℝ) * Pdiag ≤ (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / L ^ 11) :=
    mul_le_mul_of_nonneg_left hPdiag (by norm_num)
  calc (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K, Price 0 k' k i)
          + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PsymK 0 k')
             + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), PlowK 0 k') + (1 / 2) * Pdiag)
      ≤ 12 * Ccon_box * Kc * (N : ℝ) / L ^ 11
          + ((1 / 2) * (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11)
             + 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
             + (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / L ^ 11)) :=
        add_le_add hboxtot (add_le_add (add_le_add hhalfsym hsiglow) hhalfdiag)
    _ = (12 * Ccon_box + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / L ^ 11 := by ring

end Salt.Goldbach
