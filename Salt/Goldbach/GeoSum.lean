/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BoxRows
import Salt.Chen.AggSum

/-!
# G-GEOSUM — the geometric-sum final pricing (Goldbach), part I: (i)+(ii)+(iii)

Design: the adjudicated redesign of the count·max annulus absorption (G-HPRICE catch #3).  The
`hSum` slot of `gold_hBVblocksW_discharge'` carries the OUTER dyadic annulus sum `Σ_k` on the box
leg; the count·max absorb (`gold_hSum_at_op`'s `hbox`/`hbk`) demands a UNIFORM per-box price at
`/L^{13}`, which is FALSE at top-annulus live boxes (there `X·M ≈ N`, so `boxPriceKerr ≈ Kc·N/L^{12}
= Kc·N·L/L^{13} ≫ Kc·N/L^{13}`).  The fix is the GEOMETRIC-SUM absorption:

* **(i) `gold_boxPriceKerr_geo`** — the honest per-annulus price `boxPriceKerr Kc kp i ≤
  gboxConst·Kc·goldCut N (k+1)/L^{12}` (`L := log(X·M)`), the Goldbach mirror of the twin's
  `boxPriceKerr_worst_le` at the annulus scale (`X·M ≤ 4·goldCut N (k+1)` via `gold_box_XM_scale`).
* **(ii) `gold_goldCut_geosum`** — the geometric series `Σ_{k<⌊log₂N⌋+1} goldCut N (k+1) ≤ 8·N`
  (each `min(2^{k+1}, N/2) ≤ 2^{k+1}`, telescoping to `2^{K+2} ≤ 4·N`).
* **(iii) `gold_hSum_geo`** — the SAME LHS as `gold_hSum_at_op` (the terminal's `hSum` slot,
  character-for-character), but internally the box leg absorbs the annulus `Σ_k` GEOMETRICALLY
  (via (ii)) plus a SEPARATE additive tail crumb `Btail`; the RHS lands at
  `(48·Cgeo + Ctail + 3·Ccon_band + Ccon_diag/2)·Kc·N/L^{11}`, feeding `gold_hNum_close_of_tower`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## (i) The per-annulus honest price constant -/

/-- **`gboxConst`** — the honest geometric per-annulus box constant,
`2250816·(31/10)^{50} ≈ 8.3·10^{30}`.  `2250816 = 8·281352` (`8 = 2·4`: the `2` of `boxPriceKerr`,
the `4` of `X·M ≤ 4·goldCut N (k+1)`; `281352 = 1 + 6 + 2^{18} + 19201` the bracket coefficient
after folding the additive constants into `S ≥ 1`); `(31/10)^{50}` the worst-c ratio power.  This is
the twin's `CconBox` numerator WITHOUT the `/(9/10)^{12}` `log x`-transfer (we keep `L := log(X·M)`
in the denominator). -/
noncomputable def gboxConst : ℝ := 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ)

theorem gboxConst_nonneg : 0 ≤ gboxConst := by unfold gboxConst; positivity

set_option maxHeartbeats 1600000 in
-- the `boxPriceKerr` unfold carries a long rpow-bearing bracket; the Kerr-minima bounds
-- (`kerr_ratio_term_le`), the `nlinarith` bracket fold, and the `field_simp`/`ring` closes need
-- headroom above the default heartbeat budget.
/-- **`gold_boxPriceKerr_geo` (i) — the honest per-annulus box price.**  For a Goldbach
outer-annulus box (`i ∈ dyadicBoundary … (goldCut N ka) (goldCut N (ka+1)) …`) at the worst-c ratio
`(10/31)·log(X·M) ≤ log(2^{kp})` (met by every LIVE box), with `Kc ≥ 1` and `1 ≤ log(X·M)`:
`boxPriceKerr Kc kp i ≤ gboxConst·Kc·goldCut N (ka+1)/(log(X·M))^{12}`.  The Goldbach mirror of the
twin's `boxPriceKerr_worst_le` at the ANNULUS scale — `X·M ≤ 4·goldCut N (ka+1)`
(`gold_box_XM_scale`) replaces the window `X·M ≤ 4x`; we keep `L := log(X·M)` (no `log x`, so
`gboxConst =
CconBox·(9/10)^{12}`).  The dominant `6·Km_min·X·M/L^{13}` term carries `Km_min ≤ Kc·(31/10)^{50}·L`
at the live ratio, so the whole price is `≤ 2·281352·(31/10)^{50}·Kc·X·M/L^{12} ≤ gboxConst·Kc·
goldCut(ka+1)/L^{12}`. -/
theorem gold_boxPriceKerr_geo {N z y K kp ka i : ℕ} {Kc : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (z * y) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log ((2 ^ kp : ℕ) : ℝ)) :
    boxPriceKerr Kc kp i
      ≤ gboxConst * Kc * (goldCut N (ka + 1) : ℝ)
          / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (12 : ℝ) := by
  -- the per-annulus geometry: `X·M ≤ 4·goldCut N (ka+1)` (in ℝ).
  have hXM4gN : (2 ^ (i + 1) - 1 : ℕ) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi).2
  unfold boxPriceKerr gboxConst
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) with hXMdef
  set L : ℝ := Real.log XM with hLdef
  set logN : ℝ := Real.log ((2 ^ kp : ℕ) : ℝ) with hlogNdef
  have hXM4x : XM ≤ 4 * (goldCut N (ka + 1) : ℝ) := by
    rw [hXMdef]; exact_mod_cast hXM4gN
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXM1 : (1 : ℝ) ≤ XM := by
    have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM1 : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp
      have : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [hXMdef]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) :=
          mul_le_mul (by exact_mod_cast hX1) (by exact_mod_cast hM1) (by norm_num) (by positivity)
  have hXM0 : (0 : ℝ) ≤ XM := le_trans (by norm_num) hXM1
  have hKc0 : (0 : ℝ) ≤ Kc := by linarith
  -- the common bound `S := Kc·(31/10)^{50}·L`, and each Kerr term `≤ S`.
  set S : ℝ := Kc * (((31 : ℝ) / 10) ^ (50 : ℝ) * L) with hSdef
  have hterm : ∀ a e : ℝ, a ≤ 1 + e → 0 ≤ e → e ≤ 50 →
      Kc * (L ^ a / logN ^ e) ≤ S := by
    intro a e hae he0 he50
    rw [hSdef]
    exact mul_le_mul_of_nonneg_left (kerr_ratio_term_le hL1 hratio hae he0 he50) hKc0
  have hkb : Kbeta_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkm : Km_min Kc L logN 13 18 ≤ S := by
    rw [Km_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkb' : Kbeta'_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta'_min, mul_div_assoc]; exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hrpow1 : (1 : ℝ) ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hrL : (1 : ℝ) ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) * L := by nlinarith [hrpow1, hL1]
  have hSge1 : (1 : ℝ) ≤ S := by rw [hSdef]; nlinarith [hKc, hrL]
  have h26 : 32 * Real.sqrt 26 ≤ 192 := by
    have hs : Real.sqrt 26 ≤ 6 := by
      have h1 : Real.sqrt 26 ≤ Real.sqrt 36 := Real.sqrt_le_sqrt (by norm_num)
      have h2 : Real.sqrt 36 = 6 := by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith [h1, h2]
    linarith [hs]
  have h218 : (2 : ℝ) ^ ((13 : ℝ) + 5) = 262144 := by
    rw [show (13 : ℝ) + 5 = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hbracket : Kbeta_min Kc L logN 13 18
        + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1))
      ≤ 281352 * S := by
    rw [h218]; nlinarith [hkb, hkm, hkb', h26, hSge1]
  set BR : ℝ := Kbeta_min Kc L logN 13 18
      + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
        + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1)) with hBRdef
  have hL13pos : (0 : ℝ) < L ^ (13 : ℝ) := Real.rpow_pos_of_pos hLpos 13
  have hL12pos : (0 : ℝ) < L ^ (12 : ℝ) := Real.rpow_pos_of_pos hLpos 12
  have hL13 : L ^ (13 : ℝ) = L ^ (12 : ℝ) * L := by
    rw [show (13 : ℝ) = 12 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  have hstep1 : 2 * (BR * XM / L ^ (13 : ℝ)) ≤ (2 * (281352 * S)) * XM / L ^ (13 : ℝ) := by
    rw [show 2 * (BR * XM / L ^ (13 : ℝ)) = ((2 * BR) * XM) / L ^ (13 : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hL13pos).mpr
      (mul_le_mul_of_nonneg_right (by linarith [hbracket]) hXM0)
  have hLHSeq : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
      = 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ) := by
    rw [hSdef, hL13]; field_simp; ring
  have hc0 : (0 : ℝ) ≤ 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc := by positivity
  have hstep2 : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
      ≤ 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ) := by
    rw [hLHSeq]
    calc 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ)
        = (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc) * (XM / L ^ (12 : ℝ)) := by ring
      _ ≤ (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc)
            * (4 * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hL12pos).mpr hXM4x) hc0
      _ = 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (goldCut N (ka + 1) : ℝ) / L ^ (12 : ℝ) := by
          ring
  exact le_trans hstep1 hstep2

/-! ## (ii) The geometric series `Σ_k goldCut N (k+1) ≤ 8·N` -/

/-- Partial geometric sum: `Σ_{k<n} 2^{k+1} ≤ 2^{n+1}` (telescoping, `= 2^{n+1} − 2`). -/
private lemma sum_two_pow_succ_le (n : ℕ) :
    (∑ k ∈ Finset.range n, 2 ^ (k + 1)) ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc (∑ k ∈ Finset.range m, 2 ^ (k + 1)) + 2 ^ (m + 1)
          ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := Nat.add_le_add_right ih _
        _ = 2 ^ (m + 1 + 1) := by rw [pow_succ]; ring

/-- **`gold_goldCut_geosum` (ii).**  The outer-annulus cutoffs sum geometrically to `≤ 8·N`:
`Σ_{k<⌊log₂N⌋+1} goldCut N (k+1) ≤ Σ 2^{k+1} ≤ 2^{⌊log₂N⌋+2} ≤ 4·N ≤ 8·N` (`min(2^{k+1}, N/2) ≤
2^{k+1}`, `2^{⌊log₂N⌋} ≤ N`).  The geometric absorb that replaces the top-dominated count·max. -/
theorem gold_goldCut_geosum {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1), (goldCut N (k + 1) : ℝ)) ≤ 8 * (N : ℝ) := by
  have hnat : (∑ k ∈ Finset.range (Nat.log 2 N + 1), goldCut N (k + 1)) ≤ 8 * N := by
    calc (∑ k ∈ Finset.range (Nat.log 2 N + 1), goldCut N (k + 1))
        ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1), 2 ^ (k + 1) :=
          Finset.sum_le_sum (fun k _ => by unfold goldCut; exact min_le_left _ _)
      _ ≤ 2 ^ (Nat.log 2 N + 2) := sum_two_pow_succ_le _
      _ ≤ 8 * N := by
          have hpow : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
          have h4 : (2 : ℕ) ^ (Nat.log 2 N + 2) = 4 * 2 ^ Nat.log 2 N := by rw [pow_add]; ring
          omega
  calc (∑ k ∈ Finset.range (Nat.log 2 N + 1), (goldCut N (k + 1) : ℝ))
      = ((∑ k ∈ Finset.range (Nat.log 2 N + 1), goldCut N (k + 1) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
    _ ≤ 8 * (N : ℝ) := by exact_mod_cast hnat

/-! ## (iii) The geometric aggregate `gold_hSum_geo` -/

set_option maxHeartbeats 1600000 in
-- the nested annulus/piece `Σ`-closures + the geometric absorb elaborate a long product/division
-- chain; the `gold_log_absorb` folds and the final `ring` need headroom above the default budget.
/-- **`gold_hSum_geo` (iii) — the geometric `hSum` slot of `gold_hBVblocksW_discharge'`.**  The
SAME LHS as `gold_hSum_at_op` (the terminal's `hSum` slot, character-for-character): the box
quadruple sum `Σ_j Σ_{k'} Σ_k Σ_i Price` plus the band single sums and the diagonal budget.
Internally the box leg
is priced HONESTLY per annulus (`hbox`: `Price 0 k' k i ≤ Cgeo·Kc·goldCut N (k+1)/L^{12} + Btail`)
and the annulus `Σ_k` is absorbed GEOMETRICALLY (`hgeosum`: `Σ_k goldCut N (k+1) ≤ 8·N`, from (ii))
— NOT via the top-dominated count·max — leaving one piece `log` for `hcount`.  The tail crumb
`Btail` enters as a SEPARATE additive term (`htail`).  Bands/diagonal are unchanged from
`gold_hSum_at_op`.  RHS `RHD := (48·Cgeo + Ctail + 3·Ccon_band + Ccon_diag/2)·Kc·N/(log N)^{11}`. -/
theorem gold_hSum_geo (N z y K : ℕ) (ε₀ : ℝ) (Kc : ℝ)
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
      ≤ (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
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
  -- BAND legs: one `log` each (annulus `Σ_k` folded inside `PsymK`/`PlowK`), as `gold_hSum_at_op`.
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
      ≤ (48 * Cgeo * Kc * (N : ℝ) / L ^ 11 + Ctail * Kc * (N : ℝ) / L ^ 11)
          + ((1 / 2) * (2 * Ccon_band * Kc * (N : ℝ) / L ^ 11)
             + 2 * Ccon_band * Kc * (N : ℝ) / L ^ 11
             + (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / L ^ 11)) :=
        add_le_add hboxleg (add_le_add (add_le_add hhalfsym hsiglow) hhalfdiag)
    _ = (48 * Cgeo + Ctail + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / L ^ 11 := by ring

end Salt.Goldbach
