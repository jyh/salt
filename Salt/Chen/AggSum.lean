/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AssembleA3
import Salt.Chen.ChenFinal

/-!
# Node HSUM — the Kerr aggregation `RHD ≤ Ccon·K·x/L^{11}` (new file, no edits to landed files)

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin8b` entry (the four-node re-scope: this
is the HSUM node) and the `PRICE-GATE`/`PRICE-3`/`PRICE-3b` entries (the honest worst-c aggregate
`RHD ≈ Ccon·K·x/L^{11}`).  This node supplies the *aggregation machinery* for the `hSum`
hypothesis of `hBVblocksW_discharge'`.

## The exact `hSum` shape this node targets (verbatim `PDiag.lean:729–735`)

`hBVblocksW_discharge'` (`Salt/Chen/PDiag.lean:682`) consumes an `hSum` hypothesis of shape

```
(∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
    ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price j k i)
      + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
         + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
         + (1 / 2) * Pdiag))) ≤ RHD
```

— the per-`j` band group ends in `(1/2)·Pdiag` per the PDiag design; `Pdiag` is left ABSTRACT
here (the HDIAG node bounds it), taken as a parameter with its own budget row `hPdiag`.

## What this file lands (sorry-free)

1. **`kerr_ratio_term_le`** — the rpow ratio engine: `L^a/logN^e ≤ (31/10)^50·L` under the
   worst-c ratio `(10/31)·L ≤ logN` (`R := L/logN ≤ 31/10`, the honest `c = 1/3` band floor).
2. **`boxPriceKerr_worst_le`** — THE honest worst-price bound: a priced box's closed Kerr price
   `boxPriceKerr Kc k i ≤ Ccon_box·Kc·x/(log x)^{12}` with the explicit
   `Ccon_box = 2250816·(31/10)^{50}/(9/10)^{12}` (≈ `2.95·10^{31}`).
3. **`hSum_at_op`** — the aggregation: single block (`maxBlock = 0`, `ε₀ := x`), ≤ 3 boundary
   boxes per piece (`dyadicBoundary_card_le_three`), `(Nat.log 2 x + 1)` pieces, each priced ≤ a
   uniform worst `W`, plus `(1/2)·Pdiag`, closing to `(9·Ccon_box + Ccon_diag/2)·Kc·x/(log x)^{11}`.
4. **`nat_log2_count_le`** — the piece-count bound `Nat.log 2 x + 1 ≤ 2·log x`.
5. **`hSum_slot_match`** — a compiled example: `hSum_at_op` closes the verbatim `hSum` slot of
   `hBVblocksW_discharge'` at `RHD := Ccon'·Kc·x/(log x)^{11}`.

## ★ CATCH #74 — the honest worst-c constant EXCEEDS `3.5·10²³` (reported, not a blocker) ★

The gate/PRICE-3b prose carried `Ccon = 3.5·10²³` from the `c = 7/16` box floor.  The honest band
floor is `c = 1/3` (`ChenFinal` catch #72: the band carriers vanish only at `2^k ≲ x^{1/3}`, so a
LIVE band box has `2^k ≳ x^{1/3}`, ratio `R = L/logN ≈ 3`).  Redone honestly at `R = 31/10`
(Lean-safe over `R = 3`): the dominant per-box term is `2·2^{18}·R^{50}·K·XM/L^{12}` with
`(31/10)^{50} ≈ 3.70·10^{24}`, so `Ccon_box ≈ 2.95·10^{31}` and the aggregate
`Ccon' = 9·Ccon_box + Ccon_diag/2 ≈ 2.7·10^{32}` — LARGER than `3.5·10²³` by ~9 orders.  This is
FINE: `hNum_close_of_tower` (`PriceClose.lean:219`) takes `Ccon` as a free PARAMETER (its `3.5·10²³`
is docstring-only), and `tower_budget` is generic in `m ≤ L`, so `fin8c` instantiates the closure
at THIS `Ccon'`; `2·Ccon'·Kc ≤ log x` holds with astronomic room (`log x₀ ≥ w'^{w'}`,
`w' ~ exp(2·10⁹)`).  Both values recorded per catch-#74 discipline.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The rpow ratio engine (deliverable 1)

For `L ≥ 1` and the worst-c ratio `(10/31)·L ≤ logN` (i.e. `L/logN ≤ 31/10`), a Kerr-shaped
quotient `L^a/logN^e` with `a ≤ 1 + e` and `0 ≤ e ≤ 50` is bounded by `(31/10)^{50}·L`.  The
route avoids inverse lemmas: `L^a ≤ L^{1+e} = (31/10)^e·L·((10/31)^e·L^e) ≤ (31/10)^e·L·logN^e`,
then divide by `logN^e > 0` and bump the coefficient `(31/10)^e ≤ (31/10)^{50}`. -/

/-- **`kerr_ratio_term_le` (deliverable 1).**  Under the worst-c ratio `(10/31)·L ≤ logN` with
`1 ≤ L`, `a ≤ 1 + e`, `0 ≤ e ≤ 50`: `L^a / logN^e ≤ (31/10)^{50} · L`. -/
theorem kerr_ratio_term_le {L logN a e : ℝ}
    (hL1 : 1 ≤ L) (hlogN : (10 / 31 : ℝ) * L ≤ logN)
    (hae : a ≤ 1 + e) (he0 : 0 ≤ e) (he50 : e ≤ 50) :
    L ^ a / logN ^ e ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) * L := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hbase : (0 : ℝ) ≤ (10 / 31 : ℝ) * L := by positivity
  have hlogNpos : (0 : ℝ) < logN := lt_of_lt_of_le (by positivity) hlogN
  have hmono : ((10 / 31 : ℝ) * L) ^ e ≤ logN ^ e := Real.rpow_le_rpow hbase hlogN he0
  have hsplit : ((10 / 31 : ℝ) * L) ^ e = (10 / 31 : ℝ) ^ e * L ^ e :=
    Real.mul_rpow (by norm_num) hLpos.le
  have hkey : L ^ a ≤ ((31 : ℝ) / 10) ^ e * L * logN ^ e := by
    have hid : ((31 : ℝ) / 10) ^ e * L * ((10 / 31 : ℝ) ^ e * L ^ e) = L ^ (1 + e) := by
      have hc : ((31 : ℝ) / 10) ^ e * (10 / 31 : ℝ) ^ e = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num
      calc ((31 : ℝ) / 10) ^ e * L * ((10 / 31 : ℝ) ^ e * L ^ e)
          = (((31 : ℝ) / 10) ^ e * (10 / 31 : ℝ) ^ e) * (L * L ^ e) := by ring
        _ = 1 * (L * L ^ e) := by rw [hc]
        _ = L ^ (1 : ℝ) * L ^ e := by rw [one_mul, Real.rpow_one]
        _ = L ^ (1 + e) := (Real.rpow_add hLpos 1 e).symm
    have hae' : L ^ a ≤ L ^ (1 + e) := Real.rpow_le_rpow_of_exponent_le hL1 hae
    have hcoef_nn : (0 : ℝ) ≤ ((31 : ℝ) / 10) ^ e * L := by positivity
    calc L ^ a ≤ L ^ (1 + e) := hae'
      _ = ((31 : ℝ) / 10) ^ e * L * ((10 / 31 : ℝ) ^ e * L ^ e) := hid.symm
      _ ≤ ((31 : ℝ) / 10) ^ e * L * logN ^ e := by
          rw [hsplit] at hmono
          exact mul_le_mul_of_nonneg_left hmono hcoef_nn
  have hlogNe_pos : (0 : ℝ) < logN ^ e := Real.rpow_pos_of_pos hlogNpos e
  have hdiv : L ^ a / logN ^ e ≤ ((31 : ℝ) / 10) ^ e * L := by
    rw [div_le_iff₀ hlogNe_pos]; exact hkey
  have hexp : ((31 : ℝ) / 10) ^ e ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he50
  calc L ^ a / logN ^ e ≤ ((31 : ℝ) / 10) ^ e * L := hdiv
    _ ≤ ((31 : ℝ) / 10) ^ (50 : ℝ) * L := mul_le_mul_of_nonneg_right hexp hLpos.le

/-! ## 2. The honest worst-price bound (deliverable 2)

For a priced box (`i` in the pieceN-boundary, `X = 2^{i+1}−1`, `M = pieceM k`, `logN = log 2^k`)
at the worst-c ratio `(10/31)·L ≤ logN`, the closed Kerr price `boxPriceKerr Kc k i` is bounded
by the uniform `Ccon_box·Kc·x/(log x)^{12}`.  The three SW-coupling Kerr terms are each `≤ Kc·S`
with `S := (31/10)^{50}·L` (§1); the additive constants fold into `S ≥ 1` (`Kc ≥ 1`); the box
scaffold (`ChenFinal`) supplies `X·M ≤ 4x` and `L ≥ (9/10)·log x`. -/

/-- The honest aggregate box constant, `2250816·(31/10)^{50}/(9/10)^{12} ≈ 2.95·10^{31}`.
`2250816 = 8·281352`; `281352 = 1 + 6 + 2^{18} + 19201` (the bracket coefficient after folding
the `448/32√26/15360/1` constants into `S ≥ 1`); `8 = 2·4` (the `2` of `boxPriceKerr`, the `4` of
`X·M ≤ 4x`); `(31/10)^{50}` the worst-c ratio power; `/(9/10)^{12}` the `L ≥ (9/10)log x`
transfer. -/
noncomputable def CconBox : ℝ :=
  2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) / ((9 : ℝ) / 10) ^ (12 : ℝ)

theorem CconBox_nonneg : 0 ≤ CconBox := by
  unfold CconBox; positivity

/-- **`boxPriceKerr_worst_le` (deliverable 2).**  For a pieceN-boundary box at the worst-c ratio
`(10/31)·L ≤ log 2^k`, with `Kc ≥ 1`, `x ≥ 2`, `log x ≥ 10`:
`boxPriceKerr Kc k i ≤ CconBox·Kc·x/(log x)^{12}`.  The `hratio` row is met by every LIVE box
(box legs `2^k ≥ x^{7/16}/8`; middle-k `2^k ≳ x^{1/3}` — both give `logN ≥ (10/31)·L`). -/
theorem boxPriceKerr_worst_le {x k i F K : ℕ} {Kc : ℝ}
    (hKc : 1 ≤ Kc) (hx2 : 2 ≤ x) (hlogx10 : 10 ≤ Real.log x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F K)
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
        ≤ Real.log ((2 ^ k : ℕ) : ℝ)) :
    boxPriceKerr Kc k i ≤ CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12 := by
  classical
  -- box scaffold (ChenFinal): the real / log windows for `X·M`.
  obtain ⟨hlo, hhi⟩ := boundary_XM_raw hi
  obtain ⟨hXMpos, -, hXM4x⟩ := xm_real_bounds hlo hhi
  obtain ⟨hlog_lo, -⟩ := xm_log_bounds hx2 hlo hhi
  -- abbreviations matching the `boxPriceKerr` def
  unfold boxPriceKerr
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) with hXMdef
  set L : ℝ := Real.log XM with hLdef
  set logN : ℝ := Real.log ((2 ^ k : ℕ) : ℝ) with hlogNdef
  -- positivity facts
  have hlogx_pos : (0 : ℝ) < Real.log x := by linarith
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := hlogx_pos.le
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXM0 : (0 : ℝ) ≤ XM := le_of_lt hXMpos
  have hLlogx : (9 / 10 : ℝ) * Real.log x ≤ L := by rw [hLdef]; linarith
  -- the common bound `S := (31/10)^{50}·L`, and each Kerr term `≤ Kc·S`.
  set S : ℝ := Kc * (((31 : ℝ) / 10) ^ (50 : ℝ) * L) with hSdef
  have hKc0 : (0 : ℝ) ≤ Kc := by linarith
  have hterm : ∀ a e : ℝ, a ≤ 1 + e → 0 ≤ e → e ≤ 50 →
      Kc * (L ^ a / logN ^ e) ≤ S := by
    intro a e hae he0 he50
    rw [hSdef]
    exact mul_le_mul_of_nonneg_left (kerr_ratio_term_le hL1 hratio hae he0 he50) hKc0
  have hkb : Kbeta_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta_min, mul_div_assoc]
    exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkm : Km_min Kc L logN 13 18 ≤ S := by
    rw [Km_min, mul_div_assoc]
    exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  have hkb' : Kbeta'_min Kc L logN 13 18 ≤ S := by
    rw [Kbeta'_min, mul_div_assoc]
    exact hterm _ _ (by norm_num) (by norm_num) (by norm_num)
  -- `S ≥ 1` (folds the additive constants) and `√26 ≤ 6`.
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
    rw [show (13 : ℝ) + 5 = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  -- the bracket bound `BR ≤ 281352·S`.
  have hbracket : Kbeta_min Kc L logN 13 18
        + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1))
      ≤ 281352 * S := by
    rw [h218]
    nlinarith [hkb, hkm, hkb', h26, hSge1]
  -- fold the bracket into `BR`, then lift the bound through `·XM/L^{13}` and the factor `2`.
  set BR : ℝ := Kbeta_min Kc L logN 13 18
      + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
        + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1)) with hBRdef
  -- goal is now `2·(BR·XM/L^{13}) ≤ CconBox·Kc·x/(log x)^{12}`; `hbracket : BR ≤ 281352·S`.
  have hL13pos : (0 : ℝ) < L ^ (13 : ℝ) := Real.rpow_pos_of_pos hLpos 13
  have hL12pos : (0 : ℝ) < L ^ (12 : ℝ) := Real.rpow_pos_of_pos hLpos 12
  have hL13 : L ^ (13 : ℝ) = L ^ (12 : ℝ) * L := by
    rw [show (13 : ℝ) = 12 + 1 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  -- step 1: `2·(BR·XM/L^{13}) ≤ (2·(281352·S))·XM/L^{13}`
  have hstep1 : 2 * (BR * XM / L ^ (13 : ℝ)) ≤ (2 * (281352 * S)) * XM / L ^ (13 : ℝ) := by
    rw [show 2 * (BR * XM / L ^ (13 : ℝ)) = ((2 * BR) * XM) / L ^ (13 : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hL13pos).mpr
      (mul_le_mul_of_nonneg_right (by linarith [hbracket]) hXM0)
  -- step 2: `(2·(281352·S))·XM/L^{13} ≤ CconBox·Kc·x/(log x)^{12}` (the numeric close)
  have hL12ge : ((9 : ℝ) / 10) ^ (12 : ℝ) * (Real.log x) ^ (12 : ℝ) ≤ L ^ (12 : ℝ) := by
    have h2 : ((9 / 10 : ℝ) * Real.log x) ^ (12 : ℝ) ≤ L ^ (12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hLlogx (by norm_num)
    rwa [Real.mul_rpow (by norm_num) hlogx_nn] at h2
  have hdenpos : (0 : ℝ) < ((9 : ℝ) / 10) ^ (12 : ℝ) * (Real.log x) ^ (12 : ℝ) := by positivity
  have hconv : (Real.log x) ^ (12 : ℝ) = (Real.log x) ^ 12 := by
    rw [show ((12 : ℝ)) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlog12ne : (Real.log x) ^ 12 ≠ 0 := pow_ne_zero 12 hlogne
  have h910ne : ((9 : ℝ) / 10) ^ (12 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) 12)
  have hstep2 : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
      ≤ CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12 := by
    -- rewrite the LHS to `562704·(31/10)^{50}·Kc·XM/L^{12}` (unfold `S`, cancel one `L`).
    have hLHSeq : (2 * (281352 * S)) * XM / L ^ (13 : ℝ)
        = 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ) := by
      rw [hSdef, hL13]; field_simp; ring
    have hc0 : (0 : ℝ) ≤ 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc := by positivity
    have hc1 : (0 : ℝ) ≤ 2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (x : ℝ) := by positivity
    rw [hLHSeq]
    calc 562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * XM / L ^ (12 : ℝ)
        = (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc) * (XM / L ^ (12 : ℝ)) := by ring
      _ ≤ (562704 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc) * (4 * (x : ℝ) / L ^ (12 : ℝ)) :=
          mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hL12pos).mpr hXM4x) hc0
      _ = (2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (x : ℝ)) / L ^ (12 : ℝ) := by ring
      _ ≤ (2250816 * ((31 : ℝ) / 10) ^ (50 : ℝ) * Kc * (x : ℝ))
            / (((9 : ℝ) / 10) ^ (12 : ℝ) * (Real.log x) ^ (12 : ℝ)) :=
          div_le_div_of_nonneg_left hc1 hdenpos hL12ge
      _ = CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12 := by
          rw [CconBox, hconv]; field_simp
  exact le_trans hstep1 hstep2

/-! ## 3. The piece-count bound (deliverable 4)

`Nat.log 2 x + 1 ≤ 2·log x`: from `2^{Nat.log 2 x} ≤ x` (so `Nat.log 2 x·log 2 ≤ log x`) and
`log 2 > 0.6931`, `Nat.log 2 x ≤ log x/log 2 < 1.443·log x`, and `+1 ≤ 2·log x` for `log x ≥ 2`. -/

/-- **`nat_log2_count_le` (deliverable 4).**  `(Nat.log 2 x : ℝ) + 1 ≤ 2·log x` for `x ≥ 2`,
`log x ≥ 2`.  The `(Nat.log 2 x + 1)`-piece count times a per-piece `x/(log x)^{12}` closes to
`x/(log x)^{11}`. -/
theorem nat_log2_count_le {x : ℕ} (hx2 : 2 ≤ x) (hlogx : 2 ≤ Real.log x) :
    (Nat.log 2 x : ℝ) + 1 ≤ 2 * Real.log x := by
  have hx0 : x ≠ 0 := by omega
  have hpow : (2 : ℕ) ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx0
  have hpowR : (2 : ℝ) ^ Nat.log 2 x ≤ (x : ℝ) := by exact_mod_cast hpow
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 x := by positivity
  have hlogle : Real.log ((2 : ℝ) ^ Nat.log 2 x) ≤ Real.log x := Real.log_le_log h2pos hpowR
  rw [Real.log_pow] at hlogle
  -- `hlogle : ↑(Nat.log 2 x) · log 2 ≤ log x`, and `log 2 > 0.6931`
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hnn : (0 : ℝ) ≤ (Nat.log 2 x : ℝ) := Nat.cast_nonneg _
  nlinarith [hlogle, mul_nonneg hnn (by linarith [hl2] : (0 : ℝ) ≤ Real.log 2 - 0.6931471803),
    hlogx]

/-! ## 4. The aggregation (deliverable 3, the summit)

The single-block aggregate of the per-`(j,k,i)` box prices (plus the sym/low legs and the
`(1/2)·Pdiag` diagonal) closes to `(9·Ccon_box + Ccon_diag/2)·Kc·x/(log x)^{11}`.  Structure:
`ε₀ := x` collapses `maxBlock` to `0` (single block `j = 0`, `Finset.sum_range_one`); each piece
carries `≤ 3` boundary boxes (`dyadicBoundary_card_le_three`) each `≤ W`; `(Nat.log 2 x + 1)`
pieces; the band coefficients sum `3 + 1/2 + 1 = 9/2`; `(Nat.log 2 x + 1) ≤ 2·log x` (§3) and
`W ≤ Ccon_box·Kc·x/(log x)^{12}` trade one power of `log x` for the piece count. -/

/-- **`hSum_at_op` (deliverable 3).**  The exact `hSum` slot of `hBVblocksW_discharge'`
(`PDiag.lean:729–735`) at the single-block operating point (`hmax : maxBlock x z ε₀ = 0`), with a
uniform per-price worst `W` (`hbox`/`hsym`/`hlow`) and the abstract diagonal `Pdiag` bounded by
its own budget row `hPdiag`.  `RHD := (9·Ccon_box + Ccon_diag/2)·Kc·x/(log x)^{11}`. -/
theorem hSum_at_op (x z y K : ℕ) (ε₀ : ℝ) (Kc : ℝ)
    (Price : ℕ → ℕ → ℕ → ℝ) (PsymK PlowK : ℕ → ℕ → ℝ) (Pdiag W Ccon_box Ccon_diag : ℝ)
    (hmax : maxBlock x z ε₀ = 0)
    (_hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log x) (hW0 : 0 ≤ W)
    (hbox : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i ≤ W)
    (hsym : ∀ k ∈ Finset.range (Nat.log 2 x + 1), PsymK 0 k ≤ W)
    (hlow : ∀ k ∈ Finset.range (Nat.log 2 x + 1), PlowK 0 k ≤ W)
    (hWbound : W ≤ Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 12)
    (hPdiag : Pdiag ≤ Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11)
    (hcount : (Nat.log 2 x : ℝ) + 1 ≤ 2 * Real.log x) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * Pdiag)))
      ≤ (9 * Ccon_box + Ccon_diag / 2) * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
  classical
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
  -- the ≤ 3-boxes-per-piece count facts for `dyadicBoundary_card_le_three`.
  have hMcard : ∀ k, pieceM k ≤ 2 * (pieceN k + 1) := by
    intro k
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  have hTcard : x ≤ 2 * (x / 2 + 1) := by omega
  -- the three per-block sums, each `≤ (Nat.log 2 x + 1)·W`.
  have hbox0 : (∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i)
      ≤ 3 * (((Nat.log 2 x : ℝ) + 1) * W) := by
    have hper : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i)
          ≤ 3 * W := by
      intro k hk
      have hcard : (dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card ≤ 3 :=
        dyadicBoundary_card_le_three (hMcard k) hTcard
      calc (∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i)
          ≤ (dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card • W :=
            Finset.sum_le_card_nsmul _ _ _ (hbox k hk)
        _ = ((dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card : ℝ) * W :=
            nsmul_eq_mul _ _
        _ ≤ 3 * W := by
            apply mul_le_mul_of_nonneg_right _ hW0
            exact_mod_cast hcard
    calc (∑ k ∈ Finset.range (Nat.log 2 x + 1),
          ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i)
        ≤ ∑ _k ∈ Finset.range (Nat.log 2 x + 1), 3 * W := Finset.sum_le_sum hper
      _ = ((Nat.log 2 x + 1 : ℕ) : ℝ) * (3 * W) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 3 * (((Nat.log 2 x : ℝ) + 1) * W) := by push_cast; ring
  have hsym0 : (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK 0 k)
      ≤ ((Nat.log 2 x : ℝ) + 1) * W := by
    calc (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK 0 k)
        ≤ ∑ _k ∈ Finset.range (Nat.log 2 x + 1), W := Finset.sum_le_sum hsym
      _ = ((Nat.log 2 x + 1 : ℕ) : ℝ) * W := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((Nat.log 2 x : ℝ) + 1) * W := by push_cast; ring
  have hlow0 : (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK 0 k)
      ≤ ((Nat.log 2 x : ℝ) + 1) * W := by
    calc (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK 0 k)
        ≤ ∑ _k ∈ Finset.range (Nat.log 2 x + 1), W := Finset.sum_le_sum hlow
      _ = ((Nat.log 2 x + 1 : ℕ) : ℝ) * W := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((Nat.log 2 x : ℝ) + 1) * W := by push_cast; ring
  -- the numeric close of the counted aggregate.
  have hnRW : ((Nat.log 2 x : ℝ) + 1) * W
      ≤ 2 * Real.log x * (Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 12) := by
    calc ((Nat.log 2 x : ℝ) + 1) * W ≤ (2 * Real.log x) * W :=
          mul_le_mul_of_nonneg_right hcount hW0
      _ ≤ (2 * Real.log x) * (Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 12) :=
          mul_le_mul_of_nonneg_left hWbound (by positivity)
      _ = 2 * Real.log x * (Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 12) := by ring
  have hA : (9 / 2) * (((Nat.log 2 x : ℝ) + 1) * W)
      ≤ 9 * Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
    have hstepA : (9 / 2) * (((Nat.log 2 x : ℝ) + 1) * W)
        ≤ (9 / 2) * (2 * Real.log x * (Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 12)) :=
      mul_le_mul_of_nonneg_left hnRW (by norm_num)
    refine le_trans hstepA (le_of_eq ?_)
    field_simp
  have hB : (1 / 2) * Pdiag ≤ (1 / 2) * Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
    have h := mul_le_mul_of_nonneg_left hPdiag (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc (1 / 2) * Pdiag ≤ (1 / 2) * (Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11) := h
      _ = (1 / 2) * Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11 := by ring
  have hnum : (9 / 2) * (((Nat.log 2 x : ℝ) + 1) * W) + (1 / 2) * Pdiag
      ≤ (9 * Ccon_box + Ccon_diag / 2) * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
    calc (9 / 2) * (((Nat.log 2 x : ℝ) + 1) * W) + (1 / 2) * Pdiag
        ≤ 9 * Ccon_box * Kc * (x : ℝ) / (Real.log x) ^ 11
          + (1 / 2) * Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11 := by linarith [hA, hB]
      _ = (9 * Ccon_box + Ccon_diag / 2) * Kc * (x : ℝ) / (Real.log x) ^ 11 := by ring
  -- collapse the block sum (single block) and finish.
  rw [hmax, Finset.sum_range_one]
  refine le_trans ?_ hnum
  linarith [hbox0, hsym0, hlow0]

/-! ## 5. The slot match (deliverable 5, the anti-vacuity composition)

`hSum_at_op` closes the VERBATIM `hSum` hypothesis of `hBVblocksW_discharge'` (`PDiag.lean:729`)
at `RHD := (9·CconBox + Ccon_diag/2)·Kc·x/(log x)^{11}` — character-for-character the slot
`fin8c` feeds.  The uniform `W`, the diagonal budget `Ccon_diag`, and the per-price bounds enter
as the caller's rows (the dichotomy `hbox`/`hsym`/`hlow`, discharged by
`box_price_at_op`/SYMLOW + `boxPriceKerr_worst_le`; `Ccon_box := CconBox`). -/
example (x z y K : ℕ) (Kc : ℝ)
    (Price : ℕ → ℕ → ℕ → ℝ) (PsymK PlowK : ℕ → ℕ → ℝ) (Pdiag W Ccon_diag : ℝ)
    (hz : 1 ≤ z) (hx1 : 1 ≤ x)
    (hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log x) (hW0 : 0 ≤ W)
    (hbox : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i ≤ W)
    (hsym : ∀ k ∈ Finset.range (Nat.log 2 x + 1), PsymK 0 k ≤ W)
    (hlow : ∀ k ∈ Finset.range (Nat.log 2 x + 1), PlowK 0 k ≤ W)
    (hWbound : W ≤ CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12)
    (hPdiag : Pdiag ≤ Ccon_diag * Kc * (x : ℝ) / (Real.log x) ^ 11)
    (hcount : (Nat.log 2 x : ℝ) + 1 ≤ 2 * Real.log x) :
    -- the EXACT `hSum` shape of `hBVblocksW_discharge'` at `ε₀ := (x : ℝ)`
    (∑ j ∈ Finset.range (maxBlock x z (x : ℝ) + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * Pdiag)))
      ≤ (9 * CconBox + Ccon_diag / 2) * Kc * (x : ℝ) / (Real.log x) ^ 11 :=
  hSum_at_op x z y K (x : ℝ) Kc Price PsymK PlowK Pdiag W CconBox Ccon_diag
    (maxBlock_eq_zero_of_eps_self hz hx1) hKc0 hlogpos hW0 hbox hsym hlow hWbound hPdiag hcount

end Salt.Chen
