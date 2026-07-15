/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AggSum
import Salt.Chen.AssembleA3b
import Salt.Chen.AggCE
import Salt.Chen.AggDiag
import Salt.Chen.PriceClose

/-!
# Node PACK-A — the four A₃-side packaging rows (new file, no edits to landed files)

Design: `docs/blueprints/flags.md`, the `2026-07-15 fin8c` entry (THE SPEC: the exact gap list
(a)–(c) + CE→RCE), building on HSUM (`AggSum.lean`), SYMLOW (`AssembleA3b.lean`),
HCE (`AggCE.lean`), HDIAG (`AggDiag.lean`).

This file lands the four still-UNPACKAGED analytic rows fin8c needs to feed `hSum_at_op`'s
uniform-`W` slot and `hNum_close_of_tower`'s `hRCE` slot:

1. **`boxPriceKerrY_worst_le`** — the middle-`k` mirror of `AggSum.boxPriceKerr_worst_le`
   (`logN := log y`); a priced middle box `≤ CconBox·Kc·x/(log x)^{12}` under the middle-`k`
   ratio `(10/31)·L ≤ log y`.  Same engine (`kerr_ratio_term_le`), window form (takes the raw
   `X·M`-window `hlo`/`hhi`) so it applies over the sym boundary `max y (pieceN k)` too.
2. **`ratio_le_of_floor`** (+ specializations) — THE `hratio` producer:
   `(10/31)·log((2^{i+1}−1)·pieceM k) ≤ log N` from a floor `x^c/8 ≤ N` and the scaffold window
   `log(X·M) ≤ log x + 3` (via `xm_log_bounds`).  `c = 1/3` needs `log x ≥ 400`; `c = 7/16` has
   more room (`log x ≥ 60`).  Margins in the proofs.
3. **`symPriceK_worst_le` / `lowPriceK_worst_le`** — the sym/low uniform-`W` collapse: each
   per-piece price is a `≤ 3`-box boundary sum (`dyadicBoundary_card_le_three`), bounded box-by-box
   by `boxPriceKerrY_worst_le` (middle, at `log y`) / `boxPriceKerr_worst_le` (band/collapse, at
   `log 2^k`).  `sym` is UNIFORM in `k` (its boxes are always priced at `log y ≥ log(x^{1/3}/8)`
   or `log 2^k` with `2^k > y ≥ x^{1/3}/8`); `low` takes the band `k`-floor `x^{1/3}/8 ≤ 2^k` as a
   hypothesis (the LIVE-regime input — the caller uses the vanish `= 0` route otherwise).
4. **`hRCE_at_op`** — CE→RCE: collapses `hCE_at_op`'s symbolic product
   `ν(Q)·(Σ_{d∣Ps} ν d)·tripleSum/(z−1)` to `Ccon·Kc·x/(log x)^{11}` via `ν(Q) ≤ 1`,
   `Σν ≤ log x`, `tripleSum ≤ x·(log x)^C`, `z − 1 ≥ x^{1/8}/2`, and the polylog/power trade
   `2·(log x)^{C+12} ≤ x^{1/8}` (`a12_logpow_le_rpow`).  Honest scale `x^{7/8}·polylog`.

House rules: sorry-free, no `native_decide`, per-declaration axiom audits (scratchpad), zero new
warnings.  Only `[propext, Classical.choice, Quot.sound]`.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §0 — the generic raw `X·M`-window (mirror of `boundary_XM_raw` for a general lower edge `N`)

`boundary_XM_raw` (`ChenFinal`) uses the pieceN edge `N = pieceN k` (so `N+1 = 2^k`).  The sym
boundary uses `N = max y (pieceN k)`.  The corner clause `2^i·(N+1) ≤ x` still caps
`X·M = (2^{i+1}−1)·pieceM k ≤ 4·2^i·2^k ≤ 4x` as long as `2^k ≤ N+1`, which holds for any
`N ≥ pieceN k` (`pieceN k + 1 = 2^k`). -/

/-- **`boundary_XM_window_gen`.**  The raw `X·M`-window `x/2+1 < X·M ≤ 4x` for a box in a general
lower-edge boundary `dyadicBoundary N (pieceM k) (x/2+1) x F K`, whenever `2^k ≤ N + 1`. -/
theorem boundary_XM_window_gen {x k i N F K : ℕ}
    (hi : i ∈ dyadicBoundary N (pieceM k) (x / 2 + 1) x F K)
    (h2kN : 2 ^ k ≤ N + 1) :
    x / 2 + 1 < (2 ^ (i + 1) - 1) * pieceM k ∧ (2 ^ (i + 1) - 1) * pieceM k ≤ 4 * x := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcut⟩ := hi
  refine ⟨hcut, ?_⟩
  have hMle : pieceM k ≤ 2 ^ (k + 1) := Nat.sub_le _ _
  calc (2 ^ (i + 1) - 1) * pieceM k
      ≤ 2 ^ (i + 1) * 2 ^ (k + 1) := Nat.mul_le_mul (Nat.sub_le _ _) hMle
    _ = 4 * (2 ^ i * 2 ^ k) := by rw [pow_succ 2 i, pow_succ 2 k]; ring
    _ ≤ 4 * (2 ^ i * (N + 1)) := Nat.mul_le_mul (le_refl 4) (Nat.mul_le_mul (le_refl _) h2kN)
    _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner

/-! ## §1 — the `hratio` producer (deliverable 3)

From a floor `x^c/8 ≤ N` and the box's log window `L ≤ log x + 3`, the worst-c ratio
`(10/31)·L ≤ log N` holds once `log x` clears a `c`-dependent threshold (the `hmargin` row,
discharged numerically at the operating scale where `log x` is astronomical). -/

/-- **`ratio_le_of_floor` (deliverable 3, core).**  `(10/31)·L ≤ log N` from `x^c/8 ≤ N`, the
window `L ≤ log x + 3`, and the `c`-margin `(10/31)(log x + 3) ≤ c·log x − 3` (with `log 8 ≤ 3`
baked in).  `L` is the box log `log((2^{i+1}−1)·pieceM k)`; `N` is `2^k` (band/collapse) or `y`
(middle). -/
theorem ratio_le_of_floor {x : ℕ} {L N c : ℝ}
    (hx2 : 2 ≤ x) (hLup : L ≤ Real.log x + 3)
    (hNfloor : (x : ℝ) ^ c / 8 ≤ N)
    (hmargin : (10 / 31 : ℝ) * (Real.log x + 3) ≤ c * Real.log x - 3) :
    (10 / 31 : ℝ) * L ≤ Real.log N := by
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hfloorpos : (0 : ℝ) < (x : ℝ) ^ c / 8 := by positivity
  have hlogfloor : Real.log ((x : ℝ) ^ c / 8) ≤ Real.log N := Real.log_le_log hfloorpos hNfloor
  have heq : Real.log ((x : ℝ) ^ c / 8) = c * Real.log x - Real.log 8 := by
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos c)) (by norm_num),
      Real.log_rpow hxpos]
  have hlog8 : Real.log 8 ≤ 3 := by
    have h2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [h8]; linarith
  have hlogN_lb : c * Real.log x - Real.log 8 ≤ Real.log N := by rw [← heq]; exact hlogfloor
  have hstep : (10 / 31 : ℝ) * L ≤ (10 / 31 : ℝ) * (Real.log x + 3) :=
    mul_le_mul_of_nonneg_left hLup (by norm_num)
  linarith [hlogN_lb, hlog8, hstep, hmargin]

/-- The `c = 1/3` margin `(10/31)(log x + 3) ≤ (1/3)·log x − 3`, for `log x ≥ 400`
(`(1/3 − 10/31)·log x = log x/93 ≥ 400/93 ≈ 4.30 > 30/31 + 3 ≈ 3.97`). -/
theorem margin_cbrt {x : ℕ} (hlogx : (400 : ℝ) ≤ Real.log x) :
    (10 / 31 : ℝ) * (Real.log x + 3) ≤ (1 / 3 : ℝ) * Real.log x - 3 := by
  linarith [hlogx]

/-- The `c = 7/16` margin `(10/31)(log x + 3) ≤ (7/16)·log x − 3`, for `log x ≥ 60`
(`(7/16 − 10/31)·log x = 57·log x/496 ≥ 57·60/496 ≈ 6.9 > 30/31 + 3 ≈ 3.97`). -/
theorem margin_box {x : ℕ} (hlogx : (60 : ℝ) ≤ Real.log x) :
    (10 / 31 : ℝ) * (Real.log x + 3) ≤ (7 / 16 : ℝ) * Real.log x - 3 := by
  linarith [hlogx]

/-! ## §2 — the middle-`k` worst price (deliverable 1)

`boxPriceKerrY` (`AssembleA3b`) is `boxPriceKerr` with `Real.log ((2^k:ℕ):ℝ)` replaced by
`Real.log (y:ℝ)`.  So the worst-price bound is the character-for-character mirror of
`AggSum.boxPriceKerr_worst_le`, stated in window form (taking the raw `X·M`-window directly, so it
applies over the sym `max y (pieceN k)` boundary as well as the plain pieceN boundary). -/

/-- **`boxPriceKerrY_worst_le` (deliverable 1).**  For a box with `X·M`-window `x/2+1 < X·M ≤ 4x`
at the middle-`k` ratio `(10/31)·L ≤ log y`, with `Kc ≥ 1`, `x ≥ 2`, `log x ≥ 10`:
`boxPriceKerrY Kc y k i ≤ CconBox·Kc·x/(log x)^{12}`.  The middle-`k` ratio holds since
`log y ≥ log(x^{1/3}/8) > (10/31)·(log x + 3)` (via `ratio_le_of_floor` at `c = 1/3`). -/
theorem boxPriceKerrY_worst_le {x k i y : ℕ} {Kc : ℝ}
    (hKc : 1 ≤ Kc) (hx2 : 2 ≤ x) (hlogx10 : 10 ≤ Real.log x)
    (hlo : x / 2 + 1 < (2 ^ (i + 1) - 1) * pieceM k)
    (hhi : (2 ^ (i + 1) - 1) * pieceM k ≤ 4 * x)
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
        ≤ Real.log (y : ℝ)) :
    boxPriceKerrY Kc y k i ≤ CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12 := by
  classical
  obtain ⟨hXMpos, -, hXM4x⟩ := xm_real_bounds hlo hhi
  obtain ⟨hlog_lo, -⟩ := xm_log_bounds hx2 hlo hhi
  unfold boxPriceKerrY
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) with hXMdef
  set L : ℝ := Real.log XM with hLdef
  set logN : ℝ := Real.log (y : ℝ) with hlogNdef
  have hlogx_pos : (0 : ℝ) < Real.log x := by linarith
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := hlogx_pos.le
  have hlogne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXM0 : (0 : ℝ) ≤ XM := le_of_lt hXMpos
  have hLlogx : (9 / 10 : ℝ) * Real.log x ≤ L := by rw [hLdef]; linarith
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
  have hbracket : Kbeta_min Kc L logN 13 18
        + (6 * (Km_min Kc L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L logN 13 18 + 15360 + 1))
      ≤ 281352 * S := by
    rw [h218]
    nlinarith [hkb, hkm, hkb', h26, hSge1]
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

/-! ## §3 — the sym/low uniform-`W` collapse (deliverable 2)

`symPriceK`/`lowPriceK` (`AssembleA3b`) are `≤ 3`-box boundary sums of closed Kerr prices.  Each
box is priced by `boxPriceKerrY_worst_le` (middle, at `log y`) or `boxPriceKerr_worst_le`
(band/collapse, at `log 2^k`); the box count is `≤ 3` (`dyadicBoundary_card_le_three`).

* `sym` is UNIFORM in `k`: when `pieceN k < y` every box uses `boxPriceKerrY` at `log y ≥
  log(x^{1/3}/8)`; when `y ≤ pieceN k` (collapse) `max y (pieceN k) = pieceN k`, every box uses
  `boxPriceKerr` at `log 2^k` with `2^k > y ≥ x^{1/3}/8`.  Either way the `c = 1/3` floor holds.
* `low` takes the band `k`-floor `x^{1/3}/8 ≤ 2^k` (the LIVE-regime input `band_kfloor_of_live`
  supplies); in the vanish regime the discrepancy `= 0`, handled by the caller (fin8c). -/

/-- **`symPriceK_worst_le` (deliverable 2, sym).**  UNIFORM in `k`: the closed sym per-piece price
`≤ 3·CconBox·(Kb+Km)·x/(log x)^{12}`, from the `opY`-floor `x^{1/3}/8 ≤ y` alone (both the middle
`log y` and the collapse `log 2^k` clear the `c = 1/3` ratio). -/
theorem symPriceK_worst_le {x k K : ℕ} {Kb Km : ℝ} (z y : ℕ)
    (hKb : 1 ≤ Kb) (hKm : 1 ≤ Km) (hx2 : 2 ≤ x) (hlogx : (400 : ℝ) ≤ Real.log x)
    (hyfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ)) :
    symPriceK Kb Km z x y K k ≤ 3 * CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 := by
  classical
  have hlogx10 : (10 : ℝ) ≤ Real.log x := by linarith
  have hKb0 : (0 : ℝ) ≤ Kb := by linarith
  have hKm0 : (0 : ℝ) ≤ Km := by linarith
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  have hL12pos : (0 : ℝ) < (Real.log x) ^ 12 := by positivity
  have hpe : pieceN k + 1 = 2 ^ k := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  have hW0 : (0 : ℝ) ≤ CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 :=
    div_nonneg (mul_nonneg (mul_nonneg CconBox_nonneg (by linarith)) hxnn) hL12pos.le
  -- the per-box bound (uniform over the sym boundary)
  have hper : ∀ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
        (z * max y (pieceN k)) K,
      (if pieceN k < y then boxPriceKerrY Km y k i else boxPriceKerr Kb k i)
        ≤ CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 := by
    intro i hi
    have h2kN : 2 ^ k ≤ max y (pieceN k) + 1 := by
      have hpn : pieceN k ≤ max y (pieceN k) := le_max_right _ _
      omega
    obtain ⟨hlo, hhi⟩ := boundary_XM_window_gen hi h2kN
    obtain ⟨-, hLup⟩ := xm_log_bounds hx2 hlo hhi
    split_ifs with hlt
    · -- middle: boxPriceKerrY at `log y`
      have hratio := ratio_le_of_floor (x := x) (N := (y : ℝ)) (c := (1 : ℝ) / 3)
        hx2 hLup hyfloor (margin_cbrt hlogx)
      calc boxPriceKerrY Km y k i
          ≤ CconBox * Km * (x : ℝ) / (Real.log x) ^ 12 :=
            boxPriceKerrY_worst_le hKm hx2 hlogx10 hlo hhi hratio
        _ ≤ CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 :=
            (div_le_div_iff_of_pos_right hL12pos).mpr
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by linarith) CconBox_nonneg) hxnn)
    · -- collapse: `max = pieceN k`, boxPriceKerr at `log 2^k` (`2^k > y ≥ x^{1/3}/8`)
      rw [not_lt] at hlt
      rw [max_eq_right hlt] at hi
      have hpnk : pieceN k ≤ 2 ^ k := by unfold pieceN; exact Nat.sub_le _ _
      have hy2k : y ≤ 2 ^ k := le_trans hlt hpnk
      have hylt : (y : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hy2k
      have h2kfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := by linarith [hyfloor]
      have hratio := ratio_le_of_floor (x := x) (N := ((2 ^ k : ℕ) : ℝ)) (c := (1 : ℝ) / 3)
        hx2 hLup h2kfloor (margin_cbrt hlogx)
      calc boxPriceKerr Kb k i
          ≤ CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 :=
            boxPriceKerr_worst_le hKb hx2 hlogx10 hi hratio
        _ ≤ CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 :=
            (div_le_div_iff_of_pos_right hL12pos).mpr
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by linarith) CconBox_nonneg) hxnn)
  -- `≤ 3` boxes per piece
  have hMcard : pieceM k ≤ 2 * (max y (pieceN k) + 1) := by
    have hpn : pieceN k ≤ max y (pieceN k) := le_max_right _ _
    have hM : pieceM k = 2 ^ (k + 1) - 1 := rfl
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    omega
  have hTcard : x ≤ 2 * (x / 2 + 1) := by omega
  have hcard : (dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
      (z * max y (pieceN k)) K).card ≤ 3 := dyadicBoundary_card_le_three hMcard hTcard
  unfold symPriceK
  calc ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x (z * max y (pieceN k)) K,
        (if pieceN k < y then boxPriceKerrY Km y k i else boxPriceKerr Kb k i)
      ≤ (dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x (z * max y (pieceN k)) K).card
          • (CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12) :=
        Finset.sum_le_card_nsmul _ _ _ hper
    _ = ((dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
            (z * max y (pieceN k)) K).card : ℝ)
          * (CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12) :=
        nsmul_eq_mul _ _
    _ ≤ 3 * (CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hW0
    _ = 3 * CconBox * (Kb + Km) * (x : ℝ) / (Real.log x) ^ 12 := by ring

/-- **`lowPriceK_worst_le` (deliverable 2, low).**  In the LIVE regime (band `k`-floor
`x^{1/3}/8 ≤ 2^k`, from `band_kfloor_of_live`): the closed low per-piece price
`≤ 3·CconBox·Kb·x/(log x)^{12}`.  Each of the `≤ 3` boundary boxes is priced by
`boxPriceKerr_worst_le` at `log 2^k`.  (Vanish → the discrepancy is `0`; the caller routes it.) -/
theorem lowPriceK_worst_le {x k K : ℕ} {Kb : ℝ} (z y : ℕ)
    (hKb : 1 ≤ Kb) (hx2 : 2 ≤ x) (hlogx : (400 : ℝ) ≤ Real.log x)
    (hkfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ)) :
    lowPriceK Kb z x y K k ≤ 3 * CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 := by
  classical
  have hlogx10 : (10 : ℝ) ≤ Real.log x := by linarith
  have hKb0 : (0 : ℝ) ≤ Kb := by linarith
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  have hL12pos : (0 : ℝ) < (Real.log x) ^ 12 := by positivity
  have hW0 : (0 : ℝ) ≤ CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 :=
    div_nonneg (mul_nonneg (mul_nonneg CconBox_nonneg hKb0) hxnn) hL12pos.le
  have hper : ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
      boxPriceKerr Kb k i ≤ CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := boundary_XM_raw hi
    obtain ⟨-, hLup⟩ := xm_log_bounds hx2 hlo hhi
    have hratio := ratio_le_of_floor (x := x) (N := ((2 ^ k : ℕ) : ℝ)) (c := (1 : ℝ) / 3)
      hx2 hLup hkfloor (margin_cbrt hlogx)
    exact boxPriceKerr_worst_le hKb hx2 hlogx10 hi hratio
  have hMcard : pieceM k ≤ 2 * (pieceN k + 1) := by
    have hpe : pieceN k + 1 = 2 ^ k := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      unfold pieceN; omega
    have hM : pieceM k = 2 ^ (k + 1) - 1 := rfl
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    omega
  have hTcard : x ≤ 2 * (x / 2 + 1) := by omega
  have hcard : (dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card ≤ 3 :=
    dyadicBoundary_card_le_three hMcard hTcard
  unfold lowPriceK
  calc ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, boxPriceKerr Kb k i
      ≤ (dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card
          • (CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12) :=
        Finset.sum_le_card_nsmul _ _ _ hper
    _ = ((dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K).card : ℝ)
          * (CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12) := nsmul_eq_mul _ _
    _ ≤ 3 * (CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hW0
    _ = 3 * CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 := by ring

/-! ## §4 — CE→RCE: the finding-5 product collapses to `Ccon·Kc·x/(log x)^{11}` (deliverable 4)

`hCE_at_op` (`AggCE`) bounds the `hCE` double sum by the symbolic product
`ν(Q)·(Σ_{d∣Ps} ν d)·tripleSum x z y/(z−1)`.  The numeric collapse: `ν(Q) ≤ 1` (`nuChen_le_one`),
`Σν ≤ log x` (`nu_sum_le_log_at_op`, a polylog), `tripleSum ≤ x·(log x)^C` (the landed count
keystone `tripleSum_le_cbar_final(_W)`), `z − 1 ≥ x^{1/8}/2` (`opf_*`), and the polylog/power
trade `2·(log x)^{C+12} ≤ x^{1/8}` (`a12_logpow_le_rpow`) give `x^{7/8}·polylog ≤ x/(log x)^{11}`.
The landed inputs enter as hypotheses (fin8c supplies them at the operating point); the collapse
itself is the owed row. -/

/-- **`hRCE_at_op` (deliverable 4).**  The finding-5 product `ν(Q)·(Σ_{d∣Ps} ν d)·tripleSum/(z−1)`
(the RHS of `hCE_at_op`) is `≤ Ccon·Kc·x/(log x)^{11}` — the `hRCE` shape of
`hNum_close_of_tower` (`PriceClose`).  The `x^{1/8}` room absorbs the polylog factors. -/
theorem hRCE_at_op {x z y Q Ps : ℕ} {Kc Ccon : ℝ} {C : ℕ}
    (hx2 : 2 ≤ x) (hlogxpos : 0 < Real.log x)
    (hKcCcon : 1 ≤ Ccon * Kc)
    (hSigma : (∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Real.log x)
    (htriple : tripleSum x z y ≤ (x : ℝ) * (Real.log x) ^ C)
    (hz1pos : 0 < (z : ℝ) - 1)
    (hzlow : (x : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (z : ℝ) - 1)
    (hkey : 2 * (Real.log x) ^ (C + 12) ≤ (x : ℝ) ^ ((1 : ℝ) / 8)) :
    nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y / ((z : ℝ) - 1)
      ≤ Ccon * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
  classical
  have hxRpos : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hnuQ1 : nuChen Q ≤ 1 := nuChen_le_one Q
  have hSigma0 : (0 : ℝ) ≤ ∑ d ∈ Nat.divisors Ps, nuChen d :=
    Finset.sum_nonneg (fun d _ => by rw [nuChen_apply]; positivity)
  have hT0 : (0 : ℝ) ≤ tripleSum x z y := by rw [tripleSum_eq_card]; positivity
  have hlogx0 : (0 : ℝ) ≤ Real.log x := hlogxpos.le
  have hlog11pos : (0 : ℝ) < (Real.log x) ^ 11 := by positivity
  -- Step A: numerator ≤ x·(log x)^{C+1}
  have hnum : nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y
      ≤ (x : ℝ) * (Real.log x) ^ (C + 1) := by
    have hchain := mul_le_mul
      (mul_le_mul hnuQ1 hSigma hSigma0 (by norm_num : (0 : ℝ) ≤ 1))
      htriple hT0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hlogx0)
    calc nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y
        ≤ 1 * Real.log x * ((x : ℝ) * (Real.log x) ^ C) := hchain
      _ = (x : ℝ) * (Real.log x) ^ (C + 1) := by rw [pow_succ]; ring
  -- Step B: divide by (z−1) > 0
  have hB : nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y / ((z : ℝ) - 1)
      ≤ (x : ℝ) * (Real.log x) ^ (C + 1) / ((z : ℝ) - 1) :=
    (div_le_div_iff_of_pos_right hz1pos).mpr hnum
  -- Step C: ≤ x/(log x)^{11}
  have hC : (x : ℝ) * (Real.log x) ^ (C + 1) / ((z : ℝ) - 1) ≤ (x : ℝ) / (Real.log x) ^ 11 := by
    rw [div_le_iff₀ hz1pos, div_mul_eq_mul_div, le_div_iff₀ hlog11pos]
    have hexp : (C + 1) + 11 = C + 12 := by omega
    have hpow : (x : ℝ) * (Real.log x) ^ (C + 1) * (Real.log x) ^ 11
        = (x : ℝ) * (Real.log x) ^ (C + 12) := by rw [mul_assoc, ← pow_add, hexp]
    rw [hpow]
    have hle : (Real.log x) ^ (C + 12) ≤ (z : ℝ) - 1 := by
      have h1 : (Real.log x) ^ (C + 12) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) / 2 := by linarith [hkey]
      linarith [h1, hzlow]
    exact mul_le_mul_of_nonneg_left hle hxpos.le
  -- Step D: ≤ Ccon·Kc·x/(log x)^{11}
  have hD : (x : ℝ) / (Real.log x) ^ 11 ≤ Ccon * Kc * (x : ℝ) / (Real.log x) ^ 11 := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left (div_nonneg hxpos.le hlog11pos.le) hKcCcon
  exact le_trans hB (le_trans hC hD)

/-! ## §5 — the CE slot match (the anti-vacuity composition)

`hCE_at_op ∘ hRCE_at_op` lands the `hCE` double sum of `hBVblocksW_discharge'` directly in the
`Ccon·Kc·x/(log x)^{11}` = `hRCE` shape that `hNum_close_of_tower` consumes — the exact `RCE`
`fin8c` threads. -/

/-- **The CE→RCE slot match.**  The verbatim `hCE` double sum `≤ Ccon·Kc·x/(log x)^{11}`, from
`hCE_at_op` (the finding-5 symbolic bound) chained through `hRCE_at_op` (the numeric collapse). -/
example (x z y Q Ps w' : ℕ) (QR : ℝ) (Dlev : ℕ) {Kc Ccon : ℝ} {C : ℕ}
    (hPs : Squarefree Ps) (hz2 : 2 ≤ z) (hx2 : 2 ≤ x) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQfac : ∀ p ∈ Q.primeFactors, p < w')
    (hPy : ∀ p ∈ Ps.primeFactors, p < y) (hw'z : w' ≤ z)
    (hlogxpos : 0 < Real.log x) (hKcCcon : 1 ≤ Ccon * Kc)
    (hSigma : (∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Real.log x)
    (htriple : tripleSum x z y ≤ (x : ℝ) * (Real.log x) ^ C)
    (hz1pos : 0 < (z : ℝ) - 1) (hzlow : (x : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (z : ℝ) - 1)
    (hkey : 2 * (Real.log x) ^ (C + 12) ≤ (x : ℝ) ^ ((1 : ℝ) / 8)) :
    (∑ j ∈ Finset.range (maxBlock x z (x : ℝ) + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y (x : ℝ) j Q d else 0)
      ≤ Ccon * Kc * (x : ℝ) / (Real.log x) ^ 11 :=
  le_trans (hCE_at_op x z y Q Ps w' QR Dlev hPs hz2 hx2 hQ1 hQPs hQfac hPy hw'z)
    (hRCE_at_op (x := x) (z := z) (y := y) (Q := Q) (Ps := Ps)
      hx2 hlogxpos hKcCcon hSigma htriple hz1pos hzlow hkey)

end Salt.Chen
