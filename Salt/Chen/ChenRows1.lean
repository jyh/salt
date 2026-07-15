/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenFinal2
import Salt.Chen.HeadlineW2
import Salt.Chen.GlueFinal

/-!
# Node fin7a — the BOX-leg row bundle `box_rows_at_op` (a dedicated-volume node)

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin6` entry (the RESTRUCTURE to
`fin7a (box rows, ChenRows1.lean) ∥ fin7b (band rows, ChenRows2.lean) → fin8`), the
`fin5` handoff (the boundary-window scaffold + the m-floor clause `z·y < 2^{i+1}`), the
`fin4` / `EDGE` entries (the `kfloor_of_live_box` 7/16 floor), and the `PRICE-GATE`
ROW-MARGIN table.  New file; no edits to any landed file; not wired into `All.lean`.

## Mandate — discharge every analytic hypothesis of `box_hprice_at_2pow_lo`

`ChenHeadline.box_hprice_at_2pow_lo` prices a LIVE box leg's two-`T` disc sum against
`2·Kerr`, deferring **23 named hypotheses** at the operating point.  This node packages
their per-row dischargers into the composite `box_rows_at_op`, so that fin8 can apply
`box_hprice_at_2pow_lo` with NO analytic side conditions — only the structural/boundary
facts (`hk`, `hi`, `hXsub`) and the H_W-level constants (`N₀`, `Q`, `QR`, `Dlev` via
`hN₀`/`hDbnd`) remaining.

### The spec — `box_hprice_at_2pow_lo`'s hypothesis list (verbatim, in binder order)

At the operating parameters `X = 2^{i+1}−1` (boundary box `i` at `F = z·y`),
`M = pieceM k`, `N = 2^k` (with `x^{7/16}/8 ≤ 2^k`), `D` the conductor
(`x^{11/24}/8 ≤ D ≤ x^{499/1000}`, covering `opQ·(QR·opDlev)`), `Lb = log(4x)`,
`L = log(X·M)`, at `A = 13, B = 15, C0 = 18`:

| # | binder | statement | class | discharger (margin) |
|---|--------|-----------|-------|---------------------|
| 1 | `hk` | `2 ≤ k` | structural | fin8 |
| 2 | `hx` | `exp(10⁹) ≤ x` | tower | composite (base) |
| 3 | `hi` | `i ∈ dyadicBoundary (pieceN k) (pieceM k) (x/2+1) x F Krange` | structural | fin8 |
| 4 | `hXsub` | `X = 2^{i+1}−1` | structural | fin8 |
| 5 | `hNfloor` | `x^{7/16}/8 ≤ 2^k` | landed atom | `kfloor_of_live_box` (2√2 < 8) |
| 6 | `hN₀` | `N₀ ≤ 2^k` | H_W-const | fin8 (from `hNfloor`, any fixed `N₀`) |
| 7 | `hL2` | `2 ≤ log(X·M)` | row | `row_hL2` (log x − 1 ≥ 2) |
| 8 | `hX2` | `2 ≤ X` | row | `row_hX2` (X ≥ F ≥ x^{11/24}/4) |
| 9 | `hD1` | `1 ≤ D` | row | from `hDlo` (x^{11/24}/8 ≥ 1) |
| 10 | `hDge_x` | `x^{11/24}/8 ≤ D` | row | input `hDlo` |
| 11 | `hDbnd` | `Q·(QR·Dlev) ≤ D` | H_W-const | fin8 |
| 12 | `hDscale` | `D ≤ √(X·M)/L^{15}` | row | `row_hDscale` (x^{3/1000}/polylog) |
| 13 | `hDsq` | `D < (2^k+1)²` | landed atom | `hDsq_piece_of_kfloor ∘ hDsmall_at_op` (x^{1/9}) |
| 14 | `habs` | `4(1+log D)·D ≤ 2^k·M/L^{13}` | row | `row_habs` (x^{3/8} vs 2²⁷) |
| 15 | `hXsqrt` | `L^{16} ≤ √X` | row | `row_hXsqrt` (x^{11/48} vs polylog) |
| 16 | `hMsqrt` | `L^{16} ≤ √(pieceM k)` | row | `row_hMsqrt` (x^{7/32} vs polylog) |
| 17 | `herr_lev` | `D·L^{18} ≤ √(X·M)` | row | `row_herr_lev` (x^{1/1000}/polylog) |
| 18 | `herr_Mlev` | `L^{18} ≤ √(pieceM k)` | row | `row_hMsqrt` (same, exponent 18) |
| 19 | `hFX` | `F ≤ X` | row | `row_hFX` (m-floor `F < 2^{i+1}`) |
| 20 | `hDx` | `D ≤ √x` | row | `row_hDx` (499/1000 < 1/2) |
| 21 | `hLbb` | `log(X·M) ≤ Lb` | row | `row_hLbb` (X·M ≤ 4x) |
| 22 | `hfloor` | `(3/log2)⁸·x^{1/6}·Lb^{18} ≤ √F` | row | `GlueFinal.hfloor_row` (x^{1/16}) |
| 23 | `hDXM` | `D ≤ X·M` | row | `row_hDXM` (√x ≤ x/2 < X·M) |

Class-(i) (already supplied by landed atoms): `hNfloor`, `hDsq`.
Class-(ii) (fresh operating-point rows): everything else in the "row" class.
Remaining for fin8: `hk`, `hi`, `hXsub`, `hN₀`, `hDbnd`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §0 — shared numeric helpers -/

/-- `exp e ≤ x^c` whenever `e ≤ c·log x` (`x > 0`).  (Local copy; the GlueFinal one is
`private`.) -/
private theorem row_exp_le_rpow {x c e : ℝ} (hx : 0 < x) (h : e ≤ c * Real.log x) :
    Real.exp e ≤ x ^ c := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.mpr (h.trans_eq (mul_comm c (Real.log x)))

/-- **The tower facts.**  From `exp(10⁹) ≤ x`: `0 < x`, `2 ≤ x`, `1 ≤ log x`, `10⁹ ≤ log x`. -/
private theorem row_tower {x : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ)) :
    (0 : ℝ) < (x : ℝ) ∧ 2 ≤ x ∧ (1 : ℝ) ≤ Real.log x ∧ (10 ^ 9 : ℝ) ≤ Real.log x := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : (10 ^ 9 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hx2 : 2 ≤ x := by
    have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hmono : Real.exp 1 ≤ Real.exp (10 ^ 9) := Real.exp_le_exp.mpr (by norm_num)
    have : (2 : ℝ) < (x : ℝ) := by linarith
    exact_mod_cast this.le
  exact ⟨hxpos, hx2, by linarith, hlogx⟩

/-- **The polylog-power bound.**  For the box log `L` with `1 ≤ L ≤ 2·log x`, `1 ≤ log x`,
and the a12 polylog fact `(log x)^{18} ≤ x^{1/2000}`: `L^E ≤ 262144·x^{1/2000}` for every
`0 ≤ E ≤ 18`.  (`262144 = 2^{18}`.)  This is the single engine behind the polylog rows. -/
private theorem row_Lpow_le {x : ℕ} {L : ℝ} (hlogx1 : 1 ≤ Real.log x)
    (hL0 : 0 ≤ L) (hLle : L ≤ 2 * Real.log x)
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    {E : ℝ} (hE0 : 0 ≤ E) (hE18 : E ≤ 18) :
    L ^ E ≤ (262144 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2000) := by
  have h218 : (2 : ℝ) ^ (18 : ℝ) = 262144 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc L ^ E ≤ (2 * Real.log x) ^ E := Real.rpow_le_rpow hL0 hLle hE0
    _ = (2 : ℝ) ^ E * (Real.log x) ^ E := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ (18 : ℝ) * (Real.log x) ^ (18 : ℝ) := by
        refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE18)
          (Real.rpow_le_rpow_of_exponent_le hlogx1 hE18)
          (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (262144 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2000) := by
        rw [h218]; exact mul_le_mul_of_nonneg_left hpl (by norm_num)

/-- `log x ≤ x^{1/2000}` from the a12 polylog fact (`t ≤ t^{18}` for `t ≥ 1`). -/
private theorem row_logx_le {x : ℕ} (hlogx1 : 1 ≤ Real.log x)
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000)) :
    Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 2000) := by
  refine le_trans ?_ hpl
  calc Real.log x = (Real.log x) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (Real.log x) ^ (18 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlogx1 (by norm_num)

/-! ## §1 — the boundary-window facts (extracted once per row from `hi`)

Every row reads the scaffold (`ChenFinal.boundary_XM_raw`/`xm_sqrt_bounds`/`boundary_log_bounds`)
at `X = 2^{i+1}−1`, `M = pieceM k`, plus the `X ≥ F` corollary of the m-floor clause and the
operating floor `F ≥ x^{11/24}/4` (`GlueFinal.zy_floor_ge`).  `row_box_window` packages them. -/

/-- **`row_box_window`** — the reusable per-box window.  From boundary membership at
`F = z·y` (`z = opZ x`, `y = opY x`) and `X = 2^{i+1}−1`, at the tower `exp(10⁹)`:
the raw/real/√/log windows plus `F ≤ X` and `x^{11/24}/4 ≤ F ≤ X`. -/
private theorem row_box_window {x k i F Krange X : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    x / 2 + 1 < X * pieceM k
      ∧ X * pieceM k ≤ 4 * x
      ∧ F ≤ X
      ∧ (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (F : ℝ)
      ∧ (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (X : ℝ) := by
  obtain ⟨hxpos, hx2, _, _⟩ := row_tower hx
  -- extract clauses (a copy, keeping `hi` folded)
  have hclauses := hi
  rw [dyadicBoundary, Finset.mem_filter] at hclauses
  obtain ⟨-, -, hfloor', -⟩ := hclauses
  -- raw window (X = 2^{i+1}−1 baked into `boundary_XM_raw`)
  obtain ⟨hlo0, hhi0⟩ := boundary_XM_raw hi
  have hlo : x / 2 + 1 < X * pieceM k := by rw [hXsub]; exact hlo0
  have hhi : X * pieceM k ≤ 4 * x := by rw [hXsub]; exact hhi0
  -- F ≤ X from m-floor F < 2^{i+1}
  have hFX : F ≤ X := by rw [hXsub]; omega
  -- operating floor F ≥ x^{11/24}/4
  have hFR : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (F : ℝ) := by
    have hzy := zy_floor_ge (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 10 ^ 9)) hx)
    have hFeq : (F : ℝ)
        = ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
      rw [hF]; rfl
    rw [hFeq]; exact hzy
  have hFXR : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (X : ℝ) :=
    le_trans hFR (by exact_mod_cast hFX)
  exact ⟨hlo, hhi, hFX, hFR, hFXR⟩

/-! ## §2 — the class-(i) rows (landed atoms) -/

/-- **Row `hNfloor` (#5).**  `x^{7/16}/8 ≤ 2^k` for a LIVE boundary box, via
`kfloor_of_live_box` at `z = opZ x ≤ x^{1/8}`.  Margin: `2√2 < 8`. -/
theorem row_hNfloor {x k i F Krange : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hlive : 2 ^ i < opZ x * pieceN k + 1) :
    (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := by
  obtain ⟨hxpos, _, _, _⟩ := row_tower hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.exp (10 ^ 9) := by
      have := Real.add_one_le_exp ((10 : ℝ) ^ 9); linarith
    linarith
  have hz : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    change ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8)
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  subst hF
  exact kfloor_of_live_box hx1 hi hlive hz

/-- **Row `hDsq` (#13).**  `D < (2^k+1)²` via the carrier k-floor
(`y_lt_two_pow_succ_of_carrier`: `opY x < 2^{k+1}`) and `hDsq_piece_of_kfloor ∘ hDsmall_at_op`.
Needs the m-floor clause `opZ x · opY x < 2^{i+1}` and the live carrier.  Margin: `x^{1/9}`. -/
theorem row_hDsq {x k i F Krange D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hlive : 2 ^ i < opZ x * pieceN k + 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)) :
    D < (2 ^ k + 1) * (2 ^ k + 1) := by
  obtain ⟨hxpos, _, _, hlogx⟩ := row_tower hx
  -- the m-floor clause `F < 2^{i+1}`, i.e. `opZ x · opY x < 2^{i+1}`
  have hclauses := hi
  rw [dyadicBoundary, Finset.mem_filter] at hclauses
  obtain ⟨-, -, hfloor', -⟩ := hclauses
  rw [hF] at hfloor'
  -- carrier k-floor `opY x < 2^{k+1}`
  have hkf : opY x < 2 ^ (k + 1) := y_lt_two_pow_succ_of_carrier hlive hfloor'
  -- `x ≥ 10^{96}` (from the tower)
  have hx96 : (10 : ℝ) ^ 96 ≤ (x : ℝ) := by
    have hlog10 : Real.log 10 ≤ 9 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)]
    have hkey : (96 : ℝ) * Real.log 10 ≤ Real.log x := by
      have h9 : (96 : ℝ) * 9 ≤ (10 : ℝ) ^ 9 := by norm_num
      nlinarith [hlog10, hlogx]
    calc (10 : ℝ) ^ 96 = Real.exp (Real.log ((10 : ℝ) ^ 96)) :=
          (Real.exp_log (by positivity)).symm
      _ = Real.exp ((96 : ℝ) * Real.log 10) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hkey
      _ = (x : ℝ) := Real.exp_log hxpos
  -- `D ≤ x^{5/9}` (499/1000 < 5/9)
  have hD59 : (D : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 9) := by
    refine le_trans hDhi ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hDsmall := hDsmall_at_op hx96 hD59
  exact hDsq_piece_of_kfloor hkf hDsmall

/-! ## §3 — the D-scale rows (`hDscale`, `herr_lev`, `hDx`, `hDXM`) -/

/-- **Row `hDx` (#20).**  `D ≤ √x` from `D ≤ x^{499/1000} ≤ x^{1/2} = √x`. -/
theorem row_hDx {x D : ℕ} (hx1 : (1 : ℝ) ≤ (x : ℝ))
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)) :
    (D : ℝ) ≤ Real.sqrt (x : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact le_trans hDhi (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))

/-- **`row_const_le_rpow`** — the tower closure `(27/10)^n ≤ x^c` whenever `n ≤ c·10⁹`
(`c > 0`), at `x ≥ exp(10⁹)`.  The engine behind every `Const ≤ x^{gap}` numeric close. -/
private theorem row_const_le_rpow {x : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ)) {c : ℝ}
    (hc : 0 < c) (n : ℕ) (hn : (n : ℝ) ≤ c * 10 ^ 9) :
    ((27 : ℝ) / 10) ^ n ≤ (x : ℝ) ^ c := by
  obtain ⟨hxpos, -, -, hlogx⟩ := row_tower hx
  have hmul : c * (10 ^ 9 : ℝ) ≤ c * Real.log x := mul_le_mul_of_nonneg_left hlogx hc.le
  calc ((27 : ℝ) / 10) ^ n ≤ Real.exp (n : ℝ) := a12_pow27_le_exp n
    _ ≤ Real.exp (c * Real.log x) := Real.exp_le_exp.mpr (by linarith [hn, hmul])
    _ = (x : ℝ) ^ c := by rw [Real.rpow_def_of_pos hxpos]; congr 1; ring

/-- **`row_mono_close`** — `C·x^a ≤ x^b` for `a < b`, `x ≥ exp(10⁹)`, `C ≤ (27/10)^n ≤ x^{b−a}`. -/
private theorem row_mono_close {x : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ)) {a b C : ℝ}
    {n : ℕ} (hab : a < b) (hC : C ≤ ((27 : ℝ) / 10) ^ n)
    (hnc : (n : ℝ) ≤ (b - a) * 10 ^ 9) :
    C * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
  obtain ⟨hxpos, -, -, -⟩ := row_tower hx
  have hstep : ((27 : ℝ) / 10) ^ n ≤ (x : ℝ) ^ (b - a) := row_const_le_rpow hx (by linarith) n hnc
  have hann : (0 : ℝ) ≤ (x : ℝ) ^ a := Real.rpow_nonneg hxpos.le _
  calc C * (x : ℝ) ^ a ≤ ((27 : ℝ) / 10) ^ n * (x : ℝ) ^ a := mul_le_mul_of_nonneg_right hC hann
    _ ≤ (x : ℝ) ^ (b - a) * (x : ℝ) ^ a := mul_le_mul_of_nonneg_right hstep hann
    _ = (x : ℝ) ^ b := by rw [← Real.rpow_add hxpos]; congr 1; ring

/-! ## §4 — the `D·L^p ≤ √(X·M)` core (`hDscale`, `herr_lev`) -/

/-- **`row_DLpow_le_sqrtXM`** — `D·L^p ≤ √(X·M)` for `0 ≤ p ≤ 18`, at `D ≤ x^{499/1000}`.
`D·L^p ≤ 262144·x^{999/2000} ≤ (1/2)√x ≤ √(X·M)` (margin `x^{1/2000}` over the level gap). -/
private theorem row_DLpow_le_sqrtXM {x k i F Krange X D : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000))
    {p : ℝ} (hp0 : 0 ≤ p) (hp18 : p ≤ 18) :
    (D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ p
      ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ)) := by
  obtain ⟨hxpos, hx2, hlogx1, hlogx⟩ := row_tower hx
  obtain ⟨hlo, hhi, -, -, -⟩ := row_box_window hx hF hi hXsub
  subst hXsub
  obtain ⟨hLlow, hLhi⟩ := boundary_log_bounds hx2 hi
  set L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) with hLdef
  have hL0 : 0 ≤ L := by linarith [hLlow, hlogx]
  have hLle : L ≤ 2 * Real.log x := by linarith [hLhi, hlogx]
  have hLpow : L ^ p ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) :=
    row_Lpow_le hlogx1 hL0 hLle hpl hp0 hp18
  have hDL : (D : ℝ) * L ^ p
      ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000)) :=
    mul_le_mul hDhi hLpow (Real.rpow_nonneg hL0 p) (Real.rpow_nonneg hxpos.le _)
  have heq : (x : ℝ) ^ ((499 : ℝ) / 1000) * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000))
      = 262144 * (x : ℝ) ^ ((999 : ℝ) / 2000) := by
    have h : (x : ℝ) ^ ((499 : ℝ) / 1000) * (x : ℝ) ^ ((1 : ℝ) / 2000)
        = (x : ℝ) ^ ((999 : ℝ) / 2000) := by rw [← Real.rpow_add hxpos]; congr 1; norm_num
    calc (x : ℝ) ^ ((499 : ℝ) / 1000) * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000))
        = 262144 * ((x : ℝ) ^ ((499 : ℝ) / 1000) * (x : ℝ) ^ ((1 : ℝ) / 2000)) := by ring
      _ = 262144 * (x : ℝ) ^ ((999 : ℝ) / 2000) := by rw [h]
  have hmono : (524288 : ℝ) * (x : ℝ) ^ ((999 : ℝ) / 2000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
    row_mono_close hx (a := 999 / 2000) (b := 1 / 2) (C := 524288) (n := 14)
      (by norm_num) (by norm_num) (by norm_num)
  have hsqrtXM : (1 / 2 : ℝ) * Real.sqrt x
      ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) := (xm_sqrt_bounds hlo hhi).1
  have hsx : Real.sqrt (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  calc (D : ℝ) * L ^ p
      ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000)) := hDL
    _ = 262144 * (x : ℝ) ^ ((999 : ℝ) / 2000) := heq
    _ ≤ (1 / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) := by linarith [hmono]
    _ = (1 / 2) * Real.sqrt x := by rw [hsx]
    _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) := hsqrtXM

/-- **Row `hDscale` (#12).**  `D ≤ √(X·M)/L^{15}`. -/
theorem row_hDscale {x k i F Krange X D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)) :
    (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
        / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ) := by
  obtain ⟨-, hx2, -, hlogx⟩ := row_tower hx
  have hLpos : 0 < Real.log ((X : ℝ) * (pieceM k : ℝ)) := by
    rw [hXsub]; obtain ⟨hLlow, -⟩ := boundary_log_bounds hx2 hi; linarith [hlogx]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
  exact row_DLpow_le_sqrtXM hx hpl hF hi hXsub hDhi (by norm_num) (by norm_num)

/-- **Row `herr_lev` (#17).**  `D·L^{18} ≤ √(X·M)`. -/
theorem row_herr_lev {x k i F Krange X D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)) :
    (D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ)) :=
  row_DLpow_le_sqrtXM hx hpl hF hi hXsub hDhi (by norm_num) (by norm_num)

/-! ## §5 — the `L^p ≤ √X` / `L^p ≤ √(pieceM k)` rows (`hXsqrt`, `hMsqrt`, `herr_Mlev`) -/

/-- **Row `hXsqrt` (#15).**  `L^{16} ≤ √X` from `√X ≥ x^{11/48}/2` (X ≥ F ≥ x^{11/24}/4). -/
theorem row_hXsqrt {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ) := by
  obtain ⟨hxpos, hx2, hlogx1, hlogx⟩ := row_tower hx
  obtain ⟨-, -, -, -, hFXR⟩ := row_box_window hx hF hi hXsub
  subst hXsub
  obtain ⟨hLlow, hLhi⟩ := boundary_log_bounds hx2 hi
  set L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) with hLdef
  have hL0 : 0 ≤ L := by linarith [hLlow, hlogx]
  have hLle : L ≤ 2 * Real.log x := by linarith [hLhi, hlogx]
  have hLpow : L ^ ((13 : ℝ) + 3) ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) :=
    row_Lpow_le hlogx1 hL0 hLle hpl (by norm_num) (by norm_num)
  have hsqrtX : (x : ℝ) ^ ((11 : ℝ) / 48) / 2 ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) := by
    rw [show (x : ℝ) ^ ((11 : ℝ) / 48) / 2
        = Real.sqrt (((x : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h48 : ((x : ℝ) ^ ((11 : ℝ) / 48)) ^ (2 : ℕ) = (x : ℝ) ^ ((11 : ℝ) / 24) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((11 : ℝ) / 48)) 2, ← Real.rpow_mul hxpos.le,
        show (11 : ℝ) / 48 * ((2 : ℕ) : ℝ) = 11 / 24 by push_cast; ring]
    have hsq : ((x : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ) = (x : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
      rw [div_pow, h48]; norm_num
    rw [hsq]; exact hFXR
  have htail : (262144 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2000) ≤ (x : ℝ) ^ ((11 : ℝ) / 48) / 2 := by
    have hm := row_mono_close hx (a := 1 / 2000) (b := 11 / 48) (C := 524288) (n := 14)
      (by norm_num) (by norm_num) (by norm_num)
    linarith [hm]
  calc L ^ ((13 : ℝ) + 3) ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
    _ ≤ (x : ℝ) ^ ((11 : ℝ) / 48) / 2 := htail
    _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) := hsqrtX

/-- **Rows `hMsqrt` (#16, `E = 16`) / `herr_Mlev` (#18, `E = 18`).**  `L^E ≤ √(pieceM k)` for
`0 ≤ E ≤ 18`, from `√(pieceM k) ≥ x^{7/32}/3` (`pieceM k ≥ 2^k ≥ x^{7/16}/8`). -/
theorem row_hMsqrt {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hNf : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ))
    {E : ℝ} (hE0 : 0 ≤ E) (hE18 : E ≤ 18) :
    (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ E ≤ Real.sqrt (pieceM k : ℝ) := by
  obtain ⟨hxpos, hx2, hlogx1, hlogx⟩ := row_tower hx
  subst hXsub
  obtain ⟨hLlow, hLhi⟩ := boundary_log_bounds hx2 hi
  set L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) with hLdef
  have hL0 : 0 ≤ L := by linarith [hLlow, hlogx]
  have hLle : L ≤ 2 * Real.log x := by linarith [hLhi, hlogx]
  have hLpow : L ^ E ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) :=
    row_Lpow_le hlogx1 hL0 hLle hpl hE0 hE18
  have hMge : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (pieceM k : ℝ) :=
    le_trans hNf (by exact_mod_cast two_pow_le_pieceM k)
  have hx716nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) := Real.rpow_nonneg hxpos.le _
  have hsqrtM : (x : ℝ) ^ ((7 : ℝ) / 32) / 3 ≤ Real.sqrt (pieceM k : ℝ) := by
    rw [show (x : ℝ) ^ ((7 : ℝ) / 32) / 3
        = Real.sqrt (((x : ℝ) ^ ((7 : ℝ) / 32) / 3) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h32 : ((x : ℝ) ^ ((7 : ℝ) / 32)) ^ (2 : ℕ) = (x : ℝ) ^ ((7 : ℝ) / 16) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((7 : ℝ) / 32)) 2, ← Real.rpow_mul hxpos.le,
        show (7 : ℝ) / 32 * ((2 : ℕ) : ℝ) = 7 / 16 by push_cast; ring]
    have hsq : ((x : ℝ) ^ ((7 : ℝ) / 32) / 3) ^ (2 : ℕ) = (x : ℝ) ^ ((7 : ℝ) / 16) / 9 := by
      rw [div_pow, h32]; norm_num
    rw [hsq]; linarith [hMge, hx716nn]
  have htail : (262144 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2000) ≤ (x : ℝ) ^ ((7 : ℝ) / 32) / 3 := by
    have hm := row_mono_close hx (a := 1 / 2000) (b := 7 / 32) (C := 786432) (n := 15)
      (by norm_num) (by norm_num) (by norm_num)
    linarith [hm]
  calc L ^ E ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
    _ ≤ (x : ℝ) ^ ((7 : ℝ) / 32) / 3 := htail
    _ ≤ Real.sqrt (pieceM k : ℝ) := hsqrtM

/-! ## §6 — the structural / arithmetic rows -/

/-- **Row `hL2` (#7).**  `2 ≤ log(X·M)` from `log(X·M) ≥ log x − 1 ≥ 10⁹ − 1`. -/
theorem row_hL2 {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) := by
  obtain ⟨-, hx2, -, hlogx⟩ := row_tower hx
  subst hXsub
  obtain ⟨hLlow, -⟩ := boundary_log_bounds hx2 hi
  linarith [hlogx]

/-- **Row `hX2` (#8).**  `2 ≤ X` from `X ≥ F ≥ x^{11/24}/4 ≥ 2`. -/
theorem row_hX2 {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) : 2 ≤ X := by
  obtain ⟨-, -, -, -, hFXR⟩ := row_box_window hx hF hi hXsub
  have h8 : (8 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
    le_trans (by norm_num : (8 : ℝ) ≤ ((27 : ℝ) / 10) ^ 3)
      (row_const_le_rpow hx (by norm_num) 3 (by norm_num))
  have : (2 : ℝ) ≤ (X : ℝ) := by linarith [hFXR, h8]
  exact_mod_cast this

/-- **Row `hD1` (#9).**  `1 ≤ D` from `D ≥ x^{11/24}/8 ≥ 1`. -/
theorem row_hD1 {x D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hDlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) : 1 ≤ D := by
  have h8 : (8 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
    le_trans (by norm_num : (8 : ℝ) ≤ ((27 : ℝ) / 10) ^ 3)
      (row_const_le_rpow hx (by norm_num) 3 (by norm_num))
  have : (1 : ℝ) ≤ (D : ℝ) := by linarith [hDlo, h8]
  exact_mod_cast this

/-- **Row `hFX` (#19).**  `F ≤ X` from the m-floor clause `F < 2^{i+1}`. -/
theorem row_hFX {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) : F ≤ X := by
  obtain ⟨-, -, hFX, -, -⟩ := row_box_window hx hF hi hXsub
  exact hFX

/-- **Row `hLbb` (#21).**  `log(X·M) ≤ log(4x)` from `X·M ≤ 4x`. -/
theorem row_hLbb {x k i F Krange X : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Real.log (4 * (x : ℝ)) := by
  obtain ⟨hlo, hhi, -, -, -⟩ := row_box_window hx hF hi hXsub
  have hcast : ((X * pieceM k : ℕ) : ℝ) = (X : ℝ) * (pieceM k : ℝ) := by push_cast; ring
  have hXMpos : (0 : ℝ) < (X : ℝ) * (pieceM k : ℝ) := by
    rw [← hcast]; have : 0 < X * pieceM k := by omega
    exact_mod_cast this
  have hle : (X : ℝ) * (pieceM k : ℝ) ≤ 4 * (x : ℝ) := by rw [← hcast]; exact_mod_cast hhi
  exact Real.log_le_log hXMpos hle

/-- **Row `hDXM` (#23).**  `D ≤ X·M` from `D ≤ √x ≤ x/2 < X·M`. -/
theorem row_hDXM {x k i F Krange X D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000)) :
    (D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
  obtain ⟨hxpos, -, -, -⟩ := row_tower hx
  obtain ⟨hlo, hhi, -, -, -⟩ := row_box_window hx hF hi hXsub
  have hx4 : (4 : ℝ) ≤ (x : ℝ) := by
    have h1 : (4 : ℝ) ≤ Real.exp (10 ^ 9) := by
      linarith [Real.add_one_le_exp ((10 : ℝ) ^ 9), (by norm_num : (4 : ℝ) ≤ 1 + 10 ^ 9)]
    linarith [hx, h1]
  have hDx := row_hDx (by linarith [hx4]) hDhi
  have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) / 2 := by
    rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt; nlinarith [hx4, hxpos]
  have hhalf : (x : ℝ) / 2 < (X : ℝ) * (pieceM k : ℝ) := (xm_real_bounds hlo hhi).2.1
  linarith [hDx, hsqrtx, hhalf]

/-- **Row `habs` (#14).**  `4(1+log D)·D ≤ 2^k·M/L^{13}`.  `LHS·L^{13} ≤ 2097152·x^{1/2}
≤ x^{7/8}/64 ≤ (2^k)² ≤ 2^k·M`, using `hNfloor` (`2^k ≥ x^{7/16}/8`).  Margin `x^{3/8}` vs `2²⁷`. -/
theorem row_habs {x k i F Krange X D : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000))
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000))
    (hNf : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ)) :
    4 * (1 + Real.log D) * (D : ℝ)
      ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
          / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) := by
  obtain ⟨hxpos, hx2, hlogx1, hlogx⟩ := row_tower hx
  have hLpos : 0 < Real.log ((X : ℝ) * (pieceM k : ℝ)) := by
    rw [hXsub]; obtain ⟨hLlow, -⟩ := boundary_log_bounds hx2 hi; linarith [hlogx]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
  subst hXsub
  obtain ⟨hLlow, hLhi⟩ := boundary_log_bounds hx2 hi
  set L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) with hLdef
  have hL0 : 0 ≤ L := by linarith [hLlow, hlogx]
  have hLle : L ≤ 2 * Real.log x := by linarith [hLhi, hlogx]
  have hLpow : L ^ (13 : ℝ) ≤ 262144 * (x : ℝ) ^ ((1 : ℝ) / 2000) :=
    row_Lpow_le hlogx1 hL0 hLle hpl (by norm_num) (by norm_num)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
    linarith
  have hlogx_poly : Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 2000) := row_logx_le hlogx1 hpl
  have hDxle : (D : ℝ) ≤ (x : ℝ) := le_trans hDhi
    (by calc (x : ℝ) ^ ((499 : ℝ) / 1000) ≤ (x : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
          _ = (x : ℝ) := Real.rpow_one _)
  have hlogD : Real.log D ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]; linarith [hlogx1]
    · exact Real.log_le_log (by exact_mod_cast hDpos) hDxle
  have hx2000_1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000) := Real.one_le_rpow hx1 (by norm_num)
  have hA : 4 * (1 + Real.log D) ≤ 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) := by
    have : Real.log D ≤ (x : ℝ) ^ ((1 : ℝ) / 2000) := le_trans hlogD hlogx_poly
    linarith [this, hx2000_1]
  have hprod : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
      ≤ 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
          * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000)) := by
    have h1 : 4 * (1 + Real.log D) * (D : ℝ)
        ≤ 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000) :=
      mul_le_mul hA hDhi (Nat.cast_nonneg D) (by positivity)
    exact mul_le_mul h1 hLpow (Real.rpow_nonneg hL0 _) (by positivity)
  have heq : 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
        * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000)) = 2097152 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hxa : (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
          * (x : ℝ) ^ ((1 : ℝ) / 2000)
        = (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; congr 1; norm_num
    calc 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
          * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000))
        = 2097152 * ((x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
            * (x : ℝ) ^ ((1 : ℝ) / 2000)) := by ring
      _ = 2097152 * (x : ℝ) ^ ((1 : ℝ) / 2) := by rw [hxa]
  have hclose : (2097152 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((7 : ℝ) / 8) / 64 := by
    have hm := row_mono_close hx (a := 1 / 2) (b := 7 / 8) (C := 134217728) (n := 20)
      (by norm_num) (by norm_num) (by norm_num)
    linarith [hm]
  have heq2 : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 * ((x : ℝ) ^ ((7 : ℝ) / 16) / 8)
      = (x : ℝ) ^ ((7 : ℝ) / 8) / 64 := by
    rw [div_mul_div_comm, ← Real.rpow_add hxpos, show (7 : ℝ) / 16 + 7 / 16 = 7 / 8 by norm_num]
    norm_num
  have hnf2 : (x : ℝ) ^ ((7 : ℝ) / 8) / 64 ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
    have hprodk : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 * ((x : ℝ) ^ ((7 : ℝ) / 16) / 8)
        ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) :=
      mul_le_mul hNf hNf (by positivity) (Nat.cast_nonneg _)
    rw [← heq2]; exact hprodk
  have hkm : ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast two_pow_le_pieceM k) (Nat.cast_nonneg _)
  calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
      ≤ 8 * (x : ℝ) ^ ((1 : ℝ) / 2000) * (x : ℝ) ^ ((499 : ℝ) / 1000)
          * (262144 * (x : ℝ) ^ ((1 : ℝ) / 2000)) := hprod
    _ = 2097152 * (x : ℝ) ^ ((1 : ℝ) / 2) := heq
    _ ≤ (x : ℝ) ^ ((7 : ℝ) / 8) / 64 := hclose
    _ ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := hnf2
    _ ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) := hkm

/-- **Row `hfloor` (#22).**  `(3/log2)⁸·x^{1/6}·Lb^{18} ≤ √F` at `Lb = log(4x)`,
`F = opZ x · opY x`.  Direct transfer of `GlueFinal.hfloor_row` (threshold `e^{4000}`). -/
theorem row_hfloor {x F : ℕ} (hx : Real.exp 4000 ≤ (x : ℝ))
    (hF : F = opZ x * opY x) {Lb : ℝ} (hLb : Lb = Real.log (4 * (x : ℝ))) :
    ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (F : ℝ) := by
  subst hLb
  rw [show (13 : ℝ) + 5 = (18 : ℝ) by norm_num, hF]
  exact hfloor_row hx

/-! ## §7 — the composite `box_rows_at_op` -/

/-- **`box_rows_at_op` (fin7a, the BOX-leg row bundle).**  At the operating parameters
(`F = opZ x · opY x`, `X = 2^{i+1}−1`, `M = pieceM k`, `2^k` the block scale, `Lb = log(4x)`,
`D` with `x^{11/24}/8 ≤ D ≤ x^{499/1000}` covering `opQ·(QR·opDlev)`) for a LIVE boundary box,
EVERY analytic hypothesis of `ChenHeadline.box_hprice_at_2pow_lo` holds simultaneously.  This
lets fin8 apply `box_hprice_at_2pow_lo` with NO analytic side conditions — only the structural
facts (`hk`, `hi`, `hXsub`) and the H_W constants (`N₀ ≤ 2^k` from `hNfloor`, `Q·QR·Dlev ≤ D`)
remaining.  The 18 conjuncts, in `box_hprice_at_2pow_lo`'s binder order:
`hx, hNfloor, hL2, hX2, hD1, hDge_x, hDscale, hDsq, habs, hXsqrt, hMsqrt, herr_lev, herr_Mlev,
hFX, hDx, hLbb, hfloor, hDXM`. -/
theorem box_rows_at_op :
    ∃ x₁ : ℝ, ∀ (x : ℕ), x₁ ≤ (x : ℝ) →
      ∀ (k i X F Krange D : ℕ) (Lb : ℝ),
        F = opZ x * opY x →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        2 ^ i < opZ x * pieceN k + 1 →
        Lb = Real.log (4 * (x : ℝ)) →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) →
        Real.exp (10 ^ 9) ≤ (x : ℝ)
        ∧ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ)
        ∧ 2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ))
        ∧ 2 ≤ X
        ∧ 1 ≤ D
        ∧ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)
        ∧ (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)
        ∧ D < (2 ^ k + 1) * (2 ^ k + 1)
        ∧ 4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)
        ∧ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)
        ∧ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM k : ℝ)
        ∧ (D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
        ∧ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM k : ℝ)
        ∧ F ≤ X
        ∧ (D : ℝ) ≤ Real.sqrt (x : ℝ)
        ∧ Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Lb
        ∧ ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)
        ∧ (D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
  obtain ⟨xpl, hxpl⟩ := a12_logpow_le_rpow 18 (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨max (Real.exp (10 ^ 9)) ((xpl : ℝ)), ?_⟩
  intro x hx₁ k i X F Krange D Lb hF hi hXsub hlive hLb hDlo hDhi
  have hx : Real.exp (10 ^ 9) ≤ (x : ℝ) := le_trans (le_max_left _ _) hx₁
  have hxplx : xpl ≤ x := by
    have h : (xpl : ℝ) ≤ (x : ℝ) := le_trans (le_max_right _ _) hx₁
    exact_mod_cast h
  have hpl : (Real.log x) ^ (18 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2000) := hxpl x hxplx
  have hNf := row_hNfloor hx hF hi hlive
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h2 : (2 : ℝ) ≤ (x : ℝ) := by obtain ⟨-, hx2, -, -⟩ := row_tower hx; exact_mod_cast hx2
    linarith
  refine ⟨hx, hNf, row_hL2 hx hi hXsub, row_hX2 hx hF hi hXsub, row_hD1 hx hDlo, hDlo,
    row_hDscale hx hpl hF hi hXsub hDhi, row_hDsq hx hF hi hlive hDhi,
    row_habs hx hpl hi hXsub hDhi hNf, row_hXsqrt hx hpl hF hi hXsub,
    row_hMsqrt hx hpl hi hXsub hNf (by norm_num) (by norm_num),
    row_herr_lev hx hpl hF hi hXsub hDhi,
    row_hMsqrt hx hpl hi hXsub hNf (by norm_num) (by norm_num),
    row_hFX hx hF hi hXsub, row_hDx hx1 hDhi, ?_, ?_, row_hDXM hx hF hi hXsub hDhi⟩
  · rw [hLb]; exact row_hLbb hx hF hi hXsub
  · exact row_hfloor (le_trans (Real.exp_le_exp.mpr (by norm_num)) hx) hF hLb

/-! ## §8 — anti-#69 witness: the bundle feeds `box_hprice_at_2pow_lo` -/

/-- **The anti-#69 witness (#4).**  `box_rows_at_op` actually feeds `box_hprice_at_2pow_lo`:
at symbolic operating values, past the row threshold and with the H_W structural facts (`hk`,
`hi`, `hXsub`, `hlive`, `N₀ ≤ 2^k`, `Q·QR·Dlev ≤ D`), the row bundle discharges every analytic
slot, so the box price term `_price` type-checks.  This is the disciplined check that the bundle
is not vacuous and its shapes match the consumer character-for-character. -/
example (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps) (hQPs : Nat.Coprime Q Ps)
    (hQa2 : Nat.Coprime Q (a + 2)) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (x : ℕ) (ε₀ : ℝ) (j k i F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ)
    (hk : 2 ≤ k) (hF : F = opZ x * opY x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange)
    (hXsub : X = 2 ^ (i + 1) - 1) (hlive : 2 ^ i < opZ x * pieceN k + 1)
    (hDlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ))
    (hDhi : (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000))
    (hDbnd : (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ)) : True := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := box_hprice_at_2pow_lo z y Ps Q a hQ1 hPspos hQPs hQa2 hPodd
  obtain ⟨x₁, hrows⟩ := box_rows_at_op
  by_cases hprem : x₁ ≤ (x : ℝ) ∧ N₀ ≤ 2 ^ k
  · obtain ⟨hxge, hN₀⟩ := hprem
    obtain ⟨hxt, hNfloor, hL2, hX2, hD1, hDge_x, hDscale, hDsq, habs, hXsqrt, hMsqrt,
      herr_lev, herr_Mlev, hFX, hDx, hLbb, hfloor, hDXM⟩ :=
      hrows x hxge k i X F Krange D (Real.log (4 * (x : ℝ))) hF hi hXsub hlive rfl hDlo hDhi
    have _price := hbody x ε₀ j k i (Real.log (4 * (x : ℝ))) F Krange X QR Dlev D
      hk hxt hi hXsub hNfloor hN₀ hL2 hX2 hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt
      herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM
    trivial
  · trivial

end Salt.Chen
