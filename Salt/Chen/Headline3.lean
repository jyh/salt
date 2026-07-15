/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenRows1
import Salt.Chen.ChenRows2

/-!
# Node fin8 — the final-assembly atoms (F1 residuals: the band `habs` row + the middle-`k` guard)

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin7b` entry (★ CATCH #73 ★ — the sym middle-`k`
box, ADJUDICATED SMALL) and the `fin7a`/`fin6`/`fin5`/`PRICE-3b` row-checklist entries.  New file;
namespace `Salt.Chen`; NO edits to any landed file; NOT wired into `All.lean`.

This file lands the two F1 **residuals** that `fin7b` explicitly threaded to fin8 (its report:
"Residuals threaded to fin8: rows 12 (caller QR) + 15 (habs, one more poly3 row)"), plus the
middle-`k` `M ≤ 2·N` guard the `middle_k_price` repair needs.  Both `low_rows_at_op` and
`sym_rows_at_op` (ChenRows2) take the band `habs` row as an *input* hypothesis; fin8 discharges it
here.

* **`band_habs_row`** (F1 residual #15).  The `4·(1+log D)·D ≤ 2^k·M/L^{13}` row at the **band**
  floor `x^{1/3}/8 ≤ 2^k` (fin7a's `row_habs` needed the stronger box floor `x^{7/16}/8`).  One
  more `poly3` application (the `log3pow_le_rpow` engine from ChenRows2): `LHS·L^{13} ≤
  4·(log x+3)^{14}·x^{1/2−9·10⁻⁵} ≤ x^{2/3}/64 = (x^{1/3}/8)² ≤ (2^k)² ≤ 2^k·M`.

* **`middle_k_M_le_two_y`** (the catch-#73 `M ≤ 2N` guard at `N := y`).  On the single middle `k`
  (`pieceN k < y`), `2^k ≤ y` gives `pieceM k ≤ 2·y` — the `M ≤ 2·N` guard of
  `medium_survivor_price_sqrtD` closes at `N := y` DIRECTLY (no `2^k` bridge), exactly as the
  fin7b/#73 adjudication records.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §1 — the band `habs` row (F1 residual #15, "one more poly3 row") -/

/-- **`band_habs_row` (F1 residual #15).**  The `habs` row of `low_rows_at_op`/`sym_rows_at_op`
(`4·(1+log D)·D ≤ 2^k·(pieceM k)/L^{13}`, `L = log((2^{i+1}−1)·pieceM k)`) at the **band** floor
`x^{1/3}/8 ≤ 2^k` and `D ≤ x^{1/2−9·10⁻⁵}` (the `opD` bound), given the raw `X·M`-window
`x/2+1 < (2^{i+1}−1)·pieceM k ≤ 4x` (from `boundary_XM_raw`).  Discharge (poly3):
`LHS·L^{13} ≤ 4·(log x+3)^{14}·x^{1/2−9·10⁻⁵} ≤ x^{2/3}/64 = (x^{1/3}/8)² ≤ (2^k)² ≤ 2^k·(pieceM k)`
— the band floor `2^k ≥ x^{1/3}/8` supplies the last two steps with `x^{1/12}` room. -/
theorem band_habs_row :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → ∀ (k i D : ℕ),
      (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
      (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) →
      x / 2 + 1 < (2 ^ (i + 1) - 1) * pieceM k →
      (2 ^ (i + 1) - 1) * pieceM k ≤ 4 * x →
      4 * (1 + Real.log D) * (D : ℝ)
        ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
            / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) := by
  obtain ⟨x₂, h₂⟩ := log3pow_le_rpow (14 : ℝ) (1 / 12) (by norm_num) (by norm_num)
  obtain ⟨x₃, h₃⟩ := a12_log_ge (max 6 (12 * Real.log 256))
  refine ⟨max 2 (max x₂ x₃), fun x hx k i D hNfloor hDub hXMlo hXMhi => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx2x : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3x : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨_hexpx, hlogx⟩ := h₃ x hx3x
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlogx6 : (6 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hlog256 : 12 * Real.log 256 ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  -- the `L` window `log x − 1 ≤ L ≤ log x + 3`
  obtain ⟨hLlo, hLub⟩ := xm_log_bounds hx2 hXMlo hXMhi
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) with hLdef
  have hLnn : (0 : ℝ) ≤ L := by linarith [hLlo, hlogx6]
  have hLpos : (0 : ℝ) < L := by linarith [hLlo, hlogx6]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
  -- factor bounds
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hDx : (D : ℝ) ≤ (x : ℝ) := by
    refine le_trans hDub ?_
    calc (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hlogD : Real.log D ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast hDpos) hDx
  have hLb3nn : (0 : ℝ) ≤ Real.log x + 3 := by linarith
  have hLb3pos : (0 : ℝ) < Real.log x + 3 := by linarith
  have hfac1 : 4 * (1 + Real.log D) ≤ 4 * (Real.log x + 3) := by linarith
  have hL13 : L ^ (13 : ℝ) ≤ (Real.log x + 3) ^ (13 : ℝ) :=
    Real.rpow_le_rpow hLnn hLub (by norm_num)
  have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hLnn _
  have hAnn : (0 : ℝ) ≤ 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hxpos.le _)
  -- LHS ≤ 4·(log x+3)·x^{1/2−9e−5}·(log x+3)^{13}
  have hprod : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
      ≤ 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
          * (Real.log x + 3) ^ (13 : ℝ) := by
    have s1 : 4 * (1 + Real.log D) * (D : ℝ)
        ≤ 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
      mul_le_mul hfac1 hDub hDnn (by linarith)
    calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
        ≤ (4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) * L ^ (13 : ℝ) :=
          mul_le_mul_of_nonneg_right s1 hL13nn
      _ ≤ (4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000))
            * (Real.log x + 3) ^ (13 : ℝ) :=
          mul_le_mul_of_nonneg_left hL13 hAnn
  -- (log x+3)^{14} ≤ x^{1/12}
  have hpoly : (Real.log x + 3) ^ (14 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := h₂ x hx2x
  -- 256 ≤ x^{1/12}
  have h256 : (256 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
    have hkey : Real.log 256 ≤ Real.log x * ((1 : ℝ) / 12) := by linarith
    calc (256 : ℝ) = Real.exp (Real.log 256) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log x * ((1 : ℝ) / 12)) := Real.exp_le_exp.mpr hkey
      _ = (x : ℝ) ^ ((1 : ℝ) / 12) := (Real.rpow_def_of_pos hxpos _).symm
  -- x^{2/3}/64 = (x^{1/3}/8)² ≤ (2^k)² ≤ 2^k·M
  have hx23eq : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      = (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := by
    rw [div_mul_div_comm, ← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 1 / 3 = 2 / 3 by norm_num]
    norm_num
  have hsqfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) :=
    mul_le_mul hNfloor hNfloor (by positivity) (Nat.cast_nonneg _)
  have hkm : ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast two_pow_le_pieceM k) (Nat.cast_nonneg _)
  -- numeric closure
  have hfinal : 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
        * (Real.log x + 3) ^ (13 : ℝ)
      ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) := by
    have hstep1 : 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
          * (Real.log x + 3) ^ (13 : ℝ)
        = 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (Real.log x + 3) ^ (14 : ℝ) := by
      rw [show (14 : ℝ) = 1 + 13 by norm_num, Real.rpow_add hLb3pos, Real.rpow_one]; ring
    rw [hstep1]
    have hs2 : 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (Real.log x + 3) ^ (14 : ℝ)
        ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    have hmid : 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12)
        ≤ (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
      have hcomb : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12)
            * (x : ℝ) ^ ((1 : ℝ) / 12)
          = (x : ℝ) ^ ((2 : ℝ) / 3 - 9 / 100000) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; congr 1; norm_num
      have hx23le : (x : ℝ) ^ ((2 : ℝ) / 3 - 9 / 100000) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      calc 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12) * 64
          = 256 * ((x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12)) := by ring
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 12)
              * ((x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12)) :=
            mul_le_mul_of_nonneg_right h256 (by positivity)
        _ = (x : ℝ) ^ ((2 : ℝ) / 3 - 9 / 100000) := by rw [← hcomb]; ring
        _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := hx23le
    calc 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (Real.log x + 3) ^ (14 : ℝ)
        ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((1 : ℝ) / 12) := hs2
      _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := hmid
      _ = (x : ℝ) ^ ((1 : ℝ) / 3) / 8 * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) := hx23eq.symm
      _ ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := hsqfloor
      _ ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) := hkm
  calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
      ≤ 4 * (Real.log x + 3) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (Real.log x + 3) ^ (13 : ℝ) :=
        hprod
    _ ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ) := hfinal

/-! ## §2 — the middle-`k` `M ≤ 2·N` guard at `N := y` (catch #73) -/

/-- **`middle_k_M_le_two_y` (catch #73 guard).**  On the single middle `k` (`pieceN k < y`),
`2^k ≤ y` gives `pieceM k ≤ 2·y` — the `M ≤ 2·N` guard of `medium_survivor_price_sqrtD` closes at
`N := y` directly (no `2^k` bridge), exactly as the fin7b/#73 adjudication records. -/
theorem middle_k_M_le_two_y {y k : ℕ} (h : pieceN k < y) : pieceM k ≤ 2 * y := by
  have h2k : 2 ^ k ≤ y := two_pow_le_of_pieceN_lt h
  have hM : pieceM k = 2 ^ (k + 1) - 1 := rfl
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  omega

end Salt.Chen
