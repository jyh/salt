/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# A power of two in `[y, 4y]`, and the scale window `x/2 < X·M ≤ 4x`

For a real `y ≥ 2` there is a `k` with `y ≤ 2^k ≤ 4y`: round `y` up to the natural `n = ⌈y⌉`
(so `n ≤ y + 1 ≤ 2y`), then take the least power of two at or above `n`, which is at most `2n`.

This is the dyadic-window step that the Chen and Goldbach band assemblies took inline
(`ChenFinal2`, `PriceOne`, `PriceTwo` ×2, `BandWin`, `D0Win`, `D0Win2`), each time at
`y = L ^ 17`. The first conjunct `2 ≤ 2^k` is what those assemblies pass on as the window's
floor. `k` is returned by an existential, so `Nat.clog` and `Nat.ceil` stay out of reach of
defeq at the call site.

## Main result
* `exists_two_pow_window` — for `2 ≤ y`, some `k` has `2 ≤ 2^k`, `y ≤ 2^k` and `2^k ≤ 4·y`.
* `xm_log_bounds_of_le` — `log x − 1 ≤ log(X·M) ≤ log x + 3` from `x/2 + 1 ≤ X·M ≤ 4x`, `x ≥ 2`;
  `xm_log_bounds` is its strict form, and `xm_real_bounds(_of_le)` the real window under it.
* `d0_window_core_band`, `d0_window_core_lo`, `d0_window_core_lo_bump` — the `D0`-window theorem
  of the Chen and Goldbach band assemblies, at the band floor and at the strip floor.
-/

namespace Salt.Chen

/-- **A dyadic point in `[y, 4y]`.** For `2 ≤ y` there is `k` with `2 ≤ 2^k`, `y ≤ 2^k` and
`2^k ≤ 4·y`. Proof: `n = ⌈y⌉₊` satisfies `y ≤ n ≤ y + 1` and `1 < n`; `k = Nat.clog 2 n` gives
`n ≤ 2^k ≤ 2n`. -/
theorem exists_two_pow_window {y : ℝ} (hy : 2 ≤ y) :
    ∃ k : ℕ, 2 ≤ 2 ^ k ∧ y ≤ ((2 ^ k : ℕ) : ℝ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 4 * y := by
  obtain ⟨n, hn_ge, hn_le⟩ : ∃ n : ℕ, y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + 1 :=
    ⟨⌈y⌉₊, Nat.le_ceil _, le_of_lt (Nat.ceil_lt_add_one (by linarith))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  refine ⟨Nat.clog 2 n, ?_, ?_, ?_⟩
  · exact le_trans (by omega : 2 ≤ n) (Nat.le_pow_clog (by norm_num) n)
  · exact le_trans hn_ge (by exact_mod_cast Nat.le_pow_clog (by norm_num) n)
  · have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      have := Nat.clog_pos (b := 2) (by norm_num) hn1
      omega
    have h2n : 2 ^ Nat.clog 2 n ≤ 2 * n := by
      rw [← hsplit]
      exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
    have h2nR : ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast h2n
    linarith

/-! ## The scale window `x/2 < X·M ≤ 4x` and its logarithm

From the raw Nat window `x/2 + 1 ≤ X·M ≤ 4x`, `X·M ≍ x` in `ℝ` and
`log(X·M) ∈ [log x − 1, log x + 3]`; the `−1` and `+3` are `log 2 ≤ 1` and `log 4 ≤ 3`. The
Chen and Goldbach band assemblies (`ChenFinal2`, `PriceOne`, `PriceTwo` ×2, `BandWin`, `D0Win`,
`D0Win2`) each derived the logarithmic pair inline. The `≤` forms serve the Goldbach annuli,
whose cut gives `x/2 + 1 ≤ X·M`; the strict forms are the box rows' original statements. -/

/-- **`xm_real_bounds_of_le`.** The real window from the raw Nat window: `0 < X·M`,
`x/2 < X·M`, `X·M ≤ 4x`. -/
theorem xm_real_bounds_of_le {x X M : ℕ} (hlo : x / 2 + 1 ≤ X * M) (hhi : X * M ≤ 4 * x) :
    (0 : ℝ) < (X : ℝ) * (M : ℝ)
      ∧ (x : ℝ) / 2 < (X : ℝ) * (M : ℝ)
      ∧ (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hhiR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hhi
  refine ⟨hXMposR, ?_, hhiR⟩
  have h1 : x < (x / 2 + 1) * 2 := by omega
  have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
  have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast hlo
  push_cast at h1R h2R
  linarith

/-- **`xm_real_bounds` (F1-rows(a)).** `xm_real_bounds_of_le` from the strict window
`x/2 + 1 < X·M`. -/
theorem xm_real_bounds {x X M : ℕ} (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    (0 : ℝ) < (X : ℝ) * (M : ℝ)
      ∧ (x : ℝ) / 2 < (X : ℝ) * (M : ℝ)
      ∧ (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) :=
  xm_real_bounds_of_le hlo.le hhi

/-- **`xm_log_bounds_of_le`.** `log x − 1 ≤ log(X·M) ≤ log x + 3` from the raw Nat window
(`x ≥ 2`). The `−1`/`+3` come from `log 2 ≤ 1` and `log 4 ≤ 3`. -/
theorem xm_log_bounds_of_le {x X M : ℕ} (hx : 2 ≤ x)
    (hlo : x / 2 + 1 ≤ X * M) (hhi : X * M ≤ 4 * x) :
    Real.log x - 1 ≤ Real.log ((X : ℝ) * (M : ℝ))
      ∧ Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log x + 3 := by
  obtain ⟨hXMposR, hhalf, hhiR⟩ := xm_real_bounds_of_le hlo hhi
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  constructor
  · have hlog : Real.log ((x : ℝ) / 2) ≤ Real.log ((X : ℝ) * (M : ℝ)) :=
      Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  · have h1 : Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log (4 * (x : ℝ)) :=
      Real.log_le_log hXMposR hhiR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith

/-- **`xm_log_bounds` (F1-rows(a)).** `xm_log_bounds_of_le` from the strict window
`x/2 + 1 < X·M`. -/
theorem xm_log_bounds {x X M : ℕ} (hx : 2 ≤ x)
    (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    Real.log x - 1 ≤ Real.log ((X : ℝ) * (M : ℝ))
      ∧ Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log x + 3 :=
  xm_log_bounds_of_le hx hlo.le hhi

/-! ## The `D0`-window cores (O13-e row 285)

The Chen and Goldbach band assemblies each derived the same `D0`-window statement in full: a dyadic
`D0 = 2^{k0}` in `[L^{17}, 4·L^{17}]` at `L = log(X·M)`, with the nine-conjunct conclusion the
price lemmas read. Two parameter sets occur. The band floor (`x^{1/3}/8 ≤ N`, tower `exp(10^{10})`,
ratio `L ≤ (31/10)·W`) gave `d0_window_of_XM_band` (`ChenFinal2`) and `gold_d0_window_band`
(`BandWin`). The strip floor (`x^{7/16}/8 ≤ N`, tower `exp(10^9)`, ratio `L ≤ (12/5)·W`) gave
`d0_window_of_XM_lo` (`PriceOne`), `d0_window_nonempty_lo` (`SqrtDFold`) and
`gold_d0_window_annulus` (`D0Win`). Each proof used the lower scale fact only as `x/2 + 1 ≤ X·M`,
so the cores below take that form. The Goldbach annuli supply it from `goldCut`, the box rows
from their strict `x/2 + 1 < X·M`, and all five are instances. `d0_window_core_lo` gives the
`x`-scale conjunct at the floor's own exponent `7/16`; `d0_window_core_lo_bump` relaxes it to
`11/24`, the form the Chen strip lemmas state.
-/

/-- **`d0_window_core_band`.** The band-floor `D0` window: block floor `x^{1/3}/8 ≤ N`, tower
`exp(10^{10})`, `W := (1/3)·log x − 7`, ratio `L ≤ (31/10)·W`, and the raw scale window
`x/2 + 1 ≤ X·M ≤ 4x`. The `x`-scale conjunct is `x^{11/24}/8`, via the bump
`x^{1/3} ≤ x^{11/24}`. -/
theorem d0_window_core_band {x N M X : ℕ}
    (hx : Real.exp (10 ^ 10) ≤ (x : ℝ))
    (hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (N : ℝ))
    (hXMlo : x / 2 + 1 ≤ X * M)
    (hXMhi : X * M ≤ 4 * x) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ N := by
  -- ① the scale facts: `t ≥ 10^{10}`, `x ≥ 2`.
  have h1010 : (10 : ℝ) ^ 10 = 10000000000 := by norm_num
  have ht : (10 : ℝ) ^ 10 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 10)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  -- ② the scale facts (from the RAW bounds): `x/2 < X·M ≤ 4x`.
  have hXM4x : X * M ≤ 4 * x := hXMhi
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  obtain ⟨hL_lo, hL_up⟩ : Real.log x - 1 ≤ L ∧ L ≤ Real.log x + 3 :=
    xm_log_bounds_of_le hx2 hXMlo hXM4x
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by linarith
  have hL20 : (1048576 : ℝ) ≤ L := by linarith
  -- ④ the block-floor log: `W := (1/3)·t − 7 ≤ log N`  (the band floor).
  set W : ℝ := 1 / 3 * Real.log x - 7 with hWdef
  have hWlogN : W ≤ Real.log N := by
    have hlogN := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num))
      hNfloor
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num : (8 : ℝ) ≠ 0),
      Real.log_rpow hxpos] at hlogN
    have h8log : Real.log 8 ≤ 7 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]
    rw [hWdef]
    linarith
  have hWpos : (0 : ℝ) < W := by rw [hWdef]; linarith
  have hW1296 : (1296 : ℝ) ≤ W := by rw [hWdef]; linarith
  have hLW : L ≤ 31 / 10 * W := by rw [hWdef]; linarith
  have hW4 : 4 * ((31 : ℝ) / 10) ^ ((17 : ℝ)) ≤ W := by
    have hc : ((31 : ℝ) / 10) ^ ((17 : ℝ)) = ((31 : ℝ) / 10) ^ (17 : ℕ) := by
      rw [show ((17 : ℝ)) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnum : 4 * ((31 : ℝ) / 10) ^ (17 : ℕ) ≤ 1 / 3 * 10 ^ 10 - 7 := by norm_num
    rw [hc, hWdef]
    linarith
  -- ⑤ the dyadic window: `D0 = 2^{k0} ∈ [L^{17}, 4·L^{17}]`.
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  obtain ⟨k0, h2k0, hD0_lo, hD0_hi⟩ := Salt.Chen.exists_two_pow_window hL17_2
  have hL18eq : L ^ ((18 : ℝ)) = L * L ^ ((17 : ℝ)) := by
    have hh := Real.rpow_add hLpos 1 17
    rw [Real.rpow_one] at hh
    rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
  have h17nn : (0 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.rpow_nonneg hLnn _
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}` (the band-floor binding row, ≈ 3.7× room).
  have hW18 : 4 * L ^ ((17 : ℝ)) ≤ W ^ ((18 : ℝ)) := by
    have hW17 : L ^ ((17 : ℝ)) ≤ ((31 : ℝ) / 10) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) := by
      calc L ^ ((17 : ℝ)) ≤ (31 / 10 * W) ^ ((17 : ℝ)) :=
            Real.rpow_le_rpow hLnn hLW (by norm_num)
        _ = ((31 : ℝ) / 10) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) :=
            Real.mul_rpow (by norm_num) hWpos.le
    have hW18eq : W ^ ((18 : ℝ)) = W * W ^ ((17 : ℝ)) := by
      have hh := Real.rpow_add hWpos 1 17
      rw [Real.rpow_one] at hh
      rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
    have h17Wnn : (0 : ℝ) ≤ W ^ ((17 : ℝ)) := Real.rpow_nonneg hWpos.le _
    rw [hW18eq]
    calc 4 * L ^ ((17 : ℝ))
        ≤ 4 * (((31 : ℝ) / 10) ^ ((17 : ℝ)) * W ^ ((17 : ℝ))) := by linarith
      _ = (4 * ((31 : ℝ) / 10) ^ ((17 : ℝ))) * W ^ ((17 : ℝ)) := by ring
      _ ≤ W * W ^ ((17 : ℝ)) := mul_le_mul_of_nonneg_right hW4 h17Wnn
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W ≤ x^{1/3}/8`  (SHARP at the band floor).
  have hexpW : W ^ ((18 : ℝ)) ≤ Real.exp W := by
    have hunn : (0 : ℝ) ≤ W / 36 := by linarith
    have hquad : W ≤ (W / 36) ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexpand : (W / 36) ^ (2 : ℕ) = W * W / 1296 := by ring
      rw [hexpand, le_div_iff₀ (by norm_num : (0 : ℝ) < 1296)]
      have keyq : (0 : ℝ) ≤ (W - 1296) * W := mul_nonneg (by linarith) hWpos.le
      linarith [keyq]
    have hu : W / 36 ≤ Real.exp (W / 36) := by linarith [Real.add_one_le_exp (W / 36)]
    calc W ^ ((18 : ℝ))
        ≤ ((W / 36) ^ ((2 : ℝ))) ^ ((18 : ℝ)) :=
          Real.rpow_le_rpow hWpos.le hquad (by norm_num)
      _ = (W / 36) ^ ((36 : ℝ)) := by
          rw [← Real.rpow_mul hunn]
          norm_num
      _ ≤ (Real.exp (W / 36)) ^ ((36 : ℝ)) := Real.rpow_le_rpow hunn hu (by norm_num)
      _ = Real.exp W := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
  have hexp_le : Real.exp W ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 := by
    have hEW : Real.exp W = (x : ℝ) ^ ((1 : ℝ) / 3) / Real.exp 7 := by
      rw [hWdef, Real.exp_sub, Real.rpow_def_of_pos hxpos]
      have hmul : Real.log (x : ℝ) * ((1 : ℝ) / 3) = 1 / 3 * Real.log x := by ring
      rw [hmul]
    rw [hEW]
    have h7 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by norm_num) h7
  -- the `x`-scale bump: `x^{1/3}/8 ≤ x^{11/24}/8`  (`1/3 ≤ 11/24`, `x ≥ 1`).
  have hxbump : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have hmono : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith [hmono]
  -- ⑧ emit the rows.
  have hcast : ((2 ^ k0 : ℕ) : ℝ) = (2 : ℝ) ^ k0 := by push_cast; ring
  refine ⟨2 ^ k0, k0, rfl, h2k0, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hD0lo_main`, the DECOUPLED row (exponent `A+2 = 15`)
    have h15 : L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2k0pos : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    calc L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) := h15
      _ ≤ ((2 ^ k0 : ℕ) : ℝ) := hD0_lo
      _ = (2 : ℝ) ^ k0 := hcast
      _ ≤ 2 * (2 : ℝ) ^ k0 := by linarith
  · -- `hD0` (`D0 ≤ L^{C0}`, `C0 = 18`)
    rw [hL18eq]
    have key : (0 : ℝ) ≤ (L - 4) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
    linarith [hD0_hi, key]
  · -- `hD0N'` (`D0 ≤ (log N)^{C0}`, `C0 = 18`) — the binding band-floor row
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log N) ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hWpos.le hWlogN (by norm_num)
    linarith [hD0_hi, hW18, hmono]
  · -- `herr_D0E` in the `herr_scale` form (`LE ≥ L/2`, exponent `C0 = 18`)
    intro LE hLE
    have hhalfpos : (0 : ℝ) < L / 2 := by linarith
    have hstep : 4 * L ^ ((17 : ℝ)) ≤ (L / 2) ^ ((18 : ℝ)) := by
      have hdiv : (L / 2) ^ ((18 : ℝ)) = L ^ ((18 : ℝ)) / (2 : ℝ) ^ ((18 : ℝ)) :=
        Real.div_rpow hLnn (by norm_num) _
      have h218 : (2 : ℝ) ^ ((18 : ℝ)) = 262144 := by
        rw [show ((18 : ℝ)) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hdiv, h218, hL18eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)]
      have key : (0 : ℝ) ≤ (L - 1048576) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
      linarith [key]
    have hmono : (L / 2) ^ ((18 : ℝ)) ≤ LE ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hhalfpos.le (by linarith) (by norm_num)
    linarith [hD0_hi]
  · -- the `x`-scale bound (`D0 ≤ x^{11/24}/8`) — SAME conjunct, via bump
    linarith only [hD0_hi, hW18, hexpW, hexp_le, hxbump]
  · -- `hD0N` (`D0 ≤ N`) — SHARP off the band floor `x^{1/3}/8 ≤ N`
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (N : ℝ) := by
      linarith only [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-- **`d0_window_core_lo`.** The strip-floor `D0` window: block floor `x^{7/16}/8 ≤ N`, tower
`exp(10^9)`, `W := (7/16)·log x − 7`, ratio `L ≤ (12/5)·W`, and the raw scale window
`x/2 + 1 ≤ X·M ≤ 4x`. The `x`-scale conjunct is at the floor's exponent, `x^{7/16}/8`. -/
theorem d0_window_core_lo {x N M X : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hNfloor : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (N : ℝ))
    (hXMlo : x / 2 + 1 ≤ X * M)
    (hXMhi : X * M ≤ 4 * x) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8
      ∧ D0 ≤ N := by
  -- ① the scale facts: `t ≥ 10^9`, `x ≥ 2`.
  have h109 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
  have ht : (10 : ℝ) ^ 9 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- ② the scale facts (from the RAW bounds, in place of the boundary corner): `x/2 < X·M ≤ 4x`.
  have hXM4x : X * M ≤ 4 * x := hXMhi
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  obtain ⟨hL_lo, hL_up⟩ : Real.log x - 1 ≤ L ∧ L ≤ Real.log x + 3 :=
    xm_log_bounds_of_le hx2 hXMlo hXM4x
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by linarith
  have hL20 : (1048576 : ℝ) ≤ L := by linarith
  -- ④ the block-floor log: `W := (7/16)·t − 7 ≤ log N`  (the WEAKENED strip floor).
  set W : ℝ := 7 / 16 * Real.log x - 7 with hWdef
  have hWlogN : W ≤ Real.log N := by
    have hlogN := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num))
      hNfloor
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num : (8 : ℝ) ≠ 0),
      Real.log_rpow hxpos] at hlogN
    have h8log : Real.log 8 ≤ 7 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]
    rw [hWdef]
    linarith
  have hWpos : (0 : ℝ) < W := by rw [hWdef]; linarith
  have hW1296 : (1296 : ℝ) ≤ W := by rw [hWdef]; linarith
  have hLW : L ≤ 12 / 5 * W := by rw [hWdef]; linarith
  have hW4 : 4 * ((12 : ℝ) / 5) ^ ((17 : ℝ)) ≤ W := by
    have hc : ((12 : ℝ) / 5) ^ ((17 : ℝ)) = ((12 : ℝ) / 5) ^ (17 : ℕ) := by
      rw [show ((17 : ℝ)) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnum : 4 * ((12 : ℝ) / 5) ^ (17 : ℕ) ≤ 7 / 16 * 10 ^ 9 - 7 := by norm_num
    rw [hc, hWdef]
    linarith
  -- ⑤ the dyadic window: `D0 = 2^{k0} ∈ [L^{17}, 4·L^{17}]`.
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  obtain ⟨k0, h2k0, hD0_lo, hD0_hi⟩ := Salt.Chen.exists_two_pow_window hL17_2
  have hL18eq : L ^ ((18 : ℝ)) = L * L ^ ((17 : ℝ)) := by
    have hh := Real.rpow_add hLpos 1 17
    rw [Real.rpow_one] at hh
    rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
  have h17nn : (0 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.rpow_nonneg hLnn _
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}` (the Finding-3 anti-#64 margin, ≈ 37×).
  have hW18 : 4 * L ^ ((17 : ℝ)) ≤ W ^ ((18 : ℝ)) := by
    have hW17 : L ^ ((17 : ℝ)) ≤ ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) := by
      calc L ^ ((17 : ℝ)) ≤ (12 / 5 * W) ^ ((17 : ℝ)) :=
            Real.rpow_le_rpow hLnn hLW (by norm_num)
        _ = ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) :=
            Real.mul_rpow (by norm_num) hWpos.le
    have hW18eq : W ^ ((18 : ℝ)) = W * W ^ ((17 : ℝ)) := by
      have hh := Real.rpow_add hWpos 1 17
      rw [Real.rpow_one] at hh
      rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
    have h17Wnn : (0 : ℝ) ≤ W ^ ((17 : ℝ)) := Real.rpow_nonneg hWpos.le _
    rw [hW18eq]
    calc 4 * L ^ ((17 : ℝ))
        ≤ 4 * (((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ))) := by linarith
      _ = (4 * ((12 : ℝ) / 5) ^ ((17 : ℝ))) * W ^ ((17 : ℝ)) := by ring
      _ ≤ W * W ^ ((17 : ℝ)) := mul_le_mul_of_nonneg_right hW4 h17Wnn
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W ≤ x^{7/16}/8`  (SHARP at the strip floor).
  have hexpW : W ^ ((18 : ℝ)) ≤ Real.exp W := by
    have hunn : (0 : ℝ) ≤ W / 36 := by linarith
    have hquad : W ≤ (W / 36) ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexpand : (W / 36) ^ (2 : ℕ) = W * W / 1296 := by ring
      rw [hexpand, le_div_iff₀ (by norm_num : (0 : ℝ) < 1296)]
      have keyq : (0 : ℝ) ≤ (W - 1296) * W := mul_nonneg (by linarith) hWpos.le
      linarith [keyq]
    have hu : W / 36 ≤ Real.exp (W / 36) := by linarith [Real.add_one_le_exp (W / 36)]
    calc W ^ ((18 : ℝ))
        ≤ ((W / 36) ^ ((2 : ℝ))) ^ ((18 : ℝ)) :=
          Real.rpow_le_rpow hWpos.le hquad (by norm_num)
      _ = (W / 36) ^ ((36 : ℝ)) := by
          rw [← Real.rpow_mul hunn]
          norm_num
      _ ≤ (Real.exp (W / 36)) ^ ((36 : ℝ)) := Real.rpow_le_rpow hunn hu (by norm_num)
      _ = Real.exp W := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
  have hexp_le : Real.exp W ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 := by
    have hEW : Real.exp W = (x : ℝ) ^ ((7 : ℝ) / 16) / Real.exp 7 := by
      rw [hWdef, Real.exp_sub, Real.rpow_def_of_pos hxpos]
      have hmul : Real.log (x : ℝ) * ((7 : ℝ) / 16) = 7 / 16 * Real.log x := by ring
      rw [hmul]
    rw [hEW]
    have h7 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by norm_num) h7
  -- ⑧ emit the rows.
  have hcast : ((2 ^ k0 : ℕ) : ℝ) = (2 : ℝ) ^ k0 := by push_cast; ring
  refine ⟨2 ^ k0, k0, rfl, h2k0, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hD0lo_main`, the DECOUPLED row (exponent `A+2 = 15`)
    have h15 : L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2k0pos : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    calc L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) := h15
      _ ≤ ((2 ^ k0 : ℕ) : ℝ) := hD0_lo
      _ = (2 : ℝ) ^ k0 := hcast
      _ ≤ 2 * (2 : ℝ) ^ k0 := by linarith
  · -- `hD0` (`D0 ≤ L^{C0}`, `C0 = 18`)
    rw [hL18eq]
    have key : (0 : ℝ) ≤ (L - 4) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
    linarith [hD0_hi, key]
  · -- `hD0N'` (`D0 ≤ (log N)^{C0}`, `C0 = 18`) — the binding Finding-3 row
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log N) ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hWpos.le hWlogN (by norm_num)
    linarith [hD0_hi, hW18, hmono]
  · -- `herr_D0E` in the `herr_scale` form (`LE ≥ L/2`, exponent `C0 = 18`)
    intro LE hLE
    have hhalfpos : (0 : ℝ) < L / 2 := by linarith
    have hstep : 4 * L ^ ((17 : ℝ)) ≤ (L / 2) ^ ((18 : ℝ)) := by
      have hdiv : (L / 2) ^ ((18 : ℝ)) = L ^ ((18 : ℝ)) / (2 : ℝ) ^ ((18 : ℝ)) :=
        Real.div_rpow hLnn (by norm_num) _
      have h218 : (2 : ℝ) ^ ((18 : ℝ)) = 262144 := by
        rw [show ((18 : ℝ)) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hdiv, h218, hL18eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)]
      have key : (0 : ℝ) ≤ (L - 1048576) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
      linarith [key]
    have hmono : (L / 2) ^ ((18 : ℝ)) ≤ LE ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hhalfpos.le (by linarith) (by norm_num)
    linarith [hD0_hi]
  · -- the `x`-scale bound (`D0 ≤ x^{7/16}/8`)
    linarith only [hD0_hi, hW18, hexpW, hexp_le]
  · -- `hD0N` (`D0 ≤ N`) — SHARP off the strip floor `x^{7/16}/8 ≤ N`
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (N : ℝ) := by
      linarith only [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-- **`d0_window_core_lo_bump`.** `d0_window_core_lo` with the `x`-scale conjunct relaxed to
`x^{11/24}/8` (`7/16 ≤ 11/24`, `x ≥ 1`). -/
theorem d0_window_core_lo_bump {x N M X : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hNfloor : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (N : ℝ))
    (hXMlo : x / 2 + 1 ≤ X * M)
    (hXMhi : X * M ≤ 4 * x) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ N := by
  obtain ⟨D0, k0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := d0_window_core_lo hx hNfloor hXMlo hXMhi
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (Real.one_le_exp (by positivity)) hx
  have hmono : (x : ℝ) ^ ((7 : ℝ) / 16) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  exact ⟨D0, k0, h1, h2, h3, h4, h5, h6, h7, by linarith, h9⟩

end Salt.Chen
