/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenFinal

/-!
# Node fin6 — the band window (F0) + the row bundles (F1) + F2 + F3 → `chen_headline`

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin5` entry (★ CATCH #72 ★ — the band-carrier
k-floor asymmetry — and its RATIFIED ADDITIVE repair, the band D0 window at floor `x^{1/3}/8`), the
`fin4` / `EDGE` / `PRICE-3b` / `PRICE-GATE` entries.  New file; no edits to any landed file.

This node closes the PRICE wave.  It is organized in floors (F0 → F1-rows → F2 → F3).

## Floor F0 — the band D0 window + the band price mirrors (the catch #72 additive repair)

The box leg meets the `x^{7/16}/8` price floor via `kfloor_of_live_box`; the band carriers
`blockAlphaSym`/`blockAlphaLow` do NOT (catch #72: their live boxes only give `2^k ≳ x^{1/3}`).  The
repair is a `d0_window` variant at the band floor `x^{1/3}/8` (fin5-ratified, ADDITIVE):

* **`d0_window_of_XM_band`** — the PriceTwo §1b construction re-run at the band floor
  `x^{1/3}/8 ≤ N`, with `W := (1/3)·log x − 7`.  The ONLY binding row is `hD0N'`
  (`4·L^{17} ≤ W^{18}`); with the
  Lean-safe ratio `L ≤ (31/10)·W` it closes at `log x ≥ 3·(4·(31/10)^{17} + 7) ≈ 2.71·10⁹` — we take
  the clean tower `log x ≥ 10^{10}` (margin ≈ 3.7×).  The whole-assembly tower (`Ccon·K ~ 10^{23}`)
  dwarfs this, so `x ≥ exp(10^{10})` is free downstream.

  | quantity                                    | value at `t = log x = 10^{10}`  |
  |---------------------------------------------|---------------------------------|
  | `W = (1/3)·10^{10} − 7`                      | `≈ 3.333·10⁹`                   |
  | ratio bound used: `L ≤ (31/10)·W`           | `31/10 = 3.1 > 3 = lim L/W`     |
  | binding requirement `4·(31/10)^{17} ≤ W`    | `4·(31/10)^{17} ≈ 9.02·10⁸`     |
  | **room** `W / (4·(31/10)^{17})`             | **`≈ 3.7×`**                    |

* **`medium_box_price_at_op_band`** — `medium_box_price_at_op_lo` restated at the band floor
  `x^{1/3}/8 ≤ 2^k` and tower `exp(10^{10})`, reading off `medium_box_price_core` by feeding
  `d0_window_of_XM_band`.  Conclusion character-for-character identical to `_lo`/`_at_op`.

* **`sym_box_hprice_at_2pow_band` / `low_box_hprice_at_2pow_band`** — the PriceThree band legs
  (`sym_/low_box_hprice_at_2pow`) rerouted through `medium_box_price_at_op_band` (band floor).

* **`band_kfloor_of_live`** — the band live-box k-floor: a live band box has `y < 2^k` (from
  ChenFinal's `blockAlphaLow_eq_zero_of_pieceN_le` / `blockAlphaSym_eq_zero_of_pieceM_le`
  contrapositive, and the sym `max`-collapse `y ≤ pieceN k`), so with the operating fact
  `x^{1/3}/8 ≤ y` (from `opY x = ⌊x^{1/3}⌋`) the band floor `x^{1/3}/8 ≤ 2^k` holds.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §F0.1 — `d0_window_of_XM_band` — the band-floor D0 window (catch #72 additive repair)

The band-floor (`x^{1/3}/8`) analogue of `d0_window_of_XM_lo`.  Same catch-#71 factoring (raw
`X·M` bounds), block floor `x^{1/3}/8 ≤ N`, `W := (1/3)·log x − 7`, tower `exp(10^{10})`, ratio
`L ≤ (31/10)·W`.  IDENTICAL 9-conjunct conclusion (the `x`-scale conjunct kept at `x^{11/24}/8` via
the bump `x^{1/3} ≤ x^{11/24}`).  `SqrtDFold`/`d0_window_of_XM_lo` are left untouched. -/

/-- **`d0_window_of_XM_band` (fin6 F0, catch #72 additive repair).**  `d0_window_of_XM_lo` with the
block floor at the band bottom `x^{1/3}/8 ≤ N` and the tower raised to `exp(10^{10})` (so the
binding row `4·L^{17} ≤ W^{18}` closes at `W = (1/3)·log x − 7`).  Conclusion
character-for-character `d0_window_of_XM_lo`'s (the `x`-scale conjunct kept at `x^{11/24}/8`). -/
theorem d0_window_of_XM_band {x N M X : ℕ}
    (hx : Real.exp (10 ^ 10) ≤ (x : ℝ))
    (hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (N : ℝ))
    (hXMlo : x / 2 + 1 < X * M)
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
  have hXM : x / 2 + 1 < X * M := hXMlo
  have hXM4x : X * M ≤ 4 * x := hXMhi
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hXM4xR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hXM4x
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  have hL_lo : Real.log x - 1 ≤ L := by
    have h1 : x < (x / 2 + 1) * 2 := by omega
    have h2 : x / 2 + 1 ≤ X * M := by omega
    have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
    have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast h2
    push_cast at h1R h2R
    have hhalf : (x : ℝ) / 2 < (X : ℝ) * (M : ℝ) := by linarith
    have hlog : Real.log ((x : ℝ) / 2) ≤ L := Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hL_up : L ≤ Real.log x + 3 := by
    have h1 : L ≤ Real.log (4 * (x : ℝ)) := Real.log_le_log hXMposR hXM4xR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith
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
  have hL17_1 : (1 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  obtain ⟨n, hn_ge, hn_le⟩ :
      ∃ n : ℕ, L ^ ((17 : ℝ)) ≤ (n : ℝ) ∧ (n : ℝ) ≤ L ^ ((17 : ℝ)) + 1 :=
    ⟨⌈L ^ ((17 : ℝ))⌉₊, Nat.le_ceil _,
      le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hLnn _))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  obtain ⟨k0, hnpow, hpow2n⟩ : ∃ k0 : ℕ, n ≤ 2 ^ k0 ∧ 2 ^ k0 ≤ 2 * n := by
    refine ⟨Nat.clog 2 n, Nat.le_pow_clog (by norm_num) n, ?_⟩
    have hk0pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
    have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hsplit]
    exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
  have hD0_lo : L ^ ((17 : ℝ)) ≤ ((2 ^ k0 : ℕ) : ℝ) := by
    refine le_trans hn_ge ?_
    exact_mod_cast hnpow
  have hD0_hi : ((2 ^ k0 : ℕ) : ℝ) ≤ 4 * L ^ ((17 : ℝ)) := by
    have h1 : ((2 ^ k0 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpow2n
    linarith
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
  refine ⟨2 ^ k0, k0, rfl, le_trans (by omega : 2 ≤ n) hnpow, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
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

/-! ## §F0.2 — `band_kfloor_of_live` — the band live-box k-floor (catch #72's `2^k > y` form)

The box leg meets the `x^{7/16}/8` floor via `kfloor_of_live_box` (carrier VANISHES ABOVE its cap).
The band carriers have the MIRRORED geometry (catch #72): they vanish BELOW `pieceN k ≤ y`
(`blockAlphaLow_eq_zero_of_pieceN_le`) resp. `pieceM k ≤ y` (`blockAlphaSym_eq_zero_of_pieceM_le`),
so a LIVE band box has `y < pieceN k`/`y < pieceM k`, i.e. `y < 2^k`.  With the operating fact
`x^{1/3}/8 ≤ y` (from `opY x = ⌊x^{1/3}⌋`, `x` large) the band floor `x^{1/3}/8 ≤ 2^k` follows — the
floor `d0_window_of_XM_band` needs.  Stated abstractly (`y < 2^k` + `x^{1/3}/8 ≤ y`): the low leg
supplies `y < pieceN k = 2^k − 1 < 2^k`, the sym leg via its `max`-collapse `y ≤ pieceN k < 2^k`. -/

/-- **`band_kfloor_of_live` (fin6 F0).**  A live band box gives `y < 2^k`; with the operating
`x^{1/3}/8 ≤ y` the band floor `x^{1/3}/8 ≤ 2^k` holds — the hypothesis
`medium_box_price_at_op_band` demands for the band legs. -/
theorem band_kfloor_of_live {x y k : ℕ}
    (hy : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ))
    (hlt : y < 2 ^ k) :
    (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := by
  have hylt : (y : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hlt
  linarith

/-- The low-band live form: `blockAlphaLow z y ε₀ j (pieceN k) m ≠ 0 ⟹ y < 2^k`.  Contrapositive of
`blockAlphaLow_eq_zero_of_pieceN_le`. -/
theorem lt_two_pow_of_blockAlphaLow_ne_zero {z y : ℕ} {ε₀ : ℝ} {j k m : ℕ}
    (h : blockAlphaLow z y ε₀ j (pieceN k) m ≠ 0) : y < 2 ^ k := by
  by_contra hc
  have hc' : 2 ^ k ≤ y := Nat.not_lt.mp hc
  -- `2^k ≤ y ⟹ pieceN k = 2^k − 1 ≤ y`
  have : pieceN k ≤ y := by unfold pieceN; omega
  exact h (blockAlphaLow_eq_zero_of_pieceN_le this)

/-- The low-band live form (the low dichotomy's priced branch): `y < pieceN k ⟹ y < 2^k`
(`pieceN k = 2^k − 1`).  Supplies `band_kfloor_of_live`'s `hlt` for the low leg. -/
theorem lt_two_pow_of_lt_pieceN {y k : ℕ} (h : y < pieceN k) : y < 2 ^ k := by
  unfold pieceN at h; omega

/-- The sym-band live form (the sym dichotomy's priced branch, on the `max`-collapse strip):
`y ≤ pieceN k ⟹ y < 2^k` (`pieceN k = 2^k − 1 < 2^k`).  Supplies `band_kfloor_of_live`'s `hlt` for
the sym leg, where the price also needs `y ≤ pieceN k` for the `max`-collapse.  NOTE (catch #72,
recorded): the sym vanishing lemma alone gives only `y < pieceM k`, i.e. `2^k > y/2`; the sharp
`y < 2^k` for the sym leg comes from the collapse condition `y ≤ pieceN k`, which the sym feeder
`sym_box_hprice_at_2pow(_band)` requires anyway. -/
theorem lt_two_pow_of_le_pieceN {y k : ℕ} (h : y ≤ pieceN k) : y < 2 ^ k := by
  have hpk : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  unfold pieceN at h; omega

/-! ## §F0.3 — `medium_box_price_at_op_band` — the box price at the band floor

`medium_box_price_at_op_lo` restated with the block-floor hypothesis at the band bottom
`x^{1/3}/8 ≤ 2^k` (was `x^{7/16}/8`) and the tower raised to `exp(10^{10})`.  Read off
`medium_box_price_core` by feeding `d0_window_of_XM_band`; the tower for the core (`exp(10^9)`) is
derived from the raised one.  The `x^{11/24}/8 ≤ D` row `hDge_x` is UNCHANGED (it consumes the
bundle's `x`-scale conjunct, kept at `x^{11/24}/8`).  Conclusion character-for-character identical
to `medium_box_price_at_op(_lo)`. -/

/-- **`medium_box_price_at_op_band` (fin6 F0).**  `medium_box_price_at_op_lo` at the band floor
`x^{1/3}/8 ≤ 2^k`, tower `exp(10^{10})`, routing through `medium_box_price_core` + the band D0
window `d0_window_of_XM_band`.  Conclusion identical to PriceOne's `medium_box_price_at_op`. -/
theorem medium_box_price_at_op_band :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x : ℕ) (Lb : ℝ) (F Krange k i : ℕ) (α : ℕ → ℂ) (X T D : ℕ)
        (Dset : Finset ℕ) (r : ℕ → ℕ),
        2 ≤ k →
        Real.exp (10 ^ 10) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        (∀ m, ‖α m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) →
        (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (∀ d ∈ Dset, d ≤ D) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM k : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM k : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt (x : ℝ)) →
        (Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        ((D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ)) →
        ∑ d ∈ Dset,
            ‖apDiscBilinCutoff α (blockPrimeInd (pieceN k)) X (pieceM k) (r d) d T‖
          ≤ (Kbeta_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                  (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
              + (6 * (Km_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                        (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                  + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                      * Kbeta'_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
            * ((X : ℝ) * (pieceM k : ℝ)) / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) := by
  obtain ⟨K, N₀, hK0, hcore⟩ := medium_box_price_core
  refine ⟨K, N₀, hK0, fun x Lb F Krange k i α X T D Dset r hk hx hi hXsub hNfloor hα hd1 hcop2
    hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor hDXM => ?_⟩
  -- the core wants the `exp(10^9)` tower; the band floor demands `exp(10^{10})`.
  have hx9 : Real.exp (10 ^ 9) ≤ (x : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  -- rebuild the band `D0`-window from the WEAK pieceN corner (catch #71, ratified (a)).
  have hpk : pieceN k + 1 = 2 ^ k := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  have hclause := hi
  rw [dyadicBoundary, Finset.mem_filter] at hclause
  obtain ⟨-, hcorner, -, hcutoff⟩ := hclause
  rw [hpk] at hcorner
  have hXMlo : x / 2 + 1 < X * pieceM k := by rw [hXsub]; exact hcutoff
  have hXMhi : X * pieceM k ≤ 4 * x := by
    have hXle : X ≤ 2 ^ (i + 1) := by rw [hXsub]; exact Nat.sub_le _ _
    calc X * pieceM k ≤ 2 ^ (i + 1) * (2 * 2 ^ k) := Nat.mul_le_mul hXle (pieceM_le_two_pow k)
      _ = 4 * (2 ^ i * 2 ^ k) := by rw [pow_succ]; ring
      _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
  exact hcore x Lb F Krange k i α X T D Dset r hk hx9 hi hXsub hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1
    hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM
    (d0_window_of_XM_band (N := 2 ^ k) (M := pieceM k) hx hNfloor hXMlo hXMhi)

/-! ## §F0.4 — the band-leg per-box prices at the band floor (`_band` mirrors)

`sym_box_hprice_at_2pow_band` / `low_box_hprice_at_2pow_band` are the band floor (`x^{1/3}/8`)
analogues of PriceThree's `sym_box_hprice_at_2pow` / `low_box_hprice_at_2pow`, routing through
`medium_box_price_at_op_band` in place of `medium_box_price_at_op`.  Same structure (`max`-collapse
for sym; carrier `≤ 1`-norm; `Q`-image Dset rows discharged internally), tower `exp(10^{10})`, floor
`x^{1/3}/8 ≤ 2^k`. -/

/-- **`sym_box_hprice_at_2pow_band` (fin6 F0).**  The band-floor mirror of
`sym_box_hprice_at_2pow`: the sym carrier's two-`T` sum is `≤ 2·(Kerr price)` at the band floor
`x^{1/3}/8 ≤ 2^k` (tower `exp(10^{10})`).  Uses `max y (pieceN k) = pieceN k`
(needs `y ≤ pieceN k`), then `medium_box_price_at_op_band` twice. -/
theorem sym_box_hprice_at_2pow_band (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        y ≤ pieceN k →
        Real.exp (10 ^ 10) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM k : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM k : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt (x : ℝ)) →
        (Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        ((D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ)) →
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                    (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                  (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * ((X : ℝ) * (pieceM k : ℝ))
              / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op_band
  refine ⟨Kc, N₀, hK0, fun x ε₀ j k i Lb F Krange X QR Dlev D hk hyN hx hi hXsub hNfloor hN₀ hL2
    hX2 hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
    hDXM => ?_⟩
  rw [max_y_pieceN_eq hyN]
  have hα := norm_sym_leg_le_one z y ε₀ j (pieceN k) (pieceM k) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  rw [two_mul]
  exact add_le_add
    (hbody x Lb F Krange k i _ X x D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub hNfloor hα
      hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
      hFX hDx hLbb hfloor hDXM)
    (hbody x Lb F Krange k i _ X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub
      hNfloor hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
      herr_Mlev hFX hDx hLbb hfloor hDXM)

/-- **`low_box_hprice_at_2pow_band` (fin6 F0).**  The band-floor mirror of
`low_box_hprice_at_2pow`: the low carrier's two-`T` sum is `≤ 2·(Kerr price)` at the band floor
`x^{1/3}/8 ≤ 2^k` (tower `exp(10^{10})`).  Indicator already `blockPrimeInd (pieceN k)`
(no collapse); `medium_box_price_at_op_band` twice. -/
theorem low_box_hprice_at_2pow_band (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        Real.exp (10 ^ 10) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM k : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM k : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt (x : ℝ)) →
        (Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        ((D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ)) →
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                    (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * ((X : ℝ) * (pieceM k : ℝ))
              / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op_band
  refine ⟨Kc, N₀, hK0, fun x ε₀ j k i Lb F Krange X QR Dlev D hk hx hi hXsub hNfloor hN₀ hL2 hX2
    hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
    hDXM => ?_⟩
  have hα := norm_low_leg_le_one z y ε₀ j (pieceN k) (min (z * pieceN k + 1) (x + 1)) (x + 1) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  rw [two_mul]
  exact add_le_add
    (hbody x Lb F Krange k i _ X x D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub hNfloor hα
      hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
      hFX hDx hLbb hfloor hDXM)
    (hbody x Lb F Krange k i _ X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub
      hNfloor hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
      herr_Mlev hFX hDx hLbb hfloor hDXM)

end Salt.Chen
