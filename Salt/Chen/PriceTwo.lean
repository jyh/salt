/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PriceOne
import Salt.Chen.SwitchW2

/-!
# PRICE-2 — the lower-floor D0 variant + the band price variants (node PRICE-2)

Design: `docs/blueprints/flags.md`, the `2026-07-14 PRICE-GATE`/`PRICE-0`/`PRICE-1` entries and
the `GLU-2W-fin` scoping finding (Finding-3: the strip `N ∈ [x^{7/16}/4.9, x^{11/24}/8)` is real
and carries non-cancelling boxes).  This file is the PRICE wave's strip extension: it re-runs the
`d0_window_nonempty` construction at the WEAKER block floor `x^{7/16}/8 ≤ N` (deliverable 1), then
extends PriceOne's uniform per-box lemma to the strip bottom (deliverable 2) and prices the two
band carriers (`blockAlphaSym`/`blockAlphaLow`) at the operating point (deliverable 3), matching the
`PsymK`/`PlowK` price-input slots of the `SwitchW2` feeders character-for-character.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

1. (deliverable 1) **`d0_window_nonempty_lo`** — the Finding-3 variant of `SqrtDFold`'s
   `d0_window_nonempty`, with the block-floor hypothesis weakened from `x^{11/24}/8 ≤ N` to
   `x^{7/16}/8 ≤ N` (the honest strip bottom `√(x/(24z)) = x^{7/16}/(2√6) ≈ x^{7/16}/4.9`, floored
   at the convenient `/8`).  Identical 9-conjunct conclusion (the `x`-scale conjunct STAYS at
   `x^{11/24}/8`, a weaker upper bound the strip floor still supplies).  Only the binding `hD0N'`
   row (`D0 ≤ (log N)^{18}`) tightens; it holds with `≈ 37×` room at `t = 10^9` (theoretical
   ceiling `≈ 83×` at the asymptotic ratio `16/7`; see the section header for the margin table).

2. (deliverable 2) **`medium_box_price_at_op_lo`** — PriceOne's summit `medium_box_price_at_op`
   restated with the floor hypothesis at the strip bottom `x^{7/16}/8 ≤ 2^k`, consuming
   deliverable 1 in place of `d0_window_nonempty`; everything else reuses PriceOne's suppliers
   verbatim (a shared core `medium_box_price_core` parametrizes over the `D0`-window witness, with
   BOTH floors as instantiations).

3. (deliverable 3) **`sym_box_price_at_op` / `low_box_price_at_op`** — the analogues of
   `medium_box_price_at_op` at the band carriers, stated to slot into the `PsymK`/`PlowK` inputs of
   `PloW_sym_of_box_disc`/`PloW_low_of_box_disc` character-for-character.

4. (deliverable 4) **The satisfiability witnesses** (anti-#69 discipline): the `_lo` D0 witness
   fires at a concrete strip-shaped `N`; one band-price conclusion `#check`-slots into its feeder.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. `d0_window_nonempty_lo` — the Finding-3 lower-floor D0 window (deliverable 1)

**The strip and the floor.**  Finding-3 (PRICE-GATE, confirmed): the medium band carries live,
non-cancelling boxes down to the block scale `N = √(x/(24z)) = x^{7/16}/(2√6) ≈ x^{7/16}/4.9`
(below `d0_window_nonempty`'s floor `x^{11/24}/8`).  We floor at the convenient constant
`x^{7/16}/8` (strictly below the honest bottom, so the hypothesis covers the whole strip).

**What changes vs `d0_window_nonempty` (all else IDENTICAL, including the conclusion).**  The
block-floor log becomes `W := (7/16)·t − 7 ≤ log N` (was `(11/24)·t − 7`), with `t = log x ≥ 10^9`
and `L = log(X·M) ∈ [t−1, t+3]`.  The ONLY binding row is `hD0N'` (`D0 ≤ (log N)^{18}`), needing
`4·L^{17} ≤ W^{18}`:

  | quantity                                   | value at `t = 10^9`         |
  |--------------------------------------------|-----------------------------|
  | `W = (7/16)·10^9 − 7`                       | `≈ 4.375·10^8`              |
  | ratio bound used: `L ≤ (12/5)·W`           | `12/5 = 2.4 > 16/7 ≈ 2.286` |
  | binding requirement `4·(12/5)^{17} ≤ W`    | `4·(12/5)^{17} ≈ 1.16·10^7` |
  | **room** `W / (4·(12/5)^{17})`             | **`≈ 37×`**                 |
  | theoretical ceiling (ratio `→ 16/7`)       | `4·(16/7)^{17} ≈ 5.1·10^6`, `≈ 83×` |

So `hD0N'` does NOT fail: the gate's "83×+ room" claim is confirmed (37× with the concrete
Lean-valid ratio `12/5`, 83× at the asymptotic `16/7`).  NO catch #70 on this front.

The `x`-scale conjunct stays `D0 ≤ x^{11/24}/8`: the construction gives `D0 ≤ exp W ≤ x^{7/16}/8`,
which is bumped up to `x^{11/24}/8` via `x^{7/16} ≤ x^{11/24}` (`x ≥ 1`).  The `hD0N` conjunct
(`D0 ≤ N`) uses the SHARP `exp W ≤ x^{7/16}/8 ≤ N` directly off the weakened floor.  Do NOT edit
`SqrtDFold` — this variant lives here. -/

/-- **`d0_window_nonempty_lo` (node PRICE-2, deliverable 1).**  The Finding-3 lower-floor variant of
`d0_window_nonempty`: at the operating point (`x ≥ exp(10^9)`, `M ≤ 2N`) and the WEAKENED block
floor `x^{7/16}/8 ≤ N` (the honest strip bottom), EVERY `dyadicBoundary` box admits a `D0 = 2^{k0}`
satisfying ALL the `D0`-window rows of the repaired terminal family at `A = 13`, `C0 = 18` — the
IDENTICAL 9-conjunct conclusion of `d0_window_nonempty` (the `x`-scale conjunct is the same
`x^{11/24}/8` upper bound, weaker than the strip floor supplies).  See the section header for the
`hD0N'` margin table. -/
theorem d0_window_nonempty_lo {x N M K i X F : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hM2N : M ≤ 2 * N)
    (hNfloor : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (N : ℝ))
    (hi : i ∈ dyadicBoundary N M (x / 2 + 1) x F K)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
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
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  -- ② the boundary clauses: `x/2 < X·M ≤ 4x`.
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcutoff⟩ := hi
  have hXM : x / 2 + 1 < X * M := by rw [hXsub]; exact hcutoff
  have hXle : X ≤ 2 ^ (i + 1) := by rw [hXsub]; exact Nat.sub_le _ _
  have hXM4x : X * M ≤ 4 * x :=
    calc X * M ≤ 2 ^ (i + 1) * (2 * N) := Nat.mul_le_mul hXle hM2N
      _ = 4 * (2 ^ i * N) := by rw [pow_succ]; ring
      _ ≤ 4 * (2 ^ i * (N + 1)) :=
          Nat.mul_le_mul (le_refl 4) (Nat.mul_le_mul (le_refl (2 ^ i)) (Nat.le_succ N))
      _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
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
  -- the `x`-scale bump: `x^{7/16}/8 ≤ x^{11/24}/8`  (`7/16 ≤ 11/24`, `x ≥ 1`).
  have hxbump : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have hmono : (x : ℝ) ^ ((7 : ℝ) / 16) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
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
  · -- the `x`-scale bound (`D0 ≤ x^{11/24}/8`) — SAME conjunct as `d0_window_nonempty`, via bump
    linarith only [hD0_hi, hW18, hexpW, hexp_le, hxbump]
  · -- `hD0N` (`D0 ≤ N`) — SHARP off the strip floor `x^{7/16}/8 ≤ N`
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (N : ℝ) := by
      linarith only [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-! ## 2. The strip extension of the box lemma (deliverable 2)

PriceOne's `medium_box_price_at_op` restated at the strip bottom.  Its proof body consumes the
`D0`-window supplier ONLY through the destructured 9-conjunct bundle; the block floor `hNfloor`
enters ONLY as the argument that produces that bundle.  So we factor a shared core
`medium_box_price_core` that takes the bundle as a PACKED `∃`-hypothesis (literally the
`d0_window_nonempty` / `d0_window_nonempty_lo` conclusion at `N := 2^k`, `M := pieceM k`), and read
off `medium_box_price_at_op_lo` by feeding `d0_window_nonempty_lo`.  The `x^{11/24}/8 ≤ D` row
`hDge_x` STAYS at `11/24` (it consumes `hd_xscale`, the bundle's `x`-scale conjunct, which
`d0_window_nonempty_lo` keeps at `x^{11/24}/8`) — so everything below the bundle is verbatim
PriceOne. -/

/-- **`medium_box_price_core` (deliverable 2, shared core).**  PriceOne's summit
`medium_box_price_at_op` with the block-floor hypothesis REPLACED by the packed `D0`-window bundle
(the exact `d0_window_nonempty` conclusion at `N := 2^k`, `M := pieceM k`).  Both floors instantiate
it: the landed `x^{11/24}/8` floor via `d0_window_nonempty`, the Finding-3 strip floor `x^{7/16}/8`
via `d0_window_nonempty_lo`.  Everything after the bundle is the verbatim PriceOne assembly (SW
couplings at the minimal shapes, the guarded per-`e` rows via `bridge_scale`, the terminal
`medium_survivor_price_sqrtD` at `A = 13`, `B = 15`, `C0 = 18`, transported to `pieceN k`). -/
theorem medium_box_price_core :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x : ℕ) (Lb : ℝ) (F Krange k i : ℕ) (α : ℕ → ℂ) (X T D : ℕ)
        (Dset : Finset ℕ) (r : ℕ → ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (2 ^ k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
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
        -- the `D0`-window bundle: the verbatim `d0_window_nonempty(_lo)` conclusion at `N := 2^k`
        (∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
            ∧ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
            ∧ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
            ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((18 : ℝ))
            ∧ (D0 : ℝ) ≤ (Real.log ((2 ^ k : ℕ) : ℝ)) ^ ((18 : ℝ))
            ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
            ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
            ∧ D0 ≤ 2 ^ k) →
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
  obtain ⟨K, N₀, hK0, hbody⟩ := medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num)
    (by norm_num)
  refine ⟨K, N₀, hK0, fun x Lb F Krange k i α X T D Dset r hk hx hi hXsub hα hd1 hcop2
    hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor hDXM hD0win => ?_⟩
  -- abbreviations
  set M : ℕ := pieceM k with hMdef
  set L : ℝ := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set logN : ℝ := Real.log ((2 ^ k : ℕ) : ℝ) with hlogNdef
  have hk1 : 1 ≤ k := by omega
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hlogNpos : (0 : ℝ) < logN := by
    rw [hlogNdef]
    refine Real.log_pos ?_
    have : (1 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 ^ k)
    exact this
  have hM2 : 2 ≤ M := by rw [hMdef]; exact two_le_pieceM hk1
  -- the `D0`-window bundle (supplied by the caller)
  obtain ⟨D0, k0, hd_eq, hd_2D0, hd_main, hd_D0lo, hd_hD0, hd_hD0N', hd_conj7, hd_xscale,
    hd_hD0N⟩ := hD0win
  -- SW couplings (minimal choices), with `Kβ := Kbeta_min` etc.
  have hcoupG : K * L ^ ((13 : ℝ) + 18) ≤ Kbeta_min K L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) :=
    Kbeta_min_coupling hlogNpos
  have hcoup3 : K * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min K L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := Km_min_coupling hlogNpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min K L logN 13 18 * logN ^ ((13 : ℝ) + 1 + 2 * 18) :=
    fun e _ _ => Kbeta'_min_coupling hK0.le hlogNpos (log_efold_nonneg X M e)
      (log_efold_le X M e) (by norm_num)
  -- guarded per-`e` rows (catch #69 repair)
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      L ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) := by
    intro e he2 heD heX
    have h := herr_scale e he2 heD heX
    linarith [hL2]
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  -- `D0`-window rows re-shaped to the terminal's `A = 13` exponents
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_xscale hDge_x)
  have hD0lo_main : L ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : L ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_D0lo
  -- nonnegativity of the minimal SW constants
  have hKβnn : 0 ≤ Kbeta_min K L logN 13 18 := Kbeta_min_nonneg hK0.le hLnn hlogNpos.le
  have hKmnn : 0 ≤ Km_min K L logN 13 18 := Km_min_nonneg hK0.le hLnn hlogNpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min K L logN 13 18 := Kbeta'_min_nonneg hK0.le hLnn hlogNpos.le
  -- transport `blockPrimeInd (pieceN k)` ⇒ `blockPrimeInd (2^k)` and apply the terminal
  rw [sum_norm_apDiscBilinCutoff_pieceN hk]
  exact hbody (x : ℝ) Lb F α X (2 ^ k) M T D0 D k0 (Nat.log 2 D) Dset r
    (Kbeta_min K L logN 13 18) (Km_min K L logN 13 18) (Kbeta'_min K L logN 13 18) 15
    hα hKβnn hKmnn hKβ'nn hN₀ (pieceM_le_two_pow k) hd_hD0N hd1 hcop2 hL1 hd_hD0 hd_hD0N'
    (by exact_mod_cast two_pow_le_pieceM k) hD1 hDsetD hDsq habs hX2 hM2 (by norm_num) (by norm_num)
    hd_eq hd_2D0
    hD0D rfl hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor
    herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4

/-- **`medium_box_price_at_op_lo` (deliverable 2, the strip extension).**  PriceOne's
`medium_box_price_at_op`, restated with the block-floor hypothesis at the Finding-3 strip bottom
`x^{7/16}/8 ≤ 2^k` (was `x^{11/24}/8`).  Read off `medium_box_price_core` by feeding
`d0_window_nonempty_lo`; the `x^{11/24}/8 ≤ D` level row `hDge_x` is UNCHANGED (it consumes the
bundle's `x`-scale conjunct, kept at `x^{11/24}/8`).  Conclusion character-for-character identical
to PriceOne's. -/
theorem medium_box_price_at_op_lo :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x : ℕ) (Lb : ℝ) (F Krange k i : ℕ) (α : ℕ → ℂ) (X T D : ℕ)
        (Dset : Finset ℕ) (r : ℕ → ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (2 ^ k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
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
  exact hcore x Lb F Krange k i α X T D Dset r hk hx hi hXsub hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1
    hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM
    (d0_window_nonempty_lo hx (pieceM_le_two_pow k) hNfloor hi hXsub)

/-! ## 2b. The `_lo` satisfiability witnesses (deliverable 4a, anti-#69 discipline)

Catch #69 was an intrinsically FALSE hypothesis; the anti-#69 discipline requires positively
witnessing that a new lemma's hypotheses are jointly satisfiable at the intended shape.  For
deliverable 1 the intended shape is a STRIP `N` — one BELOW `d0_window_nonempty`'s floor
`x^{11/24}/8` but above the strip bottom `x^{7/16}/8`, exactly where the original lemma canNOT be
applied.  Three witnesses:

* the strip has positive width below the old floor (`x^{7/16}/8 < x^{11/24}/8` at the tower);
* the box hypothesis `i ∈ dyadicBoundary …` is inhabited at a concrete piece shape (PriceOne's
  witness, re-checked here);
* `d0_window_nonempty_lo` FIRES at a strip-shaped `N` (pinned strictly below `x^{11/24}/8`),
  producing an inhabited `D0`-window — the positive witness that deliverable 1 covers new ground. -/

/-- Anti-#69 (strip non-degeneracy): the Finding-3 strip `[x^{7/16}/8, x^{11/24}/8)` sits strictly
BELOW `d0_window_nonempty`'s floor and has positive width at the tower (`x ≥ exp(10^9) > 1`). -/
example {x : ℕ} (hx : Real.exp (10 ^ 9) ≤ (x : ℝ)) :
    (x : ℝ) ^ ((7 : ℝ) / 16) / 8 < (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    have h2 : (0 : ℝ) ≤ (10 : ℝ) ^ 9 := by positivity
    linarith
  have hmono : (x : ℝ) ^ ((7 : ℝ) / 16) < (x : ℝ) ^ ((11 : ℝ) / 24) :=
    Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)
  linarith

/-- Anti-#69 (box inhabitation, PriceOne's witness): the `dyadicBoundary` survivor set of the box
hypothesis is NONEMPTY at the concrete piece shape `k = 2`, `x = 16` (`i = 1` survives). -/
example : 1 ∈ dyadicBoundary (2 ^ 2) (pieceM 2) (16 / 2 + 1) 16 1 5 := by decide

/-- Anti-#69 (the `_lo` D0 witness FIRES at a strip-shaped `N`): pin `N` strictly below the OLD
floor `x^{11/24}/8` (so `d0_window_nonempty` is inapplicable) yet above the strip bottom
`x^{7/16}/8`; `d0_window_nonempty_lo` still produces an inhabited `D0`-window (`2 ≤ D0` and
`D0 ≤ x^{11/24}/8`).  Positive witness that deliverable 1 prices the strip the original lemma
cannot. -/
example {x N M K i X F : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hM2N : M ≤ 2 * N)
    (hstrip_lo : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (N : ℝ))
    (_hstrip_hi : (N : ℝ) < (x : ℝ) ^ ((11 : ℝ) / 24) / 8)
    (hi : i ∈ dyadicBoundary N M (x / 2 + 1) x F K)
    (hXsub : X = 2 ^ (i + 1) - 1) :
    ∃ D0 : ℕ, 2 ≤ D0 ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
  obtain ⟨D0, k0, hd_eq, hd_2D0, -, -, -, -, -, hd_xscale, -⟩ :=
    d0_window_nonempty_lo hx hM2N hstrip_lo hi hXsub
  exact ⟨D0, hd_2D0, hd_xscale⟩

/-! ## 3. The band price variants (deliverable 3)

The analogues of `medium_box_price_at_op` at the two band carriers, stated to slot into the
`PsymK`/`PlowK` price inputs of `PloW_sym_of_box_disc`/`PloW_low_of_box_disc`
(`SwitchW2`, the `hpriceSym`/`hpriceLow` slots, lines 916–935) character-for-character.

Both are the DIRECT `box_disc_three_way` (`MediumFloor`) at the band carrier — the exact design of
the landed medium W box price `SwitchW2.hNum_at_opW`, whose `hprice` slot is likewise TWO per-box
`medium_survivor_price_sqrtD` applications (`T = x`, `T = x/2+1`) at the reduced top `2^{i+1}−1`.
The three `box_disc_three_way` obligations:

* the m-side support FLOOR `hsupp`:
  - sym: `blockAlphaSym_support_floor` — the SHARP `z·max(y, pieceN k) < m` (the sym band's large
    prime satisfies `p₂ > max y N`);
  - low: `medium_support_floor_low` — `z·y < m` through the `restrictAlpha` band window.
* `hDsq` at the sym carrier is automatic via `hDsq_at_sym_carrier` — but it lives INSIDE the per-box
  price (the `hprice` hypothesis), discharged by `medium_box_price_at_op_lo` (§2, the `_lo` witness,
  since the band boxes' `N = pieceN k` reaches down to the strip) with `hDsq` supplied by
  `hDsq_at_sym_carrier`;
* the per-box `hprice` (the reduced-top single-`T` sums, `≤ 3` boxes) and `hiX` enter as named
  hypotheses — exactly as `hNum_at_opW` takes them — because the numeric `Price` values are the
  operating-point closure PRICE-3 supplies.

The `PsymK`/`PlowK` slot the caller sees is `∑ i ∈ boundary, Price i` (a `≤ 3`-term sum by
`dyadicBoundary_card_le_three`).  The `Dset := ((divisors Ps).filter (·<bound)).image (Q · ·)` and
`r := fun m => crtClassW Q (m/Q) a` are quoted verbatim from the feeders. -/

open Classical in
/-- **`sym_box_price_at_op` (deliverable 3, the sym band).**  The `box_disc_three_way` box price at
the symmetric band carrier `blockAlphaSym z y ε₀ j (pieceN k) (pieceM k)`, floor
`z·max(y, pieceN k)` (SHARP, `blockAlphaSym_support_floor`).  Conclusion character-for-character the
`hdiffK`/`hpriceSym` input of `PloW_sym_of_box_disc` (`SwitchW2`, the T-difference over the
`Q`-shifted image family at `blockPrimeInd (max y (pieceN k))`).  The per-box `hprice` — TWO
`medium_box_price_at_op(_lo)` applications at the reduced top `2^{i+1}−1` — is a named hypothesis
(PRICE-3 supplies the numeric `Price`). -/
theorem sym_box_price_at_op {x z y : ℕ} {ε₀ : ℝ} {j k X Q a : ℕ} (Ps : ℕ) (bound : ℝ) (K : ℕ)
    (Price : ℕ → ℝ)
    (hxlo : x / 2 + 1 ≤ x)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
        (z * max y (pieceN k)) K, 2 ^ (i + 1) ≤ X + 1)
    -- the per-box `hprice` slot: the reduced-top (`X_sub = 2^{i+1}−1`) single-`T` sums over the
    -- `Q`-shifted image family, at `T = x` and `T = x/2+1` (TWO `medium_box_price_at_op(_lo)`).
    (hprice : ∀ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
        (z * max y (pieceN k)) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1)
                (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1)
                  (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price i) :
    -- the `hpriceSym` slot of `PloW_sym_of_box_disc` (verbatim):
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
          - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
      ≤ ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
          (z * max y (pieceN k)) K, Price i := by
  classical
  exact box_disc_three_way K hK hxlo (fun m hm => blockAlphaSym_support_floor hm)
    (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d))
    (fun m => crtClassW Q (m / Q) a) Price hiX hprice

open Classical in
/-- **`low_box_price_at_op` (deliverable 3, the low band).**  The `box_disc_three_way` box price at
the low band carrier `restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k)) (min (z·pieceN k+1) (x+1))
(x+1)`, floor `z·y` (`medium_support_floor_low`).  Conclusion character-for-character the
`hdiffK`/`hpriceLow` input of `PloW_low_of_box_disc` at `blockPrimeInd (pieceN k)`. -/
theorem low_box_price_at_op {x z y : ℕ} {ε₀ : ℝ} {j k X Q a : ℕ} (Ps : ℕ) (bound : ℝ) (K : ℕ)
    (Price : ℕ → ℝ)
    (hxlo : x / 2 + 1 ≤ x)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                    (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price i) :
    -- the `hpriceLow` slot of `PloW_low_of_box_disc` (verbatim):
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
              (min (z * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
          - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
              (min (z * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
      ≤ ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price i := by
  classical
  exact box_disc_three_way K hK hxlo (fun m hm => medium_support_floor_low hm)
    (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d))
    (fun m => crtClassW Q (m / Q) a) Price hiX hprice

/-! ## 4. The band-price → feeder composition (deliverable 4b)

`sym_box_price_at_op`'s conclusion slots into `PloW_sym_of_box_disc`'s `hdiffK` input verbatim:
setting `PsymK k := ∑ i ∈ boundary, Price k i`, the per-`k` sym box prices compose to the feeder's
`bandSymRectDiscW`-sum bound.  The `example` below is that composition — the anti-#69 slot-match
witness. -/

open Classical in
/-- Anti-#69 (band-price → feeder slot match): the per-`k` `sym_box_price_at_op` conclusions are
EXACTLY the `hdiffK` input `PloW_sym_of_box_disc` consumes (`SwitchW2`).  Feeding them yields the
feeder's `bandSymRectDiscW`-sum bound — witnessing the character-for-character slot match. -/
example {x z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ) (K : ℕ) (Price : ℕ → ℕ → ℝ)
    (hQ1 : 1 ≤ Q) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hsym : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
              (z * max y (pieceN k)) K, Price k i) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k)
          (x / 2 + 1) x (z * max y (pieceN k)) K, Price k i :=
  PloW_sym_of_box_disc Ps bound
    (fun k => ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
      (z * max y (pieceN k)) K, Price k i) hQ1 hxX hxlo hsym

end Salt.Chen
