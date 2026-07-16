/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.GeoSum2
import Salt.Goldbach.BandPrice

/-!
# G-BANDWIN — the liveness-FREE band price chain (Goldbach A₃ band leg, sprint Q1, node 1)

Design: the G-SURV re-scope (ledger ~12:15).  The band survivors are HIGH-PASS
(`m > z·pieceN k'`, spanning `(5/24)·log₂N` scales above the box engine's `hlive` gate), so the
band route is **liveness-free**: it never touches the box's z-dependent live floor
(`gold_kfloor_live_z`, whose `hlive` gate the band survivors fail).  Instead it prices at the
**PIECE FLOOR** `(goldCut Ne (k+1))^{1/3}/8 ≤ 2^{k'}`, exactly the twin's band route
(`Salt.Chen.d0_window_of_XM_band` / `medium_box_price_at_op_band`), transported to the Goldbach
outer-annulus geometry.

This is the Goldbach mirror of the twin's `d0_window_of_XM_band`:

* **`gold_d0_window_band`** (this node) — the 9-conjunct `D0`-window at the band floor, derived from
  the annulus-native bounds `goldCut Ne k < X·M ≤ 4·goldCut Ne (k+1)` (the half-bound via
  `goldCut_succ_le_two_mul`, dissolving the factor-8 off-by-one) with the band-floor exponent `1/3`
  (not the box's `7/16`/`11/24`), `W := (1/3)·log x − 7`, ratio `L ≤ (31/10)·W`, tower
  `exp(10^{10})` (so the binding row `4·(31/10)^{17} ≤ W` closes, margin ≈ 3.7×), and the `x`-scale
  floor conjunct kept at `x^{11/24}/8` via the bump `x^{1/3} ≤ x^{11/24}` — character-for-character
  the twin's `d0_window_of_XM_band` at `x := goldCut Ne (k+1)`, `N := Nb`.

  | quantity                                     | value at `t = log x = 10^{10}`      |
  |----------------------------------------------|-------------------------------------|
  | `W = (1/3)·10^{10} − 7`                       | `≈ 3.333·10⁹`                       |
  | ratio bound used: `L ≤ (31/10)·W`            | `31/10 = 3.1 > 3 = lim L/W`         |
  | binding requirement `4·(31/10)^{17} ≤ W`     | `4·(31/10)^{17} ≈ 9.02·10⁸`         |
  | **room** `W / (4·(31/10)^{17})`              | **`≈ 3.7×`**                        |

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. `gold_d0_window_band` — the band-floor D0-window (node 1) -/

/-- **`gold_d0_window_band`.**  `gold_d0_window_annulus` re-run at the band floor: the block floor
at the band bottom `(goldCut Ne (k+1))^{1/3}/8 ≤ Nb` (exponent `1/3`, not `7/16`),
`W := (1/3)·log x − 7`, tower `exp(10^{10})` (so `4·(31/10)^{17} ≤ W`), ratio `L ≤ (31/10)·W`, and
the `x`-scale floor conjunct kept at `x^{11/24}/8` (the bump `x^{1/3} ≤ x^{11/24}`).  Conclusion
character-for-character `gold_d0_window_annulus`'s (so it feeds `gold_box_price_engine`'s `hD0*`
rows verbatim), with the floor conjunct at `x^{11/24}/8` instead of `x^{7/16}/8`.  The factor-8
collision never bites: `hL_lo` uses the NON-strict `x/2 + 1 ≤ X·M`, from
`goldCut_succ_le_two_mul`. -/
theorem gold_d0_window_band {Ne Nb M X k : ℕ}
    (hx : Real.exp (10 ^ 10) ≤ (goldCut Ne (k + 1) : ℝ))
    (hNfloor : (goldCut Ne (k + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (Nb : ℝ))
    (hXMlo : goldCut Ne k < X * M)
    (hXMhi : X * M ≤ 4 * goldCut Ne (k + 1)) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log (Nb : ℝ)) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (goldCut Ne (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ Nb := by
  -- the half-bound `x/2 + 1 ≤ X·M` from `goldCut_succ_le_two_mul` (dissolves the off-by-one).
  have hle := goldCut_succ_le_two_mul Ne k
  have h2 : goldCut Ne (k + 1) / 2 + 1 ≤ X * M := by omega
  set x := goldCut Ne (k + 1) with hxdef
  -- ① scale facts: `t ≥ 10^{10}`, `x ≥ 2`.
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
  -- ② the scale facts (annulus-native): `x/2 < X·M ≤ 4x`.
  have hXM4x : X * M ≤ 4 * x := hXMhi
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hXM4xR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hXM4x
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  have hL_lo : Real.log x - 1 ≤ L := by
    have h1 : x < (x / 2 + 1) * 2 := by omega
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
  -- ④ the band block-floor log: `W := (1/3)·t − 7 ≤ log Nb` (the band floor).
  set W : ℝ := 1 / 3 * Real.log x - 7 with hWdef
  have hWlogN : W ≤ Real.log Nb := by
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
  · -- `hD0N'` (`D0 ≤ (log Nb)^{C0}`, `C0 = 18`) — the binding band-floor row
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log Nb) ^ ((18 : ℝ)) :=
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
  · -- the `x`-scale bound (`D0 ≤ x^{11/24}/8`) — via the bump `x^{1/3} ≤ x^{11/24}`
    linarith only [hD0_hi, hW18, hexpW, hexp_le, hxbump]
  · -- `hD0N` (`D0 ≤ Nb`) — SHARP off the band floor `x^{1/3}/8 ≤ Nb`
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (Nb : ℝ) := by
      linarith only [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-! ## 2. `gold_box_price_engine_at_band` — the base engine at the band floor (node 2a)

`gold_box_price_engine` (Price, the LIVENESS-FREE base engine) with its nine `hD0*` rows discharged
from `gold_d0_window_band` (fed the band k-floor `(goldCut Ne (ka+1))^{1/3}/8 ≤ 2^{kp}` as a clean
HYPOTHESIS — no `z`, no `hlive`).  The Goldbach mirror of `gold_box_price_engine_at_live_annulus`
with the LIVE machinery removed: the false `hlive`/`hz` are GONE (the band survivors are high-pass,
they fail the box `hlive` gate), replaced by the band-floor hypothesis `hNfloor`; the floor conjunct
`hd_scale : D0 ≤ x^{11/24}/8` meets the engine's `hDge : x^{11/24}/8 ≤ D` (exponent `11/24`, the
twin's band `d0_window_of_XM_band` scale, not the box's `7/16`).  Tower `exp(10^{10})`.  Conclusion
byte-identical to `gold_box_price_engine_at_live_annulus`'s (the two-cutoff
`≤ 2·(bracket·XM/L^{13})` sum). -/
set_option maxHeartbeats 800000 in
-- the base engine (`gold_box_price_engine`) application re-elaborates the ~43-hypothesis
-- rpow-bearing row list; the whnf/defeq checks need headroom above the default budget.
theorem gold_box_price_engine_at_band :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ Ne z y K ka i : ℕ),
        2 ≤ Ne →
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1))
          (z * y) K →
        Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
        (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
        X = 2 ^ (i + 1) - 1 → M = pieceM kp →
        (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        2 ≤ kp →
        (∀ m, ‖β m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ 2 ^ kp →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ kp : ℕ) : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) →
        2 ≤ X → 2 ≤ M →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 18)
            ≤ Kβ * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 2 * 18)
            ≤ Km * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Kc * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
              ≤ Kβ' * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18)) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₁‖)
          ≤ 2 * ((Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
              * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_engine
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β X M kp D Dset r Kβ Km Kβ' T₁ T₂ Ne z y K ka i hNe hi hx hNfloor hXeq hMeq
    hDge hk hβ hKβ hKm hKβ' hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt
    hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3
    herr_book4
  -- the keystone: the band D0-window from `gold_d0_window_band`, at the band floor.
  have hsc := gold_box_XM_scale hi
  rw [← hXeq, ← hMeq] at hsc
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_band (Ne := Ne) (Nb := 2 ^ kp) (M := M) (X := X) (k := ka)
      hx hNfloor hsc.1 hsc.2
  -- the x-generic geometry rows re-derived from the piece parameter.
  have hM2N : M ≤ 2 * 2 ^ kp := by rw [hMeq]; exact pieceM_le_two_pow kp
  have hNM : ((2 ^ kp : ℕ) : ℝ) ≤ (M : ℝ) := by rw [hMeq]; exact_mod_cast two_pow_le_pieceM kp
  -- the D0 rows re-shaped to the engine's exponents / slots.
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_scale hDge)
  have hD0lo_main : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_lo
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  exact hbody x Lb F β X M kp D0 D k0 Dset r Kβ Km Kβ' T₁ T₂ hk hβ hKβ hKm hKβ' hN₀ hM2N hd_N
    hd1 hcop2 hL1 hd_hi hd_N' hNM hD1 hDsetD hDsq habs hX2 hM2 hd_eq hd_2 hD0D hDscale hD0lo_main
    hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM
    herr_scale hcoupG hcoup3 herr_book4

/-! ## 3. `gold_band_box_kerr` — the Kerr-minima collapse onto `boxPriceKerr` (node 2b)

`gold_box_price_engine_at_band` re-exported at the Kerr minima `Kβ := Kbeta_min Kc L logN 13 18` /
`Km := Km_min …` / `Kβ' := Kbeta'_min …` (`L := log((2^{i+1}−1)·pieceM kp)`, `logN := log(2^kp)`):
the three SW-coupling rows are discharged by `gold_box_hcoupG`/`gold_box_hcoup3`/
`gold_box_herr_book4` (BoxRows §1) and the RHS collapses — character-for-character — onto the twin's
closed box price `boxPriceKerr Kc kp i`.  The Goldbach mirror of `gold_box_price_live_kerr` at the
band floor: the LIVE-specific `hlive`/`hz1`/`hz_ratio` are GONE, replaced by the band-floor
`hNfloor` + the `11/24` floor `hDge`.  The remaining analytic scale rows stay parametric (the
composition supplies them from the band geometry). -/
set_option maxHeartbeats 1600000 in
-- the 39-hypothesis engine application re-elaborates the long rpow-bearing row list (incl. the
-- RHS↔`boxPriceKerr` collapse); the whnf/defeq checks need headroom above the default budget.
theorem gold_band_box_kerr : ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
    ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
      (T₁ T₂ Ne z y K ka i : ℕ),
      2 ≤ Ne →
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
      Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
      2 ≤ kp →
      (∀ m, ‖β m‖ ≤ 1) → N₀ ≤ 2 ^ kp →
      (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
      1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
      1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
      (4 * (1 + Real.log D) * (D : ℝ)
          ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)
              / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (13 : ℝ)) →
      2 ≤ 2 ^ (i + 1) - 1 → 2 ≤ pieceM kp →
      ((D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (15 : ℝ)) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 3)
          ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ)) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 3)
          ≤ Real.sqrt (pieceM kp : ℝ)) →
      ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (pieceM kp : ℝ)) →
      F ≤ 2 ^ (i + 1) - 1 →
      ((D : ℝ) ≤ Real.sqrt x) →
      (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) ≤ Lb) →
      (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (F : ℝ)) →
      (∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
          0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) →
      ((D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
      (∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
          Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
            ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) →
      (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
            (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
        + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
        ≤ boxPriceKerr Kc kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_engine_at_band
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β kp D Dset r T₁ T₂ Ne z y K ka i hNe hi hx hNfloor hDge hk hβ hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  set logN : ℝ := Real.log ((2 ^ kp : ℕ) : ℝ) with hlogNdef
  have hlogNpos : 0 < logN := by
    rw [hlogNdef]
    apply Real.log_pos
    have h2 : (4 : ℕ) ≤ 2 ^ kp := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ kp := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast (by omega : (1 : ℕ) < 2 ^ kp)
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hKβnn : 0 ≤ Kbeta_min Kc L logN 13 18 := Kbeta_min_nonneg hKc.le hL0 hlogNpos.le
  have hKmnn : 0 ≤ Km_min Kc L logN 13 18 := Km_min_nonneg hKc.le hL0 hlogNpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min Kc L logN 13 18 := Kbeta'_min_nonneg hKc.le hL0 hlogNpos.le
  have hcoupG : Kc * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := gold_box_hcoupG hlogNpos
  have hcoup3 : Kc * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := gold_box_hcoup3 hlogNpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      Kc * (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)))
            ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 1 + 2 * 18) := fun e _ _ =>
    gold_box_herr_book4 hKc.le hlogNpos (gold_box_efold_nonneg (2 ^ (i + 1) - 1) (pieceM kp) e)
      (gold_box_efold_le (2 ^ (i + 1) - 1) (pieceM kp) e)
  have hmain := hbody x Lb F β (2 ^ (i + 1) - 1) (pieceM kp) kp D Dset r
    (Kbeta_min Kc L logN 13 18) (Km_min Kc L logN 13 18) (Kbeta'_min Kc L logN 13 18)
    T₁ T₂ Ne z y K ka i hNe hi hx hNfloor rfl rfl hDge hk hβ hKβnn hKmnn hKβ'nn hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3 herr_book4
  -- the engine RHS at the Kerr minima IS `boxPriceKerr Kc kp i` (byte-for-byte the closed price)
  exact hmain

/-! ## 4. `gold_band_survsum_geoN` — the outer-scale conversion (node 2c)

The band mirror of `gold_box_hbox_geoN`: the leg-agnostic geo bridge that turns a per-survivor
`boxPriceKerr Kc kp i` bound (from `gold_band_box_kerr` at the band carrier) into the outer-scale
geo grade `Cgeo·Kc·goldCut N (ka+1)/(log N)^{12}` (`Cgeo := cr^{12}·gboxConst`), via the LANDED
`gold_boxPriceKerr_geoN`.  Leg-agnostic: the caller (G-SURV-2) supplies the band-box price `hbox`
(low leg direct, sym leg after the `max (opY N) (pieceN k') = pieceN k'` collapse) and the outer
ratio `hNXM : log N ≤ cr·log(X·M)` (holds on the high annuli the high-pass band survivors populate,
`goldCut(ka+1) ≳ N^{19/24}`; the carrier vanishes on low annuli).  This is the `hgeoSym`/`hgeoLow`
per-survivor grade the terminal `gold_hBVblocksW_at_op_band` consumes. -/
theorem gold_band_survsum_geoN {N K kp ka i : ℕ} {Kc cr P : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (opZ N * opY N) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log ((2 ^ kp : ℕ) : ℝ))
    (hlogN0 : 0 < Real.log N) (hcr : 1 ≤ cr)
    (hNXM : Real.log N ≤ cr * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hbox : P ≤ boxPriceKerr Kc kp i) :
    P ≤ (cr ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 :=
  le_trans hbox (gold_boxPriceKerr_geoN hKc hi hL1 hratio hlogN0 hcr hNXM)

end Salt.Goldbach
