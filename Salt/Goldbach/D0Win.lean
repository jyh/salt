/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BoxRows
import Salt.Goldbach.Price

/-!
# G-D0WIN — the annulus-native D0-window + live-box floor (Goldbach keystone repair)

Design: G-BOXROWS's flag (the factor-8-vs-factor-8 collision).  The twin's
`Salt.Chen.d0_window_of_XM` (PriceOne) builds the 9-conjunct `D0`-window from the RAW pair
`hXMlo : x/2 + 1 < X·M`, `hXMhi : X·M ≤ 4·x` — a factor-8 window `(x/2, 4x]`.  The Goldbach
annulus box lives in `X·M ∈ (goldCut Ne k, 8·goldCut Ne k]` (also factor-8), so NO phantom `x`
satisfies both strict bounds (`hXMhi` forces `x ≥ 2·goldCut Ne k`, `hXMlo` forces
`x < 2·goldCut Ne k`; the T₁ clause `goldCut Ne k < X·M` is one unit short of `x/2 + 1 < X·M`
at `x = 2·goldCut Ne k`).  Worse, keying `x := X·M` (which DOES clear both) would demand the
`11/24` block floor `(X·M)^{11/24}/8 ≤ Nb`, which the live boxes (7/16 floor) fail.

The repair re-walks the twin's derivation ANNULUS-NATIVELY, keyed to the D0-window's own scale
`x := goldCut Ne (k+1)` and the LIVE floor exponent `7/16` (not `11/24`):

* the collision dissolves because the re-derivation needs only the NON-strict half-bound
  `x/2 + 1 ≤ X·M` (twin's `hL_lo` uses `≤`, not the strict `<`), which
  `goldCut_succ_le_two_mul` supplies at `x := goldCut Ne (k+1)` from `goldCut Ne k < X·M`
  (`x/2 ≤ goldCut Ne k < X·M`) — the off-by-one never touches the log bound;
* the floor exponent drops `11/24 → 7/16`: the construction's only exponent constraint is
  `12/5·c > 1` (the `hLW` ratio), and `7/16 = 0.4375 > 5/12 = 0.41667`, so `7/16` closes with
  margin `12/5` — exactly the floor the live-box adjudication (`gold_kfloor_live_annulus`)
  supplies.  Every constant that changes vs the twin is called out in the file report.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* §1 **`gold_d0_window_annulus`** — the 9-conjunct `D0`-window from the annulus-native bounds
  `goldCut Ne k < X·M ≤ 4·goldCut Ne (k+1)`, scale `goldCut Ne (k+1)`, floor exponent `7/16`.
  Conclusion character-for-character `d0_window_of_XM`'s (block `Nb` abstract), so it slots into
  `gold_box_price_engine`'s `hD0*` rows verbatim.
* §2 **`gold_kfloor_live_annulus`** — the per-annulus live-box floor
  `(goldCut Ne (k+1))^{7/16}/8 ≤ 2^{k'}`, the `kfloor_of_live_box` analogue at the annulus scale
  (dead pairs → the landed `gold_box_price_vanish`; the dichotomy is stated for BoxRows2).
* §3 **`gold_box_price_engine_at_live_annulus`** — the composition: `gold_box_price_engine`'s D0
  rows discharged from §1 (fed the §2 floor) at a live annulus (the shape-lock).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. `gold_d0_window_annulus` — the annulus-native D0-window (deliverable 1) -/

/-- **`gold_d0_window_annulus` (§1, the crux).**  The `D0`-window `d0_window_of_XM` re-derived
from the annulus-native scale facts `goldCut Ne k < X·M` and `X·M ≤ 4·goldCut Ne (k+1)`, at the
D0-window scale `x := goldCut Ne (k+1)`, block floor `x^{7/16}/8 ≤ Nb` (the 7/16 live floor).
The 9-conjunct conclusion is character-for-character `d0_window_of_XM`'s with `x := goldCut Ne
(k+1)`, `N := Nb`, `11/24 ↦ 7/16` — so it feeds `gold_box_price_engine`'s `hD0*` rows verbatim.
The factor-8 collision never bites: `hL_lo` uses the NON-strict `x/2 + 1 ≤ X·M`, which
`goldCut_succ_le_two_mul` delivers (`x/2 ≤ goldCut Ne k < X·M`). -/
theorem gold_d0_window_annulus {Ne Nb M X k : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (goldCut Ne (k + 1) : ℝ))
    (hNfloor : (goldCut Ne (k + 1) : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (Nb : ℝ))
    (hXMlo : goldCut Ne k < X * M)
    (hXMhi : X * M ≤ 4 * goldCut Ne (k + 1)) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log (Nb : ℝ)) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (goldCut Ne (k + 1) : ℝ) ^ ((7 : ℝ) / 16) / 8
      ∧ D0 ≤ Nb := by
  -- the half-bound `x/2 + 1 ≤ X·M` from `goldCut_succ_le_two_mul` (dissolves the off-by-one).
  have hle := goldCut_succ_le_two_mul Ne k
  have h2 : goldCut Ne (k + 1) / 2 + 1 ≤ X * M := by omega
  set x := goldCut Ne (k + 1) with hxdef
  -- ① scale facts: `t ≥ 10^9`, `x ≥ 2`.
  have h109 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
  have ht : (10 : ℝ) ^ 9 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- ② the scale facts (annulus-native): `x/2 < X·M ≤ 4x` — `hXMhi` verbatim, `hXMlo` via `h2`.
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
  -- ④ the block-floor log: `W := (7/16)·t − 7 ≤ log Nb` (was `11/24` in the twin).
  set W : ℝ := 7 / 16 * Real.log x - 7 with hWdef
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
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}` (the anti-#64 margin).
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
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W ≤ x^{7/16}/8`.
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
  · -- `hD0N'` (`D0 ≤ (log Nb)^{C0}`, `C0 = 18`)
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
  · -- the `x`-scale bound (`D0 ≤ x^{7/16}/8`)
    linarith [hD0_hi, hW18, hexpW, hexp_le]
  · -- `hD0N` (`D0 ≤ Nb`)
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (Nb : ℝ) := by
      linarith [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-! ## 2. `gold_kfloor_live_annulus` — the per-annulus live-box floor (deliverable 2)

The `kfloor_of_live_box` analogue at the outer-dyadic axis.  For a box `i` in the annulus
boundary whose carrier is LIVE (`2^i < z·pieceN k' + 1`), the annulus cutoff clause
`goldCut Ne k < (2^{i+1}−1)·pieceM k'` forces `goldCut Ne k < 4·2^{i+k'}`, hence — via
`goldCut_succ_le_two_mul` — `goldCut Ne (k+1) < 8·2^{i+k'}`.  This is the twin's `x/8 < 2^i·2^k`
at `x := goldCut Ne (k+1)` (the `x/2` of the top-block twin is here the FULL `goldCut Ne k`,
absorbing the factor 2).  From there the twin's algebra is verbatim (`x → goldCut Ne (k+1)`,
`k → k'`), yielding `(goldCut Ne (k+1))^{7/16}/8 ≤ 2^{k'}`.

The live/dead dichotomy for BoxRows2: a box `i` is DEAD when `min (z·pieceN k' + 1) (Ne/2 + 1)
≤ 2^i` (empty carrier → `gold_box_price_vanish`, BoxRows §2), LIVE when `2^i < min (…)`, in
particular `2^i < z·pieceN k' + 1` — the `hlive` hypothesis below.  So BoxRows2 case-splits on
`min (z·pieceN k' + 1) (Ne/2 + 1) ≤ 2^i` vs its negation: the former discharges via the vanish
lemma, the latter feeds this floor.  The operating `z`-bound
`hz : z ≤ (goldCut Ne (k+1))^{1/8}` is the annulus-local form BoxRows2 supplies. -/

/-- **`gold_kfloor_live_annulus` (§2).**  For a LIVE box (`hlive : 2^i < z·pieceN k' + 1`) in the
annulus boundary, at the local operating scale `hz : (z : ℝ) ≤ (goldCut Ne (k+1))^{1/8}`:
`(goldCut Ne (k+1))^{7/16}/8 ≤ 2^{k'}`.  The `kfloor_of_live_box` mirror; the annulus cutoff
`goldCut Ne k < X·M` (`gold_box_XM_scale`) plus `goldCut_succ_le_two_mul` supplies the twin's
`x/8 < 2^i·2^{k'}` at `x := goldCut Ne (k+1)`.  Margin `2√2 < 8`, exactly the twin's. -/
theorem gold_kfloor_live_annulus {Ne z y k' k i K : ℕ} (hNe : 2 ≤ Ne)
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut Ne k) (goldCut Ne (k + 1))
      (z * y) K)
    (hlive : 2 ^ i < z * pieceN k' + 1)
    (hz : (z : ℝ) ≤ (goldCut Ne (k + 1) : ℝ) ^ ((1 : ℝ) / 8)) :
    (goldCut Ne (k + 1) : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k' : ℕ) : ℝ) := by
  -- annulus cutoff + pieceM bound: `goldCut Ne k < 4·(2^i·2^{k'})`.
  have hcut := (gold_box_XM_scale hi).1
  have hMub : pieceM k' ≤ 2 * 2 ^ k' := pieceM_le_two_pow k'
  have hXMub : (2 ^ (i + 1) - 1) * pieceM k' ≤ 4 * (2 ^ i * 2 ^ k') := by
    calc (2 ^ (i + 1) - 1) * pieceM k'
        ≤ 2 ^ (i + 1) * (2 * 2 ^ k') := Nat.mul_le_mul (Nat.sub_le _ _) hMub
      _ = 4 * (2 ^ i * 2 ^ k') := by rw [pow_succ]; ring
  have hGcut : goldCut Ne k < 4 * (2 ^ i * 2 ^ k') := lt_of_lt_of_le hcut hXMub
  have hle := goldCut_succ_le_two_mul Ne k
  -- `x := goldCut Ne (k+1) < 8·(2^i·2^{k'})`, i.e. `x/8 < 2^i·2^{k'}`.
  have hxN : goldCut Ne (k + 1) < 8 * (2 ^ i * 2 ^ k') := by omega
  have hxpos : (0 : ℝ) < (goldCut Ne (k + 1) : ℝ) := by
    have h1 : (1 : ℕ) ≤ goldCut Ne (k + 1) := one_le_goldCut hNe (k + 1)
    exact_mod_cast (by omega : (0 : ℕ) < goldCut Ne (k + 1))
  set x := goldCut Ne (k + 1) with hxdef
  -- carrier-live gives `2^i ≤ z·2^{k'}` (Nat).
  have hliveN : 2 ^ i ≤ z * 2 ^ k' := by
    have hN : pieceN k' = 2 ^ k' - 1 := rfl
    rw [hN] at hlive
    calc 2 ^ i ≤ z * (2 ^ k' - 1) := by omega
      _ ≤ z * 2 ^ k' := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  -- real forms.
  have hxR : (x : ℝ) < 8 * ((2 : ℝ) ^ i * (2 : ℝ) ^ k') := by exact_mod_cast hxN
  have hliveR : (2 : ℝ) ^ i ≤ (z : ℝ) * (2 : ℝ) ^ k' := by exact_mod_cast hliveN
  have hknn : (0 : ℝ) ≤ (2 : ℝ) ^ k' := by positivity
  have hcutR : (x : ℝ) / 8 < (2 : ℝ) ^ i * (2 : ℝ) ^ k' := by linarith [hxR]
  have hProd : (x : ℝ) / 8 < (z : ℝ) * ((2 : ℝ) ^ k' * (2 : ℝ) ^ k') := by
    nlinarith [hcutR, mul_le_mul_of_nonneg_right hliveR hknn]
  have hProd2 : (x : ℝ) / 8 < (x : ℝ) ^ ((1 : ℝ) / 8) * ((2 : ℝ) ^ k' * (2 : ℝ) ^ k') := by
    have hk2nn : (0 : ℝ) ≤ (2 : ℝ) ^ k' * (2 : ℝ) ^ k' := by positivity
    nlinarith [hProd, mul_le_mul_of_nonneg_right hz hk2nn]
  have hx18pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hxpos _
  have hxeq : (x : ℝ) = (x : ℝ) ^ ((7 : ℝ) / 8) * (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hxpos, show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]
  have hsub : (x : ℝ) / 8 = (x : ℝ) ^ ((7 : ℝ) / 8) / 8 * (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [div_mul_eq_mul_div, ← hxeq]
  have hPsq : (x : ℝ) ^ ((7 : ℝ) / 8) / 8 < (2 : ℝ) ^ k' * (2 : ℝ) ^ k' := by
    rw [hsub, mul_comm ((x : ℝ) ^ ((1 : ℝ) / 8)) ((2 : ℝ) ^ k' * (2 : ℝ) ^ k')] at hProd2
    exact lt_of_mul_lt_mul_right hProd2 hx18pos.le
  have hxx : (x : ℝ) ^ ((7 : ℝ) / 16) * (x : ℝ) ^ ((7 : ℝ) / 16) = (x : ℝ) ^ ((7 : ℝ) / 8) := by
    rw [← Real.rpow_add hxpos]; congr 1; norm_num
  have hann : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) := Real.rpow_nonneg hxpos.le _
  have h78nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 8) := Real.rpow_nonneg hxpos.le _
  rw [show ((2 ^ k' : ℕ) : ℝ) = (2 : ℝ) ^ k' by push_cast; ring]
  nlinarith [hPsq, hxx, hann, hknn, h78nn,
    show (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 + (2 : ℝ) ^ k' by positivity]

/-! ## 3. The composition — `gold_box_price_engine`'s D0 rows from the two keystones (deliverable 3)

The shape-lock: `gold_box_price_engine`'s NINE `hD0*` rows (`hD0N`/`hD0`/`hD0N'`/`hD0eq`/`h2D0`/
`hD0D`/`hD0lo_main`/`herr_D0lo`/`herr_D0E`) are discharged, at a LIVE annulus box
(`X = 2^{i+1}−1`, `M = pieceM kp`, annulus index `ka`, piece index `kp`), by:

* `gold_kfloor_live_annulus` → the 7/16 floor `(goldCut Ne (ka+1))^{7/16}/8 ≤ 2^{kp}`;
* fed to `gold_d0_window_annulus` (via `gold_box_XM_scale`'s annulus bounds) → the 9 conjuncts;
* the exponent bridges `13+2 = 15`, `13+4 = 17` (verbatim the twin's `medium_box_price_at_op`
  re-shaping), `hD0D` off conjunct-8 + the `D`-floor, `herr_D0E` off conjunct-7 + `herr_scale`.

The remaining ~30 x-generic engine rows enter as named hypotheses (BoxRows2 supplies them from the
geometry).  A compiling application of `gold_box_price_engine` is the evidence the shapes match. -/

/-- **`gold_box_price_engine_at_live_annulus` (§3).**  `gold_box_price_engine` re-exported with its
nine `hD0*` rows discharged from `gold_d0_window_annulus` (fed the `gold_kfloor_live_annulus`
7/16 floor) at a live annulus box (`X = 2^{i+1}−1`, `M = pieceM kp`).  Every D0-row slot typechecks
against the keystone output — the compile-time proof the annulus-native variant fits the engine. -/
theorem gold_box_price_engine_at_live_annulus :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ Ne z y K ka i : ℕ),
        2 ≤ Ne →
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
        2 ^ i < z * pieceN kp + 1 →
        (z : ℝ) ≤ (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 8) →
        Real.exp (10 ^ 9) ≤ (goldCut Ne (ka + 1) : ℝ) →
        X = 2 ^ (i + 1) - 1 → M = pieceM kp →
        (goldCut Ne (ka + 1) : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ (D : ℝ) →
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
  intro x Lb F β X M kp D Dset r Kβ Km Kβ' T₁ T₂ Ne z y K ka i hNe hi hlive hz hx hXeq hMeq
    hDge hk hβ hKβ hKm hKβ' hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt
    hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3
    herr_book4
  -- the two keystones: the 7/16 live floor, feeding the annulus D0-window.
  have hfloorN := gold_kfloor_live_annulus hNe hi hlive hz
  have hsc := gold_box_XM_scale hi
  rw [← hXeq, ← hMeq] at hsc
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_annulus (Ne := Ne) (Nb := 2 ^ kp) (M := M) (X := X) (k := ka)
      hx hfloorN hsc.1 hsc.2
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

end Salt.Goldbach
