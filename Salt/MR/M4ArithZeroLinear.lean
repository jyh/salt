/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiPrimeLinear

/-!
# ⟦LADDER-L G3 §4⟧ — `M4ArithZero` + `M4ArithPool` + `M4ArithPrime` + `M4SocketFused`
at the LINEAR anchor (`M4ArithZeroLinear`)

⟦COMPOSE-FLAT-2⟧'s ladder re-cut, at the ZERO-DENSITY arithmetic and the JOIN.  The `_L` twin
family of the four pages that price the `gRows` residual at `C_p = 0` and fuse the terminal,
all at `AdoorL M = 2^36·M`.

⟦WHAT THE RE-CUT BUYS HERE, EXACTLY⟧ every gate below is an `M`-LOWER demand read against
`Adoor M = 2^36·(⌊log₂M⌋+1)`; at the linear anchor the same numeral is `2^36·M`.  The gate
statements are byte-identical modulo that substitution — the pricing arithmetic
(`slot_of_log_gate`, `pricing_numerals`, `window_row_eq`) is ladder-BLIND and is replayed
verbatim — but the demand is now LINEAR in `M` where it was logarithmic.  That is the whole
content of ⟦H1-ANCHOR⟧, read at the residual page.

PURELY ADDITIVE: no landed declaration moves.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE LADDER-BLIND WORKHORSES

`M4ArithZero`'s `window_row_eq`, `slot_of_log_gate` and `pricing_numerals` are `private` to
that file and read no door at all; they are re-proved here under `L`-suffixed names so the
pricing below is the landed text verbatim. -/

/-- `M4ArithZero.window_row_eq` (:341), re-proved (the landed lemma is `private`). -/
private lemma window_row_eq_L {Xd H : ℝ} (hXd : 0 < Xd) (hH : 0 < H) :
    Xd * ((2 * Real.exp 1 * Xd / H + 1) * (Real.exp 1 / Xd ^ 2))
      = 2 * Real.exp 1 ^ 2 / H + Real.exp 1 / Xd := by
  field_simp

/-- `M4ArithZero.slot_of_log_gate` (:367), re-proved (the landed lemma is `private`). -/
private lemma slot_of_log_gate_L {v κ L : ℝ} (hv : 0 < v) (hκ : 0 < κ) (hL : 0 < L)
    (h : Real.log v + Real.log L / 500 ≤ Real.log κ) :
    v ≤ κ * L ^ (-(1 : ℝ) / 500) := by
  have hrw : κ * L ^ (-(1 : ℝ) / 500) = Real.exp (Real.log κ - Real.log L / 500) := by
    rw [Real.rpow_def_of_pos hL]
    conv_lhs => rw [← Real.exp_log hκ]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrw]
  conv_lhs => rw [← Real.exp_log hv]
  exact Real.exp_le_exp.mpr (by linarith)

/-- `M4ArithZero.pricing_numerals` (:410), re-proved (the landed lemma is `private`). -/
private lemma pricing_numerals_L :
    Real.log 14400 ≤ 14 * Real.log 2 ∧ Real.log 3 ≤ 2 * Real.log 2 ∧
      Real.log 43200 ≤ 16 * Real.log 2 ∧ Real.log 460800 ≤ 19 * Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 14400)
      (by norm_num : (14400 : ℝ) ≤ 2 ^ (14 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≤ 2 ^ (2 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 43200)
      (by norm_num : (43200 : ℝ) ≤ 2 ^ (16 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 460800)
      (by norm_num : (460800 : ℝ) ≤ 2 ^ (19 : ℕ))
    rw [Real.log_pow] at h; push_cast at h; linarith

/-! ## §1 — THE LINEAR DOOR SCALES THE PRICING READS -/

/-- `M4ArithZero.log_calP_door_one` (:307) at the linear door: `log 𝒫₁ = A_L(M)·log 2`.
(`DoorLinear.s11_log_calP_doorL_one` is the same fact; this is the `_L`-family name.) -/
lemma log_calP_door_one_L (M : ℕ) :
    Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = (AdoorL M : ℝ) * Real.log 2 :=
  s11_log_calP_doorL_one M

/-- `M4ArithZero.calP_door_one_le_two` (:314) at the linear door. -/
lemma calP_door_one_le_two_L {M : ℕ} (hM : 1 ≤ M) :
    calP (AdoorL M) (3072 * M) 1 ≤ calP (AdoorL M) (3072 * M) 2 := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rw [calE_one, calE]
  have h1 : 1 ≤ (3072 * M) ^ (2 - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.factorial 2) ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos 2)
  calc AdoorL M = AdoorL M * 1 * 1 := by ring
    _ ≤ AdoorL M * (3072 * M) ^ (2 - 1) * (Nat.factorial 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

/-- `M4ArithZero.one_div_H1door_eq_a2Level1` (:326) at the linear door — the G6 certificate
read as a quotient at `AdoorL`. -/
lemma one_div_H1doorL_eq_a2Level1_L (M : ℕ) : 1 / H1doorL M = a2Level1_L M := by
  rw [H1doorL, a2Level1_L, one_div_div]

/-! ## §2 — THE RESIDUAL AT `C_p = 0`, PRICED, AT THE LINEAR DOOR -/

/-- **⟦THE EXACT DECOMPOSITION, AT THE LINEAR DOOR⟧** (`a2RowsSum_door_decomp_L`). -/
theorem a2RowsSum_door_decomp_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    a2RowsSum_L M Xd
      = 5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hH2 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hH0 : (0 : ℝ) < H1doorL M := by linarith
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [a2RowsSum_L, hIcc, Finset.sum_insert (by decide), Finset.sum_singleton,
    show calH (H1doorL M) 1 = H1doorL M by rw [calH]; norm_num,
    show calH (H1doorL M) 2 = 4 * H1doorL M by rw [calH]; norm_num,
    window_row_eq_L hXd0 hH0, window_row_eq_L hXd0 (by linarith : (0 : ℝ) < 4 * H1doorL M),
    ← one_div_H1doorL_eq_a2Level1_L]
  ring

/-- **⟦THE ZERO-DENSITY `gRows` GATE, AT THE LINEAR DOOR⟧** (`GRowsZeroGate_L`).  Four fields,
byte-identical to `M4ArithZero.GRowsZeroGate`'s with `Adoor M` replaced by `AdoorL M` — the
demand is now LINEAR in `M`. -/
structure GRowsZeroGate_L (M Xd : ℕ) : Prop where
  /-- `1 ≤ log X_d`. -/
  base : 1 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE LEVEL-1 SLOT⟧ `μ/500 + loglog 𝒬₁/3 + 14 ≤ (log 2/12)·A_L(M)`. -/
  level1 : Real.log (Real.log (Xd : ℝ)) / 500
      + Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) / 3 + 14
    ≤ Real.log 2 / 12 * (AdoorL M : ℝ)
  /-- ⟦THE ENDPOINT SLOT⟧ `μ/500 + 13 ≤ log X_d`. -/
  endpt : Real.log (Real.log (Xd : ℝ)) / 500 + 13 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE `p²` SLOT⟧ `μ·(1 + 1/500) + 15 ≤ (log 2)·A_L(M)`. -/
  p2 : Real.log (Real.log (Xd : ℝ)) * (1 + 1 / 500) + 15 ≤ Real.log 2 * (AdoorL M : ℝ)

/-- **⟦THE RESIDUAL, PRICED, AT THE LINEAR DOOR⟧** (`gRows_zero_of_gate_L`). -/
theorem gRows_zero_of_gate_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate_L M Xd) :
    5760 * (a2RowsSum_L M Xd + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
  obtain ⟨h14400, h3, h43200, h460800⟩ := pricing_numerals_L
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hLX : (1 : ℝ) ≤ Real.log (Xd : ℝ) := hg.base
  have hLX0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) :=
    one_le_log_calQK_door_one_L hM
  have hQ10 : (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP1 : (64 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := calP_door_one_ge_L hM
  have hP10 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hP12 : ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by
    exact_mod_cast calP_door_one_le_two_L hM
  have hP20 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by linarith
  have hlogP1 := log_calP_door_one_L M
  have hlog3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hq3 : (0 : ℝ)
      < (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hQ10 _
  have hp12 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hP10 _
  have ha2pos : (0 : ℝ) < a2Level1_L M := by rw [a2Level1_L]; exact div_pos hq3 hp12
  have hepos : (0 : ℝ) < Real.exp 1 ^ 2 := pow_pos (Real.exp_pos 1) 2
  have hlvl0 : (0 : ℝ) < 14400 * Real.exp 1 ^ 2 * a2Level1_L M :=
    mul_pos (mul_pos (by norm_num) hepos) ha2pos
  have hlvllog : Real.log (14400 * Real.exp 1 ^ 2 * a2Level1_L M)
      = Real.log 14400 + 2
          + (1 : ℝ) / 3 * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
          - (1 : ℝ) / 12 * ((AdoorL M : ℝ) * Real.log 2) := by
    rw [Real.log_mul (by positivity) ha2pos.ne', Real.log_mul (by norm_num) hepos.ne',
      a2Level1_L, Real.log_div hq3.ne' hp12.ne', Real.log_rpow hQ10, Real.log_rpow hP10,
      Real.log_pow, Real.log_exp, hlogP1]
    push_cast
    ring
  have hslot1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine slot_of_log_gate_L hlvl0 (by norm_num) hLX0 ?_
    rw [hlvllog, hlog3]
    have := hg.level1
    linarith
  have hendle : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ) ≤ 43200 / (Xd : ℝ) := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hinv : (0 : ℝ) ≤ 1 / (Xd : ℝ) := (div_pos one_pos hXd0).le
    have hnum : 5760 * (2 * Real.exp 1 + 2) ≤ 43200 := by linarith
    calc 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        = 5760 * (2 * Real.exp 1 + 2) * (1 / (Xd : ℝ)) := by ring
      _ ≤ 43200 * (1 / (Xd : ℝ)) := mul_le_mul_of_nonneg_right hnum hinv
      _ = 43200 / (Xd : ℝ) := by ring
  have hslot2 : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hendle.trans (slot_of_log_gate_L (div_pos (by norm_num) hXd0)
      (by norm_num) hLX0 ?_)
    rw [Real.log_div (by norm_num) hXd0.ne', hlog3]
    have := hg.endpt
    linarith
  have hlogb : Real.logb 2 (2 * (Xd : ℝ)) ≤ 5 / 2 * Real.log (Xd : ℝ) := by
    rw [Real.logb, Real.log_mul (by norm_num) hXd0.ne', div_le_iff₀ hl2]
    nlinarith
  have hinv2 : 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
      + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ 2 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
        ≤ 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hP10 hP12
    have h2 : 2 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        = 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by ring
    linarith
  have hp2le : 92160 * Real.logb 2 (2 * (Xd : ℝ))
        * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 460800 * Real.log (Xd : ℝ) / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hA : (0 : ℝ) ≤ 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) :=
      add_nonneg (div_pos one_pos hP10).le (div_pos one_pos hP20).le
    have hB : (0 : ℝ) ≤ 92160 * (5 / 2 * Real.log (Xd : ℝ)) := by linarith
    have h2 : 92160 * Real.logb 2 (2 * (Xd : ℝ)) ≤ 92160 * (5 / 2 * Real.log (Xd : ℝ)) := by
      linarith
    refine (mul_le_mul h2 hinv2 hA hB).trans (le_of_eq ?_)
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    ring
  have hslot3 : 92160 * Real.logb 2 (2 * (Xd : ℝ))
        * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hp2le.trans (slot_of_log_gate_L
      (div_pos (mul_pos (by norm_num) hLX0) hP10) (by norm_num) hLX0 ?_)
    rw [Real.log_div (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 460800) hLX0)) hP10.ne',
      Real.log_mul (by norm_num) hLX0.ne', hlogP1, hlog3]
    have := hg.p2
    linarith
  rw [a2RowsSum_door_decomp_L hM hXd]
  have hsum : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 92160 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) := by ring
  rw [hsum]
  linarith

/-! ## §3 — ⟦R1⟧ AT THE LINEAR DOOR -/

/-- **⟦THE EXACT DECOMPOSITION — R1, AT THE LINEAR DOOR⟧** (`a2RowsSum'_door_decomp_L`). -/
theorem a2RowsSum'_door_decomp_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    a2RowsSum'_L M Xd
      = 5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hH2 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hH0 : (0 : ℝ) < H1doorL M := by linarith
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [a2RowsSum'_L, hIcc, Finset.sum_insert (by decide), Finset.sum_singleton,
    show calH (H1doorL M) 1 = H1doorL M by rw [calH]; norm_num,
    show calH (H1doorL M) 2 = 4 * H1doorL M by rw [calH]; norm_num,
    window_row_eq_L hXd0 hH0, window_row_eq_L hXd0 (by linarith : (0 : ℝ) < 4 * H1doorL M),
    ← one_div_H1doorL_eq_a2Level1_L]
  ring

/-- **⟦THE ZERO-DENSITY `gRows` GATE — R1, AT THE LINEAR DOOR⟧** (`GRowsZeroGate'_L`). -/
structure GRowsZeroGate'_L (M Xd : ℕ) : Prop where
  /-- `1 ≤ log X_d`. -/
  base : 1 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE LEVEL-1 SLOT⟧ `μ/500 + loglog 𝒬₁/3 + 14 ≤ (log 2/12)·A_L(M)`. -/
  level1 : Real.log (Real.log (Xd : ℝ)) / 500
      + Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) / 3 + 14
    ≤ Real.log 2 / 12 * (AdoorL M : ℝ)
  /-- ⟦THE ENDPOINT SLOT⟧ `μ/500 + 13 ≤ log X_d`. -/
  endpt : Real.log (Real.log (Xd : ℝ)) / 500 + 13 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE `p²` SLOT, R1⟧ `μ/500 + 15 ≤ (log 2)·A_L(M)`. -/
  p2 : Real.log (Real.log (Xd : ℝ)) * (1 / 500) + 15 ≤ Real.log 2 * (AdoorL M : ℝ)

/-- **⟦THE RESIDUAL, PRICED — R1, AT THE LINEAR DOOR⟧** (`gRows_zero_of_gate'_L`). -/
theorem gRows_zero_of_gate'_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'_L M Xd) :
    5760 * (a2RowsSum'_L M Xd + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
  obtain ⟨h14400, h3, h43200, h460800⟩ := pricing_numerals_L
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h276480 : Real.log 276480 ≤ 19 * Real.log 2 :=
    le_trans (Real.log_le_log (by norm_num) (by norm_num : (276480 : ℝ) ≤ 460800)) h460800
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hLX : (1 : ℝ) ≤ Real.log (Xd : ℝ) := hg.base
  have hLX0 : (0 : ℝ) < Real.log (Xd : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) :=
    one_le_log_calQK_door_one_L hM
  have hQ10 : (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP1 : (64 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := calP_door_one_ge_L hM
  have hP10 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hP12 : ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by
    exact_mod_cast calP_door_one_le_two_L hM
  have hP20 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by linarith
  have hlogP1 := log_calP_door_one_L M
  have hlog3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hq3 : (0 : ℝ)
      < (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hQ10 _
  have hp12 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hP10 _
  have ha2pos : (0 : ℝ) < a2Level1_L M := by rw [a2Level1_L]; exact div_pos hq3 hp12
  have hepos : (0 : ℝ) < Real.exp 1 ^ 2 := pow_pos (Real.exp_pos 1) 2
  have hlvl0 : (0 : ℝ) < 14400 * Real.exp 1 ^ 2 * a2Level1_L M :=
    mul_pos (mul_pos (by norm_num) hepos) ha2pos
  have hlvllog : Real.log (14400 * Real.exp 1 ^ 2 * a2Level1_L M)
      = Real.log 14400 + 2
          + (1 : ℝ) / 3 * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
          - (1 : ℝ) / 12 * ((AdoorL M : ℝ) * Real.log 2) := by
    rw [Real.log_mul (by positivity) ha2pos.ne', Real.log_mul (by norm_num) hepos.ne',
      a2Level1_L, Real.log_div hq3.ne' hp12.ne', Real.log_rpow hQ10, Real.log_rpow hP10,
      Real.log_pow, Real.log_exp, hlogP1]
    push_cast
    ring
  have hslot1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine slot_of_log_gate_L hlvl0 (by norm_num) hLX0 ?_
    rw [hlvllog, hlog3]
    have := hg.level1
    linarith
  have hendle : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ) ≤ 43200 / (Xd : ℝ) := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hinv : (0 : ℝ) ≤ 1 / (Xd : ℝ) := (div_pos one_pos hXd0).le
    have hnum : 5760 * (2 * Real.exp 1 + 2) ≤ 43200 := by linarith
    calc 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        = 5760 * (2 * Real.exp 1 + 2) * (1 / (Xd : ℝ)) := by ring
      _ ≤ 43200 * (1 / (Xd : ℝ)) := mul_le_mul_of_nonneg_right hnum hinv
      _ = 43200 / (Xd : ℝ) := by ring
  have hslot2 : 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hendle.trans (slot_of_log_gate_L (div_pos (by norm_num) hXd0)
      (by norm_num) hLX0 ?_)
    rw [Real.log_div (by norm_num) hXd0.ne', hlog3]
    have := hg.endpt
    linarith
  have hinv2 : 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
      + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
      ≤ 2 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
        ≤ 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hP10 hP12
    have h2 : 2 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        = 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
          + 1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by ring
    linarith
  have hp2le : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 276480 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hinv2 (by norm_num : (0 : ℝ) ≤ 138240)
    calc 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
            + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        ≤ 138240 * (2 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) := h
      _ = 276480 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by ring
  have hslot3 : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
    refine hp2le.trans (slot_of_log_gate_L (div_pos (by norm_num) hP10)
      (by norm_num) hLX0 ?_)
    rw [Real.log_div (by norm_num) hP10.ne', hlogP1, hlog3]
    have := hg.p2
    linarith
  rw [a2RowsSum'_door_decomp_L hM hXd]
  have hsum : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) := by ring
  rw [hsum]
  linarith

/-- **⟦`gRows` ON THE WHOLE CAPPED RANGE, FROM ONE INSTANCE, AT THE LINEAR DOOR⟧**
(`gRows_at_socketBase_L`).  `socketBase_base_le_three_x` is door-FREE and applies through
`socketBase_of_socketBaseL`. -/
theorem gRows_at_socketBase_L {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hM : 1 ≤ M) (hb : SocketBaseL R M H L q j A s)
    (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
          + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)))
        ≤ 1 / 2 * Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500))
    (hend : 5760 * ((2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ))
        ≤ 1 / 2 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500)) :
    5760 * (a2RowsSum'_L M (A + s) + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hXdN : 1 ≤ A + s := by omega
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have hpos : 0 < A + s := by omega
    exact_mod_cast hpos
  have hcap : (((A + s : ℕ)) : ℝ) ≤ 3 * (R.x : ℝ) := socketBase_base_le_three_x hbb
  have hmono : Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500)
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (Real.log_le_log hX0 hcap) (by norm_num)
  have hconst : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
            + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)))
      ≤ 1 / 2 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
    refine htop.trans ?_
    linarith
  rw [a2RowsSum'_door_decomp_L hM hXdN]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
            + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
          + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)))
        + 5760 * ((2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ)) := by ring
  rw [hid]
  linarith

/-! ## §4 — THE DENSITY-FREE SOCKET EXITS, AT THE LINEAR DOOR -/

/-- **⟦ITEM 11 AT THE DOOR'S ENVELOPE, `hrows`-FREE, DENSITY-FREE, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorArith_zero_L`). -/
theorem m4_chiSummedFreeRow_of_doorArith_zero_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- **⟦THE SOCKET, DISCHARGED, DENSITY-FREE, AT THE LINEAR DOOR⟧**
(`m4_socket_discharged_conditional_zero_L`). -/
theorem m4_socket_discharged_conditional_zero_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- **⟦THE SOCKET, DISCHARGED, `T₀`-BAND INCLUDED, DENSITY-FREE, AT THE LINEAR DOOR⟧**
(`m4_socket_discharged_bandfree_zero_L`). -/
theorem m4_socket_discharged_bandfree_zero_L (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hcomp⟩ := m4_socket_discharged_conditional_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_L hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-! ## §5 — `M4ArithPool` AT THE LINEAR DOOR -/

/-- **⟦THE GATED SOCKET AT THE POOL AND THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L`). -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_L_nonneg hM (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- **⟦THE ARITHMETIC GATE AT `ρ` AND THE POOL, AT THE LINEAR DOOR⟧**
(`m4_arith_henv_rho_pool_L`). -/
theorem m4_arith_henv_rho_pool_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ π₀ : ℕ → ℝ} {K ρ : ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  fun H L q j A s hb =>
    a2DoorGrade_pool_L_priced_rho (harith H L q j A s hb) (hpool (A + s))
      (hprice H L q j A s hb)

/-- **⟦THE ASSEMBLY, ARITHMETIC INCLUDED, AT THE POOL AND THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorArithRho_pool_L`). -/
theorem m4_chiSummedFreeRow_of_doorArithRho_pool_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {K ρ : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2)
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big_L
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀)
      hpool ?_ (m4_arith_henv_rho_pool_L hpool harith hprice))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool_L hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    hF.eps_pool hF.band_pool

/-! ## §6 — `M4ArithPrime` AT THE LINEAR DOOR -/

/-- **⟦THE `gRows` GATE AT THE JOIN, AT THE LINEAR DOOR⟧** (`GRowsZeroGate''_L`). -/
structure GRowsZeroGate''_L (M Xd : ℕ) (π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free, at the linear grade. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M ≤ 1 / 3 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 3 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the linear ladder. -/
  p2 : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * π₀

/-- **⟦THE RESIDUAL, PRICED AT THE JOIN AND THE LINEAR DOOR⟧** (`gRows_zero_of_gate''_L`). -/
theorem gRows_zero_of_gate''_L {M Xd : ℕ} {π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate''_L M Xd π₀) :
    5760 * (a2RowsSum'_L M Xd + (0 : ℝ) * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_L hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2]

/-- **⟦THE FRAME AT THE JOIN, FROM FOUR GATES, AT THE LINEAR DOOR⟧**
(`doorFuseFrame_pool'_of_gates_L`).  `DoorBaseFrame` and `a3_one_le_log_of_three_le` read no
ladder and are the landed objects; only `gP1` and `gRows` move. -/
theorem doorFuseFrame_pool'_of_gates_L {M Xd j : ℕ} {Cs ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate''_L M Xd π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_L M Xd j Cs 0 ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_L hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hb.X_three
      have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
        rwa [Real.log_exp] at this
      linarith
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hb.X_three
      have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
        rwa [Real.log_exp] at this
      linarith
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- **⟦THE JOINED CHAIN FEEDS THE FRAMES, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_join_L`). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_L {R : ChowlaRegime} {M : ℕ}
    {Cs C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      GRowsZeroGate''_L M (A + s) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L (Cs (A + s)) 0 M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_L (Cs := Cs) (Ccc := fun _ => 0) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband (fun A => le_trans zero_le_one (hone A))
    henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_L (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-! ## §7 — `M4SocketFused` AT THE LINEAR DOOR -/

/-- **⟦THE FUSED TERMINAL, AT THE LINEAR DOOR⟧** (`m4_socket_discharged_fused_L`) —
the fusion of `m4_socket_discharged_bandfree_zero_L` and `m4_arith_door_exit_of_delta_L`. -/
theorem m4_socket_discharged_fused_L (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                            (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ := m4_hband_at_door_slot_L hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀ hHreg
    hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) (hbandslot hbandbase) harith

/-! ## §GK — the `G`-lever twins, at the LINEAR door

The §1–§7 pages at `G := s13GK K M`.  ⟦WHAT KEEPS ITS `_L` NAME⟧
`one_div_H1doorL_eq_a2Level1_L`, `H1door_two_L`, `window_row_eq_L`, `slot_of_log_gate_L`,
`pricing_numerals_L` and `DoorBaseFrame` are LEVEL-1 or ladder-BLIND and are reused verbatim.
⚠ ⟦THE BINDER SHADOW⟧ the socket exits bind an inner `K : ℝ` (`DoorArithFrame`'s ⟦C3⟧
constant); the lever's binder is threaded past it as `Klev`. -/

/-- `log_calP_door_one_L`, at the lever — `𝒫₁` is LEVEL 1. -/
lemma log_calP_door_one_L_gk (K M : ℕ) :
    Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) = (AdoorL M : ℝ) * Real.log 2 := by
  rw [calP, calE_gk_one]
  push_cast
  rw [Real.log_pow]

/-- `calP_door_one_le_two_L`, at the lever. -/
lemma calP_door_one_le_two_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    calP (AdoorL M) (s13GK K M) 1 ≤ calP (AdoorL M) (s13GK K M) 2 := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rw [calE_one, calE]
  have h1 : 1 ≤ (s13GK K M) ^ (2 - 1) := Nat.one_le_pow _ _ (s13GK_pos K hM)
  have h2 : 1 ≤ (Nat.factorial 2) ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos 2)
  calc AdoorL M = AdoorL M * 1 * 1 := by ring
    _ ≤ AdoorL M * (s13GK K M) ^ (2 - 1) * (Nat.factorial 2) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

/-- `a2RowsSum_door_decomp_L`, at the lever. -/
theorem a2RowsSum_door_decomp_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    a2RowsSum_L_gk K M Xd
      = 5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hH2 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hH0 : (0 : ℝ) < H1doorL M := by linarith
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [a2RowsSum_L_gk, hIcc, Finset.sum_insert (by decide), Finset.sum_singleton,
    show calH (H1doorL M) 1 = H1doorL M by rw [calH]; norm_num,
    show calH (H1doorL M) 2 = 4 * H1doorL M by rw [calH]; norm_num,
    window_row_eq_L hXd0 hH0, window_row_eq_L hXd0 (by linarith : (0 : ℝ) < 4 * H1doorL M),
    ← one_div_H1doorL_eq_a2Level1_L]
  ring

/-- `GRowsZeroGate_L`, at the lever.  Only `level1`'s `𝒬₁` is rewritten, and that is a LEVEL-1
read, so the demand is literally the `_L` one (`toLanded`). -/
structure GRowsZeroGate_L_gk (K : ℕ) (M Xd : ℕ) : Prop where
  /-- `1 ≤ log X_d`. -/
  base : 1 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE LEVEL-1 SLOT⟧ `μ/500 + loglog 𝒬₁/3 + 14 ≤ (log 2/12)·A_L(M)`. -/
  level1 : Real.log (Real.log (Xd : ℝ)) / 500
      + Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) / 3 + 14
    ≤ Real.log 2 / 12 * (AdoorL M : ℝ)
  /-- ⟦THE ENDPOINT SLOT⟧ `μ/500 + 13 ≤ log X_d`. -/
  endpt : Real.log (Real.log (Xd : ℝ)) / 500 + 13 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE `p²` SLOT⟧ `μ·(1 + 1/500) + 15 ≤ (log 2)·A_L(M)`. -/
  p2 : Real.log (Real.log (Xd : ℝ)) * (1 + 1 / 500) + 15 ≤ Real.log 2 * (AdoorL M : ℝ)

/-- The levered linear gate IS the linear gate — `𝒬₁` is LEVEL 1. -/
theorem GRowsZeroGate_L_gk.toLinear {K M Xd : ℕ} (h : GRowsZeroGate_L_gk K M Xd) :
    GRowsZeroGate_L M Xd where
  base := h.base
  level1 := by rw [← calQK_gk_one_eq (AdoorL M) K M M]; exact h.level1
  endpt := h.endpt
  p2 := h.p2

/-- `gRows_zero_of_gate_L`, at the lever — a TRANSPORT through `a2RowsSum_L_gk_le`. -/
theorem gRows_zero_of_gate_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate_L_gk K M Xd) :
    5760 * (a2RowsSum_L_gk K M Xd + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
  have hlinear := gRows_zero_of_gate_L hM hXd hg.toLinear
  have hle := a2RowsSum_L_gk_le K M Xd
  linarith

/-- `a2RowsSum'_door_decomp_L`, at the lever. -/
theorem a2RowsSum'_door_decomp_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    a2RowsSum'_L_gk K M Xd
      = 5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hH2 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hH0 : (0 : ℝ) < H1doorL M := by linarith
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [a2RowsSum'_L_gk, hIcc, Finset.sum_insert (by decide), Finset.sum_singleton,
    show calH (H1doorL M) 1 = H1doorL M by rw [calH]; norm_num,
    show calH (H1doorL M) 2 = 4 * H1doorL M by rw [calH]; norm_num,
    window_row_eq_L hXd0 hH0, window_row_eq_L hXd0 (by linarith : (0 : ℝ) < 4 * H1doorL M),
    ← one_div_H1doorL_eq_a2Level1_L]
  ring

/-- `GRowsZeroGate'_L`, at the lever. -/
structure GRowsZeroGate'_L_gk (K : ℕ) (M Xd : ℕ) : Prop where
  /-- `1 ≤ log X_d`. -/
  base : 1 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE LEVEL-1 SLOT⟧ `μ/500 + loglog 𝒬₁/3 + 14 ≤ (log 2/12)·A_L(M)`. -/
  level1 : Real.log (Real.log (Xd : ℝ)) / 500
      + Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) / 3 + 14
    ≤ Real.log 2 / 12 * (AdoorL M : ℝ)
  /-- ⟦THE ENDPOINT SLOT⟧ `μ/500 + 13 ≤ log X_d`. -/
  endpt : Real.log (Real.log (Xd : ℝ)) / 500 + 13 ≤ Real.log (Xd : ℝ)
  /-- ⟦THE `p²` SLOT, R1⟧ `μ/500 + 15 ≤ (log 2)·A_L(M)`. -/
  p2 : Real.log (Real.log (Xd : ℝ)) * (1 / 500) + 15 ≤ Real.log 2 * (AdoorL M : ℝ)

/-- The levered linear R1 gate IS the linear R1 gate. -/
theorem GRowsZeroGate'_L_gk.toLinear {K M Xd : ℕ} (h : GRowsZeroGate'_L_gk K M Xd) :
    GRowsZeroGate'_L M Xd where
  base := h.base
  level1 := by rw [← calQK_gk_one_eq (AdoorL M) K M M]; exact h.level1
  endpt := h.endpt
  p2 := h.p2

/-- `gRows_zero_of_gate'_L`, at the lever — the same TRANSPORT, through `a2RowsSum'_L_gk_le`. -/
theorem gRows_zero_of_gate'_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'_L_gk K M Xd) :
    5760 * (a2RowsSum'_L_gk K M Xd + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ (Real.log (Xd : ℝ)) ^ (-(1 : ℝ) / 500) := by
  have hlinear := gRows_zero_of_gate'_L hM hXd hg.toLinear
  have hle := a2RowsSum'_L_gk_le K M Xd
  linarith

/-- `gRows_at_socketBase_L`, at the lever. -/
theorem gRows_at_socketBase_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hM : 1 ≤ M) (hb : SocketBaseL R M H L q j A s)
    (hX1 : (1 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ))
    (htop : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
          + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)))
        ≤ 1 / 2 * Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500))
    (hend : 5760 * ((2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ))
        ≤ 1 / 2 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500)) :
    5760 * (a2RowsSum'_L_gk K M (A + s) + (0 : ℝ) * (2 / (M : ℝ)))
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hA : 0 < A := hbb.2.2.2.2.2.2.2.1
  have hXdN : 1 ≤ A + s := by omega
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have hpos : 0 < A + s := by omega
    exact_mod_cast hpos
  have hcap : (((A + s : ℕ)) : ℝ) ≤ 3 * (R.x : ℝ) := socketBase_base_le_three_x hbb
  have hmono : Real.log (3 * (R.x : ℝ)) ^ (-(1 : ℝ) / 500)
      ≤ Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (Real.log_le_log hX0 hcap) (by norm_num)
  have hconst : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
            + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)))
      ≤ 1 / 2 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 500) := by
    refine htop.trans ?_
    linarith
  rw [a2RowsSum'_door_decomp_L_gk K hM hXdN]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
            + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
          + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)))
        + 5760 * ((2 * Real.exp 1 + 2) / (((A + s : ℕ)) : ℝ)) := by ring
  rw [hid]
  linarith

/-- `m4_chiSummedFreeRow_of_doorArith_zero_L`, at the lever. -/
theorem m4_chiSummedFreeRow_of_doorArith_zero_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk Klev hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L_gk Klev
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk Klev hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L_gk Klev harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk Klev hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- `m4_socket_discharged_conditional_zero_L`, at the lever. -/
theorem m4_socket_discharged_conditional_zero_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_zero_L_gk Klev hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- `m4_socket_discharged_bandfree_zero_L`, at the lever. -/
theorem m4_socket_discharged_bandfree_zero_L_gk (Klev : ℕ) (hK : Klev ≤ 170000000)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                            (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk Klev x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hcomp⟩ := m4_socket_discharged_conditional_zero_L_gk Klev hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk Klev hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-- `a2DoorGrade_pool_L_priced_rho`, at the lever (the levered pooled linear grade has the
same body — `a2Level1_L` is K-invariant). -/
theorem a2DoorGrade_pool_L_priced_rho_gk (K : ℕ) {M H j : ℕ} {X C₁ M₀ Kar ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ Kar ρ) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    arcDen 12 H * a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      ≤ RSanDoorRho ρ H := by
  have heq : a2DoorGrade_pool_L_gk K M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
      = a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := rfl
  rw [heq]
  exact a2DoorGrade_pool_L_priced_rho hfr hpool hprice

/-- `m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L`, at the lever. -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {C₁ M₀ π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (hgrade : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                (M₀ (A + s)) (π₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
          (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L_gk K R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) (π₀ (A + s)) :=
    a2DoorGrade_pool_nonneg_L_gk K hM (log_natCast_nonneg' (A + s)) hh0 (hpool (A + s))
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- `m4_arith_henv_rho_pool_L`, at the lever. -/
theorem m4_arith_henv_rho_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {C₁ M₀ π₀ : ℕ → ℝ}
    {Kar ρ : ℝ}
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
          (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  fun H L q j A s hb =>
    a2DoorGrade_pool_L_priced_rho_gk K (harith H L q j A s hb) (hpool (A + s))
      (hprice H L q j A s hb)

/-- `m4_chiSummedFreeRow_of_doorArithRho_pool_L`, at the lever. -/
theorem m4_chiSummedFreeRow_of_doorArithRho_pool_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {Kar ρ : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s))
        (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ)
              (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar ρ)
    (hprice : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      188133 * π₀ (A + s) * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2)
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big_L_gk K
    (m4_chiSummedFreeRowBig_of_doorGradeGated_pool_L_gk K hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀)
      hpool ?_ (m4_arith_henv_rho_pool_L_gk K hpool harith hprice))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows
    hF.eps_pool hF.band_pool

/-- `GRowsZeroGate''_L`, at the lever. -/
structure GRowsZeroGate''_L_gk (K : ℕ) (M Xd : ℕ) (π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free, at the linear grade. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M ≤ 1 / 3 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 3 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the levered linear ladder. -/
  p2 : 138240 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * π₀

/-- `gRows_zero_of_gate''_L`, at the lever. -/
theorem gRows_zero_of_gate''_L_gk (K : ℕ) {M Xd : ℕ} {π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate''_L_gk K M Xd π₀) :
    5760 * (a2RowsSum'_L_gk K M Xd + (0 : ℝ) * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_L_gk K hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1_L M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1_L M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2]

/-- `doorFuseFrame_pool'_of_gates_L`, at the lever. -/
theorem doorFuseFrame_pool'_of_gates_L_gk (K : ℕ) {M Xd j : ℕ} {Cs ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate''_L_gk K M Xd π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_L_gk K M Xd j Cs 0 ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_L_gk K hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hb.X_three
      have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
        rwa [Real.log_exp] at this
      linarith
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hb.X_three
      have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
        rwa [Real.log_exp] at this
      linarith
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- `m4_chiSummedFreeRow_of_doorAssembly_join_L`, at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      GRowsZeroGate''_L_gk K M (A + s) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L_gk K (Cs (A + s)) 0 M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
          (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := Cs) (Ccc := fun _ => 0)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband
    (fun A => le_trans zero_le_one (hone A)) henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_L_gk K (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-- `m4_socket_discharged_fused_L`, at the lever. -/
theorem m4_socket_discharged_fused_L_gk (K : ℕ) (hK : K ≤ 170000000) (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                            (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L_gk K R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk K hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀
    hHreg hframe (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) (hbandslot hbandbase)
    harith

/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK` ceiling binders on the `L`-chain: the ceiling moves
INSIDE the internal `∀ M` as `≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_chiSummedFreeRow_of_doorArith_zero_L_gk_kwide`) —
`m4_chiSummedFreeRow_of_doorArith_zero_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_chiSummedFreeRow_of_doorArith_zero_L_gk_kwide (Klev : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K : ℝ),
        1 ≤ M → Klev ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H)) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk_kwide Klev
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hKw hb1 hc1 hframe hbase hcap hband harith
  refine m4_chiSummedFreeRow_of_big_L_gk Klev
    (m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk Klev hM (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_L_gk Klev harith))
  intro H L q j A s hb
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_L_gk Klev hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hslot Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb)
    (hband H L q j A s hb) hF.gP1 hF.gRows ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-- ⟦WIDE CEILING TWIN⟧ (`m4_socket_discharged_conditional_zero_L_gk_kwide`) —
`m4_socket_discharged_conditional_zero_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_socket_discharged_conditional_zero_L_gk_kwide (Klev : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
        1 ≤ M → Klev ≤ 170000000 * M → 2 / 10 ^ 49 ≤ δ₀ →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
        (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                        (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
        M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
          ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
              m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
          ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hitem11⟩ := m4_chiSummedFreeRow_of_doorArith_zero_L_gk_kwide Klev
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hKw hδ₀ hHreg hb1 hc1 hframe hbase hcap hband harith
  refine ⟨hitem11 Cp hCp R M C₁ M₀ ε cU bU t₁ K hM hKw hb1 hc1 hframe hbase hcap hband harith,
    m4_arith_gate4_L M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-- ⟦WIDE CEILING TWIN⟧ (`m4_socket_discharged_bandfree_zero_L_gk_kwide`) —
`m4_socket_discharged_bandfree_zero_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `Klev ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_socket_discharged_bandfree_zero_L_gk_kwide (Klev : ℕ)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M → Klev ≤ 170000000 * M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (K δ₀ : ℝ),
            2 / 10 ^ 49 ≤ δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk Klev M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk Klev M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK Klev M))
                            (calQK (AdoorL M) (s13GK Klev M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk Klev χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk Klev x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) →
            M4ChiSummedFreeRow_L_gk Klev R M (m4ChiRowGraded_L M (fun _ H => RSanDoor H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hcomp⟩ := m4_socket_discharged_conditional_zero_L_gk_kwide Klev
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM hKw
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk Klev hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact hcomp Cp hCp R M C₁ M₀ ε cU bU t₁ K δ₀ hM hKw hδ₀ hHreg hb1 hc1 hframe hbase hcap
    (hbandslot hbandbase) harith

/-- ⟦WIDE CEILING TWIN⟧ (`m4_socket_discharged_fused_L_gk_kwide`) —
`m4_socket_discharged_fused_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_socket_discharged_fused_L_gk_kwide (K : ℕ) (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M → K ≤ 170000000 * M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
            (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
                TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
                (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                  ≤ 8 * (0 : ℝ) ^ 2
                    + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                          \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                        ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                            (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                            (mrAlpha (1 / 12)) 2,
                        ‖spoly (2 * (A + s))
                          (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                    + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                        * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorBandBase_L_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
              DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_L_gk K R M
                (m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloorL M ≤ j →
                  m4ChiRowGraded_L M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk_kwide K
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ hM hKw
  obtain ⟨C', x₀, hC'pos, hbandslot⟩ :=
    m4_hband_at_door_slot_L_gk K hMmu Aexp hAexp R M hM C₁ M₀
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU t₁ Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcap hbandbase harith
  exact m4_arith_door_exit_of_delta_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp) hM hδ₀
    hHreg hframe (hslot Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) (hbandslot hbandbase)
    harith

end Salt.MR

end
