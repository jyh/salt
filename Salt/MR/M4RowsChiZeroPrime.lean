/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiZero
import Salt.MR.M4RowsChiEndPrime

/-!
# ⟦R4 — THE `χ`-ZERO CHAIN AT ⟦R1⟧'s `L²` NUMERAL⟧ (`M4RowsChiZeroPrime`)

Design provenance: `docs/blueprints/flags.md` 2026-07-30 17:51 (⟦R3-A + R3-B LAND⟧), ⟦THE
RESIDUE (the R4 wave)⟧ item (3): *"the `χ`-zero file's `L²` re-run — the cube-gate's second
site through its whole consumer chain"*.

`M4RowsChiZero` is the sieve-vanishing twin chain: Lemma 12's fourth (block-free) row is
identically `0` at `𝒮`-supported data, so the density constant `C_p` becomes a FREE
nonnegative parameter and `SeamCalibrationK.sum_ratioK_le` is never called.  That chain
prices its `p²` row at the LANDED numerator `16·log₂(2X_d)/𝒫ⱼ` and absorbs the endpoint
half through `logb_two_mul_P_le`'s `L·P ≤ 2X_d`.

This file re-runs it at ⟦R1⟧'s direct `L²` grade — `M4P2MR.ramP2massEndMR_L2_direct`'s
`24/(X_d·𝒫)`, **`X_d`-FREE** — whose endpoint half needs the CUBE gate
`L²·𝒫 ≤ 3X_d` (`M4RowMR.logbsq_two_mul_P_le`, re-minted here at its own name because that one
is `private`).  The exit is the `hrows` supplier `M4AssemblyPrime`'s pooled/primed assembly
asks for, at a FREE `C_p ≥ 0` — in particular at `C_p := 0`, where the density debit
`5760·C_p·(2/M)` leaves the frame's `gRows` field outright.

## ⟦WHAT IS VERBATIM AND WHAT MOVES⟧

VERBATIM from `M4RowsChiZero`: §1 (`BlockLive` and its three transports, the vanishing
`blockfree_row_zero`), `DoorRowZeroBase` and `doorRowZeroBase_of_doorRowEndBase`,
`blockLive_winCutH_doorCoeffU`, and the `∀ C_p ≥ 0` shape of every statement.

MOVES: the `p²` numerator `16·log₂(2X_d)/𝒫 ↦ 24/𝒫`; the absorption gate
`L·𝒫 ≤ 2X_d ↦ L²·𝒫 ≤ 3X_d`; the row floor `2 ≤ P ↦ 4 ≤ P` (stated as `2 ≤ A` at the
calibrated exit, free from `CalFrameK.A_floor`'s `24 ≤ A` and from `Adoor M ≥ 2^18`); and the
row constant `M4RowsChiEnd.m4MrowChiEnd ↦ M4RowsChiEndPrime.m4MrowChiEnd'`, hence the
interface `ThmA2.a2Mrow ↦ ThmA2Prime.a2Mrow'`.

## Contents

* §1 the one stone: `logbsq_two_mul_P_le_zero` (the CUBE gate at its own name);
* §2 the four-row price without the density, at the `L²` numeral
  (`lemma12RowsMR_pricedK_end_zero'`, `lemma12RowsMR_priced_ratioK_end_zero'`);
* §3 the `j`-collection and the K-calibrated exit
  (`sum_lemma12RowsMR_pricedK_end_zero'`, `sum_lemma12RowsMR_priced_calibratedK2_end_zero'`);
* §4 the twisted datum (`sum_lemma12RowsMR_priced_chi_end_zero'`);
* §5 the per-`χ` seam row as a number and the `hrowsSum` slot
  (`m4_rowChi_number_of_capstone_zero'`, `m4_hrowsSum_chi_zero'`);
* §6 the door instance (`m4_hrowsSum_chi_door_zero'`, `m4_hrowsSlot_at_door_zero'`);
* §7 ⟦item 11⟧ at the zero density AND the free pool
  (`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'`) — where this chain fuses with the R1×R2
  join's frame.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  `M4RowsChiEndPrime.m4_rowChi_weighed_end'`
and `M4RowsChiEndPrime.m4MrowChiEnd'_le_a2Mrow'` are REUSED at `C_p := C`, which is why §5–§7
are short: the weighting page and the door bridge are parametric in the density constant.

⟦THE FOUR LOG SCALES⟧ stay apart exactly as in `M4RowsChiZero`.  `arcDen 12 H` is never
evaluated.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ONE STONE: THE CUBE GATE AT ITS OWN NAME

`M4RowMR.logbsq_two_mul_P_le` is `private` to its file; `M4RowsChiZero` re-minted
`logb_two_mul_P_le` for exactly the same reason.  The statement and the proof are the R1
original's, byte for byte: with `u = log X_d`, `s = √u ≥ 100`, `P ≤ e^s` and `L ≤ (3/2)u`,
the demand `(9/4)u²·e^s ≤ 3e^u` is `(3/4)u² ≤ e^{u−s}`, and
`e^{u−s} = (e^{(u−s)/3})³ ≥ ((33/100)u)³ ≥ (3/4)u²` at `u ≥ 10⁴`. -/

/-- **⟦THE CUBE GATE⟧** (`logbsq_two_mul_P_le_zero`): `log₂(2X_d)²·P ≤ 3·X_d`, from the row's
OWN binders.  This is the `L²`-form the ⟦R1⟧ numerator needs: the `B2` slot's spare half is
now the CONSTANT `12/(X_d·P)`, so the endpoint mass `4L²/X_d²` must fit inside it. -/
private lemma logbsq_two_mul_P_le_zero {P Q Xd : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd)) :
    (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 * (P : ℝ) ≤ 3 * (Xd : ℝ) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hu0 : 0 ≤ Real.log (Xd : ℝ) := by
    by_contra hcon
    rw [Real.sqrt_eq_zero'.mpr (not_le.mp hcon).le] at hbig
    norm_num at hbig
  have hsq : Real.sqrt (Real.log (Xd : ℝ)) * Real.sqrt (Real.log (Xd : ℝ))
      = Real.log (Xd : ℝ) := Real.mul_self_sqrt hu0
  have hu4 : (10000 : ℝ) ≤ Real.log (Xd : ℝ) := by nlinarith
  -- `s ≤ u/100`
  have hsu : Real.sqrt (Real.log (Xd : ℝ)) ≤ Real.log (Xd : ℝ) / 100 := by nlinarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := Real.sqrt_nonneg _
  -- `P ≤ e^s`
  have hPexp : (P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
    have hlogP : Real.log (P : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) :=
      le_trans (Real.log_le_log hP0 hPQR) hreg
    calc (P : ℝ) = Real.exp (Real.log (P : ℝ)) := (Real.exp_log hP0).symm
      _ ≤ Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := Real.exp_le_exp.mpr hlogP
  -- `log₂(2X_d) ≤ (3/2)·log X_d`
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hLb : Real.logb 2 (2 * (Xd : ℝ)) ≤ 3 / 2 * Real.log (Xd : ℝ) := by
    have hgt2 := Real.log_two_gt_d9
    have hlt2 := Real.log_two_lt_d9
    have hprod : (0 : ℝ) ≤ (Real.log (Xd : ℝ) - 10000) * (Real.log 2 - 0.6931471803) :=
      mul_nonneg (by linarith) (by linarith)
    have hlogb : Real.logb 2 (2 * (Xd : ℝ))
        = (Real.log 2 + Real.log (Xd : ℝ)) / Real.log 2 := by
      rw [Real.logb, Real.log_mul (by norm_num) (ne_of_gt hXd0)]
    rw [hlogb, div_le_iff₀ hl2]
    linarith
  -- ⟦THE CUBE⟧ `(3/4)u² ≤ e^{u−s}`
  have hx : (33 / 100 : ℝ) * Real.log (Xd : ℝ)
      ≤ (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) / 3 := by linarith
  have hx0 : (0 : ℝ) ≤ (33 / 100 : ℝ) * Real.log (Xd : ℝ) := by linarith
  have hexp1 : (33 / 100 : ℝ) * Real.log (Xd : ℝ)
      ≤ Real.exp ((Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) / 3) := by
    have h1 := Real.add_one_le_exp
      ((Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) / 3)
    linarith
  have hcube : ((33 / 100 : ℝ) * Real.log (Xd : ℝ)) ^ 3
      ≤ (Real.exp ((Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) / 3)) ^ 3 :=
    pow_le_pow_left₀ hx0 hexp1 3
  have hexp3 : (Real.exp ((Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) / 3)) ^ 3
      = Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgap : 3 / 4 * Real.log (Xd : ℝ) ^ 2
      ≤ Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ))) := by
    rw [← hexp3]
    nlinarith [hcube, hu4, sq_nonneg (Real.log (Xd : ℝ))]
  calc (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 * (P : ℝ)
      ≤ (3 / 2 * Real.log (Xd : ℝ)) ^ 2 * Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
        have hLsq : (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 ≤ (3 / 2 * Real.log (Xd : ℝ)) ^ 2 := by
          nlinarith
        exact mul_le_mul hLsq hPexp hP0.le (by positivity)
    _ = 3 * (3 / 4 * Real.log (Xd : ℝ) ^ 2) * Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
        ring
    _ ≤ 3 * Real.exp (Real.log (Xd : ℝ) - Real.sqrt (Real.log (Xd : ℝ)))
          * Real.exp (Real.sqrt (Real.log (Xd : ℝ))) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 3))
          (Real.exp_pos (Real.sqrt (Real.log (Xd : ℝ)))).le
        linarith
    _ = 3 * Real.exp (Real.log (Xd : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ = 3 * (Xd : ℝ) := by rw [Real.exp_log hXd0]

/-! ## §2 — THE FOUR-ROW PRICE WITHOUT THE DENSITY, AT THE `L²` NUMERAL

`M4RowsChiZero` §2 at ⟦R1⟧'s `p²` row.  Rows 1 and 2 are priced exactly as there; row 3 is
`M4P2MR.ramP2massEndMR_L2_direct` with §1 absorbing its endpoint half; row 4 is the vanishing
(`M4RowsChiZero.blockfree_row_zero`). -/

/-- `M4RowsChiZero.four_rows_le_zero`, re-minted (that one is `private`): the fourth row is
KILLED and the third bracket slot is gone, `8·(3/2) = 12` still closing tight. -/
private lemma four_rows_le_zero' {pre R1 R2 R3 R4 B1 B2 : ℝ}
    (h2 : R2 ≤ 2 * R1) (h1 : 2 * R1 ≤ pre * B1)
    (h3 : R3 ≤ pre * (3 / 2) * B2) (h4 : R4 = 0)
    (_hR1 : 0 ≤ R1) (_hR3 : 0 ≤ R3) :
    2 * (4 * (R1 + R2 + R3 + R4)) ≤ 12 * pre * (B1 + B2) := by
  subst h4
  linarith

/-- **⟦THE MR ROW, PRICED, DENSITY-FREE, AT THE `L²` NUMERAL⟧**
(`lemma12RowsMR_pricedK_end_zero'`).  `M4RowsChiZero.lemma12RowsMR_pricedK_end_zero` with the
`p²` slot at the `X_d`-FREE `24/(X_d·P)`; the endpoint mass `4L²/X_d²` is absorbed in the
`B2` slot's unspent half — now the CONSTANT `12/(X_d·P)` — by §1's cube gate.

⟦WHAT LEFT THE HYPOTHESIS LIST⟧ (as in the landed zero twin) the error-domination product and
the dyadic support pin, both read only by `blockfree_sum_le`.  ⟦WHAT MOVED⟧ `2 ≤ P ↦ 4 ≤ P`,
the census's floor. -/
theorem lemma12RowsMR_pricedK_end_zero' (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hH : 2 ≤ H)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : BlockLive P Q a) :
    lemma12RowsMR_end N Xd P Q H T a b c
      ≤ 12 * (2 * T + 20 * (N : ℝ))
          * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
              + 24 / ((Xd : ℝ) * (P : ℝ))) := by
  have hP2 : 2 ≤ P := by omega
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hNR : 2 * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hH0 : (0 : ℝ) < H := by linarith
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  -- ⟦ROW 1 + ROW 2⟧ the second window costs at most twice the first
  have hwin2 := second_window_le_first_row (H := H) (T := T) (Nr := (N : ℝ)) (X := Xd)
    hH hXd hT hNR
  -- ⟦ROW 1⟧ the windowed bracket is a factor `e ≥ 2` below the landed one
  have hrow1nn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2 := by positivity
  have hrow1 : 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
      ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
    have hid : (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
        - 2 * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2)
        = (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) := by
      field_simp
    have hnn : (0 : ℝ)
        ≤ (Real.exp 1 - 2) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) / (Xd : ℝ) ^ 2) :=
      mul_nonneg (by linarith) hrow1nn
    linarith [hid.le, hid.ge, hnn]
  -- ⟦ROW 3⟧ the FUSED `p²` mass at the DIRECT `L²` grade, and §1's absorption
  have hp2 := ramP2massEndMR_L2_direct N Xd P Q hXd hN hP a b c ha hb hc
  have hgate := logbsq_two_mul_P_le_zero (P := P) (Q := Q) (Xd := Xd) hP2 hPQ hXd hreg hbig
  have habs : 4 * (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 / (Xd : ℝ) ^ 2
      ≤ 1 / 2 * (24 / ((Xd : ℝ) * (P : ℝ))) := by
    rw [show (1 : ℝ) / 2 * (24 / ((Xd : ℝ) * (P : ℝ))) = 12 / ((Xd : ℝ) * (P : ℝ)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hXd0.le
      (by linarith : (0 : ℝ) ≤ 3 * (Xd : ℝ) - (Real.logb 2 (2 * (Xd : ℝ))) ^ 2 * (P : ℝ))]
  have hp2' : (∑ n ∈ Finset.Icc 1 N,
        ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 3 / 2 * (24 / ((Xd : ℝ) * (P : ℝ))) := by linarith
  have hp2nn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hrow3 : (2 * T + 20 * (N : ℝ)) * (∑ n ∈ Finset.Icc 1 N,
        ‖ramP2coeffEndMR N Xd P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * (3 / 2) * (24 / ((Xd : ℝ) * (P : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hp2' hpre
    linarith
  -- ⟦ROW 4⟧ ⟦THE VANISHING⟧
  rw [lemma12RowsMR_end]
  refine four_rows_le_zero' hwin2 ?_ hrow3 ?_ (mul_nonneg hpre hrow1nn)
    (mul_nonneg hpre hp2nn)
  · have h := mul_le_mul_of_nonneg_left hrow1 hpre
    linarith
  · rw [blockfree_row_zero hlive, mul_zero]

/-- **⟦THE `(T/X_d + 1)` EXIT, DENSITY-FREE, AT THE `L²` NUMERAL⟧**
(`lemma12RowsMR_priced_ratioK_end_zero'`).  `N ≤ 4X_d` turns `12(2T + 20N)` into
`960·X_d·(T/X_d + 1)` and the `X_d` distributes into the (two-slot) bracket, leaving the
`X_d`-FREE `24/P`. -/
theorem lemma12RowsMR_priced_ratioK_end_zero' (P Q N Xd : ℕ) (H T : ℝ) (a b c : ℕ → ℂ)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hH : 2 ≤ H)
    (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : Real.log Q ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : BlockLive P Q a) :
    lemma12RowsMR_end N Xd P Q H T a b c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
              + 24 / (P : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hXdne : (Xd : ℝ) ≠ 0 := ne_of_gt hXd0
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have h : 0 < P := by omega
    exact_mod_cast h
  have hPne : (P : ℝ) ≠ 0 := ne_of_gt hP0
  have hp2nn : (0 : ℝ) ≤ 24 / ((Xd : ℝ) * (P : ℝ)) := by positivity
  have hBnn : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2)
      + 24 / ((Xd : ℝ) * (P : ℝ)) := by
    have hH0 : (0 : ℝ) < H := by linarith
    have hb1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2) := by
      positivity
    linarith
  have hcoefle : 12 * (2 * T + 20 * (N : ℝ)) ≤ 960 * (Xd : ℝ) * (T / (Xd : ℝ) + 1) := by
    have hTid : (Xd : ℝ) * (T / (Xd : ℝ)) = T := by field_simp
    nlinarith [hN4, hT, hXd0]
  have hstep := lemma12RowsMR_pricedK_end_zero' P Q N Xd H T a b c hP hPQ hXd hN hT hH
    hreg hbig ha hb hc hlive
  refine hstep.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcoefle hBnn
  refine hmul.trans (le_of_eq ?_)
  field_simp

/-! ## §3 — THE `j`-COLLECTION, AND THE K-CALIBRATED EXIT

⟦WHERE `sum_ratioK_le` DIES⟧ exactly as in `M4RowsChiZero` §3: the collection has nothing to
collect, so the calibration step is never performed; the twin's right-hand side is the primed
landed one only because the two absent quantities (`Σ_j 1/X_d` and `C·(2/M)`) are re-added as
nonnegative slack at the interface. -/

/-- **⟦THE `j`-COLLECTION, DENSITY-FREE, AT THE `L²` NUMERAL⟧**
(`sum_lemma12RowsMR_pricedK_end_zero'`). -/
theorem sum_lemma12RowsMR_pricedK_end_zero' (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
    (Jb N Xd : ℕ) (T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ)
    (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hgates : ∀ j ∈ Finset.Icc 1 Jb, 4 ≤ Pseq j ∧ Pseq j ≤ Qseq j ∧ 2 ≤ Hseq j)
    (hreg : ∀ j ∈ Finset.Icc 1 Jb, Real.log (Qseq j : ℝ) ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (Pseq j) (Qseq j) a) :
    ∑ j ∈ Finset.Icc 1 Jb, lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ∑ j ∈ Finset.Icc 1 Jb,
              ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 24 / (Pseq j : ℝ)) := by
  have hlevel : ∀ j ∈ Finset.Icc 1 Jb,
      lemma12RowsMR_end N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 24 / (Pseq j : ℝ)) := by
    intro j hj
    obtain ⟨hP, hPQ, hH⟩ := hgates j hj
    exact lemma12RowsMR_priced_ratioK_end_zero' (Pseq j) (Qseq j) N Xd (Hseq j) T a (b j) c
      hP hPQ hXd hN hT hH hN4 (hreg j hj) hbig ha (hb j) hc (hlive j hj)
  refine (Finset.sum_le_sum hlevel).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]

/-- `M4RowMR.four_le_calP`, re-minted (that one is `private`): `2 ≤ A` and `1 ≤ G` give
`calE ≥ 2`, hence `calP = 2^{calE} ≥ 4`.  Free at the door (`Adoor M ≥ 2^18`) and on any
`CalFrameK` (`24 ≤ A`). -/
private lemma four_le_calP_zero' {A G j : ℕ} (hA : 2 ≤ A) (hG : 1 ≤ G) : 4 ≤ calP A G j := by
  have hE2 : 2 ≤ calE A G j := by
    rw [calE]
    calc (2 : ℕ) = 2 * 1 * 1 := by norm_num
      _ ≤ A * G ^ (j - 1) * (Nat.factorial j) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul hA (Nat.one_le_pow _ _ (by omega)))
            (Nat.one_le_pow _ _ (Nat.factorial_pos j))
  rw [calP]
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE2

/-- **⟦THE FULLY-PRICED MR SEAM ROW AT `C_p` FREE, AT THE `L²` NUMERAL⟧**
(`sum_lemma12RowsMR_priced_calibratedK2_end_zero'`).
`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end'`'s density-free twin: the right-hand side
is that theorem's BYTE FOR BYTE — including the `C·(2/M)` summand — but `C` is a FREE
nonnegative real instead of an existential witness, because the row it used to pay for is `0`.
`SeamCalibrationK.sum_ratioK_le` is not called anywhere in the proof. -/
theorem sum_lemma12RowsMR_priced_calibratedK2_end_zero' (C : ℝ) (hC : 0 ≤ C)
    (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (c : ℕ → ℂ)
    (hA : 2 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T)
    (hH1 : 2 ≤ H1) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log Xd))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) :
    ∑ j ∈ Finset.Icc 1 Jb,
        lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a (b j) c
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((∑ j ∈ Finset.Icc 1 Jb,
                ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                    * (Real.exp 1 / (Xd : ℝ) ^ 2))
                  + 24 / ((calP A G j : ℕ) : ℝ)
                  + 1 / (Xd : ℝ)))
            + C * (2 / (M : ℝ))) := by
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      4 ≤ calP A G j ∧ calP A G j ≤ calQK A G M j ∧ 2 ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨four_le_calP_zero' hA hG, calP_le_calQK hM hj.1, ?_⟩
    rw [calH]
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    nlinarith
  have h := sum_lemma12RowsMR_pricedK_end_zero' (calP A G) (calQK A G M) (calH H1) Jb N Xd T
    a b c hXd hN hT hN4 hgates hreg hbig ha hb hc hlive
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hstep : ∑ j ∈ Finset.Icc 1 Jb,
        ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
            * (Real.exp 1 / (Xd : ℝ) ^ 2))
          + 24 / ((calP A G j : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 Jb,
            ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                * (Real.exp 1 / (Xd : ℝ) ^ 2))
              + 24 / ((calP A G j : ℕ) : ℝ)
              + 1 / (Xd : ℝ)) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
      linarith
    have hCm : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

/-! ## §4 — THE TWISTED DATUM

`M4RowsChiZero` §4 at §3's pricer.  The pricer is datum-generic, so the lift is `TLegChi`
§1's four coefficient transports plus `M4RowsChiZero.blockLive_chiBarCoeff`. -/

/-- **⟦THE FOUR-ROW LEMMA-12 ROW SUM AT TWISTED DATA, DENSITY-FREE, AT THE `L²` NUMERAL⟧**
(`sum_lemma12RowsMR_priced_chi_end_zero'`).  The hypotheses are stated on the UNTWISTED
sequences (block-liveness included) and the bound is the `q = 1` one VERBATIM at a FREE
`C ≥ 0`. -/
theorem sum_lemma12RowsMR_priced_chi_end_zero' (C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a c : ℕ → ℂ) (b : ℕ → ℕ → ℂ)
    (hA : 2 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (hXd : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hT : 0 ≤ T)
    (hH1 : 2 ≤ H1) (hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ))
    (hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)))
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ j m, ‖b j m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hlive : ∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) :
    ∑ j ∈ Finset.Icc 1 Jb,
        lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T
          (chiBarCoeff q χ a) (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
      ≤ 960 * (T / (Xd : ℝ) + 1)
          * ((∑ j ∈ Finset.Icc 1 Jb,
                ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                    * (Real.exp 1 / (Xd : ℝ) ^ 2))
                  + 24 / ((calP A G j : ℕ) : ℝ)
                  + 1 / (Xd : ℝ)))
            + C * (2 / (M : ℝ))) :=
  sum_lemma12RowsMR_priced_calibratedK2_end_zero' C hC A G M Jb N Xd H1 T
    (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
    hA hG hM hXd hN hT hH1 hN4 hreg hbig
    (norm_chiBarCoeff_le_one χ ha) (chiBarCoeff_bfam_le_one χ hb)
    (chiBarCoeff_cseq_le_one χ hc)
    (fun j hj => blockLive_chiBarCoeff χ (hlive j hj))

/-! ## §5 — THE PER-`χ` SEAM ROW AS A NUMBER, AND THE `hrowsSum` SLOT

`M4RowsChiZero` §5 at §4's pricer.  The composition is identical; the weighting page is
`M4RowsChiEndPrime.m4_rowChi_weighed_end'`, already parametric in `Cp` and asking only
`0 ≤ Cp`. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `M4RowsChiZero.m4_rowChi_number_of_capstone_zero`: the leg's exit and the
-- pricer's exit are elaborated against one another at full ladder width.
/-- **⟦THE PER-`χ` SEAM ROW AS A NUMBER, DENSITY-FREE, AT THE `L²` NUMERAL⟧**
(`m4_rowChi_number_of_capstone_zero'`).  `M4RowsChiZero.m4_rowChi_number_of_capstone_zero`
with the Lemma-12 bracket's `p²` slot at the `X_d`-FREE constant `24/𝒫ⱼ`.  The hypothesis
list is the landed zero twin's BYTE FOR BYTE — `2 ≤ A` is read off `CalFrameK.A_floor`. -/
theorem m4_rowChi_number_of_capstone_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X Tann t₁ S η ε : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        0 ≤ Tann → 2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW, UNTWISTED⟧
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        -- ⟦THE `𝒮`-SUPPORT⟧ in place of the density gate
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        -- ⟦THE RECONCILIATION GATES (R1), (R2)⟧ — (R4) is GONE
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        -- ⟦THE A3 CAPSTONE ROW, CARRIED⟧
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S ^ 2
              + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Ct * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hfeed⟩ := TLeg_feeds_capstone_gen
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4
    hcoefWS hasupp hlive hQXd hXdbig hcap
  -- ⟦THE FRAME'S OWN READS⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA2 : 2 ≤ A := le_trans (by norm_num) hF.A_floor
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hP1nat : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast hP1nat
    linarith
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith) (one_le_calQK A G M 1) hQ1Xd hv
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  have hasuppχ := chiBarCoeff_dyadic_supp χ hasupp
  -- ⟦THE ROW SLOT, AT THE FOUR-ROW STRICT/FUSED EXIT⟧
  have hrowfam : ∀ j ∈ Finset.Icc 1 Jb,
      (∫ t in (seamAnn X Tann \ seamBall X t₁)
            ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI (calH H1 j) (calP A G j) (calQK A G M j)).card : ℝ)
            * (∑ v ∈ ramI (calH H1 j) (calP A G j) (calQK A G M j),
                ∫ t in (seamAnn X Tann \ seamBall X t₁)
                    ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                        (mrAlpha η) Jb j,
                  ‖ramMain (calH H1 j) N Xd (calP A G j) (calQK A G M j)
                    (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) v t‖ ^ 2)
          + lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
              (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) := by
    intro j hj
    exact lemma12_on_TsetG_mr_windowed_end (chiBarCoeff q χ c) (calP A G) (calQK A G M)
      (calH H1) (mrAlpha η) Jb j (hHj j hj) N Xd hXd1 hNXd (hPj1 j)
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c)
      (chiBarCoeff_seamCoefWS χ (hcoefWS j hj)) (chiBarCoeff_bfam_le_one χ hb1 j)
      (chiBarCoeff_cseq_le_one χ hc1) (hasupp_real_of_nat hasuppχ) X Tann t₁ hT0
  have hleg := hfeed (chiBarCoeff q χ c) (chiBarCoeff q χ a)
    (fun j => chiBarCoeff q χ (bfam j)) (calP A G) (calQK A G M) (calH H1) η Jb N Xd
    (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c))
    hη hη6 hJb1 hXd1 hT0 hP1pos (levelGates_calibratedK hF) hH1two hP1nat
    (calP_le_calQK hM1 le_rfl) hbot1 (chiBarCoeff_bfam_le_one χ hb1)
    (chiBarCoeff_cseq_le_one χ hc1) hrowfam hcap
  -- ⟦THE PRICE OF `Σ_j lemma12RowsMR_end`, AT THE TWISTED `𝒮`-SUPPORTED DATUM⟧
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hK2 := sum_lemma12RowsMR_priced_chi_end_zero' Cp hCp q χ A G M Jb N Xd H1 Tann a c bfam
    hA2 hG1 hM1 hXd1 hNXd hT0 hF.H1_two hN4 hreg hXdbig ha1 hb1 hc1 hlive
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

set_option maxHeartbeats 400000 in
-- Same cause as `M4RowsChiEndPrime.m4_rowChi_weighed_end'`: the number-row hypothesis is
-- matched summand by summand against `m4MrowChiEnd'`.
/-- **⟦THE `hrowsSum` SLOT, DENSITY-FREE, AT THE `L²` NUMERAL⟧** (`m4_hrowsSum_chi_zero'`).
`M4RowsChiZero.m4_hrowsSum_chi_zero` landing in `M4RowsChiEndPrime.m4MrowChiEnd'`. -/
theorem m4_hrowsSum_chi_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X h η ε : ℝ)
        (t₁ S : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S χ ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ m4MrowChiEnd' Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, hCt, hnum⟩ := m4_rowChi_number_of_capstone_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoefWS
    hasupp hlive hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum Cp hCp q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoefWS hasupp hlive hQXd hXdbig
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed_end' hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

/-! ## §6 — THE DOOR INSTANCE

`M4RowsChiZero` §6 at the primed row constant.  `DoorRowZeroBase` and
`blockLive_winCutH_doorCoeffU` are that file's, REUSED unchanged — neither reads a `p²`
numeral. -/

/-- **⟦THE `a2Mrow'`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧**
(`m4_hrowsSum_chi_door_zero'`).  §5 at the door family and the vacuous ball, landed inside
`ThmA2Prime.a2Mrow'` at a FREE `Cp ≥ 0`. -/
theorem m4_hrowsSum_chi_door_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (3072 * M) j) (calQK (Adoor M) (3072 * M) M j)
            (winCutH Xd (doorCoeffU M)) (bfam j) c) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (3072 * M))
                      (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU M))) t‖ ^ 2)
            ≤ a2Mrow' Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU M)) bfam ha1 hb1 hc1 N Xd
    (Adoor M) (3072 * M) M 2 (H1door M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at M Xd hM hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow' hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE JOIN'S ROW CONSTANT⟧**
(`m4_hrowsSlot_at_door_zero'`).  The statement below is
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'`'s `hrows` binder VERBATIM at
`Cs ≡ Ct`, `Ccc ≡ Cp` with `Cp` a free nonnegative real — in particular at `Cp := 0`. -/
theorem m4_hrowsSlot_at_door_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ a2Mrow' Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum] using hslot

/-! ## §7 — ⟦ITEM 11 AT THE ZERO DENSITY AND THE FREE POOL⟧

This is where the three R4 threads meet: §6's `hrows` supplier (item 3), the primed row
constant `a2Mrow'` (item 1's genre), and `M4AssemblyPrime`'s pooled frame (⟦R2⟧).  The
assembly is parametric in `Ccc`, so the twin is one application at the free constant; the
point of the statement is what its `hframe` now READS — at `Cp := 0` the `gRows` field is

  `5760 · (a2RowsSum' M X_d + 0·(2/M)) ≤ π₀` ,

with the density debit gone AND the `p²` slot `X_d`-FREE. -/

/-- **⟦A4 — ITEM 11 AT A FREE DENSITY CONSTANT AND THE FREE POOL⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'`).
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` at §6's supplier:
`M4ChiSummed.M4ChiSummedFreeRow` at the joined door grade `a2DoorGrade_pool`, from `hM`,
`hb1`, `hc1`, `hframe` (`DoorFuseFrame_pool'`), `hbase` (`DoorRowZeroBase` — `dom`-free),
`hcap`, `hband`, `hpool`, `henv`.

⟦WHAT THIS DEMONSTRATES⟧ every `X_d`-decaying right-hand side inside the frame is gone (⟦R2⟧),
the `log₂(2X_d)` numerator that made `gRows` grow with the base is gone (⟦R1⟧), and the
`X_d ≳ (M j²)⁸` domination floor is gone (the zero chain's own bonus): `hbase` asks six
fields, none of which caps the base. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero' :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool' M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool' (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-! ## §GK — the G-lever twin

The density-free primed door page at `G := s13GK K M`.  `M4RowsChiZero.DoorRowZeroBase_gk`
and `blockLive_winCutH_doorCoeffU_gk` are reused unchanged.

⟦THE BLOCK IS CLEARED⟧ `m4_chiSummedFreeRow_of_doorAssembly_pool_zero'` (:744) was banked
BLOCKED on `M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'_gk`, which exists now;
the twin is landed in `§GK.wire` below — one `exact`, as predicted. -/

/-- **⟦THE `a2Mrow'`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧ AT THE
G-LEVER** (`m4_hrowsSum_chi_door_zero'_gk`).  Frame: `ThmA2.calFrameK_doorH1_at_gk`, whence
`K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_zero'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (s13GK K M) j) (calQK (Adoor M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_gk K M)) (bfam j) c) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (s13GK K M))
                      (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_gk K M))) t‖ ^ 2)
            ≤ a2Mrow'_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_gk K M)) bfam ha1 hb1 hc1 N Xd
    (Adoor M) (s13GK K M) M 2 (H1door M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_gk K hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE JOIN⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_zero'_gk`). -/
theorem m4_hrowsSlot_at_door_zero'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_gk] using hslot

-- #audit (temporary)


/-! ### §GK.wire — THE BLOCKED ASSEMBLY WIRE, LANDED

⟦THE BLOCK ABOVE IS CLEARED⟧ `M4Assembly` / `M4AssemblyPrime` grew their own `§GK`
(`DoorFuseFrame_gk`, `DoorFuseFrame_pool'_gk`, `m4_chiFreeRowSq_sum_at_door_gk`,
`m4_chiSummedFreeRow_of_doorAssembly{,_pool'}_gk`), so the wire below is the landed proof
with those names substituted.  `hK : K ≤ 1.7·10⁸` is the slot supplier's frame side
condition, inherited. -/

/-- **THE FUSE, DENSITY-FREE, AT THE LEVER** —
`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'` (:744). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool'_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowZeroBase_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

end Salt.MR
