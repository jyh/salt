/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEngineRoute

/-!
# HB-L2c master assembly — fully unconditional (CHI-SIEVE freeze, Wave 2)

This leaf closes the `L2c` campaign **fully unconditionally**.  With
`hb_l2c_master_unconditional` the Heath–Brown Lemma-2 conclusion holds at the bare
four-hypothesis packet `{hsq, hz100, hz8, hzx}` — no `hcount`, no `hLz0`, no residual
anywhere.  Both of the two named residuals of the landed conditional master
(`hb_l2c_master_of_count`, `hb_l2c_master_final`) are now discharged by the χ-blind engine
route of Wave 1 (`L2cEngineRoute`): the `E_R` swap count and the class-(c) minus-prime-pair
count both land in the master's `J1` row through the frozen unconditional engine
`hb_lemma8'_unconditional`, `PretenseSum`-free.  The paper's conditional table loses a row.

* **`EL_uncov_bound_unconditional`** — the `E_L` odd-cover residual `L2cELuncov`, composed
  from the cover `ELodd_cover'` with the class-(a) mirror `EL_TmirrorT2_bound`, the class-(b)
  mid-squarefull `L2cMid_bound`, and Wave 1's new sharp class-(c) row
  `cPairSum_bound_unconditional` — now with the class-(c) budget in `J1` (`2^21·(x/z₀)`)
  rather than under `hLz0`.
* **`hb_l2c_master_unconditional`** — the master conclusion, **character-for-character** the
  landed `hb_l2c_master_of_count` conclusion (`L2cMaster.lean:377-382`).  Its proof mirrors
  `L2cMaster.lean:383-454`: the same structural chain, the same five cover lemmas, the same
  public rows `r1`–`r11`, `r13`; `r12` becomes `ER_Tsw'_bound_unconditional` and `hEL_uncov`
  becomes `EL_uncov_bound_unconditional`.  The `J1` tally is `2^30 + 4 + 2^22 < 2^31`.

Single-writer file (`L2cMasterUncond.lean`); imports `L2cEngineRoute`, touches no other file,
and adds no axioms.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-- **The unconditional `E_L` odd-cover residual bound.**  The mirror of `EL_uncov_bound`
    (`L2cMop`) with the class-(c) row routed through the χ-blind engine: `L2cELuncov` composes
    the cover `ELodd_cover'` `(a)∪(b)∪(c)` with `EL_TmirrorT2_bound` (class (a), `17915904 ≤
    2^26`), `L2cMid_bound` (class (b), junk at `1`), and `cPairSum_bound_unconditional`
    (class (c), the new sharp `J1` row `2^21·(x/z₀)` plus `x^{9/10}·L'³` junk).  No `hLz0`. -/
theorem EL_uncov_bound_unconditional (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    L2cELuncov χ z x
      ≤ 2 ^ 26 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
        + 2 ^ 21 * ((x : ℝ) / z0 z x)
        + Real.exp (2 * z0 z x)
            * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz0nn : 0 ≤ z0 z x := z0_nonneg hz2
  have hcover := ELodd_cover' (x := x) χ hsq hz100
  have ha := EL_TmirrorT2_bound χ hsq hz100 hz8 hzx
  have hb := L2cMid_bound χ hsq hz100 hz8 hzx
  have hc := cPairSum_bound_unconditional χ hsq hz100 hzx
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := pretenseSum_nonneg χ _
  have hA0 : 0 ≤ (x : ℝ) / Lwin x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) :=
    mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg x) (Lwin_nonneg x))
      (Real.exp_pos _).le) hPS0
  have hexp2ge1 : (1 : ℝ) ≤ Real.exp (2 * z0 z x) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hz0nn])
  have hP9 : 0 ≤ (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _) (pow_nonneg (Lwin_nonneg x) 3)
  have hbridge : (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3
      ≤ Real.exp (2 * z0 z x) * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by
    nlinarith [hexp2ge1, hP9]
  linarith [hcover, ha, hb, hc, hA0, hbridge]

open Classical in
/-- **THE MASTER, FULLY UNCONDITIONAL.**  The `hb_lemma2` conclusion shape on the exact
    identity, from the bare four-hypothesis packet `{hsq, hz100, hz8, hzx}` — **no** `hcount`,
    **no** `hLz0`, no residual.  With this theorem the `L2c` campaign closes fully
    unconditional: the two named residuals of `hb_l2c_master_of_count`/`_final` are both
    discharged by the χ-blind engine route of Wave 1 (`ER_Tsw'_bound_unconditional` for the
    `E_R` swap count, `EL_uncov_bound_unconditional` for the `E_L` mop-up), landing in `J1`
    and `PretenseSum`-free.  The conclusion is **character-for-character** the landed
    `hb_l2c_master_of_count` conclusion (`L2cMaster.lean:377-382`); the proof mirrors
    `L2cMaster.lean:383-454`, with `r12 := ER_Tsw'_bound_unconditional` and
    `hEL_uncov := EL_uncov_bound_unconditional`.  The `J1` tally is `2^30 + 4 + 2^22 < 2^31`. -/
theorem hb_l2c_master_unconditional (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    S2 χ (l2cWindow χ z x) - S1 (l2cWindow χ z x)
      ≤ L2cCmain * ((x : ℝ) / z0 z x)
        + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
            * PretenseSum χ (2 * x + 2)
        + L2cCmain * Real.exp (2 * z0 z x)
            * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3 := by
  classical
  rw [L2cCmain]
  -- scale facts
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz100R : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
    calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by norm_num
      _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hz100R 3
      _ ≤ (x : ℝ) := hzx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48
  have hxgt1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48
  have hx2N : 2 ≤ x := by
    have : (2 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48; exact_mod_cast this
  have hLwin1 : (1 : ℝ) ≤ Lwin x := one_le_Lwin (by omega)
  have hlogxpos : 0 < Real.log x := Real.log_pos hxgt1
  have hlogx_le : Real.log x ≤ Lwin x := by
    rw [Lwin]; exact Real.log_le_log (by linarith) (by linarith)
  have hz0nn : 0 ≤ z0 z x := z0_nonneg hz2
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := pretenseSum_nonneg χ _
  have hexp5 : 0 ≤ Real.exp (5 * z0 z x) := (Real.exp_pos _).le
  have hexp2 : 0 ≤ Real.exp (2 * z0 z x) := (Real.exp_pos _).le
  have hexp2ge1 : (1 : ℝ) ≤ Real.exp (2 * z0 z x) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hz0nn])
  have hL3 : 0 ≤ Lwin x ^ 3 := by positivity
  have hXZ : 0 ≤ (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) :=
    div_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hX9 : 0 ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  -- the J2 conversion `x/L' ≤ x/log x`
  have hA2 : (x : ℝ) / Lwin x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
      ≤ (x : ℝ) / Real.log x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
    have hxL : (x : ℝ) / Lwin x ≤ (x : ℝ) / Real.log x :=
      div_le_div_of_nonneg_left (by linarith) hlogxpos hlogx_le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxL hexp5) hPS0
  -- the squarefull → `x^{9/10}` junk conversion
  have hsqf : 2 * Real.sqrt (2 * (x : ℝ)) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x)
      ≤ 4 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
    have ha : 2 * Real.sqrt (2 * (x : ℝ)) ≤ 4 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
      linarith [master_sqrt_le (x := x) hx1]
    have hb : Lwin x ^ 2 ≤ Lwin x ^ 3 := by nlinarith [hLwin1]
    have hc : Real.exp (0.7 * z0 z x) ≤ Real.exp (2 * z0 z x) :=
      Real.exp_le_exp.mpr (by nlinarith [hz0nn])
    have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
    calc 2 * Real.sqrt (2 * (x : ℝ)) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x)
        ≤ 4 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 * Real.exp (2 * z0 z x) :=
          mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) hc
            (Real.exp_pos _).le (mul_nonneg (by positivity) (pow_nonneg hL0 3))
      _ = 4 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by ring
  -- the `x^{9/10}·L'³` bridge for `r12`'s bare junk row (`e^{2z₀} ≥ 1`)
  have hr12j : (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3
      ≤ Real.exp (2 * z0 z x) * ((x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3) := by
    nlinarith [hexp2ge1, mul_nonneg hX9 hL3]
  -- the structural chain
  have hexact := S2_sub_S1_exact χ (l2cWindow χ z x)
  rw [overshoot_eq_EL_add_ER χ z x] at hexact
  have hELeven := EL_le_ELodd_add_even χ hsq z x
  have hELcov := ELodd_cover χ hsq z x
  have hERcov := E_R_cover χ hsq (z := z) (x := x) hx2N
  -- the row bounds
  have r1 := EL_T1_bound χ hsq hz100 hz8 hzx
  rw [T1Cmain] at r1
  have r2 := EL_T2_bound χ hsq hz100 hz8 hzx
  have r3 := EL_T3F_bound χ hsq hz100 hz8 hzx
  have r4 := EL_Tsw_bound χ hsq hz100 hz8 hzx
  have r5 := EL_cJunk_bound χ hsq hz100 hz8 hzx
  have r6 := EL_corners_bound χ hsq hz100 hz8 hzx
  have r7 := EL_evenCorner_bound χ hsq hz100 hz8 hzx
  have r8 := ER_squarefull_junk χ hsq hz2 (z := z) (x := x)
  have r9 := ER_T1'_bound_mixed χ hsq hz100 hz8 hzx
  have r10 := ER_T2'_bound χ hsq hz100 hz8 hzx
  have r11 := ER_T3'_bound χ hsq hz100 hz8 hzx
  have r12 := ER_Tsw'_bound_unconditional χ hsq hz100 hzx
  have r13 := ER_wJunk_bound χ hsq hz100 hz8 hzx
  have hEL_uncov := EL_uncov_bound_unconditional χ hsq hz100 hz8 hzx
  linarith [hexact, hELeven, hELcov, hERcov, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    r12, r13, hEL_uncov, hA2, hsqf, hr12j, hPS0, hexp5, hexp2, hL3, hXZ, hX9,
    mul_nonneg (mul_nonneg
      (div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) (Lwin_nonneg x)) hexp5) hPS0,
    mul_nonneg (mul_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) hlogxpos.le) hexp5) hPS0,
    mul_nonneg (mul_nonneg hexp2 hXZ) hL3, mul_nonneg (mul_nonneg hexp2 hX9) hL3,
    div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) hz0nn]

end Salt.HB
