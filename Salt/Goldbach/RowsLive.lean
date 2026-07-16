/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Op
import Salt.Goldbach.BoxRows3
import Salt.Chen.ChenRows1
import Salt.Chen.PriceClose

/-!
# G-ROWSLIVE — the live-geometry discharge of `gold_box_price_live_kerr`'s analytic rows (Goldbach)

Design: the pilot ledger's live-geometry insight.  `gold_box_price_live_kerr` (BoxRows3 §1)
collapses the LIVE-branch two-cutoff box price onto the twin's closed `boxPriceKerr Kc kp i`, but
leaves ~24 parametric hypotheses (the "residual rows") that the twin derives from its GLOBAL window
`(x/2+1, x]` and that do **not** transfer verbatim to a per-annulus box (whose `X·M ≈ goldCut N ka`
lives at the annulus scale, not the global `x`-scale).  This file supplies the honest per-annulus
live-geometry derivation of each residual row at the operating point (`Ne := N`, `z := opZ N`,
`y := opY N`), mirroring the twin's `ChenRows1.box_rows_at_op`.

## The residual row inventory (deliverable 1)

`gold_box_price_live_kerr`'s hypothesis list, after `gold_box_price_engine_at_live_z` (D0Win2 §3)
internally discharges the nine `hD0*` rows + `hM2N`/`hNM`, is (in binder order):

* **structural / at-op-trivial:** `hNe` (`2 ≤ N`), `hi` (the box), `hlive` (LIVE), `hk` (`2 ≤ kp`).
* **z-geometry (the D0Win2-specific novel content):** `hz1` (`1 ≤ z`), `hz_ratio`
  (`6·log(8z)+15 ≤ log(goldCut N (ka+1))`), `hx` (`exp(10⁹) ≤ goldCut N (ka+1)`),
  `hDge` (`(goldCut N (ka+1)/(8z))^{1/2} ≤ D`).  §1–§2.
* **carrier / Dset (reused verbatim from the twin):** `hβ` (`norm_box_leg_le_one`), `hd1`
  (`one_le_of_mem_QImage`), `hcop2` (`gold_crtClassG_coprime_of_mem`), `hDsetD`
  (`le_D_of_mem_QImage`), `hN₀` (from the k-floor).  Discharged at the assembly, not here.
* **analytic L-scale rows (the honest live-geometry derivations, §3–§4):** `hL1`, `hD1`, `hDsq`,
  `habs`, `hX2`, `hM2`, `hDscale`, `hXsqrt`, `hMsqrt`, `herr_lev`, `herr_Mlev`, `hFX`, `hDx`,
  `hLbb`, `hfloor`, `herr_LEpos`, `hDXM`, `herr_scale`.

## The live-geometry keystones (what makes the rows TRUE at live boxes)

A LIVE box (`2^i < z·pieceN kp + 1`) in the annulus boundary forces, via the boundary `F`-floor
`z·y < 2^{i+1}` and the corner `2^i·2^kp ≤ goldCut N (ka+1)`:

* `X = 2^{i+1}−1 ≥ z·y ≥ N^{11/24}/4` (`hFX` + `zy_floor_ge`): so `√X ≥ N^{11/48}/2 ≫` poly-log.
* `2^kp ≥ (goldCut N (ka+1)/(8z))^{1/2} ≥ opY N/√32` (`gold_kfloor_live_z` +
  `gold_live_annulus_lower`): so `√(pieceM kp) ≥ N^{1/6}/√12 ≫` poly-log.
* `goldCut N (ka+1) > z·y²/4 ≥ N^{19/24}/32` (`gold_live_annulus_lower`): so `log(goldCut)`
  clears both the tower threshold `exp(10⁹)` and the `(8z)⁶` ratio (the `N^{1/24}` margin).
* `X·M ≤ 4·goldCut N (ka+1) ≤ 2N` (`gold_box_XM_scale` + `goldCut_le_half`): so `L = log(X·M)
  ≤ log(2N)`, keeping every poly-log `L^E ≤ N^{1/2000}·const`.

The margins are `N`-power vs poly-log throughout: honest routing, not tightropes.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. The operating-point scale bundle

The `opZ N`/`opY N` floor + log bounds this file threads through every row, re-exported from
`gold_op_count_rows` (Op §8) at a tower threshold `log N ≥ 2·10⁹` (`a12_log_ge`).  Everything
downstream is a `linarith`/monotonicity consequence of these. -/

/-- **`gold_op_scales` (§0).**  Past a tower threshold: the `opZ N`/`opY N` floor bounds
(`N^{1/8}/2 ≤ opZ N ≤ N^{1/8}`, `N^{1/3}/2 ≤ opY N ≤ N^{1/3}`), the log bounds
(`log N/8 − log 2 ≤ log(opZ N) ≤ log N/8`, `log N/3 − log 2 ≤ log(opY N)`), and `2·10⁹ ≤ log N`. -/
theorem gold_op_scales : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    2 ≤ N ∧ 1 ≤ opZ N ∧ 6 ≤ opY N ∧
    Real.log (opZ N : ℝ) ≤ Real.log N / 8 ∧
    Real.log N / 8 - Real.log 2 ≤ Real.log (opZ N : ℝ) ∧
    Real.log N / 3 - Real.log 2 ≤ Real.log (opY N : ℝ) ∧
    (2 * 10 ^ 9 : ℝ) ≤ Real.log N ∧
    (opZ N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧ (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (opZ N : ℝ) ∧
    (opY N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) ∧ (N : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ (opY N : ℝ) ∧
    Real.exp 4000 ≤ (N : ℝ) ∧ (64 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
  obtain ⟨xc, hc⟩ := gold_op_count_rows
  obtain ⟨xt, ht⟩ := a12_log_ge (2 * 10 ^ 9)
  refine ⟨max (max xc xt) 2, fun N hN => ?_⟩
  have hxc : xc ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxt : xt ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hy6, _, hx1, hzR2, hzRyR, hlogz, hlogy, hZle, hZge, hYle, hYge⟩ := hc N hxc
  obtain ⟨_, hlogN⟩ := ht N hxt
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- floor bounds
  have hZhalf : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (opZ N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := hzR2
    linarith [hZge]
  have hYhalf : (N : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ (opY N : ℝ) := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := le_trans hzR2 hzRyR
    linarith [hYge]
  have hZ1R : (1 : ℝ) ≤ (opZ N : ℝ) := by linarith [hZge, hzR2]
  have hZ1 : 1 ≤ opZ N := by exact_mod_cast hZ1R
  -- log bounds
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by linarith
  have hYpos : (0 : ℝ) < (opY N : ℝ) := by
    have : (6 : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hy6
    linarith
  have hlogZ_le : Real.log (opZ N : ℝ) ≤ Real.log N / 8 := by
    have := Real.log_le_log hZpos hZle; rwa [hlogz] at this
  have hlogZ_ge : Real.log N / 8 - Real.log 2 ≤ Real.log (opZ N : ℝ) := by
    have hmono : Real.log ((N : ℝ) ^ ((1 : ℝ) / 8) / 2) ≤ Real.log (opZ N : ℝ) :=
      Real.log_le_log (by positivity) hZhalf
    rw [Real.log_div (by positivity) (by norm_num), hlogz] at hmono
    linarith
  have hlogY_ge : Real.log N / 3 - Real.log 2 ≤ Real.log (opY N : ℝ) := by
    have hmono : Real.log ((N : ℝ) ^ ((1 : ℝ) / 3) / 2) ≤ Real.log (opY N : ℝ) :=
      Real.log_le_log (by positivity) hYhalf
    rw [Real.log_div (by positivity) (by norm_num), hlogy] at hmono
    linarith
  -- `exp 4000 ≤ N` (`4000 ≤ log N`)
  have hexp4000 : Real.exp 4000 ≤ (N : ℝ) := by
    calc Real.exp 4000 ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr (by linarith [hlogN])
      _ = (N : ℝ) := Real.exp_log hNpos
  -- `64 ≤ N^{1/3}` (`log 64 ≤ (1/3)·log N`)
  have hN13_16 : (64 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have hlog64 : Real.log 64 ≤ 6 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      push_cast; linarith
    calc (64 : ℝ) = Real.exp (Real.log 64) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log ((N : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply Real.exp_le_exp.mpr; rw [Real.log_rpow hNpos]; linarith [hlogN]
      _ = (N : ℝ) ^ ((1 : ℝ) / 3) := Real.exp_log (Real.rpow_pos_of_pos hNpos _)
  exact ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩

/-! ## 1. The z-geometry rows `hz_ratio` / `hx` (the D0Win2 live-geometry inputs, deliverable 2)

The two `goldCut`-lower-bound rows `gold_box_price_live_kerr` consumes.  Both come from
`gold_live_annulus_lower` (`z·y² < 4·goldCut N (ka+1)`, D0Win2 §0) fed the op log scales:
`log(goldCut) > log(z) + 2·log(y) − log 4 ≥ 19·log N/24 − const`, dwarfing both the tower `10⁹`
(`hx`) and the ratio `6·log(8z)+15 ≈ 3·log N/4 + const` (`hz_ratio`, margin `N^{1/24}`). -/

/-- **`gold_box_zx_rows` (§1).**  At op, a LIVE annulus box satisfies `hz1` (`1 ≤ opZ N`),
`hz_ratio` (`6·log(8·opZ N)+15 ≤ log(goldCut N (ka+1))`), and `hx` (`exp(10⁹) ≤ goldCut N (ka+1)`)
— the three z-geometry inputs, from `gold_live_annulus_lower` + `gold_op_scales`. -/
theorem gold_box_zx_rows : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K : ℕ),
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
        (opZ N * opY N) K →
      2 ^ i < opZ N * pieceN kp + 1 →
      1 ≤ opZ N ∧
      6 * Real.log (8 * (opZ N : ℝ)) + 15 ≤ Real.log (goldCut N (ka + 1) : ℝ) ∧
      Real.exp (10 ^ 9) ≤ (goldCut N (ka + 1) : ℝ) := by
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨xs, fun N hN kp ka i K hi hlive => ?_⟩
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, _, hlogY_ge, hlogN, _, _, _, _⟩ := hs N hN
  -- the honest live-box lower bound `z·y² < 4·goldCut` (D0Win2 §0)
  have hlow := gold_live_annulus_lower hN2 hi hlive
  -- positivity + the real lower bound `opZ N·(opY N)² < 4·goldCut`
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast (by omega : 0 < opZ N)
  have hYpos : (0 : ℝ) < (opY N : ℝ) := by exact_mod_cast (by omega : 0 < opY N)
  have hgcPos : (0 : ℝ) < (goldCut N (ka + 1) : ℝ) := by
    have h1 : 1 ≤ goldCut N (ka + 1) := one_le_goldCut hN2 (ka + 1)
    exact_mod_cast (by omega : 0 < goldCut N (ka + 1))
  have hlowR : (opZ N : ℝ) * ((opY N : ℝ) * (opY N : ℝ)) < 4 * (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast hlow
  -- take logs: `log(z·y²) < log(4·goldCut) = log 4 + log goldCut`
  have hprodPos : (0 : ℝ) < (opZ N : ℝ) * ((opY N : ℝ) * (opY N : ℝ)) := by positivity
  have hloglow : Real.log ((opZ N : ℝ) * ((opY N : ℝ) * (opY N : ℝ)))
      ≤ Real.log (4 * (goldCut N (ka + 1) : ℝ)) := Real.log_le_log hprodPos hlowR.le
  rw [Real.log_mul (ne_of_gt hZpos) (by positivity),
    Real.log_mul (ne_of_gt hYpos) (ne_of_gt hYpos),
    Real.log_mul (by norm_num) (ne_of_gt hgcPos)] at hloglow
  -- `log(opZ N) + 2·log(opY N) − log 4 ≤ log(goldCut)`
  have hlogGC : Real.log (opZ N : ℝ) + 2 * Real.log (opY N : ℝ) - Real.log 4
      ≤ Real.log (goldCut N (ka + 1) : ℝ) := by linarith [hloglow]
  -- numeric slack: `log 2, log 4, log 8` bounded above
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog8eq : Real.log (8 * (opZ N : ℝ)) = Real.log 8 + Real.log (opZ N : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hZpos)
  have hlog8 : Real.log 8 ≤ 3 := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    rw [h8]; linarith [hlog2]
  -- assemble hz_ratio and hx
  refine ⟨hZ1, ?_, ?_⟩
  · -- hz_ratio
    rw [hlog8eq]
    -- 6·(log 8 + log z) + 15 ≤ log z + 2·log y − log 4  ⇐  log N/24 ≥ const
    have key : Real.log (opZ N : ℝ) + 2 * Real.log (opY N : ℝ) - Real.log 4
        ≥ 6 * (Real.log 8 + Real.log (opZ N : ℝ)) + 15 := by
      -- use log z ≤ log N/8, log y ≥ log N/3 − log 2
      linarith [hlogZ_le, hlogY_ge, hlogN, hlog2, hlog4, hlog8]
    linarith [hlogGC, key]
  · -- hx : exp(10^9) ≤ goldCut
    have h109 : (10 : ℝ) ^ 9 ≤ Real.log (goldCut N (ka + 1) : ℝ) := by
      have key : Real.log (opZ N : ℝ) + 2 * Real.log (opY N : ℝ) - Real.log 4 ≥ (10 : ℝ) ^ 9 := by
        linarith [hlogZ_le, hlogY_ge, hlogN, hlog2, hlog4]
      linarith [hlogGC, key]
    calc Real.exp (10 ^ 9) ≤ Real.exp (Real.log (goldCut N (ka + 1) : ℝ)) :=
          Real.exp_le_exp.mpr h109
      _ = (goldCut N (ka + 1) : ℝ) := Real.exp_log hgcPos

/-! ## 2. The numeric engine (local `N`-scale mirrors of `ChenRows1`'s private toolkit)

The three private helpers behind every poly-log-vs-power close, re-exported at the global scale
`N` (the twin's are keyed to its window `x`; `private`, hence not importable). -/

/-- `(27/10)^n ≤ N^c` whenever `n ≤ c·10⁹` (`c > 0`), at `log N ≥ 10⁹`.  Mirror of
`row_const_le_rpow`. -/
private theorem gold_const_le_rpow {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hn : (n : ℝ) ≤ c * 10 ^ 9) : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ c := by
  have hmul : c * (10 ^ 9 : ℝ) ≤ c * Real.log N := mul_le_mul_of_nonneg_left hlogN hc.le
  calc ((27 : ℝ) / 10) ^ n ≤ Real.exp (n : ℝ) := a12_pow27_le_exp n
    _ ≤ Real.exp (c * Real.log N) := Real.exp_le_exp.mpr (by linarith [hn, hmul])
    _ = (N : ℝ) ^ c := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

/-- `C·N^a ≤ N^b` for `a < b`, `C ≤ (27/10)^n ≤ N^{b−a}`.  Mirror of `row_mono_close`. -/
private theorem gold_mono_close {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {a b C : ℝ} {n : ℕ} (hab : a < b)
    (hC : C ≤ ((27 : ℝ) / 10) ^ n) (hnc : (n : ℝ) ≤ (b - a) * 10 ^ 9) :
    C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have hstep : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ (b - a) :=
    gold_const_le_rpow hNpos hlogN (by linarith) n hnc
  have hann : (0 : ℝ) ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
  calc C * (N : ℝ) ^ a ≤ ((27 : ℝ) / 10) ^ n * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hC hann
    _ ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hstep hann
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- The poly-log-power bound at the box log `L` (`0 ≤ L ≤ 2·log N`): `L^E ≤ 262144·N^{1/2000}` for
`0 ≤ E ≤ 18`.  Mirror of `row_Lpow_le`. -/
private theorem gold_Lpow_le {N : ℕ} {L : ℝ} (hlogN1 : 1 ≤ Real.log N)
    (hL0 : 0 ≤ L) (hLle : L ≤ 2 * Real.log N)
    (hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000))
    {E : ℝ} (hE0 : 0 ≤ E) (hE18 : E ≤ 18) :
    L ^ E ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
  have h218 : (2 : ℝ) ^ (18 : ℝ) = 262144 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc L ^ E ≤ (2 * Real.log N) ^ E := Real.rpow_le_rpow hL0 hLle hE0
    _ = (2 : ℝ) ^ E * (Real.log N) ^ E := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ (18 : ℝ) * (Real.log N) ^ (18 : ℝ) := by
        refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE18)
          (Real.rpow_le_rpow_of_exponent_le hlogN1 hE18)
          (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
        rw [h218]; exact mul_le_mul_of_nonneg_left hpl (by norm_num)

/-! ## 3. The live-geometry `X`/`M` floors (the honest lower bounds the poly-log rows clear)

`√X ≥ N^{11/48}/2` (X ≥ z·y ≥ N^{11/24}/4, via the F-floor + `zy_floor_ge`) and
`M ≥ N^{1/3}/16` (`2^kp ≥ opY N/√32`, via `gold_kfloor_live_z` + `gold_live_annulus_lower`).  Both
are `N`-powers, dwarfing every `L^E ≤ 262144·N^{1/2000}`. -/

/-- **`gold_box_Ffloor`.**  The boundary `F`-floor clause `opZ N·opY N < 2^{i+1}` (⟹ `F ≤ X`). -/
theorem gold_box_Ffloor {N K kp ka i : ℕ}
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
      (opZ N * opY N) K) :
    opZ N * opY N < 2 ^ (i + 1) := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  exact hi.2.2.1

/-- **`gold_box_Xfloor`.**  For a boundary box at op, `N^{11/24}/4 ≤ (2^{i+1}−1 : ℝ)` (`X ≥ F` +
`zy_floor_ge`). -/
theorem gold_box_Xfloor {N K kp ka i : ℕ} (hx200 : Real.exp 200 ≤ (N : ℝ))
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
      (opZ N * opY N) K) :
    (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
  have hFfloor := gold_box_Ffloor hi
  have hFX : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := by omega
  have hzy := zy_floor_ge hx200
  -- `opZ N = ⌊N^{1/8}⌋`, `opY N = ⌊N^{1/3}⌋` definitionally
  have hFX' : (⌊(N : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(N : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) ≤ 2 ^ (i + 1) - 1 :=
    hFX
  exact le_trans hzy (by exact_mod_cast hFX')

/-- **`gold_box_Mfloor`.**  For a LIVE boundary box at op, `N^{1/3}/16 ≤ (pieceM kp : ℝ)`.
`2^kp ≥ (goldCut/(8z))^{1/2} ≥ (opY N)/√32` (`gold_kfloor_live_z` + `gold_live_annulus_lower`),
and `opY N ≥ N^{1/3}/2` (`gold_op_scales`); `√32 < 8`, so `N^{1/3}/2/8 = N^{1/3}/16`. -/
theorem gold_box_wge {N K kp ka i : ℕ} (hN2 : 2 ≤ N) (hZ1 : 1 ≤ opZ N)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
      (opZ N * opY N) K)
    (hlive : 2 ^ i < opZ N * pieceN kp + 1)
    (hYhalf : (N : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ (opY N : ℝ)) :
    (N : ℝ) ^ ((1 : ℝ) / 3) / 16
      ≤ ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) := by
  have hlow := gold_live_annulus_lower hN2 hi hlive -- z·y² < 4·goldCut
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  have h8zpos : (0 : ℝ) < 8 * (opZ N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set t : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3) with htdef
  have htpos : (0 : ℝ) < t := Real.rpow_pos_of_pos hNpos _
  have hYpos : (0 : ℝ) < (opY N : ℝ) := by linarith [hYhalf, htpos]
  have hlowR : (opZ N : ℝ) * ((opY N : ℝ) * (opY N : ℝ)) < 4 * (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast hlow
  -- `(t/16)² ≤ goldCut/(8z)` (from `goldCut > z·y²/4` and `y ≥ t/2`)
  have hsqy : (t / 2) * (t / 2) ≤ (opY N : ℝ) * (opY N : ℝ) :=
    mul_le_mul hYhalf hYhalf (by positivity) hYpos.le
  have hzsq : (opZ N : ℝ) * ((t / 2) * (t / 2)) ≤ (opZ N : ℝ) * ((opY N : ℝ) * (opY N : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqy hZpos.le
  have hsq : (t / 16) * (t / 16) ≤ (goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ)) := by
    rw [le_div_iff₀ h8zpos]
    nlinarith [hlowR, hzsq, hZpos, htpos]
  -- take the `^{1/2}`: `t/16 ≤ (goldCut/(8z))^{1/2}`
  have h1 : ((t / 16) * (t / 16)) ^ ((1 : ℝ) / 2) = t / 16 := by
    rw [show (t / 16) * (t / 16) = (t / 16) ^ (2 : ℕ) by ring,
      ← Real.rpow_natCast (t / 16) 2, ← Real.rpow_mul (by positivity),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  rw [← h1]; exact Real.rpow_le_rpow (by positivity) hsq (by norm_num)

/-- **`gold_box_Mfloor`.**  For a LIVE boundary box at op, `N^{1/3}/16 ≤ (pieceM kp : ℝ)`
(`gold_box_wge` + `gold_kfloor_live_z` + `two_pow_le_pieceM`). -/
theorem gold_box_Mfloor {N K kp ka i : ℕ} (hN2 : 2 ≤ N) (hZ1 : 1 ≤ opZ N)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
      (opZ N * opY N) K)
    (hlive : 2 ^ i < opZ N * pieceN kp + 1)
    (hYhalf : (N : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ (opY N : ℝ)) :
    (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ (pieceM kp : ℝ) := by
  have hkf := gold_kfloor_live_z hN2 hi hlive
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  linarith [le_trans (gold_box_wge hN2 hZ1 hi hlive hYhalf) hkf, hMge2kp]

/-! ## 4. The box-price leg at the operating point (deliverable 3)

`gold_box_rows_at_op` discharges EVERY residual analytic row of `gold_box_price_live_kerr` at a LIVE
annulus box (op values `Ne := N`, `z := opZ N`, `y := opY N`, `x := N`, `Lb := log(4N)`,
`F := opZ N·opY N`) with a **per-annulus** sieve level `D ∈ [w, 2w]`,
`w := (goldCut N (ka+1)/(8·opZ N))^{1/2}` — so the two-cutoff box price collapses onto the twin's
closed `boxPriceKerr Kc kp i`, arg-free but for the carrier/Dset rows (`hβ`/`hd1`/`hcop2`/`hDsetD`,
reused verbatim from the twin at the assembly).

**The per-annulus `D` (handoff note).**  `hDge`/`hDscale` force `D ≈ w ≈ √goldCut/√z`, an
annulus-scaled level: `hDge` (`w ≤ D`) needs `D ≥ √goldCut/√(8z)`, while `hDscale`
(`D·L^{15} ≤ √(X·M)`) needs `D ≤ √(X·M)/L^{15} ≈ √goldCut/L^{15}`; the window is non-empty because
`L^{15} ≤ √z` (poly-log vs `N^{1/16}`).  A single GLOBAL `D` (as the `QR·Dlev` conductor of
`gold_hBVblocksW_discharge'`) cannot meet `hDge` on the top annulus (`√(N/2)/√(8z) ≈ N^{7/16}`) and
`hDscale` on the low edge of a live annulus (`√(N^{19/24})/L^{15} ≈ N^{19/48}`) simultaneously
(`N^{21/48} > N^{19/48}`); the box-price leg therefore requires the per-annulus level, which the
final assembly (`G-ASM`) must thread — see the report. -/

set_option maxHeartbeats 4000000 in
-- The ~24-row live-geometry discharge elaborates a long rpow/sqrt-bearing chain and applies the
-- 39-hypothesis `gold_box_price_live_kerr`; the whnf/defeq checks need headroom above the default.
/-- **`gold_box_rows_at_op` (§4).**  At a LIVE annulus box at op with a per-annulus sieve level
`w ≤ D ≤ 2·w`, the two-cutoff box price is `≤ boxPriceKerr Kc kp i` — every residual analytic row of
`gold_box_price_live_kerr` discharged from the live geometry.  Only the carrier/Dset rows
(`hβ`/`hd1`/`hcop2`/`hDsetD`) remain, supplied by the assembly. -/
theorem gold_box_rows_at_op : ∃ (Kc : ℝ) (x₁ : ℕ), 0 < Kc ∧
    ∀ (N : ℕ), x₁ ≤ N →
      ∀ (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (T₁ T₂ ka i K : ℕ),
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
          (opZ N * opY N) K →
        2 ^ i < opZ N * pieceN kp + 1 →
        ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
        (D : ℝ) ≤ 2 * ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) →
        (∀ m, ‖β m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) → (∀ d ∈ Dset, d ≤ D) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
                (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
          ≤ boxPriceKerr Kc kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_live_kerr
  obtain ⟨xs, hs⟩ := gold_op_scales
  obtain ⟨xz, hzrows⟩ := gold_box_zx_rows
  obtain ⟨xp, hp⟩ := a12_logpow_le_rpow 18 (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨Kc, max (max (max xs xz) xp) ((16 * N₀) ^ 3 + 1), hKc, ?_⟩
  intro N hN β kp D Dset r T₁ T₂ ka i K hi hlive hDge hDhi hβ hd1 hcop2 hDsetD
  have hxs : xs ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxz : xz ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxp : xp ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hbigN : (16 * N₀) ^ 3 + 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩ := hs N hxs
  obtain ⟨_, hz_ratio, hx⟩ := hzrows N hxz kp ka i K hi hlive
  have hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := hp N hxp
  -- basic positivity + tower facts
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by linarith [hlogN]
  have hlogN9 : (10 : ℝ) ^ 9 ≤ Real.log N := by linarith [hlogN]
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  have h8zpos : (0 : ℝ) < 8 * (opZ N : ℝ) := by positivity
  have hgc1 : 1 ≤ goldCut N (ka + 1) := one_le_goldCut hN2 (ka + 1)
  have hgcPos : (0 : ℝ) < (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < goldCut N (ka + 1))
  -- `w := (goldCut/(8z))^{1/2}`, `w² = goldCut/(8z)`, `N^{1/3}/16 ≤ w ≤ 2^kp`
  set w : ℝ := ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) with hwdef
  have hwnn : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hw2 : w * w = (goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ)) := by
    rw [hwdef, ← Real.rpow_add (by positivity), show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num,
      Real.rpow_one]
  have hwkf : w ≤ ((2 ^ kp : ℕ) : ℝ) := gold_kfloor_live_z hN2 hi hlive
  have hwge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ w := gold_box_wge hN2 hZ1 hi hlive hYhalf
  -- box-scale geometry
  have hXMlo_nat : goldCut N ka < (2 ^ (i + 1) - 1) * pieceM kp := (gold_box_XM_scale hi).1
  have hXMhi_nat : (2 ^ (i + 1) - 1) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi).2
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  have hXge : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
    gold_box_Xfloor (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hexp4000) hi
  have hMfloor : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ (pieceM kp : ℝ) :=
    gold_box_Mfloor hN2 hZ1 hi hlive hYhalf
  -- `X·M ≤ 2N`, real bounds
  have hXM2N : (2 ^ (i + 1) - 1) * pieceM kp ≤ 2 * N := by
    have := goldCut_le_half N (ka + 1); omega
  have hMge1 : (1 : ℝ) ≤ (pieceM kp : ℝ) := by
    have : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp; have := Nat.one_le_pow kp 2 (by norm_num); omega
    exact_mod_cast this
  have hXMpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hXpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by positivity
      linarith [hXge]
    positivity
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  -- `L` window: `2 ≤ L ≤ 2·log N`
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hXMloR : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    calc (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hXge
      _ = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
          apply mul_le_mul_of_nonneg_left hMge1; positivity
  have hL2 : (2 : ℝ) ≤ L := by
    have hlogval : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4)
        = 11 / 24 * Real.log N - Real.log 4 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
    have hle : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4) ≤ L :=
      Real.log_le_log (by positivity) hXMloR
    rw [hlogval] at hle; linarith [hlogN, hlog4, hle]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hXMhiR : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 2 * (N : ℝ) := by
    have : ((2 ^ (i + 1) - 1) * pieceM kp : ℕ) ≤ 2 * N := hXM2N
    have hc : (((2 ^ (i + 1) - 1) * pieceM kp : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc ⊢; linarith [hc]
  have hLle : L ≤ 2 * Real.log N := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    have hlog : L ≤ Real.log (4 * (N : ℝ)) := Real.log_le_log hXMpos h4N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at hlog
    linarith [hlog, hlog4, hlogN1]
  have hLbb : L ≤ Real.log (4 * (N : ℝ)) := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    exact Real.log_le_log hXMpos h4N
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- `hk : 2 ≤ kp` (`2^kp ≥ w ≥ N^{1/3}/16 ≥ 1 ≥ 2^1`, and `2^kp ≥ 4`)
  have h2kp4 : (4 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
    linarith [hwge, hwkf]
  have hk : 2 ≤ kp := by
    by_contra hk2
    have : (2 : ℕ) ^ kp ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcast : ((2 ^ kp : ℕ) : ℝ) ≤ 2 := by
      have : ((2 ^ kp : ℕ) : ℝ) ≤ ((2 ^ 1 : ℕ) : ℝ) := by exact_mod_cast this
      simpa using this
    linarith [h2kp4, hcast]
  -- `hN₀ : N₀ ≤ 2^kp`
  have hN₀ : N₀ ≤ 2 ^ kp := by
    have hbigR : ((16 * N₀ : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hle : ((16 * N₀) ^ 3 : ℕ) ≤ N := by omega
      calc ((16 * N₀ : ℕ) : ℝ) ^ 3 = (((16 * N₀) ^ 3 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (N : ℝ) := by exact_mod_cast hle
    have hcube : ((16 * N₀ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have hmono := Real.rpow_le_rpow (by positivity) hbigR (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast ((16 * N₀ : ℕ) : ℝ) 3, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hmono
    have hchain : ((16 * N₀ : ℕ) : ℝ) ≤ 16 * ((2 ^ kp : ℕ) : ℝ) :=
      le_trans hcube (by linarith [hwge, hwkf])
    have hfin : ((N₀ : ℕ) : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
      have heq : ((16 * N₀ : ℕ) : ℝ) = 16 * ((N₀ : ℕ) : ℝ) := by push_cast; ring
      rw [heq] at hchain; linarith [hchain]
    exact_mod_cast hfin
  -- structural rows
  have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := by
    have h8 : (8 : ℝ) ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := by
      have h813 : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith [hN13_16]
      calc (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := h813
        _ ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have : (2 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by linarith [hXge, h8]
    exact_mod_cast this
  have hM2 : 2 ≤ pieceM kp := by
    have : (2 : ℝ) ≤ (pieceM kp : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
      linarith [hMfloor]
    exact_mod_cast this
  have hFX : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := by
    have := gold_box_Ffloor hi; omega
  -- polylog rows (√X, √M floors)
  have hsqrtX : (N : ℝ) ^ ((11 : ℝ) / 48) / 2 ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    rw [show (N : ℝ) ^ ((11 : ℝ) / 48) / 2
        = Real.sqrt (((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h48 : ((N : ℝ) ^ ((11 : ℝ) / 48)) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((11 : ℝ) / 48)) 2, ← Real.rpow_mul hNpos.le,
        show (11 : ℝ) / 48 * ((2 : ℕ) : ℝ) = 11 / 24 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
      rw [div_pow, h48]; norm_num
    rw [hsq]; exact hXge
  have hsqrtM : (N : ℝ) ^ ((1 : ℝ) / 6) / 4 ≤ Real.sqrt (pieceM kp : ℝ) := by
    rw [show (N : ℝ) ^ ((1 : ℝ) / 6) / 4
        = Real.sqrt (((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h6 : ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 6)) 2, ← Real.rpow_mul hNpos.le,
        show (1 : ℝ) / 6 * ((2 : ℕ) : ℝ) = 1 / 3 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by
      rw [div_pow, h6]; norm_num
    rw [hsq]; exact hMfloor
  have hXsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    have hLpow : L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      gold_Lpow_le hlogN1 hL0 hLle hpl (by norm_num) (by norm_num)
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := by
      have hm := gold_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 11 / 48) (C := 524288)
        (n := 14) (by norm_num) (by norm_num) (by norm_num)
      linarith
    calc L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
      _ ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := htail
      _ ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hsqrtX
  have hMrow : ∀ E : ℝ, 0 ≤ E → E ≤ 18 → L ^ E ≤ Real.sqrt (pieceM kp : ℝ) := by
    intro E hE0 hE18
    have hLpow : L ^ E ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      gold_Lpow_le hlogN1 hL0 hLle hpl hE0 hE18
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / 4 := by
      have hm := gold_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 1 / 6) (C := 1048576)
        (n := 15) (by norm_num) (by norm_num) (by norm_num)
      linarith
    linarith [hLpow, htail, hsqrtM]
  have hMsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  have herr_Mlev : L ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  -- `hfloor` (reused twin row, `F := opZ N·opY N`, `Lb := log(4N)`)
  have hfloor : ((3 : ℝ) / Real.log 2) ^ 8 * (N : ℝ) ^ ((1 : ℝ) / 6)
      * (Real.log (4 * (N : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt ((opZ N * opY N : ℕ) : ℝ) :=
    row_hfloor hexp4000 rfl rfl
  -- `√z ≥ N^{1/16}/2` (the poly-log-vs-√z room the D-scale rows use)
  have hsqrtz : (N : ℝ) ^ ((1 : ℝ) / 16) / 2 ≤ Real.sqrt (opZ N : ℝ) := by
    have hmono : Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 8) / 2) ≤ Real.sqrt (opZ N : ℝ) :=
      Real.sqrt_le_sqrt hZhalf
    have heq : Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 8) / 2)
        = (N : ℝ) ^ ((1 : ℝ) / 16) / Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow (Real.rpow_nonneg hNpos.le _) (by norm_num),
        ← Real.rpow_mul hNpos.le, show (1 : ℝ) / 8 * (1 / 2) = 1 / 16 by norm_num,
        ← Real.sqrt_eq_rpow]
    rw [heq] at hmono
    have hsqrt2le : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hN16nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg hNpos.le _
    have hstep : (N : ℝ) ^ ((1 : ℝ) / 16) / 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 16) / Real.sqrt 2 := by
      rw [div_le_div_iff₀ (by norm_num) hsqrt2pos]; nlinarith [hN16nn, hsqrt2le]
    linarith [hstep, hmono]
  -- `L^E ≤ √z` for `0 ≤ E ≤ 18`
  have hLEz : ∀ E : ℝ, 0 ≤ E → E ≤ 18 → L ^ E ≤ Real.sqrt (opZ N : ℝ) := by
    intro E hE0 hE18
    have hLpow : L ^ E ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      gold_Lpow_le hlogN1 hL0 hLle hpl hE0 hE18
    have hm := gold_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 1 / 16) (C := 524288)
      (n := 14) (by norm_num) (by norm_num) (by norm_num)
    linarith [hLpow, hm, hsqrtz]
  -- `2w·√z ≤ √(goldCut ka)`
  have h2wsz : (2 * w) * Real.sqrt (opZ N : ℝ) ≤ Real.sqrt (goldCut N ka : ℝ) := by
    have hgcka1 : 1 ≤ goldCut N ka := one_le_goldCut hN2 ka
    have hsuc : goldCut N (ka + 1) ≤ 2 * goldCut N ka := goldCut_succ_le_two_mul N ka
    have hsucR : (goldCut N (ka + 1) : ℝ) ≤ 2 * (goldCut N ka : ℝ) := by exact_mod_cast hsuc
    have hsqval : ((2 * w) * Real.sqrt (opZ N : ℝ)) * ((2 * w) * Real.sqrt (opZ N : ℝ))
        = (goldCut N (ka + 1) : ℝ) / 2 := by
      have hzz : Real.sqrt (opZ N : ℝ) * Real.sqrt (opZ N : ℝ) = (opZ N : ℝ) :=
        Real.mul_self_sqrt hZpos.le
      have hrw : ((2 * w) * Real.sqrt (opZ N : ℝ)) * ((2 * w) * Real.sqrt (opZ N : ℝ))
          = 4 * (w * w) * (Real.sqrt (opZ N : ℝ) * Real.sqrt (opZ N : ℝ)) := by ring
      rw [hrw, hzz, hw2]; field_simp; ring
    have hsq : ((2 * w) * Real.sqrt (opZ N : ℝ)) * ((2 * w) * Real.sqrt (opZ N : ℝ))
        ≤ (goldCut N ka : ℝ) := by rw [hsqval]; linarith [hsucR]
    have hnn : 0 ≤ (2 * w) * Real.sqrt (opZ N : ℝ) := by positivity
    calc (2 * w) * Real.sqrt (opZ N : ℝ)
        = Real.sqrt (((2 * w) * Real.sqrt (opZ N : ℝ)) * ((2 * w) * Real.sqrt (opZ N : ℝ))) :=
          (Real.sqrt_mul_self hnn).symm
      _ ≤ Real.sqrt (goldCut N ka : ℝ) := Real.sqrt_le_sqrt hsq
  -- the D·L^E ≤ √(X·M) core (hDscale, herr_lev)
  have hXMloR2 : (goldCut N ka : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    exact_mod_cast hXMlo_nat
  have hDLsqrt : ∀ E : ℝ, 0 ≤ E → E ≤ 18 →
      (D : ℝ) * L ^ E ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
    intro E hE0 hE18
    calc (D : ℝ) * L ^ E ≤ (2 * w) * L ^ E :=
          mul_le_mul_of_nonneg_right hDhi (Real.rpow_nonneg hL0 E)
      _ ≤ (2 * w) * Real.sqrt (opZ N : ℝ) :=
          mul_le_mul_of_nonneg_left (hLEz E hE0 hE18) (by positivity)
      _ ≤ Real.sqrt (goldCut N ka : ℝ) := h2wsz
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
          Real.sqrt_le_sqrt (le_of_lt hXMloR2)
  have hLpos : (0 : ℝ) < L := by linarith
  have hDscale : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
      / L ^ (15 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have := hDLsqrt 15 (by norm_num) (by norm_num); linarith [this]
  have herr_lev : (D : ℝ) * L ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
    hDLsqrt _ (by norm_num) (by norm_num)
  -- D-scale structural rows
  have hDge2w : (D : ℝ) ≤ 2 * w := hDhi
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ (D : ℝ) := by
      have h1w : (1 : ℝ) ≤ w := by
        have : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
        linarith [hwge]
      linarith [hDge, h1w]
    exact_mod_cast this
  have hDx : (D : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hgcN2 : (goldCut N (ka + 1) : ℝ) ≤ (N : ℝ) / 2 := by
      have := goldCut_le_half N (ka + 1)
      have hc : (goldCut N (ka + 1) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
      have : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        exact_mod_cast (by omega : N / 2 * 2 ≤ N)
      linarith [hc]
    have h2w2 : (2 * w) * (2 * w) ≤ (N : ℝ) := by
      have hval : (2 * w) * (2 * w) = 4 * (w * w) := by ring
      rw [hval, hw2,
        show 4 * ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ)))
          = (goldCut N (ka + 1) : ℝ) / (2 * (opZ N : ℝ)) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (opZ N : ℝ) := by exact_mod_cast hZ1
      nlinarith [hgcN2, mul_nonneg hNpos.le (by linarith [h1] : (0 : ℝ) ≤ (opZ N : ℝ) - 1)]
    have hnn : 0 ≤ 2 * w := by positivity
    have : 2 * w ≤ Real.sqrt (N : ℝ) := by
      rw [show 2 * w = Real.sqrt ((2 * w) * (2 * w)) from (Real.sqrt_mul_self hnn).symm]
      exact Real.sqrt_le_sqrt h2w2
    linarith [hDhi, this]
  have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hgcka0 : (0 : ℝ) ≤ (goldCut N ka : ℝ) := by positivity
    have hgcka1R : (1 : ℝ) ≤ (goldCut N ka : ℝ) := by exact_mod_cast one_le_goldCut hN2 ka
    have hsucR : (goldCut N (ka + 1) : ℝ) ≤ 2 * (goldCut N ka : ℝ) := by
      exact_mod_cast goldCut_succ_le_two_mul N ka
    have h2wsq : (2 * w) * (2 * w) ≤ (goldCut N ka : ℝ) := by
      have hval : (2 * w) * (2 * w) = 4 * (w * w) := by ring
      rw [hval, hw2,
        show 4 * ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ)))
          = (goldCut N (ka + 1) : ℝ) / (2 * (opZ N : ℝ)) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (opZ N : ℝ) := by exact_mod_cast hZ1
      nlinarith [hsucR, mul_nonneg hgcka0 (by linarith [h1] : (0 : ℝ) ≤ (opZ N : ℝ) - 1)]
    have hnn : 0 ≤ 2 * w := by positivity
    have h2wle : 2 * w ≤ (goldCut N ka : ℝ) := by
      have hsqrtself : Real.sqrt (goldCut N ka : ℝ) ≤ (goldCut N ka : ℝ) := by
        have h1 : Real.sqrt (goldCut N ka : ℝ)
            ≤ Real.sqrt ((goldCut N ka : ℝ) * (goldCut N ka : ℝ)) :=
          Real.sqrt_le_sqrt (by nlinarith [hgcka1R])
        rwa [Real.sqrt_mul_self hgcka0] at h1
      have : 2 * w ≤ Real.sqrt (goldCut N ka : ℝ) := by
        rw [show 2 * w = Real.sqrt ((2 * w) * (2 * w)) from (Real.sqrt_mul_self hnn).symm]
        exact Real.sqrt_le_sqrt h2wsq
      linarith [this, hsqrtself]
    linarith [hDhi, h2wle, hXMloR2]
  have hDsq : D < (2 ^ kp + 1) * (2 ^ kp + 1) := by
    have hDle_real : (D : ℝ) ≤ 2 * ((2 ^ kp : ℕ) : ℝ) := le_trans hDhi (by linarith [hwkf])
    have hDle : D ≤ 2 * 2 ^ kp := by exact_mod_cast hDle_real
    have hm : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
    nlinarith [hDle, hm]
  -- `habs : 4(1+log D)·D ≤ 2^kp·pieceM kp/L^{13}`
  have hlogDnn : (0 : ℝ) ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD1)
  have hlogxle : Real.log N ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := by
    refine le_trans ?_ hpl
    calc Real.log N = (Real.log N) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log N) ^ (18 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlogN1 (by norm_num)
  have hDleN : (D : ℝ) ≤ (N : ℝ) := by
    have hself : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * (N : ℝ)) :=
        Real.sqrt_le_sqrt (by nlinarith [hN1R])
      rwa [Real.sqrt_mul_self hNpos.le] at h1
    linarith [hDx, hself]
  have hlogD : Real.log D ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [hlogN1]
    · exact Real.log_le_log (by exact_mod_cast hDpos) hDleN
  have hLpow13 : L ^ (13 : ℝ) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
    gold_Lpow_le hlogN1 hL0 hLle hpl (by norm_num) (by norm_num)
  have hwbound : (4194304 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 1000) ≤ w := by
    have hm := gold_mono_close hNpos hlogN9 (a := 1 / 1000) (b := 1 / 3) (C := 67108864)
      (n := 19) (by norm_num) (by norm_num) (by norm_num)
    linarith [hwge, hm]
  have h2P : 8 * (1 + Real.log D) * L ^ (13 : ℝ) ≤ w := by
    have hb1 : 8 * (1 + Real.log D) ≤ 16 * Real.log N := by nlinarith [hlogD, hlogN1]
    have hprod : 8 * (1 + Real.log D) * L ^ (13 : ℝ)
        ≤ 16 * Real.log N * (262144 * (N : ℝ) ^ ((1 : ℝ) / 2000)) :=
      mul_le_mul hb1 hLpow13 (by positivity) (by linarith [hlogN1])
    have hcombine : 16 * Real.log N * (262144 * (N : ℝ) ^ ((1 : ℝ) / 2000))
        ≤ 4194304 * (N : ℝ) ^ ((1 : ℝ) / 1000) := by
      have hh : Real.log N * (N : ℝ) ^ ((1 : ℝ) / 2000)
          ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
        mul_le_mul_of_nonneg_right hlogxle (Real.rpow_nonneg hNpos.le _)
      rw [← Real.rpow_add hNpos, show (1 : ℝ) / 2000 + 1 / 2000 = 1 / 1000 by norm_num] at hh
      nlinarith [hh]
    linarith [hprod, hcombine, hwbound]
  have habs : 4 * (1 + Real.log D) * (D : ℝ)
      ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have hPnn : (0 : ℝ) ≤ 4 * (1 + Real.log D) * L ^ (13 : ℝ) := by positivity
    have hkey : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ) ≤ w * w := by
      nlinarith [hDhi, h2P, hwnn, hPnn, Real.rpow_nonneg hL0 (13 : ℝ)]
    calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ) ≤ w * w := hkey
      _ ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by nlinarith [hwkf, hwnn]
      _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) :=
          mul_le_mul_of_nonneg_left hMge2kp (by positivity)
  -- herr_scale / herr_LEpos (via bridge_scale on hDscale)
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      L ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) := by
    intro e he2 heD heX
    linarith [herr_scale e he2 heD heX, hL2]
  -- close via `gold_box_price_live_kerr` at the op values
  have hFXR : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := hFX
  exact hbody (N : ℝ) (Real.log (4 * (N : ℝ))) (opZ N * opY N) β kp D Dset r T₁ T₂ N (opZ N)
    (opY N) K ka i hN2 hi hlive hZ1 hz_ratio hx hDge hk hβ hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs
    hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFXR hDx hLbb hfloor herr_LEpos hDXM herr_scale

end Salt.Goldbach
