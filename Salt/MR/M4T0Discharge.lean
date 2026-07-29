/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4DoorClose
import Salt.MR.A2Wall

/-!
# `M4T0Discharge` — ⟦T0-DISCHARGE⟧: the first carried analytic arm of the M4 wave, closed

`M4DoorClose.m4_wave_structurally_closed` carried TWO analytic arms.  This file discharges the
first — the `T₀`-band conjunct of `M4DoorClose.DoorRowCarried`, i.e. the RAW slot

  `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff χ M)) (seamS0 (2X_d) X) t‖² ≤ t0BandB X C₁′ M₀`,
  `T₀ = seamT0 X = (log X)^{1/45}`,

at an EXPLICIT `(C₁′, M₀) = (cfbC₁ X (t0dC1 Cb), t0dM0 X)`.

## ⟦WHY IT CLOSES NOW, AND NOT BEFORE⟧

`M4T0Datum`'s ⟦THE PRICING RESIDUE, NAMED⟧ recorded the obstruction: §5's `hRHS` binder is
priced by `SPartStation.dilated_scale_grade`, whose floor binder `hM₀` reads the frequency
range `|v| ≤ Rad ⊇ |t₁| + Tstar(k, log k)` — the CONTOUR-BOX range, not the band's.  At the box
the landed floor is `FarL2.boxM0`'s `1/16`, and at the PRE-RE-CUT seam floor `(log X)^{1/15}`
the exit's decay gate demanded `(103/1500)·e = 0.18665` — `2.99×` more than `1/16`
(`A2Wall.a2wall_box_fails_gate_15`).  The residue was a STRENGTH shortfall, never a range one.

The `(45, 46)` re-cut moved the gate to `(1009/45000)·e = 0.060950…`, and `1/16 = 0.0625`
CLEARS it with margin `0.00155008…` (`A2Wall.a2wall_box_clears_45`, threshold constant `700`).
So the ORIGINAL `Tstar`-reach pricer works verbatim at the box floor, and the whole route is
composition:

  `FarL2.box_floor_M0_pieceDatum` (floor at `|v| ≤ 3X`, mask debit absorbed)
   → `SPartStation.dilated_scale_grade` (`t₀ = 0`, `t₁ = t`, `Rad = 3X`, `Xd = X_w`)
   → `M4T0Datum.piece_center_of_wide`'s `hRHS` slot at `B := t0dB X Cb`
   → `M4T0Datum.m4_hT0band_at_door_of_wide` (§5 ∘ §7: sup → `cfb_t0band_supply_of_sup`)
   → the RAW slot.

## ⟦THE THREE NUMERALS⟧

* `t0dM0 X = (1009/45000)·e·loglog X` — the re-cut gate value, i.e. the SMALLEST `M₀` at which
  `A2Wall.a2wall_gate_45` makes the exit's first summand `8448·C₁′²·e^{−M₀/e}` decay, at rate
  `(log X)^{−1/5000}`.  Stating the conclusion here (rather than at the box floor's own value)
  is what lets the consumer's envelope conjunct be checked with clean numerals.
* `t0dB X Cb = C(c, Cb)·(log X)^{−1009/90000} + farCStar·(log X/2)^{−1/(32e)}` — the per-piece
  `hRHS` grade.  `e^{−M₀/(2e)}` at `M₀ = t0dM0 X` IS `(log X)^{−1009/90000}` (`t0d_decay_eq`),
  and the far arm's own exponent `1/(32e) = 0.011494…` DOMINATES `1009/90000 = 0.011211…`
  (`t0d_far_exp_le`) — the second place the re-cut's margin is spent.
* `t0dC1 Cb = 4·cSq·(C(c,Cb) + 2·farCStar + 5)` — `X`-free and `q`-free, the grade comparison's
  constant.  The `5 = 4 + 1` is the four `(log X)^{−1/2+1/1000}` residues of the dissection plus
  the ONE dissection-depth term, each charged against `(log X)^{−1009/90000}`.

## ⟦WHAT IS CARRIED⟧ — the discharge's own gate list

Everything below is regime arithmetic at the block scale, plus the wide supply's own gates:

* `X₀ ≤ √X` (the hoisted threshold, `≥ e^{4096}`, hence `log X ≥ 8192`);
* the dilation frame `√X ≤ X_w ≤ X`, `1 ≤ D`, `D(X_w+1) ≤ X−1` (`SPartStation`'s);
* `0 ≤ Cb`, `ShortIntervalDatum Cb` (the short-interval datum);
* the mask debit `Σ_{i∈𝒥} Σ_{p ∈ blockWindow} 1/p ≤ Dmask` — the SAME conjunct
  `DoorRowCarried` already carries at `Dmask`;
* the `700`-threshold at the shifted constant `K + (Dmask + 4)`, the `4` paying `dilGap X X_w`
  (`t0d_dilGap_le`: at `X_w ≥ √X` the dilation price is at most `4`, absolutely);
* the `Tstar`-reach `seamT0 X + Tstar(2X, log 2X) ≤ 3X` — the box COVERS the pricer's radius;
* the dissection-depth decay `D^{−1/4} ≤ (log X)^{−1009/90000}`.

## ⟦THE TRAPS RESPECTED⟧

the five log scales at the RE-CUT numerals (`seamT0 X = (log X)^{1/45}`, `seamRad X =
(log X)^{1/46}`, `cfbC₁ X C₁ = (C₁+1)(log X)^{1/90}`, the gate `1009/45000`, the half-exponent
`1009/90000` — every one read from the CURRENT bytes); `liouChi` never `lamChi` (the pieces are
`pieceDatum = liouChi χ · g_𝒥`, and `FarL2.box_floor_M0_liouChi` is the sum-side transport);
the half-open cut `winCutH` throughout; the `t₀ = 0` pin (un-phased datum, the band frequency
enters only as the twist `eIu (−t)`); strict gates never weakened; K6 — the two suppliers'
existentials (`box_floor_M0_pieceDatum`'s `K`, `piece_center_of_wide`'s `X₀`) are hoisted
OUTSIDE the instance quantifier, their gates INSIDE.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory
open scoped BigOperators

open Salt.Entropy.Chowla

/-! ## §0 — THE RE-CUT'S NUMERALS -/

/-- **THE DISCHARGE'S FLOOR VALUE** (`t0dM0`).  `M₀⋆ = (1009/45000)·e·loglog X`, exactly the
gate `A2Wall.a2wall_gate_45` demands: at it the exit's first summand
`8448·(cfbC₁ X C₁)²·e^{−M₀/e}` is `8448·(C₁+1)²·(log X)^{1/45 − 1009/45000} =
8448·(C₁+1)²·(log X)^{−1/5000}`. -/
def t0dM0 (X : ℝ) : ℝ := 1009 / 45000 * Real.exp 1 * Real.log (Real.log X)

/-- **THE PER-PIECE `hRHS` GRADE** (`t0dB`).  `SPartStation.dilated_scale_grade`'s two summands
read at `M₀ = t0dM0 X` (main) and at the wide window's log floor `log X/2` (far). -/
def t0dB (X Cb : ℝ) : ℝ :=
  gradeAbsConstC (1 / (2 * Real.exp 1)) Cb * Real.log X ^ (-(1009 : ℝ) / 90000)
    + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))

/-- **THE DISCHARGE'S GRADE CONSTANT** (`t0dC1`).  `X`-free and `q`-free; `1 ≤ t0dC1 Cb`
outright (`one_le_t0dC1`), which is `m4_hT0band_at_door_of_wide`'s `hC₁`. -/
def t0dC1 (Cb : ℝ) : ℝ :=
  4 * cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb + 2 * farCStar + 5)

/-- `e^{−M₀⋆/(2e)} = (log X)^{−1009/90000}` — the gate value read as a power of `log X`.  The
`2e` in the sup's exponent halves the gate's `1009/45000`. -/
theorem t0d_decay_eq {X : ℝ} (hL : 0 < Real.log X) :
    Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
      = Real.log X ^ (-(1009 : ℝ) / 90000) := by
  rw [Real.rpow_def_of_pos hL, t0dM0]
  congr 1
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  field_simp
  ring

/-- **THE SECOND MARGIN** (`t0d_far_exp_le`).  `1009/90000 ≤ 1/(32e)`: the STAR far arm's own
decay `(log k)^{−1/(32e)}` is at least as fast as the re-cut gate's half-exponent.  Numerically
`0.011211… ≤ 0.011494…`; equivalently `32288·e ≤ 90000`. -/
theorem t0d_far_exp_le : (1009 : ℝ) / 90000 ≤ 1 / (32 * Real.exp 1) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 32 * Real.exp 1 := by positivity
  rw [div_le_div_iff₀ (by norm_num) h0]
  nlinarith

/-- **THE FAR ARM, PRICED AGAINST THE GATE** (`t0d_far_le`).  `(log X/2)^{−1/(32e)} ≤
2·(log X)^{−1009/90000}` — the factor `2` is `2^{1/(32e)} ≤ 2`, the exponent comparison is
`t0d_far_exp_le`. -/
theorem t0d_far_le {X : ℝ} (hL : (2 : ℝ) ≤ Real.log X) :
    (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
      ≤ 2 * Real.log X ^ (-(1009 : ℝ) / 90000) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have ha1 : 1 / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.exp_one_gt_d9]
  have hsplit : (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
      = Real.log X ^ (-(1 / (32 * Real.exp 1))) * 2 ^ (1 / (32 * Real.exp 1)) := by
    rw [Real.div_rpow hL0.le (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have h2 : (2 : ℝ) ^ (1 / (32 * Real.exp 1)) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / (32 * Real.exp 1)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 2 := Real.rpow_one 2
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / (32 * Real.exp 1)) := Real.rpow_nonneg (by norm_num) _
  have h3 : Real.log X ^ (-(1 / (32 * Real.exp 1)))
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [t0d_far_exp_le])
  have hp0 : (0 : ℝ) ≤ Real.log X ^ (-(1 / (32 * Real.exp 1))) := Real.rpow_nonneg hL0.le _
  have hq0 : (0 : ℝ) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := Real.rpow_nonneg hL0.le _
  rw [hsplit]
  nlinarith

/-- The dissection's own residue is dominated by the gate value (`t0d_P_le`):
`(log X)^{−1/2+1/1000} ≤ (log X)^{−1009/90000}` at every `log X ≥ 1`. -/
theorem t0d_P_le {X : ℝ} (hL : (1 : ℝ) ≤ Real.log X) :
    Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) :=
  Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- **`cfb_t0band_supply_of_sup`'s `hErr`, DISCHARGED** (`t0d_err_le`).
`4·(log X)^{−1/2+1/1000} ≤ (log X)^{−1009/90000}` past `log X ≥ 256`: the spare exponent is
`43901/90000 = 0.48779…`, and `4 ≤ (log X)^{1/4}` already at `log X ≥ 256`. -/
theorem t0d_err_le {X : ℝ} (hL : (256 : ℝ) ≤ Real.log X) :
    4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have h256 : ((256 : ℝ)) ^ ((1 : ℝ) / 4) = 4 := by
    rw [show (256 : ℝ) = (4 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 4,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have h4 : (4 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 4) := by
    calc (4 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 4) := h256.symm
      _ ≤ Real.log X ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  have hstep : Real.log X ^ ((1 : ℝ) / 4) ≤ Real.log X ^ ((43901 : ℝ) / 90000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hmul : Real.log X ^ ((43901 : ℝ) / 90000) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      = Real.log X ^ (-(1009 : ℝ) / 90000) := by
    rw [← Real.rpow_add hL0,
      show (43901 : ℝ) / 90000 + (-(1 : ℝ) / 2 + 1 / 1000) = -(1009 : ℝ) / 90000 by norm_num]
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hL0.le _
  nlinarith

/-- **THE DILATION PRICE IS ABSOLUTE** (`t0d_dilGap_le`).  At the wide window's own floor
`√X ≤ X_w ≤ X` the Mertens dilation gap is at most `4`, with no `X`-dependence: the first
summand is `≤ 1` because `log X ≤ 2·log X_w`, the second because `log X_w ≥ 4096`. -/
theorem t0d_dilGap_le {X Xw : ℝ} (hX0 : 0 < X) (hsq : Real.sqrt X ≤ Xw) (hXw : Xw ≤ X)
    (hL : (8192 : ℝ) ≤ Real.log X) : dilGap X Xw ≤ 4 := by
  have hsq0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hXw0 : (0 : ℝ) < Xw := lt_of_lt_of_le hsq0 hsq
  have hLw : Real.log X / 2 ≤ Real.log Xw := by
    have h := Real.log_le_log hsq0 hsq
    rwa [Real.log_sqrt hX0.le] at h
  have hLwX : Real.log Xw ≤ Real.log X := Real.log_le_log hXw0 hXw
  have hLw0 : (0 : ℝ) < Real.log Xw := by linarith
  have h1 : (Real.log X - Real.log Xw) / Real.log Xw ≤ 1 := by
    rw [div_le_one hLw0]; linarith
  have h2 : (24 : ℝ) / Real.log Xw ≤ 1 := by
    rw [div_le_one hLw0]; linarith
  unfold dilGap
  linarith

/-- `1 ≤ t0dC1 Cb` — `m4_hT0band_at_door_of_wide`'s `hC₁`, from `cSq = 20736` alone. -/
theorem one_le_t0dC1 {Cb : ℝ} (hc1 : 2 * (1 / (2 * Real.exp 1)) < 1) (hCb0 : 0 ≤ Cb) :
    1 ≤ t0dC1 Cb := by
  have hG : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hF : (0 : ℝ) ≤ farCStar := farCStar_nonneg
  have hcs : cSq = 20736 := rfl
  unfold t0dC1
  rw [hcs]
  linarith

/-! ### The four `Y`-gates at the corpus pin, re-derived

`SPartStation.ypin4_gates_sp` and `StationHoist.ypin4_gates_hs` are both `private`; the page is
re-derived here verbatim, suffixed `_t0d`.  The binding gate is the fourth,
`log(Y k) = 4 log L ≤ √L`, i.e. `8 log s ≤ s` at `s = √L`, which needs `L ≥ 4096`. -/

private lemma eight_log_le_self_t0d {Lv : ℝ} (h : 64 ≤ Lv) : 8 * Real.log Lv ≤ Lv := by
  have hL0 : (0 : ℝ) < Lv := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt Lv := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt Lv := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hsq : Real.sqrt Lv * Real.sqrt Lv = Lv := Real.mul_self_sqrt hL0.le
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog : Real.log (Real.sqrt Lv) ≤ Real.sqrt Lv / Real.exp 1 := by
    have h1 : Real.log (Real.sqrt Lv / Real.exp 1) ≤ Real.sqrt Lv / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hs0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h1
    linarith
  have hhalf : Real.log (Real.sqrt Lv) = Real.log Lv / 2 := Real.log_sqrt hL0.le
  have hdiv : Real.sqrt Lv / Real.exp 1 ≤ Real.sqrt Lv / 2 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) he2
  rw [hhalf] at hlog
  nlinarith

private lemma ypin4_gates_t0d {k : ℝ} (hk : Real.exp 4096 ≤ k) :
    10 ≤ Real.log k ^ 4 ∧ Real.log k ^ 4 ≤ Real.sqrt k
      ∧ Real.sqrt (Real.log k) ≤ Real.log k ^ 4
      ∧ Real.log (Real.log k ^ 4) ≤ Real.sqrt (Real.log k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hL : (4096 : ℝ) ≤ Real.log k := by
    rw [← Real.log_exp 4096]; exact Real.log_le_log (Real.exp_pos _) hk
  have hL0 : (0 : ℝ) < Real.log k := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log k := by linarith
  have hL4 : Real.log k ≤ Real.log k ^ 4 := le_self_pow₀ hL1 (by norm_num)
  have hsqL0 : (0 : ℝ) < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr hL0
  have hsqLsq : Real.sqrt (Real.log k) * Real.sqrt (Real.log k) = Real.log k :=
    Real.mul_self_sqrt hL0.le
  have hsqL64 : (64 : ℝ) ≤ Real.sqrt (Real.log k) := by
    have h64 : Real.sqrt 4096 = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt hL
  have hsqLle : Real.sqrt (Real.log k) ≤ Real.log k := by nlinarith
  have hlogpow : Real.log (Real.log k ^ 4) = 4 * Real.log (Real.log k) := by
    rw [Real.log_pow]; push_cast; ring
  have hbind : 4 * Real.log (Real.log k) ≤ Real.sqrt (Real.log k) := by
    have h8 := eight_log_le_self_t0d hsqL64
    have hhalf : Real.log (Real.sqrt (Real.log k)) = Real.log (Real.log k) / 2 :=
      Real.log_sqrt hL0.le
    rw [hhalf] at h8
    linarith
  have hg2 : Real.log k ^ 4 ≤ Real.sqrt k := by
    have hsk : Real.sqrt k = Real.exp (Real.log k * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
    have hp4 : Real.log k ^ 4 = Real.exp (4 * Real.log (Real.log k)) := by
      rw [← hlogpow]
      exact (Real.exp_log (by positivity)).symm
    rw [hsk, hp4]
    refine Real.exp_le_exp.mpr ?_
    have h8 := eight_log_le_self_t0d (le_trans (by norm_num) hL)
    linarith
  refine ⟨by nlinarith, hg2, le_trans hsqLle hL4, ?_⟩
  rw [hlogpow]
  exact hbind

/-! ## §1 — THE PER-PIECE `hRHS`, PRICED AT THE BOX FLOOR

`SPartStation.dilated_scale_grade` at `t₀ = 0`, `t₁ = t`, `Xd = X_w`, `Rad = 3X`, with the
floor slot filled by `FarL2.box_floor_M0_pieceDatum` (the whole contour box) through the two
landed adapters `HalaszHead.seamCoeff_trivial_dist_eq` (the `t₀`-shift, an identity at `t₀ = 0`)
and `CapFreeArm.pretDistSq_ellLin_eq` (the linearisation is invisible to `𝔻²`). -/

set_option maxHeartbeats 1600000 in
-- the four-piece split's binder block (`dilated_scale_grade`'s 13 arguments at a datum
-- carrying two `Finset` indices) is instantiated wholesale; no tactic search happens here
/-- **THE PIECE'S `hRHS` AT THE RE-CUT GATE** (`t0d_piece_hRHS`).  For every finite modulus
range there is ONE `X`-free, `q`-free `K ≥ 0` such that, past `√X ≥ e^{4096}` and under the
`700`-threshold at `K + (Dmask + 4)`, every inclusion–exclusion piece satisfies
`M4T0Datum.piece_center_of_wide`'s `hRHS` binder at the grade `t0dB X Cb`, uniformly in the
band frequency `t` and in the dilated scale `X_w ≤ k ≤ 2X`.

The `+4` in the threshold is the dilation price `dilGap X X_w ≤ 4` (`t0d_dilGap_le`), paid
inside the floor's constant by `FarL2.boxM0_add_debit`; the `+Dmask` is the mask's Mertens
window mass, paid the same way. -/
theorem t0d_piece_hRHS (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
        (𝒥 : Finset ℕ) (X Xw Cb Dmask t : ℝ) (k : ℕ), q ≤ Q →
        Real.exp 4096 ≤ Real.sqrt X → Real.sqrt X ≤ Xw → Xw ≤ X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask →
        700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log (q : ℝ)
                + (q : ℝ) + (K + (Dmask + 4))) ≤ Real.log (Real.log X) →
        |t| + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X →
        Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
          ‖prop21RHS
              (fun p => pieceDatum χ 𝒥 Pseq Qseq p * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I))
              (0 + t) (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
              (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
              (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
            ≤ t0dB X Cb * (k : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := box_floor_M0_pieceDatum Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X Xw Cb Dmask t k hq hsq4096 hsqXw hXwX hCb0 hCbound hdebit
    hthr hgateT hkXw hk2X
  -- ⟦the exponent contract of the pricer⟧
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have hc1 : 2 * (1 / (2 * Real.exp 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hce : 1 / (2 * Real.exp 1) ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [Real.exp_pos (1 : ℝ)]
  -- ⟦the scale page at the wide window's floor⟧
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hXee : Real.exp (Real.exp 1) ≤ X :=
    le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hXexp
  have hXw2 : (2 : ℝ) ≤ Xw := by linarith [le_trans hsq4096 hsqXw]
  have hk4096 : Real.exp 4096 ≤ (k : ℝ) := le_trans (le_trans hsq4096 hsqXw) hkXw
  have hk64 : Real.exp 64 ≤ (k : ℝ) := le_trans (Real.exp_le_exp.mpr (by norm_num)) hk4096
  have hkee : Real.exp (Real.exp 1) ≤ (k : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hk4096
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- ⟦THE `Tstar` REACH: the box covers the pricer's radius⟧
  have hgate : |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X := by
    have hmono := Tstar_mono hkee hk2X
    linarith
  -- ⟦THE FLOOR, at the whole contour box⟧
  have hM₀ : ∀ v : ℝ, |v| ≤ 3 * X →
      boxM0 (K + Dmask) q X
        ≤ pretDistSq (seamCoeff (ellLin (pieceDatum χ 𝒥 Pseq Qseq)) (fun _ => 1) 0)
            (costwist v) X := by
    intro v hv
    rw [seamCoeff_trivial_dist_eq, pretDistSq_ellLin_eq, add_zero]
    exact hK q χ Pseq Qseq 𝒥 X v Dmask hq hXee hv hdebit
  have hmain := dilated_scale_grade (g := pieceDatum χ 𝒥 Pseq Qseq)
    (fun p _ => norm_pieceDatum_le_one χ 𝒥 Pseq Qseq p) (c := 1 / (2 * Real.exp 1))
    (Cb := Cb) (t₀ := 0) (t₁ := t) (X := X) (Xd := Xw)
    (M₀ := boxM0 (K + Dmask) q X) (Rad := 3 * X) (k := k)
    hc0 hce hc1 hCb0 hCbound hk64 hXw2 hXwX hkXw hgate hM₀
  refine le_trans hmain ?_
  -- ⟦THE GATE CLEARS, the dilation price paid inside the floor's constant⟧
  have hdil : dilGap X Xw ≤ 4 := t0d_dilGap_le hX0 hsqXw hXwX hLX
  have hLL : (0 : ℝ) ≤ Real.log (Real.log X) := by
    obtain ⟨-, -, hll, -⟩ := cff_scale_facts hXee
    linarith
  have hclear : t0dM0 X ≤ boxM0 (K + Dmask) q X - dilGap X Xw := by
    have h := a2wall_box_floor_clears_gate_45 (K := K + (Dmask + 4)) (q := q) (X := X) hLL hthr
    rw [show K + (Dmask + 4) = K + Dmask + 4 by ring, boxM0_add_debit] at h
    unfold t0dM0
    linarith
  have hexp : Real.exp (-(1 / (2 * Real.exp 1)) * (boxM0 (K + Dmask) q X - dilGap X Xw))
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := by
    rw [← t0d_decay_eq hL0]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hclear hc0.le]
  have hfar : Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
      ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) := by
    have hLk : Real.log X / 2 ≤ Real.log (k : ℝ) := by
      have h1 : Real.log (Real.sqrt X) ≤ Real.log (k : ℝ) :=
        Real.log_le_log hsq0 (le_trans hsqXw hkXw)
      rwa [Real.log_sqrt hX0.le] at h1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hLk (neg_nonpos.mpr (by positivity))
  have hG0 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb :=
    gradeAbsConstC_nonneg hc1 hCb0
  have h1 : gradeAbsConstC (1 / (2 * Real.exp 1)) Cb * (k : ℝ)
        * Real.exp (-(1 / (2 * Real.exp 1)) * (boxM0 (K + Dmask) q X - dilGap X Xw))
      ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb * (k : ℝ)
        * Real.log X ^ (-(1009 : ℝ) / 90000) :=
    mul_le_mul_of_nonneg_left hexp (mul_nonneg hG0 hk0)
  have h2 : farCStar * (k : ℝ) * Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
      ≤ farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    mul_le_mul_of_nonneg_left hfar (mul_nonneg farCStar_nonneg hk0)
  have hring : t0dB X Cb * (k : ℝ)
      = gradeAbsConstC (1 / (2 * Real.exp 1)) Cb * (k : ℝ)
          * Real.log X ^ (-(1009 : ℝ) / 90000)
        + farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) := by
    unfold t0dB; ring
  rw [hring]
  linarith

/-! ## §2 — THE ARM, DISCHARGED

`M4T0Datum.m4_hT0band_at_door_of_wide` at the corpus pin `Y x = (log x)^4`, with §1 in the
`hRHS` slot and the two remaining binders (`hgrade`, `hErr`) discharged from §0's numerals. -/

set_option maxHeartbeats 1600000 in
-- `m4_hT0band_at_door_of_wide`'s ~20-binder application, with the grade expression carried
-- three times (`hgrade`, `hErr`, the conclusion) — elaboration cost only
/-- **THE `T₀`-BAND ARM OF `DoorRowCarried`, DISCHARGED** (`m4_t0band_discharged`).

  `⟦the discharge's gate list⟧ →
     ∫_{−seamT0 X}^{seamT0 X} ‖dpolyA (winCutH X_d (doorChiCoeff χ M)) (seamS0 (2X_d) X) t‖² dt
       ≤ t0BandB X (cfbC₁ X (t0dC1 Cb)) (t0dM0 X)`

— the RAW slot `M4MeanSq.m4_meansq_per_chi_gen` reads, at the door's sieved, χ-twisted,
UN-PHASED datum, with `(C₁′, M₀)` no longer existential but PINNED at
`(cfbC₁ X (t0dC1 Cb), (1009/45000)·e·loglog X)`.

⟦K6⟧ the two suppliers' constants — `K` (`FarL2.box_floor_M0_pieceDatum`'s masked box floor)
and `X₀` (`CaseAWide.center_halasz_supply_wideA`'s hoisted threshold, maxed with `e^{4096}`) —
are bound OUTSIDE the instance quantifier; every gate that mentions them is INSIDE. -/
theorem m4_t0band_discharged (Q : ℕ) :
    ∃ K X₀ : ℝ, 0 ≤ K ∧ 0 < X₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd D : ℕ)
        (X Xw Cb Dmask : ℝ), q ≤ Q →
        X₀ ≤ Real.sqrt X → ((Xd : ℕ) : ℝ) = X →
        Real.sqrt X ≤ Xw → Xw ≤ X → 1 ≤ D → (D : ℝ) * (Xw + 1) ≤ X - 1 →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
              (calQK (Adoor M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) →
        700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log (q : ℝ)
                + (q : ℝ) + (K + (Dmask + 4))) ≤ Real.log (Real.log X) →
        seamT0 X + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X →
        (D : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X (t0dC1 Cb)) (t0dM0 X) := by
  obtain ⟨X₀, hX₀0, hwide⟩ := m4_hT0band_at_door_of_wide (fun x => Real.log x ^ 4)
  obtain ⟨K, hK0, hpiece⟩ := t0d_piece_hRHS Q
  refine ⟨K, max X₀ (Real.exp 4096), hK0,
    lt_of_lt_of_le (Real.exp_pos 4096) (le_max_right _ _), ?_⟩
  intro q _ χ M Xd D X Xw Cb Dmask hq hX0lb hXd hsqXw hXwX hD hDgate hCb0 hCbound hdebit
    hthr hgateT hDdec
  have hX₀ : X₀ ≤ Real.sqrt X := le_trans (le_max_left _ _) hX0lb
  have hsq4096 : Real.exp 4096 ≤ Real.sqrt X := le_trans (le_max_right _ _) hX0lb
  -- ⟦the scale page⟧
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hX3 : (3 : ℝ) ≤ X := by
    have : (4097 : ℝ) ≤ X := le_trans (le_trans hexp4097 hsq4096) hsqX
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / (2 * Real.exp 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hG0 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb :=
    gradeAbsConstC_nonneg hc1 hCb0
  -- ⟦the four `Y`-gates⟧
  have hk4096 : ∀ k : ℕ, Xw ≤ (k : ℝ) → Real.exp 4096 ≤ (k : ℝ) :=
    fun k h => le_trans (le_trans hsq4096 hsqXw) h
  -- ⟦the numerals⟧
  have hE0 : (0 : ℝ) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := Real.rpow_nonneg hL0.le _
  have hQ0 : (0 : ℝ) ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg (by linarith) _
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hL0.le _
  have hB0 : (0 : ℝ) ≤ t0dB X Cb := by
    unfold t0dB
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
        * Real.log X ^ (-(1009 : ℝ) / 90000) := mul_nonneg hG0 hE0
    have h2 : (0 : ℝ) ≤ farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      mul_nonneg farCStar_nonneg hQ0
    linarith
  have hEdef : Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
      = Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_decay_eq hL0
  -- ⟦hErr⟧
  have hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X) := by
    rw [hEdef]; exact t0d_err_le (by linarith)
  -- ⟦hgrade⟧: the four residues charged against the gate value
  have hFle : farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
      ≤ 2 * farCStar * Real.log X ^ (-(1009 : ℝ) / 90000) := by
    have h := t0d_far_le (X := X) (by linarith)
    nlinarith [farCStar_nonneg]
  have hPle : Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_P_le (by linarith)
  have hcs : cSq = 20736 := rfl
  have hgrade : 8 * (cSq * (t0dB X Cb + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
        + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
      ≤ 2 * (t0dC1 Cb * Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    rw [hEdef]
    unfold t0dB t0dC1
    rw [hcs]
    linarith
  refine hwide χ M Xd (2 * Xd) D X Xw (t0dB X Cb) (t0dC1 Cb) (t0dM0 X)
    hX3 hXd (by omega) le_rfl (one_le_t0dC1 hc1 hCb0) hX₀ hsqXw hB0 hD hDgate
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.2)
    ?_ hgrade hErr
  intro 𝒥 h𝒥 t ht k hkXw hk2X
  have hgt : |t| + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X := by linarith
  exact hpiece q χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 𝒥 X Xw Cb
    Dmask t k hq hsq4096 hsqXw hXwX hCb0 hCbound (hdebit 𝒥 h𝒥) hthr hgt hkXw hk2X


/-! ## §3 — THE PINNED PAIR PAYS THE ENVELOPE

The discharge fixes `(C₁′, M₀) = (cfbC₁ X (t0dC1 Cb), t0dM0 X)`.  `A2Wall.a2wall_gate_45` then
says the register's ENVELOPE conjunct sees the first exit summand at the re-cut's own rate: the
`(log X)^{1/45}` inside `cfbC₁ X C₁ = (C₁+1)(log X)^{1/90}` is paid back with `1/5000` to
spare.  This is the fact that makes the pinning worth doing — it is the whole content of the
`(45, 46)` re-cut, read at the discharged pair. -/

/-- **THE DISCHARGED PAIR DECAYS** (`t0d_envelope_decay`).

  `(cfbC₁ X C₁)²·e^{−M₀⋆/e} ≤ (C₁+1)²·(log X)^{−1/5000}`,   `M₀⋆ = t0dM0 X`.

`cfbC₁ X C₁ ^ 2 = (C₁+1)²·(log X)^{1/45}` (the crude fold's `√(seamT0 X)` squared), and
`a2wall_gate_45`'s exponent arithmetic `1/45 − 1009/45000 = −1/5000` is EXACT. -/
theorem t0d_envelope_decay {X C₁ : ℝ} (hL : 1 ≤ Real.log X) :
    cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
      ≤ (C₁ + 1) ^ 2 * Real.log X ^ (-(1 : ℝ) / 5000) := by
  have hT0 : (0 : ℝ) ≤ seamT0 X := seamT0_nonneg (by linarith)
  have hsq : Real.sqrt (seamT0 X) ^ 2 = seamT0 X := Real.sq_sqrt hT0
  have hgate := a2wall_gate_45 (X := X) (M₀ := t0dM0 X) hL (le_of_eq rfl)
  have hsq2 : cfbC₁ X C₁ ^ 2 = (C₁ + 1) ^ 2 * Real.log X ^ ((1 : ℝ) / 45) := by
    unfold cfbC₁
    rw [mul_pow, hsq]
    rfl
  rw [hsq2, mul_assoc]
  exact mul_le_mul_of_nonneg_left hgate (sq_nonneg _)

/-! ## §4 — THE REGISTER, WITH ARM 1 DISCHARGED

`M4DoorClose.DoorRowCarried` verbatim, with TWO changes and nothing else:

* the two existential slots `C₁′`, `M₀` are GONE — the discharge pins them at
  `(cfbC₁ X (t0dC1 Cb), t0dM0 X)`, and the ENVELOPE conjunct is stated there;
* the `T₀`-band INTEGRAL conjunct is replaced by `DoorRowT0Gates` — the discharge's own gate
  list, which is regime arithmetic at the block scale and nothing analytic.

Two new existential slots appear, both regime data the wide supply already needed: the dilation
window `X_w` and the dissection depth `Ddis`. -/

/-- **THE DISCHARGE'S GATE LIST** (`DoorRowT0Gates`), as one `Prop`.  Every conjunct is
`X`-side arithmetic: the hoisted threshold, the dilation frame, the `700`-threshold at the
shifted constant (`Kbox + (Dmask + 4)`, the `4` paying `dilGap`), the `Tstar` reach inside the
contour box, and the dissection depth's own decay. -/
def DoorRowT0Gates (Kbox X₀w : ℝ) (q Ddis : ℕ) (X Xw Dmask : ℝ) : Prop :=
  (X₀w ≤ Real.sqrt X) ∧ (Real.sqrt X ≤ Xw) ∧ (Xw ≤ X) ∧ (1 ≤ Ddis) ∧
    ((Ddis : ℝ) * (Xw + 1) ≤ X - 1) ∧
    (700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log (q : ℝ)
        + (q : ℝ) + (Kbox + (Dmask + 4))) ≤ Real.log (Real.log X)) ∧
    (seamT0 X + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X) ∧
    ((Ddis : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.log X ^ (-(1009 : ℝ) / 90000))

/-- **THE DOOR ROW'S CARRIED REGISTER, ARM 1 DISCHARGED** (`DoorRowCarriedT0`).  See §4's
header for the exact diff against `M4DoorClose.DoorRowCarried`. -/
def DoorRowCarriedT0 (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (Adoor M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
                (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
          (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
          (calQK (Adoor M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1 Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1 M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4DoorClose` §3: two ~98-conjunct registers are elaborated against each
-- other; no tactic search happens, every step is a projection
/-- **THE BRIDGE** (`doorRowCarried_of_t0free`).  The T₀-free register implies the carried one:
every conjunct transports verbatim, and the ONE that does not — the `T₀`-band integral — is
supplied by `m4_t0band_discharged` from `DoorRowT0Gates` plus the register's own `(X_d : ℝ) = X`,
`0 ≤ Cb`, `ShortIntervalDatum Cb` and mask-debit conjuncts.

⟦K6⟧ `Kbox` and `X₀w` are hoisted OUTSIDE every quantifier, exactly as the register's other
eight opaque constants are. -/
theorem doorRowCarried_of_t0free (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarried Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW, SW,
    Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17,
    d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35,
    d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53,
    d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71,
    d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89,
    d90, d91, d92, d93, d94, d95, d96, d97, d98⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d93
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1 Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d69 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1 Cb), t0dM0 X,
    cqS, cgS, cW, SW, Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
    d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49,
    d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67,
    d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85,
    d86, d87, d88, d89, d90, d91, d92, hT0, d94, d95, d96, d97, d98⟩

/-! ## §5 — THE REGISTER UPDATE

`M4DoorClose.m4_wave_structurally_closed` with arm (A)(1) gone.  The carried register is now

  (the coprime-supply arm) + (regime, `T₀`-free) → `¬ logChowla2Fails R.eps R.x R.ω`. -/

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed`'s own budget: its register mentions `DoorRowCarriedT0`
-- under six binders, and that is the whole cost
/-- **THE M4 WAVE, `T₀`-ARM DISCHARGED** (`m4_wave_closed_T0_discharged`).
`M4DoorClose.m4_wave_structurally_closed` composed with §4's bridge: the register's ARM-1 line
now reads `DoorRowCarriedT0`, i.e. the `T₀`-band integral is DERIVED, not assumed.  What remains
carried is ONE analytic arm — the coprime supply `M4CoprimeBlockMeanSq` — plus regime
arithmetic. -/
theorem m4_wave_closed_T0_discharged (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloor M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (H : ℝ) ≤ (2 : ℝ) ^ (21845 : ℕ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq R M
              (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed Qm
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hlogcap harc hcp
  refine hR δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv ?_ hlogcap harc hcp
  intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
  haveI : NeZero q := ⟨by omega⟩
  have hqQm : q ≤ Qm := by
    have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hRq
  exact hbridge Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q χ M
    (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
    (hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)

end Salt.MR

end
