/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorSupplier

/-!
# `CaseAWide` — THE WIDE-WINDOW CASE-A SUPPLY (the supply side's LAST stone)

`CofactorSupplier` §8 leaves the M4 supply chain with exactly ONE open page, and names it
byte-precisely: the `hInner` binder of `caseASocketGen_of_inner`, i.e. the LANDED `ellLin`
CASE-A supply (`CaseASocket.caseA_slice2`) re-cut from its DYADIC window (`⌊W⌋₊ ≤ k ≤ N ≤ 2W`)
to the WIDE window the Route-III dissection walks (`⌊k/d⌋` for `d ≤ D`, `k ∈ [k₀, M]`, which
leaves any dyadic block at once).  This file is that page, and the compose behind it.

## The route

The dyadic supply is `caseA_slice2 ∘ caseA_partial_supply2 ∘ center_halasz_supply_YA`; the
wide one is the SAME three-layer stack with the bottom layer swapped for
`SPartStation.center_halasz_supply_wide` (R6 — the centre supply at the wide window
`Xw ≤ k ≤ 2Xa`, free floor `√Xa ≤ Xw`).  Nothing above the bottom layer is window-shaped:
`CaseASocket.caseA_rhs_socket2` (§5 there) is a PER-SCALE statement whose only scale gate is
the family gate `pin2Gate ≤ k`, so it rides the wide window verbatim.

* **§0** the SEVENTH private clone.  `center_halasz_supply_wide`'s grade page
  `centerErrorGradeWide` and its two numerals (`exp_two_lt_ten_sp`,
  `twentyfive_le_exp_eight_sp`, plus `rpow_neg_half_eq_sp` which the grade page consumes) are
  `private` in `SPartStation`; the six precedent clone sites of
  `CenterSupply.center_error_grade` are enumerated at `SPartStation` :24–32.  Re-derived here
  verbatim under a `_wd` suffix — the house's private-transplant convention (`StationHoist` §1,
  `CaseASocket` §0).
* **§1** `center_halasz_supply_wideA` — THE X₀ HOIST.  `center_halasz_supply_wide`'s `∃ X₀`
  sits UNDER the datum `g` and the centre `t₀`; the consumer binds the damping parameter
  `x ∈ [0,1]` (a CONTINUUM of data `gxDatum b P Q x`) outside its threshold, so a per-datum
  `X₀(x)` cannot be hoisted after the fact.  **The hoist is BOUNDS-UNIFORM, not finite-max**:
  the landed witness `max (max (XA+1) XB) (e^8)` is built from
  `LambdaMass.prop21_unconditional_uniform_absC` and `BridgeAdapt.loglog_absorb_pow_pin`, both
  already datum-hoisted, and mentions neither `g` nor `t₀`.  So the proof body transplants
  byte-for-byte and only the `intro` line moves — exactly `StationHoist`'s
  `seam_ball_leg_station_M_hoisted` (which hoists the SAME supply's `∃X₀` over the centre
  `t₁`) and `CaseASocket` §0's `center_halasz_supply_YA` (which hoists `_Y`'s over the datum).
  A finite-max hoist would NOT have worked here: `x` ranges over the whole interval `[0,1]`.
* **§2** `caseA_partial_supply_wide` — E-1b at `y₂` on the wide window, `∀x`-uniform.
  `caseA_partial_supply2`'s proof with the window swapped; the four `Y`-gates at
  `Y := y₂ ∘ log` are `PinFamily.pin2_basic` numerals at every scale of the wide window, and
  the `hRHS` binder is `caseA_rhs_socket2` at each scale with the far arm's shifted scale
  taken at the window BOTTOM `Xw`.
* **§3** `caseA_slice_wide` — the per-`x` slice, floor in the bare-datum slot
  (`CofactorSupply.gxDatum_trivial_window` + `caseA_floor_slot`, the landed device).
* **§4** `caseA_wide_floor` — the wide window's floor, discharged from `CapFreeFloor3` by
  `CofactorSupplier.caseA_floor_of_capFreeFloor3` at the wide bottom `⌊k₀/D⌋`.
* **§5** `caseA_inner_wide` — `caseASocketGen_of_inner`'s `hInner` binder, byte-fitted.
* **§6** `caseASocketGen_wide` / `caseASocketGen_discharged_door` — `CaseASocketGen` inhabited,
  at a general coprime-multiplicative datum and at every door piece datum.
* **§7** `m4_supplier_complete` — `CofactorSocket` at the door's own un-phased co-factor datum
  with NO remaining socket.  THE SUPPLY SIDE'S LAST STONE.

## The exit constant, and why it carries TWO scales

`PinFamily2.caseAS2 c Cb M W` fuses three summands at ONE scale `W`, because the dyadic window
has only one: `W` is both the window bottom (the far arm's shifted scale) and the window's
anchor (the grade page's `X`).  The wide window has two — the bottom `Xw` and the anchor `Xa`
with `√Xa ≤ Xw` — and the far arm reads the bottom while the grade page reads the anchor.
`caseASwide` therefore carries both, and `caseASwide c Cb M W W = caseAS2 c Cb M W`
(`caseASwide_eq_caseAS2`, `rfl`).  No inequality is hidden: had we forced the landed
one-scale shape we would have had to smuggle in `Xw ≤ Xa`, which the statement does not need.

## Law #253 — every gate in the open

`X₀ ≤ √(k₀)` (the wide anchor's threshold — NOT `X₀ ≤ k₀`: the wide supply's `S1′` threshold
is read at the SMALLEST scale in the window, and `√Xa` is the free floor), `√(k₀) ≤ ⌊k₀/D⌋`
(i.e. `D ≲ √k₀` — the dilation may not push the window below the anchor's square root),
`pin2Gate ≤ ⌊k₀/D⌋` (the R2 family gate at the wide bottom), `1 ≤ D`, `D ≤ k₀`, `k₀ ≤ M`,
`M ≤ 2k₀`, and the box gate `|t| + T*₂(j, log j) ≤ 3X` on the wide window (carried rather than
derived: `T*₂` is NOT stated monotone in its scale at this generality).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8.3; the residue design v4,
`docs/exploration/m4-residue-design-0728.md`.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators Topology

/-! ## §0 — THE SEVENTH PRIVATE CLONE

`SPartStation`'s §1 privates (`rpow_neg_half_eq_sp`, `twentyfive_le_exp_eight_sp`,
`exp_two_lt_ten_sp`, `centerErrorGradeWide`), re-derived verbatim under a `_wd` suffix. -/

/-- `L^{−1/2} = 1/√L` for `L > 0` (`CenterSupply.rpow_neg_half_eq`, re-derived — `private`
there and at all six clone sites). -/
private lemma rpow_neg_half_eq_wd {Lv : ℝ} (hL : 0 < Lv) :
    Lv ^ (-(1 : ℝ) / 2) = (Real.sqrt Lv)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `25 ≤ exp 8` (`CenterSupply.twentyfive_le_exp_eight`, re-derived). -/
private lemma twentyfive_le_exp_eight_wd : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- `exp 2 < 10` — the numeral behind the `S1′` gate `0 < c₀ − 2η` at a free `Y`. -/
private lemma exp_two_lt_ten_wd : Real.exp 2 < 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-- **THE WIDE-WINDOW GRADE PAGE (`centerErrorGradeWd`) — THE SEVENTH PRIVATE CLONE.**

`SPartStation.centerErrorGradeWide` (:192), re-derived.  The six precedent homes of
`CenterSupply.center_error_grade`'s page: `CenterSupply` :407 (the original),
`SupStation` :183 (`_st`), `SupplyGeneric` :114 (`_Y`), `GradeWindowC` :724 (`_B`),
`CofactorGrade` (`_A`), `SPartStation` :192 (`Wide` — the one cloned here), and
`CaseASocket` :139 (`_CA`).

  `C·k·(W/log k) + (k/√(log k) + 1) ≤ 4·k·(log X)^{−1/2+1/1000}`   on `√X ≤ k`. -/
private lemma centerErrorGradeWd {C W X : ℝ} {k : ℕ} (hC0 : 0 ≤ C)
    (hX8 : Real.exp 8 ≤ X) (hkw : Real.sqrt X ≤ (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * C * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    C * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_wd hX8
  have hX0 : (0 : ℝ) < X := by linarith
  set Lx := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ Lx := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < Lx := by linarith
  have hL1 : (1 : ℝ) ≤ Lx := by linarith
  have hsqX0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hsqX0 hkw
  set Lk := Real.log (k : ℝ) with hLkdef
  -- the WIDE window: `log k ≥ Lx/2`
  have hLkhalf : Lx / 2 ≤ Lk := by
    have h1 : Real.log (Real.sqrt X) ≤ Lk := Real.log_le_log hsqX0 hkw
    rwa [Real.log_sqrt hX0.le] at h1
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hsqLk0 : (0 : ℝ) < Real.sqrt Lk := Real.sqrt_pos.mpr hLk0
  -- STEP A — the cap: `W/log k ≤ 1/√(log k)`
  have hsqk : Real.sqrt Lk * Real.sqrt Lk = Lk := Real.mul_self_sqrt hLk0.le
  have hcap : W / Lk ≤ 1 / Real.sqrt Lk := by
    rw [div_le_div_iff₀ hLk0 hsqLk0]
    have h1 : W * Real.sqrt Lk ≤ Real.sqrt Lk * Real.sqrt Lk :=
      mul_le_mul_of_nonneg_right hWcap hsqLk0.le
    rw [hsqk] at h1
    linarith
  have hEshape : (k : ℝ) * (W / Lk) ≤ (k : ℝ) / Real.sqrt Lk := by
    have h1 : (k : ℝ) * (W / Lk) ≤ (k : ℝ) * (1 / Real.sqrt Lk) :=
      mul_le_mul_of_nonneg_left hcap hk0.le
    rwa [mul_one_div] at h1
  -- STEP B — the window: `k/√(log k) ≤ 2·k·Lx^{−1/2}` and `1 ≤ k·Lx^{−1/2}`
  have hsqL0 : (0 : ℝ) < Real.sqrt Lx := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt Lx / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (Lx / 4) = Real.sqrt Lx / 2 := by
      rw [show Lx / 4 = Lx * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt Lx / 2 = Real.sqrt (Lx / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt Lx / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt Lx / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt Lx / 2) = 2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq_wd hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2) := by
    have hLX : Lx ≤ X := by
      rw [hLdef]; linarith [Real.log_le_sub_one_of_pos hX0]
    have hsk : Real.sqrt Lx ≤ (k : ℝ) := le_trans (Real.sqrt_le_sqrt hLX) hkw
    rw [rpow_neg_half_eq_wd hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP C — the absorption `2C·Lx^{−1/2} ≤ Lx^{−1/2+1/1000}` (`loglog X ≥ 1`)
  have hPnn : (0 : ℝ) ≤ Lx ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hlogL1 : (1 : ℝ) ≤ Real.log Lx := by
    have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h8 : Real.log 8 ≤ Real.log Lx := Real.log_le_log (by norm_num) hL8
    have h83 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have habs : 2 * C * Lx ^ (-(1 : ℝ) / 2) ≤ Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have hCP : (0 : ℝ) ≤ C * Lx ^ (-(1 : ℝ) / 2) := mul_nonneg hC0 hPnn
    have hprod : (0 : ℝ) ≤ C * Lx ^ (-(1 : ℝ) / 2) * (Real.log Lx - 1) :=
      mul_nonneg hCP (by linarith)
    linarith
  -- STEP D — assemble
  have hGmono : Lx ^ (-(1 : ℝ) / 2) ≤ Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : C * ((k : ℝ) * (W / Lk)) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : C * ((k : ℝ) * (W / Lk)) ≤ C * ((k : ℝ) / Real.sqrt Lk) :=
      mul_le_mul_of_nonneg_left hEshape hC0
    have h2 : C * ((k : ℝ) / Real.sqrt Lk) ≤ C * (2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hdes hC0
    have h3 : C * (2 * ((k : ℝ) * Lx ^ (-(1 : ℝ) / 2)))
        = (k : ℝ) * (2 * C * Lx ^ (-(1 : ℝ) / 2)) := by ring
    have h4 : (k : ℝ) * (2 * C * Lx ^ (-(1 : ℝ) / 2))
        ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) := mul_le_mul_of_nonneg_left habs hk0.le
    linarith
  have hterm2 : (k : ℝ) * Lx ^ (-(1 : ℝ) / 2) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-! ## §1 — THE X₀ HOIST: the wide centre supply with `∃ X₀` BEFORE the datum -/

/-- **THE WIDE CENTRE SUPPLY, DATUM-HOISTED** (`center_halasz_supply_wideA`).
`SPartStation.center_halasz_supply_wide` (:302) with the `∃ X₀` quantified BEFORE the datum
`g` and the centre `t₀`.

**The route: BOUNDS-UNIFORM, not finite-max.**  The landed witness
`max (max (XA+1) XB) (e^8)` comes from `LambdaMass.prop21_unconditional_uniform_absC` and
`BridgeAdapt.loglog_absorb_pow_pin` — both datum-hoisted already — and mentions neither `g`
nor `t₀`.  So the proof body is the landed one byte-for-byte and only the `intro` line moves;
`StationHoist.seam_ball_leg_station_M_hoisted` performs the same surgery on the same supply's
threshold (over the centre `t₁` there, over the datum here).

**Why a finite-max hoist could not serve.**  The consumer (`CaseASocketGen`) binds the damping
parameter `x` over the whole interval `[0,1]` and feeds the supply the datum
`gxDatum b P Q x`, one per `x`.  That family is a CONTINUUM: `max` over finitely many
instances is unavailable, and a per-datum `X₀(x)` has no uniform bound derivable from the
statement.  The hoist is the observation that the witness depends only on the `1`-boundedness
BOUNDS, which are `x`-uniform. -/
theorem center_halasz_supply_wideA (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ t₁ X Xw B : ℝ),
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_unconditional_uniform_absC
  obtain ⟨XB, _hXB0, hBabs⟩ :=
    loglog_absorb_pow_pin (C := 2 * (2 * C_E + C_R)) (by positivity) ((1 : ℝ) / 2)
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro g hg t₀ t₁ X Xw B hXlb hXw hB0 hY10 hYsq hYlow hYlog hRHS k hkXw hkup
  have hkw : Real.sqrt X ≤ (k : ℝ) := le_trans hXw hkXw
  -- the scale page at the wide window's floor `√X`
  have hsq8 : Real.exp 8 ≤ Real.sqrt X := le_trans (le_max_right _ _) hXlb
  have hsqXA1 : XA + 1 ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hsqXB : XB ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos 8) hsq8
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq25 : (25 : ℝ) ≤ Real.sqrt X := le_trans twentyfive_le_exp_eight_wd hsq8
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hX8 : Real.exp 8 ≤ X := le_trans hsq8 hsqX
  have hXB : XB ≤ X := le_trans hsqXB hsqX
  have hkXA : XA ≤ (k : ℝ) := by linarith [le_trans hsqXA1 hkw]
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hsq0 hkw
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith [le_trans hsq25 hkw]
  -- the wide window's log floor: `log k ≥ (log X)/2 ≥ 4`
  have hLX8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X / 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (Real.sqrt X) ≤ Real.log (k : ℝ) := Real.log_le_log hsq0 hkw
    rwa [Real.log_sqrt hX0.le] at h1
  have hLk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hsqLk1 : (1 : ℝ) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hLk1
  have hsqLk0 : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hhX : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hsqLk0]; nlinarith
  -- THE `Y`-PAGE at this scale
  have hY10k : (10 : ℝ) ≤ Y (k : ℝ) := hY10 k hkXw hkup
  have hlogY2 : (2 : ℝ) ≤ Real.log (Y (k : ℝ)) := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log (Y (k : ℝ)) :=
      Real.log_le_log (Real.exp_pos 2) (le_trans exp_two_lt_ten_wd.le hY10k)
    rwa [Real.log_exp] at h1
  have hlogY0 : (0 : ℝ) < Real.log (Y (k : ℝ)) := by linarith
  have hc₀ : (1 : ℝ) < 1 + 1 / Real.log (k : ℝ) := by
    have hpos : (0 : ℝ) < 1 / Real.log (k : ℝ) := by positivity
    linarith
  have hc' : (0 : ℝ) < 1 + 1 / Real.log (k : ℝ) - 2 * (1 / Real.log (Y (k : ℝ))) := by
    have hpos : (0 : ℝ) < 1 / Real.log (k : ℝ) := by positivity
    have hhalf : 2 * (1 / Real.log (Y (k : ℝ))) ≤ 1 := by
      rw [mul_one_div, div_le_one hlogY0]
      linarith
    linarith
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (X := (k : ℝ))
    (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (c₀ := 1 + 1 / Real.log (k : ℝ))
    (y := Y (k : ℝ)) (η := 1 / Real.log (Y (k : ℝ)))
    hkXA rfl hc₀ rfl hc' hY10k (hYsq k hkXw hkup) (hYlow k hkXw hkup)
  have hR := hRHS k hkXw hkup
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set Bs := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBsdef
  set Rr := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ))) with hRdef
  have hid : A = (A - Bs) + ((Bs - Rr) + Rr) := by ring
  have htri : ‖A‖ ≤ ‖A - Bs‖ + (‖Bs - Rr‖ + ‖Rr‖) := by
    calc ‖A‖ = ‖(A - Bs) + ((Bs - Rr) + Rr)‖ := by rw [← hid]
      _ ≤ ‖A - Bs‖ + ‖(Bs - Rr) + Rr‖ := norm_add_le _ _
      _ ≤ ‖A - Bs‖ + (‖Bs - Rr‖ + ‖Rr‖) := by
          linarith [norm_add_le (Bs - Rr) Rr]
  -- the `E`-error, reduced to the `C·k·log (Y k)/log k` shape
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ)
      ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    Real.log_le_log hk0 (by linarith)
  have huq : ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
      ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hLk0]
    nlinarith
  have hEle : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
          / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
        * Real.log (Y (k : ℝ))
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
      ≤ (2 * C_E + C_R) * ((k : ℝ) * (Real.log (Y (k : ℝ)) / Real.log (k : ℝ))) := by
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * Real.log (Y (k : ℝ))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ)) := by
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Y (k : ℝ))
        = (2 * C_E + C_R) * ((k : ℝ) * (Real.log (Y (k : ℝ)) / Real.log (k : ℝ))) := by
      ring
    linarith
  -- the WIDE grade page
  have hgrade := centerErrorGradeWd (C := 2 * C_E + C_R) (W := Real.log (Y (k : ℝ)))
    (X := X) (k := k) (by positivity) hX8 hkw (hYlog k hkXw hkup) (hBabs X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-! ## §2 — E-1b AT `y₂` ON THE WIDE WINDOW -/

/-- **THE WIDE-WINDOW CASE-A EXIT CONSTANT (`caseASwide`).**  `PinFamily2.caseAS2` with its
one scale split into the window's TWO: the far arm reads the window BOTTOM `Xw` (it is
`PinFamily.hfar_star2`'s shifted scale, gated by `Xw ≤ 2k`), while the grade page reads the
window's ANCHOR `Xa` (`centerErrorGradeWd`'s `X`).  On a dyadic window the two coincide, and
then `caseASwide c Cb M W W = caseAS2 c Cb M W` definitionally. -/
def caseASwide (c Cb M Xw Xa : ℝ) : ℝ :=
  gradeAbsConstC c Cb * Real.exp (-c * M)
    + farCStar2 * Real.log Xw ^ (-(1 / (32 * Real.exp 1)))
    + 4 * Real.log Xa ^ (-(1 : ℝ) / 2 + 1 / 1000)

/-- At a single scale the wide constant IS the landed `caseAS2`. -/
lemma caseASwide_eq_caseAS2 (c Cb M W : ℝ) : caseASwide c Cb M W W = caseAS2 c Cb M W := rfl

lemma caseASwide_nonneg {c Cb M Xw Xa : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hXw : 1 ≤ Xw) (hXa : 1 ≤ Xa) : 0 ≤ caseASwide c Cb M Xw Xa := by
  have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have h3 : (0 : ℝ) ≤ Real.log Xw ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg (Real.log_nonneg hXw) _
  have h4 : (0 : ℝ) ≤ Real.log Xa ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg hXa) _
  have h5 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
  have h6 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M) := mul_nonneg h1 h5
  have h7 : (0 : ℝ) ≤ farCStar2 * Real.log Xw ^ (-(1 / (32 * Real.exp 1))) :=
    mul_nonneg farCStar2_nonneg h3
  unfold caseASwide
  linarith

/-- **E-1b AT `y₂`, ON THE WIDE WINDOW** (`caseA_partial_supply_wide`).
`CaseASocket.caseA_partial_supply2` (:918) with `center_halasz_supply_YA` replaced by §1's
wide hoist: the twisted partial sums of the DAMPED datum are linear with `caseASwide` at every
scale of `[Xw, 2Xa]`, **uniformly over the damping parameter `x ∈ [0,1]`**.

Nothing but the window changed.  `caseA_rhs_socket2` (`CaseASocket` §5) is a PER-SCALE
statement whose scale gates are the family gate `pin2Gate ≤ k` and the far arm's `Xw ≤ 2k`,
both of which the wide window supplies; and the four `Y`-gates at `Y := y₂ ∘ log` are
`PinFamily.pin2_basic` numerals at each scale, as before. -/
theorem caseA_partial_supply_wide :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P Q : ℕ) (c Cb t Xa Xw M : ℝ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ Real.sqrt Xa → Real.sqrt Xa ≤ Xw → Real.exp 1 ≤ Xw →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa → pin2Gate ≤ (k : ℝ)) → 0 ≤ M →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
          ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq
                (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * I)))
                (costwist (v - t)) (k : ℝ)) →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseASwide c Cb M Xw Xa * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := center_halasz_supply_wideA (fun z => ypin2 (Real.log z))
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg P Q c Cb t Xa Xw M hc0 hce hc1 hCb0 hCbound hXlb hXw hWe hkpin hM0 hMwin x hx
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx.1 hx.2 hg p hp
  have hW1 : (1 : ℝ) ≤ Xw := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  -- the far/grade constant is nonneg
  have hB0 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar2 * Real.log Xw ^ (-(1 / (32 * Real.exp 1))) := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h2 : (0 : ℝ) ≤ Real.log Xw ^ (-(1 / (32 * Real.exp 1))) :=
      Real.rpow_nonneg (Real.log_nonneg hW1) _
    have h3 : (0 : ℝ) ≤ farCStar2 := farCStar2_nonneg
    have h4 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
    nlinarith
  -- THE FOUR `Y`-GATES at `Y = y₂ ∘ log`, all numerals at the family gate
  have hY10 : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
      (10 : ℝ) ≤ ypin2 (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, hybig, -, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    linarith
  have hYsq : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
      ypin2 (Real.log (k : ℝ)) ≤ Real.sqrt (k : ℝ) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hysq, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    exact hysq
  have hYlow : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
      Real.sqrt (Real.log (k : ℝ)) ≤ ypin2 (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlow, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    exact hlow
  have hYlog : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
      Real.log (ypin2 (Real.log (k : ℝ))) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    have hL1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
    rw [log_ypin2, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  -- the `hRHS` binder: `caseA_rhs_socket2` at each scale of the wide window
  have hRHS : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
      ‖prop21RHS (fun p => gxDatum g P Q x p
            * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (ypin2 (Real.log (k : ℝ))) (1 / Real.log (ypin2 (Real.log (k : ℝ))))‖
        ≤ (gradeAbsConstC c Cb * Real.exp (-c * M)
            + farCStar2 * Real.log Xw ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ) := by
    intro k hk1 hk2
    have hk := hkpin k hk1 hk2
    have hkexp : Real.exp 32768 ≤ (k : ℝ) := hk
    have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 32768) hkexp
    have hW2k : Xw ≤ 2 * (k : ℝ) := by linarith
    simp only [zero_add]
    exact caseA_rhs_socket2 hg P Q hx.1 hx.2 hc0 hce hc1 hCb0 hCbound hk hWe hW2k hM0
      (hMwin x hx k hk1 hk2)
  -- the supply, at `t₀ = 0`, `t₁ = t`, at the damped datum, split point `y₂`
  have hsup := hsupply (gxDatum g P Q x) hgx 0 t Xa Xw
    (gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar2 * Real.log Xw ^ (-(1 / (32 * Real.exp 1)))) hXlb hXw hB0
    hY10 hYsq hYlow hYlog hRHS
  intro k hk1 hk2
  have h := hsup k hk1 hk2
  rw [sum_seamCoeff_zero_center] at h
  refine h.trans (le_of_eq ?_)
  unfold caseASwide
  ring

/-! ## §3 — THE PER-`x` SLICE, floor in the bare-datum slot -/

/-- **THE PER-`x` WIDE CASE-A SUPPLY** (`caseA_slice_wide`).  `CaseASocket.caseA_slice2`'s
device verbatim at §2: instantiating the `∀x` face at the datum `g_x` and the EMPTY block
window `(P,Q) = (1,0)` — where the damping is the identity for every parameter
(`CofactorSupply.gxDatum_trivial_window`) — turns both `∀x`s into the single `x`-slice, and
`CofactorSupply.caseA_floor_slot` moves the floor between the twisted and bare slots. -/
theorem caseA_slice_wide :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P Q : ℕ) (c Cb t Xa Xw M x : ℝ),
        0 ≤ x → x ≤ 1 →
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ Real.sqrt Xa → Real.sqrt Xa ≤ Xw → Real.exp 1 ≤ Xw →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa → pin2Gate ≤ (k : ℝ)) → 0 ≤ M →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa → ∀ v : ℝ,
          |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ)) →
        ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseASwide c Cb M Xw Xa * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := caseA_partial_supply_wide
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg P Q c Cb t Xa Xw M x hx0 hx1 hc0 hce hc1 hCb0 hCbound hXlb hXw hWe hkpin hM0
    hfloor
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have h := hsupply (gxDatum g P Q x) hgx 1 0 c Cb t Xa Xw M hc0 hce hc1 hCb0 hCbound hXlb
    hXw hWe hkpin hM0 ?_
  · intro k hk1 hk2
    have h0 := h 0 (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) k hk1 hk2
    simpa only [gxDatum_trivial_window] using h0
  · intro x' _ k hk1 hk2 v hv
    simpa only [gxDatum_trivial_window, caseA_floor_slot] using hfloor k hk1 hk2 v hv

/-! ## §4 — THE WIDE WINDOW'S FLOOR, from the cap-free floor

`caseASocketGen_of_inner` hands its `hInner` binder a floor on `[k₀, M]` only; the dilated
scales `⌊k/d⌋` sit BELOW `k₀`, so that binder cannot serve the wide window and is discarded.
`CofactorSupplier.caseA_floor_of_capFreeFloor3` supplies the replacement: under
`CapFreeFloor3` there is no pocket anywhere on the `3X` box, so the CASE-A window floor holds
at EVERY scale below `X`, read at the wide bottom `kbot`. -/

/-- **THE WIDE WINDOW'S FLOOR** (`caseA_wide_floor`).  `caseA_floor_of_capFreeFloor3`
quantified over the wide window `[Xw, 2Xa]`, in the bare `ellLin (g_x)` slot the supply reads.

Two gates carry the geometry honestly: `2Xa ≤ X` (every scale of the window is below the
global scale, which is what the floor's descent needs) and the box gate
`|t| + T*₂(j, log j) ≤ 3X` on the window (the pocket's frequency `v` must stay inside the
`3X` box).  Neither is derived: `T*₂` is not stated monotone in its scale at this generality,
and the consumer's own `2Xa ≤ X` is free as soon as it takes the anchor `Xa := M/2`, since
`M ≤ X` is a standing `TLBlockGates34` gate. -/
theorem caseA_wide_floor {b : ℕ → ℂ} (hb : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1)
    (P Q : ℕ) {X θ Xw Xa t : ℝ} {kbot : ℕ}
    (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 b X)
    (hkbot : ((kbot : ℕ) : ℝ) ≤ Xw) (hXaX : 2 * Xa ≤ X)
    (hbox : ∀ j : ℕ, Xw ≤ (j : ℝ) → (j : ℝ) ≤ 2 * Xa →
      |t| + Tstar2 (j : ℝ) (Real.log (j : ℝ)) ≤ 3 * X) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ j : ℕ, Xw ≤ (j : ℝ) → (j : ℝ) ≤ 2 * Xa → ∀ v : ℝ,
      |v - t| ≤ Tstar2 (j : ℝ) (Real.log (j : ℝ)) →
        cofactorMfl X θ ((kbot : ℕ) : ℝ)
          ≤ pretDistSq (ellLin (gxDatum b P Q x)) (costwist v) (j : ℝ) := by
  intro x hx0 hx1 j hj1 hj2 v hv
  have hkb : kbot ≤ j := by
    have : ((kbot : ℕ) : ℝ) ≤ (j : ℝ) := le_trans hkbot hj1
    exact_mod_cast this
  have hjX : (j : ℝ) ≤ X := le_trans hj2 hXaX
  have hvbox : |v| ≤ 3 * X := by
    have h1 : |v| - |t| ≤ |v - t| := abs_sub_abs_le_abs_sub v t
    have h2 := hbox j hj1 hj2
    linarith
  have h := caseA_floor_of_capFreeFloor3 hb P Q hx0 hx1 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor
    hkb hjX hvbox (x := x) (kbot := kbot) (k := j) (v := v)
  rwa [pretDistSq_dampDatum_eq] at h

/-! ## §5 — `caseASocketGen_of_inner`'s `hInner` BINDER, BYTE-FITTED -/

/-- **THE WIDE-WINDOW INNER SUPPLY** (`caseA_inner_wide`).  The residue `CofactorSupplier` §8
names, discharged: a COMMON grade for the landed `ellLin (g_x)` partial sums at every dilated
scale `⌊k/d⌋`, `d ≤ D`, `k ∈ [k₀, M]`, uniformly over the damping parameter `x ∈ [0,1]`.

The window arithmetic is Nat division's own monotonicity: `⌊k₀/D⌋ ≤ ⌊k/d⌋ ≤ k ≤ M` for
`k₀ ≤ k ≤ M` and `1 ≤ d ≤ D`.  So the wide window `[Xw, 2Xa]` covers every dilated scale as
soon as `Xw ≤ ⌊k₀/D⌋` and `M ≤ 2Xa` — the two gates below, both in the open (law #253).

The floor is a HYPOTHESIS here, at the wide window (§4 discharges it from `CapFreeFloor3`);
the exit is `caseASwide`, the two-scale twin of the landed `caseAS2`. -/
theorem caseA_inner_wide :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (b : ℕ → ℂ), (∀ p, p.Prime → ‖b p‖ ≤ 1) →
      ∀ (P Q : ℕ) (c Cb t Xa Xw Mfl : ℝ) (k₀ M D : ℕ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ Real.sqrt Xa → Real.sqrt Xa ≤ Xw → Real.exp 1 ≤ Xw →
        Xw ≤ ((k₀ / D : ℕ) : ℝ) → (M : ℝ) ≤ 2 * Xa → 1 ≤ D →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa → pin2Gate ≤ (k : ℝ)) → 0 ≤ Mfl →
        (∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ j : ℕ, Xw ≤ (j : ℝ) → (j : ℝ) ≤ 2 * Xa → ∀ v : ℝ,
          |v - t| ≤ Tstar2 (j : ℝ) (Real.log (j : ℝ)) →
            Mfl ≤ pretDistSq (ellLin (gxDatum b P Q x)) (costwist v) (j : ℝ)) →
        ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ d : ℕ, 1 ≤ d → d ≤ D →
          ‖∑ m ∈ Finset.Icc 1 (k / d), ellLin (gxDatum b P Q x) m * eIu (-t) m‖
            ≤ caseASwide c Cb Mfl Xw Xa * ((k / d : ℕ) : ℝ) := by
  obtain ⟨X₀, hX₀0, hslice⟩ := caseA_slice_wide
  refine ⟨X₀, hX₀0, ?_⟩
  intro b hb P Q c Cb t Xa Xw Mfl k₀ M D hc0 hce hc1 hCb0 hCbound hXlb hXw hWe hXwk hMXa hD1
    hkpin hMfl0 hfloor x hx0 hx1 k hk1 hk2 d hd1 hdD
  -- the dilated scale sits inside the wide window
  have hdivmono : k₀ / D ≤ k / d :=
    le_trans (Nat.div_le_div_right hk1) (Nat.div_le_div_left hdD hd1)
  have hlo : Xw ≤ ((k / d : ℕ) : ℝ) := by
    refine le_trans hXwk ?_
    exact_mod_cast Nat.cast_le.mpr hdivmono
  have hup : ((k / d : ℕ) : ℝ) ≤ 2 * Xa := by
    have h1 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k d
    have h2 : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk2
    linarith
  exact hslice b hb P Q c Cb t Xa Xw Mfl x hx0 hx1 hc0 hce hc1 hCb0 hCbound hXlb hXw hWe
    hkpin hMfl0 (fun j hj1 hj2 v hv => hfloor x hx0 hx1 j hj1 hj2 v hv) (k / d) hlo hup

/-! ## §6 — `CaseASocketGen` INHABITED -/

/-- `CaseASocketGen` is monotone in its exit constant (the conclusion is `≤ S·k`, `k ≥ 0`). -/
lemma caseASocketGen_mono {b : ℕ → ℂ} {P Q : ℕ} {X θ : ℝ} {k₀ M : ℕ} {t S S' : ℝ}
    (hSS : S ≤ S') (h : CaseASocketGen b P Q X θ k₀ M t S) :
    CaseASocketGen b P Q X θ k₀ M t S' := by
  intro x hx0 hx1 hfl k hk1 hk2
  exact le_trans (h x hx0 hx1 hfl k hk1 hk2)
    (mul_le_mul_of_nonneg_right hSS (Nat.cast_nonneg k))

/-- **`CaseASocketGen` DISCHARGED AT A GENERAL COPRIME-MULTIPLICATIVE DATUM**
(`caseASocketGen_wide`).  §5 fed to `CofactorSupplier.caseASocketGen_of_inner`, with the wide
floor discharged from `CapFreeFloor3` by §4 at the wide bottom `⌊k₀/D⌋`.

The exit is Route III's price on the wide supply:
`cSq·caseASwide + cSq·D^{−1/4}` with `cSq = 20736` (the FULL constant — the damped datum
`b·x^ω` is multiplicative on coprimes only, never completely multiplicative, so the cheap
constant does not apply; ⟦THE TRAP⟧ of `CofactorSupplier` §8).

The window is pinned: `Xw := ⌊k₀/D⌋`, since §4 states the floor's VALUE at the wide bottom and
§5 needs the window to start there.  The anchor `Xa` stays free under three gates. -/
theorem caseASocketGen_wide :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (b : ℕ → ℂ), b 1 = 1 → (∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) →
      ∀ (P Q : ℕ) (c Cb X θ t Xa : ℝ) (k₀ M D : ℕ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → Real.exp 1 ≤ Real.log X →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → CapFreeFloor3 b X →
        1 ≤ D → D ≤ k₀ →
        X₀ ≤ Real.sqrt Xa → Real.sqrt Xa ≤ ((k₀ / D : ℕ) : ℝ) →
        pin2Gate ≤ ((k₀ / D : ℕ) : ℝ) → Real.exp 1 ≤ Xa →
        (M : ℝ) ≤ 2 * Xa → 2 * Xa ≤ X →
        0 ≤ cofactorMfl X θ ((k₀ / D : ℕ) : ℝ) →
        (∀ j : ℕ, ((k₀ / D : ℕ) : ℝ) ≤ (j : ℝ) → (j : ℝ) ≤ 2 * Xa →
          |t| + Tstar2 (j : ℝ) (Real.log (j : ℝ)) ≤ 3 * X) →
        CaseASocketGen b P Q X θ k₀ M t
          (cSq * caseASwide c Cb (cofactorMfl X θ ((k₀ / D : ℕ) : ℝ))
              ((k₀ / D : ℕ) : ℝ) Xa
            + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨X₀, hX₀0, hinner⟩ := caseA_inner_wide
  refine ⟨X₀, hX₀0, ?_⟩
  intro b hb1 hbmul hble P Q c Cb X θ t Xa k₀ M D hc0 hce hc1 hCb0 hCbound hθ0 hθ32 hLX
    hPlow hQhigh hPQ hfloor hD1 hDk₀ hXlb hsqXa hpin hXae hMXa hXaX hMfl0 hbox
  set Xw : ℝ := ((k₀ / D : ℕ) : ℝ) with hXwdef
  have hbp : ∀ p : ℕ, p.Prime → ‖b p‖ ≤ 1 := fun p _ => hble p
  have hWe : Real.exp 1 ≤ Xw :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 32768)) hpin
  have hW1 : (1 : ℝ) ≤ Xw := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hXa1 : (1 : ℝ) ≤ Xa := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXae
  have hkpin : ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * Xa → pin2Gate ≤ (k : ℝ) :=
    fun k h1 _ => le_trans hpin h1
  have hS0 : 0 ≤ caseASwide c Cb (cofactorMfl X θ Xw) Xw Xa :=
    caseASwide_nonneg hc1 hCb0 hW1 hXa1
  have hfl := caseA_wide_floor hbp P Q hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor
    (kbot := k₀ / D) (Xw := Xw) (Xa := Xa) (t := t) le_rfl hXaX hbox
  exact caseASocketGen_of_inner hb1 hbmul hble P Q X θ k₀ M D t
    (caseASwide c Cb (cofactorMfl X θ Xw) Xw Xa) hD1 hDk₀ hS0
    (fun x hx0 hx1 _ => hinner b hbp P Q c Cb t Xa Xw (cofactorMfl X θ Xw) k₀ M D hc0 hce hc1
      hCb0 hCbound hXlb hsqXa hWe le_rfl hMXa hD1 hkpin hMfl0 hfl x hx0 hx1)

/-- **`CaseASocketGen` AT EVERY DOOR PIECE DATUM** (`caseASocketGen_discharged_door`).
§6 at `b := pieceDatum χ 𝒥 Pseq Qseq` — the door's inclusion–exclusion pieces `λχ̄·g_𝒥`,
which are COMPLETELY multiplicative (`CofactorSupplier.pieceDatum_mul`, no coprimality) and
hence a fortiori coprime-multiplicative, `1`-bounded and `1` at `1`.

This is the final link `CofactorSupplier` §6 names: with it, `cofactorSocket_door`'s `hA2`
binder is dischargeable from the block data and the per-piece cap-free floor alone. -/
theorem caseASocketGen_discharged_door :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ)
        (P Q : ℕ) (c Cb X θ t Xa : ℝ) (k₀ M D : ℕ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        0 < θ → θ ≤ 1 / 32 → Real.exp 1 ≤ Real.log X →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X →
        1 ≤ D → D ≤ k₀ →
        X₀ ≤ Real.sqrt Xa → Real.sqrt Xa ≤ ((k₀ / D : ℕ) : ℝ) →
        pin2Gate ≤ ((k₀ / D : ℕ) : ℝ) → Real.exp 1 ≤ Xa →
        (M : ℝ) ≤ 2 * Xa → 2 * Xa ≤ X →
        0 ≤ cofactorMfl X θ ((k₀ / D : ℕ) : ℝ) →
        (∀ j : ℕ, ((k₀ / D : ℕ) : ℝ) ≤ (j : ℝ) → (j : ℝ) ≤ 2 * Xa →
          |t| + Tstar2 (j : ℝ) (Real.log (j : ℝ)) ≤ 3 * X) →
        CaseASocketGen (pieceDatum χ 𝒥 Pseq Qseq) P Q X θ k₀ M t
          (cSq * caseASwide c Cb (cofactorMfl X θ ((k₀ / D : ℕ) : ℝ))
              ((k₀ / D : ℕ) : ℝ) Xa
            + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨X₀, hX₀0, hgen⟩ := caseASocketGen_wide
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ Pseq Qseq 𝒥 P Q' c Cb X θ t Xa k₀ M D
  exact hgen (pieceDatum χ 𝒥 Pseq Qseq) (pieceDatum_one χ 𝒥 Pseq Qseq)
    (fun m n _ => pieceDatum_mul χ 𝒥 Pseq Qseq m n) (norm_pieceDatum_le_one χ 𝒥 Pseq Qseq)
    P Q' c Cb X θ t Xa k₀ M D

/-! ## §7 — THE DOOR'S SOCKET, NO REMAINING SOCKET

`CofactorSupplier`'s `cofactorSocket_of_gen`/`cofactorSocket_door` demand their CASE-A binder
at EVERY real centre `t`, although they only ever USE it at `|t| ≤ T_ann` (the annulus the
`CofactorSocket` predicate itself quantifies).  The wide supply's floor is discharged from
`CapFreeFloor3` through the `3X` box, which costs the `t`-dependent box gate — so the
`∀ t : ℝ` form is unavailable and the `|t| ≤ T_ann` form is exactly what is provable.

The two `_tb` twins below are the landed proofs verbatim with that one binder restricted;
they are ADDITIVE (no landed statement is touched, Iron rule 1) and their bodies are
byte-identical to `cofactorSocket_of_gen`'s and `cofactorSocket_door`'s. -/

/-- `cofactorSocket_of_gen` with the CASE-A binder restricted to the annulus `|t| ≤ T_ann` —
which is the only place the landed proof reads it. -/
theorem cofactorSocket_of_gen_tb {b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hbmul : ∀ m n : ℕ, Nat.Coprime m n → b (m * n) = b m * b n) (hble : ∀ n : ℕ, ‖b n‖ ≤ 1)
    {H : ℝ} {N Xd P Q : ℕ} {Mt kk : ℕ → ℕ}
    {cq L cg Cb X θ Rrad Tann t₁ Rbar S : ℝ} (hS0 : 0 ≤ S) (hR0 : 0 < Rrad)
    (hsock : PocketSocket3Gen b P Q X θ t₁)
    (hblk : ∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j)
    (hbox : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X)
    (hA2 : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      CaseASocketGen b P Q X θ (kk j) (Mt j) t S)
    (hendGen : ∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
      ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar b := by
  intro j hj t ht hfar
  obtain ⟨-, -, -, -, -, -, hk₀th, hMN, hk₀lo, hk₀hi, hbot, hlow, hhigh, hMtop, hMX,
    hgate32, -⟩ := hblk j hj
  exact le_trans
    (cofactor_Rbd34_local_nocap3_gen hb1 hbmul hble H N Xd P Q j (Mt j) (kk j) X θ t t₁ Rrad S
      hS0 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX (hbox j hj t ht) hgate32 hR0 hfar
      hsock (hA2 j hj t ht) (hendGen j hj))
    (hRbdU j hj)

/-- `cofactorSocket_door` with the CASE-A binder restricted to the annulus, and with
⟦THE SHIFT DECOUPLING⟧ (the BAND wave) applied: the sieve SHIFT `Ps` inside `doorCofactor0`
is a fresh binder, independent of the Ramaré band bottom `P`.  The band chain reads it at
`Ps := 1` (`CofactorSupplier.doorCofactor0_at_one`). -/
theorem cofactorSocket_door_tb {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    {H : ℝ} {N Xd P Q J Ps : ℕ} {Mt kk : ℕ → ℕ}
    {cq L cg Cb X θ Rrad Tann t₁ Rbar0 S : ℝ}
    (hPs1 : 1 ≤ Ps) (hS0 : 0 ≤ S) (hR0 : 0 < Rrad)
    (hθ0 : 0 < θ) (hθ32 : θ ≤ 1 / 32) (hLX : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X θ ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset, CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X)
    (hblk : ∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j)
    (hbox : ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X)
    (hA2 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset, ∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
      CaseASocketGen (pieceDatum χ 𝒥 Pseq Qseq) P Q X θ (kk j) (Mt j) t S)
    (hendGen : ∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
      ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ (2 ^ J * Rbar0)
      (doorCofactor0 χ Pseq Qseq J Ps) := by
  refine cofactorSocket_door_of_pieces χ Pseq Qseq hPs1 (fun 𝒥 h𝒥 => ?_)
  have hble : ∀ n : ℕ, ‖pieceDatum χ 𝒥 Pseq Qseq n‖ ≤ 1 :=
    norm_pieceDatum_le_one χ 𝒥 Pseq Qseq
  exact cofactorSocket_of_gen_tb (pieceDatum_one χ 𝒥 Pseq Qseq)
    (fun m n _ => pieceDatum_mul χ 𝒥 Pseq Qseq m n) hble hS0 hR0
    (pocketSocket3Gen_of_floor3 (fun p _ => hble p) hθ0 hθ32 hLX hPlow hQhigh hPQ
      (hfloor 𝒥 h𝒥) t₁)
    hblk hbox (hA2 𝒥 h𝒥) hendGen hRbdU

/-- **THE SUPPLY SIDE'S LAST STONE** (`m4_supplier_complete`).

`CofactorSocket` — the ONE datum the whole `𝒰`/err leg reads after ⟦THE SOCKET CUT⟧ — holds
at the DOOR's own un-phased co-factor datum `b(m) = 1_𝒮(P·m)·λ(m)·χ̄(m)`, with **no remaining
socket**: every hypothesis below is either a gate on the named constants, a block-ladder fact
(`TLBlockGates34`), or the per-piece cap-free floor, which `CofactorSupplier`'s
`capFreeFloor3_pieceDatum` supplies from the assembled χ-floor's own margin.

The chain, end to end:

  `caseA_inner_wide` (§5, the wide-window `ellLin` supply)
    → `caseASocketGen_wide` (§6, via `CofactorSupplier.caseASocketGen_of_inner`, paying
      Route III's `cSq = 20736`)
    → `caseASocketGen_discharged_door` (§6, at every piece `λχ̄·g_𝒥`)
    → `cofactorSocket_of_gen_tb` (§7, `= cofactor_Rbd34_local_nocap3_gen` per block)
    → `cofactorSocket_door_tb` (§7, the `2^J`-piece triangle).

**The hypothesis list, by group.**
* the `c`-contract: `0 < c ≤ 1/e`, `2c < 1`, `0 ≤ Cb` with `ShortIntervalDatum Cb`;
* the §8.3 block window and the χ-floor's page: `1 ≤ P`, `0 < R_rad`, `0 < θ ≤ 1/32`,
  `e ≤ log X`, `P83 X θ ≤ P ≤ Q ≤ Q83 X`, and `CapFreeFloor3` at every piece;
* the block ladder: `TLBlockGates34` at every `j ∈ ramI`, plus the annulus box gate;
* THE WIDE SUPPLY'S OWN GATES, per block `j`, at the dilation depth `Dd j` and the wide
  anchor `Xa j`: `1 ≤ Dd j ≤ kk j`, `X₀ ≤ √(Xa j) ≤ ⌊kk j/Dd j⌋`, `pin2Gate ≤ ⌊kk j/Dd j⌋`,
  `e ≤ Xa j`, `Mt j ≤ 2·Xa j`, `2·Xa j ≤ X`, `0 ≤ cofactorMfl X θ ⌊kk j/Dd j⌋`, and the wide
  box gate on `[⌊kk j/Dd j⌋, 2·Xa j]`;
* the accounting: a UNIFORM ceiling `S` for the per-block CASE-A exits (`CaseASocketGen` is
  monotone in it, `caseASocketGen_mono`), the `ramRbot` endpoint charge, and the `R̄₀`
  ceiling — the two `cofactorRbdGen` charges `CofactorSupplier` §5 already carries.

**The `2·Xa j ≤ X` gate is free at the door**: taking `Xa j := Mt j/2` makes it
`TLBlockGates34`'s own `hMX`, and `Mt j ≤ 2·Xa j` an equality. -/
theorem m4_supplier_complete :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
        (H : ℝ) (N Xd P Q J Ps : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
        (cq L cg Cb X θ Rrad Tann t₁ Rbar0 c S : ℝ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ P → 1 ≤ Ps → 0 < Rrad → 0 < θ → θ ≤ 1 / 32 → Real.exp 1 ≤ Real.log X →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        (∀ 𝒥 ∈ (Finset.Icc 1 J).powerset, CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X) →
        (∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 1 ≤ Dd j) →
        (∀ j ∈ ramI H P Q, Dd j ≤ kk j) →
        (∀ j ∈ ramI H P Q, X₀ ≤ Real.sqrt (Xa j)) →
        (∀ j ∈ ramI H P Q, Real.sqrt (Xa j) ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, pin2Gate ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, Real.exp 1 ≤ Xa j) →
        (∀ j ∈ ramI H P Q, ((Mt j : ℕ) : ℝ) ≤ 2 * Xa j) →
        (∀ j ∈ ramI H P Q, 2 * Xa j ≤ X) →
        (∀ j ∈ ramI H P Q, 0 ≤ cofactorMfl X θ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann → ∀ i : ℕ,
          ((kk j / Dd j : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa j →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) →
        0 ≤ S →
        (∀ j ∈ ramI H P Q,
          cSq * caseASwide c Cb (cofactorMfl X θ ((kk j / Dd j : ℕ) : ℝ))
              ((kk j / Dd j : ℕ) : ℝ) (Xa j)
            + cSq * ((Dd j : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ S) →
        (∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
          ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3) →
        (∀ j ∈ ramI H P Q,
          cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) →
        CofactorSocket H N Xd P Q Tann Rrad t₁ (2 ^ J * Rbar0)
          (doorCofactor0 χ Pseq Qseq J Ps) := by
  obtain ⟨X₀, hX₀0, hpiece⟩ := caseASocketGen_discharged_door
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ Pseq Qseq H N Xd P Q' J Ps Mt kk Dd Xa cq L cg Cb X θ Rrad Tann t₁ Rbar0 c S
    hc0 hce hc1 hCb0 hCbound _hP1 hPs1 hR0 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor hblk hbox
    hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0 hboxw hS0 hSbd hendGen hRbdU
  refine cofactorSocket_door_tb χ Pseq Qseq hPs1 hS0 hR0 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor
    hblk hbox ?_ hendGen hRbdU
  intro 𝒥 h𝒥 j hj t ht
  refine caseASocketGen_mono (hSbd j hj) ?_
  exact hpiece q χ Pseq Qseq 𝒥 P Q' c Cb X θ t (Xa j) (kk j) (Mt j) (Dd j) hc0 hce hc1 hCb0
    hCbound hθ0 hθ32 hLX hPlow hQhigh hPQ (hfloor 𝒥 h𝒥)
    (hD1 j hj) (hDk j hj) (hX₀j j hj) (hsqXa j hj) (hpin j hj) (hXae j hj) (hMXa j hj)
    (hXaX j hj) (hMfl0 j hj) (fun i hi1 hi2 => hboxw j hj t ht i hi1 hi2)

end Salt.MR
