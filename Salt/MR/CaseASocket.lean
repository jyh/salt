/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetGradedPrice
import Salt.MR.SupplyGeneric

/-!
# `CaseASocket` — THE `y₂` CASE-A WINDOW-FLOOR CHAIN (`USetGradedPrice`'s ONE open page)

`USetGradedPrice` carries exactly one page as a named socket: `CaseASocket2` (:122), the
`y₂` twin of `CofactorSupply.caseA_partial_supply_slice`.  Its module docstring's
window-alignment verdict says why the LANDED CASE-A page cannot feed it — the landed slice's
`hMwin` lives on the `T*`-windows, and `T*₂ < T*` throughout the live range, so the split
window the `q = 3/4` repair forces is SMALLER than the windows the landed supply consumes.

This file closes that page.  The route is the one `PinFamily2` §3 lays out for the BALL arm,
re-run with the exponent `c` FREE and the floor binder in WINDOW form:

* `PinFamily2` §3 is the pin template (`joint_supF_pin_trunc2`, `joint_cs_trunc_pin2`,
  `crossKer_width_pin_const2`, `beta_integral_pin_const2`, `rhs_grade_at_scale_trunc2`) —
  every one of them at `c = 1/(2e)` and with the seam-shaped floor (`hXk`/`hgate`/`hmin`);
* `GradeWindowC` is the `c`-template (`joint_supF_pin_atC`, `joint_cs_trunc_pinC`,
  `rhs_grade_at_scale_windowC`) — free `c`, window floor `hMwin`, but at the CORPUS pin
  `y = L⁴`, `η = 1/log y`.

The two are merged here at `y = ypin2 L`, `η = eta2 L`, `T = Tstar2 k L`, `c` free under its
three gates `0 < c`, `c ≤ 1/e`, `2c < 1` (law #253: all three in-statement).

## THE MIXED-PIN CONVENTION, unchanged

⟦V7⟧'s width ruling is in force verbatim: the SERIES SPLIT runs at `y₂` while the WIDTH
amplitude stays at the old scale `L⁴` (`PinFamily2.crossKer_width_pin_const2`, which is
already `c`-free and is CITED, not cloned).  So the main term's constant is
`gradeAbsConstC c Cb` — `GradeWindowC.rhsAgradeConstC_le` applies UNCHANGED at `y := L⁴`.

## ⚑ THE DATUM-POSITION FINDING (§0) ⚑

`SupplyGeneric.center_halasz_supply_Y` is `Y`-generic, `B`-abstract and centre-uniform — but
its `∃ X₀` sits UNDER the datum `g` (`{g} (hg) (t₀) (Y) : ∃ X₀, ∀ t₁ X N B, …`).  The CASE-A
socket needs the threshold uniform over the DAMPING PARAMETER `x ∈ [0,1]`, because
`CaseASocket2` binds `x` outside everything; the datum it feeds the supply is
`gxDatum g P Q x`, one per `x`.  A per-datum `∃ X₀` cannot be hoisted over that family.

`CofactorGrade.center_halasz_supply_A` is the same hoisting done once at the CORPUS pin (its
docstring says so in as many words), and it is the reason the landed CASE-A slice has a
datum-free threshold.  §0 is that hoisting at a free `Y`: `center_halasz_supply_YA`, the
verbatim transplant of `center_halasz_supply_Y` with `g`, `t₀` moved INSIDE the `∃`.  The
witness `max (max (XA+1) XB) (e^8)` never mentioned the datum — `prop21_unconditional_uniform_absC`
and `loglog_absorb_pow_pin` are both datum-hoisted already — so the proof body is unchanged
byte-for-byte and only the `intro` line moves.  `SupplyGeneric`'s three `CenterSupply`
privates plus `center_error_grade_Y` are `private` there and are re-derived here verbatim
under a `_CA` suffix (the house's re-derivation convention).

## The stones

* **§0** `center_halasz_supply_YA` — the `Y`-generic centre supply, `∃ X₀` DATUM-HOISTED.
* **§1** the `c`-generic integrability/continuity privates at `y₂` (`RHSGradeC`'s `_GC`
  page and `PinFamily2`'s `_2` page, merged under a `_2C` suffix).
* **§2** `joint_supF_pin_at2C`, `joint_supF_pin_window2C`, `joint_cs_trunc_pin2C`,
  `jointIntegrableAtC_pin2_free` — S-A/S-C/S-D at `y₂` with `c` free and the floor in window
  form.  The integrability bundle is DISCHARGED here (`JointPlumb.jointIntegrableAt_of_gates`
  is `y`-generic; only `jointIntegrableAt_pin` is pinned), so `PinFamily2`'s `hInt` socket
  does not reappear.
* **§3** `beta_integral_pin_const2C` — the width face at the DECOUPLED width, `c` free.
* **§4** `rhs_grade_at_scale_window2C` — the grade at scale, `y₂`, free `c`, window floor.
* **§5** `caseA_rhs_socket2` — the `prop21RHS` socket at the `y₂` pins, far arm priced by
  `PinFamily.hfar_star2` at `T*₂` (ADDITIVE, never absorbed), exit `caseAS2`-shaped.
* **§6** `caseA_partial_supply2`, `caseA_slice2`, and
  **`caseASocket2_discharged` : `CaseASocket2` PROVEN** — `hUG34_fully_priced`'s CASE-A
  condition drops.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8.3 pp. 27–29;
`docs/exploration/hsup-design.md` ⟦V6b⟧/⟦V7⟧.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators Topology

/-! ## §0 — the `Y`-generic centre supply, with the `∃ X₀` DATUM-HOISTED

`SupplyGeneric`'s §1/§2 privates, re-derived verbatim under a `_CA` suffix. -/

/-- `L^{−1/2} = 1/√L` for `L > 0` (`CenterSupply.rpow_neg_half_eq`, re-derived). -/
private lemma rpow_neg_half_eq_CA {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (`CenterSupply.two_log_le_self`, re-derived). -/
private lemma two_log_le_self_CA {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs4 : (4 : ℝ) ≤ Real.sqrt X := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hX
  have hlog : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  nlinarith [hs4, hlog, hsq, hhalf]

/-- `25 ≤ exp 8` (`CenterSupply.twentyfive_le_exp_eight`, re-derived). -/
private lemma twentyfive_le_exp_eight_CA : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- `exp 2 < 10` — the numeral behind the `y`-page's `c₀ − 2η > 0` gate at a free `Y`. -/
private lemma exp_two_lt_ten_CA : Real.exp 2 < 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-- **THE `y`-GENERIC GRADE PAGE (`center_error_grade_CA`).**  `CenterSupply`'s
`center_error_grade` with the pin's `loglog k` replaced by a FREE weight `W` capped by
`√(log k)`.  The two error legs of the centre composition — the desmooth cost
`h+1 = k/√(log k) + 1` and the `S1′` `E`-error, reduced to `D·k·W/log k` — become the single
`X`-scale term `4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions: `W/log k ≤ 1/√(log k)` (the cap); `1/√(log k) ≤ 2/√L` and
`1 ≤ k/√L` (the window, `L := log X`, with `2·log X ≤ X`); and the absorption
`2D·(log X)^{−1/2} ≤ (log X)^{−1/2+1/1000}` supplied by `hB` (A-6 at the pinned
`ε = 1/1000`, through `loglog X ≥ 1`).

Where `center_error_grade` spends A-6 on the `loglog k/log k` shape, this page spends it on
the constant alone — which is why the cap `W ≤ √(log k)` is exactly enough. -/
private lemma center_error_grade_CA {D W X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * D * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    D * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_CA hX8
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hkX2 : X / 2 ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  set L := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set Lk := Real.log (k : ℝ) with hLkdef
  have hLklo : L - Real.log 2 ≤ Lk := by
    have h1 : Real.log (X / 2) ≤ Lk := Real.log_le_log (by linarith) hkX2
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hLkhalf : L / 2 ≤ Lk := by linarith
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
  -- STEP B — the window: `k/√(log k) ≤ 2·k·L^{−1/2}` and `1 ≤ k·L^{−1/2}`
  have hsqL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt L / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (L / 4) = Real.sqrt L / 2 := by
      rw [show L / 4 = L * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt L / 2 = Real.sqrt (L / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt L / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt L / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt L / 2) = 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq_CA hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self_CA (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq_CA hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP C — the absorption `2D·L^{−1/2} ≤ L^{−1/2+1/1000}` (`loglog X ≥ 1`)
  have hPnn : (0 : ℝ) ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h8 : Real.log 8 ≤ Real.log L := Real.log_le_log (by norm_num) hL8
    have h83 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have habs : 2 * D * L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have hDP : (0 : ℝ) ≤ D * L ^ (-(1 : ℝ) / 2) := mul_nonneg hD0 hPnn
    have hprod : (0 : ℝ) ≤ D * L ^ (-(1 : ℝ) / 2) * (Real.log L - 1) :=
      mul_nonneg hDP (by linarith)
    linarith
  -- STEP D — assemble
  have hGmono : L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : D * ((k : ℝ) * (W / Lk)) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : D * ((k : ℝ) * (W / Lk)) ≤ D * ((k : ℝ) / Real.sqrt Lk) :=
      mul_le_mul_of_nonneg_left hEshape hD0
    have h2 : D * ((k : ℝ) / Real.sqrt Lk) ≤ D * (2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hdes hD0
    have h3 : D * (2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)))
        = (k : ℝ) * (2 * D * L ^ (-(1 : ℝ) / 2)) := by ring
    have h4 : (k : ℝ) * (2 * D * L ^ (-(1 : ℝ) / 2))
        ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := mul_le_mul_of_nonneg_left habs hk0.le
    linarith
  have hterm2 : (k : ℝ) * L ^ (-(1 : ℝ) / 2) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-- **§0 — THE `y`-GENERIC CENTRE SUPPLY, DATUM-HOISTED** (`center_halasz_supply_YA`).
`SupplyGeneric.center_halasz_supply_Y` with the `∃ X₀` quantified BEFORE the datum `g` and
the centre `t₀` — `CofactorGrade.center_halasz_supply_A`'s hoisting, at a FREE `Y`.

The witness is `max (max (XA+1) XB) (e^8)`, where `XA` comes from
`LambdaMass.prop21_unconditional_uniform_absC` and `XB` from
`BridgeAdapt.loglog_absorb_pow_pin` — both datum-hoisted already.  So the proof body is the
landed one byte-for-byte; only the `intro` line moves.

**Why the hoisting is needed here and not upstream.**  CASE A feeds the supply the DAMPED
datum `gxDatum g P Q x`, one per damping parameter `x ∈ [0,1]`, and `CaseASocket2` binds `x`
outside its threshold.  A per-datum `∃ X₀` gives `X₀(x)`, which no `[0,1]`-uniform statement
can consume.

**LIVE GUARD (inherited).**  `SupplyGeneric`'s guard transfers verbatim: the four `Y`-gates
are the whole `Y`-contract, and nothing here commits to an exponent. -/
theorem center_halasz_supply_YA (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ t₁ X : ℝ) (N : ℕ) (B : ℝ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ B →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_unconditional_uniform_absC
  obtain ⟨XB, _hXB0, hBabs⟩ :=
    loglog_absorb_pow_pin (C := 2 * (2 * C_E + C_R)) (by positivity) ((1 : ℝ) / 2)
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro g hg t₀ t₁ X N B hXlb hXN hN2 hB0 hY10 hYsq hYlow hYlog hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_CA hX8
  have hX0 : (0 : ℝ) < X := by linarith
  -- the dyadic `k`-window
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk1 : X - 1 < (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  have hk2 : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hkN) hN2
  have hkXA : XA ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith
  -- `log k ≥ 1` (the window: `log k ≥ log X − log 2 ≥ 8 − 0.7`)
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X - Real.log 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
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
  have hY10k : (10 : ℝ) ≤ Y (k : ℝ) := hY10 k hkfl hkN
  have hlogY2 : (2 : ℝ) ≤ Real.log (Y (k : ℝ)) := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log (Y (k : ℝ)) :=
      Real.log_le_log (Real.exp_pos 2) (le_trans exp_two_lt_ten_CA.le hY10k)
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
    hkXA rfl hc₀ rfl hc' hY10k (hYsq k hkfl hkN) (hYlow k hkfl hkN)
  have hR := hRHS k hkfl hkN
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set Bs := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBsdef
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ))) with hRdef
  have hid : A = (A - Bs) + ((Bs - R) + R) := by ring
  have htri : ‖A‖ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
    calc ‖A‖ = ‖(A - Bs) + ((Bs - R) + R)‖ := by rw [← hid]
      _ ≤ ‖A - Bs‖ + ‖(Bs - R) + R‖ := norm_add_le _ _
      _ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
          linarith [norm_add_le (Bs - R) R]
  -- the `E`-error, reduced to the `D·k·log (Y k)/log k` shape
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
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
  -- the grade page
  have hgrade := center_error_grade_CA (D := 2 * C_E + C_R) (W := Real.log (Y (k : ℝ)))
    (X := X) (k := k) (by positivity) hX8 hk1 (hYlog k hkfl hkN) (hBabs X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-! ## §1 — the `c`-generic integrability/continuity privates at `y₂`

`RHSGradeC`'s four `_GC` re-derivations (they are `private` there and in `GradeConst`);
carried here under a `_2C` suffix.  All four are `y`-BLIND, so the corpus pages serve `y₂`
unchanged. -/

/-- Interval-integrability of the `c`-generic σ-integrand `rhsFboundC c M L σ/σ`.
Re-derivation of `GradeConst`'s private `rhs_sigma_div_integrableC` at the freed exponent. -/
private lemma rhs_sigma_div_integrable2C {c M L b : ℝ} (hL0 : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable (fun σ : ℝ => rhsFboundC c M L σ / σ) volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFboundC]
  refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id
    (fun σ hσ => (hpos σ hσ).ne')
  · exact continuousOn_const.mul
      (continuousOn_const.div continuousOn_id (fun σ hσ => (hpos σ hσ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL0).ne'))

/-- Interval-integrability of `bridge_adapter`'s translated `c`-generic integrand.
Re-derivation of `GradeConst`'s private `rhs_shift_integrableC` at the freed exponent. -/
private lemma rhs_shift_integrable2C {c M L η Kα : ℝ} (hL0 : 0 < L) (hη0 : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => Kα * (rhsFboundC c M L (β + 1 / L) / (β + 1 / L))) volume 0 η := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ β ∈ Set.uIcc (0 : ℝ) η, (0 : ℝ) < β + 1 / L := by
    intro β hβ
    rw [Set.uIcc_of_le hη0, Set.mem_Icc] at hβ
    linarith [hβ.1]
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFboundC]
  refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul ?_ ?_) ?_
    (fun β hβ => (hpos β hβ).ne'))
  · exact continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) (fun β hβ => (hpos β hβ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      (fun β hβ => (mul_pos (hpos β hβ) hL0).ne'))
  · fun_prop

/-- Continuity of `α ↦ a^{−α}` at a positive base.  Re-derivation of `GradeConst`'s private
`continuous_rpow_negC` (staged for the `α`-integral of W4-4; `c`-free). -/
private lemma continuous_rpow_neg2C {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative on the pin's data.  Re-derivation of `GradeConst`'s
private `widthKamp_nonneg` (`c`-free — the amplitude side never sees the exponent). -/
private lemma widthKamp_nonneg2C {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-! ## §2 — S-A / S-C / S-D at `y₂`, at a FREE `c`, with the floor in WINDOW form -/

/-- **S-A at `y₂`, at a FREE `c`** (`joint_supF_pin_at2C`).  `PinFamily.joint_supF_pin_at2`
with the exponent freed — equivalently `GradeWindowC.joint_supF_pin_atC` re-pinned to `y₂`.

The `supF` interior (`PretSupply.supF_pret_pointwise`) asks only `e ≤ y` and `α, β ≤ 1/log y`
— both DEFINITIONAL at `y₂` (`PinFamily.pin2_basic`) — plus the exponent's own two gates.

**The `c`-gates, in-statement (law #253):** `0 < c` and `c ≤ 1/e`.  Nothing else moves: the
conclusion `rhsFboundC c M L (β + 1/L)` is `rhsFbound`'s at `c = 1/(2e)` (`RHSGradeC`'s
`rhsFbound_eq_rhsFboundC`, `rfl`), so the two families never diverge. -/
theorem joint_supF_pin_at2C {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀eq : c₀ = 1 + 1 / L)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ)
    (hMt : M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFboundC c M L (β + 1 / L) := by
  obtain ⟨hk0, hL32, -, -, hηeq, hη0, hη64, -, hylo, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  have hylo' : Real.exp 1 ≤ y := by rw [hy]; exact hylo
  have hηy : η = 1 / Real.log y := by rw [hy, hη]; exact hηeq
  have hη4 : η ≤ 1 / 4 := by rw [hη]; linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := c) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) hc0 hce
    hylo' (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hηy]; exact hαη) (by rw [← hηy]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFboundC rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · nlinarith [mul_le_mul_of_nonneg_left hMt hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-- **S-C at `y₂`, at a FREE `c` — THE WINDOW-FLOOR `hsupF` BINDER**
(`joint_supF_pin_window2C`).  `GradeWindowC.joint_supF_pin_windowC` at the R2 pin:
`TruncFactor.joint_cs_factoring_trunc`'s `hsupF` binder byte-for-byte, discharged from the
SINGLE window binder

  `hMwin : ∀ t, |t − t₀'| ≤ T → M ≤ 𝔻²(ℓ(damped datum), p^{i(t−t₀')}; k)`.

No `t₀`, no `t₁`, no `R`, no `X`, no `⌊·⌋₊`: the seam geometry stays with the consumer, and
`PinFamily2.joint_supF_pin_trunc2`'s recentring supplier (`center_dist_floor_recentred`) is
ONE way to meet it, not a requirement of the chain. -/
theorem joint_supF_pin_window2C {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η T : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀eq : c₀ = 1 + 1 / L)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ, |t - t₀'| ≤ T →
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ rhsFboundC c M L (β + 1 / L) := by
  intro α hα β hβ t ht
  exact joint_supF_pin_at2C hg hc0 hce hk hL hy hη hc₀eq hα.1 hβ.1 hα.2 hβ.2 t (hMwin t ht)

/-- **S-D at `y₂`, at a FREE `c`** (`joint_cs_trunc_pin2C`).  `PinFamily2.joint_cs_trunc_pin2`
with the exponent freed and the window binder in place of `hXk`/`hgate`/`hmin`; equivalently
`GradeWindowC.joint_cs_trunc_pinC` re-pinned.  This compile is the byte-exactness certificate
for `joint_supF_pin_window2C`.

The far arm (`Ffar`, `Kfar`, `hFar`, `hKfar`) is `joint_cs_factoring_trunc`'s own — threaded
verbatim, NOT discharged and NEVER absorbed.  The only pin-sensitive gate inside is
`0 < c₀ − 2η₂`, FREER here than at the corpus pin (`η₂ ≤ 1/64` versus `η ≤ 1/8`). -/
theorem joint_cs_trunc_pin2C {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η h T Ffar Kfar : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀eq : c₀ = 1 + 1 / L) (hh0 : 0 < h)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β T ≤ Kfar)
    (hInt : JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
      t₀' M k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            rhsFboundC c M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hη64' : η ≤ 1 / 64 := by rw [hη]; exact hη64
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk1 : (1 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  refine joint_cs_factoring_trunc hk1 hh0 hη0'.le ?_ hFfar0 ?_
    (joint_supF_pin_window2C hg hc0 hce hk hL hy hη hc₀eq hMwin) hFar hKfar hIβ hIβ' hIα hIα'
  · rw [hc₀eq]; linarith
  · exact fun _ _ β hβ => rhsFboundC_nonneg _ _ _ (by linarith [hβ.1])

/-- **THE `c`-GENERIC INTEGRABILITY BUNDLE AT `y₂`, DISCHARGED**
(`jointIntegrableAtC_pin2_free`).  `GradeWindowC.jointIntegrableAtC_pin_free`'s twin at the
R2 pin.

**`PinFamily2`'s `hInt` socket does not reappear.**  `rhs_grade_at_scale_trunc2` and
`hRHS_socket_star2` both CARRY `JointIntegrableAt` as a hypothesis, because the discharged
face they had (`JointPlumb.jointIntegrableAt_pin`) is written at the corpus pin.  But the
stone one level up, `JointPlumb.jointIntegrableAt_of_gates`, is `y`-GENERIC: its only
`y`-input is `joint_cs_factoring`'s own `supF` binder, and `PinFamily.joint_supF_pin_at2` at
`M := 0` supplies exactly that at `y₂` (the same instance `far_supF_bound2` uses).  So the
four sockets cost the family gate `exp 32768 ≤ k` and nothing else — no minimality, no `M`,
no `c`-gate. -/
theorem jointIntegrableAtC_pin2_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (c : ℝ)
    {t₀' M k L c₀ y η h : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L)
    (hη : η = eta2 L) (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) :
    JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' M k L c₀ y η h := by
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk1 : (1 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hη0' : (0 : ℝ) ≤ η := by rw [hη]; exact hη0.le
  have hc2η : (0 : ℝ) < c₀ - 2 * η := by
    rw [hc₀, hη]; linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  refine jointIntegrableAtC_of_gates hk1 hh0 hL0 hη0' hc2η ?_
  refine jointIntegrableAt_of_gates hk1 hh0 hL0 hη0' hc2η ?_
  intro α hα β hβ t
  refine joint_supF_pin_at2 hg hk hL hy hη hc₀ hα.1 hβ.1 hα.2 hβ.2 t ?_
  exact pretDistSq_nonneg _ _ _
    (fun n => ellLin_norm_le_one _ hgtw n) (fun n => le_of_eq (costwist_norm _ n))

/-! ## §3 — the width face at `y₂`, at a FREE `c` (⟦V7⟧'s mixed pin, unchanged) -/

/-- **A-6a at `y₂`, at a FREE `c`** (`beta_integral_pin_const2C`).
`PinFamily2.beta_integral_pin_const2` with the exponent freed — equivalently
`RHSGradeC.beta_integral_pin_constC` re-pinned to `y₂`.

**THE MIXED PIN IS THE POINT.**  The series split runs at `y₂` while the width amplitude
stays at the OLD scale `L⁴`: `PinFamily2.crossKer_width_pin_const2` is `c`-FREE and is CITED,
not cloned, so `GradeWindowC.rhsAgradeConstC_le` applies UNCHANGED at `y := L⁴` one stone
later.  The bandwidth constraint ⟦V7⟧ found broken at `y₂` never appears — it is the gate of
a CHOICE (`A = (y/2)^{1/8}`) that is not made here.

**The `c`-gates, in-statement (law #253):** `0 < c` and `2c < 1` —
`PretSupply.joint_sigma_integral`'s own two, the σ-cutoff's honest convergence boundary. -/
theorem beta_integral_pin_const2C (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀' M k L c₀ y η h α : ℝ} (hc0 : 0 < c) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hM0 : 0 ≤ M)
    (hα0 : 0 ≤ α) (hαη : α ≤ η)
    (hIβ : IntervalIntegrable (fun β => rhsFboundC c M L (β + 1 / L)
        * crossKer g k h y c₀ t₀' α β) volume 0 η) :
    (∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L) * crossKer g k h y c₀ t₀' α β)
      ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L := by
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, hηL, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hη64' : η ≤ 1 / 64 := by rw [hη]; exact hη64
  have hLη : 1 / L ≤ η := by rw [hη]; linarith
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hy40 : (0 : ℝ) < L ^ 4 := by positivity
  have hK0 : (0 : ℝ) ≤ widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α) :=
    mul_nonneg (widthKamp_nonneg2C hCb0 hk0 hh0 hy40) (Real.rpow_nonneg hkh0.le _)
  have hcross : ∀ β ∈ Icc (0 : ℝ) η,
      crossKer g k h y c₀ t₀' α β
        ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * (1 / (β + 1 / L)) := by
    intro β hβ
    rw [hy]
    exact crossKer_width_pin_const2 g hg hCb0 hCbound hk hL hc₀ hh rfl hα0 hβ.1
      (by linarith [hβ.2])
  have hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ rhsFboundC c M L (β + 1 / L) := by
    intro β hβ
    exact rhsFboundC_nonneg c M L (by linarith [hβ.1])
  have hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ rhsFboundC c M L σ := by
    intro σ hσ
    exact rhsFboundC_nonneg c M L (lt_of_lt_of_le hLinv0 hσ.1)
  have hIσ := rhs_sigma_div_integrable2C (c := c) (M := M) (L := L) (b := 2 * η) hL0
    (by linarith)
  have hBA := bridge_adapter (g := g) (X := k) (h := h) (y := y) (c₀ := c₀) (t₀ := t₀')
    (L := L) (η := η) (Kα := widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) (α := α)
    (supF := fun _ β => rhsFboundC c M L (β + 1 / L)) (Fbound := rhsFboundC c M L)
    hL0 hLη hK0 hsup0 hcross (fun β _ => le_rfl) hFnn hIβ
    (rhs_shift_integrable2C hL0 hη0'.le) hIσ
  refine le_trans hBA ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hlogk3 : (3 : ℝ) ≤ Real.log k := by rw [← hL]; linarith
  rw [hL]
  exact joint_sigma_integral (Fbound := rhsFboundC c M (Real.log k))
    (c := c) (X := k) (b := 2 * η) (M := M) (CSF := rhsCSF)
    hc0 hc1 hlogk3 hM0 rhsCSF_pos.le (by rw [← hL]; linarith) (by rw [← hL]; exact hIσ)
    (fun σ _ => le_rfl)

/-! ## §4 — THE GRADE AT SCALE at `y₂`, at a FREE `c`, in WINDOW-FLOOR form -/

-- MEASURED: no `maxHeartbeats` bump.  `PinFamily2.rhs_grade_at_scale_trunc2` and
-- `FarStar`/`SupClose`'s twins all need `800000` because their `M` is the opaque
-- `pretDistSq (seamCoeff (ellLin g) 1 t₀) (costwist t₁) X`, repeated across both integrals.
-- The WINDOW form carries a bare free real `M` instead — the seam geometry never enters the
-- statement — and the whole file elaborates inside the default budget.
/-- **S-E at `y₂`, at a FREE `c` — THE GRADE AT SCALE IN WINDOW-FLOOR FORM**
(`rhs_grade_at_scale_window2C`).  `PinFamily2.rhs_grade_at_scale_trunc2` and
`GradeWindowC.rhs_grade_at_scale_windowC` merged:

  `‖prop21RHS (damped datum) t₀' k h c₀ y₂ η₂‖
     ≤ gradeAbsConstC c Cb · k · e^{−c·M} + (1/π)·η₂²·(Ffar·Kfar)`.

**The floor binder is the window one alone** — `hXk`, `hgate`, `hmin`, `R`, `t₀`, `t₁`, `X`
are all gone, replaced by

  `hMwin : ∀ t, |t − t₀'| ≤ T → M ≤ 𝔻²(ℓ(damped datum), p^{i(t−t₀')}; k)`,

which is EXACTLY what the chain consumes (`joint_supF_pin_window2C`), at the contour's own
centre `t₀'`.  `M` is a free real: the consumer names it.

**The main term is the CORPUS one** — same `gradeAbsConstC c Cb`, no `y₂` in it.  That is
⟦V7⟧'s width ruling cashed at a free `c`: the width `A` stayed at `(L⁴/2)^{1/8}`, so
`GradeWindowC.rhsAgradeConstC_le` applies unchanged at `y = L⁴` while the series split runs
at `y₂`.

**The far arm rides ADDITIVELY** (`joint_cs_factoring_trunc`'s own `Ffar`/`Kfar`, threaded
verbatim, never absorbed) — §5 prices it, at `T*₂`, by `PinFamily.hfar_star2`.

**The `c`-gates, in-statement (law #253):** `0 < c`, `c ≤ 1/e`, `2c < 1`.  At the CASE-A
exponent `c = 1/e` all three hold; at `c = 1/(2e)` this is `rhs_grade_at_scale_trunc2` with
`hMwin` in place of `hmin`. -/
theorem rhs_grade_at_scale_window2C {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀' M k L c₀ y η h T Ffar Kfar : ℝ}
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hM0 : 0 ≤ M)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ T →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β T ≤ Kfar)
    (hInt : JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
      t₀' M k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ gradeAbsConstC c Cb * k * Real.exp (-c * M)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL32, -, -, -, hη0, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hη0' : (0 : ℝ) < η := by rw [hη]; exact hη0
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk64 : Real.exp 64 ≤ k :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (64 : ℝ) ≤ 32768)) hkexp
  have hy40 : (0 : ℝ) < L ^ 4 := by positivity
  have hd : (0 : ℝ) < 1 - 2 * c := by linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hKamp0 : (0 : ℝ) ≤ widthKamp Cb k h (L ^ 4) c₀ :=
    widthKamp_nonneg2C hCb0 hk0 hh0 hy40
  have hG0 : (0 : ℝ) ≤ rhsSigmaGC c M L := by
    unfold rhsSigmaGC
    have hE : (0 : ℝ) ≤ Real.exp (c * 48) / (1 - 2 * c) := by positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  -- the truncated factoring at `y₂` and a free `c`, with the window floor as the only
  -- frequency input
  have hJ1 := joint_cs_trunc_pin2C hg hc0 hce hk hL hy hη hc₀ hh0 hMwin hFfar0 hFar hKfar
    ⟨hIβ, hIβ', hIα, hIα'⟩
  -- the MAIN term: the width face at the DECOUPLED width
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L :=
    fun α hα => beta_integral_pin_const2C _ hgtw hc0 hc1 hCb0 hCbound hk hL hy hη hc₀ hh hM0
      hα.1 hα.2 (hIβ α hα)
  have hKcont : Continuous
      (fun α : ℝ => (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L) :=
    ((continuous_rpow_neg2C hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0'.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L
      = (widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L) * ((k + h) ^ (-α)) := fun α => by
    ring
  have hpull : (∫ α in (0 : ℝ)..η,
        (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L)
      = (widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L)
          * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith [Real.add_one_le_exp (32768 : ℝ)]) hη0'.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFboundC c M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β
      ≤ (1 / Real.pi)
          * ((widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L) * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ ∫ α in (0 : ℝ)..η, (widthKamp Cb k h (L ^ 4) c₀ * (k + h) ^ (-α))
            * rhsSigmaGC c M L := hmono
      _ = (widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L)
            * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L) * (1 / L) :=
          mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  have hmaineq : (1 / Real.pi)
        * ((widthKamp Cb k h (L ^ 4) c₀ * rhsSigmaGC c M L) * (1 / L))
      = rhsAgradeConstC c Cb k h (L ^ 4) c₀ * Real.exp (-c * M) := by
    have hexpeq : Real.exp (-(c * M)) = Real.exp (-c * M) := by rw [neg_mul]
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hdne : (1 : ℝ) - 2 * c ≠ 0 := ne_of_gt hd
    unfold rhsAgradeConstC rhsSigmaGC
    rw [← hexpeq]
    field_simp
  -- the amplitude at the absolute constant: the CORPUS page, at `y = L⁴`, unchanged
  have habs : rhsAgradeConstC c Cb k h (L ^ 4) c₀ * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * k * Real.exp (-c * M) :=
    mul_le_mul_of_nonneg_right (rhsAgradeConstC_le hc1 hCb0 hk64 hL rfl hh hc₀)
      (Real.exp_nonneg _)
  have hmain := hstep.trans (le_of_eq hmaineq)
  linarith

/-! ## §5 — the `prop21RHS` socket at the `y₂` pins, far arm priced at `T*₂` -/

/-- **E-1a at `y₂`** (`caseA_rhs_socket2`).  `CofactorGrade.caseA_rhs_socket`'s twin at the
R2 pin: §4 at the damped datum `g_x = gxDatum g P Q x`, with

* the integrability bundle from `jointIntegrableAtC_pin2_free` (no `c`-gate, family gate
  only),
* the far `supF` binder from `PinFamily.far_supF_bound2` (`Ffar := farFbound (log k)` — the
  `F`-page does NOT move with the pin),
* the far kernel binder from `PinFamily.far_kernel_bound_star2` at `T := T*₂(k, log k)`,
* and the far REMAINDER priced by `PinFamily.hfar_star2` — ADDITIVELY, never absorbed —

so that the two-term exit collapses into the supply's own binder shape `‖prop21RHS‖ ≤ B·k`
with `B` scale-free.

The floor binder is the window one alone, at the contour's own centre `τ`, and on the `T*₂`
windows: `hMwin : ∀ v, |v − τ| ≤ T*₂(k, log k) → M ≤ 𝔻²(ℓ(g_x·p^{−iτ}), p^{i(v−τ)}; k)`.
That is the window `USetGradedPrice.CaseASocket2` states, and the whole reason this file
exists — the landed CASE-A page consumes `T*`, and `T*₂ < T*`.

`hW2k : W ≤ 2k` is `hfar_star2`'s own scale relation, and `W` is the SHIFTED scale: the far
numeral is `(log W)^{−1/(32e)}`.  Every constant on the exit is `x`-free and `k`-free. -/
theorem caseA_rhs_socket2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {c Cb x τ W M : ℝ} {k : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : pin2Gate ≤ (k : ℝ)) (hWe : Real.exp 1 ≤ W) (hW2k : W ≤ 2 * (k : ℝ))
    (hM0 : 0 ≤ M)
    (hMwin : ∀ v : ℝ, |v - τ| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
      M ≤ pretDistSq (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * I)))
        (costwist (v - τ)) (k : ℝ)) :
    ‖prop21RHS (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * I)) τ (k : ℝ)
        ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
        (ypin2 (Real.log (k : ℝ))) (1 / Real.log (ypin2 (Real.log (k : ℝ))))‖
      ≤ (gradeAbsConstC c Cb * Real.exp (-c * M)
          + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ) := by
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have hgtw : ∀ p : ℕ, p.Prime →
      ‖(fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist τ hp.one_lt.le, mul_one]
    exact hgx p hp
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk rfl
  have hL0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  -- the `η`-slot: the closed form `η₂` IS `1/log y₂`
  have hηeq : (1 : ℝ) / Real.log (ypin2 (Real.log (k : ℝ))) = eta2 (Real.log (k : ℝ)) :=
    (eta2_eq_inv_log hL0).symm
  -- the window-floor grade at `y₂` and a free `c`, far arm carried additively
  have hmain := rhs_grade_at_scale_window2C (g := gxDatum g P Q x) (c := c) (Cb := Cb)
    (t₀' := τ) (M := M) (k := (k : ℝ)) (L := Real.log (k : ℝ))
    (c₀ := 1 + 1 / Real.log (k : ℝ)) (y := ypin2 (Real.log (k : ℝ)))
    (η := 1 / Real.log (ypin2 (Real.log (k : ℝ))))
    (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (T := Tstar2 (k : ℝ) (Real.log (k : ℝ)))
    (Ffar := farFbound (Real.log (k : ℝ)))
    (Kfar := farKfarStar2 (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * I))
      (k : ℝ) (Real.log (k : ℝ)))
    hgx hc0 hce hc1 hCb0 hCbound hk rfl rfl hηeq rfl rfl hM0 hMwin
    (farFbound_nonneg hL0.le) (far_supF_bound2 hgx hk rfl rfl hηeq rfl)
    (far_kernel_bound_star2 hk rfl rfl hηeq rfl)
    (jointIntegrableAtC_pin2_free hgx c hk rfl rfl hηeq rfl rfl)
  -- the far remainder, priced at `T*₂` and at the SHIFTED scale `W`
  have hfar := hfar_star2 hgtw hk (L := Real.log (k : ℝ)) rfl rfl hηeq hWe hW2k
  have hring : (gradeAbsConstC c Cb * Real.exp (-c * M)
        + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ)
      = gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * M)
        + farCStar2 * (k : ℝ) * Real.log W ^ (-(1 / (32 * Real.exp 1))) := by ring
  rw [hring]
  linarith

/-! ## §6 — the partial-sum supply at `y₂`, the per-`x` slice, and THE SOCKET -/

/-- **E-1b at `y₂`** (`caseA_partial_supply2`).  §0 ∘ §5: under the window floor on the
`T*₂`-windows, the twisted partial sums of the DAMPED datum are linear with the R2 CASE-A
constant,

  `‖∑_{n≤k} ℓ(g_x)(n)·n^{−it}‖ ≤ caseAS2 c Cb M W · k`,   `⌊W⌋₊ ≤ k ≤ N`,

**uniformly over the damping parameter `x ∈ [0,1]`** — which is what `CaseASocket2` binds,
and why §0's datum hoisting is needed.

The split point is fed to `center_halasz_supply_YA` as `Y := ypin2 ∘ log`, and its four
`Y`-gates are `PinFamily.pin2_basic` NUMERALS at `y₂`, not eventual facts:
`10 ≤ y₂` (from `131072 ≤ y₂`), `y₂ ≤ √k`, `√(log k) ≤ y₂`, and the ONE new gate
`log y₂ = L^{2/5} ≤ L^{1/2} = √(log k)`, true for every `L ≥ 1`.

Every constant on the exit is `x`-free and `k`-free.  `W` is the SHIFTED scale: the two
threshold gates `X₀ ≤ W`, `e ≤ W` and the family gate on the row are stated there
(law #253). -/
theorem caseA_partial_supply2 :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ) (c Cb t W M : ℝ) (N : ℕ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ W → Real.exp 1 ≤ W → W ≤ (N : ℝ) → (N : ℝ) ≤ 2 * W →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → pin2Gate ≤ (k : ℝ)) → 0 ≤ M →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq
                (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * I)))
                (costwist (v - t)) (k : ℝ)) →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseAS2 c Cb M W * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := center_halasz_supply_YA (fun z => ypin2 (Real.log z))
  refine ⟨max X₀ (Real.exp 1), lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro g hg P Q c Cb t W M N hc0 hce hc1 hCb0 hCbound hWlb hWe hWN hN2 hkpin hM0 hMwin x hx
  have hX₀W : X₀ ≤ W := le_trans (le_max_left _ _) hWlb
  have hW1 : (1 : ℝ) ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx.1 hx.2 hg p hp
  -- the far/grade constant is nonneg
  have hB0 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1))) := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h2 : (0 : ℝ) ≤ Real.log W ^ (-(1 / (32 * Real.exp 1))) :=
      Real.rpow_nonneg (Real.log_nonneg hW1) _
    have h3 : (0 : ℝ) ≤ farCStar2 := farCStar2_nonneg
    have h4 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
    nlinarith
  -- THE FOUR `Y`-GATES at `Y = y₂ ∘ log`, all numerals at the family gate
  have hY10 : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → (10 : ℝ) ≤ ypin2 (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, hybig, -, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    linarith
  have hYsq : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
      ypin2 (Real.log (k : ℝ)) ≤ Real.sqrt (k : ℝ) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hysq, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    exact hysq
  have hYlow : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
      Real.sqrt (Real.log (k : ℝ)) ≤ ypin2 (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlow, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    exact hlow
  have hYlog : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
      Real.log (ypin2 (Real.log (k : ℝ))) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    intro k h1 h2
    obtain ⟨-, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic (hkpin k h1 h2) rfl
    have hL1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
    rw [log_ypin2, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  -- the `hRHS` binder: §5 at each scale of the window
  have hRHS : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => gxDatum g P Q x p
            * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (ypin2 (Real.log (k : ℝ))) (1 / Real.log (ypin2 (Real.log (k : ℝ))))‖
        ≤ (gradeAbsConstC c Cb * Real.exp (-c * M)
            + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ) := by
    intro k hk1 hk2
    have hk := hkpin k hk1 hk2
    have hkexp : Real.exp 32768 ≤ (k : ℝ) := hk
    have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 32768) hkexp
    have hW2k : W ≤ 2 * (k : ℝ) := by
      have h1 : W < (⌊W⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W
      have h2 : ((⌊W⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
      have h3 : (1 : ℝ) ≤ (k : ℝ) := by
        linarith [Real.add_one_le_exp (32768 : ℝ)]
      linarith
    simp only [zero_add]
    exact caseA_rhs_socket2 hg P Q hx.1 hx.2 hc0 hce hc1 hCb0 hCbound hk hWe hW2k hM0
      (hMwin x hx k hk1 hk2)
  -- the supply, at `t₀ = 0`, `t₁ = t`, at the damped datum, split point `y₂`
  have hsup := hsupply (gxDatum g P Q x) hgx 0 t W N
    (gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))) hX₀W hWN hN2 hB0
    hY10 hYsq hYlow hYlog hRHS
  intro k hk1 hk2
  have h := hsup k hk1 hk2
  rw [sum_seamCoeff_zero_center] at h
  refine h.trans (le_of_eq ?_)
  unfold caseAS2
  ring

/-- **THE PER-`x` CASE-A SUPPLY AT `y₂`** (`caseA_slice2`).  `caseA_partial_supply2` for ONE
damping parameter, with the floor stated in the transported (bare-datum) slot:

  `∀ k ∈ [⌊W⌋₊, N], ∀ v, |v − t| ≤ T*₂(k, log k) → M ≤ 𝔻²(ℓ(g_x), p^{iv}; k)`
  `⟹  ∀ k ∈ [⌊W⌋₊, N], ‖∑_{n≤k} ℓ(g_x)(n)·n^{−it}‖ ≤ caseAS2 c Cb M W · k`.

`CofactorSupply.caseA_partial_supply_slice`'s device, verbatim: instantiating §6 at the datum
`g_x` and the EMPTY block window `(P,Q) = (1,0)` — where the damping is the identity for every
parameter (`CofactorSupply.gxDatum_trivial_window`) — turns both `∀x`s into the single
`x`-slice, and `CofactorSupply.caseA_floor_slot` moves the floor between the twisted and bare
slots.  No landed statement is touched. -/
theorem caseA_slice2 :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ) (c Cb t W M x : ℝ) (N : ℕ),
        0 ≤ x → x ≤ 1 →
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ W → Real.exp 1 ≤ W → W ≤ (N : ℝ) → (N : ℝ) ≤ 2 * W →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → pin2Gate ≤ (k : ℝ)) → 0 ≤ M →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → ∀ v : ℝ,
          |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ)) →
        ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseAS2 c Cb M W * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := caseA_partial_supply2
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg P Q c Cb t W M x N hx0 hx1 hc0 hce hc1 hCb0 hCbound hX₀W hWe hWN hN2 hkpin hM0
    hfloor
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  -- the empty-window instance: the whole damping family collapses to the single slice
  have h := hsupply (gxDatum g P Q x) hgx 1 0 c Cb t W M N hc0 hce hc1 hCb0 hCbound hX₀W hWe
    hWN hN2 hkpin hM0 ?_
  · intro k hk1 hk2
    have h0 := h 0 (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) k hk1 hk2
    simpa only [gxDatum_trivial_window] using h0
  · intro x' _ k hk1 hk2 v hv
    simpa only [gxDatum_trivial_window, caseA_floor_slot] using hfloor k hk1 hk2 v hv

/-- **THE CASE-A SOCKET AT `y₂`, DISCHARGED** (`caseASocket2_discharged`).
`USetGradedPrice.CaseASocket2` — the ONE page that file carries as a socket — PROVEN.

The socket's own binder shape is byte-fitted (Iron rule 1): the window `k₀ ≤ k ≤ M`, the
floor value `cofactorMfl X θ k₀` on the `T*₂(k, log k)` windows in the BARE-datum slot, and
the exit `caseAS2 c Cb (cofactorMfl X θ k₀) k₀ · k`.

**The gates, in-statement (law #253).**  `X₀ ≤ k₀` is §0's datum-free threshold; `pin2Gate ≤
k₀` is the R2 family gate (`USetGradedPrice.pin2Gate_le_ballQuarterThreshold` supplies it
from the consumer's `ballQuarterThreshold ≤ k₀`, so no NEW gate reaches
`cofactor_Rbd34_local`); `k₀ ≤ M ≤ 2k₀` is the dyadic window the co-factor geometry already
gives; `0 ≤ cofactorMfl X θ k₀` is `cofactor_Rbd34_local`'s own floor-value binder; and the
`c`-contract is the three `caseAS2` gates.

With this, `USetGradedPrice.hUG34_fully_priced`'s CASE-A condition
`∀ j ∈ ramI …, ∀ t, CaseASocket2 g P Q (1/e) Cb X θ₂₉₃ (kk j) (Mt j) t` is dischargeable at
every block from the block data alone. -/
theorem caseASocket2_discharged :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P Q : ℕ) (c Cb X θ : ℝ) (k₀ M : ℕ) (t : ℝ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ (k₀ : ℝ) → pin2Gate ≤ (k₀ : ℝ) → k₀ ≤ M → (M : ℝ) ≤ 2 * (k₀ : ℝ) →
        0 ≤ cofactorMfl X θ (k₀ : ℝ) →
        CaseASocket2 g P Q c Cb X θ k₀ M t := by
  obtain ⟨X₀, hX₀0, hslice⟩ := caseA_slice2
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg P Q c Cb X θ k₀ M t hc0 hce hc1 hCb0 hCbound hX₀k hk₀pin hk₀M hM2k hMfl0 x hx0
    hx1 hfloor k hk1 hk2
  have hfl : ⌊((k₀ : ℕ) : ℝ)⌋₊ = k₀ := Nat.floor_natCast k₀
  have hkexp : Real.exp 32768 ≤ (k₀ : ℝ) := hk₀pin
  have hk₀e : Real.exp 1 ≤ (k₀ : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 32768)) hkexp
  have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk₀M
  have hkpin : ∀ j : ℕ, ⌊((k₀ : ℕ) : ℝ)⌋₊ ≤ j → j ≤ M → pin2Gate ≤ (j : ℝ) := by
    intro j hj1 _
    rw [hfl] at hj1
    have hjR : (k₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    exact le_trans hk₀pin hjR
  refine hslice g hg P Q c Cb t (k₀ : ℝ) (cofactorMfl X θ (k₀ : ℝ)) x M hx0 hx1 hc0 hce hc1
    hCb0 hCbound hX₀k hk₀e hk₀MR hM2k hkpin hMfl0 ?_ k (by rw [hfl]; exact hk1) hk2
  intro k' hk1' hk2' v hv
  rw [hfl] at hk1'
  exact hfloor k' hk1' hk2' v hv

end Salt.MR
