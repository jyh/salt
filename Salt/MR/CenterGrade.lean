/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The centre supply's grade pages

The centre supplies (`CenterSupply` · `CofactorGrade` · `GradeWindowC` · `SupStation` ·
`SupplyGeneric` · `CaseASocket` · `CaseAWide` · `SPartStation`) each convert the two error legs
of the centre composition, the desmooth cost `k/√(log k) + 1` and the `S1′` error, into one
`X`-scale term `4·k·(log X)^{−1/2+1/1000}`. Each file carried its own private copy of that
conversion and of the elementary facts it uses. They are stated here once.

## Main results
* `center_error_grade` — the dyadic window `X − 1 < k ≤ 2X`, error `D·k·loglog k/log k`.
* `center_error_grade_W` — the same window, error `D·k·W/log k` with `W ≤ √(log k)`.
* `center_error_grade_wide` — the window `√X ≤ k`, error `C·k·W/log k` with `W ≤ √(log k)`.
* the elementary facts: `rpow_neg_half_eq`, `two_log_le_self`, `twentyfive_le_exp_eight`,
  `exp_two_lt_ten`.
-/

namespace Salt.MR

/-- `L^{−1/2} = 1/√L`. -/
theorem rpow_neg_half_eq {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (the `√X`-route: `log X = 2 log √X ≤ 2(√X−1)`, then
`4√X − 4 ≤ X` is `(√X−2)² ≥ 0`). -/
theorem two_log_le_self {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
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

/-- `25 ≤ exp 8` (used only to place the threshold above `16`). -/
theorem twentyfive_le_exp_eight : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- `exp 2 < 10` — the numeral behind the `y`-page's `c₀ − 2η > 0` gate at a free `Y`. -/
theorem exp_two_lt_ten : Real.exp 2 < 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith only [h1, h0, h2]

/-- **THE GRADE PAGE (`center_error_grade`).**  The two error legs of the centre
composition — the desmooth cost `h+1 = k/√(log k) + 1` and the S1′ `E`-error, already
reduced to `D·k·loglog k/log k` — are converted into the SINGLE `X`-scale term
`4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions, each elementary: `log k ∈ [L/2, 2L]` (the window, `L := log X`);
`loglog k / log k ≤ 4·loglog X / log X`, absorbed by `hB` (A-6 at the pinned `ε = 1/1000`);
`1/√(log k) ≤ 2/√L` and `1 ≤ k/√L` (the latter from `2·log X ≤ X`, `two_log_le_self`). -/
theorem center_error_grade {D X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * X)
    (hB : 4 * D * Real.log (Real.log X) * Real.log X ^ (-(1 : ℝ))
        ≤ Real.log X ^ (-(1 : ℝ) + 1 / 1000)) :
    D * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight hX8
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
  have hLkhi : Lk ≤ L + Real.log 2 := by
    have h1 : Lk ≤ Real.log (2 * X) := Real.log_le_log hk0 hk2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hLkhalf : L / 2 ≤ Lk := by linarith
  have hLk2L : Lk ≤ 2 * L := by linarith
  have hlogLk0 : (0 : ℝ) ≤ Real.log Lk := Real.log_nonneg hLk1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  -- STEP A/B/C — `loglog k / log k ≤ 4·loglog X / log X`
  have hlogLk : Real.log Lk ≤ 2 * Real.log L := by
    have h1 : Real.log Lk ≤ Real.log (2 * L) := Real.log_le_log hLk0 hLk2L
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hstepC : Real.log Lk / Lk ≤ 4 * (Real.log L / L) := by
    have hq0 : (0 : ℝ) ≤ 4 * (Real.log L / L) := by positivity
    have h1 : 4 * (Real.log L / L) * (L / 2) ≤ 4 * (Real.log L / L) * Lk :=
      mul_le_mul_of_nonneg_left hLkhalf hq0
    have h2 : 4 * (Real.log L / L) * (L / 2) = 2 * Real.log L := by
      field_simp
      ring
    rw [div_le_iff₀ hLk0]
    linarith
  -- STEP D — the A-6 absorption at the pin
  have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
  have hPmono : L ^ (-(1 : ℝ) + 1 / 1000) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hstepD : D * (Real.log Lk / Lk) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : D * (Real.log Lk / Lk) ≤ D * (4 * (Real.log L / L)) :=
      mul_le_mul_of_nonneg_left hstepC hD0
    have h2 : D * (4 * (Real.log L / L)) = 4 * D * Real.log L * L ^ (-(1 : ℝ)) := by
      rw [hLinv]; field_simp
    linarith
  -- STEP E — the desmooth leg
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
      rw [rpow_neg_half_eq hL0]
      field_simp
    linarith
  -- STEP F — `1 ≤ k·L^{−1/2}`
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP G — assemble
  have hPnn : (0 : ℝ) ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hGmono : L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : D * ((k : ℝ) * (Real.log Lk / Lk))
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h := mul_le_mul_of_nonneg_left hstepD hk0.le
    calc D * ((k : ℝ) * (Real.log Lk / Lk)) = (k : ℝ) * (D * (Real.log Lk / Lk)) := by ring
      _ ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := h
  have hterm2 : (k : ℝ) * L ^ (-(1 : ℝ) / 2)
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-- **THE `y`-GENERIC GRADE PAGE (`center_error_grade_W`).**  `center_error_grade`
with the pin's `loglog k` replaced by a FREE weight `W` capped by
`√(log k)`.  The two error legs of the centre composition — the desmooth cost
`h+1 = k/√(log k) + 1` and the `S1′` `E`-error, reduced to `D·k·W/log k` — become the single
`X`-scale term `4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions: `W/log k ≤ 1/√(log k)` (the cap); `1/√(log k) ≤ 2/√L` and
`1 ≤ k/√L` (the window, `L := log X`, with `2·log X ≤ X`); and the absorption
`2D·(log X)^{−1/2} ≤ (log X)^{−1/2+1/1000}` supplied by `hB` (A-6 at the pinned
`ε = 1/1000`, through `loglog X ≥ 1`).

Where `center_error_grade` spends A-6 on the `loglog k/log k` shape, this page spends it on
the constant alone — which is why the cap `W ≤ √(log k)` is exactly enough. -/
theorem center_error_grade_W {D W X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * D * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    D * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight hX8
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
      rw [rpow_neg_half_eq hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
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

/-- **THE WIDE-WINDOW GRADE PAGE (`center_error_grade_wide`).**  `center_error_grade_W` on
the wide window `√X ≤ k` in place of `X − 1 < k`, with the same cap `W ≤ √(log k)` and the
same absorption `hB`.

  `C·k·(W/log k) + (k/√(log k) + 1) ≤ 4·k·(log X)^{−1/2+1/1000}`   on `√X ≤ k`. -/
theorem center_error_grade_wide {C W X : ℝ} {k : ℕ} (hC0 : 0 ≤ C)
    (hX8 : Real.exp 8 ≤ X) (hkw : Real.sqrt X ≤ (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * C * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    C * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight hX8
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
      rw [rpow_neg_half_eq hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * Lx ^ (-(1 : ℝ) / 2) := by
    have hLX : Lx ≤ X := by
      rw [hLdef]; linarith [Real.log_le_sub_one_of_pos hX0]
    have hsk : Real.sqrt Lx ≤ (k : ℝ) := le_trans (Real.sqrt_le_sqrt hLX) hkw
    rw [rpow_neg_half_eq hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
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

end Salt.MR
