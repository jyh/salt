/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CenterSupply
import Salt.MR.PinFamily2

/-!
# THE `y`-GENERIC CENTRE SUPPLY (`SupplyGeneric`)

`PinFamily2`'s RESIDUAL 1: `CenterSupply.ball_sup_supplied` carries the CORPUS pin
`y = (log k)^4`, `η = 1/log((log k)^4)` LITERALLY inside its `hRHS` binder
(`CenterSupply` :477–482), so `PinFamily2.hRHS_socket_star2` — the ready `y₂`-shaped
object — cannot feed it.  This file is the `y`-GENERIC TWIN CHAIN that unblocks it.

**Iron rule 1 is respected literally**: no landed statement is touched, no existing file is
edited.  Every stone below is a NEW twin at a FREE split point `Y : ℝ → ℝ`.

## WHERE THE PIN IS ACTUALLY CONSUMED (the audit)

Reading `CenterSupply.center_halasz_supply` (:296–430) end-to-end, `(log k)^4` enters at
exactly TWO places, and NEITHER is structural:

1. **the `S1′` representation** — `LambdaMass.prop21_uniform_at_scale_absC` is invoked at
   the pin.  But that stone is itself a thin instance of `prop21_unconditional_uniform_absC`
   (`LambdaMass` :243), which is **already free in `y`**: its whole `y`-page is
   `10 ≤ y`, `y ≤ √X`, `√(log X) ≤ y`, `η = 1/log y`, `0 < c₀ − 2η`.  Skipping the pinned
   instance and calling the free stone directly is the entire fix for leg 1.  (This is the
   same observation `PinFamily`'s §3 makes at `y₂`; here it is made ONCE, generically.)
2. **the grade page** — `center_error_grade`'s `E`-leg is shaped `D·k·loglog k/log k`,
   which is the pin's `log y = 4·loglog k` already substituted.  §2 below re-derives the
   page at a FREE `log y`, capped by the single generic gate

     `log (Y k) ≤ √(log k)`        (`hYlog`).

   The cap is the natural dual of the `S1′` floor `√(log k) ≤ Y k`: the window is
   `√L ≤ Y ≤ exp √L`.  Both corpus pins sit inside it — `(log k)^4` eventually, and
   `y₂ = exp(L^{2/5})` for EVERY `L ≥ 1` (since `2/5 < 1/2`).

Everything else in the chain is `y`-BLIND: the twist combine, the desmooth, the triangle,
`BallSup.ball_sup_of_center` (whose `S₀` was always a free real).

## THE CLONE BASE

`GradeWindowC.center_halasz_supply_B_uniform` (:838) — the `B`-abstract, centre-uniform
face — is the cheaper base: the grade factor is already opaque, so the twin below is
`B`-abstract AND centre-uniform for free.  `SupStation`'s §2 hoisting is inherited the same
way (the `∃ X₀` witness mentions neither `g`, `t₀`, `t₁` nor `Y`).

## The stones

* §2 `center_error_grade_Y` — the grade page at a free `log y` (private).
* §3 `center_halasz_supply_Y` — the `HCENTER` closure at a FREE `Y`, `B`-abstract,
  centre-uniform.
* §4 `ball_sup_supplied_Y` — the crown at a free `Y`, in `ball_sup_supplied`'s own shape.
* §5 `ball_sup_closed_star2` — **THE UNBLOCK**: §4 at `Y := ypin2 ∘ log` fed by
  `PinFamily2.hRHS_socket_star2`.  `FarStar.ball_sup_closed_star`'s assembly at the R2 pin.

The exponent stays the BALL arm's `c = 1/(2e)` throughout, and the absorption exponent
stays the pinned `ε = 1/1000`; `CenterSupply`'s LIVE GUARD (a §8.3 consumer citing this head
is a STOP) transfers verbatim.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the re-derived privates

`CenterSupply`'s three private helpers, re-derived byte-for-byte (the `_st`/`_B`/`_A`
clones in `SupStation`/`GradeWindowC`/`CofactorGrade` are the precedent). -/

/-- `L^{−1/2} = 1/√L` for `L > 0` (`CenterSupply.rpow_neg_half_eq`, re-derived). -/
private lemma rpow_neg_half_eq_Y {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (`CenterSupply.two_log_le_self`, re-derived). -/
private lemma two_log_le_self_Y {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
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
private lemma twentyfive_le_exp_eight_Y : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- `exp 2 < 10` — the numeral behind the `y`-page's `c₀ − 2η > 0` gate at a free `Y`. -/
private lemma exp_two_lt_ten_Y : Real.exp 2 < 10 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-! ## §2 — THE GRADE PAGE AT A FREE `log y` -/

/-- **THE `y`-GENERIC GRADE PAGE (`center_error_grade_Y`).**  `CenterSupply`'s
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
private lemma center_error_grade_Y {D W X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ))
    (hWcap : W ≤ Real.sqrt (Real.log (k : ℝ)))
    (hB : 2 * D * Real.log (Real.log X) * Real.log X ^ (-((1 : ℝ) / 2))
        ≤ Real.log X ^ (-((1 : ℝ) / 2) + 1 / 1000)) :
    D * ((k : ℝ) * (W / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  rw [show (-((1 : ℝ) / 2) : ℝ) = -(1 : ℝ) / 2 from by norm_num] at hB
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_Y hX8
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
      rw [rpow_neg_half_eq_Y hL0]
      field_simp
    linarith
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self_Y (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq_Y hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
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

/-! ## §3 — THE `HCENTER` CLOSURE AT A FREE `Y` -/

/-- **THE `y`-GENERIC CENTRE SUPPLY (`center_halasz_supply_Y`).**
`CenterSupply.center_halasz_supply` (:296) with the split point a FREE function
`Y : ℝ → ℝ`, the grade factor abstracted to an opaque nonneg `B`
(`GradeWindowC.center_halasz_supply_B_uniform`'s device) and the threshold quantified
BEFORE the centre `t₁` (`SupStation`'s hoisting):

  `hRHS : ∀ k ∈ [⌊X⌋₊, N], ‖prop21RHS (damped datum) (t₀+t₁) k h c₀ (Y k) (1/log (Y k))‖
            ≤ B·k`
  ⟹  `∀ k ∈ [⌊X⌋₊, N], ‖∑_{n≤k} f n·e^{−it₁ log n}‖ ≤ (B + 4·(log X)^{−1/2+1/1000})·k`,

at `h = k/√(log k)`, `c₀ = 1 + 1/log k` — the two slots the `S1′` page really does pin.

**THE `Y`-GATES, in-statement (law #253), all four on the row `[⌊X⌋₊, N]`:**

* `hY10  : 10 ≤ Y k`                   — `prop21_unconditional_uniform_absC`'s floor;
* `hYsq  : Y k ≤ √k`                   — its ceiling (the Λ-window must fit under `√k`);
* `hYlow : √(log k) ≤ Y k`             — its `hygate` (the window mass floor);
* `hYlog : log (Y k) ≤ √(log k)`       — §2's cap, the ONLY new gate versus the corpus.

The `η`-slot is not a gate but a DEFINITION: `η = 1/log (Y k)`, written into the binder.
The fifth `S1′` gate `0 < c₀ − 2η` is DISCHARGED here from `hY10` alone (`log 10 > 2`).

**Both corpus pins satisfy all four.**  At `y₂ = exp((log k)^{2/5})` the cap is
`(log k)^{2/5} ≤ (log k)^{1/2}`, true for every `log k ≥ 1`; the other three are
`PinFamily.pin2_basic`.  At the corpus pin `(log k)^4` the cap is `4·loglog k ≤ √(log k)`,
true eventually.

The named residual `hRHS` is carried, exactly as upstream — see `CenterSupply`'s module
docstring for why it is a binder and not a proof.  **LIVE GUARD**: `c = 1/(2e)` is the BALL
arm's halved constant; a §8.3 consumer citing this head is a STOP. -/
theorem center_halasz_supply_Y {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ)
    (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N : ℕ) (B : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ B →
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
  intro t₁ X N B hXlb hXN hN2 hB0 hY10 hYsq hYlow hYlog hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_Y hX8
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
      Real.log_le_log (Real.exp_pos 2) (le_trans exp_two_lt_ten_Y.le hY10k)
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
  have hgrade := center_error_grade_Y (D := 2 * C_E + C_R) (W := Real.log (Y (k : ℝ)))
    (X := X) (k := k) (by positivity) hX8 hk1 (hYlog k hkfl hkN) (hBabs X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-! ## §4 — THE CROWN AT A FREE `Y` -/

/-- **THE `y`-GENERIC CROWN (`ball_sup_supplied_Y`).**  `CenterSupply.ball_sup_supplied`
(:477) at a FREE split point `Y : ℝ → ℝ`: §3 fed into `BallSup.ball_sup_of_center`, giving
the pointwise weighted ball bound in exactly `SeamBallWeighted.ball_leg_of_sup_weighted`'s
`hSup′` binder shape,

  `∀ t ∈ Ann ∩ ball, ∀ m ≤ N, ‖spolyA a t m‖ ≤ ballSupS X S₀ · m/(1+|t−t₁|)`,
  `S₀ = C₁·exp(−(1/(2e))·𝔻²(f, p^{it₁}; X)) + 4·(log X)^{−1/2+1/1000}`.

Everything the corpus crown discharges is discharged here identically — the datum facts
`hf1`/`hfmul`/`hfle` (`seamCoeff_ellLin_one`, `seamCoeff_ellLin_mul_coprime`,
`norm_seamCoeff_le`) and `hMball` (through `pretDistSq_twist_slot` and
`SmallStones.hMball_of_A4_cap`) — because NONE of them ever sees the split point.  The
`hRHS` binder is the ONLY place `Y` appears, which is exactly the block this file removes:
the `y₂`-shaped socket now fits.

**The carried binders**: `hsupp`/`hDatum` (the dyadic bridge), the four `Y`-gates, `hRHS`
(the joint-head grade socket) and `hMcap` (the A-10 ball-centre dichotomy).  Nothing
else. -/
theorem ball_sup_supplied_Y {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ)
    (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (T C₁ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
            pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
              ≤ (1 / 16) * Real.log (Real.log X)) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply_Y hg t₀ Y
  refine ⟨max X₁ ballMertensThreshold, lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N T C₁ a hXlb hXN hN2 hC₁0 hsupp hDatum hY10 hYsq hYlow hYlog hRHS hMcap
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hXth : ballMertensThreshold ≤ X := le_trans (le_max_right _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hB0 : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
    mul_nonneg hC₁0 (Real.exp_nonneg _)
  have hS₀ : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h2 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogX0 _
    linarith
  -- the grade factor, in the supply's `B·k` shape
  have hRHS' : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
        ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X))
          * (k : ℝ) := by
    intro k h1 h2
    have h := hRHS k h1 h2
    have hring : (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) * (k : ℝ)
        = C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by ring
    rw [hring]
    exact h
  have hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
          (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
    refine hMball_of_A4_cap hXth ?_
    intro x h1 h2
    rw [← pretDistSq_twist_slot]
    exact hMcap x h1 h2
  exact ball_sup_of_center hX3 hXN hN2 (seamCoeff_ellLin_one g t₀)
    (seamCoeff_ellLin_mul_coprime g t₀)
    (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
    hS₀ hsupp hDatum
    (hsupply t₁ X N _ hX1 hXN hN2 hB0 hY10 hYsq hYlow hYlog hRHS') hMball

/-! ## §5 — THE UNBLOCK: the crown at `T*₂` and the R2 pin -/

/-- The four `Y`-gates at `Y := ypin2 ∘ log`, from the single family gate `exp 32768 ≤ k`.
Three are `PinFamily.pin2_basic` conjuncts verbatim; the fourth — §3's cap — is the
inequality `(log k)^{2/5} ≤ (log k)^{1/2}`, which is the whole reason `2/5` was pinned
below `1/2`. -/
private lemma ypin2_gates_Y {k : ℝ} (hk : pin2Gate ≤ k) :
    10 ≤ ypin2 (Real.log k) ∧ ypin2 (Real.log k) ≤ Real.sqrt k
      ∧ Real.sqrt (Real.log k) ≤ ypin2 (Real.log k)
      ∧ Real.log (ypin2 (Real.log k)) ≤ Real.sqrt (Real.log k) := by
  obtain ⟨-, hL32, -, hlogy, -, -, -, -, -, hy131072, hysq, hsqL, -⟩ := pin2_basic hk rfl
  refine ⟨by linarith, hysq, hsqL, ?_⟩
  rw [hlogy, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

-- Unlike `FarStar.ball_sup_closed_star`, this assembly needs NO heartbeat bump: the crown it
-- instantiates is `Y`-generic, so the binder block unifies against ONE opaque `Y` rather than
-- against five pin expressions per socket (measured: default budget, no `set_option`).
/-- **THE UNBLOCK — THE CROWN AT `T*₂` AND THE R2 PIN (`ball_sup_closed_star2`).**
`PinFamily2`'s RESIDUAL 1, closed.  `FarStar.ball_sup_closed_star`'s assembly at the second
wall: §4 instantiated at `Y := fun z => ypin2 (log z)` and fed by
`PinFamily2.hRHS_socket_star2`, with the `η`-slot identified through
`PinFamily.eta2_eq_inv_log` (`η₂ = 1/log y₂`, in closed form).

  `‖spolyA a t m‖ ≤ ballSupS X (C₁·e^{−(1/(2e))·𝔻²} + 4(log X)^{−1/2+1/1000})·m/(1+|t−t₁|)`,
  `C₁ = gradeAbsConst Cb + farCStar2` ABSOLUTE.

**The carried hypotheses, enumerated** (item for item `FarStar.ball_sup_closed_star`'s list,
with `T*₂`/`seamGateRstar2`/`pin2Gate` in place of `T*`/`seamGateRstar`/`e^{64}`):
(1) `hg`, the primes' norm bound;
(2) the scale frame `X₀ ≤ X`, `e ≤ X`, `X ≤ N ≤ 2X`;
(3) `0 ≤ Cb` and `ShortIntervalDatum Cb`;
(4) the coefficient equations for `a`;
(5) `hmin`, the COMPACT minimality at radius `seamGateRstar2 X T_ann`;
(6) `hMcap`, the crown's A-10 ball cap on `[X, 2X]`;
(7) `hkg`, the family gate `exp 32768 ≤ k` on the row's range;
(8) `hne`, the ball leg's domain nonempty;
(9) the `JointIntegrableAt` sockets, upstream's own, at the `y₂` pin.

**Nothing new is assumed versus the corpus crown**: the four `Y`-gates are DISCHARGED here
from (7) alone (`ypin2_gates_Y`), and the exit constant is `PinFamily2`'s
`gradeAbsConst Cb + farCStar2` — the width ruling's byte-identical `gradeAbsConst`. -/
theorem ball_sup_closed_star2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tb Cb Tann : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → Real.exp 1 ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ seamGateRstar2 X Tann →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → pin2Gate ≤ (k : ℝ)) →
        (seamAnn X Tann ∩ seamBall X t₁).Nonempty →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
            (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
            (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (ypin2 (Real.log (k : ℝ)))
            (eta2 (Real.log (k : ℝ))) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tb → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X ((gradeAbsConst Cb + farCStar2)
                  * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, H⟩ := ball_sup_supplied_Y hg t₀ t₁ (fun z => ypin2 (Real.log z))
  refine ⟨X₀, hX₀0, ?_⟩
  intro X N Tb Cb Tann a hXlb hXe hXN hN2 hCb0 hCbound hsupp hDatum hmin hMcapX hkg hne hInt
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  -- the four `Y`-gates, from the family gate alone
  have hY10 : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ ypin2 (Real.log (k : ℝ)) :=
    fun k h1 h2 => (ypin2_gates_Y (hkg k h1 h2)).1
  have hYsq : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ypin2 (Real.log (k : ℝ)) ≤ Real.sqrt (k : ℝ) :=
    fun k h1 h2 => (ypin2_gates_Y (hkg k h1 h2)).2.1
  have hYlow : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      Real.sqrt (Real.log (k : ℝ)) ≤ ypin2 (Real.log (k : ℝ)) :=
    fun k h1 h2 => (ypin2_gates_Y (hkg k h1 h2)).2.2.1
  have hYlog : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      Real.log (ypin2 (Real.log (k : ℝ))) ≤ Real.sqrt (Real.log (k : ℝ)) :=
    fun k h1 h2 => (ypin2_gates_Y (hkg k h1 h2)).2.2.2
  -- the `y₂` socket, with the `η`-slot identified
  have hsock := hRHS_socket_star2 hg hCb0 hCbound hXe hN2 hmin
    (hMcapX X le_rfl (by linarith)) hkg hne hInt
  have hRHS : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (ypin2 (Real.log (k : ℝ))) (1 / Real.log (ypin2 (Real.log (k : ℝ))))‖
        ≤ (gradeAbsConst Cb + farCStar2) * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
    intro k h1 h2
    have hkgate := hkg k h1 h2
    obtain ⟨-, -, -, -, hη, -, -, -, -, -, -, -, -⟩ :=
      pin2_basic hkgate (L := Real.log (k : ℝ)) rfl
    rw [← hη]
    exact hsock k h1 h2
  exact H X N Tb (gradeAbsConst Cb + farCStar2) a hXlb hXN hN2
    (by have := gradeAbsConst_nonneg hCb0; have := farCStar2_nonneg; linarith) hsupp hDatum
    hY10 hYsq hYlow hYlog hRHS hMcapX

end Salt.MR
