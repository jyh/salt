/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetPrice

/-!
# USetResiduals — ⟦V5f⟧'s three pricing residuals `R-1`/`R-2`/`R-3`

`USetPrice.hU_fully_priced` closes §8.3's `hU` at the pins, but leaves three families of
hypotheses riding in-statement (law #253).  This file prices them.

* **§1 (R-1) `Rbd_grade_priced`** — `R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` at `c = 1/e`, with `C_R`
  EXPLICIT (`gradeCR`).  The CASE-A arm is `caseAS_293` plus `CofactorSupply.descent_tail_le`
  (the descent factor `e^{(2/e)(S(X)−S(W))}` is at most the absolute `e^{13}` at the live
  descent gate); the far arm's MAIN term is `2√2/Rrad ≤ 3(log X)^{−ρ}` at `Rrad = seamRad X`
  (`1/16 > ρ₂₉₃`, the max's second branch as ⟦V5f⟧ describes it).

  **⚠ THE FAR ARM'S GS-7.1 ERROR DOES NOT DECAY — R-1 IS REFUTED AT THE LIVE `Tann`.**
  `cofactorRbd` is a `max`, so `R̄ ≥ 3·farErr kmin Ymax (Dmax+1)`, and
  `farErr = 4·ballSupC·(1 + log(3 + Rmax(1+log Y)))/√(log W)` carries `Rmax = Dmax + 1 ≥ Tann`.
  `USetPins.TannGate` FORCES `Tann ≥ exp(30(log X)^{1/2})`, i.e. `log Rmax ≥ 30(log X)^{1/2}`,
  so with `log kmin ≤ log X` the quotient is bounded BELOW by an absolute constant:

    `farErr kmin Ymax (Dmax+1) ≥ 120·ballSupC`   (`farErr_TannGate_floor`),

  hence `R̄ ≥ 360·ballSupC` (`Rbd_TannGate_floor`) and `R̄ ≤ C_R(log X)^{−ρ}` FAILS for every
  fixed `C_R` once `(log X)^{ρ₂₉₃} > C_R/(360·ballSupC)` (`Rbd_grade_refuted`).  At the live
  row height `Tann ≍ X/log X` the far error is `≍ 4·ballSupC·√(log X)`, i.e. it GROWS.
  §1 therefore states R-1 with the far-arm gate `hfar` visible, and §1b certifies that `hfar`
  is unsatisfiable under `TannGate` — the honest verdict is that ⟦V5f⟧'s "compare honestly,
  the caseAS branch dominates" reading holds only for the `2√2/R` half of `farSupS`, not for
  `farErr`.  `Rbd_and_Cq_gates_collide` records the joint collision with R-3(i): the two
  gates together force an explicit CEILING on `log X`.

* **§2 (R-2) `E_priced`** — the `E`-slot of `hU_fully_priced`, assembled from
  `RamareWindows.ramErr_moment_split` + `RamareErr.ramWindowErr_moment_grade` (MR's
  `720(T/X+1)/H` seam row) + `RamareWindows.ramP2corr_moment` (the `1/P` row) +
  `RamareErr.ramCopTail_moment_zero` (the §8.3 support pin kills the third row):
  `∫‖ramErr‖² ≤ 3(720(T/X+1)/H + EP2)` with `EP2` the `p²`-row's own value.
  `EP2_gate_of_row` then discharges `12·EP2 ≤ (log X)^{−θ₂₉₃}` from any `1/P`-shaped row
  bound, at `P ≥ P₈₃ = exp((log X)^{1−θ})`: `P83_ge_polylog` prices the super-polylog `P₈₃`
  against a polylog front constant, so the gate is free with ~2 powers of `log X` to spare.

  **Zeno residual (stated, not proved here)** — and it is SHARPER than "find a `1/P` bound":
  the corpus ALREADY has a `p²`-row mass page, `SmallStones.ramP2mass_le`
  (`Σ_{n≤N} ‖ramP2coeffMR n‖²/n² ≤ 64/P²`, which is MR's `1/P` row and better), and it is
  **too lossy for §8.3**.  §8.3 multiplies the mass by `(2T + 20N) ≍ X`, so that route gives
  `EP2 ≍ X/P²`, while EVERY admissible `P` obeys the §8.3 pin `P ≤ Q ≤ Q₈₃ X`, whence
  `P² ≤ √X` and the row DIVERGES (`P2_route_64_over_Psq_insufficient`, kernel-checked).
  What is needed is the `ℓ²`-PRESERVING mass `Σ ‖ramP2coeff n‖²/n² ≲ K·(1+log N)/(X·P)`;
  `SmallStones` loses exactly that factor at its `∑ a² ≤ (∑ a)²` step (`SmallStones`:241),
  which discards the `ℓ²` gain over the `≍ X/P` non-zero frequencies.  Its page needs
  (i) the support step (`hwin` + `hsupp` ⟹ every non-zero frequency has `n ≥ X`, so
  `1/n² ≤ 1/(X·n)`), (ii) a fibre-card bound (`#{p ≥ P prime : p² ∣ n} ≤ 2 log n`), (iii) the
  fibrewise regroup onto `ramP2dom`, and (iv) the `(p,m) ↦ (p, m/p)` reindex with the harmonic
  `m`-sum and the `Σ_{p≥P} 1/p² ≤ 1/(P−1)` telescope.

* **§3 (R-3) `numeral_gates_discharged`** — ⟦V5f⟧'s three numeral gates at explicit `X`
  thresholds: `gate_Cq_CR` (∃-shaped in `C_q`, `C_R` — a numeral against a growing power),
  `gate_KS_live_delta` (the `δ'`-level gate at the live pin `δ' = (log X)^{−100}`, free with
  197 powers of `log X` to spare), and `gate_absorb_8640` (`8640 ≤ (log X)^{1/1000}` at
  `X ≥ exp(8640^1000)`).

Source pins (D5): MR arXiv v4 (`1501.04585v4`) pp. 19–20, 27–29 (§8.3);
`docs/exploration/hsup-design.md` ⟦V5e⟧/⟦V5f⟧/⟦V6⟧ (W-2).
-/

namespace Salt.MR

open scoped BigOperators
open Finset

/-! ## §0 — the two `rpow` gate pages (law #253's arithmetic) -/

/-- **A numeral against a growing power.**  `A ≤ (log X)^a` holds as soon as
`log X ≥ A^{1/a}` — the explicit `X`-threshold behind every ⟦V5f⟧ gate of the form
"numeral ≤ power of `log X`". -/
theorem rpow_gate_of_threshold {A a X : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hX : A ^ (1 / a) ≤ Real.log X) : A ≤ (Real.log X) ^ a := by
  have h1 : (A ^ (1 / a)) ^ a ≤ (Real.log X) ^ a :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA _) hX ha.le
  rwa [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ (ne_of_gt ha), Real.rpow_one] at h1

/-- **The exponential beats its fourth power**: `(y/4)^4 ≤ exp y` for `y ≥ 0`
(`exp y = (exp (y/4))^4 ≥ (1 + y/4)^4`).  This is what makes `P₈₃ = exp((log X)^{1−θ})`
super-polylog at an explicit threshold. -/
theorem exp_ge_quartic {y : ℝ} (hy : 0 ≤ y) : (y / 4) ^ 4 ≤ Real.exp y := by
  have h1 : y / 4 ≤ Real.exp (y / 4) := by
    have := Real.add_one_le_exp (y / 4); linarith
  have h2 : (y / 4) ^ 4 ≤ (Real.exp (y / 4)) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
  have h3 : (Real.exp (y / 4)) ^ 4 = Real.exp y := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith [h3 ▸ h2]

/-! ## §1 — R-1: the co-factor grade `R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` -/

/-- `ρ₂₉₃ ≤ 1/(32e)` — the CASE-A leading exponent is below the far-star exponent. -/
theorem rho293_le_far : rho293 ≤ 1 / (32 * Real.exp 1) := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  rw [rho293, theta293,
    show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1))) = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `ρ₂₉₃ ≤ 499/1000` — the CASE-A leading exponent is below the desmooth exponent. -/
theorem rho293_le_desmooth : rho293 ≤ 499 / 1000 := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  rw [rho293, theta293,
    show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1))) = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `ρ₂₉₃ ≤ 1/16` — the CASE-A leading exponent is below the seam-radius exponent, so the
`2√2/R` half of `farSupS` is `(log X)^{−1/16}`-graded, better than the exit. -/
theorem rho293_le_seam : rho293 ≤ 1 / 16 := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  rw [rho293, theta293,
    show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1))) = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **THE SHIFTED-SCALE TRANSFER.**  Under the live descent gate the window bottom obeys
`log W ≥ (1/2)log X`, so a negative power of `log W` costs at most the factor `2` when read
at the GLOBAL scale, and any exponent at or beyond `ρ₂₉₃` is majorised by the exit grade. -/
theorem logW_rpow_le {X W a : ℝ} (hL1 : 1 ≤ Real.log X)
    (hhalf : 1 / 2 * Real.log X ≤ Real.log W) (hρa : rho293 ≤ a) (ha1 : a ≤ 1) :
    (Real.log W) ^ (-a) ≤ 2 * (Real.log X) ^ (-rho293) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hhalf0 : (0 : ℝ) < 1 / 2 * Real.log X := by linarith
  have ha0 : (0 : ℝ) ≤ a := le_trans rho293_pos.le hρa
  have h1 : (Real.log W) ^ (-a) ≤ (1 / 2 * Real.log X) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hhalf0 hhalf (by linarith)
  have h2 : (1 / 2 * Real.log X) ^ (-a) = ((1 : ℝ) / 2) ^ (-a) * (Real.log X) ^ (-a) :=
    Real.mul_rpow (by norm_num) hL0.le
  have h3 : ((1 : ℝ) / 2) ^ (-a) = (2 : ℝ) ^ a := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  have h4 : (2 : ℝ) ^ a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
    rwa [Real.rpow_one] at this
  have h5 : (Real.log X) ^ (-a) ≤ (Real.log X) ^ (-rho293) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h60 : (0 : ℝ) ≤ (Real.log X) ^ (-a) := Real.rpow_nonneg hL0.le _
  calc (Real.log W) ^ (-a) ≤ ((1 : ℝ) / 2) ^ (-a) * (Real.log X) ^ (-a) := by
        rw [← h2]; exact h1
    _ = (2 : ℝ) ^ a * (Real.log X) ^ (-a) := by rw [h3]
    _ ≤ 2 * (Real.log X) ^ (-rho293) := by
        have := mul_le_mul h4 h5 h60 (by norm_num : (0 : ℝ) ≤ 2)
        linarith

/-- **THE DESCENT FACTOR IS ABSOLUTE.**  At the live-regime descent gate,
`CofactorSupply.descent_tail_le` puts the only trace of the scale descent,
`e^{(2/e)(S(X)−S(W))}`, under the absolute constant `e^{13}` — the `1 + o(1)` of ⟦V5d⟧, made
a numeral (law #253: nothing is `O(1)`-absorbed). -/
theorem descent_factor_le {X W : ℝ} (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log W) :
    Real.exp ((2 / Real.exp 1) * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
      ≤ Real.exp 13 := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hW0 : (0 : ℝ) < Real.log W := Real.log_pos (by linarith)
  have hhalf : 1 / 2 * Real.log X ≤ Real.log W := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  have hdesc := descent_tail_le hW2 hWX hlX hgate
  have h1 : (4 : ℝ) / Real.log (Real.log X) ≤ 2 := by
    rw [div_le_iff₀ hLL0]; linarith
  have h2 : (24 : ℝ) / Real.log W ≤ 16 := by
    rw [div_le_iff₀ hW0]; linarith
  have h3 : (24 : ℝ) / Real.log X ≤ 8 := by
    rw [div_le_iff₀ hL0]; linarith
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hinv : (2 : ℝ) / Real.exp 1 ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hdiv0 : (0 : ℝ) < 2 / Real.exp 1 := by positivity
  have hkey : (2 / Real.exp 1) * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W) ≤ 13 := by
    rcases le_or_gt 0 (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W) with hpos | hneg
    · have hm := mul_le_mul_of_nonneg_right hinv hpos
      rw [one_mul] at hm
      linarith
    · have hm := mul_neg_of_pos_of_neg hdiv0 hneg
      linarith
  exact Real.exp_le_exp.mpr hkey

/-- **THE EXPLICIT `C_R`** (⟦V5f⟧'s silent-vacuity catch: the constant is CARRIED).
`C_R(Cb) = 6·(C₁(1/e,Cb)·e^{13} + 2·C_far* + 8) + 12`, where `C₁ = gradeAbsConstC` is U-7's
own absolute front constant, `e^{13}` caps the descent factor (`descent_factor_le`),
`2·C_far*` and `8` are the two additive CASE-A terms after the shifted-scale transfer, and the
outer shape is `3·max(2·caseAS, farSupS)` with the far arm at `4`. -/
noncomputable def gradeCR (Cb : ℝ) : ℝ :=
  6 * (gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 8) + 12

/-- `C_R > 1` — the constant is not a silent `1` (⟦V5f⟧'s non-vacuity catch). -/
theorem one_lt_gradeCR {Cb : ℝ} (hCb0 : 0 ≤ Cb) : 1 < gradeCR Cb := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have h2 : (0 : ℝ) ≤ farCStar := farCStar_nonneg
  have h3 : (0 : ℝ) < Real.exp 13 := Real.exp_pos _
  have h4 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 := mul_nonneg h1 h3.le
  unfold gradeCR
  linarith

/-- **R-1 (the CASE-A arm), PRICED.**  At the pin `c = 1/e` the CASE-A exit constant reads at
the GLOBAL scale:

  `caseAS (1/e) Cb (cofactorMfl X θ₂₉₃ W) W ≤ (C₁(1/e,Cb)·e^{13} + 2·C_far* + 8)·(log X)^{−ρ₂₉₃}`.

Three pages: `caseAS_293` (the identity), `descent_factor_le` (the Mertens `S(X)−S(W)` page,
`CofactorSupply.descent_tail_le` evaluated), and `logW_rpow_le` twice (the shifted-scale
transfer at `1/(32e) > ρ₂₉₃` and at `499/1000 > ρ₂₉₃`). -/
theorem caseAS_arm_priced {X W Cb : ℝ} (hCb0 : 0 ≤ Cb) (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log W) :
    caseAS (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W
      ≤ (gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 8)
        * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) (le_trans hW2 hWX)
  have hXe : Real.exp 1 ≤ X := by
    calc Real.exp 1 ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hL1
      _ = X := Real.exp_log hX0
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hhalf : 1 / 2 * Real.log X ≤ Real.log W := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hC1nn : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg hL0.le _
  rw [caseAS_293 (X := X) (W := W) (Cb := Cb) hXe]
  have hd := descent_factor_le hW2 hWX hlX hgate
  have hterm1 : gradeAbsConstC (1 / Real.exp 1) Cb
        * (Real.exp ((2 / Real.exp 1)
            * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
          * Real.log X ^ (-rho293))
      ≤ gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 * (Real.log X) ^ (-rho293) := by
    have h1 : Real.exp ((2 / Real.exp 1)
          * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
        * Real.log X ^ (-rho293)
        ≤ Real.exp 13 * (Real.log X) ^ (-rho293) :=
      mul_le_mul_of_nonneg_right hd hpow0
    calc gradeAbsConstC (1 / Real.exp 1) Cb
          * (Real.exp ((2 / Real.exp 1)
              * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial W))
            * Real.log X ^ (-rho293))
        ≤ gradeAbsConstC (1 / Real.exp 1) Cb * (Real.exp 13 * (Real.log X) ^ (-rho293)) :=
          mul_le_mul_of_nonneg_left h1 hC1nn
      _ = gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 * (Real.log X) ^ (-rho293) := by ring
  have hfar1 : (1 : ℝ) / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hterm2 : farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))
      ≤ farCStar * (2 * (Real.log X) ^ (-rho293)) :=
    mul_le_mul_of_nonneg_left (logW_rpow_le hL1 hhalf rho293_le_far hfar1) farCStar_nonneg
  have hexp3 : (-(1 : ℝ) / 2 + 1 / 1000) = -(499 / 1000) := by norm_num
  have hterm3 : 4 * Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ 4 * (2 * (Real.log X) ^ (-rho293)) := by
    rw [hexp3]
    exact mul_le_mul_of_nonneg_left
      (logW_rpow_le hL1 hhalf rho293_le_desmooth (by norm_num)) (by norm_num)
  nlinarith [hterm1, hterm2, hterm3]

/-- **R-1 (the far arm's MAIN term), PRICED.**  At the intended radius pin `Rrad = seamRad X`
the trivial-centre transfer is `2√2·(log X)^{−1/16} ≤ 3·(log X)^{−ρ₂₉₃}` — ⟦V5f⟧'s
"`ρ₂₉₃ ≈ 0.0102 < 1/16`" comparison, in the kernel.  (The gate is a LOWER bound on `Rrad`:
`hU_fully_priced` carries only `Rrad ≤ seamRad X`, which alone leaves `2√2/Rrad` unbounded.) -/
theorem farMain_priced {X Rrad : ℝ} (hL1 : 1 ≤ Real.log X) (hRlow : seamRad X ≤ Rrad) :
    2 * Real.sqrt 2 / Rrad ≤ 3 * (Real.log X) ^ (-rho293) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hseam : seamRad X = (Real.log X) ^ ((1 : ℝ) / 16) := rfl
  have hs0 : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hL0 _
  have hRlow' : (Real.log X) ^ ((1 : ℝ) / 16) ≤ Rrad := by rw [← hseam]; exact hRlow
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : 2 * Real.sqrt 2 / Rrad ≤ 2 * Real.sqrt 2 / (Real.log X) ^ ((1 : ℝ) / 16) := by
    have h2sqrt : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
    exact div_le_div_of_nonneg_left h2sqrt hs0 hRlow'
  have h2 : (Real.log X) ^ (-((1 : ℝ) / 16)) ≤ (Real.log X) ^ (-rho293) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [rho293_le_seam])
  have h3 : 2 * Real.sqrt 2 / (Real.log X) ^ ((1 : ℝ) / 16)
      = 2 * Real.sqrt 2 * (Real.log X) ^ (-((1 : ℝ) / 16)) := by
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have h4 : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
  have h5 : 2 * Real.sqrt 2 * (Real.log X) ^ (-((1 : ℝ) / 16))
      ≤ 3 * (Real.log X) ^ (-rho293) := by
    have hp1 : (0 : ℝ) ≤ (Real.log X) ^ (-((1 : ℝ) / 16)) := Real.rpow_nonneg hL0.le _
    have hp2 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg hL0.le _
    nlinarith
  linarith [h3 ▸ h1]

/-- **R-1 — `R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` at the pin `c = 1/e`**, with `C_R = gradeCR Cb`
EXPLICIT.

  `R̄ = cofactorRbd (1/e) Cb X θ₂₉₃ kmin Ymax (Dmax+1) Rrad = 3·max(2·caseAS …, farSupS …)`.

The CASE-A branch is `caseAS_arm_priced`; the far branch is `farMain_priced` (`2√2/Rrad`) plus
the GS-7.1 error, which enters through the STATED gate `hfar`.

**⚠ `hfar` IS NOT SATISFIABLE AT THE LIVE `Tann`** — see §1b (`farErr_TannGate_floor`): under
`TannGate X Tann` and `Tann ≤ Dmax` the left side of `hfar` is bounded BELOW by `120·ballSupC`,
an absolute positive constant, while the right side tends to `0`.  The gate is kept
in-statement (law #253) precisely so that the obstruction is visible rather than absorbed. -/
theorem Rbd_grade_priced {X Cb kmin Ymax Dmax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hfar : farErr kmin Ymax (Dmax + 1) ≤ (Real.log X) ^ (-rho293)) :
    cofactorRbd (1 / Real.exp 1) Cb X theta293 kmin Ymax (Dmax + 1) Rrad
      ≤ gradeCR Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg hL0.le _
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  set CA := gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 8 with hCA
  have hCA0 : (0 : ℝ) ≤ CA := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h2 : (0 : ℝ) ≤ farCStar := farCStar_nonneg
    have h3 : (0 : ℝ) < Real.exp 13 := Real.exp_pos _
    rw [hCA]; nlinarith
  have hA := caseAS_arm_priced (X := X) (W := kmin) (Cb := Cb) hCb0 hk2 hkX hlX hgate
  have hB : farSupS kmin Ymax (Dmax + 1) Rrad ≤ 4 * (Real.log X) ^ (-rho293) := by
    have hm := farMain_priced (X := X) (Rrad := Rrad) hL1 hRlow
    unfold farSupS
    linarith
  have hmax : max (2 * caseAS (1 / Real.exp 1) Cb (cofactorMfl X theta293 kmin) kmin)
      (farSupS kmin Ymax (Dmax + 1) Rrad) ≤ (2 * CA + 4) * (Real.log X) ^ (-rho293) := by
    refine max_le ?_ ?_
    · nlinarith [hA]
    · nlinarith [hB]
  have hCRval : gradeCR Cb = 3 * (2 * CA + 4) := by rw [gradeCR, hCA]; ring
  unfold cofactorRbd
  rw [hCRval]
  nlinarith [hmax]

/-! ### §1b — THE FAR-ARM OBSTRUCTION (the honest verdict on R-1)

`TannGate X Tann` (`USetPins`:320) is the row's own gate: `Tann ≥ exp(30(log X)^{1/2})`, and
`USetPins.TannGate_fails_polylog_deg` proves it fails at every polylog height, so it cannot be
weakened.  But the far arm's GS-7.1 error reads `log Rmax` in its NUMERATOR against `√(log W)`
in its denominator, and `Rmax = Dmax + 1 ≥ Tann`.  The two requirements collide. -/

/-- **THE FAR ERROR HAS AN ABSOLUTE FLOOR under `TannGate`.**
`farErr kmin Ymax (Dmax+1) ≥ 120·ballSupC` whenever `Tann ≤ Dmax`, `1 ≤ Ymax`, `1 < kmin ≤ X`
and `TannGate X Tann` — the numerator carries `log Tann ≥ 30(log X)^{1/2}` and the denominator
only `√(log kmin) ≤ √(log X)`.  (At the LIVE row height `Tann ≍ X/log X` the same page gives
`farErr ≳ 4·ballSupC·(log X)^{1/2}`: the far arm GROWS.) -/
theorem farErr_TannGate_floor {X Tann kmin Ymax Dmax : ℝ}
    (hTgate : TannGate X Tann) (hDmax : Tann ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hk1 : 1 < kmin) (hkX : kmin ≤ X) :
    120 * ballSupC ≤ farErr kmin Ymax (Dmax + 1) := by
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  have hk0 : (0 : ℝ) < Real.log kmin := Real.log_pos hk1
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hk1 hkX
  have hLX0 : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hlogle : Real.log kmin ≤ Real.log X := Real.log_le_log (by linarith) hkX
  have hsq0 : (0 : ℝ) < Real.sqrt (Real.log kmin) := Real.sqrt_pos.mpr hk0
  have hsqle : Real.sqrt (Real.log kmin) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlogle
  have hTpos : (0 : ℝ) < Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_pos _
  have hTann0 : (0 : ℝ) < Tann := lt_of_lt_of_le hTpos hTgate
  have hlogT : 30 * (Real.log X) ^ ((1 : ℝ) / 2) ≤ Real.log Tann := by
    have h := Real.log_le_log hTpos hTgate
    rwa [Real.log_exp] at h
  have hY0 : (0 : ℝ) ≤ Real.log Ymax := Real.log_nonneg hY1
  have harg : Tann ≤ 3 + (Dmax + 1) * (1 + Real.log Ymax) := by nlinarith
  have hlogarg : Real.log Tann ≤ Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)) :=
    Real.log_le_log hTann0 harg
  have hroot : (Real.log X) ^ ((1 : ℝ) / 2) = Real.sqrt (Real.log X) := rpow_half_eq_sqrt _
  rw [farErr, le_div_iff₀ hsq0]
  have hstep1 : 120 * ballSupC * Real.sqrt (Real.log kmin)
      ≤ 120 * ballSupC * Real.sqrt (Real.log X) :=
    mul_le_mul_of_nonneg_left hsqle (by positivity)
  have hstep2 : 30 * Real.sqrt (Real.log X)
      ≤ Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)) := by
    rw [← hroot]; linarith
  nlinarith [hstep1, hstep2]

/-- **THE `R̄` FLOOR.**  `cofactorRbd` is `3·max(…, farSupS …)` and `farSupS ≥ farErr`, so the
far error's floor is `R̄`'s floor: `R̄ ≥ 360·ballSupC` at ANY `c`, `Cb`, `Rrad > 0`. -/
theorem Rbd_TannGate_floor {X Tann cg Cb kmin Ymax Dmax Rrad : ℝ}
    (hTgate : TannGate X Tann) (hDmax : Tann ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hk1 : 1 < kmin) (hkX : kmin ≤ X) (hR0 : 0 < Rrad) :
    360 * ballSupC ≤ cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad := by
  have hfl := farErr_TannGate_floor hTgate hDmax hY1 hk1 hkX
  have hmain : (0 : ℝ) ≤ 2 * Real.sqrt 2 / Rrad := by positivity
  have h2 : farErr kmin Ymax (Dmax + 1) ≤ farSupS kmin Ymax (Dmax + 1) Rrad := by
    unfold farSupS; linarith
  have h3 : farSupS kmin Ymax (Dmax + 1) Rrad
      ≤ max (2 * caseAS cg Cb (cofactorMfl X theta293 kmin) kmin)
          (farSupS kmin Ymax (Dmax + 1) Rrad) := le_max_right _ _
  unfold cofactorRbd
  linarith

/-- **R-1 IS REFUTED AT THE LIVE `Tann`.**  For every fixed `C_R`, the ⟦V5f⟧ residual
`R̄ ≤ C_R·(log X)^{−ρ₂₉₃}` FAILS once `(log X)^{ρ₂₉₃} > C_R/(360·ballSupC)` — an explicit
`X`-threshold, stated (law #253).  The obstruction is structural, not a lossy page: it is the
`max` in `cofactorRbd` meeting `TannGate`'s lower bound on the ambient radius. -/
theorem Rbd_grade_refuted {X Tann cg Cb kmin Ymax Dmax Rrad CR : ℝ}
    (hTgate : TannGate X Tann) (hDmax : Tann ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hk1 : 1 < kmin) (hkX : kmin ≤ X) (hR0 : 0 < Rrad)
    (hXgate : CR < 360 * ballSupC * (Real.log X) ^ rho293) :
    ¬ (cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad
        ≤ CR * (Real.log X) ^ (-rho293)) := by
  intro hle
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hk1 hkX
  have hL0 : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hp0 : (0 : ℝ) < (Real.log X) ^ (-rho293) := Real.rpow_pos_of_pos hL0 _
  have hid : (Real.log X) ^ rho293 * (Real.log X) ^ (-rho293) = 1 := by
    rw [← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero]
  have h1 : CR * (Real.log X) ^ (-rho293) < 360 * ballSupC := by
    have h := mul_lt_mul_of_pos_right hXgate hp0
    calc CR * (Real.log X) ^ (-rho293)
        < 360 * ballSupC * (Real.log X) ^ rho293 * (Real.log X) ^ (-rho293) := h
      _ = 360 * ballSupC * ((Real.log X) ^ rho293 * (Real.log X) ^ (-rho293)) := by ring
      _ = 360 * ballSupC := by rw [hid, mul_one]
  have h2 := Rbd_TannGate_floor (cg := cg) (Cb := Cb) hTgate hDmax hY1 hk1 hkX hR0
  linarith

/-- **R-1 AND R-3(i) COLLIDE.**  If BOTH ⟦V5f⟧ gates hold — the co-factor grade
`R̄ ≤ C_R(log X)^{−ρ₂₉₃}` and the block gate `1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}` — then, under
`TannGate`, `log X` is BOUNDED: `1728·C_q·(360·ballSupC)²·(log X)^{4θ₂₉₃} ≤ 1`.  Since
`θ₂₉₃ > 0`, the left side is unbounded in `X`, so the two gates cannot hold together beyond an
explicit ceiling.  (`ρ₂₉₃ = 3θ₂₉₃` is what makes the collision quantitative: the floor costs
`(log X)^{6θ}` in `C_R²` against the gate's `(log X)^{2θ}`.) -/
theorem Rbd_and_Cq_gates_collide {X Tann cg Cb kmin Ymax Dmax Rrad CR Cq : ℝ}
    (hTgate : TannGate X Tann) (hDmax : Tann ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hk1 : 1 < kmin) (hkX : kmin ≤ X) (hR0 : 0 < Rrad) (hCq0 : 0 ≤ Cq)
    (hR1 : cofactorRbd cg Cb X theta293 kmin Ymax (Dmax + 1) Rrad
      ≤ CR * (Real.log X) ^ (-rho293))
    (hR3 : 1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293)) :
    1728 * Cq * (360 * ballSupC) ^ 2 * (Real.log X) ^ (4 * theta293) ≤ 1 := by
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hk1 hkX
  have hL0 : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hfloor := Rbd_TannGate_floor (cg := cg) (Cb := Cb) hTgate hDmax hY1 hk1 hkX hR0
  have hp0 : (0 : ℝ) < (Real.log X) ^ rho293 := Real.rpow_pos_of_pos hL0 _
  have hn0 : (0 : ℝ) < (Real.log X) ^ (-rho293) := Real.rpow_pos_of_pos hL0 _
  have hid : (Real.log X) ^ (-rho293) * (Real.log X) ^ rho293 = 1 := by
    rw [← Real.rpow_add hL0, neg_add_cancel, Real.rpow_zero]
  -- `C_R ≥ 360·ballSupC·(log X)^ρ`
  have hCRlow : 360 * ballSupC * (Real.log X) ^ rho293 ≤ CR := by
    have h1 : 360 * ballSupC ≤ CR * (Real.log X) ^ (-rho293) := le_trans hfloor hR1
    have h2 := mul_le_mul_of_nonneg_right h1 hp0.le
    calc 360 * ballSupC * (Real.log X) ^ rho293
        ≤ CR * (Real.log X) ^ (-rho293) * (Real.log X) ^ rho293 := h2
      _ = CR * ((Real.log X) ^ (-rho293) * (Real.log X) ^ rho293) := by ring
      _ = CR := by rw [hid, mul_one]
  -- squaring, at `ρ = 3θ`
  have hsq : (360 * ballSupC) ^ 2 * (Real.log X) ^ (6 * theta293) ≤ CR ^ 2 := by
    have hlow0 : (0 : ℝ) ≤ 360 * ballSupC * (Real.log X) ^ rho293 := by positivity
    have h1 : (360 * ballSupC * (Real.log X) ^ rho293) ^ 2 ≤ CR ^ 2 :=
      pow_le_pow_left₀ hlow0 hCRlow 2
    have h2 : (360 * ballSupC * (Real.log X) ^ rho293) ^ 2
        = (360 * ballSupC) ^ 2 * ((Real.log X) ^ rho293 * (Real.log X) ^ rho293) := by ring
    have h3 : (Real.log X) ^ rho293 * (Real.log X) ^ rho293
        = (Real.log X) ^ (6 * theta293) := by
      rw [← Real.rpow_add hL0, rho293]; ring_nf
    rw [h2, h3] at h1
    exact h1
  -- and the block gate
  have h4 : 1728 * Cq * ((360 * ballSupC) ^ 2 * (Real.log X) ^ (6 * theta293))
      ≤ (Real.log X) ^ (2 * theta293) := by
    have h5 : 1728 * Cq * ((360 * ballSupC) ^ 2 * (Real.log X) ^ (6 * theta293))
        ≤ 1728 * Cq * CR ^ 2 := by
      refine mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  -- divide by `(log X)^{2θ}`
  have hd0 : (0 : ℝ) < (Real.log X) ^ (-(2 * theta293)) := Real.rpow_pos_of_pos hL0 _
  have hid2 : (Real.log X) ^ (2 * theta293) * (Real.log X) ^ (-(2 * theta293)) = 1 := by
    rw [← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero]
  have hid3 : (Real.log X) ^ (6 * theta293) * (Real.log X) ^ (-(2 * theta293))
      = (Real.log X) ^ (4 * theta293) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have h6 := mul_le_mul_of_nonneg_right h4 hd0.le
  calc 1728 * Cq * (360 * ballSupC) ^ 2 * (Real.log X) ^ (4 * theta293)
      = 1728 * Cq * ((360 * ballSupC) ^ 2 * (Real.log X) ^ (6 * theta293))
          * (Real.log X) ^ (-(2 * theta293)) := by rw [← hid3]; ring
    _ ≤ (Real.log X) ^ (2 * theta293) * (Real.log X) ^ (-(2 * theta293)) := h6
    _ = 1 := hid2

/-- **THE REPAIR TARGET (the positive direction).**  The far arm's GS-7.1 error DOES meet the
exit grade whenever the AMBIENT radius is quasi-polylog:

  `8·ballSupC·(1 + log(3 + Rmax(1+log Y))) ≤ (log X)^{1/2 − ρ₂₉₃}  ⟹  farErr ≤ (log X)^{−ρ₂₉₃}`,

using only `log kmin ≥ (1/2)log X` (the descent gate's own consequence).  This is the exact
inequality a repaired §8.3 would have to supply — it is a gate on `log Rmax ≈ log Tann`, i.e.
on the ROW HEIGHT, not on any co-factor datum. -/
theorem farErr_le_of_ambient_gate {X kmin Ymax Dmax : ℝ}
    (hL1 : 1 ≤ Real.log X) (hk1 : 1 < kmin) (hD0 : 0 ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hhalf : 1 / 2 * Real.log X ≤ Real.log kmin)
    (hamb : 8 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
      ≤ (Real.log X) ^ ((1 : ℝ) / 2 - rho293)) :
    farErr kmin Ymax (Dmax + 1) ≤ (Real.log X) ^ (-rho293) := by
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hk0 : (0 : ℝ) < Real.log kmin := Real.log_pos hk1
  have hroot : (Real.log X) ^ ((1 : ℝ) / 2) = Real.sqrt (Real.log X) := rpow_half_eq_sqrt _
  have hs0 : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL0 _
  have hhalf0 : (0 : ℝ) < 1 / 2 * (Real.log X) ^ ((1 : ℝ) / 2) := by linarith
  -- `√(log kmin) ≥ (1/2)(log X)^{1/2}`
  have hquarter : Real.sqrt (1 / 4 * Real.log X) = 1 / 2 * Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) / 4 * Real.log X = ((1 : ℝ) / 2) ^ 2 * Real.log X by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hden : 1 / 2 * (Real.log X) ^ ((1 : ℝ) / 2) ≤ Real.sqrt (Real.log kmin) := by
    rw [hroot, ← hquarter]
    exact Real.sqrt_le_sqrt (by linarith)
  -- the numerator's non-negativity (the window top and the ambient radius are live data)
  have hY0 : (0 : ℝ) ≤ Real.log Ymax := Real.log_nonneg hY1
  have hargpos : (1 : ℝ) ≤ 3 + (Dmax + 1) * (1 + Real.log Ymax) := by nlinarith
  have hlognn : (0 : ℝ) ≤ Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)) :=
    Real.log_nonneg hargpos
  have hnum0 : (0 : ℝ) ≤ 4 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))) := by
    positivity
  -- the descent to the majorised denominator
  have hstep : farErr kmin Ymax (Dmax + 1)
      ≤ 4 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
        / (1 / 2 * (Real.log X) ^ ((1 : ℝ) / 2)) := by
    rw [farErr]
    exact div_le_div_of_nonneg_left hnum0 hhalf0 hden
  have hform : 4 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
        / (1 / 2 * (Real.log X) ^ ((1 : ℝ) / 2))
      = (8 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))))
        * ((Real.log X) ^ ((1 : ℝ) / 2))⁻¹ := by
    field_simp
    ring
  have hinv0 : (0 : ℝ) ≤ ((Real.log X) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
  have hlast : (Real.log X) ^ ((1 : ℝ) / 2 - rho293) * ((Real.log X) ^ ((1 : ℝ) / 2))⁻¹
      = (Real.log X) ^ (-rho293) := by
    rw [← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    congr 1
    ring
  calc farErr kmin Ymax (Dmax + 1)
      ≤ (8 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax))))
        * ((Real.log X) ^ ((1 : ℝ) / 2))⁻¹ := by rw [← hform]; exact hstep
    _ ≤ (Real.log X) ^ ((1 : ℝ) / 2 - rho293) * ((Real.log X) ^ ((1 : ℝ) / 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hamb hinv0
    _ = (Real.log X) ^ (-rho293) := hlast

/-- **R-1, END-TO-END, IN A QUASI-POLYLOG-AMBIENT REGIME.**  `Rbd_grade_priced` with its far
gate discharged from the ambient gate: this is the form R-1 would take if §8.3's row height
were capped instead of floored.  It is stated so that a repaired route can consume R-1 without
re-deriving anything — only `hamb` would change. -/
theorem Rbd_grade_priced_of_ambient {X Cb kmin Ymax Dmax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X) (hD0 : 0 ≤ Dmax) (hY1 : 1 ≤ Ymax)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hamb : 8 * ballSupC * (1 + Real.log (3 + (Dmax + 1) * (1 + Real.log Ymax)))
      ≤ (Real.log X) ^ ((1 : ℝ) / 2 - rho293)) :
    cofactorRbd (1 / Real.exp 1) Cb X theta293 kmin Ymax (Dmax + 1) Rrad
      ≤ gradeCR Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hhalf : 1 / 2 * Real.log X ≤ Real.log kmin := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  exact Rbd_grade_priced hCb0 hk2 hkX hlX hgate hRlow
    (farErr_le_of_ambient_gate hL1 (by linarith) hD0 hY1 hhalf hamb)

/-- **THE REPAIR WINDOW IS EMPTY.**  The ambient gate caps the row height at
`exp((log X)^{1/2−ρ₂₉₃}/(8·ballSupC))`; `TannGate` floors it at `exp(30(log X)^{1/2})`.  The cap
sits strictly BELOW the floor for every `X` with `(log X)^{−ρ₂₉₃} < 240·ballSupC` — which, since
`(log X)^{−ρ₂₉₃} ≤ 1` at `log X ≥ 1` and `ballSupC = renormaliseConst·e^{M/2+6}` with
`renormaliseConst = 28(1+2(log 4+36))e^8`, is EVERY `X` in the live range.  So no `Tann`
satisfies both: this is the collision, in one line. -/
theorem ambient_cap_below_TannGate_floor {X : ℝ} (hL1 : 1 ≤ Real.log X)
    (hXgate : (Real.log X) ^ (-rho293) < 240 * ballSupC) :
    (Real.log X) ^ ((1 : ℝ) / 2 - rho293) / (8 * ballSupC)
      < 30 * (Real.log X) ^ ((1 : ℝ) / 2) := by
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hs0 : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL0 _
  have hsplit : (Real.log X) ^ ((1 : ℝ) / 2 - rho293)
      = (Real.log X) ^ ((1 : ℝ) / 2) * (Real.log X) ^ (-rho293) := by
    rw [← Real.rpow_add hL0, sub_eq_add_neg]
  rw [hsplit, div_lt_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left hXgate hs0]

/-! ## §2 — R-2: the `E`-slot and the `1/P` row's gate -/

/-- **R-2 (the assembly) — `E_priced`.**  `hU_fully_priced`'s two `E` binders, discharged:

  `∫_{−T}^{T} ‖ramErr‖² ≤ 3·(720(T/X + 1)/H + EP2)`,  `EP2 = (2T+20N)·Σ_{n≤N} ‖ramP2coeff‖²/n²`.

Lemma 12's three rows through `RamareWindows.ramErr_moment_split`: the seam row at MR's own
grade (`RamareErr.ramWindowErr_moment_grade`), the `p²`-correction row (`ramP2corr_moment` —
this is the `EP2` slot), and the coprime tail, which is identically ZERO under the §8.3 support
pin `hsupp` (`RamareErr.ramCopTail_moment_zero`).  Nothing here is estimated: `EP2` is the row's
own value, and §2's `EP2_gate_of_row` is what converts a `1/P`-shaped bound on it into
`hU_fully_priced`'s `12·EP2 ≤ (log X)^{−θ₂₉₃}`. -/
theorem E_priced (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 3 * (720 * (T / (Xd : ℝ) + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) := by
  refine (ramErr_moment_split H (by linarith) N Xd P Q hP a b c hcoef T hT).trans ?_
  have h1 := ramWindowErr_moment_grade H hH N Xd P Q hX hN hN2 hHX hP b c hb hc hwin T hT
  have h2 := ramP2corr_moment N P Q a b c T
  have h3 := ramCopTail_moment_zero N P Q a hsupp T
  rw [h3]
  linarith

/-- **R-2 (the plug) — `E_priced` AT THE ROW SCALE.**  `hU_fully_priced`'s `hErow` binder reads
`720·(Tann/X + 1)/H` at the row's REAL scale `X`, while Lemma 12's row is at the DYADIC scale
`Xd` (`ramErr H N Xd P Q`).  The two meet under `X ≤ Xd`, and only then; stated separately so
that the scale mismatch is visible rather than silent (⟦V4⟧'s law). -/
theorem E_priced_row_scale (H : ℝ) (hH : 2 ≤ H) (N Xd P Q : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N)
    (hN2 : (N : ℝ) ≤ 2 * (Xd : ℝ)) (hHX : H ≤ (Xd : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T X : ℝ) (hT : 0 ≤ T) (hX0 : 0 < X) (hXd : X ≤ (Xd : ℝ)) :
    (∫ t in (-T)..T, ‖ramErr H N Xd P Q a b c t‖ ^ 2)
      ≤ 3 * (720 * (T / X + 1) / H
          + (2 * T + 20 * (N : ℝ))
              * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hscale : T / (Xd : ℝ) ≤ T / X := div_le_div_of_nonneg_left hT hX0 hXd
  have hrow : 720 * (T / (Xd : ℝ) + 1) / H ≤ 720 * (T / X + 1) / H := by
    have h1 : 720 * (T / (Xd : ℝ) + 1) ≤ 720 * (T / X + 1) := by linarith
    rw [div_le_div_iff_of_pos_right hH0]
    exact h1
  exact le_trans (E_priced H hH N Xd P Q hX hN hN2 hHX hP a b c hcoef hb hc hwin hsupp T hT)
    (by linarith)

/-- **`P₈₃` IS SUPER-POLYLOG.**  `(log X)^{4−4θ₂₉₃}/256 ≤ P₈₃ X θ₂₉₃ = exp((log X)^{1−θ₂₉₃})`
— `exp_ge_quartic` at `y = (log X)^{1−θ}`.  Four powers of `log X` are enough for every gate
this file needs; the true growth is of course faster than any power. -/
theorem P83_ge_polylog {X : ℝ} (hL0 : 0 < Real.log X) :
    (Real.log X) ^ (4 - 4 * theta293) / 256 ≤ P83 X theta293 := by
  have hy0 : (0 : ℝ) ≤ (Real.log X) ^ (1 - theta293) := Real.rpow_nonneg hL0.le _
  have h := exp_ge_quartic hy0
  have heq : ((Real.log X) ^ (1 - theta293) / 4) ^ 4
      = (Real.log X) ^ (4 - 4 * theta293) / 256 := by
    have h1 : ((Real.log X) ^ (1 - theta293)) ^ (4 : ℕ)
        = (Real.log X) ^ (4 - 4 * theta293) := by
      rw [← Real.rpow_natCast ((Real.log X) ^ (1 - theta293)) 4, ← Real.rpow_mul hL0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, h1]
    norm_num
  rw [P83, ← heq]
  exact h

/-- **R-2 (the gate) — `12·EP2 ≤ (log X)^{−θ₂₉₃}` IS FREE AT `P₈₃`.**  From any `1/P`-shaped
row bound `EP2 ≤ Kmass/P` with a polylog front constant (`12·Kmass ≤ (log X)²` — the honest
size of `(2T+20N)·K/(X(P−1))`'s numerator at `T ≤ X ≤ N/2` and `K ≍ log N`), the ⟦V5f⟧ gate
holds at the explicit threshold `log X ≥ 256`: `P₈₃`'s four polylog powers
(`P83_ge_polylog`) beat the two spent, with `(log X)^{2−5θ₂₉₃}` to spare. -/
theorem EP2_gate_of_row {X Kmass EP2 P : ℝ}
    (hL : 256 ≤ Real.log X) (hP83 : P83 X theta293 ≤ P)
    (hEP2 : EP2 ≤ Kmass / P) (hKfit : 12 * Kmass ≤ (Real.log X) ^ (2 : ℝ)) :
    12 * EP2 ≤ (Real.log X) ^ (-theta293) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hP830 : (0 : ℝ) < P83 X theta293 := Real.exp_pos _
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le hP830 hP83
  have hbase0 : (0 : ℝ) < (Real.log X) ^ (4 - 4 * theta293) / 256 := by positivity
  have hlow : (Real.log X) ^ (4 - 4 * theta293) / 256 ≤ P := le_trans (P83_ge_polylog hL0) hP83
  -- `12·EP2 ≤ (log X)²/P`
  have hstep1 : 12 * EP2 ≤ (Real.log X) ^ (2 : ℝ) / P := by
    have h1 : 12 * EP2 ≤ 12 * (Kmass / P) := by linarith
    have h2 : 12 * (Kmass / P) = (12 * Kmass) / P := by ring
    have h3 : (12 * Kmass) / P ≤ (Real.log X) ^ (2 : ℝ) / P := by
      rw [div_le_div_iff_of_pos_right hP0]
      exact hKfit
    linarith [h2 ▸ h1]
  -- `(log X)²/P ≤ 256·(log X)^{4θ−2}`
  have hstep2 : (Real.log X) ^ (2 : ℝ) / P ≤ 256 * (Real.log X) ^ (4 * theta293 - 2) := by
    have h1 : (Real.log X) ^ (2 : ℝ) / P
        ≤ (Real.log X) ^ (2 : ℝ) / ((Real.log X) ^ (4 - 4 * theta293) / 256) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _) hbase0 hlow
    have h2 : (Real.log X) ^ (2 : ℝ) / ((Real.log X) ^ (4 - 4 * theta293) / 256)
        = 256 * (Real.log X) ^ (4 * theta293 - 2) := by
      rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, ← Real.rpow_sub hL0]
      congr 2
      ring
    linarith [h2 ▸ h1]
  -- and `256·(log X)^{4θ−2} ≤ (log X)^{−θ}`
  have hbig : (256 : ℝ) ≤ (Real.log X) ^ (2 - 5 * theta293) := by
    have h1 : (Real.log X) ^ (1 : ℝ) ≤ (Real.log X) ^ (2 - 5 * theta293) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [theta293_lt_one_div_32])
    rw [Real.rpow_one] at h1
    linarith
  have hid : (Real.log X) ^ (2 - 5 * theta293) * (Real.log X) ^ (4 * theta293 - 2)
      = (Real.log X) ^ (-theta293) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (4 * theta293 - 2) := Real.rpow_nonneg hL0.le _
  have hstep3 : 256 * (Real.log X) ^ (4 * theta293 - 2) ≤ (Real.log X) ^ (-theta293) := by
    calc 256 * (Real.log X) ^ (4 * theta293 - 2)
        ≤ (Real.log X) ^ (2 - 5 * theta293) * (Real.log X) ^ (4 * theta293 - 2) :=
          mul_le_mul_of_nonneg_right hbig hpow0
      _ = (Real.log X) ^ (-theta293) := hid
  linarith

/-- **THE EXISTING `p²`-ROW PAGE IS TOO LOSSY FOR §8.3'S PINS.**  `SmallStones.ramP2mass_le`
already prices the `p²` row's mass at `64/P²` (for the MR-range coefficient `ramP2coeffMR`),
and that is MR's own `1/P` row and more.  It does NOT discharge ⟦V5f⟧'s gate, because §8.3
multiplies the mass by `(2T + 20N) ≍ X`: the resulting `EP2` is `≍ X/P²`, and EVERY admissible
`P` is capped by the §8.3 pin `P ≤ Q ≤ Q₈₃ X = exp(log X/loglog X)`, so `P² ≤ √X` and the row
is `≳ √X` — DIVERGENT, not `≤ (log X)^{−θ₂₉₃}`.

Hence the residual named in this file's header is not "prove some `1/P` bound" but
specifically: prove the `ℓ²`-preserving mass `Σ ‖ramP2coeff n‖²/n² ≲ K/(X·P)`.  The corpus
page loses exactly that factor by passing through `∑ a² ≤ (∑ a)²` (`SmallStones`:241), which
discards the `ℓ²` gain over the `≍ X/P` non-zero frequencies.

The statement below is the certificate: at `log X ≥ e⁴` (i.e. `X ≥ exp(e⁴)`, live) the
`64/P²` route's own bound EXCEEDS the target for every `P ≤ Q₈₃ X`. -/
theorem P2_route_64_over_Psq_insufficient {X T : ℝ} {N P : ℕ}
    (hX0 : 0 < X) (hL : Real.exp 4 ≤ Real.log X) (hT0 : 0 ≤ T) (hXN : X ≤ (N : ℝ))
    (hP1 : 1 ≤ (P : ℝ)) (hPQ : (P : ℝ) ≤ Q83 X) :
    (Real.log X) ^ (-theta293) < 12 * (2 * T + 20 * (N : ℝ)) * (64 / (P : ℝ) ^ 2) := by
  have he4 : (54 : ℝ) ≤ Real.exp 4 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7182818283 : ℝ) ^ (4 : ℕ) ≤ (Real.exp 1) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1.le 4
    rw [h2]
    calc (54 : ℝ) ≤ (2.7182818283 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (4 : ℕ) := h3
  have hL54 : (54 : ℝ) ≤ Real.log X := le_trans he4 hL
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL : (4 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 4) hL
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hX1 : (1 : ℝ) < X := by
    have h1 : Real.log X + 1 ≤ Real.exp (Real.log X) := Real.add_one_le_exp _
    rw [Real.exp_log hX0] at h1
    linarith
  -- `P² ≤ √X`, for EVERY admissible `P` (the §8.3 upper pin `P ≤ Q ≤ Q₈₃`)
  have hQ83 : Q83 X = Real.exp (Real.log X / Real.log (Real.log X)) := rfl
  have hroot0 : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
  have hPsq : ((P : ℝ)) ^ 2 ≤ X ^ ((1 : ℝ) / 2) := by
    have hQ0 : (0 : ℝ) < Q83 X := by rw [hQ83]; exact Real.exp_pos _
    have hsq : ((P : ℝ)) ^ 2 ≤ (Q83 X) ^ 2 := by nlinarith
    have hQsq : (Q83 X) ^ 2 = Real.exp (2 * (Real.log X / Real.log (Real.log X))) := by
      rw [hQ83, pow_two, ← Real.exp_add]
      congr 1
      ring
    have hexp : 2 * (Real.log X / Real.log (Real.log X)) ≤ 1 / 2 * Real.log X := by
      have h1 : Real.log X / Real.log (Real.log X) ≤ Real.log X / 4 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hLL
      linarith
    have hXhalf : X ^ ((1 : ℝ) / 2) = Real.exp (1 / 2 * Real.log X) := by
      rw [Real.rpow_def_of_pos hX0]
      congr 1
      ring
    rw [hXhalf]
    calc ((P : ℝ)) ^ 2 ≤ (Q83 X) ^ 2 := hsq
      _ = Real.exp (2 * (Real.log X / Real.log (Real.log X))) := hQsq
      _ ≤ Real.exp (1 / 2 * Real.log X) := Real.exp_le_exp.mpr hexp
  -- the route's own bound is at least `15360·√X`
  have hroot1 : (1 : ℝ) ≤ X ^ ((1 : ℝ) / 2) := Real.one_le_rpow hX1.le (by norm_num)
  have hPsq0 : (0 : ℝ) < ((P : ℝ)) ^ 2 := by nlinarith
  have hinv : 64 / X ^ ((1 : ℝ) / 2) ≤ 64 / ((P : ℝ)) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) hPsq0 hPsq
  have hne : X ^ ((1 : ℝ) / 2) ≠ 0 := ne_of_gt hroot0
  have hXsq : X ^ ((1 : ℝ) / 2) * X ^ ((1 : ℝ) / 2) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have hXdiv : X / X ^ ((1 : ℝ) / 2) = X ^ ((1 : ℝ) / 2) := by
    rw [div_eq_iff hne, hXsq]
  have h1 : 12 * (20 * X) * (64 / X ^ ((1 : ℝ) / 2)) = 15360 * (X / X ^ ((1 : ℝ) / 2)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [hXdiv] at h1
  have hpre : 12 * (20 * X) ≤ 12 * (2 * T + 20 * (N : ℝ)) := by linarith
  have hbig : 15360 * X ^ ((1 : ℝ) / 2)
      ≤ 12 * (2 * T + 20 * (N : ℝ)) * (64 / ((P : ℝ)) ^ 2) := by
    calc 15360 * X ^ ((1 : ℝ) / 2) = 12 * (20 * X) * (64 / X ^ ((1 : ℝ) / 2)) := h1.symm
      _ ≤ 12 * (2 * T + 20 * (N : ℝ)) * (64 / X ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hpre (by positivity)
      _ ≤ 12 * (2 * T + 20 * (N : ℝ)) * (64 / ((P : ℝ)) ^ 2) := by
          have hfac : (0 : ℝ) ≤ 12 * (2 * T + 20 * (N : ℝ)) := by nlinarith
          exact mul_le_mul_of_nonneg_left hinv hfac
  have hsmall : (Real.log X) ^ (-theta293) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [theta293_pos])
  nlinarith

/-! ## §3 — R-3: ⟦V5f⟧'s three numeral gates at explicit `X`-thresholds -/

/-- **R-3 (i) — the `C_q`/`C_R` gate.**  `1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}`: a numeral against
a GROWING power, so it is `∃X₀ ∀X ≥ X₀`-shaped, with `X₀ = exp((1728·C_q·C_R²)^{1/(2θ₂₉₃)})`
EXPLICIT.  `C_q` is `USetBalance.tL_supply_discharged`'s existential constant, so the gate is
honestly stated with `C_q` universally quantified and `X₀` depending on it. -/
theorem gate_Cq_CR (Cq CR : ℝ) (hCq0 : 0 ≤ Cq) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) := by
  refine ⟨Real.exp ((1728 * Cq * CR ^ 2) ^ (1 / (2 * theta293))), Real.exp_pos _, ?_⟩
  intro X hX
  refine rpow_gate_of_threshold (by positivity) (by linarith [theta293_pos]) ?_
  have h0 : (0 : ℝ) < Real.exp ((1728 * Cq * CR ^ 2) ^ (1 / (2 * theta293))) := Real.exp_pos _
  have h := Real.log_le_log h0 hX
  rwa [Real.log_exp] at h

/-- **R-3 (ii) — the `KS` gate at the LIVE level `δ' = (log X)^{−100}`.**

  `32·(log X)^{2+2θ}·(20512·δ'²·(1 + log 2Tann)) ≤ (log X)^{−θ}`.

⟦V5f⟧ calls this "a gate on the level `δ'`"; at the banked live pin `δ' = (log X)^{−100}` the
`δ'²` contributes `(log X)^{−200}` and the gate is free with ~197 powers of `log X` to spare —
it holds already at `log X ≥ 4` (the `1 + log 2Tann ≤ 3 log X` step uses only `Tann ≤ X`). -/
theorem gate_KS_live_delta {X Tann δ' : ℝ} (hL4 : 4 ≤ Real.log X) (hT1 : 1 < Tann)
    (hTX : Tann ≤ X) (hδ : δ' = (Real.log X) ^ (-(100 : ℝ))) :
    32 * (Real.log X) ^ (2 + 2 * theta293) * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
      ≤ (Real.log X) ^ (-theta293) := by
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  -- `δ'² = (log X)^{−200}`
  have hδsq : δ' ^ 2 = (Real.log X) ^ (-(200 : ℝ)) := by
    rw [hδ, ← Real.rpow_natCast ((Real.log X) ^ (-(100 : ℝ))) 2, ← Real.rpow_mul hL0.le]
    norm_num
  -- `1 + log 2Tann ≤ 3 log X`
  have hlogT : 1 + Real.log (2 * Tann) ≤ 3 * Real.log X := by
    have h1 : Real.log (2 * Tann) = Real.log 2 + Real.log Tann :=
      Real.log_mul (by norm_num) (by linarith)
    have h2 : Real.log Tann ≤ Real.log X := Real.log_le_log (by linarith) hTX
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hlogT0 : (0 : ℝ) ≤ 1 + Real.log (2 * Tann) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Tann by linarith)
    linarith
  have hp0 : (0 : ℝ) < (Real.log X) ^ (-(200 : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hp1 : (0 : ℝ) < (Real.log X) ^ (2 + 2 * theta293) := Real.rpow_pos_of_pos hL0 _
  -- collapse the two powers
  have hcollapse : (Real.log X) ^ (2 + 2 * theta293) * (Real.log X) ^ (-(200 : ℝ))
        * Real.log X
      = (Real.log X) ^ (2 * theta293 - 197) := by
    calc (Real.log X) ^ (2 + 2 * theta293) * (Real.log X) ^ (-(200 : ℝ)) * Real.log X
        = (Real.log X) ^ (2 + 2 * theta293 + -(200 : ℝ)) * (Real.log X) ^ (1 : ℝ) := by
          rw [Real.rpow_one, ← Real.rpow_add hL0]
      _ = (Real.log X) ^ (2 * theta293 - 197) := by
          rw [← Real.rpow_add hL0]; congr 1; ring
  have hstep : 32 * (Real.log X) ^ (2 + 2 * theta293) * (20512 * δ' ^ 2
        * (1 + Real.log (2 * Tann)))
      ≤ 1969152 * (Real.log X) ^ (2 * theta293 - 197) := by
    rw [hδsq]
    have h1 : 20512 * (Real.log X) ^ (-(200 : ℝ)) * (1 + Real.log (2 * Tann))
        ≤ 20512 * (Real.log X) ^ (-(200 : ℝ)) * (3 * Real.log X) := by
      have h2 : (0 : ℝ) ≤ 20512 * (Real.log X) ^ (-(200 : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_left hlogT h2
    have h3 : 32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * (Real.log X) ^ (-(200 : ℝ)) * (3 * Real.log X))
        = 1969152 * ((Real.log X) ^ (2 + 2 * theta293) * (Real.log X) ^ (-(200 : ℝ))
            * Real.log X) := by ring
    have h4 : (0 : ℝ) ≤ 32 * (Real.log X) ^ (2 + 2 * theta293) := by positivity
    have h5 := mul_le_mul_of_nonneg_left h1 h4
    rw [h3, hcollapse] at h5
    exact h5
  -- the numeral gate: `1969152 ≤ (log X)^{197−3θ}`
  have hbig : (1969152 : ℝ) ≤ (Real.log X) ^ (197 - 3 * theta293) := by
    have h1 : (4 : ℝ) ^ (21 : ℝ) ≤ (Real.log X) ^ (21 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL4 (by norm_num)
    have h2 : (Real.log X) ^ (21 : ℝ) ≤ (Real.log X) ^ (197 - 3 * theta293) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [theta293_lt_one_div_32])
    have h3 : (4 : ℝ) ^ (21 : ℝ) = 4398046511104 := by
      rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h3] at h1
    linarith
  have hid : (Real.log X) ^ (197 - 3 * theta293) * (Real.log X) ^ (2 * theta293 - 197)
      = (Real.log X) ^ (-theta293) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (2 * theta293 - 197) := Real.rpow_nonneg hL0.le _
  calc 32 * (Real.log X) ^ (2 + 2 * theta293) * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
      ≤ 1969152 * (Real.log X) ^ (2 * theta293 - 197) := hstep
    _ ≤ (Real.log X) ^ (197 - 3 * theta293) * (Real.log X) ^ (2 * theta293 - 197) :=
        mul_le_mul_of_nonneg_right hbig hpow0
    _ = (Real.log X) ^ (-theta293) := hid

/-- **R-3 (iii) — the `o(1)` absorption of Lemma 12's absolute constants.**
`8640 ≤ (log X)^{1/1000}` at the EXPLICIT threshold `X ≥ exp(8640^1000)` (in-statement, never
"`X` large enough"): `ε = 1/1000` is the value ⟦V5f⟧'s `priced_exit_beats_door` runs at. -/
theorem gate_absorb_8640 {X : ℝ} (hX : Real.exp ((8640 : ℝ) ^ (1000 : ℕ)) ≤ X) :
    (8640 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 1000) := by
  refine rpow_gate_of_threshold (by norm_num) (by norm_num) ?_
  have h0 : (0 : ℝ) < Real.exp ((8640 : ℝ) ^ (1000 : ℕ)) := Real.exp_pos _
  have h := Real.log_le_log h0 hX
  rw [Real.log_exp] at h
  rwa [one_div_one_div, show ((1000 : ℝ)) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **R-3 — THE THREE NUMERAL GATES, DISCHARGED TOGETHER** at ONE explicit threshold
`X₀ = max (exp((1728C_qC_R²)^{1/2θ})) (exp(8640^1000))`.  All three are ⟦V5f⟧'s verbatim
residual gates; each is a numeral (or a polylog-level pin) against a growing power of `log X`,
and none of them is an "`X` large enough" (law #253). -/
theorem numeral_gates_discharged (Cq CR : ℝ) (hCq0 : 0 ≤ Cq) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X Tann δ' : ℝ, X₀ ≤ X → 1 < Tann → Tann ≤ X →
      δ' = (Real.log X) ^ (-(100 : ℝ)) →
      1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293)
      ∧ 32 * (Real.log X) ^ (2 + 2 * theta293)
          * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293)
      ∧ (8640 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 1000) := by
  obtain ⟨X₁, hX₁0, hX₁⟩ := gate_Cq_CR Cq CR hCq0
  refine ⟨max X₁ (Real.exp ((8640 : ℝ) ^ (1000 : ℕ))), lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X Tann δ' hX hT1 hTX hδ
  have hX1' : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX2' : Real.exp ((8640 : ℝ) ^ (1000 : ℕ)) ≤ X := le_trans (le_max_right _ _) hX
  have h8640 := gate_absorb_8640 hX2'
  -- the absorption threshold already forces `log X ≥ 4`
  have hL4 : (4 : ℝ) ≤ Real.log X := by
    have h0 : (0 : ℝ) < Real.exp ((8640 : ℝ) ^ (1000 : ℕ)) := Real.exp_pos _
    have h := Real.log_le_log h0 hX2'
    rw [Real.log_exp] at h
    have h1 : (4 : ℝ) ≤ (8640 : ℝ) ^ (1000 : ℕ) := by
      calc (4 : ℝ) ≤ 8640 := by norm_num
        _ = (8640 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ (8640 : ℝ) ^ (1000 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact le_trans h1 h
  exact ⟨hX₁ X hX1', gate_KS_live_delta hL4 hT1 hTX hδ, h8640⟩

end Salt.MR
