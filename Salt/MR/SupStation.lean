/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarStar
import Salt.MR.JointPlumb
import Salt.MR.SeamBallWeighted

/-!
# THE hSUP STATION — the seam row's ball leg, composed (`SupStation`)

The final assembly of the ball arm: every landed piece composed into
`SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup` binder, with **no analytic hypothesis
left** — only the row's own frame (`g` 1-bounded at the primes, the seam datum's support
equations, the dyadic scale frame `X₀ ≤ X ≤ N ≤ 2X`, the annulus height `0 ≤ T_ann`) and the
A-10 ball cap, which is the seam's own case split and is carried as the antecedent of the
exit at the centre this file PRODUCES.

## The quantifier page (⟦V3e⟧ → the assembly)

`FarStar.ball_sup_closed_star` is stated as `∀ g t₀ t₁, ∃ X₀, ∀ X ≥ X₀, …` — the centre `t₁`
is fixed BEFORE the scale.  The station cannot consume it in that order: its centre is
`FarStar.exists_min_gate_star`'s minimizer at radius `seamGateRstar X T_ann`, which depends
on `X` through BOTH the radius and the objective `𝔻²(·; X)`.  Consuming the crown at a
per-`X` centre needs `X₀(t₁) ≤ X` for a centre chosen after `X` — a circularity at the
statement level.

**It is not a circularity in the mathematics.**  The threshold's witness is `t₁`-free:
`CenterSupply.center_halasz_supply` produces `max (max (XA+1) XB) (e⁸)` where `XA` comes from
`LambdaMass.prop21_uniform_at_scale_absC` (the datum-hoisted A-7b form, whose constants
precede `g`, `t₀`, `t₁`) and `XB` from `BridgeAdapt.loglog_absorb_pow_pin` (a function of
`C_E`, `C_R` alone); `ball_sup_supplied` adds `SmallStones.ballMertensThreshold`; the crown
adds nothing.  Neither `g`, `t₀` nor `t₁` occurs in any of them.  §2 below therefore re-runs
the SAME composition with the `∃ X₀` hoisted over `t₁` — statements only, proofs verbatim
(`center_error_grade` and its three arithmetic helpers are `private` in `CenterSupply`, so
they are restated here as `_st` clones).  Nothing upstream is changed (iron rule 1); the
ideal repair is the hoisting done in `CenterSupply` itself, which is a Fable-tier edit of a
landed statement.

## What is here

* §1 — **`JointIntegrableAt` is `M`-free** (`jointIntegrableAt_of_zero`): the distance
  parameter enters only through the constant factor `e^{−M/(2e)}` of `rhsFbound`, so the four
  integrability sockets at any `M` follow from the same sockets at `M = 0`.  With
  `JointPlumb.jointIntegrableAt_pin` at `M := 0` (whose floor is `pretDistSq_nonneg`), the
  `hInt` bundle is discharged with NO minimality hypothesis at all
  (`jointIntegrableAt_pin_free`).  This closes the last carried socket of ⟦V3b⟧ without
  touching the on-ℝ (vacuous) minimality.
* §2 — the uniform-`X₀` re-derivation (`center_halasz_supply_uniform`,
  `ball_sup_supplied_uniform`, `ball_sup_closed_star_uniform`).
* §3 — **AS-1 `seam_ball_leg_station`**: the composed exit.  The centre is produced per-`X`;
  `hmin`, `hgate`, `hne`, `hInt`, `hk64` and the Chebyshev datum `Cb` are all discharged
  internally; the empty and nonempty arms deliver the SAME binder at the SAME `S`
  (`SeamGate.seam_sup_binder_of_inter_empty` on one side, the crown on the other).
* §4 — **AS-2 `seam_ball_leg_station_M`**: the ⟦TWO-M⟧ option-(A) corollary.  Under the MVT
  guard `T_ann ≤ X/2` the enlarged radius satisfies `seamGateRstar X T_ann ≤ X`
  (`seamGateRstar_le_self`), so the produced centre lies in MRT's own window `|t| ≤ X` and
  the exit may be stated at ANY lower bound `M₀` for `𝔻²(·; X)` on that window — in
  particular at `M(f;X) = inf_{|t|≤X} 𝔻²`.
* §5 — **AS-3 `prop_A3_T1_row_station`**: AS-1 in `prop_A3_T1_row_split_weighted`'s ball slot.

**LIVE GUARD** (inherited from the ball chain): `c = 1/(2e)` is the BALL arm's halved
constant; a §8.3 consumer citing this exit is a STOP.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set

/-! ## §1 — the integrability sockets, discharged without minimality

`RHSGrade.JointIntegrableAt d t₀' M k L c₀ y η h` mentions `M` in exactly two of its four
components, and there only through `rhsFbound M L (β + 1/L)`.  Since

  `rhsFbound M L σ = e^{−M/(2e)} · rhsFbound 0 L σ`

(the `M`-slot is a σ-free factor of the exponential), each of those components is a CONSTANT
multiple of its `M = 0` counterpart. -/

/-- The `M`-slot of `rhsFbound` is a constant factor. -/
lemma rhsFbound_eq_exp_mul (M L σ : ℝ) :
    rhsFbound M L σ = Real.exp (-(1 / (2 * Real.exp 1)) * M) * rhsFbound 0 L σ := by
  unfold rhsFbound
  rw [show -(1 / (2 * Real.exp 1)) * (M - 2 * Real.log (σ * L) - 48)
        = -(1 / (2 * Real.exp 1)) * M
          + -(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48) from by ring,
    Real.exp_add]
  ring

/-- **`JointIntegrableAt` is `M`-free.**  The four sockets at any distance `M` follow from the
same four at `M = 0`: components 2 and 4 do not mention `M`, and components 1 and 3 are the
`M = 0` integrands scaled by the constant `e^{−M/(2e)}`. -/
theorem jointIntegrableAt_of_zero {d : ℕ → ℂ} {t₀' k L c₀ y η h : ℝ} (M : ℝ)
    (h0 : JointIntegrableAt d t₀' 0 k L c₀ y η h) :
    JointIntegrableAt d t₀' M k L c₀ y η h := by
  obtain ⟨h1, h2, h3, h4⟩ := h0
  refine ⟨fun α hα => ?_, h2, ?_, h4⟩
  · have hfun : (fun β => rhsFbound M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β)
        = fun β => Real.exp (-(1 / (2 * Real.exp 1)) * M)
            * (rhsFbound 0 L (β + 1 / L) * crossKer d k h y c₀ t₀' α β) := by
      funext β
      rw [rhsFbound_eq_exp_mul M L (β + 1 / L)]
      ring
    rw [hfun]
    exact (h1 α hα).const_mul _
  · have hfun : (fun α => ∫ β in (0 : ℝ)..η,
          rhsFbound M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β)
        = fun α => Real.exp (-(1 / (2 * Real.exp 1)) * M)
            * ∫ β in (0 : ℝ)..η, rhsFbound 0 L (β + 1 / L) * crossKer d k h y c₀ t₀' α β := by
      funext α
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun β _ => ?_)
      rw [rhsFbound_eq_exp_mul M L (β + 1 / L)]
      ring
    rw [hfun]
    exact h3.const_mul _

/-- **The `hInt` bundle, hypothesis-free (`jointIntegrableAt_pin_free`).**
`JointPlumb.jointIntegrableAt_pin` at `M := 0` — where the floor `hMt` is just
`pretDistSq_nonneg` — transported to an arbitrary `M` by `jointIntegrableAt_of_zero`.

The four `JointIntegrableAt` sockets that every consumer of the ball chain carries
(⟦V3b⟧'s residual (2)) therefore cost exactly the scale gate `e^{64} ≤ k`. -/
theorem jointIntegrableAt_pin_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀' M : ℝ)
    {k : ℕ} (hk64 : Real.exp 64 ≤ (k : ℝ)) :
    JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' M (k : ℝ)
      (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
      (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  refine jointIntegrableAt_of_zero M (jointIntegrableAt_pin hg hk64 (fun t => ?_))
  exact pretDistSq_nonneg _ _ _ (fun n => ellLin_norm_le_one _ hgtw n)
    (fun n => le_of_eq (costwist_norm _ n))
/-! ## §2 — the uniform-`X₀` re-derivation

Statements only are new: each proof below is `CenterSupply`'s / `FarStar`'s own, replayed
with the `∃ X₀` hoisted over the centre `t₁`.  The four arithmetic helpers of
`CenterSupply`'s §2 are `private` there, so they are restated (`_st` clones, same proofs).
-/

/-- `L^{−1/2} = 1/√L`. -/
private lemma rpow_neg_half_eq_st {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (the `√X`-route: `log X = 2 log √X ≤ 2(√X−1)`, then
`4√X − 4 ≤ X` is `(√X−2)² ≥ 0`). -/
private lemma two_log_le_self_st {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
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
private lemma twentyfive_le_exp_eight_st : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- **THE GRADE PAGE (`center_error_grade_st`).**  The two error legs of the centre
composition — the desmooth cost `h+1 = k/√(log k) + 1` and the S1′ `E`-error, already
reduced to `D·k·loglog k/log k` — are converted into the SINGLE `X`-scale term
`4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions, each elementary: `log k ∈ [L/2, 2L]` (the window, `L := log X`);
`loglog k / log k ≤ 4·loglog X / log X`, absorbed by `hB` (A-6 at the pinned `ε = 1/1000`);
`1/√(log k) ≤ 2/√L` and `1 ≤ k/√L` (the latter from `2·log X ≤ X`, `two_log_le_self_st`). -/
private lemma center_error_grade_st {D X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * X)
    (hB : 4 * D * Real.log (Real.log X) * Real.log X ^ (-(1 : ℝ))
        ≤ Real.log X ^ (-(1 : ℝ) + 1 / 1000)) :
    D * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_st hX8
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
      rw [rpow_neg_half_eq_st hL0]
      field_simp
    linarith
  -- STEP F — `1 ≤ k·L^{−1/2}`
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self_st (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq_st hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
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

/-- **The `HCENTER` closure, UNIFORM in the centre (`center_halasz_supply_uniform`).**
`CenterSupply.center_halasz_supply` with the threshold quantified BEFORE `t₁`.  The proof is
that theorem's own: its witness `max (max (XA+1) XB) (e⁸)` mentions neither `g`, `t₀` nor
`t₁`, so hoisting the `refine` past the centre is the whole edit. -/
theorem center_halasz_supply_uniform {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N : ℕ) (C₁ : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_uniform_at_scale_absC
  obtain ⟨XB, _hXB0, hB⟩ :=
    loglog_absorb_pow_pin (C := 4 * (8 * C_E + 4 * C_R)) (by positivity) 1
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro t₁ X N C₁ hXlb hXN hN2 hC₁0 hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_st hX8
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
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (k : ℝ) hkXA
  have hR := hRHS k hkfl hkN
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set B := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBdef
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4)) with hRdef
  have hid : A = (A - B) + ((B - R) + R) := by ring
  have htri : ‖A‖ ≤ ‖A - B‖ + (‖B - R‖ + ‖R‖) := by
    calc ‖A‖ = ‖(A - B) + ((B - R) + R)‖ := by rw [← hid]
      _ ≤ ‖A - B‖ + ‖(B - R) + R‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ + (‖B - R‖ + ‖R‖) := by
          linarith [norm_add_le (B - R) R]
  -- the `E`-error, reduced to the `D·k·loglog k/log k` shape
  have hlogpow : Real.log (Real.log (k : ℝ) ^ 4) = 4 * Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pow]; norm_num
  have hlogLk0 : (0 : ℝ) ≤ Real.log (Real.log (k : ℝ)) := Real.log_nonneg hLk1
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
        * Real.log (Real.log (k : ℝ) ^ 4)
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Real.log (k : ℝ) ^ 4)
      ≤ (8 * C_E + 4 * C_R)
          * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
    rw [hlogpow]
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * (4 * Real.log (Real.log (k : ℝ)))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ))) := by
      have hq : (0 : ℝ) ≤ 4 * Real.log (Real.log (k : ℝ)) := by linarith
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this hq
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
        = (8 * C_E + 4 * C_R)
            * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
      field_simp
      ring
    linarith
  -- the grade page
  have hgrade := center_error_grade_st (D := 8 * C_E + 4 * C_R) (X := X) (k := k)
    (by positivity) hX8 hk1 hk2 (hB X hXB)
  have hexpand : (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-- **The crown's supply, UNIFORM in the centre (`ball_sup_supplied_uniform`).**
`CenterSupply.ball_sup_supplied` on the hoisted supply; its own threshold summand
`ballMertensThreshold` is a numeral. -/
theorem ball_sup_supplied_uniform {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N : ℕ) (T C₁ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
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
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply_uniform hg t₀
  refine ⟨max X₁ ballMertensThreshold, lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro t₁ X N T C₁ a hXlb hXN hN2 hC₁0 hsupp hDatum hRHS hMcap
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hXth : ballMertensThreshold ≤ X := le_trans (le_max_right _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hS₀ : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
      mul_nonneg hC₁0 (Real.exp_nonneg _)
    have h2 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogX0 _
    linarith
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
    hS₀ hsupp hDatum (hsupply t₁ X N C₁ hX1 hXN hN2 hC₁0 hRHS) hMball

set_option maxHeartbeats 800000 in
-- As at `FarStar.ball_sup_closed_star`: the crown's binder block is instantiated wholesale.
/-- **THE CROWN AT `T*`, UNIFORM IN THE CENTRE (`ball_sup_closed_star_uniform`).**
`FarStar.ball_sup_closed_star` with `∃ X₀` hoisted over `t₁`.  Its proof consumes
`ball_sup_supplied` (now hoisted) and `FarStar.hRHS_socket_star`, which carries no threshold
of its own; the carried hypothesis list is unchanged, item for item. -/
theorem ball_sup_closed_star_uniform {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N : ℕ) (Tb Cb Tann : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → Real.exp 1 ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ seamGateRstar X Tann →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ)) →
        (seamAnn X Tann ∩ seamBall X t₁).Nonempty →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
            (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
            (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
            (1 / Real.log (Real.log (k : ℝ) ^ 4))
            ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tb → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X ((gradeAbsConst Cb + farCStar)
                  * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, H⟩ := ball_sup_supplied_uniform hg t₀
  refine ⟨X₀, hX₀0, ?_⟩
  intro t₁ X N Tb Cb Tann a hXlb hXe hXN hN2 hCb0 hCbound hsupp hDatum hmin hMcapX hk64 hne
    hInt
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  exact H t₁ X N Tb (gradeAbsConst Cb + farCStar) a hXlb hXN hN2
    (by have := gradeAbsConst_nonneg hCb0; have := farCStar_nonneg; linarith) hsupp hDatum
    (hRHS_socket_star hg hCb0 hCbound hXe hN2 hmin (hMcapX X le_rfl (by linarith)) hk64 hne
      hInt) hMcapX

/-! ## §3 — AS-1: THE STATION

The composed exit.  Read the hypothesis list of the conclusion: `hg`, the seam datum's two
coefficient equations, the dyadic scale frame, `0 ≤ T_ann`, and — inside, at the centre this
theorem produces — the A-10 ball cap.  Everything else the crown enumerates is discharged
here: the Chebyshev datum `Cb` (`GradeConst.exists_shortIntervalDatum`, opened once,
outermost, so the constant `C₁` is ABSOLUTE), the compact minimality `hmin` and the
recentring gate (`FarStar.exists_min_gate_star` / `seam_gate_star_of_nonempty`, inside the
crown), the scale gate `e^{64} ≤ k` (from the threshold), the four integrability sockets (§1),
and the ball geometry `hne` — by the dichotomy, whose EMPTY arm supplies the very same binder
at the very same `S` (`SeamGate.seam_sup_binder_of_inter_empty`).

No `T_ann ≤ X/2` guard is needed here: the ⟦TWO-M⟧ option-(A) statement is uniform in both
regimes.  The guard enters only in §4, where the exit is re-expressed at MRT's `M(f;X)`. -/

set_option maxHeartbeats 1000000 in
-- The crown's binder block (eight sockets, five pin expressions each) is instantiated
-- wholesale, as at `FarStar.ball_sup_closed_star`; the unification exceeds the default budget.
/-- **AS-1 — THE hSUP STATION (`seam_ball_leg_station`).**  For an absolute constant `C₁` and
an absolute threshold `X₀`: on the seam row's frame the ball leg has a centre `t₁` — the
minimizer of the pretentious distance over the ENLARGED window `|v| ≤ seamGateRstar X T_ann`
(⟦TWO-M DIRECTION RATIFIED: OPTION (A)⟧) — at which

  `‖A_t(m)‖ ≤ ballSupS X (C₁·e^{−𝔻²(t₁)/(2e)} + 4(log X)^{−1/2+1/1000})·m/(1+|t−t₁|)`

for every `t` in the annulus∩ball and every `m ≤ N`: exactly
`SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup` binder, at the row's own annulus
height `T_ann`.

**The remaining hypotheses, in full**: `hg` (the primes' 1-boundedness); `X₀ ≤ X`,
`X ≤ N ≤ 2X` (the dyadic frame); `0 ≤ T_ann`; the two coefficient equations for `a`; and the
A-10 ball cap at the produced centre, carried as the antecedent of the exit — it is the seam's
own case split (the ball arm's live band), not an analytic socket.  **Nothing else.** -/
theorem seam_ball_leg_station {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tann : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ Tann →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        ∃ t₁ : ℝ, |t₁| ≤ seamGateRstar X Tann ∧
          (∀ v : ℝ, |v| ≤ seamGateRstar X Tann →
            pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
              ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) ∧
          ((∀ x : ℝ, X ≤ x → x ≤ 2 * X →
              pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
                ≤ (1 / 16) * Real.log (Real.log X)) →
            ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
              ∀ m : ℕ, m ≤ N →
                ‖spolyA a t m‖
                  ≤ ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|)) := by
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  obtain ⟨X₀, hX₀0, H⟩ := ball_sup_closed_star_uniform hg t₀
  refine ⟨gradeAbsConst Cb + farCStar, max X₀ (Real.exp 64 + 1),
    by have := gradeAbsConst_nonneg hCb0; have := farCStar_nonneg; linarith,
    lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro X N Tann a hXlb hXN hN2 hTann hsupp hDatum
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX64 : Real.exp 64 + 1 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXe : Real.exp 1 ≤ X := by
    have h1 : Real.exp 1 ≤ Real.exp 64 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith [Real.add_one_le_exp (1 : ℝ)]
  -- the centre: the compact minimizer at the star radius
  obtain ⟨t₁, ht₁abs, hmin⟩ :=
    exists_min_gate_star (seamCoeff (ellLin g) (fun _ => 1) t₀) hTann hX1
  refine ⟨t₁, ht₁abs, hmin, ?_⟩
  intro hMcap
  -- the scale gate, from the threshold alone
  have hk64 : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ) := by
    intro k hk1 _
    have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h2 : (⌊X⌋₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  -- the four integrability sockets, hypothesis-free (§1)
  have hInt : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
        (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
        (1 / Real.log (Real.log (k : ℝ) ^ 4))
        ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    fun k hk1 hk2 => jointIntegrableAt_pin_free hg (t₀ + t₁) _ (hk64 k hk1 hk2)
  -- the ball geometry: the dichotomy, both arms at the SAME `S`
  rcases Set.eq_empty_or_nonempty (seamAnn X Tann ∩ seamBall X t₁) with hE | hne
  · exact seam_sup_binder_of_inter_empty hE
  · exact H t₁ X N Tann Cb Tann a hXX₀ hXe hXN hN2 hCb0 hCbound hsupp hDatum hmin hMcap hk64
      hne hInt

/-! ## §4 — AS-2: the option-(A) corollary at MRT's own `M(f;X)`

⟦A.3 FAITHFULNESS CHECK⟧: MRT's Proposition A.3 opens by reducing to `T ≤ X/2` (the mean
value theorem covers `T > X/2` with `O(T/X + 1)`), and states its grade at
`M(f;X) = inf_{|t| ≤ X} 𝔻²`.  Carrying that reduction here — as the row's guard
`T_ann ≤ X/2` — the enlarged radius obeys

  `seamGateRstar X T_ann = T_ann + seamRad X + T*(2X) + 1 ≤ X/2 + X/8 + X/4 + 1 ≤ X`,

since `T*` is sub-polynomial (`T*(2X) = (log 2X)⁴·(2X)^{1/(4 loglog 2X)} ≤ (log 2X)⁴·√(2X)`)
and `log` is.  So the produced centre lies in MRT's window, `[−R, R] ⊆ [−X, X]`, and the
option-(A) exit implies the `M(f;X)` one — stated here at an arbitrary lower bound `M₀` for
`𝔻²(·; X)` on `|v| ≤ X`, of which `M(f;X)` is the greatest. -/

/-- `8·(log X)⁴ ≤ √X` eventually (`isLittleO_log_rpow_rpow_atTop` at exponents `4` and `1/2`,
as in `HExit`'s private clone, with the constant the station needs). -/
private lemma eight_logpow4_le_sqrt_st :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → 8 * (Real.log X) ^ 4 ≤ Real.sqrt X := by
  have hlo : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[Filter.atTop]
      fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / 8 by norm_num)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (4 : ℝ) := Real.rpow_nonneg hlogXnn 4
  have h2nn : (0 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow] at hkey
  linarith [hkey]

/-- **The MVT guard closes the radius (`seamGateRstar_le_self`).**  Under `T_ann ≤ X/2` — MRT's
own opening reduction — the enlarged minimality radius sits below `X` for all large `X`:
`seamRad X ≤ X/8` (a log), `T*(2X, log 2X) ≤ X/4` (sub-polynomial), `1 ≤ X/8`. -/
theorem seamGateRstar_le_self :
    ∃ X₁ : ℝ, 0 < X₁ ∧ ∀ X T : ℝ, X₁ ≤ X → 0 ≤ T → T ≤ X / 2 → seamGateRstar X T ≤ X := by
  obtain ⟨A, hA⟩ := eight_logpow4_le_sqrt_st
  refine ⟨max (max A 256) (Real.exp 8), lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro X T hX hT0 hTX
  have hAX : A ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX256 : (256 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hLX8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLX1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
  have hsq0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsqX : Real.sqrt X ≤ X := by nlinarith [hsq, hsq0, hX256]
  -- the seam radius: a log, below `X/8`
  have hrad : seamRad X ≤ X / 8 := by
    have h1 : Real.log X ^ (1 / 16 : ℝ) ≤ Real.log X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num)
    rw [Real.rpow_one] at h1
    have h2 : Real.log X ≤ Real.log X ^ 4 := by
      nlinarith [hLX8, sq_nonneg (Real.log X), sq_nonneg (Real.log X - 1)]
    have h3 := hA X hAX
    unfold seamRad
    linarith
  -- the star height: sub-polynomial, below `X/4`
  have h2X : (1 : ℝ) ≤ 2 * X := by linarith
  have hA2X : A ≤ 2 * X := by linarith
  have hL2X : Real.log X ≤ Real.log (2 * X) := Real.log_le_log hX0 (by linarith)
  have hL2X8 : (8 : ℝ) ≤ Real.log (2 * X) := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log (2 * X)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hstar : Tstar (2 * X) (Real.log (2 * X)) ≤ X / 4 := by
    have hexp : 1 / (4 * Real.log (Real.log (2 * X))) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hpow : (2 * X) ^ (1 / (4 * Real.log (Real.log (2 * X)))) ≤ (2 * X) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2X hexp
    rw [← Real.sqrt_eq_rpow (2 * X)] at hpow
    have hs2 : Real.sqrt (2 * X) * Real.sqrt (2 * X) = 2 * X :=
      Real.mul_self_sqrt (by linarith)
    have hs20 : (0 : ℝ) ≤ Real.sqrt (2 * X) := Real.sqrt_nonneg _
    have hlog4nn : (0 : ℝ) ≤ Real.log (2 * X) ^ 4 := by positivity
    have hA2 := hA (2 * X) hA2X
    have step1 : Real.log (2 * X) ^ 4 * (2 * X) ^ (1 / (4 * Real.log (Real.log (2 * X))))
        ≤ Real.log (2 * X) ^ 4 * Real.sqrt (2 * X) :=
      mul_le_mul_of_nonneg_left hpow hlog4nn
    have step2 : Real.log (2 * X) ^ 4 * Real.sqrt (2 * X)
        ≤ Real.sqrt (2 * X) / 8 * Real.sqrt (2 * X) :=
      mul_le_mul_of_nonneg_right (by linarith) hs20
    have step3 : Real.sqrt (2 * X) / 8 * Real.sqrt (2 * X) = X / 4 := by
      have hcomm : Real.sqrt (2 * X) / 8 * Real.sqrt (2 * X)
          = Real.sqrt (2 * X) * Real.sqrt (2 * X) / 8 := by ring
      rw [hcomm, hs2]
      ring
    unfold Tstar
    linarith
  unfold seamGateRstar
  linarith

/-- `ballSupS X ·` is monotone in the centre bound `S₀` (an affine function with a
nonnegative slope). -/
lemma ballSupS_mono (X : ℝ) {S₀ S₁ : ℝ} (h : S₀ ≤ S₁) : ballSupS X S₀ ≤ ballSupS X S₁ := by
  unfold ballSupS
  have h2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
-- The exit's `S`-slot carries the five pin expressions of the crown; the transfer unifies
-- them twice (once per side of the monotonicity step).
/-- **AS-2 — THE STATION AT `M(f;X)` (`seam_ball_leg_station_M`).**  AS-1 under the MVT guard
`T_ann ≤ X/2`, with the exit re-stated at any lower bound `M₀` of the pretentious distance on
MRT's own window `|v| ≤ X` — in particular at `M(f;X) = inf_{|t|≤X} 𝔻²(f, n^{it}; X)`:

  `‖A_t(m)‖ ≤ ballSupS X (C₁·e^{−M(f;X)/(2e)} + 4(log X)^{−1/2+1/1000})·m/(1+|t−t₁|)`.

The produced centre additionally satisfies `|t₁| ≤ X`, so it IS an admissible point of MRT's
window (the `[−R,R] ⊆ [−X,X]` comparison of ⟦TWO-M DIRECTION RATIFIED: OPTION (A)⟧).  The
hypothesis list is AS-1's plus the guard. -/
theorem seam_ball_leg_station_M {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tann M₀ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ Tann → Tann ≤ X / 2 →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ X →
          M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        ∃ t₁ : ℝ, |t₁| ≤ X ∧
          ((∀ x : ℝ, X ≤ x → x ≤ 2 * X →
              pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
                ≤ (1 / 16) * Real.log (Real.log X)) →
            ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
              ∀ m : ℕ, m ≤ N →
                ‖spolyA a t m‖
                  ≤ ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
                      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|)) := by
  obtain ⟨C₁, X₀, hC₁0, hX₀0, H⟩ := seam_ball_leg_station hg t₀
  obtain ⟨X₁, hX₁0, hR⟩ := seamGateRstar_le_self
  refine ⟨C₁, max X₀ X₁, hC₁0, lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro X N Tann M₀ a hXlb hXN hN2 hTann hTX hsupp hDatum hM₀
  obtain ⟨t₁, ht₁abs, _hmin, hexit⟩ :=
    H X N Tann a (le_trans (le_max_left _ _) hXlb) hXN hN2 hTann hsupp hDatum
  have hRX : seamGateRstar X Tann ≤ X :=
    hR X Tann (le_trans (le_max_right _ _) hXlb) hTann hTX
  have ht₁X : |t₁| ≤ X := le_trans ht₁abs hRX
  refine ⟨t₁, ht₁X, fun hMcap t ht1 ht2 ht3 m hm => ?_⟩
  have hbase := hexit hMcap t ht1 ht2 ht3 m hm
  have hM : M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X :=
    hM₀ t₁ ht₁X
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have hexp : Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hS : C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    nlinarith
  have hmono := ballSupS_mono X hS
  have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
  refine le_trans hbase ?_
  rw [div_le_div_iff₀ hd hd]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmono (Nat.cast_nonneg m)) hd.le

/-! ## §5 — AS-3: the station in the row's ball slot

`SeamBallWeighted.prop_A3_T1_row_split_weighted` takes the centre `t₁` and the sup constant
`S` as FREE parameters and consumes exactly AS-1's binder, so the plug is a composition with
no adapter: the row's `hSup` slot is `seam_ball_leg_station`'s exit verbatim, at
`S := ballSupS X (C₁·e^{−𝔻²(t₁)/(2e)} + 4(log X)^{−1/2+1/1000})`, and the ball leg lands as
`8S²`. -/

/-- **AS-3 — THE SEAM ROW ON THE STATION'S BALL LEG (`prop_A3_T1_row_station`).**
`prop_A3_T1_row_split_weighted` with its `hSup` binder supplied by AS-1 at the centre the
station produces:

  `∫_{Ann} ‖spoly‖² ≤ 8·ballSupS X (C₁·e^{−𝔻²(t₁)/(2e)} + 4(log X)^{−1/2+1/1000})²
      + ∫_{(Ann∖ball) ∩ 𝒯tot} ‖spoly‖² + U`.

The `𝒯`-leg and `hU` are the row's own (the §8.3 interior); the ball leg is now closed. -/
theorem prop_A3_T1_row_station {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tann : ℝ) (a fb : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (Jb : ℕ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ Tann →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        ∃ t₁ : ℝ, |t₁| ≤ seamGateRstar X Tann ∧
          ((∀ x : ℝ, X ≤ x → x ≤ 2 * X →
              pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
                ≤ (1 / 16) * Real.log (Real.log X)) →
            ∀ U : ℝ,
              (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ Uset fb Pseq Qseq δ Jb,
                ‖spoly N a t‖ ^ 2) ≤ U →
              (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
                ≤ 8 * ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                    + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) ^ 2
                  + (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ seamTtot fb Pseq Qseq δ Jb,
                      ‖spoly N a t‖ ^ 2) + U) := by
  obtain ⟨C₁, X₀, hC₁0, hX₀0, H⟩ := seam_ball_leg_station hg t₀
  refine ⟨C₁, max X₀ 1, hC₁0, lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro X N Tann a fb Pseq Qseq δ Jb hXlb hXN hN2 hTann hsupp hDatum
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨t₁, ht₁abs, _hmin, hexit⟩ :=
    H X N Tann a (le_trans (le_max_left _ _) hXlb) hXN hN2 hTann hsupp hDatum
  refine ⟨t₁, ht₁abs, fun hMcap U hU => ?_⟩
  exact prop_A3_T1_row_split_weighted a N fb Pseq Qseq δ Jb X Tann t₁ _ U hL hTann hX0 hXN hN2
    hsupp (hexit hMcap) hU

end Salt.MR
