/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.GradeConst
import Salt.MR.TruncFactor

/-!
# GRADE-CLOSE rung B-4 — the truncated grade seam (`SupClose`)

**What this file is.**  `GradeConst`'s capstone (`center_halasz_of_grade_const`) still carries
the ON-`ℝ` minimality binder `hmin : ∀ v : ℝ, …` — the sixth vacuity catch.  `TruncFactor`
(B-1/B-1b) supplies the compact replacement (`center_dist_floor_trunc`,
`center_dist_floor_compact`, `joint_cs_factoring_trunc`).  This file is the SEAM between
them: the compact minimality is carried through the pin's `supF` binder into
`joint_cs_factoring_trunc`, giving the grade at scale with NO `∀ v : ℝ` anywhere and the far
part carried as one honest additive remainder.

## The two walls found (why the naive swap does not typecheck)

1. **The `hMt` wall.**  `GradeConst.rhs_grade_at_scale_const` takes
   `hMt : ∀ t : ℝ, M ≤ 𝔻²(…; k)` — the WHOLE line — because it is built on
   `JointHead.joint_cs_factoring`, whose `hsupF` binder is `∀ t : ℝ`.  Substituting
   `center_dist_floor_trunc` (which produces the floor only for `|t − t₀| ≤ R`) at the
   capstone's `center_dist_floor` slot is an application type mismatch.  The swap therefore
   cannot happen at the capstone; it must happen one rung DOWN, at the factoring — which is
   what `joint_cs_factoring_trunc` is for, and what this file does.
2. **The recentring wall (the "overhang" of ⟦V3⟧).**  The truncated contour is centred at
   `t₀' = t₀ + t₁`, while `center_dist_floor_trunc`'s hypothesis and conclusion share ONE
   radius `R` centred at the SEAM point `t₀`.  A contour point `|t − t₀'| ≤ T` has
   `|t − t₀| ≤ T + |t₁|`, so the floor is available exactly under the gate `|t₁| + T ≤ R`
   (`center_dist_floor_recentred` below).  The compact minimizer of
   `CompactMin.exists_min_dist_abs` at radius `R` supplies `|t₁| ≤ R` — NOT `|t₁| ≤ R − T`
   — so it does not by itself discharge the gate; a consumer must bound the centre's
   location independently.  The gate is carried as a hypothesis, never forced.

## What is carried out of here

`rhs_grade_at_scale_trunc`'s exit is

  `‖prop21RHS‖ ≤ gradeAbsConst Cb · k · e^{−(1/(2e))·M} + (1/π)·η²·(Ffar·Kfar)`,

`M` the seam datum's own distance at the centre `t₁` — the main term is BYTE-IDENTICAL to
`hRHS_discharged_const`'s right-hand side, and the far part is the un-absorbed remainder.
Absorbing that remainder into `C₁·k·e^{−(1/(2e))·M}` needs the live-band cap on `M`
(`hMcap`) and the numerals for `Ffar`/`Kfar` at the pin — the analysis rung that separates
this exit from `center_halasz_supply`'s `hRHS` binder.  It is NOT done here.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set

/-! ## §0 — the pin's arithmetic, re-derived

`GradeConst`'s `four_log_le_selfC` / `pin_basic64` are `private`; the two re-derivations
below are verbatim (same proofs, same statements). -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `GradeConst`'s private
`four_log_le_selfC`. -/
private lemma four_log_le_selfS {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- The pin's elementary arithmetic at the `e^{64}` gate.  Re-derivation of `GradeConst`'s
private `pin_basic64`. -/
private lemma pin_basic64S {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ 0 < Real.log y ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L ≤ η ∧ L ^ 4 ≤ k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hy131072 : (131072 : ℝ) ≤ y := by
    rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  refine ⟨hk0, hL64, hy131072, hlogy0, by rw [hη]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_le_div_iff₀ hL0 (by linarith)]
    linarith [four_log_le_selfS hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfS hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-- Continuity of `α ↦ a^{−α}`.  Re-derivation of `GradeConst`'s private
`continuous_rpow_negC`. -/
private lemma continuous_rpow_negS {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative.  Re-derivation of `GradeConst`'s private
`widthKamp_nonneg`. -/
private lemma widthKamp_nonnegS {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-! ## §1 — the pin's `supF` at a SINGLE contour point -/

/-- **S-A — the pointwise pin `supF` (`joint_supF_pin_at`).**  `RHSGrade.joint_supF_pin` with
its floor binder taken at the ONE contour point where the proof uses it: `joint_supF_pin`
asks for `∀ t : ℝ, M ≤ 𝔻²(…; k)` but consumes it only as `hMt t` (`RHSGrade.lean:313`), so
the per-`t` form is a strict weakening, proved by the same page.

This is the stone the CONTOUR TRUNCATION needs: on the truncated contour the floor is
available only for `|t − t₀| ≤ R`, never for all `t`. -/
theorem joint_supF_pin_at {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀' M k L c₀ y η : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ)
    (hMt : M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  -- the `y`-gates
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hylo : Real.exp 1 ≤ y := by
    rw [hy]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL3 4]
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  have hη4 : η ≤ 1 / 4 := by
    rw [hη, hlogy]
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- the twisted datum is 1-bounded at primes
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  -- the scale condition `e^{1/σ} ≤ k` on `σ ≥ 1/L`
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := 1 / (2 * Real.exp 1)) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) (by positivity)
    (by
      rw [div_le_div_iff₀ (by positivity) (Real.exp_pos 1)]
      nlinarith [Real.exp_pos 1])
    hylo (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hη]; exact hαη) (by rw [← hη]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFbound rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hMt hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-! ## §2 — the recentred floor: the gate the truncation forces -/

/-- **S-B — the RECENTRED truncated floor (`center_dist_floor_recentred`).**
`TruncFactor.center_dist_floor_trunc` at the contour centre the grade actually uses.

The grade's contour is centred at `t₀' = t₀ + t₁` (the twisted datum's frequency), while the
minimality radius `R` is centred at the SEAM point `t₀`.  A truncated contour point
`|t − t₀'| ≤ T` therefore satisfies `|t − t₀| ≤ T + |t₁|`, and the floor is available exactly
under the gate

  `|t₁| + T ≤ R`.

That gate is the WEAKEST covering the chain's single consumption point, and it is carried,
never forced: `CompactMin.exists_min_dist_abs` at radius `R` gives `|t₁| ≤ R`, which does NOT
imply `|t₁| ≤ R − T`.  Closing it needs an independent bound on the centre's location — the
⟦V3⟧ "overhang". -/
theorem center_dist_floor_recentred {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X z R T : ℝ} (hXz : ⌊X⌋₊ ≤ ⌊z⌋₊)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hgate : |t₁| + T ≤ R) {t : ℝ} (ht : |t - (t₀ + t₁)| ≤ T) :
    pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
          (costwist (t - (t₀ + t₁))) z := by
  have hR : |t - t₀| ≤ R := by
    have htri := abs_add_le (t - (t₀ + t₁)) t₁
    rw [show t - (t₀ + t₁) + t₁ = t - t₀ from by ring] at htri
    linarith
  exact center_dist_floor_trunc hg hXz hmin hR

/-! ## §3 — the `hsupF` binder of `joint_cs_factoring_trunc`, discharged -/

/-- **S-C — the truncated pin `supF` (`joint_supF_pin_trunc`).**
`TruncFactor.joint_cs_factoring_trunc`'s `hsupF` binder byte-for-byte, discharged from the
COMPACT minimality alone (`|v| ≤ R`) — no `∀ v : ℝ` anywhere.

`S-B` supplies the floor at each truncated contour point, `S-A` converts it into the pin's
`Fbound`.  The floor constant is the seam datum's OWN distance at the centre `t₁`, i.e.
exactly the `M` appearing in `hRHS_discharged_const`'s exponent. -/
theorem joint_supF_pin_trunc {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X k L c₀ y η R T : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L) (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ, |t - (t₀ + t₁)| ≤ T →
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
            L (β + 1 / L) := by
  intro α hα β hβ t ht
  exact joint_supF_pin_at hg hk hL hy hη hc₀eq hα.1 hβ.1 hα.2 hβ.2 t
    (center_dist_floor_recentred hg hXk hmin hgate ht)

/-- **S-D — the TRUNCATED joint factoring at the pin (`joint_cs_trunc_pin`).**
`joint_cs_factoring_trunc` with `hsupF` discharged by `S-C`: the joint head's `prop21RHS`
against the pin's own `Fbound`, with the compact minimality as the ONLY frequency hypothesis.

The far arm (`Ffar`, `Kfar` and the two binders `hFar`/`hKfar`) is `joint_cs_factoring_trunc`'s
own — threaded verbatim, not invented here, and NOT discharged: `hFar` is the FREE `M = 0`
majorant and `hKfar` is `TruncFactor.crossKerFar_pin_le` at `T := L⁴`.

This compile is the byte-exactness certificate for `S-C`. -/
theorem joint_cs_trunc_pin {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X k L c₀ y η h R T Ffar Kfar : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L) (hh0 : 0 < h) (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β T ≤ Kfar)
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                  (t₀ + t₁) α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL64, -, -, hη0, hη8, -, -⟩ := pin_basic64S hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hk1 : (1 : ℝ) ≤ k := by
    have h65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hk3 : Real.exp 3 ≤ k := by
    have h3 : Real.exp 3 ≤ Real.exp 64 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  refine joint_cs_factoring_trunc hk1 hh0 hη0.le ?_ hFfar0 ?_
    (joint_supF_pin_trunc hg hk3 hL hy hη hc₀eq hXk hgate hmin) hFar hKfar hIβ hIβ' hIα hIα'
  · rw [hc₀eq]; linarith
  · exact fun _ _ β hβ => rhsFbound_nonneg _ _ (by linarith [hβ.1])

/-! ## §4 — the grade at scale, truncated -/

/-- **S-E — THE TRUNCATED GRADE AT SCALE (`rhs_grade_at_scale_trunc`).**
`GradeConst.rhs_grade_at_scale_const`'s conclusion with its `∀ t : ℝ` floor binder `hMt`
REPLACED by the compact minimality `hmin` (`|v| ≤ R`), at the cost of the one additive far
term of `joint_cs_factoring_trunc`:

  `‖prop21RHS‖ ≤ gradeAbsConst Cb · k · e^{−(1/(2e))·M} + (1/π)·η²·(Ffar·Kfar)`,
  `M = 𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t₁; X)`.

The main term is `hRHS_discharged_const`'s right-hand side BYTE-FOR-BYTE (same
`gradeAbsConst Cb · k · e^{−M/(2e)}`), so the only distance between this exit and
`CenterSupply.center_halasz_supply`'s `hRHS` binder is the far remainder.

**The remainder is NOT absorbed here.**  Absorbing `(1/π)·η²·(Ffar·Kfar)` into
`C₁·k·e^{−(1/(2e))·M}` needs (i) the numerals for `Ffar` (the FREE `M = 0` majorant,
`β`-uniform) and `Kfar` (`crossKerFar_pin_le` at `T := L⁴`), and (ii) the live-band cap on
`M` (`hMcap`), since `e^{−M/(2e)}` is what the far term must be measured against.  That is
the analysis rung; this file stops at the algebra. -/
theorem rhs_grade_at_scale_trunc {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X k L c₀ y η h R T Ffar Kfar : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β T ≤ Kfar)
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ gradeAbsConst Cb * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  obtain ⟨hk0, hL64, -, -, hη0, -, -, hyk⟩ := pin_basic64S hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hh0, -, -, -⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have hyk' : y ≤ k := by rw [hy]; exact hyk
  have hM0 : (0 : ℝ) ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X :=
    pretDistSq_nonneg _ _ _
      (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
      (fun n => le_of_eq (costwist_norm t₁ n))
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hKamp0 : (0 : ℝ) ≤ widthKamp Cb k h y c₀ := widthKamp_nonnegS hCb0 hk0 hh0 hy0
  have hG0 : (0 : ℝ) ≤ rhsSigmaG
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L := by
    unfold rhsSigmaG
    have hE : (0 : ℝ) ≤ Real.exp (1 / (2 * Real.exp 1) * 48)
        / (1 - 2 * (1 / (2 * Real.exp 1))) := by
      have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
        rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
        have h1 : 1 / Real.exp 1 < 1 := by
          rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
        linarith
      positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  -- the truncated factoring, with the compact minimality as the only frequency hypothesis
  have hJ1 := joint_cs_trunc_pin hg hk hL hy hη hc₀ hh0 hXk hgate hmin hFfar0 hFar hKfar
    ⟨hIβ, hIβ', hIα, hIα'⟩
  -- the MAIN term: `rhs_grade_at_scale_const`'s own page, unchanged
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η,
          rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              L (β + 1 / L)
            * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                (t₀ + t₁) α β)
        ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L :=
    fun α hα => beta_integral_pin_const _ hgtw hCb0 hCbound hk hL hy hη hc₀ hh hyk' hM0
      hα.1 hα.2 (hIβ α hα)
  have hKcont : Continuous
      (fun α : ℝ => (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L) :=
    ((continuous_rpow_negS hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L
      = (widthKamp Cb k h y c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * ((k + h) ^ (-α)) := fun α => by ring
  have hpull : (∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
      = (widthKamp Cb k h y c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith) hη0.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
            L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
              (t₀ + t₁) α β
      ≤ (1 / Real.pi) * ((widthKamp Cb k h y c₀
          * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
            * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
              rhsFbound (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                  L (β + 1 / L)
                * crossKer (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀
                    (t₀ + t₁) α β)
        ≤ ∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α))
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                L := hmono
      _ = (widthKamp Cb k h y c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
              * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (widthKamp Cb k h y c₀
            * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
              * (1 / L) := mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  have hmaineq : (1 / Real.pi) * ((widthKamp Cb k h y c₀
        * rhsSigmaG (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) L)
          * (1 / L))
      = rhsAgradeConst Cb k h y c₀
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
    have hexpeq : Real.exp (-(1 / (2 * Real.exp 1)
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X))
        = Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
      rw [neg_mul]
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    unfold rhsAgradeConst rhsSigmaG
    rw [← hexpeq]
    field_simp
  -- the amplitude at the absolute constant
  have habs : rhsAgradeConst Cb k h y c₀
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      ≤ gradeAbsConst Cb * k
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
    mul_le_mul_of_nonneg_right (rhsAgradeConst_le hCb0 hk hL hy hh hc₀) (Real.exp_nonneg _)
  have hmain := hstep.trans (le_of_eq hmaineq)
  linarith

end Salt.MR
