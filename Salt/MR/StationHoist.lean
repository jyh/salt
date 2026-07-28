/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SPartStation

/-!
# The station exit with its threshold HOISTED (`StationHoist`)

Freeze: `docs/exploration/s8-freeze-0727.md`, ⟦AMENDMENT I⟧ finding 2.

`SPartStation.seam_ball_leg_station_M_gen` reads

  `∀ t₀ t₁, ∃ X₀, 0 < X₀ ∧ ∀ X …, X₀ ≤ √X → …`

— the threshold sits UNDER the centre `t₁`.  `ThmA2Rows` (module docstring, item 2) records
the consequence: on the socketed branch the centre `v₀` is PRODUCED inside the proof (by
`ThmA2.a2_row_cap_of_not_capFreeFloor`), so no single `X₀ ≤ √X` hypothesis can be stated in
advance and the ball-leg supply is carried as the `hStation` binder rather than derived.

The landed proof's witness is `max (max X₁ ballMertensThreshold) (exp 4096)` with `X₁` from
`center_halasz_supply_wide hgF t₀ (fun x => (log x)^4)` — and that supply is ALREADY uniform
in the centre (`t₁` is the first variable under its own `∃X₀`, `SPartStation` :302–319).  So
the witness is `t₁`-free and the quantifier order is an artefact of the statement, not of
the mathematics.  This file states the twin with the order fixed:

* `seam_ball_leg_station_M_hoisted` — `_M_gen` verbatim with `∀ t₁` moved UNDER `∃ X₀`, so
  ONE `X₀` serves every centre.  The proof is `_M_gen`'s, transplanted with the `intro` of
  `t₁` moved after the `refine` (the witness line is unchanged); it is NOT derivable from
  `_M_gen` itself, whose statement gives only a per-centre `X₀` with no uniform bound.
* `hStation_of_hoisted` — the consumer plug: the twin in the exact shape of
  `ThmA2Rows.a2Rows_of_cap`'s `hStation` binder, at a named grade `Sb`.

**What the hoist does NOT remove.**  The T3 gap (⟦AMENDMENT B⟧) is untouched: `hMcap`, the
A-10 ball cap `𝔻²(seamCoeff F 1 t₀, p^{it₁}; x) ≤ (1/16)loglog X` on `x ∈ [X,2X]`, is a
statement about the `t₀`-SHIFTED datum which the routing witness does not supply, and in the
plug it REMAINS a binder — now quantified over the box, `∀ t₁, |t₁| ≤ X → …`.  Also still
carried: the `M₀` distance floor out to `Rad` (the D10 defect), the dissection gates, the
scale frame, and `a`'s two coefficient equations.  What the hoist removes is exactly the
quantifier obstruction of item 2 — the threshold now precedes the centre, so a consumer
holding `X₀ ≤ √X` may apply the supply at a centre produced later in its own proof.

Three helpers of `SPartStation` §4 (`eight_log_le_self_sp`, `ypin4_gates_sp`,
`le_natDiv_of_le`) are `private` there; they are re-derived here verbatim, suffixed `_hs`.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation

/-! ## §1 — the three `private` helpers of `SPartStation` §4, re-derived -/

/-- `8·log L ≤ L` for `L ≥ 64` (`FarStar.eight_log_le_selfT`, re-derived — `private` there). -/
private lemma eight_log_le_self_hs {Lv : ℝ} (h : 64 ≤ Lv) : 8 * Real.log Lv ≤ Lv := by
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

/-- **The four `Y`-gates at the corpus pin `Y x = (log x)^4`**, from the single scale gate
`e^{4096} ≤ k`.  The binding one is the fourth, `log (Y k) = 4 log L ≤ √L`, which is
`8 log s ≤ s` at `s = √L`; it needs `√L ≥ 64`, i.e. `L ≥ 4096`.  (`SupplyGeneric`'s
`ypin2_gates_Y` is the same page at the OTHER pin `y₂ = exp(L^{2/5})`, where the gate is
`2/5 < 1/2`.) -/
private lemma ypin4_gates_hs {k : ℝ} (hk : Real.exp 4096 ≤ k) :
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
  -- the log-power identity
  have hlogpow : Real.log (Real.log k ^ 4) = 4 * Real.log (Real.log k) := by
    rw [Real.log_pow]; push_cast; ring
  -- the binding gate: `4 log L ≤ √L`
  have hbind : 4 * Real.log (Real.log k) ≤ Real.sqrt (Real.log k) := by
    have h8 := eight_log_le_self_hs hsqL64
    have hhalf : Real.log (Real.sqrt (Real.log k)) = Real.log (Real.log k) / 2 :=
      Real.log_sqrt hL0.le
    rw [hhalf] at h8
    linarith
  -- gate 2: `L^4 ≤ √k`
  have hg2 : Real.log k ^ 4 ≤ Real.sqrt k := by
    have hsk : Real.sqrt k = Real.exp (Real.log k * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
    have hp4 : Real.log k ^ 4 = Real.exp (4 * Real.log (Real.log k)) := by
      rw [← hlogpow]
      exact (Real.exp_log (by positivity)).symm
    rw [hsk, hp4]
    refine Real.exp_le_exp.mpr ?_
    have h8 := eight_log_le_self_hs (le_trans (by norm_num) hL)
    linarith
  refine ⟨by nlinarith, hg2, le_trans hsqLle hL4, ?_⟩
  rw [hlogpow]
  exact hbind

/-- The floor of a real quotient dominates any `z` one unit below it: if `z + 1 ≤ k/d` then
`z ≤ ⌊k/d⌋` (Nat division).  The dissection's window arithmetic. -/
private lemma le_natDiv_of_le_hs {k d : ℕ} {z : ℝ} (hd : 1 ≤ d)
    (h : z + 1 ≤ (k : ℝ) / (d : ℝ)) : z ≤ ((k / d : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmod : (d : ℝ) * ((k / d : ℕ) : ℝ) + ((k % d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.div_add_mod k d
  have hlt : ((k % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.mod_lt k (show 0 < d by omega)
  have h2 : (k : ℝ) / (d : ℝ) - 1 < ((k / d : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd0]
    nlinarith
  linarith

/-! ## §2 — the hoisted twin -/

set_option maxHeartbeats 1000000 in
-- `SPartStation.seam_ball_leg_station_M_gen`'s own budget, transplanted with its proof: the
-- crown's binder block is instantiated wholesale and the `S`-slot carries the assembled
-- grade expression twice.
/-- **THE STATION EXIT WITH ITS THRESHOLD HOISTED** (`seam_ball_leg_station_M_hoisted`).
`SPartStation.seam_ball_leg_station_M_gen` with `∀ t₁` moved UNDER `∃ X₀`: one threshold
serves EVERY centre.  Hypotheses, grade and conclusion are otherwise verbatim —

  `‖A_t(m)‖ ≤ ballSupS X S₀ · m/(1+|t−t₁|)`,
  `S₀ = cSq·(C₁(c,Cb)·e^{−(1/(2e))(M₀ − dilGap X Xd)} + farCStar·(log X/2)^{−1/(32e)}
        + 4(log X)^{−1/2+1/1000}) + cSq·D^{−1/4}`, `cSq = 20736`.

**Why this is a transplant and not a corollary.**  `_M_gen` gives, at each `t₁`, SOME
`X₀(t₁) > 0`; nothing in its statement bounds those thresholds uniformly, so the hoisted
form does not follow from it.  It follows from its PROOF: the only source of `X₀` there is
`center_halasz_supply_wide hgF t₀ Y`, whose own `∃X₀` already quantifies `t₁` INSIDE, and
the witness `max (max X₁ ballMertensThreshold) (exp 4096)` mentions no centre.  The proof
below is `_M_gen`'s with `t₁` intro'd after the `refine`; every later step is the
original's, unchanged. -/
theorem seam_ball_leg_station_M_hoisted {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1) (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (t₁ X : ℝ) (N D : ℕ) (Cb Xd M₀ Rad T : ℝ) (a : ℕ → ℂ),
        X₀ ≤ Real.sqrt X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ D → Real.sqrt X ≤ Xd → Xd ≤ X → (D : ℝ) * (Xd + 1) ≤ X - 1 →
        |t₁| + Tstar (2 * X) (Real.log (2 * X)) ≤ Rad →
        (∀ v : ℝ, |v| ≤ Rad →
          M₀ ≤ pretDistSq (seamCoeff (ellLin F) (fun _ => 1) t₀) (costwist v) X) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff F (fun _ => 1) t₀ n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff F (fun _ => 1) t₀) (costwist t₁) x
            ≤ 1 / 16 * Real.log (Real.log X)) →
        ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N →
            ‖spolyA a t m‖
              ≤ ballSupS X (cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
                      * Real.exp (-(1 / (2 * Real.exp 1)) * (M₀ - dilGap X Xd))
                    + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
                    + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
                  + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * m / (1 + |t - t₁|) := by
  have hgF : ∀ p : ℕ, p.Prime → ‖F p‖ ≤ 1 := fun p _ => hFb p
  have hF1 : F 1 = 1 := by
    have h := hFm.map_one
    rwa [toAF_apply, if_neg one_ne_zero] at h
  obtain ⟨X₁, hX₁0, hsupply⟩ :=
    center_halasz_supply_wide hgF t₀ (fun x => Real.log x ^ 4)
  refine ⟨max (max X₁ ballMertensThreshold) (Real.exp 4096),
    lt_of_lt_of_le (Real.exp_pos 4096) (le_max_right _ _), ?_⟩
  intro t₁ X N D Cb Xd M₀ Rad T a hXlb hXN hN2 hCb0 hCbound hD hsqXd hXdX hDgate hRad hM₀
    hsupp hDatum hMcap
  set c : ℝ := 1 / (2 * Real.exp 1) with hcdef
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hc1 : 2 * c < 1 := by
    rw [hcdef, mul_one_div, div_lt_one (by positivity)]
    linarith
  have hce : c ≤ 1 / Real.exp 1 := by
    rw [hcdef, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [Real.exp_pos (1 : ℝ)]
  -- the scale page
  have hX1lb : X₁ ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hthlb : ballMertensThreshold ≤ Real.sqrt X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hsq4096 : Real.exp 4096 ≤ Real.sqrt X := le_trans (le_max_right _ _) hXlb
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXth : ballMertensThreshold ≤ X := le_trans hthlb hsqX
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hLhalf0 : (0 : ℝ) < Real.log X / 2 := by linarith
  have hXd2 : (2 : ℝ) ≤ Xd := by linarith [le_trans hsq4096 hsqXd]
  -- the datum facts (all datum-free interfaces of `ball_sup_of_center`)
  have hfle : ∀ n : ℕ, ‖seamCoeff F (fun _ => 1) t₀ n‖ ≤ 1 := norm_seamCoeff_trivial_le hFb t₀
  have hf1 : seamCoeff F (fun _ => 1) t₀ 1 = 1 := seamCoeff_one_eq_one hF1 t₀
  have hfmul : ∀ p q : ℕ, Nat.Coprime p q →
      seamCoeff F (fun _ => 1) t₀ (p * q)
        = seamCoeff F (fun _ => 1) t₀ p * seamCoeff F (fun _ => 1) t₀ q := by
    intro p q hpq
    by_cases hp : p = 0
    · subst hp
      have hq1 : q = 1 := Nat.coprime_zero_left q |>.mp hpq
      subst hq1
      simp [seamCoeff]
    · by_cases hq : q = 0
      · subst hq
        have hp1 : p = 1 := Nat.coprime_zero_right p |>.mp hpq
        subst hp1
        simp [seamCoeff]
      · have hmul := (seamCoeff_isMultiplicative hFm t₀).map_mul_of_coprime hpq
        have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp hq
        rwa [toAF_apply, toAF_apply, toAF_apply, if_neg hpq0, if_neg hp, if_neg hq] at hmul
  have hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
    refine hMball_of_A4_cap hXth ?_
    intro x h1 h2
    rw [← pretDistSq_twist_slot]
    exact hMcap x h1 h2
  -- the grade constant at the dilated scales
  set B : ℝ := gradeAbsConstC c Cb * Real.exp (-c * (M₀ - dilGap X Xd))
      + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) with hBdef
  have hgc0 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hrp0 : (0 : ℝ) ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg hLhalf0.le _
  have hB0 : (0 : ℝ) ≤ B := by
    have h1 := mul_nonneg hgc0 (Real.exp_nonneg (-c * (M₀ - dilGap X Xd)))
    have h2 := mul_nonneg farCStar_nonneg hrp0
    rw [hBdef]; linarith
  -- the window's scale gate
  have hk4096 : ∀ k : ℕ, Xd ≤ (k : ℝ) → Real.exp 4096 ≤ (k : ℝ) :=
    fun k h => le_trans (le_trans hsq4096 hsqXd) h
  have hLklo : ∀ k : ℕ, Xd ≤ (k : ℝ) → Real.log X / 2 ≤ Real.log (k : ℝ) := by
    intro k h
    have h1 : Real.log (Real.sqrt X) ≤ Real.log (k : ℝ) :=
      Real.log_le_log hsq0 (le_trans hsqXd h)
    rwa [Real.log_sqrt hX0.le] at h1
  -- §2 AT EVERY DILATED SCALE — the wide supply's `hRHS` binder
  have hRHSb : ∀ k : ℕ, Xd ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
      ‖prop21RHS (fun p => F p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          ((fun x => Real.log x ^ 4) (k : ℝ))
          (1 / Real.log ((fun x => Real.log x ^ 4) (k : ℝ)))‖
        ≤ B * (k : ℝ) := by
    intro k hk1 hk2
    have hkA := hk4096 k hk1
    have hk64 : Real.exp 64 ≤ (k : ℝ) :=
      le_trans (Real.exp_le_exp.mpr (by norm_num)) hkA
    have hkee : Real.exp (Real.exp 1) ≤ (k : ℝ) :=
      le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])) hkA
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hgate : |t₁| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ Rad := by
      have hmono := Tstar_mono hkee hk2
      linarith
    have hmain := dilated_scale_grade hgF (c := c) (Cb := Cb) (t₀ := t₀) (t₁ := t₁)
      (X := X) (Xd := Xd) (M₀ := M₀) (Rad := Rad) (k := k)
      hc0 hce hc1 hCb0 hCbound hk64 hXd2 hXdX hk1 hgate hM₀
    refine le_trans hmain ?_
    have hfarmono : Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
        ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      Real.rpow_le_rpow_of_nonpos hLhalf0 (hLklo k hk1)
        (neg_nonpos.mpr (by positivity))
    have hfk : farCStar * (k : ℝ) * Real.log (k : ℝ) ^ (-(1 / (32 * Real.exp 1)))
        ≤ farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      mul_le_mul_of_nonneg_left hfarmono (mul_nonneg farCStar_nonneg hk0)
    have hring : B * (k : ℝ)
        = gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd))
          + farCStar * (k : ℝ) * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) := by
      rw [hBdef]; ring
    rw [hring]
    linarith
  -- §1 AT EVERY DILATED SCALE
  have hSupplyAt := hsupply t₁ X Xd B hX1lb hsqXd hB0
    (fun k h _ => (ypin4_gates_hs (hk4096 k h)).1)
    (fun k h _ => (ypin4_gates_hs (hk4096 k h)).2.1)
    (fun k h _ => (ypin4_gates_hs (hk4096 k h)).2.2.1)
    (fun k h _ => (ypin4_gates_hs (hk4096 k h)).2.2.2)
    hRHSb
  -- §3: the dissected centre bound, i.e. `ball_sup_of_center`'s `hCenter`
  set S : ℝ := B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by
    have h1 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
      Real.rpow_nonneg (by linarith) _
    rw [hSdef]; linarith
  have hDR : (D : ℝ) ≤ X - 1 := by
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    nlinarith
  have hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, seamCoeff F (fun _ => 1) t₀ n * eIu (-t₁) n‖
        ≤ (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
    intro k hk1 hk2
    have hkX : X - 1 < (k : ℝ) := by
      have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
      linarith
    have hkN : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hk2) hN2
    have hDk : D ≤ k := by
      have hlt : (D : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast le_of_lt hlt
    refine hCenter_dissected hFm hFb t₀ t₁ hD hDk hS0 ?_
    intro d hd1 hdD
    have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hulow : Xd ≤ ((k / d : ℕ) : ℝ) := by
      refine le_natDiv_of_le_hs hd1 ?_
      rw [le_div_iff₀ hd0]
      have h1 : (Xd + 1) * (d : ℝ) ≤ (Xd + 1) * (D : ℝ) :=
        mul_le_mul_of_nonneg_left hdD' (by linarith)
      have h2 : (Xd + 1) * (D : ℝ) = (D : ℝ) * (Xd + 1) := by ring
      linarith
    have huup : ((k / d : ℕ) : ℝ) ≤ 2 * X := by
      have h1 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.div_le_self k d
      linarith
    exact hSupplyAt (k / d) hulow huup
  have hS₀ : (0 : ℝ) ≤ cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
    have h1 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
    have := mul_nonneg hcS hS0
    have := mul_nonneg hcS h1
    linarith
  exact ball_sup_of_center hX3 hXN hN2 hf1 hfmul hfle hS₀ hsupp hDatum hCenter hMball

/-! ## §3 — the consumer plug: `ThmA2Rows`' `hStation`, DERIVED -/

/-- **THE `hStation` BINDER, SUPPLIED** (`hStation_of_hoisted`).  The hoisted twin at
`T := X`, in the exact shape `ThmA2Rows.a2Rows_of_cap` carries as `hStation`:

  `∀ t₁, |t₁| ≤ X → ∀ t, seamT0 X ≤ |t| → |t| ≤ X → |t − t₁| ≤ seamRad X →
     ∀ m ≤ N, ‖spolyA a t m‖ ≤ Sb·m/(1 + |t − t₁|)`,

at any `Sb` dominating the station's grade `ballSupS X (cSq·(…) + cSq·D^{−1/4})`.

Two hypotheses are re-cut for the box; nothing else moves.  The recentring gate becomes
centre-free — `X + T*(2X, log 2X) ≤ Rad`, which with `|t₁| ≤ X` gives `_M_gen`'s
`|t₁| + T*(2X, log 2X) ≤ Rad` at every centre of the box.  And `hMcap` — THE T3 GAP —
stays a binder, now over the box.

**Exactly what remains carried**: `hMcap` over the box (the T3 gap, untouched by the
hoist); the `M₀` floor on `|v| ≤ Rad` (the D10 defect at `Rad`, `M_window_bridge_seam`
gives it on `|v| ≤ X`); the dissection gates `1 ≤ D`, `√X ≤ Xd ≤ X`, `D(Xd+1) ≤ X−1`; the
scale frame `X₀ ≤ √X`, `X ≤ N ≤ 2X`; `0 ≤ Cb` with `ShortIntervalDatum Cb`; `a`'s two
coefficient equations; and the grade gate at `Sb`.  What is GONE is the quantifier
obstruction: `X₀` here precedes the centre, so it may be discharged before the routing
witness is produced. -/
theorem hStation_of_hoisted {F : ℕ → ℂ}
    (hFm : (toArithmeticFunction F).IsMultiplicative) (hFb : ∀ n, ‖F n‖ ≤ 1) (t₀ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N D : ℕ) (Cb Xd M₀ Rad Sb : ℝ) (a : ℕ → ℂ),
        X₀ ≤ Real.sqrt X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ D → Real.sqrt X ≤ Xd → Xd ≤ X → (D : ℝ) * (Xd + 1) ≤ X - 1 →
        X + Tstar (2 * X) (Real.log (2 * X)) ≤ Rad →
        (∀ v : ℝ, |v| ≤ Rad →
          M₀ ≤ pretDistSq (seamCoeff (ellLin F) (fun _ => 1) t₀) (costwist v) X) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff F (fun _ => 1) t₀ n) →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff F (fun _ => 1) t₀) (costwist t₁) x
            ≤ 1 / 16 * Real.log (Real.log X)) →
        ballSupS X (cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
                * Real.exp (-(1 / (2 * Real.exp 1)) * (M₀ - dilGap X Xd))
              + farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
            + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) ≤ Sb →
        ∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, hst⟩ := seam_ball_leg_station_M_hoisted hFm hFb t₀
  refine ⟨X₀, hX₀0, ?_⟩
  intro X N D Cb Xd M₀ Rad Sb a hXlb hXN hN2 hCb0 hCbound hD hsqXd hXdX hDgate hRad hM₀
    hsupp hDatum hMcap hSb t₁ ht₁ t ht0 htT htb m hm
  have hgate : |t₁| + Tstar (2 * X) (Real.log (2 * X)) ≤ Rad := by linarith
  have hmain := hst t₁ X N D Cb Xd M₀ Rad X a hXlb hXN hN2 hCb0 hCbound hD hsqXd hXdX hDgate
    hgate hM₀ hsupp hDatum (hMcap t₁ ht₁) t ht0 htT htb m hm
  refine le_trans hmain ?_
  have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSb hm0)
    (inv_nonneg.mpr hd.le)
  simpa [div_eq_mul_inv] using h2


end Salt.MR
