/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ShiftTrivChar
import Salt.SW.ShiftVariants
import Salt.SW.LandauPage

/-!
# The SW rung, wave S6b — the per-character dispatcher

Design: `docs/blueprints/sw.md`, S6 row. This module assembles the landed S5 contour-shift bounds
(`psi1_contour_shift`, `psi1_contour_shift_exceptional`, `psi1_contour_shift_trivchar_full`) with
the S3/S3e zero-free machinery (`zero_free_region_all`, `zeta_zero_free_region`,
`landau_one_exceptional_at`) into the two S6c-facing per-character bounds:

* `psi1_char_bound` — for every primitive `χ ≠ 1`, either the clean bound
  `‖ψ₁(x,χ)‖ ≤ K₄ x² e^{-c₄√log x}` holds, or there is a simple real (quadratic) Landau zero `β₁`
  and `‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄ x² e^{-c₄√log x}`.
* `psi1_trivchar_bound` — the χ₀ companion `‖ψ₁(x,χ₀) − x²/2‖ ≤ K₄ x² e^{-c₄√log x}`.

Parameters (frozen S6 design): `L := log x`, `s := √L`, `T = e^s`, `σ₀ = 1 − a/s`, `w = a/(2s)`
with `a := c₀'/8`, `c₀' := min(min c₀ c₃)(1/3750)`, `c₄ := a/2`. The `q`-smallness hypothesis is
`log(q(T+4)) ≤ 2√log x`.

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no new
axioms, no `sorry`.
-/

open Complex DirichletCharacter Filter
open scoped Topology

namespace Salt.SW

/-! ## 1. The polynomial-vs-exp absorption lemma -/

/-- **Absorption.** For `s ≥ 1` and `β > 0`, `s² ≤ (27/β³)·exp(β s)`. Route: `exp(βs) =
(exp(βs/3))³ ≥ (1 + βs/3)³ ≥ (βs/3)³ = β³s³/27`, so `s³ ≤ (27/β³)exp(βs)`, and `s² ≤ s³`. -/
theorem sq_le_C_exp (β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : 1 ≤ s) :
    s ^ 2 ≤ 27 / β ^ 3 * Real.exp (β * s) := by
  have hs0 : 0 ≤ s := by linarith
  have hstep : (1 + β * s / 3) ≤ Real.exp (β * s / 3) := by
    have := Real.add_one_le_exp (β * s / 3); linarith
  have hnn : 0 ≤ 1 + β * s / 3 := by positivity
  have hcube : (1 + β * s / 3) ^ 3 ≤ (Real.exp (β * s / 3)) ^ 3 :=
    pow_le_pow_left₀ hnn hstep 3
  have hexp3 : (Real.exp (β * s / 3)) ^ 3 = Real.exp (β * s) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hlb : (β * s / 3) ^ 3 ≤ (1 + β * s / 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hchain : β ^ 3 * s ^ 3 / 27 ≤ Real.exp (β * s) := by
    have hEq : (β * s / 3) ^ 3 = β ^ 3 * s ^ 3 / 27 := by ring
    rw [← hEq]
    calc (β * s / 3) ^ 3 ≤ (1 + β * s / 3) ^ 3 := hlb
      _ ≤ (Real.exp (β * s / 3)) ^ 3 := hcube
      _ = Real.exp (β * s) := hexp3
  have hs3 : s ^ 3 ≤ 27 / β ^ 3 * Real.exp (β * s) := by
    have hβ3 : (0:ℝ) < β ^ 3 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hβ3]; nlinarith [hchain]
  nlinarith [hs3, hs, hs0]

/-! ## 2. The shared E-shape decay bound -/

/-- **The E-shape decay bound.** The explicit error `E` produced by all three S5 contour-shift
bounds (clean/exceptional/χ₀ — same shape modulo the edge constant `B`) is
`≤ K₄·x²·e^{-(a/2)√log x}` once `B ≤ Kb·log x` and the box parameters are set. This is the S6
arithmetic (`x^{c+1} = e·x²`, `x^{σ'+1} ≤ e^{-a√L}·x²`, `T = e^{√L}`, and the log-power absorption
`s²·e^{-γs} ≤ (216/a³)·e^{-(a/2)s}` for `γ ≥ a`). -/
theorem E_shape_bound {a Kb : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hKb : 0 < Kb) :
    ∃ K₄ : ℝ, 0 < K₄ ∧ ∀ {x T σ' B : ℝ}, 3 ≤ x →
      T = Real.exp (Real.sqrt (Real.log x)) →
      9 / 10 ≤ σ' → σ' ≤ 1 - a / Real.sqrt (Real.log x) → 0 ≤ B → B ≤ Kb * Real.log x →
      (1 / (2 * Real.pi)) *
        (2 * ((1 + 1 / Real.log x) - σ') * B * x ^ ((1 + 1 / Real.log x) + 1) / T ^ 2
          + B * x ^ (σ' + 1) * (Real.pi / σ')
          + (Real.log x + 1) * x ^ ((1 + 1 / Real.log x) + 1) * (2 / T))
        ≤ K₄ * x ^ 2 * Real.exp (-(a / 2 * Real.sqrt (Real.log x))) := by
  set C0 : ℝ := 216 / a ^ 3 with hC0def
  have hC0pos : 0 < C0 := by rw [hC0def]; positivity
  set e := Real.exp 1 with he
  have hepos : 0 < e := Real.exp_pos 1
  set M1 : ℝ := (11 / 5) * Kb * C0 * e with hM1
  set M2 : ℝ := (10 * Real.pi / 9) * Kb * C0 with hM2
  set M3 : ℝ := 4 * e * C0 with hM3
  refine ⟨(1 / (2 * Real.pi)) * (M1 + M2 + M3), by positivity, ?_⟩
  intro x T σ' B hx hT hσ'lo hσ'dec hB0 hBs
  have hxpos : 0 < x := by linarith
  have hlogx1 : (1:ℝ) < Real.log x := by
    have : Real.log (Real.exp 1) < Real.log x :=
      Real.log_lt_log (Real.exp_pos 1)
        (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
    rwa [Real.log_exp] at this
  set L := Real.log x with hL
  set s := Real.sqrt L with hs
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hL1
  have hss : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hab : ∀ γ : ℝ, a ≤ γ → s ^ 2 * Real.exp (-(γ * s)) ≤ C0 * Real.exp (-(a / 2 * s)) := by
    intro γ hγ
    have hC0e : s ^ 2 ≤ C0 * Real.exp (a / 2 * s) := by
      have h := sq_le_C_exp (a / 2) (by positivity) s hs1
      have heq : (27 : ℝ) / (a / 2) ^ 3 = C0 := by rw [hC0def, div_pow]; field_simp; ring
      rwa [heq] at h
    calc s ^ 2 * Real.exp (-(γ * s))
        ≤ (C0 * Real.exp (a / 2 * s)) * Real.exp (-(γ * s)) :=
          mul_le_mul_of_nonneg_right hC0e (Real.exp_pos _).le
      _ = C0 * Real.exp (a / 2 * s - γ * s) := by rw [mul_assoc, ← Real.exp_add]; congr 2
      _ ≤ C0 * Real.exp (-(a / 2 * s)) := by
          apply mul_le_mul_of_nonneg_left _ hC0pos.le
          exact Real.exp_le_exp.mpr (by nlinarith [hγ, hs1, ha])
  have hxc1 : x ^ ((1 + 1 / L) + 1) = e * x ^ 2 := by
    have hL0 : L ≠ 0 := by positivity
    rw [show (1 + 1 / L) + 1 = (2:ℝ) + 1 / L by ring, Real.rpow_add hxpos, Real.rpow_two]
    have hxL : x ^ (1 / L) = e := by rw [he, Real.rpow_def_of_pos hxpos, mul_one_div, div_self hL0]
    rw [hxL]; ring
  have hxσ : x ^ (σ' + 1) ≤ Real.exp (-(a * s)) * x ^ 2 := by
    have hsplit : x ^ (σ' + 1) = x ^ (2:ℝ) * x ^ (σ' - 1) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    have hx2 : x ^ (2:ℝ) = x ^ 2 := by rw [Real.rpow_two]
    have hexp : x ^ (σ' - 1) = Real.exp ((σ' - 1) * L) := by
      rw [Real.rpow_def_of_pos hxpos, ← hL]; congr 1; ring
    have hle : (σ' - 1) * L ≤ -(a * s) := by
      have h1 : σ' - 1 ≤ -(a / s) := by linarith [hσ'dec]
      have hstep : (σ' - 1) * L ≤ -(a / s) * L := mul_le_mul_of_nonneg_right h1 hLpos.le
      have heq : -(a / s) * L = -(a * s) := by rw [← hss]; field_simp
      linarith [hstep, heq.le, heq.ge]
    rw [hsplit, hx2, hexp, mul_comm (x^2) _]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (by positivity)
  have hT2 : T ^ 2 = Real.exp (2 * s) := by rw [hT, sq, ← Real.exp_add]; congr 1; ring
  have hc2 : (1 + 1 / L) - σ' ≤ 11 / 10 := by
    have : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
    linarith [hσ'lo]
  have hπσ : Real.pi / σ' ≤ 10 * Real.pi / 9 := by
    have hσ'pos : 0 < σ' := by linarith
    rw [div_le_div_iff₀ hσ'pos (by norm_num)]
    nlinarith [Real.pi_pos, hσ'lo]
  set W : ℝ := x ^ 2 * Real.exp (-(a / 2 * s)) with hW
  have hx2nn : (0:ℝ) ≤ x ^ 2 := by positivity
  have hP1 : 2 * ((1 + 1 / L) - σ') * B * x ^ ((1 + 1 / L) + 1) / T ^ 2 ≤ M1 * W := by
    rw [hxc1, hT2, div_eq_mul_inv, ← Real.exp_neg]
    have hprod : 2 * ((1 + 1 / L) - σ') * B ≤ (11 / 5) * (Kb * s ^ 2) := by
      have hb : B ≤ Kb * s ^ 2 := by rw [hss]; exact hBs
      calc 2 * ((1 + 1 / L) - σ') * B = 2 * (((1 + 1 / L) - σ') * B) := by ring
        _ ≤ 2 * ((11 / 10) * B) := by linarith [mul_le_mul_of_nonneg_right hc2 hB0]
        _ = (11 / 5) * B := by ring
        _ ≤ (11 / 5) * (Kb * s ^ 2) := by
            linarith [mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 11 / 5)]
    calc 2 * ((1 + 1 / L) - σ') * B * (e * x ^ 2) * Real.exp (-(2 * s))
        ≤ (11 / 5) * (Kb * s ^ 2) * (e * x ^ 2) * Real.exp (-(2 * s)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = (11 / 5) * Kb * e * x ^ 2 * (s ^ 2 * Real.exp (-(2 * s))) := by ring
      _ ≤ (11 / 5) * Kb * e * x ^ 2 * (C0 * Real.exp (-(a / 2 * s))) := by
          apply mul_le_mul_of_nonneg_left (hab 2 (by linarith)) (by positivity)
      _ = M1 * W := by rw [hM1, hW]; ring
  have hP2 : B * x ^ (σ' + 1) * (Real.pi / σ') ≤ M2 * W := by
    calc B * x ^ (σ' + 1) * (Real.pi / σ')
        ≤ (Kb * s ^ 2) * (Real.exp (-(a * s)) * x ^ 2) * (10 * Real.pi / 9) := by
          have hb : B ≤ Kb * s ^ 2 := by rw [hss]; exact hBs
          apply mul_le_mul (mul_le_mul hb hxσ (by positivity) (by positivity)) hπσ
            (by positivity) (by positivity)
      _ = (10 * Real.pi / 9) * Kb * x ^ 2 * (s ^ 2 * Real.exp (-(a * s))) := by ring
      _ ≤ (10 * Real.pi / 9) * Kb * x ^ 2 * (C0 * Real.exp (-(a / 2 * s))) := by
          apply mul_le_mul_of_nonneg_left (hab a (le_refl a)) (by positivity)
      _ = M2 * W := by rw [hM2, hW]; ring
  have hP3 : (L + 1) * x ^ ((1 + 1 / L) + 1) * (2 / T) ≤ M3 * W := by
    rw [hxc1, hT, div_eq_mul_inv, ← Real.exp_neg]
    have hs2 : L + 1 ≤ 2 * s ^ 2 := by rw [hss]; linarith [hL1]
    calc (L + 1) * (e * x ^ 2) * (2 * Real.exp (-s))
        ≤ (2 * s ^ 2) * (e * x ^ 2) * (2 * Real.exp (-s)) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs2 (by positivity))
            (by positivity)
      _ = 4 * e * x ^ 2 * (s ^ 2 * Real.exp (-(1 * s))) := by rw [one_mul]; ring
      _ ≤ 4 * e * x ^ 2 * (C0 * Real.exp (-(a / 2 * s))) := by
          apply mul_le_mul_of_nonneg_left (hab 1 ha1) (by positivity)
      _ = M3 * W := by rw [hM3, hW]; ring
  have hsum : (2 * ((1 + 1 / L) - σ') * B * x ^ ((1 + 1 / L) + 1) / T ^ 2
      + B * x ^ (σ' + 1) * (Real.pi / σ') + (L + 1) * x ^ ((1 + 1 / L) + 1) * (2 / T))
      ≤ (M1 + M2 + M3) * W := by
    have := add_le_add (add_le_add hP1 hP2) hP3; linarith [this]
  calc (1 / (2 * Real.pi)) *
        (2 * ((1 + 1 / L) - σ') * B * x ^ ((1 + 1 / L) + 1) / T ^ 2
          + B * x ^ (σ' + 1) * (Real.pi / σ') + (L + 1) * x ^ ((1 + 1 / L) + 1) * (2 / T))
      ≤ (1 / (2 * Real.pi)) * ((M1 + M2 + M3) * W) := by
        apply mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (2 * Real.pi)) * (M1 + M2 + M3) * x ^ 2 * Real.exp (-(a / 2 * s)) := by
        rw [hW]; ring

/-! ## 3. The edge-constant argument bounds `log(4 M) ≤ 9√log x` -/

/-- The primitive-character growth-log bound `log(4·5(4+T)√q(1+log q)) ≤ 9s` (`T = e^s`, `s ≥ 1`,
`log q ≤ 2s`), feeding the edge constant `B`. -/
theorem logL4_le (q : ℕ) {s T : ℝ} (hq1 : 1 ≤ q) (hs1 : 1 ≤ s) (hT : T = Real.exp s)
    (hlogq : Real.log (q : ℝ) ≤ 2 * s) :
    Real.log (4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) ≤ 9 * s := by
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  have hlogqnn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have hTpos : 0 < T := by rw [hT]; exact hexps
  have hT1 : 1 ≤ T := by
    rw [hT]; calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
                  _ ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
  have hb1 : 4 + T ≤ 5 * Real.exp s := by rw [hT]; nlinarith [hexps, hT1, hT]
  have hsqrtq : Real.sqrt (q : ℝ) ≤ Real.exp s := by
    have hqle : (q : ℝ) ≤ (Real.exp s) ^ 2 := by
      calc (q : ℝ) = Real.exp (Real.log (q : ℝ)) := (Real.exp_log hqpos).symm
        _ ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr hlogq
        _ = (Real.exp s) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
    calc Real.sqrt (q : ℝ) ≤ Real.sqrt ((Real.exp s) ^ 2) := Real.sqrt_le_sqrt hqle
      _ = Real.exp s := Real.sqrt_sq hexps.le
  have hb3 : 1 + Real.log (q : ℝ) ≤ 3 * s := by linarith [hlogq, hs1]
  have harg : 4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
      ≤ 300 * s * Real.exp (2 * s) := by
    have he2 : Real.exp s * Real.exp s = Real.exp (2 * s) := by rw [← Real.exp_add]; congr 1; ring
    calc 4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))
        ≤ 4 * (5 * (5 * Real.exp s) * Real.exp s * (3 * s)) := by gcongr
      _ = 300 * s * (Real.exp s * Real.exp s) := by ring
      _ = 300 * s * Real.exp (2 * s) := by rw [he2]
  have hargpos : 0 < 4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))) := by
    have h1 : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    have h2 : 0 < 4 + T := by linarith
    positivity
  calc Real.log (4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
      ≤ Real.log (300 * s * Real.exp (2 * s)) := Real.log_le_log hargpos harg
    _ = Real.log 300 + Real.log s + 2 * s := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
          Real.log_mul (by norm_num) (by linarith), Real.log_exp]
    _ ≤ 9 * s := by
        have h300 : Real.log 300 ≤ 6 := by
          rw [show (6:ℝ) = Real.log (Real.exp 6) from (Real.log_exp 6).symm]
          apply Real.log_le_log (by norm_num)
          have h27 : (2.7:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          have hp : (2.7:ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h27.le 6
          have hexp6 : Real.exp 6 = (Real.exp 1) ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
          rw [hexp6]; nlinarith [hp]
        have hlogs : Real.log s ≤ s := by
          have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < s); linarith
        nlinarith [h300, hlogs, hs1]

/-- The ζ growth-log bound `log(4·M0zeta T) ≤ 9s` (`T = e^s`, `s ≥ 1`), feeding the χ₀ edge
constant `B₀`. -/
theorem logM0_le {s T : ℝ} (hs1 : 1 ≤ s) (hT : T = Real.exp s) :
    Real.log (4 * M0zeta T) ≤ 9 * s := by
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have hTpos : 0 < T := by rw [hT]; exact hexps
  have h2es : (2:ℝ) ≤ Real.exp s :=
    le_trans (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) (Real.exp_le_exp.mpr hs1)
  have hM0eq : M0zeta T = 1 + 5 * (19 / 4 + T) * (15 / 4 + T) := by
    unfold M0zeta; rw [abs_of_pos hTpos]
  rw [hM0eq]
  have hes2 : (Real.exp s) ^ 2 = Real.exp (2 * s) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hb1 : 19 / 4 + T ≤ 5 * Real.exp s := by rw [hT]; nlinarith [h2es]
  have hb2 : 15 / 4 + T ≤ 5 * Real.exp s := by rw [hT]; nlinarith [h2es]
  have hprod : (19 / 4 + T) * (15 / 4 + T) ≤ 25 * (Real.exp s) ^ 2 := by
    nlinarith [mul_le_mul hb1 hb2 (by positivity) (by positivity), hexps]
  have harg : 4 * (1 + 5 * (19 / 4 + T) * (15 / 4 + T)) ≤ 504 * Real.exp (2 * s) := by
    rw [← hes2]; nlinarith [hprod, h2es]
  have hargpos : 0 < 4 * (1 + 5 * (19 / 4 + T) * (15 / 4 + T)) := by
    have : 0 < 19 / 4 + T := by linarith
    have : 0 < 15 / 4 + T := by linarith
    positivity
  calc Real.log (4 * (1 + 5 * (19 / 4 + T) * (15 / 4 + T)))
      ≤ Real.log (504 * Real.exp (2 * s)) := Real.log_le_log hargpos harg
    _ = Real.log 504 + 2 * s := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ 9 * s := by
        have h504 : Real.log 504 ≤ 7 := by
          rw [show (7:ℝ) = Real.log (Real.exp 7) from (Real.log_exp 7).symm]
          apply Real.log_le_log (by norm_num)
          have h27 : (2.7:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          have hp : (2.7:ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) h27.le 7
          have hexp7 : Real.exp 7 = (Real.exp 1) ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
          rw [hexp7]; nlinarith [hp]
        linarith [h504, hs1]

/-! ## 4. The per-character dispatcher -/

/-- **Off-window suppression.** A zero `ρ` of `L(·,χ)` (primitive `χ ≠ 1`) with `1/2 ≤ Re ρ`,
`|Im ρ| ≤ T+2`, that is either non-real or of a non-quadratic character (`χ²≠1 ∨ Im ρ ≠ 0`) is
pushed off the box: `Re ρ ≤ 1 − c₀/(2√log x)` (via `zero_free_region_all` at the `q`-smallness
`log(q(T+4)) ≤ 2s`). Used for the case-(iii) forcing and the exceptional carve-out. -/
theorem dispatch_zero_re_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c₀ s T : ℝ}
    (hc₀pos : 0 < c₀)
    (hc₀ : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
      ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hq1 : 1 ≤ q) (hspos : 0 < s) (hq : Real.log ((q : ℝ) * (T + 4)) ≤ 2 * s)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hρhalf : 1 / 2 ≤ ρ.re) (hρim : |ρ.im| ≤ T + 2)
    (hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) :
    ρ.re ≤ 1 - c₀ / (2 * s) := by
  have hqR1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  have hb := hc₀ hρ0 hρhalf hor
  have hlogρ : Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ 2 * s := by
    have hmono : Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log (by positivity)
      have : |ρ.im| + 2 ≤ T + 4 := by linarith [hρim]
      nlinarith [mul_le_mul_of_nonneg_left this hqpos.le]
    linarith [hmono, hq]
  have hlogρpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; nlinarith [hqR1, abs_nonneg ρ.im]
  have hc0div : c₀ / (2 * s) ≤ c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    rw [div_le_div_iff_of_pos_left hc₀pos (by positivity) hlogρpos]; exact hlogρ
  linarith [hb, hc0div]

set_option maxHeartbeats 4000000 in
-- The dispatcher threads two full S5 contour-shift assemblies (clean + exceptional), the E-shape
-- decay bound, the forcing/Landau argument and the adaptive box through one `set`-heavy proof; the
-- elaborator needs headroom past the default to check it in a single pass.
/-- **S6b — the per-character dispatcher (primitive `χ ≠ 1`).** For every primitive Dirichlet
character `χ ≠ 1` mod `q`, at `T = e^{√log x}` with the `q`-smallness `log(q(T+4)) ≤ 2√log x`,
either the clean bound `‖ψ₁(x,χ)‖ ≤ K₄·x²·e^{-c₄√log x}` holds (no exceptional zero in the box),
or there is a simple real quadratic Landau zero `β₁ ∈ [9/10, 1)` and
`‖ψ₁(x,χ) + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄·x²·e^{-c₄√log x}`. Constants
`c₄ = c₀'/16`, `c₀' = min(min c₀ c₃)(1/3750)` (`c₀` from `zero_free_region_all`, `c₃` from
`zeta_zero_free_region`). -/
theorem psi1_char_bound :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∀ {x T : ℝ}, 3 ≤ x → T = Real.exp (Real.sqrt (Real.log x)) →
          Real.log ((q : ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) →
          (‖psi1Chi x χ‖ ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))))
          ∨ (∃ β₁ : ℝ, LFunction χ (β₁ : ℂ) = 0 ∧
              analyticOrderAt (LFunction χ) (β₁ : ℂ) = 1 ∧ χ ^ 2 = 1 ∧
              (9 / 10 ≤ β₁ ∧ β₁ < 1) ∧
              1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₁ ∧
              ‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
                ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x)))) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := zero_free_region_all
  obtain ⟨c₃, hc₃pos, _hc₃⟩ := zeta_zero_free_region
  set c₀' : ℝ := min (min c₀ c₃) (1 / 3750) with hc₀'def
  have hc₀'pos : 0 < c₀' := lt_min (lt_min hc₀pos hc₃pos) (by norm_num)
  have hc₀'c₀ : c₀' ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₀'3750 : c₀' ≤ 1 / 3750 := min_le_right _ _
  set a : ℝ := c₀' / 8 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have ha30000 : a ≤ 1 / 30000 := by rw [hadef]; linarith [hc₀'3750]
  have ha1 : a ≤ 1 := by linarith [ha30000]
  set Kb : ℝ := 1080 + 18 / (a * Real.log (7 / 6)) with hKbdef
  have hlog76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hden : 0 < a * Real.log (7 / 6) := by positivity
  have hKbpos : 0 < Kb := by rw [hKbdef]; positivity
  obtain ⟨K₄, hK₄pos, hE⟩ := E_shape_bound ha ha1 hKbpos
  refine ⟨a / 2, K₄, by positivity, hK₄pos, ?_⟩
  intro q iq χ hχprim hχ1 x T hx hT hq
  -- basic x facts
  have hxpos : 0 < x := by linarith
  have hlogx1 : (1:ℝ) < Real.log x := by
    have : Real.log (Real.exp 1) < Real.log x :=
      Real.log_lt_log (Real.exp_pos 1)
        (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
    rwa [Real.log_exp] at this
  set L := Real.log x with hL
  set s := Real.sqrt L with hs
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hL1
  have hss : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hsL : s ≤ L := by rw [← hss]; nlinarith [hs1]
  have hT_eq : T = Real.exp s := hT
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have hTpos : 0 < T := by rw [hT_eq]; exact hexps
  have hTge2 : (2:ℝ) ≤ T := by
    rw [hT_eq]
    exact le_trans (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) (Real.exp_le_exp.mpr hs1)
  -- q ≥ 2, q ≥ 1
  have hq2 : 2 ≤ q := by
    have hcond : χ.conductor = q := hχprim
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1; have := NeZero.ne q; omega
  have hq1 : 1 ≤ q := by omega
  have hqR1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  -- parameters σ₀, w with the linear-in-w key relations
  set w : ℝ := a / (2 * s) with hwdef
  set σ₀ : ℝ := 1 - a / s with hσ₀def
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have h2w : 2 * w = a / s := by rw [hwdef]; field_simp
  have h2ws : 2 * w * s = a := by rw [hwdef]; field_simp
  have hasa : a / s ≤ a := div_le_self ha.le hs1
  have hw_bound : w ≤ 1 / 60000 := by nlinarith [h2w, hasa, ha30000]
  have hσ₀_2w : σ₀ = 1 - 2 * w := by rw [hσ₀def, ← h2w]
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀_2w]; linarith [hwpos]
  have hσ₀lo : 9 / 10 ≤ σ₀ := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀w : 9 / 10 ≤ σ₀ - w := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀dec : σ₀ ≤ 1 - a / s := le_of_eq hσ₀def
  -- log q ≤ 2s
  have hlogq : Real.log (q : ℝ) ≤ 2 * s := by
    have hmono : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log hqpos
      nlinarith [mul_nonneg hqpos.le (show (0:ℝ) ≤ T + 3 by linarith)]
    linarith [hmono, hq]
  -- the edge constant B
  set L4 : ℝ := Real.log (4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
    with hL4def
  have hL4_9s : L4 ≤ 9 * s := logL4_le q hq1 hs1 hT_eq hlogq
  have hL4nn : 0 ≤ L4 := by
    rw [hL4def]; apply Real.log_nonneg
    have hp1 : (4:ℝ) ≤ 4 + T := by linarith [hTpos]
    have hsq1 : (1:ℝ) ≤ Real.sqrt (q : ℝ) := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hqR1
    have hlq : (1:ℝ) ≤ 1 + Real.log (q : ℝ) := by linarith [Real.log_nonneg hqR1]
    have h1 : (4:ℝ) ≤ (4 + T) * Real.sqrt (q : ℝ) := by
      calc (4:ℝ) = 4 * 1 := by ring
        _ ≤ (4 + T) * Real.sqrt (q : ℝ) := mul_le_mul hp1 hsq1 (by norm_num) (by linarith [hp1])
    have step : (1:ℝ) ≤ (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      calc (1:ℝ) ≤ 4 * 1 := by norm_num
        _ ≤ (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) :=
            mul_le_mul h1 hlq (by norm_num) (by linarith [h1])
    nlinarith [step]
  set Bexpr : ℝ := 120 * L4 + L4 / Real.log (7 / 6) / w with hBexprdef
  have hB0 : 0 ≤ Bexpr := by rw [hBexprdef]; positivity
  have hBs : Bexpr ≤ Kb * L := by
    have hBform : Bexpr = 120 * L4 + 2 * s * L4 / (a * Real.log (7 / 6)) := by
      rw [hBexprdef, hwdef]; field_simp
    have hnum : 2 * s * L4 ≤ 18 * L := by rw [← hss]; nlinarith [hL4_9s, hs1, hL4nn]
    have hd2 : 2 * s * L4 / (a * Real.log (7 / 6)) ≤ 18 * L / (a * Real.log (7 / 6)) := by
      rw [div_le_div_iff_of_pos_right hden]; exact hnum
    have ht1 : 120 * L4 ≤ 1080 * L := by nlinarith [hL4_9s, hsL, hL4nn]
    rw [hBform, hKbdef]
    have hsplit : (1080 + 18 / (a * Real.log (7 / 6))) * L
        = 1080 * L + 18 * L / (a * Real.log (7 / 6)) := by field_simp
    rw [hsplit]; linarith [ht1, hd2]
  -- the case split on whether L(χ) has a zero in the box
  by_cases hbox : ∃ ρ : ℂ, LFunction χ ρ = 0 ∧ σ₀ - w ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T + 2
  · -- case (iii): exceptional zero
    obtain ⟨ρ₀, hρ₀0, hρ₀re1, hρ₀re2, hρ₀im⟩ := hbox
    have hρ₀half : 1 / 2 ≤ ρ₀.re := by linarith [hρ₀re1, hσ₀w]
    -- forcing: χ² = 1 and ρ₀ real
    have hforce : χ ^ 2 = 1 ∧ ρ₀.im = 0 := by
      by_contra hcon
      have hor : χ ^ 2 ≠ 1 ∨ ρ₀.im ≠ 0 := by
        rcases not_and_or.mp hcon with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hb2 : ρ₀.re ≤ 1 - c₀ / (2 * s) :=
        dispatch_zero_re_le χ hc₀pos (hc₀ q χ hχprim hχ1) hq1 hspos hq hρ₀0 hρ₀half hρ₀im hor
      have hc0_3a : 3 * a < c₀ := by rw [hadef]; nlinarith [hc₀'c₀, hc₀pos]
      have h3ac : 3 * a / (2 * s) < c₀ / (2 * s) := by
        rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * s)]; exact hc0_3a
      have hσ₀wval : σ₀ - w = 1 - 3 * a / (2 * s) := by
        rw [hσ₀def, hwdef]; ring
      linarith [hρ₀re1, hb2, hσ₀wval, h3ac]
    obtain ⟨hsq, hρ₀im0⟩ := hforce
    set β₁ : ℝ := ρ₀.re with hβ₁def
    have hρ₀eq : ρ₀ = (β₁ : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]; exact hρ₀im0
    have hz : LFunction χ (β₁ : ℂ) = 0 := hρ₀eq ▸ hρ₀0
    have hβ1lt : β₁ < 1 := by
      by_contra hc
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
        (by rw [Complex.ofReal_re]; exact not_lt.mp hc) hz
    have hβ90 : 9 / 10 ≤ β₁ := by linarith [hρ₀re1, hσ₀w]
    -- Landau window for β₁
    have hlog4q : 0 < Real.log (4 * (q : ℝ)) := by apply Real.log_pos; nlinarith [hqR1]
    have hlog4q_le : Real.log (4 * (q : ℝ)) ≤ 2 * s := by
      have hmono : Real.log (4 * (q : ℝ)) ≤ Real.log ((q : ℝ) * (T + 4)) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_nonneg hqpos.le hTpos.le]
      linarith [hmono, hq]
    have hβ1_ge : 1 - 3 * w ≤ β₁ := by
      have hσ₀wval : σ₀ - w = 1 - 3 * w := by rw [hσ₀_2w]; ring
      linarith [hρ₀re1, hσ₀wval]
    have hβwin : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₁ := by
      have hkey : 3 * w ≤ (1 / 5000) / Real.log (4 * (q : ℝ)) := by
        rw [le_div_iff₀ hlog4q]
        nlinarith [mul_le_mul_of_nonneg_left hlog4q_le (show (0:ℝ) ≤ 3 * w by positivity),
          h2ws, ha30000, hspos, hwpos]
      linarith [hβ1_ge, hkey]
    have hsimple : analyticOrderAt (LFunction χ) (β₁ : ℂ) = 1 :=
      (landau_one_exceptional_at hχprim hχ1 hz hz hβwin hβwin).2
    -- the adaptive box
    set σ₀'' : ℝ := min σ₀ (β₁ - 2 * w) with hσ''def
    have hσ''le : σ₀'' ≤ σ₀ := min_le_left _ _
    have hσ''le2 : σ₀'' ≤ β₁ - 2 * w := min_le_right _ _
    have hσ''βsep : σ₀'' + w ≤ β₁ := by linarith [hσ''le2, hwpos]
    have hσ''dec : σ₀'' ≤ 1 - a / s := le_trans hσ''le hσ₀dec
    have hσ''1 : σ₀'' < 1 := lt_of_le_of_lt hσ''le hσ₀1
    have hσ''w : 9 / 10 ≤ σ₀'' - w := by
      have hA : 9 / 10 + w ≤ σ₀ := by rw [hσ₀_2w]; linarith [hw_bound]
      have hB : 9 / 10 + w ≤ β₁ - 2 * w := by linarith [hβ1_ge, hw_bound]
      have := le_min hA hB; rw [hσ''def]; linarith [this]
    have hσ''lo : 9 / 10 ≤ σ₀'' := by linarith [hσ''w, hwpos]
    -- hzf for the exceptional variant: every box zero equals β₁
    have hzfexc : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀'' - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
        ρ = (β₁ : ℂ) := by
      intro ρ hρ0 hρre1 _hρre2 hρim
      have hρhalf : 1 / 2 ≤ ρ.re := by linarith [hρre1, hσ''w]
      have hσ''w_ge : 1 - 6 * w ≤ σ₀'' - w := by
        have hA : 1 - 6 * w + w ≤ σ₀ := by rw [hσ₀_2w]; linarith
        have hB : 1 - 6 * w + w ≤ β₁ - 2 * w := by linarith [hβ1_ge]
        have := le_min hA hB; rw [hσ''def]; linarith [this]
      have hρim0 : ρ.im = 0 := by
        by_contra hne
        have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := Or.inr hne
        have hb2 : ρ.re ≤ 1 - c₀ / (2 * s) :=
          dispatch_zero_re_le χ hc₀pos (hc₀ q χ hχprim hχ1) hq1 hspos hq hρ0 hρhalf hρim hor
        have hc0_6a : 6 * a < c₀ := by rw [hadef]; nlinarith [hc₀'c₀, hc₀pos]
        have h6as : 6 * w < c₀ / (2 * s) := by
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * s)]; nlinarith [hc0_6a, h2ws]
        linarith [hρre1, hb2, hσ''w_ge, h6as]
      have hρeq : ρ = (ρ.re : ℂ) := by
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]; exact hρim0
      have hzρ : LFunction χ (ρ.re : ℂ) = 0 := hρeq ▸ hρ0
      have hρwin : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ ρ.re := by
        have hρ_ge : 1 - 6 * w ≤ ρ.re := by linarith [hρre1, hσ''w_ge]
        have hkey : 6 * w ≤ (1 / 5000) / Real.log (4 * (q : ℝ)) := by
          rw [le_div_iff₀ hlog4q]
          nlinarith [mul_le_mul_of_nonneg_left hlog4q_le (show (0:ℝ) ≤ 6 * w by positivity),
            h2ws, ha30000, hspos, hwpos]
        linarith [hρ_ge, hkey]
      have heqβ : ρ.re = β₁ := (landau_one_exceptional_at hχprim hχ1 hzρ hz hρwin hβwin).1
      rw [hρeq, heqβ]
    -- assemble the exceptional bound
    refine Or.inr ⟨β₁, hz, hsimple, hsq, ⟨hβ90, hβ1lt⟩, hβwin, ?_⟩
    exact le_trans
      (psi1_contour_shift_exceptional χ hχprim hq2 hx hTge2 hwpos hσ''w hσ''1 hσ''βsep hβ1lt
        hsimple hzfexc)
      (hE hx hT hσ''lo hσ''dec hB0 hBs)
  · -- case (ii): clean
    have hzf : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False :=
      fun ρ h1 h2 h3 h4 => hbox ⟨ρ, h1, h2, h3, h4⟩
    refine Or.inl (le_trans (psi1_contour_shift χ hχprim hq2 hx hTge2 hwpos hσ₀w hσ₀1 hzf) ?_)
    exact hE hx hT hσ₀lo hσ₀dec hB0 hBs

/-! ## 5. The χ₀ (trivial character) companion -/

/-- **ζ off-window suppression.** A zero `ρ` of `ζ` with `1/2 ≤ Re ρ`, `|Im ρ| ≤ T+2` has
`Re ρ ≤ 1 − c₃/(2√log x)` (via `zeta_zero_free_region` at `log(q(T+4)) ≤ 2s`, `q ≥ 1`). -/
theorem dispatch_zeta_re_le {c₃ s T : ℝ} (hc₃pos : 0 < c₃)
    (hc₃ : ∀ {ρ : ℂ}, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 - c₃ / Real.log (|ρ.im| + 2))
    (q : ℕ) (hq1 : 1 ≤ q) (hspos : 0 < s) (hq : Real.log ((q : ℝ) * (T + 4)) ≤ 2 * s)
    {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hρhalf : 1 / 2 ≤ ρ.re) (hρim : |ρ.im| ≤ T + 2) :
    ρ.re ≤ 1 - c₃ / (2 * s) := by
  have hqR1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hb := hc₃ hρ0 hρhalf
  have himnn : (0:ℝ) ≤ |ρ.im| := abs_nonneg _
  have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * s := by
    have hmono : Real.log (|ρ.im| + 2) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log (by positivity)
      have hle1 : |ρ.im| + 2 ≤ T + 4 := by linarith [hρim]
      have hqm1 : (0:ℝ) ≤ (q : ℝ) - 1 := by linarith
      have hT4 : (0:ℝ) ≤ T + 4 := by linarith
      nlinarith [hle1, mul_nonneg hqm1 hT4]
    linarith [hmono, hq]
  have hlogρpos : 0 < Real.log (|ρ.im| + 2) := by apply Real.log_pos; linarith
  have hc3div : c₃ / (2 * s) ≤ c₃ / Real.log (|ρ.im| + 2) := by
    rw [div_le_div_iff_of_pos_left hc₃pos (by positivity) hlogρpos]; exact hlogρ
  linarith [hb, hc3div]

set_option maxHeartbeats 4000000 in
-- The companion threads the S5d χ₀ contour-shift assembly, the E-shape decay bound and the ζ
-- zero-free discharge through one `set`-heavy proof; it needs headroom past the default.
/-- **S6b — the χ₀ companion.** For the trivial character `χ₀ = 1 mod q`, at `T = e^{√log x}`
with `log(q(T+4)) ≤ 2√log x`, `‖ψ₁(x,χ₀) − x²/2‖ ≤ K₄·x²·e^{-c₄√log x}` (same shape as
`psi1_char_bound`, main-term `x²/2` subtracted). The ζ zero-free region (`c₃`) discharges the box
non-vanishing; no exceptional zero (ζ has none in the region). -/
theorem psi1_trivchar_bound :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
      ∀ (q : ℕ) [NeZero q], ∀ {x T : ℝ}, 3 ≤ x → T = Real.exp (Real.sqrt (Real.log x)) →
        Real.log ((q : ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) →
        ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x : ℂ) ^ 2 / 2‖
          ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))) := by
  obtain ⟨c₀, hc₀pos, _hc₀⟩ := zero_free_region_all
  obtain ⟨c₃, hc₃pos, hc₃⟩ := zeta_zero_free_region
  set c₀' : ℝ := min (min c₀ c₃) (1 / 3750) with hc₀'def
  have hc₀'pos : 0 < c₀' := lt_min (lt_min hc₀pos hc₃pos) (by norm_num)
  have hc₀'c₃ : c₀' ≤ c₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc₀'3750 : c₀' ≤ 1 / 3750 := min_le_right _ _
  set a : ℝ := c₀' / 8 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have ha30000 : a ≤ 1 / 30000 := by rw [hadef]; linarith [hc₀'3750]
  have ha1 : a ≤ 1 := by linarith [ha30000]
  have hlog76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hden : 0 < a * Real.log (7 / 6) := by positivity
  set Kb₀ : ℝ := 1080 + 18 / (a * Real.log (7 / 6)) + 4 + 2 / a with hKb₀def
  have hKb₀pos : 0 < Kb₀ := by rw [hKb₀def]; positivity
  obtain ⟨K₄, hK₄pos, hE⟩ := E_shape_bound ha ha1 hKb₀pos
  refine ⟨a / 2, K₄, by positivity, hK₄pos, ?_⟩
  intro q iq x T hx hT hq
  have hxpos : 0 < x := by linarith
  have hlogx1 : (1:ℝ) < Real.log x := by
    have : Real.log (Real.exp 1) < Real.log x :=
      Real.log_lt_log (Real.exp_pos 1)
        (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
    rwa [Real.log_exp] at this
  set L := Real.log x with hL
  set s := Real.sqrt L with hs
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hL1
  have hss : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hsL : s ≤ L := by rw [← hss]; nlinarith [hs1]
  have hT_eq : T = Real.exp s := hT
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have hTpos : 0 < T := by rw [hT_eq]; exact hexps
  have hTge2 : (2:ℝ) ≤ T := by
    rw [hT_eq]
    exact le_trans (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) (Real.exp_le_exp.mpr hs1)
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqR1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  -- parameters
  set w : ℝ := a / (2 * s) with hwdef
  set σ₀ : ℝ := 1 - a / s with hσ₀def
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have h2w : 2 * w = a / s := by rw [hwdef]; field_simp
  have hasa : a / s ≤ a := div_le_self ha.le hs1
  have hw_bound : w ≤ 1 / 60000 := by nlinarith [h2w, hasa, ha30000]
  have hσ₀_2w : σ₀ = 1 - 2 * w := by rw [hσ₀def, ← h2w]
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀_2w]; linarith [hwpos]
  have hσ₀lo : 9 / 10 ≤ σ₀ := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀w : 9 / 10 ≤ σ₀ - w := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀dec : σ₀ ≤ 1 - a / s := le_of_eq hσ₀def
  have hσ₀w1 : σ₀ + w ≤ 1 := by rw [hσ₀_2w]; linarith [hwpos]
  -- log q ≤ 2s
  have hlogq : Real.log (q : ℝ) ≤ 2 * s := by
    have hmono : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log hqpos
      nlinarith [mul_nonneg hqpos.le (show (0:ℝ) ≤ T + 3 by linarith)]
    linarith [hmono, hq]
  -- discharge hzfζ
  have hzfζ : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False := by
    intro ρ hρ0 hρre1 _hρre2 hρim
    have hρhalf : 1 / 2 ≤ ρ.re := by linarith [hρre1, hσ₀w]
    have hb2 := dispatch_zeta_re_le hc₃pos hc₃ q hq1 hspos hq hρ0 hρhalf hρim
    have hc3_3a : 3 * a < c₃ := by rw [hadef]; nlinarith [hc₀'c₃, hc₃pos]
    have h3ac : 3 * a / (2 * s) < c₃ / (2 * s) := by
      rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * s)]; exact hc3_3a
    have hσ₀wval : σ₀ - w = 1 - 3 * a / (2 * s) := by rw [hσ₀def, hwdef]; ring
    linarith [hρre1, hb2, hσ₀wval, h3ac]
  -- edge constant B₀
  set L0 : ℝ := Real.log (4 * M0zeta T) with hL0def
  have hL0_9s : L0 ≤ 9 * s := logM0_le hs1 hT_eq
  have hL0nn : 0 ≤ L0 := by
    rw [hL0def]; apply Real.log_nonneg
    have : (1:ℝ) ≤ M0zeta T := one_le_M0zeta T
    linarith
  set B0 : ℝ := 120 * L0 + L0 / Real.log (7 / 6) / w + 2 * Real.log (q : ℝ) + 1 / w with hB0def
  have hB0nn : 0 ≤ B0 := by
    rw [hB0def]
    have hlq : (0:ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hqR1
    positivity
  have hB0s : B0 ≤ Kb₀ * L := by
    have hB0form : B0 = 120 * L0 + 2 * s * L0 / (a * Real.log (7 / 6)) + 2 * Real.log (q : ℝ)
        + 2 * s / a := by rw [hB0def, hwdef]; field_simp
    have ht1 : 120 * L0 ≤ 1080 * L := by nlinarith [hL0_9s, hsL, hL0nn]
    have ht2 : 2 * s * L0 / (a * Real.log (7 / 6)) ≤ 18 * L / (a * Real.log (7 / 6)) := by
      rw [div_le_div_iff_of_pos_right hden]; rw [← hss]; nlinarith [hL0_9s, hs1, hL0nn]
    have ht3 : 2 * Real.log (q : ℝ) ≤ 4 * L := by nlinarith [hlogq, hsL, Real.log_nonneg hqR1]
    have ht4 : 2 * s / a ≤ 2 * L / a := by
      rw [div_le_div_iff_of_pos_right ha]; linarith [hsL]
    rw [hB0form, hKb₀def]
    have hsplit : (1080 + 18 / (a * Real.log (7 / 6)) + 4 + 2 / a) * L
        = 1080 * L + 18 * L / (a * Real.log (7 / 6)) + 4 * L + 2 * L / a := by field_simp
    rw [hsplit]; linarith [ht1, ht2, ht3, ht4]
  exact le_trans
    (psi1_contour_shift_trivchar_full q hx hTge2 hwpos hσ₀w hσ₀1 hσ₀w1 hzfζ)
    (hE hx hT hσ₀lo hσ₀dec hB0nn hB0s)

end Salt.SW
