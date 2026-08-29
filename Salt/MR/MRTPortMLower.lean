/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTQualityLam
import Salt.MR.MRTPortA1

/-!
# The MRT port (item 15) — the λ-quality floor at `lamCoeff` (node E3)

Dispatched from the frozen executor brief
`2026-08-25-item15-WAVE-B-ARC-OUT-OF-SCOPE-FROZEN.md`, node **E3**.  The
three statements below are the **door-wave gate's own**, copied verbatim from that
brief; they are not the maestro's or this executor's paraphrase.

| decl | content |
|---|---|
| `mrtM_lamCoeff_lower` | the landed λ-quality bound, transported to the `lamCoeff` spelling |
| `mrtM_lamCoeff_loglog_floor` | the honest correction term absorbed: `(1/8)·loglog X ≤ M(λ; X)` |
| `mrtM_lamCoeff_ge` | the same floor read as "eventually above any constant" |

The landed supply is `mrtM_lam_lower` (`MRTQualityLam.lean:75`), unconditional and
effective, in the shape

  `M(λ; X) ≥ (1/4)·loglog X − 4·logloglog(X + 16) − C`   (`X ≥ x0`),

and `mrtM_lam_eq_lamCoeff` (`MRTPortA1.lean:54`, node D2) moves it from the `lam`
spelling to `lamCoeff`.  What this file adds is the **absorption**: the correction
`4·logloglog(X + 16) + C` is `o(loglog X)`, so half the main term swallows it past an
explicit threshold.

## The absorption route (deliberately `rpow`-free)

The brief's proposed route went through `Real.log_le_rpow_div` at `ε = 1/2` and a
square-root `nlinarith`.  That step is not needed: the crude **linear** page

  `log t ≤ log a + t/a − 1`   (any `a > 0`, from `log s ≤ s − 1` at `s = t/a`)

is already enough, because the coefficient in front of the triple logarithm is a
constant `4` while the main term carries `1/8` of a *single* `loglog`.  At `a = 128`
the transported correction costs `L/32`, and `1/8 − 1/32 = 3/32 > 0` leaves room for
every additive constant.  So the chain is

  `logloglog(X + 16) ≤ log(log 2 + L) ≤ log 128 + (log 2 + L)/128 − 1`,  `L := loglog X`,

whose first step is `X + 16 ≤ X²` (valid for `X ≥ 16`) followed by two applications of
`Real.log_le_log`.  Everything below is `linarith` over the atoms `log 128`, `log 2`,
`L`, `logloglog(X + 16)` — no `rpow`, no `Real.sqrt`, no `nlinarith` on the main line.

⚠️ The `+ 16` shift is inherited from `lambda_nonpret` and is load-bearing in the same
way it is in `MRTQualityLam.log3_shift_mono`: it keeps `log(X + 16) > 1`, hence
`loglog(X + 16) > 0`, which is the positivity the second `Real.log_le_log` needs.

⛔ **SCOPE.**  `mrtM_lam_lower` is unconditional, so all three statements below are
unconditional.  They say nothing about MRT Theorem A.1 itself: `MRTThmA1` is still a
`def … : Prop` with no producer (GAP A.1), and nothing here touches the major arc
(GAP α).  This file supplies a *hypothesis slot*, it does not close a gap.

**Not rooted.**  This module is imported by nothing; build it targeted.  Rooting it in
`Salt/MR/All.lean` is maestro-tier.
-/

namespace Salt.MR

/-! ## The elementary linear page for `Real.log` -/

/-- **`log t ≤ log 128 + t/128 − 1`** for `t > 0`.

`Real.log_le_sub_one_of_pos` at `t/128`, then `Real.log_div`.  The base `128` is the
only choice that matters: it fixes the transported slope at `4/128 = 1/32`, which must
stay strictly below the `1/8` of the floor being proved. -/
theorem log_le_div_add_const_128 {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ Real.log 128 + t / 128 - 1 := by
  have hd : (0 : ℝ) < t / 128 := by positivity
  have h1 : Real.log (t / 128) ≤ t / 128 - 1 := Real.log_le_sub_one_of_pos hd
  have h2 : Real.log (t / 128) = Real.log t - Real.log 128 :=
    Real.log_div (ne_of_gt ht) (by norm_num)
  rw [h2] at h1
  linarith

/-- **The shifted triple logarithm, priced linearly in `loglog X`.**  For `X ≥ 16`,

  `logloglog(X + 16) ≤ log 128 + (log 2 + loglog X)/128 − 1`.

Route: `X + 16 ≤ X²` gives `log(X + 16) ≤ 2·log X`; `Real.log_le_log` twice pushes that
through to `logloglog(X + 16) ≤ log(log 2 + loglog X)`; then the linear page above.  The
positivity side conditions are all supplied by `X ≥ 16 > e`. -/
theorem log3_shift_le_linear {X : ℝ} (hX : (16 : ℝ) ≤ X) :
    Real.log (Real.log (Real.log (X + 16)))
      ≤ Real.log 128 + (Real.log 2 + Real.log (Real.log X)) / 128 - 1 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 : (0 : ℝ) < X + 16 := by linarith
  -- `X ≥ 16 > e`, so both `log X` and `log (X + 16)` exceed `1`.
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlogX1 : (1 : ℝ) < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hX0]; linarith
  have hlogX0 : (0 : ℝ) < Real.log X := by linarith
  have hs1 : (1 : ℝ) < Real.log (X + 16) := by
    rw [Real.lt_log_iff_exp_lt hs0]; linarith
  have hs1' : (0 : ℝ) < Real.log (X + 16) := by linarith
  -- step A : `log (X + 16) ≤ 2 · log X`
  have hsq : X + 16 ≤ X * X := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X - 16) (by linarith : (0 : ℝ) ≤ X)]
  have hA : Real.log (X + 16) ≤ 2 * Real.log X := by
    have h1 : Real.log (X + 16) ≤ Real.log (X * X) := Real.log_le_log hs0 hsq
    rw [Real.log_mul (ne_of_gt hX0) (ne_of_gt hX0)] at h1
    linarith
  -- step B : `loglog (X + 16) ≤ log 2 + loglog X`
  have hB : Real.log (Real.log (X + 16)) ≤ Real.log 2 + Real.log (Real.log X) := by
    have h1 : Real.log (Real.log (X + 16)) ≤ Real.log (2 * Real.log X) :=
      Real.log_le_log hs1' hA
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogX0)] at h1
  -- step C : one more `Real.log_le_log`, off `loglog (X + 16) > 0`
  have hC0 : (0 : ℝ) < Real.log (Real.log (X + 16)) := Real.log_pos hs1
  have hC : Real.log (Real.log (Real.log (X + 16)))
      ≤ Real.log (Real.log 2 + Real.log (Real.log X)) := Real.log_le_log hC0 hB
  -- step D : the linear page
  have hL0 : (0 : ℝ) < Real.log (Real.log X) := Real.log_pos hlogX1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hD := log_le_div_add_const_128
    (t := Real.log 2 + Real.log (Real.log X)) (by linarith)
  linarith

/-! ## E3 — the quality floor at `lamCoeff` -/

/-- **E3 (1) — the landed λ-quality lower bound, transported to `lamCoeff`.**

One rewrite.  `mrtM_lam_lower` (`MRTQualityLam.lean:75`) is unconditional — it rides
`lambda_nonpret` (`NonPretClose.lean:49`), which carries no hypothesis binder — and
`mrtM_lam_eq_lamCoeff` (`MRTPortA1.lean:54`, node D2) is the spelling transport.  This
is the first consumer of D2. -/
theorem mrtM_lamCoeff_lower :
    ∃ x0 C : ℝ, ∀ X : ℝ, x0 ≤ X →
      (1 / 4) * Real.log (Real.log X)
          - 4 * Real.log (Real.log (Real.log (X + 16))) - C
        ≤ mrtM lamCoeff X := by
  obtain ⟨x0, C, h⟩ := mrtM_lam_lower
  refine ⟨x0, C, fun X hX => ?_⟩
  rw [← mrtM_lam_eq_lamCoeff]
  exact h X hX

/-- **E3 (2) — the floor `(1/8)·loglog X ≤ M(λ; X)`, absorption done.**

The target shape is the corpus's own case-split hypothesis: it appears as an unsupplied
binder at `MRTPropA3.lean:295`, `:519`, `:538`, `:1547`, `:1556`, `:3533` (there at a
general `f`), so this is the first producer of that shape at `f := lamCoeff`.

Threshold: `X₀ = max (max x0 16) (exp (exp (max 1 (32·K/3))))` with
`K = 4·log 128 + (log 2)/32 − 4 + C`.  It is existential-harmless — the `∃ X₀` is the
whole interface — but it is effective, since `x0` and `C` come from `lambda_nonpret`. -/
theorem mrtM_lamCoeff_loglog_floor :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      (1 / 8) * Real.log (Real.log X) ≤ mrtM lamCoeff X := by
  obtain ⟨x0, C, h⟩ := mrtM_lamCoeff_lower
  refine ⟨max (max x0 16)
      (Real.exp (Real.exp (max 1 (32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3)))),
    ?_, ?_⟩
  · have h1 : (16 : ℝ) ≤ max (max x0 16)
        (Real.exp (Real.exp
          (max 1 (32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3)))) :=
      le_trans (le_max_right x0 16) (le_max_left _ _)
    linarith
  · intro X hX
    have hx0 : x0 ≤ X := le_trans (le_trans (le_max_left x0 16) (le_max_left _ _)) hX
    have h16 : (16 : ℝ) ≤ X := le_trans (le_trans (le_max_right x0 16) (le_max_left _ _)) hX
    have hexp : Real.exp (Real.exp
        (max 1 (32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3))) ≤ X :=
      le_trans (le_max_right _ _) hX
    -- transport the threshold through the two logarithms
    have hlogX_ge : Real.exp
        (max 1 (32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3)) ≤ Real.log X := by
      have h2 := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at h2
    have hLge : max 1 (32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3)
        ≤ Real.log (Real.log X) := by
      have h2 := Real.log_le_log (Real.exp_pos _) hlogX_ge
      rwa [Real.log_exp] at h2
    have hLK : 32 * (4 * Real.log 128 + Real.log 2 / 32 - 4 + C) / 3
        ≤ Real.log (Real.log X) := le_trans (le_max_right _ _) hLge
    have hlin := log3_shift_le_linear h16
    have hlow := h X hx0
    linarith

/-- **E3 (3) — the floor read as "eventually above any constant".**

`(1/8)·loglog X ≥ B` as soon as `X ≥ exp (exp (8·B))`.  This is the currency node E5
consumes: `mul_exp_neg_le_two_div` (`MRTPortA1Tail.lean:35`) needs `0 < M` and a
quantitative floor on `M` to turn `exp(−M)·M` into an arbitrarily small constant. -/
theorem mrtM_lamCoeff_ge (B : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X → B ≤ mrtM lamCoeff X := by
  obtain ⟨X₁, hX₁, h⟩ := mrtM_lamCoeff_loglog_floor
  refine ⟨max X₁ (Real.exp (Real.exp (8 * B))), lt_of_lt_of_le hX₁ (le_max_left _ _), ?_⟩
  intro X hX
  have h1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have h2 : Real.exp (Real.exp (8 * B)) ≤ X := le_trans (le_max_right _ _) hX
  have h3 : Real.exp (8 * B) ≤ Real.log X := by
    have h4 := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp] at h4
  have h5 : 8 * B ≤ Real.log (Real.log X) := by
    have h6 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h6
  have h7 := h X h1
  linarith

end Salt.MR
