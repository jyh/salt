/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RHSGrade
import Salt.MR.CompactMin

/-!
# GRADE-CLOSE ladder, rungs B-1/B-3 — the CONTOUR TRUNCATION (`TruncFactor`)

**The sixth vacuity catch, repaired on the analytic side.**  `CompactMin` (B-2) supplies the
honest minimizer: `hmin` quantified over a COMPACT `|v| ≤ R`, where attainment is free.  But
the consumer chain could not yet USE it, because `joint_cs_factoring`'s `hsupF` binder is
quantified over `∀ t : ℝ` (the whole contour), which forces the distance floor — and hence
`hmin` — onto the whole frequency line, where it is vacuous against any band floor
(Kronecker density drives the `ℝ`-infimum of the finite prime sum to `0`; see
`docs/exploration/hsup-design.md`, ⟦GRADE-SCOPE VERDICT + AMENDMENT V3⟧, and the
`ℝ`-caveat at `RHSGrade.lean:61-63`).

This file TRUNCATES the contour at height `T*`, so the `supF` binder is only ever needed on
the compact `|t − t₀| ≤ T*`:

* **B-1** `joint_cs_factoring_trunc` — J1 with the `hsupF` binder weakened to
  `|t − t₀| ≤ T*` plus a separate CRUDE global binder `hFar` (the FREE `M = 0` floor: no
  distance information at all) covering the far part.  The main term is BYTE-IDENTICAL to
  J1's — `(1/π)·∫∫ supF·crossKer` — and the far part enters as one ADDITIVE term
  `(1/π)·η²·(Ffar·Kfar)`.  So every downstream identification of `crossKer` (the mixed-line
  Plancherel bridge, the σ-cutoff, the width-decoupled grade) is untouched.
* **B-3** `crossKerFar_le_tail` / `far_tail_absorb` / `crossKerFar_pin_le` — the far part's
  own budget.  The far kernel mass is the Poisson tail `∫_{|τ|>T*} ‖K‖ ≤ 4(X+h)^{c+1}/(hT*)`
  (`hat_tail`, both sides), and at the pin `h = X/√L`, `T* = L⁴` this is
  `(X+h)^c·4(√L+1)/L⁴ ≤ (X+h)^c·L^{−5/2}` for `L ≥ 8` — the `hMcap` margin.
* **B-1b** `center_dist_floor_trunc` / `center_dist_floor_compact` — the `§0` floor with
  `hmin` on `|v| ≤ R` only, and its VACUITY-FREE existential form: no hypothesis at all,
  the minimizer produced by `exists_min_dist_abs`.

## The far part is FREE (why the crude binder suffices)

`hFar` asks only for a `t`-uniform bound on `‖𝒮·𝓛‖` with NO distance input — i.e. the
`M = 0` end of the pretentious majorant, which every consumer already has (it is
`supF_pret_majorant_sigma` at `M := 0`, or the plain `1/σ` Mertens side).  It is paid for by
the kernel's `L^{−7/2}` tail at the pin, against a main term of size `≥ (X+h)^c`.  Nothing in
the live band is spent.

## What is NOT done here

The `Kfar` socket of B-1 is stated as a named binder (`hKfar`), the house
conditional-assembly form — `crossKerFar_pin_le` discharges it at the pin from the two
window-mass bounds (`norm_windowSum_le_mass` at the worst line `c₀ − η`, one line each).
The composition into `rhs_grade_at_scale`'s `Agrade` shape is the consumer's (B-4+).
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## B-1 — the truncated CS factoring

### The far region and the far window–kernel cross-integral -/

/-- The far region `{t : T < |t − t₀|}` of the truncated contour. -/
lemma measurableSet_farRegion (t₀ T : ℝ) : MeasurableSet {t : ℝ | T < |t - t₀|} :=
  measurableSet_lt measurable_const (Continuous.measurable (by fun_prop))

/-- The centred far region `{τ : T < |τ|}`. -/
lemma measurableSet_farAbs (T : ℝ) : MeasurableSet {τ : ℝ | T < |τ|} :=
  measurableSet_lt measurable_const (Continuous.measurable (by fun_prop))

/-- **The far window–kernel cross-integral `crossKerFar`.**  `crossKer`'s integrand,
integrated over the FAR region `|t − t₀| > T` only.  The B-1 split writes the joint head as
`supF·crossKer` (the full `crossKer` — the main term is untouched) plus
`Ffar·crossKerFar`. -/
def crossKerFar (g : ℕ → ℂ) (X h y c₀ t₀ α β T : ℝ) : ℝ :=
  ∫ t in {t : ℝ | T < |t - t₀|},
    ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
      * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖

/-- `crossKerFar` is nonnegative (integrand is a product of norms). -/
lemma crossKerFar_nonneg (g : ℕ → ℂ) (X h y c₀ t₀ α β T : ℝ) :
    0 ≤ crossKerFar g X h y c₀ t₀ α β T := by
  unfold crossKerFar
  exact setIntegral_nonneg (measurableSet_farRegion t₀ T) (fun t _ => by positivity)

/-- **The abstract two-regime domination.**  If `‖A‖ ≤ F·P` off a measurable set `S` and
`‖A‖ ≤ Ffar·P` on `S`, with `P ≥ 0` integrable, then `‖∫A‖ ≤ F·∫P + Ffar·∫_S P`.

No integrability of `A` is needed: the single dominating function
`F·P + Ffar·1_S·P` is integrable and dominates `‖A‖` POINTWISE (on `S` the slack
`F·P ≥ 0` absorbs the difference), so `norm_integral_le_integral_norm` followed by
`integral_mono_of_nonneg` never asks whether `∫A` converges. -/
private lemma norm_integral_split_abs {A : ℝ → ℂ} {P : ℝ → ℝ} {F Ffar : ℝ} {S : Set ℝ}
    (hSm : MeasurableSet S) (hP0 : ∀ t, 0 ≤ P t) (hPint : Integrable P)
    (hF0 : 0 ≤ F)
    (hnear : ∀ t, t ∉ S → ‖A t‖ ≤ F * P t)
    (hfar : ∀ t, t ∈ S → ‖A t‖ ≤ Ffar * P t) :
    ‖∫ t : ℝ, A t‖ ≤ F * (∫ t : ℝ, P t) + Ffar * ∫ t in S, P t := by
  have hdom : Integrable (fun t : ℝ => F * P t + Ffar * S.indicator P t) :=
    (hPint.const_mul F).add ((hPint.indicator hSm).const_mul Ffar)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hstep : (∫ t : ℝ, ‖A t‖) ≤ ∫ t : ℝ, (F * P t + Ffar * S.indicator P t) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      hdom (Filter.Eventually.of_forall (fun t => ?_))
    have hcase : ‖A t‖ ≤ F * P t + Ffar * S.indicator P t := by
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
        have h1 := hfar t ht
        have h2 : (0 : ℝ) ≤ F * P t := mul_nonneg hF0 (hP0 t)
        linarith
      · rw [Set.indicator_of_notMem ht]
        have h1 := hnear t ht
        linarith
    exact hcase
  refine hstep.trans (le_of_eq ?_)
  rw [integral_add (hPint.const_mul F) ((hPint.indicator hSm).const_mul Ffar),
    integral_const_mul, integral_const_mul, integral_indicator hSm]

/-- **B-1 core — the TRUNCATED per-`(α,β)` CS factoring.**  `joint_inner_factor` with the
`𝒮·𝓛` sup binder weakened to the compact `|t − t₀| ≤ T` and a separate CRUDE global bound
`Ffar` covering the far part:

  `‖∫_t 𝒮·𝓛·P·P·K‖ ≤ F·crossKer α β + Ffar·crossKerFar α β T`.

The main term keeps the FULL `crossKer` (not its near part), so downstream identifications
of `crossKer` are byte-unchanged; the far part is a clean additive remainder. -/
lemma joint_inner_factor_trunc {g : ℕ → ℂ} {t₀ X h c₀ y α β F Ffar T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hF0 : 0 ≤ F) (_hFfar0 : 0 ≤ Ffar)
    (hsupF : ∀ t : ℝ, |t - t₀| ≤ T →
      ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ F)
    (hFar : ∀ t : ℝ,
      ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar) :
    ‖∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ F * crossKer g X h y c₀ t₀ α β + Ffar * crossKerFar g X h y c₀ t₀ α β T := by
  unfold crossKer crossKerFar
  refine norm_integral_split_abs (S := {t : ℝ | T < |t - t₀|})
    (P := fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
    (measurableSet_farRegion t₀ T) (fun t => by positivity)
    (crossKer_integrand_integrable hX hh hc) hF0 (fun t ht => ?_) (fun t ht => ?_)
  · -- NEAR: `|t − t₀| ≤ T`, the truncated sup applies
    simp only [Set.mem_setOf_eq, not_lt] at ht
    rw [norm_mul, norm_mul, norm_mul]
    have hSL := hsupF t ht
    calc ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
              * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ F * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by gcongr
      _ = F * (‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := by ring
  · -- FAR: the crude `M = 0` global bound
    clear ht
    rw [norm_mul, norm_mul, norm_mul]
    have hSL := hFar t
    calc ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
              * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ Ffar * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by gcongr
      _ = Ffar * (‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := by ring

/-- **B-1 — the TRUNCATED joint CS factoring (`joint_cs_factoring_trunc`).**  The repair of
the sixth vacuity catch on the analytic side: `joint_cs_factoring` with its `∀ t : ℝ` sup
binder split into

* `hsupF` on the COMPACT `|t − t₀| ≤ T` — where `CompactMin`'s honest minimizer lives, and
  where the `ℝ`-caveat of `RHSGrade.lean:61-63` is moot;
* `hFar`, a CRUDE global binder (no distance input — the FREE `M = 0` floor), whose kernel
  mass is confined to the far region by `hKfar`.

Conclusion: the J1 main term VERBATIM, plus one additive far term.

  `‖prop21RHS‖ ≤ (1/π)·∫₀^η∫₀^η supF α β·crossKer α β + (1/π)·η²·(Ffar·Kfar)`.

`T` is a FREE parameter — the `T* := L⁴` pin is the consumer's (see `far_tail_absorb`).
The four integrability sockets are `joint_cs_factoring`'s own, unchanged; `hKfar` is the one
new socket (discharged at the pin by `crossKerFar_pin_le`). -/
theorem joint_cs_factoring_trunc {g : ℕ → ℂ} {t₀ X h c₀ y η T Ffar Kfar : ℝ}
    {supF : ℝ → ℝ → ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η) (hFfar0 : 0 ≤ Ffar)
    (hsupF0 : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ supF α β)
    (hsupF : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ, |t - t₀| ≤ T →
        ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
            * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ supF α β)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
        ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
            * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
        crossKerFar g X h y c₀ t₀ α β T ≤ Kfar)
    (hIβ : ∀ α ∈ Icc (0 : ℝ) η,
        IntervalIntegrable (fun β => supF α β * crossKer g X h y c₀ t₀ α β) volume 0 η)
    (hIβ' : ∀ α ∈ Icc (0 : ℝ) η,
        IntervalIntegrable
          (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖)
          volume 0 η)
    (hIα : IntervalIntegrable
        (fun α => ∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β) volume 0 η)
    (hIα' : IntervalIntegrable
        (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
          ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖) volume 0 η) :
    ‖prop21RHS g t₀ X h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          supF α β * crossKer g X h y c₀ t₀ α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  have hπ0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  -- per-`β` pointwise bound
  have hperβ : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖
        ≤ (1 / (2 * Real.pi) : ℝ)
            * (supF α β * crossKer g X h y c₀ t₀ α β + Ffar * Kfar) := by
    intro α hα β hβ
    have hc : 0 < c₀ - α - β := by
      obtain ⟨_, hαη⟩ := hα; obtain ⟨_, hβη⟩ := hβ; linarith
    rw [norm_smul, Real.norm_of_nonneg hπ0]
    refine mul_le_mul_of_nonneg_left ?_ hπ0
    refine (joint_inner_factor_trunc hX hh hc (hsupF0 α hα β hβ) hFfar0
      (hsupF α hα β hβ) (hFar α hα β hβ)).trans ?_
    have hK := mul_le_mul_of_nonneg_left (hKfar α hα β hβ) hFfar0
    linarith
  -- per-`α` bound
  have hperα : ∀ α ∈ Icc (0 : ℝ) η,
      ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖
        ≤ (1 / (2 * Real.pi) : ℝ)
            * ((∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
                + η * (Ffar * Kfar)) := by
    intro α hα
    have hrhs : IntervalIntegrable
        (fun β => (1 / (2 * Real.pi) : ℝ)
          * (supF α β * crossKer g X h y c₀ t₀ α β + Ffar * Kfar)) volume 0 η :=
      ((hIβ α hα).add intervalIntegrable_const).const_mul (1 / (2 * Real.pi))
    refine (intervalIntegral.norm_integral_le_integral_norm hη0).trans ?_
    refine (intervalIntegral.integral_mono_on hη0 (hIβ' α hα) hrhs
      (fun β hβ => hperβ α hα β hβ)).trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hπ0
    rw [intervalIntegral.integral_add (hIβ α hα) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  -- assemble the outer `α`-integral
  have hIrhs : IntervalIntegrable
      (fun α => (1 / (2 * Real.pi) : ℝ)
        * ((∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
            + η * (Ffar * Kfar))) volume 0 η :=
    (hIα.add intervalIntegrable_const).const_mul (1 / (2 * Real.pi))
  rw [prop21RHS_eq_jointIntegrand, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) * ‖∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
          ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖
      ≤ 2 * ∫ α in (0 : ℝ)..η,
          ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖ :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hη0)
          (by norm_num)
    _ ≤ 2 * ∫ α in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ)
          * ((∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
              + η * (Ffar * Kfar)) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_on hη0 hIα' hIrhs hperα) (by norm_num)
    _ = (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            supF α β * crossKer g X h y c₀ t₀ α β)
          + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hIα intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        rw [show (1 / Real.pi) = 2 * (1 / (2 * Real.pi)) from by rw [mul_one_div]; ring_nf]
        ring

/-! ## B-3 — the far part's budget

The far term is paid for by the kernel's Poisson tail beyond `T`.  Three stones: the
translated far kernel mass (`kernel_far_mass`), its transfer to `crossKerFar`
(`crossKerFar_le_tail`), and the pin arithmetic (`far_tail_absorb`). -/

/-- Translation of a far-region integral to the centred far region.  Pure change of
variables (`integral_sub_right_eq_self` on the indicator); no integrability needed. -/
private lemma setIntegral_far_comp_sub (φ : ℝ → ℝ) (t₀ T : ℝ) :
    (∫ t in {t : ℝ | T < |t - t₀|}, φ (t - t₀)) = ∫ τ in {τ : ℝ | T < |τ|}, φ τ := by
  rw [← integral_indicator (measurableSet_farRegion t₀ T),
    ← integral_indicator (measurableSet_farAbs T)]
  rw [show (fun t : ℝ => Set.indicator {t : ℝ | T < |t - t₀|} (fun t => φ (t - t₀)) t)
        = (fun t : ℝ => Set.indicator {τ : ℝ | T < |τ|} φ (t - t₀)) from by
      funext t
      by_cases ht : t ∈ {t : ℝ | T < |t - t₀|}
      · have ht' : t - t₀ ∈ {τ : ℝ | T < |τ|} := ht
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      · have ht' : t - t₀ ∉ {τ : ℝ | T < |τ|} := ht
        rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']]
  exact integral_sub_right_eq_self (Set.indicator {τ : ℝ | T < |τ|} φ) t₀

/-- The far-region kernel integral, recentred. -/
private lemma setIntegral_far_kernel (X h c t₀ T : ℝ) :
    (∫ t in {t : ℝ | T < |t - t₀|}, ‖hatKernel X h c (t - t₀)‖)
      = ∫ τ in {τ : ℝ | T < |τ|}, ‖hatKernel X h c τ‖ :=
  setIntegral_far_comp_sub (fun τ => ‖hatKernel X h c τ‖) t₀ T

/-- The centred far region as a union of two rays. -/
private lemma farAbs_eq_union (T : ℝ) : {τ : ℝ | T < |τ|} = Set.Iio (-T) ∪ Set.Ioi T := by
  ext τ
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · intro hτ
    rcases le_or_gt τ 0 with hs | hs
    · rw [abs_of_nonpos hs] at hτ; exact Or.inl (by linarith)
    · rw [abs_of_pos hs] at hτ; exact Or.inr hτ
  · rintro (h1 | h1) <;> rcases le_or_gt τ 0 with hs | hs
    · rw [abs_of_nonpos hs]; linarith
    · rw [abs_of_pos hs]; linarith
    · rw [abs_of_nonpos hs]; linarith
    · rw [abs_of_pos hs]; linarith

/-- **The far kernel mass.**  `∫_{|τ| > T} ‖hatKernel X h c τ‖ ≤ 4(X+h)^{c+1}/(hT)` — the
branch-2 (Poisson, `1/‖s‖²`) tail on both rays (`hat_tail`, evenness of the dominator).
This is `kernel_L1_mass_sharp`'s tail piece, isolated. -/
lemma kernel_far_mass {X h c T : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (hT : 0 < T) :
    (∫ τ in {τ : ℝ | T < |τ|}, ‖hatKernel X h c τ‖) ≤ 4 * (X + h) ^ (c + 1) / (h * T) := by
  have hInt : Integrable (fun τ : ℝ => ‖hatKernel X h c τ‖) :=
    (integrable_hatKernel hX hh hc).norm
  have hb2 : Integrable (fun τ : ℝ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2))) :=
    integrable_branch2 hc
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_Iio] at ha
    simp only [Set.mem_Ioi] at hb
    linarith
  have hright : (∫ τ in Set.Ioi T, ‖hatKernel X h c τ‖) ≤ 2 * (X + h) ^ (c + 1) / (h * T) := by
    calc ∫ τ in Set.Ioi T, ‖hatKernel X h c τ‖
        ≤ ∫ τ in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2.integrableOn measurableSet_Ioi
            (fun τ _ => hatKernel_branch2 hX hh hc τ)
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T) := hat_tail hX hh hc hT
  have heven : (∫ τ in Set.Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)))
      = ∫ τ in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) := by
    rw [show (∫ τ in Set.Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)))
          = ∫ τ in Set.Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + (-τ) ^ 2)) from
        setIntegral_congr_fun measurableSet_Iic (fun τ _ => by rw [neg_sq])]
    rw [integral_comp_neg_Iic (-T) (fun τ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)))]
    rw [neg_neg]
  have hleft : (∫ τ in Set.Iio (-T), ‖hatKernel X h c τ‖)
      ≤ 2 * (X + h) ^ (c + 1) / (h * T) := by
    rw [← integral_Iic_eq_integral_Iio]
    calc ∫ τ in Set.Iic (-T), ‖hatKernel X h c τ‖
        ≤ ∫ τ in Set.Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2.integrableOn measurableSet_Iic
            (fun τ _ => hatKernel_branch2 hX hh hc τ)
      _ = ∫ τ in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) := heven
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T) := hat_tail hX hh hc hT
  rw [farAbs_eq_union T,
    setIntegral_union hdisj measurableSet_Ioi hInt.integrableOn hInt.integrableOn]
  have hsum : 4 * (X + h) ^ (c + 1) / (h * T)
      = 2 * (X + h) ^ (c + 1) / (h * T) + 2 * (X + h) ^ (c + 1) / (h * T) := by ring
  linarith

/-- **B-3a — the far cross-integral's budget (`crossKerFar_le_tail`).**  With crude
`t`-uniform masses `Mm`, `Mp` for the two window legs (`norm_windowSum_le_mass`, one line
each — constant in `t`, valid at ANY line, so the worst line `c₀ − η` makes them uniform in
`β`), the far window–kernel cross-integral is bounded by the kernel's Poisson tail:

  `crossKerFar ≤ Mm·Mp·(4(X+h)^{c+1}/(hT))`,  `c = c₀ − α − β`. -/
lemma crossKerFar_le_tail {g : ℕ → ℂ} {X h y c₀ t₀ α β T Mm Mp : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hT : 0 < T)
    (hMm0 : 0 ≤ Mm) (hMp0 : 0 ≤ Mp)
    (hbm : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm)
    (hbp : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp) :
    crossKerFar g X h y c₀ t₀ α β T
      ≤ Mm * Mp * (4 * (X + h) ^ (c₀ - α - β + 1) / (h * T)) := by
  have hSm := measurableSet_farRegion t₀ T
  have hPint : Integrable (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    crossKer_integrand_integrable hX hh hc
  have hkerint : Integrable
      (fun t : ℝ => Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    (((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (Mm * Mp)
  have hstep1 : crossKerFar g X h y c₀ t₀ α β T
      ≤ ∫ t in {t : ℝ | T < |t - t₀|},
          Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by
    unfold crossKerFar
    refine setIntegral_mono_on hPint.integrableOn hkerint.integrableOn hSm (fun t _ => ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hbm (t - t₀)) (hbp (t - t₀)) (norm_nonneg _) hMm0) (norm_nonneg _)
  have hstep2 : (∫ t in {t : ℝ | T < |t - t₀|},
        Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      = Mm * Mp * ∫ τ in {τ : ℝ | T < |τ|}, ‖hatKernel X h (c₀ - α - β) τ‖ := by
    rw [integral_const_mul, setIntegral_far_kernel]
  refine hstep1.trans ?_
  rw [hstep2]
  exact mul_le_mul_of_nonneg_left (kernel_far_mass hX hh hc hT) (mul_nonneg hMm0 hMp0)

/-- The amplitude ratio at the pin `h = X/√L`: `4(X+h)/h = 4(√L+1)`. -/
private lemma far_ratio_calc {X s Q : ℝ} (hX : 0 < X) (hs : 0 < s) (hQ : 0 < Q) :
    4 * (X + X / s) / (X / s * Q) = 4 * (s + 1) / Q := by
  have hX' : X ≠ 0 := ne_of_gt hX
  have hs' : s ≠ 0 := ne_of_gt hs
  have hQ' : Q ≠ 0 := ne_of_gt hQ
  field_simp

/-- **B-3b — the absorption arithmetic (`far_tail_absorb`).**  At the corpus pin
`h = X·L^{−1/2}` and the truncation height `T* = L⁴`, the far kernel tail is

  `4(X+h)^{c+1}/(h·T*) = (X+h)^c·4(√L+1)/L⁴ ≤ (X+h)^c/(L²√L)`,

i.e. the far term is `L^{−5/2}` RELATIVE TO THE BARE KERNEL SCALE `(X+h)^c` — and the main
term carries `(X+h)^c` times a factor `≥ 1` (`Θ(log L)` on the `Tsplit`-sharp face,
`Θ(√L)` on the crude face), so the relative margin is at least `L^{−5/2}` and in fact
`L^{−7/2}` against the sharp mass, `L^{−4}` against the crude one.

**The exponent, honestly.**  What is proven here is `L^{−5/2}` against `(X+h)^c`; the
true amplitude ratio is `4(√L+1)/L⁴ ≍ 4L^{−7/2}`, and the numeral `5/2` is the SLACK-CARRYING
statement (the gate is `4L + 4√L ≤ L²`, true from `L ≥ 8`).  A consumer wanting the sharper
`L^{−7/2}` gets it from the same page with `L ≥ 8` replaced by nothing — but `L^{−5/2}` is
what the `hMcap` slot needs and what leaves room for the live band's `exp(M/2) ≤ L^{1/32}`
crude-versus-pretentious price.  No positivity of the exponent `c` is needed: the identity
`(X+h)^{c+1} = (X+h)^c·(X+h)` and the amplitude cancellation hold at every real `c`. -/
theorem far_tail_absorb {X L c : ℝ} (hX : 1 ≤ X) (hL : 8 ≤ L) :
    4 * (X + X / Real.sqrt L) ^ (c + 1) / (X / Real.sqrt L * L ^ 4)
      ≤ (X + X / Real.sqrt L) ^ c / (L ^ 2 * Real.sqrt L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + X / Real.sqrt L := by positivity
  have hpc : (0 : ℝ) < (X + X / Real.sqrt L) ^ c := Real.rpow_pos_of_pos hXh0 c
  have hpow : (X + X / Real.sqrt L) ^ (c + 1)
      = (X + X / Real.sqrt L) ^ c * (X + X / Real.sqrt L) := by
    rw [Real.rpow_add hXh0, Real.rpow_one]
  have hratio : 4 * (X + X / Real.sqrt L) / (X / Real.sqrt L * L ^ 4)
      = 4 * (Real.sqrt L + 1) / L ^ 4 := far_ratio_calc hX0 hs0 (by positivity)
  have hsL : Real.sqrt L ≤ L := by
    nlinarith [hsq, sq_nonneg (Real.sqrt L - 1), hL]
  have hmargin : 4 * (Real.sqrt L + 1) / L ^ 4 ≤ 1 / (L ^ 2 * Real.sqrt L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 4 * (L + Real.sqrt L) ≤ L ^ 2 := by
      nlinarith [hsL, hL, mul_nonneg (by linarith : (0 : ℝ) ≤ L - 8) hL0.le]
    have h2 : L ^ 2 * (4 * (L + Real.sqrt L)) ≤ L ^ 2 * L ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
    have h3 : 4 * (Real.sqrt L + 1) * (L ^ 2 * Real.sqrt L)
        = L ^ 2 * (4 * (L + Real.sqrt L)) := by
      linear_combination (4 * L ^ 2) * hsq
    have h4 : L ^ 2 * L ^ 2 = 1 * L ^ 4 := by ring
    linarith
  rw [hpow]
  have hEq : 4 * ((X + X / Real.sqrt L) ^ c * (X + X / Real.sqrt L))
        / (X / Real.sqrt L * L ^ 4)
      = (X + X / Real.sqrt L) ^ c
          * (4 * (X + X / Real.sqrt L) / (X / Real.sqrt L * L ^ 4)) := by ring
  rw [hEq, hratio, div_eq_mul_one_div ((X + X / Real.sqrt L) ^ c) (L ^ 2 * Real.sqrt L)]
  exact mul_le_mul_of_nonneg_left hmargin hpc.le

/-- **B-3 exit — the `hKfar` socket at the pin (`crossKerFar_pin_le`).**  Composing B-3a and
B-3b: at `h = X/√L`, `T* = L⁴`, `L ≥ 8`,

  `crossKerFar ≤ Mm·Mp·(X+h)^{c₀−α−β}/(L²√L)`.

This is exactly `joint_cs_factoring_trunc`'s `hKfar` binder, with `Kfar` taken at the
`β`-uniform masses (`norm_windowSum_le_mass` at the worst line `c₀ − η`). -/
theorem crossKerFar_pin_le {g : ℕ → ℂ} {X L y c₀ t₀ α β Mm Mp : ℝ}
    (hX : 1 ≤ X) (hL : 8 ≤ L) (hc : 0 < c₀ - α - β) (hMm0 : 0 ≤ Mm) (hMp0 : 0 ≤ Mp)
    (hbm : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm)
    (hbp : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp) :
    crossKerFar g X (X / Real.sqrt L) y c₀ t₀ α β (L ^ 4)
      ≤ Mm * Mp * ((X + X / Real.sqrt L) ^ (c₀ - α - β) / (L ^ 2 * Real.sqrt L)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < X / Real.sqrt L := by positivity
  have hT0 : (0 : ℝ) < L ^ 4 := by positivity
  refine (crossKerFar_le_tail hX hh0 hc hT0 hMm0 hMp0 hbm hbp).trans ?_
  exact mul_le_mul_of_nonneg_left (far_tail_absorb hX hL) (mul_nonneg hMm0 hMp0)

/-! ## B-1b — the `§0` distance floor with `hmin` on the compact

`RHSGrade.center_dist_floor` consumes its `hmin` at exactly ONE frequency, `v = t − t₀`.
Under the truncation `|t − t₀| ≤ R` that frequency lies in the compact, so the whole
`∀ v : ℝ` binder — the vacuous one — is unnecessary. -/

/-- **B-1b — the TRUNCATED centre floor (`center_dist_floor_trunc`).**
`RHSGrade.center_dist_floor` with `hmin` quantified over the COMPACT `|v| ≤ R` only, valid
for every contour point `t` with `|t − t₀| ≤ R`.  Proof is `center_dist_floor`'s, with the
single use `hmin (t − t₀)` supplied by the truncation hypothesis.

This is the statement `CompactMin.exists_min_dist_abs` actually produces — so the composed
chain is no longer vacuous in the live band. -/
theorem center_dist_floor_trunc {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t₁ X z R : ℝ} (hXz : ⌊X⌋₊ ≤ ⌊z⌋₊)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    {t : ℝ} (ht : |t - t₀| ≤ R) :
    pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
          (costwist (t - (t₀ + t₁))) z := by
  have hEll : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := ellLin_norm_le_one g hg
  have hcw : ∀ n : ℕ, ‖costwist t n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have h1 := twisted_datum_dist_eq g (t₀ + t₁) (t - (t₀ + t₁)) z
  rw [show t - (t₀ + t₁) + (t₀ + t₁) = t from by ring] at h1
  have h2 : pretDistSq (ellLin g) (costwist t) X ≤ pretDistSq (ellLin g) (costwist t) z :=
    pretDistSq_mono_floor hEll hcw hXz
  have h3 : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist (t - t₀)) X
      = pretDistSq (ellLin g) (costwist t) X := by
    rw [seamCoeff_trivial_dist_eq, show t - t₀ + t₀ = t from by ring]
  have h4 := hmin (t - t₀) ht
  rw [h1]
  linarith

/-- **B-1b exit — the VACUITY-FREE centre floor (`center_dist_floor_compact`).**  The
truncated floor with NO minimality hypothesis at all: the minimizer is produced by
`CompactMin.exists_min_dist_abs` (extreme value theorem on `[−R, R]`), so the composed
statement is unconditional in the frequency structure.

This is the shape the truncated consumer wants: pick `R := X + T*`, get a centre `t₁`
inside the truncated range together with the floor at every contour point. -/
theorem center_dist_floor_compact {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ X : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ t₁ : ℝ, |t₁| ≤ R ∧
      ∀ z t : ℝ, ⌊X⌋₊ ≤ ⌊z⌋₊ → |t - t₀| ≤ R →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
              (costwist (t - (t₀ + t₁))) z := by
  obtain ⟨t₁, ht₁R, hmin⟩ :=
    exists_min_dist_abs (seamCoeff (ellLin g) (fun _ => 1) t₀) X hR
  exact ⟨t₁, ht₁R, fun z t hXz ht => center_dist_floor_trunc hg hXz hmin ht⟩

end Salt.MR
