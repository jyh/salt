/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HExit
import Salt.MR.SupF

/-!
# PART 3 — the JOINT HEAD: the σ-live CS-factoring of `prop21RHS` (J1/J2)

The joint-head route to `hRHS` (`T1_head_wire`'s named residual), the last input of
S8's Part 3.  Where the box-collapsed leg (`prop21RHS_le_head`, HELD — BALL-REF
confirmed-fatal) freezes the four-factor sup `F0` as a single box constant and collapses
the window cross-integral to `Kmass·Sη²`, discarding the `L²`-mean structure the σ-cutoff
needs, the JOINT route keeps the `𝒮·𝓛` sup **β-dependent** (`supF α β`) and keeps the
two window legs `P·P` **together with the kernel's Poisson weight** as a genuine
cross-integral (`crossKer α β`), so the σ-integral (GHS Cor 1.2) has a home.

Design: `docs/exploration/supf-design.md`, the ⟦JOINT-SCOPE VERDICT⟧ block (J1/J2/J3);
the dimensional page is `HalaszSeam`'s LOG-POWER LEDGER (`:81-108`, marked PASSES).

## J1 — `joint_cs_factoring`: the weighted CS separating `F = 𝒮·𝓛` from `P·P·hatKernel`

The `t`-integrand of `prop21RHS` is `𝒮(s−α−β)·𝓛(s+β)·P(s−β)·P(s+β)·hatKernel(c₀−α−β)`.
J1 pulls the `𝒮·𝓛` factor out by its per-`(α,β)` sup `supF α β` (KEPT β-dependent — the
old socket's fatal was freezing this box-uniform) and keeps the window–kernel remainder
as the cross-integral

  `crossKer α β := ∫_t ‖P(s−β)‖·‖P(s+β)‖·‖hatKernel X h (c₀−α−β) (t−t₀)‖ dt`,

so that `‖prop21RHS‖ ≤ (1/π)·∫₀^η∫₀^η supF α β · crossKer α β dβ dα`.  The kernel's
Poisson weight is kept WITH the `P·P` (the `k4_cross_CS` pattern J2 re-runs on `crossKer`).

## The mixed-line residual (J2's ONE medium risk — socketed)

`crossKer`'s two window legs sit on the DISTINCT lines `c₀−β`, `c₀+β`, and the kernel's
Poisson weight (dominant branch of `hat_mellin_bound`) on a THIRD line `c₀−α−β`.  The
landed diagonalization `dirichlet_plancherel`/`k4_cross_CS` is single-line (one `c` for
both polynomials and the weight); the three-line cross-integral is a genuinely new
Plancherel variant.  Per the campaign law ("STOP if a genuinely new Plancherel variant is
needed"), the `crossKer → (x/y)^{2β}·min(L²,1/β²)` identification is carried as a NAMED
hypothesis in J2 (`hcross_supply`), the honest socket for the flagged medium risk.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## J1 — the window–kernel cross-integral and the CS factoring -/

/-- The `t`-integrand of `prop21RHS` (`s = c₀+(t−t₀)·I`): the four-series product against
the centered hat kernel.  Defeq to the integrand written inline in `prop21RHS`. -/
def jointIntegrand (g : ℕ → ℂ) (t₀ X h c₀ y α β t : ℝ) : ℂ :=
  smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
    * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
    * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
    * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
    * hatKernel X h (c₀ - α - β) (t - t₀)

/-- `prop21RHS` written via `jointIntegrand` (definitional). -/
lemma prop21RHS_eq_jointIntegrand (g : ℕ → ℂ) (t₀ X h c₀ y η : ℝ) :
    prop21RHS g t₀ X h c₀ y η
      = (2 : ℝ) • ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi)) •
          ∫ t : ℝ, jointIntegrand g t₀ X h c₀ y α β t := rfl

/-- **The window–kernel cross-integral `crossKer`.**  The `t`-integral of the two window
Dirichlet polynomials `P(s−β)`, `P(s+β)` against the kernel norm at the shifted line
`c₀−α−β`, `s = c₀+(t−t₀)·I`.  This is the object J1 separates out of `prop21RHS`'s
integrand and J2 identifies (via the mixed-line Plancherel, socketed) with the
`(x/y)^{2β}·min(L²,1/β²)` shape.  Poisson weight kept WITH `P·P` (the `k4_cross_CS`
pattern). -/
def crossKer (g : ℕ → ℂ) (X h y c₀ t₀ α β : ℝ) : ℝ :=
  ∫ t : ℝ,
    ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
      * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖

/-- `crossKer` is nonnegative (integrand is a product of norms). -/
lemma crossKer_nonneg (g : ℕ → ℂ) (X h y c₀ t₀ α β : ℝ) :
    0 ≤ crossKer g X h y c₀ t₀ α β := by
  unfold crossKer
  refine integral_nonneg (fun t => ?_)
  positivity

/-- The `crossKer` integrand is integrable: each window leg is bounded pointwise by its
`n^{−c}`-weighted coefficient mass (`norm_windowSum_le_mass`, constant in `t`), and the
kernel is integrable (`integrable_hatKernel`). -/
lemma crossKer_integrand_integrable {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    Integrable (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := by
  set Mm := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hMm
  set Mp := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hMp
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg (fun n _ => by positivity)
  have hMp0 : 0 ≤ Mp := Finset.sum_nonneg (fun n _ => by positivity)
  -- dominator: (Mm·Mp) · ‖hatKernel‖, integrable
  have hker : Integrable
      (fun t : ℝ => Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    (((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (Mm * Mp)
  -- continuity of the integrand (each window leg continuous in t; kernel continuous)
  have hs : Continuous (fun t : ℝ => ((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)) := by
    fun_prop
  have hPm : Continuous (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖) :=
    ((continuous_windowSum g X y).comp (hs.sub continuous_const)).norm
  have hPp : Continuous (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖) :=
    ((continuous_windowSum g X y).comp (hs.add continuous_const)).norm
  have hKc : Continuous (fun t : ℝ => ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    ((continuous_hatKernel (by linarith) hh hc).comp (continuous_id.sub continuous_const)).norm
  have hcont : Continuous (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := (hPm.mul hPp).mul hKc
  refine hker.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
  have hbm : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm := by
    rw [hMm]
    exact norm_windowSum_le_mass g X y (c₀ - β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
  have hbp : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp := by
    rw [hMp]
    exact norm_windowSum_le_mass g X y (c₀ + β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
  rw [Real.norm_of_nonneg (by positivity)]
  have hstep : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mm * Mp :=
    mul_le_mul hbm hbp (norm_nonneg _) hMm0
  calc ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)

/-- **J1 core — the per-`(α,β)` CS factoring.**  The `t`-integral of `prop21RHS`'s
integrand has norm `≤ F · crossKer α β`, where `F` is any per-`(α,β)` bound on the
four-factor `‖𝒮·𝓛‖` (KEPT β-dependent — the box-collapse's fatal was freezing this).
The `𝒮·𝓛` factor is pulled out by `F`; the window–kernel remainder is `crossKer` (Poisson
weight kept WITH `P·P`).  Real content: `norm_integral_le_integral_norm` + pointwise
domination + `integral_const_mul`. -/
lemma joint_inner_factor {g : ℕ → ℂ} {t₀ X h c₀ y α β F : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (_hF0 : 0 ≤ F)
    (hsupF : ∀ t : ℝ,
      ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ F) :
    ‖∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ F * crossKer g X h y c₀ t₀ α β := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : Integrable (fun t : ℝ => F *
      (‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)) :=
    (crossKer_integrand_integrable hX hh hc).const_mul F
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    hbound (Filter.Eventually.of_forall (fun t => ?_))).trans_eq ?_
  · -- pointwise: ‖𝒮·𝓛·P·P·hatK‖ ≤ F·(‖P‖·‖P‖·‖hatK‖)
    dsimp only
    rw [norm_mul, norm_mul, norm_mul]
    have hSL := hsupF t
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
  · exact MeasureTheory.integral_const_mul F _

/-- **J1 — the joint CS factoring (`joint_cs_factoring`).**  `‖prop21RHS‖` factors into
`(1/π)·∫₀^η∫₀^η supF α β · crossKer α β`, the σ-live interface: the `𝒮·𝓛` sup `supF α β`
is KEPT β-dependent and the window–kernel remainder `crossKer α β` keeps `P·P` WITH the
kernel's Poisson weight (so J2's σ-cutoff has a home — the box-collapse's fatal defect
repaired).  Unconditional in the four analytic sockets: the two `supF` bounds and the two
levels of interval-integrability of the assembled bound (the `α,β`-collapse's plumbing —
the honest conditional-assembly house form). -/
theorem joint_cs_factoring {g : ℕ → ℂ} {t₀ X h c₀ y η : ℝ} {supF : ℝ → ℝ → ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hsupF0 : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ supF α β)
    (hsupF : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
        ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
            * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ supF α β)
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
      ≤ (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          supF α β * crossKer g X h y c₀ t₀ α β := by
  have hπ0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  -- per-α bound: ‖∫β (1/2π)•innerT‖ ≤ ∫β (1/2π)·(supF·crossKer)
  have hperα : ∀ α ∈ Icc (0 : ℝ) η,
      ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖
        ≤ ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) * (supF α β * crossKer g X h y c₀ t₀ α β) := by
    intro α hα
    refine (intervalIntegral.norm_integral_le_integral_norm hη0).trans ?_
    refine intervalIntegral.integral_mono_on hη0 (hIβ' α hα)
      ((hIβ α hα).const_mul (1 / (2 * Real.pi))) (fun β hβ => ?_)
    have hc : 0 < c₀ - α - β := by
      obtain ⟨_, hαη⟩ := hα; obtain ⟨_, hβη⟩ := hβ; linarith
    rw [norm_smul, Real.norm_of_nonneg hπ0]
    refine mul_le_mul_of_nonneg_left ?_ hπ0
    exact joint_inner_factor hX hh hc (hsupF0 α hα β hβ) (hsupF α hα β hβ)
  -- assemble the outer α-integral
  rw [prop21RHS_eq_jointIntegrand, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) * ‖∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
          ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖
      ≤ 2 * ∫ α in (0 : ℝ)..η,
          ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand g t₀ X h c₀ y α β t‖ :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hη0)
          (by norm_num)
    _ ≤ 2 * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          (1 / (2 * Real.pi) : ℝ) * (supF α β * crossKer g X h y c₀ t₀ α β) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_on hη0 hIα'
            ((hIα.const_mul (1 / (2 * Real.pi))).congr
              (fun α _ => (intervalIntegral.integral_const_mul _ _).symm))
            hperα)
          (by norm_num)
    _ = (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          supF α β * crossKer g X h y c₀ t₀ α β := by
        have hcm : ∀ α : ℝ,
            (∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) * (supF α β * crossKer g X h y c₀ t₀ α β))
              = (1 / (2 * Real.pi)) * ∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β :=
          fun α => intervalIntegral.integral_const_mul _ _
        rw [show (fun α => ∫ β in (0 : ℝ)..η,
              (1 / (2 * Real.pi) : ℝ) * (supF α β * crossKer g X h y c₀ t₀ α β))
            = fun α => (1 / (2 * Real.pi) : ℝ) * ∫ β in (0 : ℝ)..η,
              supF α β * crossKer g X h y c₀ t₀ α β from funext hcm,
          intervalIntegral.integral_const_mul]
        rw [show (1 / Real.pi) = 2 * (1 / (2 * Real.pi)) from by
          rw [mul_one_div]; ring_nf]
        ring

/-! ## J2 — the σ-cutoff wiring (`sigma_wiring`)

Wires the landed `sigma_cutoff` (STONE 2, the `(1+M)` two-regime split, GHS Cor 1.2) into
the per-`α` window cross-integral.  The `β`-integral of `supF·crossKer` is mapped to the
`σ`-weighted integral `∫ Fbound σ/σ` (`σ = β + 1/L`, the ledger's step 4) by the
**mixed-line bridge** `hbridge` — the campaign's ONE flagged medium risk, socketed here:
`crossKer`'s two window legs live on the distinct lines `c₀∓β` with the kernel Poisson
weight on `c₀−α−β`, a THREE-line cross-integral the single-line `dirichlet_plancherel` /
`k4_cross_CS` cannot diagonalize (a genuinely new Plancherel variant — STOP + socket, per
the campaign law).  The pretentious socket `hpret` (`Fbound σ ≤ e^{−M}·L`) is SupF's
general-`g` distance split (the PENDING residual — SupF lands the pin `σ = 1/L` via
`head_pin_bound`, but the `loglog X − M(t)` evaluation is available only at the principal
datum); `htriv` (`Fbound σ ≤ 1/σ`) is the Mertens 1/σ side.  `sigma_cutoff` itself is
consumed unconditionally. -/
theorem sigma_wiring {g : ℕ → ℂ} {t₀ X h c₀ y η L M Kα : ℝ} {supF : ℝ → ℝ → ℝ}
    {Fbound : ℝ → ℝ} {α : ℝ}
    (hL : 3 ≤ L) (hM : 0 ≤ M) (hlo : 1 / L ≤ 2 * η) (hKα0 : 0 ≤ Kα)
    (hint : IntervalIntegrable (fun σ => Fbound σ / σ) volume (1 / L) (2 * η))
    (hpret : ∀ σ ∈ Icc (1 / L) (2 * η), Fbound σ ≤ Real.exp (-M) * L)
    (htriv : ∀ σ ∈ Icc (1 / L) (2 * η), Fbound σ ≤ 1 / σ)
    (hbridge : (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
        ≤ Kα * ∫ σ in (1 / L)..(2 * η), Fbound σ / σ) :
    (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
      ≤ Kα * ((1 + M) * Real.exp (-M) * L) :=
  hbridge.trans (mul_le_mul_of_nonneg_left
    (sigma_cutoff Fbound hL hM hlo hint hpret htriv) hKα0)

/-! ## The joint grade assembly (`joint_grade_assembly`) — J1 ∘ J2 ∘ α-integral

Composes J1 (`hJ1`: `‖prop21RHS‖ ≤ (1/π)∫∫ supF·crossKer`) with J2's per-`α` σ-cutoff
(`hJ2`: `∫β supF·crossKer ≤ Kfun α · (1+M)e^{−M}L`) and the α-integration.  The
`(1+M)e^{−M}L` factor is `α`-uniform, so it pulls out; the kernel-scale α-integral
`∫₀^η Kfun` supplies the `1/L` that cancels the σ-cutoff's `L` (LEDGER `κ=1`), leaving
`‖prop21RHS‖ ≤ Agrade·(1+M)e^{−M}` with `Agrade := (1/π)·L·∫₀^η Kfun` — EXACTLY the
`hjoint` input of `hRHS_discharged_joint` (HExit).  The grade socket then is
`Agrade ≤ C₁·X` (the `∫₀^η Kfun ≍ X/L` kernel-mass residual, the `Tsplit`/`arcsinh`
sharpening flagged in `kernel_mass_ledger`). -/
theorem joint_grade_assembly {g : ℕ → ℂ} {t₀ X h c₀ y η L M : ℝ} {supF : ℝ → ℝ → ℝ}
    {Kfun : ℝ → ℝ}
    (hη0 : 0 ≤ η) (_hEML0 : 0 ≤ (1 + M) * Real.exp (-M) * L)
    (hJ1 : ‖prop21RHS g t₀ X h c₀ y η‖
        ≤ (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            supF α β * crossKer g X h y c₀ t₀ α β)
    (hJ2 : ∀ α ∈ Icc (0 : ℝ) η,
        (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
          ≤ Kfun α * ((1 + M) * Real.exp (-M) * L))
    (hIα : IntervalIntegrable
        (fun α => ∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β) volume 0 η)
    (hKI : IntervalIntegrable Kfun volume 0 η) :
    ‖prop21RHS g t₀ X h c₀ y η‖
      ≤ ((1 / Real.pi) * L * ∫ α in (0 : ℝ)..η, Kfun α) * ((1 + M) * Real.exp (-M)) := by
  refine hJ1.trans ?_
  have hπ0 : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  -- α-integral: ∫α∫β ≤ ∫α (Kfun α · EML) = (∫α Kfun)·EML
  have hmono : (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
      ≤ ∫ α in (0 : ℝ)..η, Kfun α * ((1 + M) * Real.exp (-M) * L) :=
    intervalIntegral.integral_mono_on hη0 hIα (hKI.mul_const _) hJ2
  have hpull : (∫ α in (0 : ℝ)..η, Kfun α * ((1 + M) * Real.exp (-M) * L))
      = (∫ α in (0 : ℝ)..η, Kfun α) * ((1 + M) * Real.exp (-M) * L) :=
    intervalIntegral.integral_mul_const _ _
  calc (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          supF α β * crossKer g X h y c₀ t₀ α β
      ≤ (1 / Real.pi) * ∫ α in (0 : ℝ)..η, Kfun α * ((1 + M) * Real.exp (-M) * L) :=
        mul_le_mul_of_nonneg_left hmono hπ0
    _ = ((1 / Real.pi) * L * ∫ α in (0 : ℝ)..η, Kfun α) * ((1 + M) * Real.exp (-M)) := by
        rw [hpull]; ring

/-! ## HGRADE — the `Tsplit`-sharp kernel L¹ mass (`kernel_L1_mass_sharp`)

The sharpening flagged in `kernel_mass_ledger` (HExit) and named as the `hgrade` residual of
`hRHS_discharged_joint`.  The crude ledger (`kernel_L1_mass`) uses the DOMINANT (Poisson,
`1/‖s‖²`) branch of `hat_mellin_bound` on the FULL line, giving
`∫_t ‖hatKernel X h c t‖ ≤ (X+h)^c·(2(X+h)/h)·(π/c) ≍ (X+h)^c·√L` at the pin `h = X·L^{−1/2}`
(the known `√L` excess).  The SHARP route splits the `t`-integral at `±T`:

* **main** `|t| ≤ T`: branch-1 (`2/‖s‖`) of `hat_mellin_bound` →
  `∫_{−T}^{T} (X+h)^c·2/√(c²+t²) dt = 4(X+h)^c·arsinh(T/c)` (the `arsinh` antiderivative,
  `integral_inv_sqrt_c_sq_add`, is the piece the crude ledger lacked);
* **tail** `|t| > T`: branch-2 (`hat_tail`, both sides by evenness) →
  `4(X+h)^{c+1}/(hT) = (X+h)^c·4(X+h)/(hT)`.

Assembly: `∫_t ‖hatKernel X h c t‖ ≤ (X+h)^c·(4·arsinh(T/c) + 4(X+h)/(hT))`.

**Grade page (worked before Lean — the α-decay resolution, and the honest deficit).**
`L := log X`, `h = X·L^{−1/2}`, `c₀ = 1+1/L`, `c = c₀−α−β ≍ 1`, `T = Tsplit = L⁴`:
`arsinh(T/c) ≍ log(2L⁴) ≍ 4 log L` and `4(X+h)/(hT) ≍ 4√L/L⁴ = 4 L^{−7/2}` (negligible), so the
per-line sharp mass is `(X+h)^c·Θ(log L)` — the crude `√L` is genuinely replaced by `log L`
(the tightest bound `hat_mellin_bound` yields: the `min`-mass of the truncation kernel is
`Θ((X+h)^c·log((X+h)/h))`, the classical Perron-truncation `log`).  The α-integral keeps the
`(X+h)^{−α}` decay: `∫₀^η (X+h)^{−α} dα = (1−(X+h)^{−η})/log(X+h) ≤ 1/L` (GHS's `x^{−α}` α-decay).
So the α-integrated kernel-scale mass is `(X+h)^{c₀−β}·Θ(log L)·(1/L) ≍ X·(log L)/L`, and
`Agrade := (1/π)·L·∫₀^η Kα dα ≍ X·log L = X·log log X`.

**The J3 socket `Agrade ≤ C₁·X` (constant `C₁`) therefore does NOT discharge via this route:**
a genuine `log log X` factor survives — the intrinsic L¹ mass of the ramp-truncation kernel
(ratio `(X+h)/h ≍ √L`).  Per iron rule 1 and the SF-EXIT law ("if the grade page shows a
log-power gap, STOP with the exact deficit — never force"), the socket is NOT forced here.  The
constant-`X` grade is reachable only by the mixed-line Plancherel bridge (`hbridge`, the OTHER
named residual), which diagonalizes the kernel WITH the window legs and never incurs the
standalone mass.  `kernel_L1_mass_sharp` stands as the honest shelf stone: the machine-checked
`√L → log L` sharpening, and the concrete substantiation of the `log log X` deficit. -/

/-- The full-line antiderivative of `1/√(c²+t²)` (`c > 0`) is `arsinh(t/c)`. -/
lemma hasDerivAt_arsinh_div {c : ℝ} (hc : 0 < c) (t : ℝ) :
    HasDerivAt (fun t => Real.arsinh (t / c)) ((Real.sqrt (c ^ 2 + t ^ 2))⁻¹) t := by
  have hbase := Real.hasDerivAt_arsinh (t / c)
  have hinner : HasDerivAt (fun t : ℝ => t / c) c⁻¹ t := by
    simpa using (hasDerivAt_id t).div_const c
  have hcomp := hbase.comp t hinner
  have hsimp : (Real.sqrt (1 + (t / c) ^ 2))⁻¹ * c⁻¹ = (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ := by
    have hkey : Real.sqrt (c ^ 2 + t ^ 2) = c * Real.sqrt (1 + (t / c) ^ 2) := by
      rw [show c * Real.sqrt (1 + (t / c) ^ 2) = Real.sqrt (c ^ 2 * (1 + (t / c) ^ 2)) by
            rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]]
      congr 1
      field_simp
    rw [hkey, mul_inv]; ring
  rwa [hsimp] at hcomp

/-- **The `arsinh` main-part evaluation.**  `∫_{−T}^{T} (c²+t²)^{−1/2} dt = 2·arsinh(T/c)`
(`c > 0`) — the branch-1 kernel-mass piece the crude `kernel_L1_mass` ledger lacked. -/
lemma integral_inv_sqrt_c_sq_add {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ = 2 * Real.arsinh (T / c) := by
  have hcont : Continuous (fun t : ℝ => (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) := by
    apply Continuous.inv₀
    · exact (Real.continuous_sqrt.comp (by fun_prop))
    · intro t; positivity
  have hint : IntervalIntegrable (fun t : ℝ => (Real.sqrt (c ^ 2 + t ^ 2))⁻¹)
      volume (-T) T := hcont.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_arsinh_div hc t) hint]
  rw [show (-T) / c = -(T / c) by ring, Real.arsinh_neg]
  ring

/-- **Branch-1 pointwise** (`|t| ≤ Tsplit` regime): `‖hatKernel X h c t‖ ≤ (X+h)^c·2/√(c²+t²)`
(the `2/‖s‖` branch of `hat_mellin_bound`, `‖s‖ = √(c²+t²)`). -/
lemma hatKernel_branch1 {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖ ≤ (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ := by
  have hb := hat_mellin_bound hX hh hc t
  have hnorm : ‖(c : ℂ) + (t : ℂ) * I‖ = Real.sqrt (c ^ 2 + t ^ 2) := Complex.norm_add_mul_I c t
  have hXh : (0 : ℝ) < X + h := by linarith
  calc ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
          (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := hb
    _ ≤ (X + h) ^ c * (2 / ‖(c : ℂ) + (t : ℂ) * I‖) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg hXh.le c)
    _ = (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ := by
        rw [hnorm, div_eq_mul_inv]; ring

/-- **Branch-2 pointwise** (the tail regime): `‖hatKernel X h c t‖ ≤ 2(X+h)^{c+1}/(h(c²+t²))`
(the dominant `1/‖s‖²` branch — matches `hat_tail`'s integrand). -/
lemma hatKernel_branch2 {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖ ≤ 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) := by
  have hb := hat_mellin_bound hX hh hc t
  have hnorm2 : ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hXh : (0 : ℝ) < X + h := by linarith
  calc ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
          (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := hb
    _ ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hXh.le c)
    _ = 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) := by
        rw [hnorm2, Real.rpow_add hXh, Real.rpow_one]; ring

/-- The branch-2 dominating function is `L¹` on the whole line (`(c²+t²)⁻¹` scaled). -/
lemma integrable_branch2 {X h c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))) := by
  have h0 : (fun t : ℝ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)))
      = fun t : ℝ => (2 * (X + h) ^ (c + 1) / h) * (c ^ 2 + t ^ 2)⁻¹ := by
    funext t; rw [div_mul_eq_div_div, div_eq_mul_inv]
  rw [h0]
  exact (Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul _

/-- **HGRADE — the `Tsplit`-sharp kernel L¹ mass (`kernel_L1_mass_sharp`).**  For any split
height `T > 0`,

  `∫_t ‖hatKernel X h c t‖ dt ≤ (X+h)^c·(4·arsinh(T/c) + 4(X+h)/(hT))`.

Branch-1 (`arsinh`, `integral_inv_sqrt_c_sq_add`) on `|t| ≤ T`; branch-2 (`hat_tail`, both
tails by evenness) on `|t| > T`.  At `h = X·L^{−1/2}`, `T = L⁴`, `c ≍ 1` this is
`(X+h)^c·Θ(log L)` — the honest `√L → log L` sharpening of `kernel_L1_mass`.  See the section
docstring for the grade page: the surviving `log log X` is intrinsic (the truncation kernel's
L¹ mass), so this does NOT discharge the constant-`X` `Agrade` socket — the STOP is recorded,
not forced. -/
theorem kernel_L1_mass_sharp {X h c T : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (hT : 0 < T) :
    ∫ t : ℝ, ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * (4 * Real.arsinh (T / c) + 4 * (X + h) / (h * T)) := by
  have hXh : (0 : ℝ) < X + h := by linarith
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hInt : Integrable (fun t : ℝ => ‖hatKernel X h c t‖) :=
    (integrable_hatKernel hX hh hc).norm
  have hb2int : Integrable (fun t : ℝ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))) :=
    integrable_branch2 hc
  have hpow : (X + h) ^ (c + 1) = (X + h) ^ c * (X + h) := by
    rw [Real.rpow_add hXh, Real.rpow_one]
  -- MIDDLE part: the arsinh main mass
  have hmid : (∫ t in Ioc (-T) T, ‖hatKernel X h c t‖)
      ≤ (X + h) ^ c * (4 * Real.arsinh (T / c)) := by
    rw [← intervalIntegral.integral_of_le hTle]
    have hKcont : IntervalIntegrable (fun t : ℝ => ‖hatKernel X h c t‖) volume (-T) T :=
      hInt.intervalIntegrable
    have hbr1 : IntervalIntegrable
        (fun t : ℝ => (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) volume (-T) T := by
      apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      apply Continuous.inv₀
      · exact Real.continuous_sqrt.comp (by fun_prop)
      · intro t; positivity
    calc ∫ t in (-T)..T, ‖hatKernel X h c t‖
        ≤ ∫ t in (-T)..T, (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ :=
          intervalIntegral.integral_mono_on hTle hKcont hbr1
            (fun t _ => hatKernel_branch1 hX hh hc t)
      _ = (X + h) ^ c * 2 * ∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ :=
          intervalIntegral.integral_const_mul _ _
      _ = (X + h) ^ c * 2 * (2 * Real.arsinh (T / c)) := by rw [integral_inv_sqrt_c_sq_add hc]
      _ = (X + h) ^ c * (4 * Real.arsinh (T / c)) := by ring
  -- RIGHT tail
  have htail_r : (∫ t in Ioi T, ‖hatKernel X h c t‖) ≤ (X + h) ^ c * (2 * (X + h) / (h * T)) := by
    calc ∫ t in Ioi T, ‖hatKernel X h c t‖
        ≤ ∫ t in Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2int.integrableOn measurableSet_Ioi
            (fun t _ => hatKernel_branch2 hX hh hc t)
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T) := hat_tail hX hh hc hT
      _ = (X + h) ^ c * (2 * (X + h) / (h * T)) := by rw [hpow]; ring
  -- LEFT tail (evenness of the branch-2 dominator)
  have htail_l : (∫ t in Iic (-T), ‖hatKernel X h c t‖)
      ≤ (X + h) ^ c * (2 * (X + h) / (h * T)) := by
    have heven : (∫ t in Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)))
        = ∫ t in Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) := by
      rw [show (∫ t in Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)))
            = ∫ t in Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + (-t) ^ 2)) from
          setIntegral_congr_fun measurableSet_Iic (fun t _ => by rw [neg_sq])]
      rw [integral_comp_neg_Iic (-T) (fun t => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)))]
      rw [neg_neg]
    calc ∫ t in Iic (-T), ‖hatKernel X h c t‖
        ≤ ∫ t in Iic (-T), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2int.integrableOn measurableSet_Iic
            (fun t _ => hatKernel_branch2 hX hh hc t)
      _ = ∫ t in Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2)) := heven
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T) := hat_tail hX hh hc hT
      _ = (X + h) ^ c * (2 * (X + h) / (h * T)) := by rw [hpow]; ring
  -- ASSEMBLE the three regions
  have hsplit1 : (∫ t : ℝ, ‖hatKernel X h c t‖)
      = (∫ t in Iic (-T), ‖hatKernel X h c t‖) + ∫ t in Ioi (-T), ‖hatKernel X h c t‖ :=
    (intervalIntegral.integral_Iic_add_Ioi hInt.integrableOn hInt.integrableOn).symm
  have hsplit2 : (∫ t in Ioi (-T), ‖hatKernel X h c t‖)
      = (∫ t in Ioc (-T) T, ‖hatKernel X h c t‖) + ∫ t in Ioi T, ‖hatKernel X h c t‖ := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          hInt.integrableOn hInt.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hTle]
  rw [hsplit1, hsplit2]
  calc (∫ t in Iic (-T), ‖hatKernel X h c t‖)
        + ((∫ t in Ioc (-T) T, ‖hatKernel X h c t‖) + ∫ t in Ioi T, ‖hatKernel X h c t‖)
      ≤ (X + h) ^ c * (2 * (X + h) / (h * T))
        + ((X + h) ^ c * (4 * Real.arsinh (T / c)) + (X + h) ^ c * (2 * (X + h) / (h * T))) := by
        gcongr
    _ = (X + h) ^ c * (4 * Real.arsinh (T / c) + 4 * (X + h) / (h * T)) := by ring

end Salt.MR

/-! ## BRIDGE — the S-ladder shelf stones for the `hbridge` discharge (BRIDGE-EXEC, 2026-07-23)

Two route-independent building blocks for the confirmed CS+Lorentzian route to `hbridge`
(`sigma_wiring`'s mixed-line residual): the pointwise Lorentzian comparison `lorentz_compare`
(kernel leg) and the decoupled weighted Cauchy–Schwarz `mixed_weight_cs` (the `k4_cross_CS`
Hölder-2-2 pattern with the weight peeled off the line, so the two window legs may sit on the
DISTINCT lines `c₀∓β`).  Both land unconditionally.  The full discharge is NOT completed —
see the residual record after `mixed_weight_cs` for the exact structural gap (append-only; the
STOP comment at `:35-43` stands unrewritten — the residual is isolated, not dissolved). -/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-- **S3 — the pointwise Lorentzian comparison (`lorentz_compare`).**  For a general pair
`0 < a ≤ b`, the Poisson/Lorentzian at the inner line `a` is dominated by the one at the outer
line `b`, paying the sup factor `(b/a)²` (attained at `τ = 0`):

  `1/(a²+τ²) ≤ (b/a)²·1/(b²+τ²)`.

Elementary: cross-multiplying reduces to `a²τ² ≤ b²τ²`, i.e. `a² ≤ b²`.  This is the kernel
leg of the S-ladder — the hat kernel's Lorentzian `1/((c₀−α−β)²+τ²)` (from `norm_hatKernel_le`)
is replaced by the leg Lorentzians at `b = c₀∓β` (both `≥ a = c₀−α−β` since `α, β ≥ 0`), so a
single `∫‖P₋‖‖P₊‖·K` splits into the two diagonal weights `k4_plan_le_diag_sharp` consumes. -/
theorem lorentz_compare {a b τ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / (a ^ 2 + τ ^ 2) ≤ (b / a) ^ 2 / (b ^ 2 + τ ^ 2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha2 : (0 : ℝ) < a ^ 2 + τ ^ 2 := by positivity
  have hb2 : (0 : ℝ) < b ^ 2 + τ ^ 2 := by positivity
  have hab2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rw [div_le_div_iff₀ ha2 hb2, one_mul, div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
  nlinarith [mul_nonneg (sq_nonneg τ) (sub_nonneg.mpr hab2)]

/-- **S2 — the decoupled weighted Cauchy–Schwarz (`mixed_weight_cs`).**  The `k4_cross_CS`
Hölder-2-2 pattern with the weight `w` DECOUPLED from the line (so the two legs may live on
distinct lines — the mixed-line content of `crossKer`): for `w ≥ 0` and nonneg `f, g` whose
`√w`-scalings are `L²`,

  `∫ f·g·w ≤ √(∫ f²·w)·√(∫ g²·w)`.

Setting `u = f·√w`, `v = g·√w` gives `u·v = f·g·w`, `u² = f²·w`, `v² = g²·w`, and the bound is
`integral_mul_le_Lp_mul_Lq_of_nonneg` at the self-conjugate exponent `2`.  The `L²` sockets are
supplied for the window legs by `k4Poly_sqInt` (with `w` the kernel's Poisson weight). -/
theorem mixed_weight_cs {f g w : ℝ → ℝ}
    (hw : ∀ t, 0 ≤ w t) (hfnn : ∀ t, 0 ≤ f t) (hgnn : ∀ t, 0 ≤ g t)
    (hu : MemLp (fun t => f t * Real.sqrt (w t)) 2 volume)
    (hv : MemLp (fun t => g t * Real.sqrt (w t)) 2 volume) :
    (∫ t : ℝ, f t * g t * w t)
      ≤ Real.sqrt (∫ t : ℝ, f t ^ 2 * w t) * Real.sqrt (∫ t : ℝ, g t ^ 2 * w t) := by
  set u : ℝ → ℝ := fun t => f t * Real.sqrt (w t) with hudef
  set v : ℝ → ℝ := fun t => g t * Real.sqrt (w t) with hvdef
  have huv : ∀ t, u t * v t = f t * g t * w t := fun t => by
    simp only [hudef, hvdef]; rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw t)]
  have husq : ∀ t, u t ^ (2 : ℝ) = f t ^ 2 * w t := fun t => by
    simp only [hudef]; rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw t)]
  have hvsq : ∀ t, v t ^ (2 : ℝ) = g t ^ 2 * w t := fun t => by
    simp only [hvdef]; rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw t)]
  have hunn : (0 : ℝ → ℝ) ≤ᵐ[volume] u :=
    Filter.Eventually.of_forall (fun t => by
      simp only [Pi.zero_apply, hudef]; exact mul_nonneg (hfnn t) (Real.sqrt_nonneg _))
  have hvnn : (0 : ℝ → ℝ) ≤ᵐ[volume] v :=
    Filter.Eventually.of_forall (fun t => by
      simp only [Pi.zero_apply, hvdef]; exact mul_nonneg (hgnn t) (Real.sqrt_nonneg _))
  have hu2 : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]; exact hu
  have hv2 : MemLp v (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]; exact hv
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hunn hvnn hu2 hv2
  have eLHS : (∫ t : ℝ, f t * g t * w t) = ∫ t : ℝ, u t * v t :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => (huv t).symm))
  have eA : (∫ t : ℝ, u t ^ (2 : ℝ)) = ∫ t : ℝ, f t ^ 2 * w t :=
    integral_congr_ae (Filter.Eventually.of_forall husq)
  have eB : (∫ t : ℝ, v t ^ (2 : ℝ)) = ∫ t : ℝ, g t ^ 2 * w t :=
    integral_congr_ae (Filter.Eventually.of_forall hvsq)
  rw [eLHS, ← eA, ← eB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hholder

/-! ## The `hbridge` discharge — RESIDUAL RECORD (BRIDGE-EXEC, VERIFY-FIRST outcome)

The three paper gates all PASS in shape — but the discharge into the ABSTRACT `hbridge` binder
of `sigma_wiring` is blocked at the wiring level by structure ABSENT from that binder's
signature.  Recorded here so the next session inherits the exact gap, not a re-derivation.

**Gate (a) — per-leg diagonal power (PASS).**  With `c₀ = 1 + 1/L` (the standing GHS base, cf.
`DistHalasz`'s `1 + 1/log x`): the low leg sits at `c₀−β = 1 − (β−1/L)`, the high leg at
`c₀+β = 1 + σ`, `σ = β+1/L`.  `k4_plan_le_diag_sharp` at line `c₀∓β` gives `(π/(c₀∓β))·S∓²` with
`S∓ = ∑_{y<n<X/y} ‖lambdaLin (restrictAbove y g) n‖/n^{c₀∓β}` (`norm_windowSum_le_mass`).  The
honest window evaluations (`‖λ_ℓ‖ ≤ Λ`, `mertens_first_upper` for the prime part `∑_{y<n<X/y}
Λ(n)/n ≤ log(X/y)+C`, plus the bounded `k≥2` prime-power tail):
  `S₋ ≤ (X/y)^{max(β−1/L,0)}·(L+C)`,   `S₊ ≤ y^{−σ}·(L+C)`.

**Gate (b) — the product at every regime corner (PASS, with slack).**  Target
`S₋·S₊ ≤ C·(X/y)^{2β}·min(L,1/σ)²`.  Since `σ ≥ 1/L`, `min(L,1/σ) = 1/σ` throughout, so the
target is `C·(X/y)^{2β}/σ²`.  Writing the honest product's power in `X,y`-exponents:
  β ≥ 1/L:  `S₋·S₊ ≤ (X/y)^{β−1/L}·y^{−σ}·(L+C)² = X^{β−1/L}·y^{−2β}·(L+C)²`,
so `(S₋·S₊)/target = X^{−σ}·((L+C)σ)²/C = e^{−Lσ}·((L+C)σ)²/C` (using `L = log X`), and with
`v := Lσ ≥ 1`, `e^{−v}·(v+Cσ)²` is bounded by an ABSOLUTE constant — the exponential power
decay `X^{−σ}` kills the `(Lσ)²` overshoot.  The CRUDE Mertens `L` (not the sharp `1/σ`) already
suffices.  β < 1/L: `S₋·S₊ ≤ y^{−2/L}·(L+C)²`, `(L+C)σ = Lβ+1+O(1) = O(1)` (`β<1/L`), and the
power ratio `y^{2β−2/L}·X^{−2β} ≤ 1`, so bounded again; at the corner `β=0, y=1` the ratio → 1
(the tight corner).  The WORST corner `β=η, y=√X` is the EMPTY window (`X/y = y`), `S∓ = 0`,
`0 ≤ RHS`.  No regime overshoots — the honest product is `≤ target` with an absolute constant.

**Gate (c) — the Kα absorption (PASS, explicit).**  Chaining S3 (`lorentz_compare`) inside S2
(`mixed_weight_cs`) with weight `w = ‖hatKernel X h (c₀−α−β)‖`, `a := c₀−α−β`, `B(a) :=
2(X+h)^{a+1}/h` (`norm_hatKernel_le`), `b∓ = c₀∓β`:
  `crossKer α β ≤ B(a)·(π/a²)·√((c₀−β)(c₀+β))·(S₋·S₊)`,
so the uniform per-`(α,β)` constant over the box `0 < c₀−2η` is
  `Kα(α,β) = B(a)·(π/a²)·√((c₀−β)(c₀+β))·C`  (all factors bounded on the box).

**THE GAP (why `sigma_wiring_unconditional` does NOT stand).**  `sigma_wiring` carries `X, L, c₀,
y, η` as FREE reals (only `1 ≤ X`, `3 ≤ L`, `0 < c₀−2η`, `1/L ≤ 2η`).  The discharge needs, and
the binder does NOT provide:
  1. the parameter relations `c₀ = 1 + 1/L` and `L ≤ log X` — the latter is LOAD-BEARING (it is
     what turns `X^{−σ}` into `e^{−Lσ}` to kill `(Lσ)²`; without it gate (b) is false);
  2. the σ-range: `σ = β+1/L` maps `β ∈ [0,η]` to `[1/L, η+1/L]`, but the target integral runs to
     `2η` (the "σ = 2η scale-mismatch" flagged in `supf-design.md`).  Closing it needs `1/L ≤ η`
     (so `η+1/L ≤ 2η`) AND `Fbound ≥ 0` on `[η+1/L, 2η]` to extend the reparametrized integral
     upward — neither is in the binder.
  3. `Fbound` and `supF` are ABSTRACT parameters here; a genuine discharge must INSTANTIATE
     `Fbound σ := (S-ladder integrand at β = σ−1/L)` and then re-prove `hpret`/`htriv` for THAT
     concrete `Fbound` — which is exactly SupF's PENDING pretentious residual (`supf-design.md`,
     SF-2/SF-3, on HOLD).

Hence `hbridge` is dischargeable only in a DOWNSTREAM lemma that first fixes `c₀ = 1+1/L`,
`L = log X`, `η = 1/log y`, `1/L ≤ η`, and supplies the concrete `Fbound` from SupF — NOT at the
abstraction of `sigma_wiring`.  The S-ladder itself (S3 ∘ S2 ∘ S5 ∘ gate (c)) is sound and its
two mechanical stones are landed above; S5 (`window_mass_product`) and S6 (`hbridge_discharge`)
await that parameter-pinned home.  This is the VERIFY-FIRST STOP: the excess is zero (no regime
corner overshoots), the block is the missing binder structure. -/

/-! ## J2′ — the OFF-DIAGONAL-KEPT window evaluation (`offdiag_window_eval`)

The K4' Plancherel residual, now DISCHARGED (`dirichlet_plancherel`, `HalaszContour`), lands
the window bilinear form as an EXACT double sum

  `∫ ‖P(c+it)‖²/(c²+t²) dt = (π/c)·∑_{m,n∈F} Re(b_m·conj b_n)/(mn)^c·e^{−c·|log m − log n|}`.

`k4_plan_le_diag_sharp` (`HalaszHead`) collapses the off-diagonal factor
`e^{−c·|log m − log n|} ≤ 1` and reaches the DIAGONAL `(π/c)·(∑ ‖b_n‖/n^c)²` — the window mass
SQUARED (`≍ L²`).  This stone KEEPS the off-diagonal decay and recovers one factor `L`: for a
line `c ≥ 1` and `Λ`-bounded coefficients (`‖b_n‖ ≤ Λ(n)`, e.g. `b = lambdaLin (restrictAbove
y g)` via `lambdaLin_norm_le`), the double sum is bounded by the SINGLE mass times an absolute
constant.

The mechanism is the exact identity `e^{−c·|log m − log n|}/(mn)^c = 1/max(m,n)^{2c}`
(for `m ≤ n`: `1/n^{2c}`), which turns the bilinear form into `∑_{m,n} ‖b_m‖‖b_n‖/max(m,n)^{2c}`.
Symmetrizing and summing the smaller index against the Chebyshev bound
`∑_{m≤n} Λ(m) = ψ(n) ≤ (log 4 + 4)·n` (`Chebyshev.psi_le_const_mul_self`) collapses the inner
sum to `(log 4 + 4)·n`, and `n·n^{−2c} ≤ n^{−c}` (`c ≥ 1`) leaves exactly the single mass:

  `∑_{m,n∈F} Re(b_m·conj b_n)/(mn)^c·e^{−c·|log m−log n|} ≤ 2(log 4 + 4)·∑_{n∈F} ‖b_n‖/n^c`.

NO GRADE CLAIM: `2(log 4 + 4)` is an absolute constant, and the single mass `∑ Λ(n)/n^c ≍ L` is
the honest window mass (the `L²→L` recovery over the diagonal, not a bound on `M`).  The
`1/c'`-band factor of the scoping is absorbed into the constant here because `c ≥ 1` makes the
banded geometric sum `O(1)`.  **Route note.** SHARP-SCOPE routed this through a `k`-band split
against `shortInterval_vonMangoldt_le`; the `1/max^{2c}`-identity + Chebyshev route below reaches
the same single-`L` exit with no band combinatorics or regime checks, so it is used instead.
Stated at a general line `c ≥ 1` (covers the base `c₀ = 1 + 1/L` and the high leg `c₀ + β`);
the low leg `c₀ − β < 1` needs the `c ≥ 1` hypothesis relaxed and is left as the assembly's
shift step (the scoper's honest note). -/

/-- The symmetric, nonnegative off-diagonal kernel of the window bilinear form:
`‖b_m‖‖b_n‖/(mn)^c·e^{−c·|log m − log n|}`. -/
private noncomputable def offdiagKer (b : ℕ → ℂ) (c : ℝ) (m n : ℕ) : ℝ :=
  ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
    * Real.exp (-(c * |Real.log m - Real.log n|))

/-- For a SYMMETRIC nonnegative kernel `T`, the full double sum is at most twice its
lower-triangular part (the swap `m ↔ n` maps the strict-upper part onto the strict-lower). -/
private lemma sum_sym_le_two_lower {F : Finset ℕ} {T : ℕ → ℕ → ℝ}
    (hsymm : ∀ m n, T m n = T n m) (hnn : ∀ m n, 0 ≤ T m n) :
    ∑ m ∈ F, ∑ n ∈ F, T m n
      ≤ 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0) := by
  have hle : ∀ m ∈ F, ∀ n ∈ F,
      T m n ≤ (if m ≤ n then T m n else 0) + (if n ≤ m then T n m else 0) := by
    intro m _ n _
    by_cases h : m ≤ n
    · rw [if_pos h]
      have h0 : (0 : ℝ) ≤ (if n ≤ m then T n m else 0) := by
        split_ifs with h'
        · exact hnn n m
        · exact le_refl 0
      linarith
    · have hnm : n ≤ m := (not_le.mp h).le
      rw [if_neg h, if_pos hnm, hsymm n m]
      linarith
  calc ∑ m ∈ F, ∑ n ∈ F, T m n
      ≤ ∑ m ∈ F, ∑ n ∈ F,
          ((if m ≤ n then T m n else 0) + (if n ≤ m then T n m else 0)) :=
        Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hle m hm n hn))
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0))
          + (∑ m ∈ F, ∑ n ∈ F, (if n ≤ m then T n m else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0))
          + (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0)) := by
        congr 1
        exact Finset.sum_comm
    _ = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0) := by ring

/-- **J2′ — the off-diagonal-kept window evaluation** (`offdiag_window_eval`).  For a line
`c ≥ 1`, a finite window `F` of positive integers, and `Λ`-bounded coefficients
`‖b_n‖ ≤ Λ(n)`, the window bilinear form (the RHS of `dirichlet_plancherel`, up to `π/c`) is
bounded by the SINGLE window mass times an absolute constant:
`∑_{m,n∈F} Re(b_m·conj b_n)/(mn)^c·e^{−c·|log m−log n|} ≤ 2(log 4 + 4)·∑_{n∈F} ‖b_n‖/n^c`.
This recovers one factor `L` over `k4_plan_le_diag_sharp`'s diagonal `(∑ ‖b_n‖/n^c)²`. -/
theorem offdiag_window_eval {F : Finset ℕ} {b : ℕ → ℂ} {c : ℝ} (hc : 1 ≤ c)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n) :
    (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(c * |Real.log m - Real.log n|)))
      ≤ 2 * (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  have hc0 : (0 : ℝ) < c := by linarith
  -- step 1: `Re(b_m conj b_n) ≤ ‖b_m‖‖b_n‖`, so the .re double sum ≤ the norm kernel sum
  have step1 : (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(c * |Real.log m - Real.log n|)))
        ≤ ∑ m ∈ F, ∑ n ∈ F, offdiagKer b c m n := by
    refine Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => ?_))
    simp only [offdiagKer]
    have hre : (b m * (starRingEnd ℂ) (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * (starRingEnd ℂ) (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(c * |Real.log m - Real.log n|)) := by positivity
    calc (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|))
        = (b m * (starRingEnd ℂ) (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(c * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(c * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  -- the kernel is symmetric and nonnegative
  have hTsymm : ∀ m n, offdiagKer b c m n = offdiagKer b c n m := by
    intro m n
    simp only [offdiagKer]
    rw [mul_comm (‖b m‖) (‖b n‖), Nat.mul_comm m n, abs_sub_comm (Real.log m) (Real.log n)]
  have hTnn : ∀ m n, 0 ≤ offdiagKer b c m n := by
    intro m n; simp only [offdiagKer]; positivity
  -- the identity `offdiagKer m n = ‖b_m‖·(‖b_n‖/n^{2c})` for `m ≤ n`
  have hident : ∀ m ∈ F, ∀ n ∈ F, m ≤ n →
      offdiagKer b c m n = ‖b m‖ * (‖b n‖ / (n : ℝ) ^ (2 * c)) := by
    intro m hm n hn hmn
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hF m hm
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
    have hlogle : Real.log m ≤ Real.log n := Real.log_le_log hm0 (by exact_mod_cast hmn)
    have habs : |Real.log m - Real.log n| = Real.log n - Real.log m := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hexp : Real.exp (-(c * (Real.log n - Real.log m))) = (m : ℝ) ^ c / (n : ℝ) ^ c := by
      rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0, ← Real.exp_sub]
      congr 1; ring
    have hmc : (m : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hm0 c).ne'
    have hnc : (n : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hn0 c).ne'
    simp only [offdiagKer]
    rw [habs, hexp,
      show ((m * n : ℕ) : ℝ) ^ c = (m : ℝ) ^ c * (n : ℝ) ^ c from by
        push_cast; rw [Real.mul_rpow hm0.le hn0.le],
      show (n : ℝ) ^ (2 * c) = (n : ℝ) ^ c * (n : ℝ) ^ c from by
        rw [two_mul, Real.rpow_add hn0]]
    field_simp
  -- the per-`n` Chebyshev collapse of the lower-triangular inner sum
  have hPn : ∀ n : ℕ, (∑ m ∈ F, (if m ≤ n then ‖b m‖ else 0)) ≤ (Real.log 4 + 4) * (n : ℝ) := by
    intro n
    rw [← Finset.sum_filter]
    have hsub : (F.filter (fun m => m ≤ n)) ⊆ Finset.Ioc 0 n := by
      intro m hmf
      rw [Finset.mem_filter] at hmf
      rw [Finset.mem_Ioc]
      exact ⟨hF m hmf.1, hmf.2⟩
    calc ∑ m ∈ F.filter (fun m => m ≤ n), ‖b m‖
        ≤ ∑ m ∈ F.filter (fun m => m ≤ n), ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum (fun m _ => hb m)
      _ ≤ ∑ k ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi (n : ℝ) := by
          rw [show Chebyshev.psi (n : ℝ)
              = ∑ k ∈ Finset.Ioc 0 ⌊(n : ℝ)⌋₊, ArithmeticFunction.vonMangoldt k from rfl,
            Nat.floor_natCast]
      _ ≤ (Real.log 4 + 4) * (n : ℝ) := Chebyshev.psi_le_const_mul_self (by positivity)
  -- the key bound: the lower-triangular kernel sum ≤ (log 4 + 4)·(single mass)
  have key : (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKer b c m n else 0))
      ≤ (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
    calc ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKer b c m n else 0)
        = ∑ n ∈ F, ∑ m ∈ F, (if m ≤ n then offdiagKer b c m n else 0) := Finset.sum_comm
      _ = ∑ n ∈ F, (‖b n‖ / (n : ℝ) ^ (2 * c)) * (∑ m ∈ F, if m ≤ n then ‖b m‖ else 0) := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          by_cases h : m ≤ n
          · rw [if_pos h, if_pos h, hident m hm n hn h, mul_comm]
          · rw [if_neg h, if_neg h, mul_zero]
      _ ≤ ∑ n ∈ F, (Real.log 4 + 4) * (‖b n‖ / (n : ℝ) ^ c) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF n hn
          have hKnn : (0 : ℝ) ≤ ‖b n‖ / (n : ℝ) ^ (2 * c) := by positivity
          have he1 : (n : ℝ) ^ (1 - 2 * c) = (n : ℝ) / (n : ℝ) ^ (2 * c) := by
            rw [Real.rpow_sub hn0, Real.rpow_one]
          have he2 : (n : ℝ) ^ (-c) = 1 / (n : ℝ) ^ c := by
            rw [Real.rpow_neg hn0.le, one_div]
          have hstep : (n : ℝ) / (n : ℝ) ^ (2 * c) ≤ 1 / (n : ℝ) ^ c := by
            rw [← he1, ← he2]
            exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
          calc (‖b n‖ / (n : ℝ) ^ (2 * c)) * (∑ m ∈ F, if m ≤ n then ‖b m‖ else 0)
              ≤ (‖b n‖ / (n : ℝ) ^ (2 * c)) * ((Real.log 4 + 4) * (n : ℝ)) :=
                mul_le_mul_of_nonneg_left (hPn n) hKnn
            _ = (Real.log 4 + 4) * (‖b n‖ * ((n : ℝ) / (n : ℝ) ^ (2 * c))) := by ring
            _ ≤ (Real.log 4 + 4) * (‖b n‖ * (1 / (n : ℝ) ^ c)) := by
                have hlog4 : (0 : ℝ) ≤ Real.log 4 + 4 := by positivity
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hstep (norm_nonneg _)) hlog4
            _ = (Real.log 4 + 4) * (‖b n‖ / (n : ℝ) ^ c) := by rw [mul_one_div]
      _ = (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by rw [Finset.mul_sum]
  -- assemble
  calc (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(c * |Real.log m - Real.log n|)))
      ≤ ∑ m ∈ F, ∑ n ∈ F, offdiagKer b c m n := step1
    _ ≤ 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKer b c m n else 0) :=
        sum_sym_le_two_lower hTsymm hTnn
    _ ≤ 2 * ((Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by ring

end Salt.MR
