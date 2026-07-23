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

end Salt.MR
