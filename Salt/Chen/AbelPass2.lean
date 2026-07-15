/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AbelPass

/-!
# AB2 — `I(u)`'s calculus, Application B, the change of variables, and the count composition

Design: `docs/blueprints/flags.md`, the CNT2 / AB1 entries.  This is the last analysis node
of the Chen count line.  It carries the `p₁`-Abel pass at the carrier

  `I(u) = ∫_y^{√(N/u)} h_u(t)/(t log t) dt`      (`Ifun`),

sends `∫_z^y I d(loglog)` to the switch constant `c̄` (landed `cbar_eq_double_integral`), and
composes the two Abel passes into the final `c̄/2` count.

## Dissolving the moving-boundary Leibniz wall (the AB1 flag's identified blocker)

`I(u)` has `u` in BOTH the integrand `h_u` and the upper limit `√(N/u)`, so a direct
derivative is a Leibniz moving-boundary computation with thin mathlib support.  We AVOID it:
the inner change of variables `t = N^σ` (monotone,
`intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg`) plus the landed partial-fraction
antiderivative gives the **closed form**

  `I(u) = log(2 − 3·log u/log N) / (log N − log u)`   (`Ifun_closed_form`, on `Ioo 0 N^{2/3}`),

whose `u`-derivative is a routine elementary `.div`/`.log` computation (`Ifuncf_hasDerivAt`),
transferred to `Ifun` by `HasDerivAt.congr_of_eventuallyEq` on the open band.  The
monotonicity finding: writing `P = 2 − 3β`, `β = log u/log N ∈ [1/8, 1/3]` on `[z, y]`, the
derivative sign reduces to `P log P ≤ 1 + P` for `P ∈ [1, 13/8]` — TRUE, so **`I` is globally
antitone on `[z, y]`** and the antitone Abel pass (`prime_sum_abel_antitone`) applies directly.
(Numerically verified: `I(u)` matches the closed form to ~1e−12; the derivative `< 0`
throughout the operating range.)

No `sorry`, no `native_decide`, no new axioms.
-/

open MeasureTheory intervalIntegral Set
open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the inner partial-fraction integral (neighbourhood version)

`cbar_inner_integral` (landed) evaluates the inner integral for `β ∈ [1/8, 1/3]`; for the
derivative we need a two-sided neighbourhood of `[1/8, 1/3]`, so we re-prove it for the open
condition `β < 2/3` (the only constraint the antiderivative needs). -/

/-- **The inner partial-fraction integral, neighbourhood form.**  For `β < 2/3`,
`∫_{1/3}^{(1-β)/2} 1/(σ(1 − β − σ)) dσ = log(2 − 3β)/(1 − β)`.  Same antiderivative
`F(σ) = (1−β)⁻¹(log σ − log(1 − β − σ))` as the landed `cbar_inner_integral`, but valid on
the open range (the interval may run backwards when `β > 1/3`). -/
theorem inner_pf_integral {β : ℝ} (hβ : β < 2 / 3) :
    ∫ σ in (1 / 3 : ℝ)..((1 - β) / 2), (σ * (1 - β - σ))⁻¹
      = Real.log (2 - 3 * β) / (1 - β) := by
  have hpos : ∀ σ ∈ Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2),
      (0 : ℝ) < σ ∧ (0 : ℝ) < 1 - β - σ := by
    intro σ hσ
    rw [Set.mem_uIcc] at hσ
    rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hderiv : ∀ σ ∈ Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2),
      HasDerivAt (fun s => (1 - β)⁻¹ * (Real.log s - Real.log (1 - β - s)))
        ((σ * (1 - β - σ))⁻¹) σ := by
    intro σ hσ
    obtain ⟨hσ0, h1βσ0⟩ := hpos σ hσ
    have hβ1 : (0 : ℝ) < 1 - β := by linarith
    have hd1 : HasDerivAt (fun s : ℝ => Real.log s) σ⁻¹ σ := Real.hasDerivAt_log hσ0.ne'
    have hinner : HasDerivAt (fun s : ℝ => 1 - β - s) (-1) σ := by
      simpa using (hasDerivAt_id σ).const_sub (1 - β)
    have hd2 : HasDerivAt (fun s : ℝ => Real.log (1 - β - s)) ((1 - β - σ)⁻¹ * (-1)) σ :=
      (Real.hasDerivAt_log h1βσ0.ne').comp σ hinner
    have hF := (hd1.sub hd2).const_mul (1 - β)⁻¹
    have hval : (1 - β)⁻¹ * (σ⁻¹ - (1 - β - σ)⁻¹ * (-1)) = (σ * (1 - β - σ))⁻¹ := by
      rw [mul_inv]; field_simp; ring
    rwa [hval] at hF
  have hcont : ContinuousOn (fun σ : ℝ => (σ * (1 - β - σ))⁻¹)
      (Set.uIcc (1 / 3 : ℝ) ((1 - β) / 2)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro σ hσ; obtain ⟨hσ0, h1βσ0⟩ := hpos σ hσ; positivity
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hkey]
  have htop : Real.log ((1 - β) / 2) - Real.log (1 - β - (1 - β) / 2) = 0 := by
    have : (1 : ℝ) - β - (1 - β) / 2 = (1 - β) / 2 := by ring
    rw [this]; ring
  have hbot : Real.log (1 / 3 : ℝ) - Real.log (1 - β - 1 / 3) = -Real.log (2 - 3 * β) := by
    have hpos23 : (0 : ℝ) < 2 - 3 * β := by linarith
    have h23 : (1 : ℝ) - β - 1 / 3 = (2 - 3 * β) / 3 := by ring
    rw [h23, Real.log_div hpos23.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]
    ring
  rw [htop, hbot]; ring

/-! ## Section 2 — the carrier `I(u)` and its closed form -/

/-- The BJS outer carrier `I(u) = ∫_y^{√(N/u)} h_u(t)/(t log t) dt` (`hbjs N u t = 1/log(N/ut)`,
the `d(log log t)` weight `/(t log t)`).  `y` is the fixed lower limit (parametric). -/
noncomputable def Ifun (N y u : ℝ) : ℝ :=
  ∫ t in y..(Real.sqrt (N / u)), hbjs N u t / (t * Real.log t)

/-- The numerator argument `P(u) = 2 − 3 log u/log N` of the closed form (`= 2 − 3β`). -/
noncomputable def IargA (N u : ℝ) : ℝ := 2 - 3 * Real.log u / Real.log N

/-- The denominator `Q(u) = log N − log u = log(N/u)` of the closed form. -/
noncomputable def IdenA (N u : ℝ) : ℝ := Real.log N - Real.log u

/-- The closed form `I(u) = log P(u)/Q(u) = log(2 − 3 log u/log N)/(log N − log u)`. -/
noncomputable def Ifun_cf (N u : ℝ) : ℝ := Real.log (IargA N u) / IdenA N u

/-- `I'(u)`, the closed-form derivative in its natural factored form
`u⁻¹·(log P − 3Q/(log N·P))/Q²`.  Using `3Q = (1 + P)·log N` this equals
`(P log P − (1 + P))/(P·u·Q²)`, so its sign is that of `P log P − (1 + P)`; on `[z, y]`
(`P ∈ [1, 13/8]`) this is `≤ 0` (`I` antitone). -/
noncomputable def Ifun_deriv (N u : ℝ) : ℝ :=
  u⁻¹ * (Real.log (IargA N u) - 3 * IdenA N u / (Real.log N * IargA N u)) / IdenA N u ^ 2

/-- **The closed form.**  For `1 < N`, `0 < y` with `log y = log N/3` (i.e. `y = N^{1/3}`),
`0 < u`, and `log u < (2/3) log N` (i.e. `u < N^{2/3}`),

  `I(u) = log(2 − 3 log u/log N)/(log N − log u)`.

Route: the monotone change of variables `t = exp(σ·log N)` (so `t = N^σ`) turns the
`d(log log)` integrand into `(log N)⁻¹·1/(σ(1 − β − σ))` with `β = log u/log N`, mapping
`[y, √(N/u)]` to `[1/3, (1−β)/2]`; then `inner_pf_integral`. -/
theorem Ifun_closed_form {N y u : ℝ} (hN : 1 < N) (hy0 : 0 < y)
    (hy : Real.log y = Real.log N / 3) (hu0 : 0 < u)
    (huM : Real.log u < 2 / 3 * Real.log N) :
    Ifun N y u = Ifun_cf N u := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogun : Real.log u < Real.log N := by linarith
  set β := Real.log u / Real.log N with hβdef
  have hβlt : β < 2 / 3 := by rw [hβdef, div_lt_iff₀ hLN]; linarith
  have hβ1 : (0 : ℝ) < 1 - β := by
    rw [hβdef]; rw [sub_pos, div_lt_one hLN]; linarith
  -- the substitution function φ σ = exp (σ · log N) and its derivative
  set φ : ℝ → ℝ := fun σ => Real.exp (σ * Real.log N) with hφ
  set φ' : ℝ → ℝ := fun σ => Real.exp (σ * Real.log N) * Real.log N with hφ'
  have hφderiv : ∀ σ : ℝ, HasDerivAt φ (φ' σ) σ := by
    intro σ
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log N) (Real.log N) σ := by
      simpa using (hasDerivAt_id σ).mul_const (Real.log N)
    simpa [hφ, hφ'] using h1.exp
  -- endpoints φ(1/3) = y, φ((1-β)/2) = √(N/u)
  have hφ13 : φ (1 / 3) = y := by
    rw [hφ]; simp only
    rw [show (1 / 3 : ℝ) * Real.log N = Real.log N / 3 by ring, ← hy]; exact Real.exp_log hy0
  have hNu : (0 : ℝ) < N / u := div_pos hNpos hu0
  have hφb : φ ((1 - β) / 2) = Real.sqrt (N / u) := by
    rw [hφ]; simp only
    have hexp : (1 - β) / 2 * Real.log N = Real.log (Real.sqrt (N / u)) := by
      rw [Real.log_sqrt hNu.le, Real.log_div hNpos.ne' hu0.ne', hβdef]
      field_simp
    rw [hexp]; exact Real.exp_log (Real.sqrt_pos.mpr hNu)
  -- change of variables (monotone: φ' ≥ 0)
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := φ') (g := fun s => hbjs N u s / (s * Real.log s))
    (a := 1 / 3) (b := (1 - β) / 2)
    (Continuous.continuousOn (by rw [hφ]; fun_prop))
    (fun x _ => hφderiv x)
    (fun x _ => by rw [hφ']; positivity)
  rw [hφ13, hφb] at hcov
  -- Ifun N y u = ∫ σ, (g ∘ φ) σ * φ' σ
  rw [Ifun, ← hcov]
  -- rewrite the integrand pointwise to (log N)⁻¹ · (σ(1-β-σ))⁻¹
  rw [intervalIntegral.integral_congr
      (g := fun σ => (Real.log N)⁻¹ * (σ * (1 - β - σ))⁻¹) ?_]
  · rw [intervalIntegral.integral_const_mul, inner_pf_integral hβlt]
    have h23 : (2 : ℝ) - 3 * β = 2 - 3 * Real.log u / Real.log N := by rw [hβdef]; ring
    rw [h23, Ifun_cf, IargA, IdenA, hβdef]
    have hQne : Real.log N - Real.log u ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlogun)
    have h1βne : (1 : ℝ) - Real.log u / Real.log N ≠ 0 := by
      rw [sub_ne_zero]; intro h
      rw [eq_comm, div_eq_one_iff_eq hLN.ne'] at h; linarith
    field_simp
  · -- the pointwise integrand identity
    intro σ hσ
    obtain ⟨hσ0, h1βσ0⟩ : (0 : ℝ) < σ ∧ (0 : ℝ) < 1 - β - σ := by
      rw [Set.mem_uIcc] at hσ
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hEpos : (0 : ℝ) < Real.exp (σ * Real.log N) := Real.exp_pos _
    have hlogexp : Real.log (Real.exp (σ * Real.log N)) = σ * Real.log N := Real.log_exp _
    have hlogarg : Real.log (N / (u * Real.exp (σ * Real.log N)))
        = Real.log N - Real.log u - σ * Real.log N := by
      rw [Real.log_div hNpos.ne' (by positivity), Real.log_mul hu0.ne' hEpos.ne', hlogexp]; ring
    have h1βσ0' : (0 : ℝ) < 1 - Real.log u / Real.log N - σ := by rw [hβdef] at h1βσ0; exact h1βσ0
    simp only [Function.comp, hbjs, hφ, hφ', hlogarg, hlogexp, hβdef]
    rw [eq_comm]
    have hEne : Real.exp (σ * Real.log N) ≠ 0 := hEpos.ne'
    have hden : Real.log N - Real.log u - σ * Real.log N ≠ 0 := by
      have heq : Real.log N - Real.log u - σ * Real.log N
          = Real.log N * (1 - Real.log u / Real.log N - σ) := by field_simp
      rw [heq]; exact mul_ne_zero hLN.ne' h1βσ0'.ne'
    field_simp

/-! ## Section 3 — the derivative calculus of the closed form -/

/-- **`I(u)`'s derivative.**  For `1 < N`, `0 < u`, `log u < (2/3) log N`,
`HasDerivAt (Ifun_cf N) (Ifun_deriv N u) u` — an elementary `.div`/`.log` computation. -/
theorem Ifuncf_hasDerivAt {N u : ℝ} (hN : 1 < N) (hu0 : 0 < u)
    (huM : Real.log u < 2 / 3 * Real.log N) :
    HasDerivAt (Ifun_cf N) (Ifun_deriv N u) u := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hP0 : 0 < IargA N u := by
    rw [IargA]
    have : 3 * Real.log u / Real.log N < 2 := by rw [div_lt_iff₀ hLN]; linarith
    linarith
  have hQ0 : 0 < IdenA N u := by
    rw [IdenA]; have : Real.log u < Real.log N := by linarith
    linarith
  have hlogu : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
  have hP : HasDerivAt (fun w => IargA N w) (-(3 * u⁻¹ / Real.log N)) u := by
    have h1 : HasDerivAt (fun w => 3 * Real.log w / Real.log N) (3 * u⁻¹ / Real.log N) u :=
      (hlogu.const_mul 3).div_const (Real.log N)
    have h2 := h1.const_sub 2
    simpa [IargA] using h2
  have hA : HasDerivAt (fun w => Real.log (IargA N w))
      ((-(3 * u⁻¹ / Real.log N)) / IargA N u) u := hP.log hP0.ne'
  have hB : HasDerivAt (fun w => IdenA N w) (-u⁻¹) u := by
    have := hlogu.const_sub (Real.log N)
    simpa [IdenA] using this
  have key : Ifun_deriv N u
      = (-(3 * u⁻¹ / Real.log N) / IargA N u * IdenA N u - Real.log (IargA N u) * -u⁻¹)
        / IdenA N u ^ 2 := by
    rw [Ifun_deriv]
    field_simp [hu0.ne', hLN.ne', hP0.ne', hQ0.ne']
    ring
  rw [key]
  exact hA.div hB hQ0.ne'

/-- **`I(u)`'s derivative (transferred to `Ifun`).**  `Ifun N y` agrees with the closed form
`Ifun_cf N` on the open band `Ioo 0 N^{2/3}`, so `HasDerivAt (Ifun N y) (Ifun_deriv N u) u` for
`u` in that band — this is the moving-boundary Leibniz derivative, obtained WITHOUT a
moving-boundary computation. -/
theorem Ifun_hasDerivAt {N y u : ℝ} (hN : 1 < N) (hy0 : 0 < y)
    (hy : Real.log y = Real.log N / 3) (hu0 : 0 < u)
    (huM : Real.log u < 2 / 3 * Real.log N) :
    HasDerivAt (Ifun N y) (Ifun_deriv N u) u := by
  have hM : u < Real.exp (2 / 3 * Real.log N) := by
    calc u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ < Real.exp (2 / 3 * Real.log N) := Real.exp_lt_exp.mpr huM
  have hEq : Set.EqOn (Ifun N y) (Ifun_cf N) (Set.Ioo 0 (Real.exp (2 / 3 * Real.log N))) := by
    intro v hv
    obtain ⟨hv0, hvM⟩ := hv
    have hvlog : Real.log v < 2 / 3 * Real.log N := by
      have := Real.log_lt_log hv0 hvM; rwa [Real.log_exp] at this
    exact Ifun_closed_form hN hy0 hy hv0 hvlog
  exact (Ifuncf_hasDerivAt hN hu0 huM).congr_of_eventuallyEq
    (hEq.eventuallyEq_of_mem (Ioo_mem_nhds hu0 hM))

/-- **`I` is antitone on `[z, y]`.**  For `log N/8 ≤ log u ≤ log N/3` (i.e. `u ∈ [N^{1/8},
N^{1/3}]`, so `P = 2 − 3β ∈ [1, 13/8]`), `Ifun_deriv N u ≤ 0`.  Reduces to `P log P ≤ 1 + P` on
`[1, 13/8]` via `log P ≤ P − 1` and `P² − 2P − 1 ≤ 0`. -/
theorem Ifun_deriv_nonpos {N u : ℝ} (hN : 1 < N) (hu0 : 0 < u)
    (hu_lo : Real.log N / 8 ≤ Real.log u) (hu_hi : Real.log u ≤ Real.log N / 3) :
    Ifun_deriv N u ≤ 0 := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hP_lo : (1 : ℝ) ≤ IargA N u := by
    rw [IargA]
    have : 3 * Real.log u / Real.log N ≤ 1 := by rw [div_le_iff₀ hLN]; linarith
    linarith
  have hP_hi : IargA N u ≤ 13 / 8 := by
    rw [IargA]
    have : (3 : ℝ) / 8 ≤ 3 * Real.log u / Real.log N := by rw [le_div_iff₀ hLN]; linarith
    linarith
  have hP0 : 0 < IargA N u := by linarith
  have hQ0 : 0 < IdenA N u := by
    rw [IdenA]; have : Real.log u < Real.log N := by linarith
    linarith
  have hlogP : Real.log (IargA N u) ≤ IargA N u - 1 := Real.log_le_sub_one_of_pos hP0
  have hkey : IargA N u * Real.log (IargA N u) - (1 + IargA N u) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogP hP0.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ 13 / 8 - IargA N u) (by linarith : (0:ℝ) ≤ IargA N u - 1)]
  -- the P-Q relation `3Q = (1 + P)·log N`, hence `3Q/(log N·P) = (1 + P)/P`
  have hR : 3 * IdenA N u = (1 + IargA N u) * Real.log N := by
    simp only [IargA, IdenA]; field_simp; ring
  have hfrac : 3 * IdenA N u / (Real.log N * IargA N u) = (1 + IargA N u) / IargA N u := by
    rw [hR]; field_simp
  simp only [Ifun_deriv]
  rw [hfrac]
  have hnum : Real.log (IargA N u) - (1 + IargA N u) / IargA N u ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hP0]; nlinarith [hkey]
  have hu0' : 0 < u⁻¹ := by positivity
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos hu0'.le hnum
  · positivity

/-- Continuity of `Ifun_deriv N` on `[z, y]` (all denominators bounded away from `0`), hence
interval-integrability. -/
theorem Ifun_deriv_intervalIntegrable {N z y : ℝ} (hN : 1 < N) (hz0 : 0 < z) (hzy : z ≤ y)
    (hy_hi : Real.log y < 2 / 3 * Real.log N) :
    IntervalIntegrable (Ifun_deriv N) MeasureTheory.volume z y := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hzy]
  have hmem : ∀ u ∈ Set.Icc z y, 0 < u ∧ Real.log u < 2 / 3 * Real.log N := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    refine ⟨hu0, ?_⟩
    have : Real.log u ≤ Real.log y := Real.log_le_log hu0 hu.2
    linarith [hy_hi]
  have hlogcont : ContinuousOn Real.log (Set.Icc z y) :=
    Real.continuousOn_log.mono (fun u hu => (hmem u hu).1.ne')
  have hIarg_cont : ContinuousOn (fun u => IargA N u) (Set.Icc z y) := by
    change ContinuousOn (fun u => 2 - 3 * Real.log u / Real.log N) (Set.Icc z y)
    exact continuousOn_const.sub ((hlogcont.const_mul 3).div_const (Real.log N))
  have hIden_cont : ContinuousOn (fun u => IdenA N u) (Set.Icc z y) := by
    change ContinuousOn (fun u => Real.log N - Real.log u) (Set.Icc z y)
    exact continuousOn_const.sub hlogcont
  have hP0 : ∀ u ∈ Set.Icc z y, 0 < IargA N u := by
    intro u hu
    obtain ⟨hu0, huM⟩ := hmem u hu
    rw [IargA]
    have : 3 * Real.log u / Real.log N < 2 := by rw [div_lt_iff₀ hLN]; linarith
    linarith
  have hQne : ∀ u ∈ Set.Icc z y, IdenA N u ≠ 0 := by
    intro u hu
    obtain ⟨hu0, huM⟩ := hmem u hu
    rw [IdenA]; exact sub_ne_zero.mpr (ne_of_gt (by linarith : Real.log u < Real.log N))
  change ContinuousOn (fun u => u⁻¹ * (Real.log (IargA N u)
    - 3 * IdenA N u / (Real.log N * IargA N u)) / IdenA N u ^ 2) (Set.Icc z y)
  have hLNP_ne : ∀ u ∈ Set.Icc z y, Real.log N * IargA N u ≠ 0 :=
    fun u hu => mul_ne_zero hLN.ne' (hP0 u hu).ne'
  apply ContinuousOn.div
  · apply ContinuousOn.mul
    · exact (continuousOn_inv₀.mono (fun u hu => (hmem u hu).1.ne'))
    · apply ContinuousOn.sub (hIarg_cont.log (fun u hu => (hP0 u hu).ne'))
      exact (continuousOn_const.mul hIden_cont).div (continuousOn_const.mul hIarg_cont) hLNP_ne
  · exact hIden_cont.pow 2
  · intro u hu; exact pow_ne_zero 2 (hQne u hu)

/-- **`I ≥ 0` on `[z, y]`.**  Via the closed form: on `[z, y]`, `P = 2 − 3 log t/log N ∈ [1, 13/8]`
so `log P ≥ 0`, and `Q = log N − log t > 0`. -/
theorem Ifun_nonneg {N y t : ℝ} (hN : 1 < N) (hy0 : 0 < y)
    (hy : Real.log y = Real.log N / 3) (ht0 : 0 < t)
    (ht_hi : Real.log t ≤ Real.log N / 3) :
    0 ≤ Ifun N y t := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have htM : Real.log t < 2 / 3 * Real.log N := by linarith
  rw [Ifun_closed_form hN hy0 hy ht0 htM, Ifun_cf]
  apply div_nonneg
  · apply Real.log_nonneg
    rw [IargA]
    have : 3 * Real.log t / Real.log N ≤ 1 := by rw [div_le_iff₀ hLN]; linarith
    linarith
  · rw [IdenA]; linarith

/-! ## Section 4 — Application B: the `p₁`-sum Abel pass at the carrier `I` (BJS Lemma 52) -/

/-- **Application B — the `p₁`-Abel pass on the carrier `I`.**  For `1 < N`, `0 < y` with
`log y = log N/3` (`y = N^{1/3}`), `2 ≤ z ≤ y` with `log z = log N/8` (`z = N^{1/8}`),

  `Σ_{p₁ ∈ [z,y) prime} I(p₁)/p₁ ≤ ∫_z^y I(t)/(t log t) dt + (21/log z)·I(z)`.

Direct instantiation of the antitone Abel pass (`prime_sum_abel_antitone`) at `f = I`, whose
four hypotheses are Floor A's calculus package (`Ifun_hasDerivAt`, `Ifun_deriv_intervalIntegrable`,
`Ifun_nonneg`, `Ifun_deriv_nonpos`). -/
theorem applicationB {N z y : ℝ} (hN : 1 < N) (hy0 : 0 < y)
    (hy : Real.log y = Real.log N / 3) (hz2 : 2 ≤ z) (hzy : z ≤ y)
    (hz : Real.log z = Real.log N / 8) :
    ∑ p₁ ∈ Salt.BrunLower.primesInWindow z y, Ifun N y p₁ / p₁
      ≤ (∫ t in z..y, Ifun N y t / (t * Real.log t)) + (21 / Real.log z) * Ifun N y z := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hz0 : 0 < z := by linarith
  have hbounds : ∀ t ∈ Set.Icc z y,
      0 < t ∧ Real.log N / 8 ≤ Real.log t ∧ Real.log t ≤ Real.log N / 3 := by
    intro t ht; rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨ht0, ?_, ?_⟩
    · calc Real.log N / 8 = Real.log z := hz.symm
        _ ≤ Real.log t := Real.log_le_log hz0 ht.1
    · calc Real.log t ≤ Real.log y := Real.log_le_log ht0 ht.2
        _ = Real.log N / 3 := hy
  refine prime_sum_abel_antitone hz2 hzy (f' := Ifun_deriv N) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht0, _, hthi⟩ := hbounds t ht
    exact Ifun_hasDerivAt hN hy0 hy ht0 (by linarith)
  · exact Ifun_deriv_intervalIntegrable hN hz0 hzy (by rw [hy]; linarith)
  · intro t ht
    obtain ⟨ht0, _, hthi⟩ := hbounds t ht
    exact Ifun_nonneg hN hy0 hy ht0 hthi
  · intro t ht
    obtain ⟨ht0, htlo, hthi⟩ := hbounds t ht
    exact Ifun_deriv_nonpos hN ht0 htlo hthi

/-! ## Section 5 — the change of variables `∫_z^y I d(loglog) = c̄/log N` (BJS Lemma 52, step 6) -/

/-- **The outer change of variables.**  For `z = N^{1/8}`, `y = N^{1/3}`,

  `∫_z^y I(t)/(t log t) dt = c̄/log N`   (`Salt.Chen.cbar`).

The monotone substitution `t = exp(β·log N)` (so `t = N^β`) maps `[z, y]` to `[1/8, 1/3]`; the
closed form `I(N^β) = log(2 − 3β)/((1 − β) log N)` collapses the integrand to
`(log N)⁻¹·log(2 − 3β)/(β(1 − β))`, whose integral over `[1/8, 1/3]` IS `c̄`.  This is the
`(t,s) → (β,σ)` step-6 change of variables the AB1 flag isolated; `cbar_eq_double_integral`
(landed) confirms the far end matches. -/
theorem Ifun_integral_eq_cbar {N z y : ℝ} (hN : 1 < N) (hy0 : 0 < y)
    (hy : Real.log y = Real.log N / 3) (hz0 : 0 < z) (hz : Real.log z = Real.log N / 8) :
    (∫ t in z..y, Ifun N y t / (t * Real.log t)) = cbar / Real.log N := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  set φ : ℝ → ℝ := fun β => Real.exp (β * Real.log N) with hφ
  set φ' : ℝ → ℝ := fun β => Real.exp (β * Real.log N) * Real.log N with hφ'
  have hφderiv : ∀ β : ℝ, HasDerivAt φ (φ' β) β := by
    intro β
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log N) (Real.log N) β := by
      simpa using (hasDerivAt_id β).mul_const (Real.log N)
    simpa [hφ, hφ'] using h1.exp
  have hφ18 : φ (1 / 8) = z := by
    rw [hφ]; simp only
    rw [show (1 / 8 : ℝ) * Real.log N = Real.log N / 8 by ring, ← hz]; exact Real.exp_log hz0
  have hφ13 : φ (1 / 3) = y := by
    rw [hφ]; simp only
    rw [show (1 / 3 : ℝ) * Real.log N = Real.log N / 3 by ring, ← hy]; exact Real.exp_log hy0
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := φ') (g := fun t => Ifun N y t / (t * Real.log t))
    (a := 1 / 8) (b := 1 / 3)
    (Continuous.continuousOn (by rw [hφ]; fun_prop))
    (fun x _ => hφderiv x)
    (fun x _ => by rw [hφ']; positivity)
  rw [hφ18, hφ13] at hcov
  rw [← hcov]
  rw [intervalIntegral.integral_congr
      (g := fun β => (Real.log N)⁻¹ * (Real.log (2 - 3 * β) / (β * (1 - β)))) ?_]
  · rw [intervalIntegral.integral_const_mul]
    have hcbar : (∫ β in (1 / 8 : ℝ)..(1 / 3), Real.log (2 - 3 * β) / (β * (1 - β))) = cbar := by
      rw [cbar]
    rw [hcbar, div_eq_inv_mul]
  · -- the pointwise integrand identity
    intro β hβ
    obtain ⟨hβlo, hβhi⟩ : (1 : ℝ) / 8 ≤ β ∧ β ≤ 1 / 3 := by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 8 ≤ 1 / 3), Set.mem_Icc] at hβ; exact hβ
    have hφβ0 : (0 : ℝ) < Real.exp (β * Real.log N) := Real.exp_pos _
    have hlogφ : Real.log (Real.exp (β * Real.log N)) = β * Real.log N := Real.log_exp _
    have hβlt : β * Real.log N < 2 / 3 * Real.log N := by nlinarith [hLN]
    have hcf : Ifun N y (Real.exp (β * Real.log N))
        = Ifun_cf N (Real.exp (β * Real.log N)) :=
      Ifun_closed_form hN hy0 hy hφβ0 (by rw [hlogφ]; exact hβlt)
    have hβ0 : (0 : ℝ) < β := by linarith
    have h1β0 : (0 : ℝ) < 1 - β := by linarith
    simp only [Function.comp, hφ, hφ', hcf, Ifun_cf, IargA, IdenA, hlogφ]
    rw [eq_comm]
    have hIarg : (2 : ℝ) - 3 * (β * Real.log N) / Real.log N = 2 - 3 * β := by
      field_simp
    have hIden : Real.log N - β * Real.log N = (1 - β) * Real.log N := by ring
    rw [hIarg, hIden]
    field_simp

/-! ## Section 6 — the fibered re-index of `weightedPairSum` (composition, step 1) -/

/-- **The fibered re-index.**  `weightedPairSum` (the landed `Salt.Chen.WeightedCount` object,
`Σ_{(p₁,p₂) ∈ pairSet} 1/(p₁p₂·log(N/p₁p₂))`) factors over `p₁` into the inner `p₂`-Abel-pass
carrier `Σ_{p₂} h_{p₁}(p₂)/p₂`:

  `weightedPairSum = Σ_{p₁ ∈ S1set} (1/p₁)·(Σ_{p₂ ∈ S2set} h_{p₁}(p₂)/p₂)`,

with `h_{p₁}(p₂) = hbjs x p₁ p₂ = 1/log(x/(p₁p₂))` (`= (logND)⁻¹`).  This is the object the two
Abel passes (`applicationA` on the inner `p₂`-sum, `applicationB` on the outer `p₁`-sum) consume.
Composes `pairSet_factor` (landed) with `Finset.sum_product`. -/
theorem weightedPairSum_fibered (x z y : ℕ) :
    weightedPairSum x z y
      = ∑ p₁ ∈ S1set x z y, (1 / (p₁ : ℝ))
          * ∑ p₂ ∈ S2set x y, hbjs (x : ℝ) (p₁ : ℝ) (p₂ : ℝ) / (p₂ : ℝ) := by
  rw [weightedPairSum, pairSet_factor, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p₁ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p₂ _ => ?_)
  simp only [hbjs, logND]
  ring

-- **Composition bracket.**  The landed input `tripleSum_le_weighted_pairSum` bounds
-- `tripleSum` by `(1 + o(1))·(x/2)·weightedPairSum`; `weightedPairSum_fibered` re-indexes
-- `weightedPairSum` into the two Abel-pass carriers; `applicationA`/`applicationB` bound the
-- inner/outer sums; `Ifun_integral_eq_cbar` evaluates the outer integral to `c̄/log N`.  The
-- remaining glue (the ℕ-window ↔ `primesInWindow` bridge, the (187) tail, the slack ledger →
-- `tripleSum ≤ (1 + slack₁)(c̄/2 + slack₂)·x/log x`) is flagged (AB2, FULL floor).
#check @tripleSum_le_weighted_pairSum
#check @cbar_eq_double_integral
#check @weightedPairSum_fibered

end Salt.Chen
