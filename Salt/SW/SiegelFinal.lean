/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Growth
import Salt.SW.EulerBridge
import Salt.SW.FourFold
import Salt.SW.Siegel
import Salt.SW.EstermannInterface
import Salt.SW.Page

/-!
# The SW rung, node S4b‴ — the Siegel exceptional-branch assembly

Design: `docs/blueprints/sw.md`, wave S4; flags `SW S4b`/`S4b′`/`S4b″`. This module discharges
the *exceptional-branch assembly* that `Salt.SW.siegel_zero_free_of_exceptional_case` folded into
its `hHard` hypothesis, using the now-landed inputs:
`estermannPositivity` (`EstermannInterface.lean`), `goldfeld_L_one_lower` (`Siegel.lean`), the
`changeLevel` wiring (`FourFold.changeLevel_quadratic`, `Page.product_ne_one`), the
imprimitive→primitive bridge (`EulerBridge.LFunction_eq_primitive_mul`), and the growth bound
(`Growth.LFunction_growth`).

## The mean-value step (fully proven here)

`LFunction_one_re_le_mvt` is the derivative mean-value conversion `L(1,χ) ≪ (1−β)·q^{1/2}·log q`
(the last of the four deferred `hHard` pieces): if `L(β,χ) = 0` for a real `β ∈ [3/4,1)`, then
`(L(1,χ)).re ≤ (1−β)·27·√q·(1+log q)`. Route: the fundamental theorem of calculus
`L(1) − L(β) = ∫_β^1 L'(σ) dσ` (`intervalIntegral.integral_eq_sub_of_hasDerivAt` on the real
segment, `HasDerivAt.comp_ofReal`), `L(β) = 0`, and the Cauchy first-derivative estimate
`‖L'(σ)‖ ≤ 27·√q·(1+log q)` on `[3/4,1]` (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
on the radius-`1/4` disk, whose sphere stays in the growth region `Re z ∈ [1/2, 5/4]`,
`LFunction_growth`).

## Scope note (the ε-optimization is deferred — see `docs/blueprints/flags.md`, SW S4b‴)

The mean-value step above is intrinsically `q^{1/2}`-lossy (the growth bound is `≪ √q log q`); the
imprimitive one-point bounds `B₁, B₂` fed to `goldfeld_L_one_lower` are `≪ 2^{ω(N)}`. Turning the
concrete Goldfeld lower bound into the ε-quantified `L(1,χ) ≫_ε q^{−ε}` / `β ≤ 1 − C/q^ε` requires
the sharp near-the-line growth `L(s,χ) ≪ log q` (`Re s ≥ 1 − c/log q`) and the divisor bound
`2^{ω(N)} = N^{o(1)}`, neither of which is in mathlib or the salt SW stack. Those are the deferred
inputs; everything below is the assembly around them.
-/

namespace Salt.SW

open Complex Metric DirichletCharacter MeasureTheory
open scoped ComplexOrder

/-- The crude imprimitive disk/point growth constant `27/2·√N·(1+log N)·N` (`≥ 1`, polynomial in
`N`), used as the `M`-bound and one-point `B₁,B₂`-bounds fed to `goldfeld_L_one_lower`. -/
noncomputable def diskConst (N : ℕ) : ℝ := 27 / 2 * Real.sqrt N * (1 + Real.log N) * N

/-! ## 1. The derivative mean-value step (the fourth deferred `hHard` piece) -/

/-- **Cauchy first-derivative bound near the 1-line.** For a primitive `χ` mod `f ≥ 2` and real
`σ ∈ [3/4, 1]`, `‖L'(σ,χ)‖ ≤ 27·√f·(1+log f)`. The radius-`1/4` disk about `σ` stays in the growth
region (`Re z ∈ [1/2, 5/4] ⊆ [1/2, 4]`, `‖z‖ ≤ 5/4`), where `LFunction_growth` gives
`‖L(z,χ)‖ ≤ 3·(1+‖z‖)·√f·(1+log f) ≤ (27/4)·√f·(1+log f)`; Cauchy (`norm_deriv ≤ C/R`, `R = 1/4`)
multiplies by `4`. -/
theorem norm_deriv_LFunction_le {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {σ : ℝ} (hσlo : 3 / 4 ≤ σ) (hσhi : σ ≤ 1) :
    ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ 27 * Real.sqrt f * (1 + Real.log f) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set C : ℝ := 27 / 4 * Real.sqrt f * (1 + Real.log f) with hCdef
  -- sphere sup bound
  have hsphere : ∀ z ∈ sphere (σ : ℂ) (1 / 4), ‖LFunction χ z‖ ≤ C := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hzre_lo : (1 : ℝ) / 2 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - (σ : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re, hz] at h
      have := abs_le.mp h; linarith [this.1]
    have hzre_hi : z.re ≤ 4 := by
      have h := Complex.abs_re_le_norm (z - (σ : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re, hz] at h
      have := abs_le.mp h; linarith [this.2]
    have hznorm : ‖z‖ ≤ 5 / 4 := by
      calc ‖z‖ = ‖(σ : ℂ) + (z - (σ : ℂ))‖ := by ring_nf
        _ ≤ ‖(σ : ℂ)‖ + ‖z - (σ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + 1 / 4 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hz]; linarith
        _ = 5 / 4 := by norm_num
    have hg := LFunction_growth χ hχ hf hzre_lo hzre_hi
    have hsqrtlog : (0 : ℝ) ≤ Real.sqrt f * (1 + Real.log f) := sqrtlog_nonneg hf
    calc ‖LFunction χ z‖ ≤ 3 * (1 + ‖z‖) * Real.sqrt f * (1 + Real.log f) := hg
      _ ≤ 3 * (1 + 5 / 4) * Real.sqrt f * (1 + Real.log f) := by
          have : 3 * (1 + ‖z‖) ≤ 3 * (1 + 5 / 4) := by linarith [hznorm]
          nlinarith [hsqrtlog, norm_nonneg z, Real.sqrt_nonneg (f : ℝ),
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f) : (1:ℝ) ≤ f)]
      _ = C := by rw [hCdef]; ring
  have hdcc : DiffContOnCl ℂ (LFunction χ) (ball (σ : ℂ) (1 / 4)) :=
    (differentiable_LFunction hχ1).diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
    hdcc hsphere
  calc ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ C / (1 / 4) := hcauchy
    _ = 27 * Real.sqrt f * (1 + Real.log f) := by rw [hCdef]; ring

/-- **The derivative mean-value step (the fourth deferred `hHard` piece).** For a primitive `χ`
mod `f ≥ 2` with a real zero `β ∈ [3/4, 1)` of `L(·,χ)`,
`(L(1,χ)).re ≤ (1 − β)·27·√f·(1+log f)`.
Route: `L(1) − L(β) = ∫_β^1 L'(σ) dσ` (FTC on the real segment via `HasDerivAt.comp_ofReal`),
`L(β) = 0`, then `‖L(1)‖ ≤ (1−β)·sup_{[β,1]}‖L'‖ ≤ (1−β)·27√f(1+log f)`
(`norm_deriv_LFunction_le`); finish with `(L(1)).re ≤ ‖L(1)‖`. -/
theorem LFunction_one_re_le_mvt {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) {β : ℝ} (hzero : LFunction χ (β : ℂ) = 0)
    (hβlo : 3 / 4 ≤ β) (hβhi : β < 1) :
    (LFunction χ 1).re ≤ (1 - β) * (27 * Real.sqrt f * (1 + Real.log f)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hf
  set K : ℝ := 27 * Real.sqrt f * (1 + Real.log f) with hKdef
  -- the derivative of `σ ↦ L(σ,χ)` along the real axis
  set F' : ℝ → ℂ := fun σ => deriv (LFunction χ) (σ : ℂ) with hF'def
  have hderiv : ∀ σ ∈ Set.uIcc β (1 : ℝ),
      HasDerivAt (fun t : ℝ => LFunction χ (t : ℂ)) (F' σ) σ := by
    intro σ _
    exact (differentiable_LFunction hχ1 (σ : ℂ)).hasDerivAt.comp_ofReal
  -- interval integrability of `F'` (continuous, since `L` is entire hence `deriv` analytic)
  have hana : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ
  have hcont : Continuous (deriv (LFunction χ)) :=
    continuousOn_univ.mp hana.deriv.continuousOn
  have hcontF' : Continuous F' := by
    rw [hF'def]; exact hcont.comp Complex.continuous_ofReal
  have hint : IntervalIntegrable F' volume β 1 := hcontF'.intervalIntegrable _ _
  -- FTC: `∫_β^1 F' = L(1) − L(β) = L(1)`
  have hFTC : (∫ σ in β..(1 : ℝ), F' σ) = LFunction χ 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    rw [show ((1 : ℝ) : ℂ) = (1 : ℂ) by norm_num, hzero, sub_zero]
  -- norm bound on the integral
  have hnorm_int : ‖(∫ σ in β..(1 : ℝ), F' σ)‖ ≤ (1 - β) * K := by
    have hbnd : ∀ σ ∈ Set.uIoc β (1 : ℝ), ‖F' σ‖ ≤ K := by
      intro σ hσ
      rw [Set.uIoc_of_le hβhi.le, Set.mem_Ioc] at hσ
      exact norm_deriv_LFunction_le χ hχ hf (by linarith [hσ.1]) hσ.2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - β), mul_comm] at h
  -- assemble
  calc (LFunction χ 1).re ≤ ‖LFunction χ 1‖ := Complex.re_le_norm _
    _ = ‖(∫ σ in β..(1 : ℝ), F' σ)‖ := by rw [hFTC]
    _ ≤ (1 - β) * K := hnorm_int

/-! ## 2. The imprimitive disk-growth bound `M` (the first deferred `hHard` piece)

`goldfeld_L_one_lower` requires an `M`-bound `‖L(χ₁,z)·L(χ₂,z)·L(χ₁χ₂,z)‖ ≤ M` on `ball 2 (3/2)`,
but its characters live at the common level `N = q₁·q` where the products are *imprimitive*. The
primitive growth bound `LFunction_growth` covers only primitive characters; we bridge through the
Euler correction `L(χ) = L(χ_prim)·eulerCorr(χ)` (`EulerBridge.LFunction_eq_primitive_mul`) and a
crude `‖eulerCorr‖ ≤ N` on the ball. -/

/-- Per-Euler-factor disk bound: `‖1 − ψ_prim(p)·p^{−z}‖ ≤ 2` for `Re z ≥ 0` (then `p^{−Re z} ≤ 1`
and `‖ψ_prim(p)‖ ≤ 1`). -/
lemma norm_eulerFactor_ball_le {N : ℕ} (ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    {z : ℂ} (hz : (0 : ℝ) ≤ z.re) : ‖eulerFactor ψ.primitiveCharacter p z‖ ≤ 2 := by
  have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hcpow : ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hP0, Complex.neg_re]
  have hle1 : (p : ℝ) ^ (-z.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have hstep : ‖ψ.primitiveCharacter p‖ * (p : ℝ) ^ (-z.re) ≤ 1 := by
    calc ‖ψ.primitiveCharacter p‖ * (p : ℝ) ^ (-z.re)
        ≤ 1 * 1 := mul_le_mul (ψ.primitiveCharacter.norm_le_one _) hle1
          (Real.rpow_nonneg hP0.le _) (by norm_num)
      _ = 1 := by norm_num
  rw [eulerFactor]
  calc ‖(1 : ℂ) - ψ.primitiveCharacter p * (p : ℂ) ^ (-z)‖
      ≤ ‖(1 : ℂ)‖ + ‖ψ.primitiveCharacter p * (p : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ = 1 + ‖ψ.primitiveCharacter p‖ * (p : ℝ) ^ (-z.re) := by rw [norm_one, norm_mul, hcpow]
    _ ≤ 1 + 1 := by linarith [hstep]
    _ = 2 := by norm_num

/-- Crude Euler-correction disk bound: `‖eulerCorr ψ z‖ ≤ N` for `Re z > 1/2`, via `‖·‖ ≤ 2^{ω(N)}`
(per-factor `≤ 2`) and `2^{ω(N)} ≤ ∏_{p∣N} p ≤ N`. -/
lemma norm_eulerCorr_ball_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : (0 : ℝ) ≤ z.re) : ‖eulerCorr ψ z‖ ≤ (N : ℝ) := by
  rw [eulerCorr, norm_prod]
  calc ∏ p ∈ N.primeFactors, ‖eulerFactor ψ.primitiveCharacter p z‖
      ≤ ∏ p ∈ N.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun p hp => norm_eulerFactor_ball_le ψ (Nat.prime_of_mem_primeFactors hp) hz)
    _ ≤ ∏ p ∈ N.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ (N : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
          (Nat.prod_primeFactors_dvd N)

/-- The single-character imprimitive disk bound: for `ψ ≠ 1` mod `N ≥ 2`, on `ball 2 (3/2)`,
`‖L(ψ,z)‖ ≤ (27/2)·√N·(1+log N)·N`. Route: `L(ψ) = L(ψ_prim)·eulerCorr(ψ)`
(`LFunction_eq_primitive_mul`), the primitive factor by `LFunction_growth` (`ψ_prim` primitive of
conductor `≥ 2`, `Re z ∈ [1/2,7/2]`, `‖z‖ ≤ 7/2`), the correction by `norm_eulerCorr_ball_le`. -/
lemma norm_LFunction_ball_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ1 : ψ ≠ 1)
    {z : ℂ} (hz : z ∈ ball (2 : ℂ) (3 / 2)) :
    ‖LFunction ψ z‖ ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) * N := by
  rw [mem_ball, Complex.dist_eq] at hz
  have hzre_lo : (1 : ℝ) / 2 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - 2)
    rw [Complex.sub_re, Complex.re_ofNat] at h
    have := abs_le.mp (le_of_lt (lt_of_le_of_lt h hz)); linarith [this.1]
  have hzre_hi : z.re ≤ 4 := by
    have h := Complex.abs_re_le_norm (z - 2)
    rw [Complex.sub_re, Complex.re_ofNat] at h
    have := abs_le.mp (le_of_lt (lt_of_le_of_lt h hz)); linarith [this.2]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  have hznorm : ‖z‖ ≤ 7 / 2 := by
    calc ‖z‖ = ‖(2 : ℂ) + (z - 2)‖ := by ring_nf
      _ ≤ ‖(2 : ℂ)‖ + ‖z - 2‖ := norm_add_le _ _
      _ ≤ 2 + 3 / 2 := by rw [hn2]; linarith [hz.le]
      _ = 7 / 2 := by norm_num
  -- primitive/euler split
  have hprim1 : ψ.primitiveCharacter ≠ 1 := fun h =>
    hψ1 (by rw [← changeLevel_primitiveCharacter ψ, h, changeLevel_one])
  have hcond2 : 2 ≤ ψ.conductor := by
    have hc1 : ψ.conductor ≠ 1 := fun h => hψ1 (eq_one_iff_conductor_eq_one.mpr h)
    have := ψ.conductor_ne_zero; omega
  have hcondN : ψ.conductor ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (conductor_dvd_level ψ)
  have hsplit : LFunction ψ z = LFunction ψ.primitiveCharacter z * eulerCorr ψ z :=
    LFunction_eq_primitive_mul ψ (Or.inl hψ1)
  have hgprim : ‖LFunction ψ.primitiveCharacter z‖
      ≤ 3 * (1 + ‖z‖) * Real.sqrt ψ.conductor * (1 + Real.log ψ.conductor) :=
    LFunction_growth ψ.primitiveCharacter (primitiveCharacter_isPrimitive ψ) hcond2
      hzre_lo hzre_hi
  have hcorr : ‖eulerCorr ψ z‖ ≤ (N : ℝ) := norm_eulerCorr_ball_le ψ (by linarith)
  -- bookkeeping bounds
  have hcondR : (ψ.conductor : ℝ) ≤ N := by exact_mod_cast hcondN
  have hcond1R : (1 : ℝ) ≤ (ψ.conductor : ℝ) := by exact_mod_cast (by omega : 1 ≤ ψ.conductor)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := le_trans hcond1R hcondR
  have hsqrt : Real.sqrt ψ.conductor ≤ Real.sqrt N := Real.sqrt_le_sqrt hcondR
  have hlog : Real.log ψ.conductor ≤ Real.log N := Real.log_le_log (by linarith) hcondR
  have hlognn : (0 : ℝ) ≤ Real.log ψ.conductor := Real.log_nonneg hcond1R
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt ψ.conductor := Real.sqrt_nonneg _
  have hgprim' : ‖LFunction ψ.primitiveCharacter z‖
      ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) := by
    calc ‖LFunction ψ.primitiveCharacter z‖
        ≤ 3 * (1 + ‖z‖) * Real.sqrt ψ.conductor * (1 + Real.log ψ.conductor) := hgprim
      _ ≤ 3 * (1 + 7 / 2) * Real.sqrt N * (1 + Real.log N) := by gcongr
      _ = 27 / 2 * Real.sqrt N * (1 + Real.log N) := by ring
  -- assemble the product
  have hA : (0 : ℝ) ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) := by
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1R
    positivity
  rw [hsplit, norm_mul]
  calc ‖LFunction ψ.primitiveCharacter z‖ * ‖eulerCorr ψ z‖
      ≤ (27 / 2 * Real.sqrt N * (1 + Real.log N)) * (N : ℝ) :=
        mul_le_mul hgprim' hcorr (norm_nonneg _) hA
    _ = 27 / 2 * Real.sqrt N * (1 + Real.log N) * N := by ring

/-- The single-character imprimitive disk bound is `≥ 1` for `N ≥ 1` (`27/2·√N·(1+log N)·N ≥ 27/2`).
-/
lemma one_le_diskConst {N : ℕ} [NeZero N] :
    (1 : ℝ) ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) * N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  have hlog0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have p1 : (1 : ℝ) ≤ 27 / 2 * Real.sqrt N := by nlinarith [hsqrt1]
  calc (1 : ℝ) ≤ 27 / 2 * Real.sqrt N := p1
    _ ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) :=
        le_mul_of_one_le_right (by linarith [p1]) (by linarith [hlog0])
    _ ≤ 27 / 2 * Real.sqrt N * (1 + Real.log N) * N :=
        le_mul_of_one_le_right (by nlinarith [p1, hlog0]) hN1

/-- **The imprimitive fourfold disk bound** (exactly the `hMbnd` shape `goldfeld_L_one_lower`
consumes). For real (or any) characters `χ₁, χ₂, χ₁χ₂` all `≠ 1` mod `N ≥ 2`, on `ball 2 (3/2)`,
`‖L(χ₁,z)·L(χ₂,z)·L(χ₁χ₂,z)‖ ≤ (27/2·√N·(1+log N)·N)^3`. -/
theorem fourfold_disk_bound {N : ℕ} [NeZero N] (χ₁ χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) (hp : χ₁ * χ₂ ≠ 1) {z : ℂ} (hz : z ∈ ball (2 : ℂ) (3 / 2)) :
    ‖LFunction χ₁ z * LFunction χ₂ z * LFunction (χ₁ * χ₂) z‖
      ≤ (27 / 2 * Real.sqrt N * (1 + Real.log N) * N) ^ 3 := by
  set B : ℝ := 27 / 2 * Real.sqrt N * (1 + Real.log N) * N with hBdef
  have hBnn : (0 : ℝ) ≤ B := le_trans zero_le_one one_le_diskConst
  have b1 := norm_LFunction_ball_le χ₁ h1 hz
  have b2 := norm_LFunction_ball_le χ₂ h2 hz
  have b3 := norm_LFunction_ball_le (χ₁ * χ₂) hp hz
  rw [← hBdef] at b1 b2 b3
  rw [norm_mul, norm_mul]
  calc ‖LFunction χ₁ z‖ * ‖LFunction χ₂ z‖ * ‖LFunction (χ₁ * χ₂) z‖
      ≤ B * B * B :=
        mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) hBnn) b3 (norm_nonneg _) (by positivity)
    _ = B ^ 3 := by ring

/-! ## 3. The Goldfeld exceptional-branch assembly (the common-level wiring)

Given the *fixed* exceptional character `χ₁` mod `q₁` (primitive real quadratic, `≠ 1`) with a real
zero `β₁ ∈ [19/20, 1)`, and any *distinct* target `χ` mod `q` (primitive real quadratic, `≠ 1`),
lift both to the common level `N = q₁·q` (`changeLevel`, preserving `χ² = 1` via
`changeLevel_quadratic`), verify the three non-principality conditions
(`changeLevel` of a nontrivial primitive is nontrivial via `conductor_changeLevel`;
`χ₁'·χ' ≠ 1` via `Page.product_ne_one` from distinctness), transfer the zero
(`LFunction_changeLevel` at `β₁`), supply the disk bound `M = (diskConst N)^3`
(`fourfold_disk_bound`) and one-point bounds `B₁ = B₂ = diskConst N`
(`norm_LFunction_ball_le` at `1 ∈ ball 2 (3/2)`), and fire `goldfeld_L_one_lower` (which consumes
the now-unconditional `estermannPositivity`). The result is the concrete Goldfeld lower bound on
the lifted target `(L(χ',1)).re`. -/

private lemma mem_ball_one : (1 : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
  rw [mem_ball, Complex.dist_eq, show (1 : ℂ) - 2 = -1 by ring, norm_neg, norm_one]; norm_num

/-- `changeLevel` of a nontrivial primitive character is nontrivial (its conductor is unchanged,
hence `≥ 2 > 1`). -/
private lemma changeLevel_ne_one {q N : ℕ} [NeZero q] [NeZero N] (hqN : q ∣ N)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    changeLevel hqN χ ≠ 1 := by
  intro he
  have hc : (changeLevel hqN χ).conductor = χ.conductor := conductor_changeLevel χ hqN
  rw [he, conductor_one, (hprim : χ.conductor = q)] at hc
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [(hprim : χ.conductor = q)] at hc1; have := NeZero.ne q; omega
  omega

/-- **The Goldfeld exceptional-branch L(1) lower bound (lifted form).** For the fixed exceptional
`χ₁` mod `q₁` (primitive real quadratic `≠ 1`, real zero `β₁ ∈ [19/20, 1)`) and a distinct target
`χ` mod `q` (primitive real quadratic `≠ 1`), with `N = q₁·q` and `χ' = changeLevel (q ∣ N) χ`,
`(1−β₁)/4 · (diskConst N ^ 3)^{−3(1−β₁)} / (diskConst N · diskConst N) ≤ (L(χ',1)).re`.
This is `goldfeld_L_one_lower` (Estermann + the nonnegative fourfold coefficients) fired end-to-end
with the `changeLevel`-lifted real characters and the crude disk/point bounds constructed above. -/
theorem siegel_L_one_exceptional {q₁ q : ℕ} [NeZero q₁] [NeZero q]
    (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (hp₁ : χ₁.IsPrimitive) (hpχ : χ.IsPrimitive)
    (hsq₁ : χ₁ ^ 2 = 1) (hsqχ : χ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ1 : χ ≠ 1)
    (hdist : ∀ (h : q₁ = q), (h ▸ χ₁) ≠ χ)
    {β₁ : ℝ} (hz₁ : LFunction χ₁ (β₁ : ℂ) = 0) (hβlo : (19 / 20 : ℝ) ≤ β₁) (hβhi : β₁ < 1) :
    (1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
        / (diskConst (q₁ * q) * diskConst (q₁ * q))
      ≤ (LFunction (changeLevel (dvd_mul_left q q₁) χ) 1).re := by
  set N : ℕ := q₁ * q with hNdef
  haveI : NeZero N := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have h₁dvd : q₁ ∣ N := dvd_mul_right q₁ q
  have hdvd : q ∣ N := dvd_mul_left q q₁
  set χ₁' : DirichletCharacter ℂ N := changeLevel h₁dvd χ₁ with hχ₁'
  set χ' : DirichletCharacter ℂ N := changeLevel hdvd χ with hχ'
  -- quadratic + non-principal
  have hsq1' : χ₁' ^ 2 = 1 := changeLevel_quadratic h₁dvd hsq₁
  have hsq2' : χ' ^ 2 = 1 := changeLevel_quadratic hdvd hsqχ
  have h1 : χ₁' ≠ 1 := changeLevel_ne_one h₁dvd hp₁ hχ₁1
  have h2 : χ' ≠ 1 := changeLevel_ne_one hdvd hpχ hχ1
  have hp' : χ₁' * χ' ≠ 1 := product_ne_one h₁dvd hdvd hp₁ hpχ hsqχ hdist
  -- the zero transfers to the lift
  have hzero' : LFunction χ₁' (β₁ : ℂ) = 0 := by
    rw [hχ₁', LFunction_changeLevel h₁dvd χ₁ (Or.inl hχ₁1), hz₁, zero_mul]
  -- the disk bound `M = (diskConst N)^3`
  set D : ℝ := diskConst N with hDdef
  have hD1 : (1 : ℝ) ≤ D := one_le_diskConst
  have hDpos : (0 : ℝ) < D := by linarith
  have hM : (1 : ℝ) ≤ D ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ D ^ 3 := by gcongr
  have hMbnd : ∀ z ∈ ball (2 : ℂ) (3 / 2),
      ‖LFunction χ₁' z * LFunction χ' z * LFunction (χ₁' * χ') z‖ ≤ D ^ 3 :=
    fun z hz => fourfold_disk_bound χ₁' χ' h1 h2 hp' hz
  -- one-point bounds `B₁ = B₂ = diskConst N`
  have hB₁ : (LFunction χ₁' 1).re ≤ D :=
    le_trans (Complex.re_le_norm _) (norm_LFunction_ball_le χ₁' h1 mem_ball_one)
  have hB₂ : (LFunction (χ₁' * χ') 1).re ≤ D :=
    le_trans (Complex.re_le_norm _) (norm_LFunction_ball_le (χ₁' * χ') hp' mem_ball_one)
  -- fire Goldfeld
  exact goldfeld_L_one_lower estermannPositivity χ₁' χ' hsq1' hsq2' h1 h2 hp' hM hMbnd
    hB₁ hB₂ hDpos hDpos hβlo hβhi hzero'

/-! ## 4. The imprimitive mean-value step and the end-to-end zero-free bound

To close the loop we need the mean-value step *for the lifted (imprimitive) target* `χ'`, so that it
composes directly with `siegel_L_one_exceptional` (whose output is `(L(χ',1)).re`) — no
imprimitive→primitive `L(1)`-conversion required. The Cauchy estimate uses the imprimitive disk
bound `norm_LFunction_ball_le` on a radius-`1/8` disk (its sphere stays inside `ball 2 (3/2)` for
`σ ∈ [7/8, 1]`). -/

/-- Imprimitive Cauchy derivative bound: for `ψ ≠ 1` mod `N` and `σ ∈ [7/8, 1]`,
`‖L'(σ,ψ)‖ ≤ 8·diskConst N`. The radius-`1/8` disk about `σ` has its sphere inside `ball 2 (3/2)`
(`‖z − 2‖ ≤ 1/8 + 9/8 = 5/4 < 3/2`), where `norm_LFunction_ball_le` bounds `‖L(ψ,z)‖ ≤ diskConst N`;
Cauchy (`R = 1/8`) multiplies by `8`. -/
theorem norm_deriv_LFunction_imprim_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ1 : ψ ≠ 1) {σ : ℝ} (hσlo : 7 / 8 ≤ σ) (hσhi : σ ≤ 1) :
    ‖deriv (LFunction ψ) (σ : ℂ)‖ ≤ 8 * diskConst N := by
  have hdC : diskConst N = 27 / 2 * Real.sqrt N * (1 + Real.log N) * N := rfl
  have hsphere : ∀ z ∈ sphere (σ : ℂ) (1 / 8), ‖LFunction ψ z‖ ≤ diskConst N := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hzball : z ∈ ball (2 : ℂ) (3 / 2) := by
      rw [mem_ball, Complex.dist_eq]
      calc ‖z - 2‖ = ‖(z - (σ : ℂ)) + ((σ : ℂ) - 2)‖ := by ring_nf
        _ ≤ ‖z - (σ : ℂ)‖ + ‖(σ : ℂ) - 2‖ := norm_add_le _ _
        _ ≤ 1 / 8 + 9 / 8 := by
            rw [hz, show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonpos (by linarith)]
            linarith
        _ < 3 / 2 := by norm_num
    exact norm_LFunction_ball_le ψ hψ1 hzball
  have hdcc : DiffContOnCl ℂ (LFunction ψ) (ball (σ : ℂ) (1 / 8)) :=
    (differentiable_LFunction hψ1).diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/8)
    hdcc hsphere
  calc ‖deriv (LFunction ψ) (σ : ℂ)‖ ≤ diskConst N / (1 / 8) := hcauchy
    _ = 8 * diskConst N := by rw [div_div_eq_mul_div]; ring

/-- **The imprimitive mean-value step.** For `ψ ≠ 1` mod `N` with a real zero `β ∈ [7/8, 1)`,
`(L(ψ,1)).re ≤ (1−β)·8·diskConst N`. Same FTC route as `LFunction_one_re_le_mvt`, using the
imprimitive Cauchy bound `norm_deriv_LFunction_imprim_le`. -/
theorem LFunction_one_re_le_mvt_imprim {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ1 : ψ ≠ 1) {β : ℝ} (hzero : LFunction ψ (β : ℂ) = 0) (hβlo : 7 / 8 ≤ β) (hβhi : β < 1) :
    (LFunction ψ 1).re ≤ (1 - β) * (8 * diskConst N) := by
  set F' : ℝ → ℂ := fun σ => deriv (LFunction ψ) (σ : ℂ) with hF'def
  have hderiv : ∀ σ ∈ Set.uIcc β (1 : ℝ),
      HasDerivAt (fun t : ℝ => LFunction ψ (t : ℂ)) (F' σ) σ :=
    fun σ _ => (differentiable_LFunction hψ1 (σ : ℂ)).hasDerivAt.comp_ofReal
  have hana : AnalyticOnNhd ℂ (LFunction ψ) Set.univ :=
    (differentiable_LFunction hψ1).differentiableOn.analyticOnNhd isOpen_univ
  have hcontF' : Continuous F' :=
    (continuousOn_univ.mp hana.deriv.continuousOn).comp Complex.continuous_ofReal
  have hint : IntervalIntegrable F' volume β 1 := hcontF'.intervalIntegrable _ _
  have hFTC : (∫ σ in β..(1 : ℝ), F' σ) = LFunction ψ 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
      show ((1 : ℝ) : ℂ) = (1 : ℂ) by norm_num, hzero, sub_zero]
  have hnorm_int : ‖(∫ σ in β..(1 : ℝ), F' σ)‖ ≤ (1 - β) * (8 * diskConst N) := by
    have hbnd : ∀ σ ∈ Set.uIoc β (1 : ℝ), ‖F' σ‖ ≤ 8 * diskConst N := by
      intro σ hσ
      rw [Set.uIoc_of_le hβhi.le, Set.mem_Ioc] at hσ
      exact norm_deriv_LFunction_imprim_le ψ hψ1 (by linarith [hσ.1]) hσ.2
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - β), mul_comm] at h
  calc (LFunction ψ 1).re ≤ ‖LFunction ψ 1‖ := Complex.re_le_norm _
    _ = ‖(∫ σ in β..(1 : ℝ), F' σ)‖ := by rw [hFTC]
    _ ≤ (1 - β) * (8 * diskConst N) := hnorm_int

/-- **The end-to-end exceptional-branch zero-free bound (concrete).** Composing the whole
Estermann → Goldfeld → `L(1)`-lower → mean-value pipeline: for the fixed exceptional `χ₁` mod `q₁`
(real zero `β₁ ∈ [19/20,1)`) and a distinct target `χ` mod `q` (both primitive real quadratic
`≠ 1`), every real zero `β ∈ [7/8, 1)` of `L(·,χ)` obeys `β ≤ 1 − G/(8·D)` where `D = diskConst N`
(`N = q₁·q`) and `G = (1−β₁)/4·(D³)^{−3(1−β₁)}/(D·D)` is the Goldfeld lower bound.
(The bound is intrinsically `≪ q^{−poly}`-lossy — sub-optimal versus the ε-quantified Siegel
statement, which needs the deferred tight bounds; see the module header and `flags.md` SW S4b‴.
The `β < 7/8` case is trivial: `1 − β > 1/8`.) -/
theorem siegel_zero_free_exceptional {q₁ q : ℕ} [NeZero q₁] [NeZero q]
    (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (hp₁ : χ₁.IsPrimitive) (hpχ : χ.IsPrimitive)
    (hsq₁ : χ₁ ^ 2 = 1) (hsqχ : χ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ1 : χ ≠ 1)
    (hdist : ∀ (h : q₁ = q), (h ▸ χ₁) ≠ χ)
    {β₁ : ℝ} (hz₁ : LFunction χ₁ (β₁ : ℂ) = 0) (hβ₁lo : (19 / 20 : ℝ) ≤ β₁) (hβ₁hi : β₁ < 1)
    {β : ℝ} (hzβ : LFunction χ (β : ℂ) = 0) (hβlo : (7 / 8 : ℝ) ≤ β) (hβhi : β < 1) :
    β ≤ 1 - ((1 - β₁) / 4 * (diskConst (q₁ * q) ^ 3) ^ (-(3 * (1 - β₁)))
        / (diskConst (q₁ * q) * diskConst (q₁ * q))) / (8 * diskConst (q₁ * q)) := by
  set N : ℕ := q₁ * q with hNdef
  haveI : NeZero N := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hdvd : q ∣ N := dvd_mul_left q q₁
  set χ' : DirichletCharacter ℂ N := changeLevel hdvd χ with hχ'
  have h2 : χ' ≠ 1 := changeLevel_ne_one hdvd hpχ hχ1
  set D : ℝ := diskConst N with hDdef
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one one_le_diskConst
  set G : ℝ := (1 - β₁) / 4 * (D ^ 3) ^ (-(3 * (1 - β₁))) / (D * D) with hGdef
  -- lower bound from Goldfeld (lifted)
  have hlow : G ≤ (LFunction χ' 1).re :=
    siegel_L_one_exceptional χ₁ χ hp₁ hpχ hsq₁ hsqχ hχ₁1 hχ1 hdist hz₁ hβ₁lo hβ₁hi
  -- the target zero transfers to the lift
  have hzβ' : LFunction χ' (β : ℂ) = 0 := by
    rw [hχ', LFunction_changeLevel hdvd χ (Or.inl hχ1), hzβ, zero_mul]
  -- upper bound from the imprimitive mean-value step
  have hup : (LFunction χ' 1).re ≤ (1 - β) * (8 * D) :=
    LFunction_one_re_le_mvt_imprim χ' h2 hzβ' hβlo hβhi
  -- combine
  have hcomb : G ≤ (1 - β) * (8 * D) := le_trans hlow hup
  have h8D : (0 : ℝ) < 8 * D := by positivity
  have hfin : G / (8 * D) ≤ 1 - β := by rw [div_le_iff₀ h8D]; linarith [hcomb]
  linarith [hfin]

end Salt.SW
