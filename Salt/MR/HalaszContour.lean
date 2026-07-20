/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszKernel

/-!
# HALASZ-INFRA wave I-1, K4' residual — the Poisson-kernel cosine integral

The named residual of the minimal-seam Halász route
(`docs/exploration/halasz-infra-freeze.md`, FILE A, rung K4').  Two stones:

* `cos_int_pair` — the Fourier cosine transform of the Poisson/Cauchy kernel,
  `∫ cos(θt)/(c²+t²) dt = (π/c)·e^{-c|θ|}` for `0 < c`.  mathlib-absent
  (Cauchy characteristic function is not formalised); proved here by the
  rectangle-CIF contour route on a growing square `[-R,R]×[0,R]`, using the
  landed residue apparatus `Salt.SW.ContourShift.rectBI_cif_eq`.  The pole at
  `s = ci` in the upper half-plane contributes the constant residue
  `(π/c)e^{-cθ}` for every `R`; the top and two side edges vanish as `R→∞`
  (`squeeze_zero'` against `2R/(R²−c²) → 0`); the bottom edge converges to the
  full-line integral (`intervalIntegral_tendsto_integral`).

* `dirichlet_plancherel` — the Finset-bilinear consumer:
  `∫ ‖∑_{n∈F} bₙ n^{-s}‖²/(c²+t²) dt = (π/c)·∑_{m,n} Re(bₘ b̄ₙ)/(mn)^c·e^{-c|log m−log n|}`.
  Norm-square expansion → `n^{-s} = n^{-c}e^{-it log n}` → finite Fubini →
  per-pair `Re`-linear split consuming `cos_int_pair` and the sin-oddness of
  `∫ sin(θt)/(c²+t²) = 0`.  Does NOT consume `MVHilbert` (freeze law).

The K4' statements are FROZEN (iron rule 1); the routes are the executor's.
-/

open MeasureTheory Complex Set Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## The integrand and its algebraic skeleton -/

/-- The residue factor `φ(s) = e^{iθs}/(s + ci)`; analytic on the upper closed
square (its only zero of the denominator is at `s = −ci`, below the real axis). -/
private noncomputable def poisφ (θ c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * s * I) / (s + (c : ℂ) * I)

/-- The full integrand `F(s) = e^{iθs}/((s+ci)(s−ci)) = e^{iθs}/(c²+s²)`. -/
private noncomputable def poisF (θ c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * s * I) / ((s + (c : ℂ) * I) * (s - (c : ℂ) * I))

/-- `F(s) = φ(s)/(s − ci)`: the exact `rectBI_cif_eq` shape. -/
private lemma poisF_eq (θ c : ℝ) (s : ℂ) : poisF θ c s = poisφ θ c s / (s - (c : ℂ) * I) := by
  rw [poisF, poisφ, div_div]

/-- On the real axis `F(x) = e^{iθx}/(c²+x²)` — the target integrand. -/
private lemma poisF_ofReal (θ c : ℝ) (x : ℝ) :
    poisF θ c (x : ℂ) = Complex.exp (((θ * x : ℝ) : ℂ) * I) / (((c ^ 2 + x ^ 2 : ℝ)) : ℂ) := by
  rw [poisF]
  congr 1
  · push_cast; ring
  · rw [show ((x : ℂ) + (c : ℂ) * I) * ((x : ℂ) - (c : ℂ) * I)
        = (x : ℂ) ^ 2 - (c : ℂ) ^ 2 * I ^ 2 by ring, Complex.I_sq]
    push_cast; ring

/-- `‖F(s)‖ = e^{−θ·Im s}/‖(s+ci)(s−ci)‖`. -/
private lemma norm_poisF (θ c : ℝ) (s : ℂ) :
    ‖poisF θ c s‖ = Real.exp (-(θ * s.im)) / ‖(s + (c : ℂ) * I) * (s - (c : ℂ) * I)‖ := by
  rw [poisF, norm_div, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

/-! ## The `R/(R²−c²) → 0` decay used for the three vanishing edges. -/

/-- The edge-bound ratio tends to `0`. -/
private lemma ratio_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => R / (R ^ 2 - c ^ 2)) atTop (𝓝 0) := by
  have h2R : Tendsto (fun R : ℝ => 2 / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ h2R
  · filter_upwards [eventually_gt_atTop c] with R hR
    have hR0 : 0 < R := lt_trans hc hR
    have : 0 < R ^ 2 - c ^ 2 := by
      nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
    positivity
  · filter_upwards [eventually_gt_atTop c, eventually_ge_atTop (Real.sqrt 2 * c)] with R hR hR1
    have hR0 : 0 < R := lt_trans hc hR
    have hden : 0 < R ^ 2 - c ^ 2 := by
      nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : (Real.sqrt 2 * c) ^ 2 = 2 * c ^ 2 := by rw [mul_pow, hs2]
    have hle : 2 * c ^ 2 ≤ R ^ 2 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ Real.sqrt 2 * c by positivity) hR1 2
      rwa [hexp] at h
    rw [div_le_div_iff₀ hden hR0]
    nlinarith [hle]

/-! ## The residue: the boundary integral is the constant `(π/c)e^{-cθ}`. -/

open Salt.SW in
/-- The rectangle boundary integral of `F` over the growing square `[-R,R]×[0,R]`
picks up the residue at the interior pole `s = ci` — the constant `2πi·φ(ci)` for
every `R > c`. -/
private lemma poisF_residue {θ c : ℝ} (hc : 0 < c) {R : ℝ} (hR : c < R) :
    rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c)
      = 2 * (Real.pi : ℂ) * I * poisφ θ c ((c : ℂ) * I) := by
  have hR0 : 0 < R := lt_trans hc hR
  set z : ℂ := ((-R : ℝ) : ℂ) with hz
  set w : ℂ := ((R : ℝ) + (R : ℝ) * I) with hw
  set p : ℂ := ((c : ℂ) * I) with hp
  have hzre : z.re = -R := by simp [hz]
  have hzim : z.im = 0 := by simp [hz]
  have hwre : w.re = R := by simp [hw]
  have hwim : w.im = R := by simp [hw]
  have hpre : p.re = 0 := by simp [hp]
  have hpim : p.im = c := by simp [hp]
  have hcongr : (poisF θ c) = (fun s => poisφ θ c s / (s - p)) := by
    funext s; rw [poisF_eq, hp]
  rw [hcongr]
  refine rectBI_cif_eq ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [closedRect, mem_reProdIm] at hs
    have hsim : 0 ≤ s.im := by
      have h2 := hs.2
      rw [hzim, hwim, Set.uIcc_of_le hR0.le] at h2
      exact h2.1
    have hden : s + (c : ℂ) * I ≠ 0 := by
      intro h
      have h2 : (s + (c : ℂ) * I).im = 0 := by rw [h]; simp
      simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero] at h2
      linarith
    have hnum : DifferentiableAt ℂ (fun s : ℂ => Complex.exp ((θ : ℂ) * s * I)) s := by
      fun_prop
    have hden' : DifferentiableAt ℂ (fun s : ℂ => s + (c : ℂ) * I) s := by fun_prop
    have hd : DifferentiableAt ℂ (poisφ θ c) s := by
      unfold poisφ; exact hnum.div hden' hden
    exact hd.differentiableWithinAt
  · rw [hzre, hwre]; linarith
  · rw [hzim, hwim]; exact hR0
  · rw [hzre, hwre, hpre]; exact ⟨by linarith, hR0⟩
  · rw [hzim, hwim, hpim]; exact ⟨hc, hR⟩

/-- The residue value: `2πi·φ(ci) = (π/c)·e^{-cθ}` (a real number). -/
private lemma poisφ_at_pole {θ c : ℝ} (hc : 0 < c) :
    2 * (Real.pi : ℂ) * I * poisφ θ c ((c : ℂ) * I)
      = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have harg : (θ : ℂ) * ((c : ℂ) * I) * I = ((-(c * θ) : ℝ) : ℂ) := by
    rw [show (θ : ℂ) * ((c : ℂ) * I) * I = (θ : ℂ) * (c : ℂ) * (I * I) from by ring,
      Complex.I_mul_I]
    push_cast; ring
  rw [poisφ, harg, ← Complex.ofReal_exp,
    show ((c : ℂ) * I + (c : ℂ) * I) = 2 * (c : ℂ) * I from by ring]
  push_cast
  field_simp

/-! ## The uniform edge bound `‖F(s)‖ ≤ (R²−c²)⁻¹`. -/

/-- On the upper half-plane (`0 ≤ Im s`) and outside the disc of radius `R > c`,
the integrand is bounded by `(R²−c²)⁻¹`. -/
private lemma norm_poisF_le {θ c : ℝ} (hθ : 0 ≤ θ) {s : ℂ} (hsim : 0 ≤ s.im)
    {R : ℝ} (hRc : 0 < R ^ 2 - c ^ 2) (hsR : R ^ 2 ≤ ‖s‖ ^ 2) :
    ‖poisF θ c s‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
  have heq : (s + (c : ℂ) * I) * (s - (c : ℂ) * I) = s ^ 2 + ((c ^ 2 : ℝ) : ℂ) := by
    rw [show (s + (c : ℂ) * I) * (s - (c : ℂ) * I) = s ^ 2 - (c : ℂ) ^ 2 * I ^ 2 from by ring,
      Complex.I_sq]
    push_cast; ring
  have hncsq : ‖((c ^ 2 : ℝ) : ℂ)‖ = c ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
  have hlow : R ^ 2 - c ^ 2 ≤ ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := by
    have htri : ‖s ^ 2‖ - ‖((c ^ 2 : ℝ) : ℂ)‖ ≤ ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := by
      have := norm_sub_norm_le (s ^ 2) (-(((c ^ 2 : ℝ) : ℂ)))
      simpa using this
    rw [hncsq, norm_pow] at htri
    nlinarith [htri, hsR]
  have hDpos : 0 < ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ := lt_of_lt_of_le hRc hlow
  rw [norm_poisF, heq, div_le_iff₀ hDpos]
  have hexp1 : Real.exp (-(θ * s.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hθ hsim))
  have h1 : (R ^ 2 - c ^ 2)⁻¹ * (R ^ 2 - c ^ 2) = 1 := inv_mul_cancel₀ hRc.ne'
  have h2 : (R ^ 2 - c ^ 2)⁻¹ * (R ^ 2 - c ^ 2)
      ≤ (R ^ 2 - c ^ 2)⁻¹ * ‖s ^ 2 + ((c ^ 2 : ℝ) : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith

/-! ## The three non-bottom edges vanish as `R → ∞`. -/

/-- Any edge whose norm is eventually `≤ M·R/(R²−c²)` tends to `0`. -/
private lemma edge_tendsto {c : ℝ} (hc : 0 < c) {J : ℝ → ℂ} {M : ℝ}
    (hb : ∀ᶠ R in atTop, ‖J R‖ ≤ M * (R / (R ^ 2 - c ^ 2))) :
    Tendsto J atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb ?_
  simpa using (ratio_tendsto hc).const_mul M

/-- The top edge (`Im = R`) vanishes. -/
private lemma top_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I)) atTop (𝓝 0) := by
  refine edge_tendsto hc (M := 2) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ x ∈ Set.uIoc (-R) R, ‖poisF θ c ((x : ℂ) + (R : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro x _
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : ((x : ℂ) + (R : ℂ) * I).im = R := by simp
      rw [this]; exact hR0.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ x ^ 2 + R ^ 2 by positivity)]
      nlinarith [sq_nonneg x]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - -R| = 2 * R by rw [show R - -R = 2 * R by ring, abs_of_pos (by linarith)]] at hnorm
  calc ‖∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * (2 * R) := hnorm
    _ = 2 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-- The right edge (`Re = R`) vanishes. -/
private lemma right_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  refine edge_tendsto hc (M := 1) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ y ∈ Set.uIoc (0:ℝ) R, ‖poisF θ c ((R : ℂ) + (y : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro y hy
    rw [Set.uIoc_of_le hR0.le] at hy
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : ((R : ℂ) + (y : ℂ) * I).im = y := by simp
      rw [this]; exact hy.1.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ _ by positivity)]
      nlinarith [sq_nonneg y]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]] at hnorm
  calc ‖∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * R := hnorm
    _ = 1 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-- The left edge (`Re = −R`) vanishes. -/
private lemma left_tendsto {θ c : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 0) := by
  refine edge_tendsto hc (M := 1) ?_
  filter_upwards [eventually_gt_atTop c] with R hR
  have hR0 : 0 < R := lt_trans hc hR
  have hRc : 0 < R ^ 2 - c ^ 2 := by
    nlinarith [mul_pos (show (0:ℝ) < R - c by linarith) (show (0:ℝ) < R + c by linarith)]
  have hbd : ∀ y ∈ Set.uIoc (0:ℝ) R,
      ‖poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ (R ^ 2 - c ^ 2)⁻¹ := by
    intro y hy
    rw [Set.uIoc_of_le hR0.le] at hy
    refine norm_poisF_le hθ ?_ hRc ?_
    · have : (((-R : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
      rw [this]; exact hy.1.le
    · rw [Complex.norm_add_mul_I, Real.sq_sqrt (show (0:ℝ) ≤ _ by positivity)]
      nlinarith [sq_nonneg y]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [show |R - 0| = R by rw [sub_zero, abs_of_pos hR0]] at hnorm
  calc ‖∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (R ^ 2 - c ^ 2)⁻¹ * R := hnorm
    _ = 1 * (R / (R ^ 2 - c ^ 2)) := by rw [div_eq_mul_inv]; ring

/-! ## Assembly of the complex Poisson integral. -/

/-- `‖F(x)‖ = (c²+x²)⁻¹` on the real axis, hence `F(↑·)` is integrable. -/
private lemma norm_poisF_ofReal {θ c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖poisF θ c (t : ℂ)‖ = (c ^ 2 + t ^ 2)⁻¹ := by
  rw [poisF_ofReal, norm_div, Complex.norm_exp]
  have h1 : (((θ * t : ℝ) : ℂ) * I).re = 0 := by simp
  rw [h1, Real.exp_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < c ^ 2 + t ^ 2), one_div]

private lemma integrable_poisF_ofReal {θ c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => poisF θ c (t : ℂ)) := by
  refine (Salt.SW.integrable_inv_c_sq_add_sq hc).mono' ?_
    (Filter.Eventually.of_forall (fun t => le_of_eq (norm_poisF_ofReal hc t)))
  have he : (fun t : ℝ => poisF θ c (t : ℂ))
      = fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ) :=
    funext (fun t => poisF_ofReal θ c t)
  rw [he]
  refine (Continuous.div ?_ ?_ ?_).aestronglyMeasurable
  · fun_prop
  · fun_prop
  · exact fun t => Complex.ofReal_ne_zero.mpr (by positivity)

open Salt.SW in
/-- **The complex Poisson integral** (`θ ≥ 0`): `∫ e^{iθt}/(c²+t²) dt = (π/c)e^{-cθ}`. -/
private lemma cexp_pois_integral {c θ : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    ∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
      = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) := by
  set V : ℂ := ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ) with hV
  have hInt := integrable_poisF_ofReal (θ := θ) hc
  -- bottom edge converges to the full-line integral
  have hbot : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c (x : ℂ)) atTop
      (𝓝 (∫ t : ℝ, poisF θ c (t : ℂ))) :=
    intervalIntegral_tendsto_integral hInt tendsto_neg_atTop_atBot tendsto_id
  -- the eventual identity: bottom = residue + top − I·right + I·left
  have hrel : ∀ᶠ R : ℝ in atTop, (∫ x in (-R)..R, poisF θ c (x : ℂ))
      = V + (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
        - I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
        + I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) := by
    filter_upwards [eventually_gt_atTop c] with R hR
    have hres : rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c) = V := by
      rw [poisF_residue hc hR, poisφ_at_pole hc]
    have hunf : rectBI ((-R : ℝ) : ℂ) ((R : ℝ) + (R : ℝ) * I) (poisF θ c)
        = (∫ x in (-R)..R, poisF θ c (x : ℂ))
          - (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
          + I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
          - I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I)) := by
      rw [rectBI]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_zero,
        mul_zero, zero_mul, add_zero, mul_one, sub_zero, zero_add]
    rw [hunf] at hres
    linear_combination hres
  -- the top/right/left edges vanish
  have hsum : Tendsto (fun R : ℝ => V + (∫ x in (-R)..R, poisF θ c ((x : ℂ) + (R : ℂ) * I))
      - I * (∫ y in (0:ℝ)..R, poisF θ c ((R : ℂ) + (y : ℂ) * I))
      + I * (∫ y in (0:ℝ)..R, poisF θ c (((-R : ℝ) : ℂ) + (y : ℂ) * I))) atTop (𝓝 V) := by
    have h := (((tendsto_const_nhds (x := V)).add (top_tendsto hc hθ)).sub
      ((right_tendsto hc hθ).const_mul I)).add ((left_tendsto hc hθ).const_mul I)
    simpa using h
  have hbot2 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poisF θ c (x : ℂ)) atTop (𝓝 V) :=
    hsum.congr' (hrel.mono fun R h => h.symm)
  have key : (∫ t : ℝ, poisF θ c (t : ℂ)) = V := tendsto_nhds_unique hbot hbot2
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (poisF_ofReal θ c t).symm))

/-! ## K4' stone 1 — `cos_int_pair`. -/

/-- The `θ ≥ 0` case: `∫ cos(θt)/(c²+t²) = (π/c)e^{-cθ}` (real part of the complex integral). -/
private lemma cos_int_pair_nonneg {c θ : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) :
    ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2) = Real.pi / c * Real.exp (-(c * θ)) := by
  have hInt : Integrable
      (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
        = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
    rw [he]; exact integrable_poisF_ofReal hc
  have hre : ∀ t : ℝ,
      (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
        = Real.cos (θ * t) / (c ^ 2 + t ^ 2) := by
    intro t; rw [Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
  calc ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2)
      = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
        integral_congr_ae (Filter.Eventually.of_forall (fun t => (hre t).symm))
    _ = (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
        integral_re hInt
    _ = ((Real.pi / c * Real.exp (-(c * θ)) : ℝ) : ℂ).re := by rw [cexp_pois_integral hc hθ]
    _ = Real.pi / c * Real.exp (-(c * θ)) := Complex.ofReal_re _

/-- **K4' stone 1** (`cos_int_pair`, FROZEN).  The Fourier cosine transform of the
Poisson kernel: `∫ cos(θt)/(c²+t²) dt = (π/c)·e^{-c|θ|}`. -/
theorem cos_int_pair {c th : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Real.cos (th * t) / (c ^ 2 + t ^ 2) = Real.pi / c * Real.exp (-(c * |th|)) := by
  rw [← cos_int_pair_nonneg hc (abs_nonneg th)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  have hcos : Real.cos (th * t) = Real.cos (|th| * t) := by
    rcases abs_choice th with h1 | h1
    · rw [h1]
    · rw [h1, show (-th) * t = -(th * t) from by ring, Real.cos_neg]
  simp only [hcos]

/-! ## K4' stone 2 — `dirichlet_plancherel`. -/

/-- The sin transform of the Poisson kernel vanishes (odd integrand). -/
private lemma sin_int_zero {c θ : ℝ} (_hc : 0 < c) :
    ∫ t : ℝ, Real.sin (θ * t) / (c ^ 2 + t ^ 2) = 0 := by
  set f : ℝ → ℝ := fun t => Real.sin (θ * t) / (c ^ 2 + t ^ 2) with hf
  have hodd : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := by
    funext t
    simp only [hf]
    rw [show θ * -t = -(θ * t) by ring, Real.sin_neg, show (-t) ^ 2 = t ^ 2 by ring]
    ring
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have h1 : ∫ t : ℝ, f (-t) = ∫ t : ℝ, f t := hmp.integral_comp hemb f
  have h3 : ∫ t : ℝ, f (-t) = -∫ t : ℝ, f t := by rw [hodd, integral_neg]
  have : ∫ t : ℝ, f t = -∫ t : ℝ, f t := h1.symm.trans h3
  linarith

/-- **The full complex Poisson integral** (all real `θ`):
`∫ e^{iθt}/(c²+t²) dt = (π/c)e^{-c|θ|}` — real part is `cos_int_pair`, imaginary
part vanishes by `sin_int_zero`. -/
private lemma cexp_pois_full {c θ : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
      = ((Real.pi / c * Real.exp (-(c * |θ|)) : ℝ) : ℂ) := by
  have hInt : Integrable
      (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
        = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
    rw [he]; exact integrable_poisF_ofReal hc
  have hre : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
      = Real.pi / c * Real.exp (-(c * |θ|)) := by
    have hcos : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
          = Real.cos (θ * t) / (c ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          (integral_re hInt).symm
      _ = ∫ t : ℝ, Real.cos (θ * t) / (c ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hcos)
      _ = Real.pi / c * Real.exp (-(c * |θ|)) := cos_int_pair hc
  have him : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
      = 0 := by
    have hsin : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
          = Real.sin (θ * t) / (c ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).im :=
          (integral_im hInt).symm
      _ = ∫ t : ℝ, Real.sin (θ * t) / (c ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hsin)
      _ = 0 := sin_int_zero hc
  rw [← Complex.re_add_im
    (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)), hre, him]
  push_cast; ring

/-- The per-pair `cpow` decomposition: `(bₘ/mˢ)·conj(bₙ/nˢ)` factors into the
constant amplitude `bₘ b̄ₙ (mn)^{-c}` times the unit `e^{i(log n − log m)t}`. -/
private lemma pair_cpow {c t : ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (bm bn : ℂ) :
    (bm / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (bn / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
      = (bm * starRingEnd ℂ bn) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have em : (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hmC, ← Complex.natCast_log]
  have en : (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  have hrpow : (((m : ℝ) * (n : ℝ)) ^ c)⁻¹
      = Real.exp (-(c * (Real.log m + Real.log n))) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hm0.ne' hn0.ne', ← Real.exp_neg]
    ring_nf
  have hexp : Complex.exp (-((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)
        + starRingEnd ℂ ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I))))
      = (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
    rw [show ((((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ)) : ℂ)
        = Complex.exp ((-(c * (Real.log m + Real.log n)) : ℝ) : ℂ) by
      rw [hrpow, Complex.ofReal_exp], ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [em, en, map_div₀, ← Complex.exp_conj, div_mul_div_comm, div_eq_mul_inv,
    ← Complex.exp_add, ← Complex.exp_neg, hexp]
  ring

/-- **K4' stone 2** (`dirichlet_plancherel`, FROZEN).  The Dirichlet-polynomial
Plancherel bilinear form against the Poisson kernel: consumes `cos_int_pair` (via
`cexp_pois_full`) pair-by-pair.  Does NOT consume `MVHilbert`. -/
theorem dirichlet_plancherel (F : Finset ℕ) (b : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = Real.pi / c * ∑ m ∈ F, ∑ n ∈ F,
          (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(c * |Real.log m - Real.log n|)) := by
  -- integrability of each unit Poisson integrand
  have hg_int : ∀ θ : ℝ,
      Integrable (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) :=
    fun θ => by
      have he : (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
          = fun t : ℝ => poisF θ c (t : ℂ) := funext (fun t => (poisF_ofReal θ c t).symm)
      rw [he]; exact integrable_poisF_ofReal hc
  -- per-pair integrand as constant × unit Poisson integrand
  have hpint : ∀ m ∈ F, ∀ n ∈ F, Integrable (fun t : ℝ =>
      (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow (hF m hm) (hF n hn)]; ring
    rw [hrw]; exact (hg_int _).const_mul _
  -- per-pair integral value
  have hpval : ∀ m ∈ F, ∀ n ∈ F,
      ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)
        = (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / c * Real.exp (-(c * |Real.log n - Real.log m|)) : ℝ) : ℂ) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow (hF m hm) (hF n hn)]; ring
    rw [hrw, integral_const_mul, cexp_pois_full hc]
  -- expand the squared norm as a double sum over F × F
  have hsum_expand : ∀ t : ℝ,
      ((‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) := by
    intro t
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  -- reduce the real integral to the real part of the complex double-sum integral
  have hcplx : ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
      = (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / c * Real.exp (-(c * |Real.log n - Real.log m|)) : ℝ) : ℂ)).re := by
    have hpt : ∀ t : ℝ,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
        = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
      intro t
      have h1 : (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ))
          = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_div])
      rw [h1, ← hsum_expand t, Complex.div_ofReal_re, Complex.ofReal_re]
    calc ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (c ^ 2 + t ^ 2)
        = ∫ t : ℝ, (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ t : ℝ, ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_re (MeasureTheory.integrable_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn)))
      _ = (∑ m ∈ F, ∑ n ∈ F, ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((c ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
          rw [MeasureTheory.integral_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn))]
          refine congrArg _ (Finset.sum_congr rfl (fun m hm => ?_))
          rw [MeasureTheory.integral_finsetSum _ (fun n hn => hpint m hm n hn)]
      _ = _ := by rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl
            (fun n hn => hpval m hm n hn))]
  rw [hcplx, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    abs_sub_comm (Real.log n) (Real.log m), Nat.cast_mul, div_eq_mul_inv]
  ring

end Salt.MR
