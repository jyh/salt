/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.VonKoch
import Salt.SW.ContourShift

/-!
# O106 row R1, node N5 — the rectangle and its residue at `s = 1`

Under RH, `Zc` has no zero on `Re s > 1/2`, so

`φ(s) := (1 − (s − 1)·logDeriv Zc s) · y^s / s`

is holomorphic on the closed rectangle `[σ₀, c₀] × [−T, T]` for `1/2 < σ₀ < 1 < c₀`. This is the
refuter pass's repair 2: written through `Zc`, `φ(1) = y`, while the `ζ` form reads `0` at `1`.
The residues-lite Cauchy formula (`Salt.SW.rectBI_cif_eq`) then gives
`rectBI (σ₀ − iT) (c₀ + iT) (φ / (s − 1)) = 2πi · y`. Off `s = 1`,
`φ(s)/(s − 1) = −ζ′/ζ(s) · y^s/s` (`phiR_div_eq`), which is the Perron integrand on `Re s > 1`.
-/

namespace Salt.RH

open Complex Salt.SW

/-- The residue-carrying numerator. -/
noncomputable def phiR (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * logDeriv Zc s) * (y : ℂ) ^ s / s

theorem phiR_one {y : ℝ} : phiR y 1 = y := by
  simp [phiR]

/-- `logDeriv Zc` is differentiable wherever `Zc ≠ 0`. -/
theorem differentiableAt_logDeriv_Zc {s : ℂ} (hs : Zc s ≠ 0) :
    DifferentiableAt ℂ (logDeriv Zc) s := by
  have han : AnalyticAt ℂ Zc s := Zc_differentiable.analyticAt s
  have hd : DifferentiableAt ℂ (deriv Zc) s := han.deriv.differentiableAt
  have : logDeriv Zc = fun z => deriv Zc z / Zc z := by
    funext z; rw [logDeriv_apply]
  rw [this]
  exact hd.div (Zc_differentiable s) hs

theorem differentiableAt_phiR (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (phiR y) s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hZ := differentiableAt_logDeriv_Zc (zc_ne_zero_of_half_lt hRH hs)
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (y : ℂ) ^ z) s :=
    (differentiableAt_id.const_cpow (Or.inl hy0))
  unfold phiR
  refine DifferentiableAt.div ?_ differentiableAt_id hs0
  refine DifferentiableAt.mul ?_ hpow
  exact (differentiableAt_const _).sub ((differentiableAt_id.sub_const _).mul hZ)

/-- **N5.** Under RH, for `1/2 < σ₀ < 1 < c₀` and `T > 0`,
`rectBI (σ₀ − iT) (c₀ + iT) (φ / (s − 1)) = 2πi · y`. -/
theorem rectBI_phiR_eq (hRH : RiemannHypothesis) {y σ₀ c₀ T : ℝ} (hy : 0 < y)
    (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) (h2 : 1 < c₀) (hT : 0 < T) :
    rectBI ((σ₀ : ℂ) - (T : ℂ) * I) ((c₀ : ℂ) + (T : ℂ) * I) (fun s => phiR y s / (s - 1))
      = 2 * (Real.pi : ℂ) * I * y := by
  have hdiff : DifferentiableOn ℂ (phiR y)
      (closedRect ((σ₀ : ℂ) - (T : ℂ) * I) ((c₀ : ℂ) + (T : ℂ) * I)) := by
    intro s hs
    have hre : s.re ∈ Set.uIcc σ₀ c₀ := by
      have := (Complex.mem_reProdIm.mp hs).1
      simpa using this
    have hre' : σ₀ ≤ s.re := by
      rw [Set.uIcc_of_le (by linarith)] at hre; exact hre.1
    exact (differentiableAt_phiR hRH hy (by linarith)).differentiableWithinAt
  have h := rectBI_cif_eq (p := 1) hdiff (by simp; linarith) (by simp; linarith)
    (by refine ⟨?_, ?_⟩ <;> simp <;> linarith) (by refine ⟨?_, ?_⟩ <;> simp <;> linarith)
  rw [h, phiR_one]

/-- Off `s = 1`, with `ζ s ≠ 0`, the integrand is `−ζ′/ζ(s) · y^s / s`. -/
theorem phiR_div_eq {y : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    phiR y s / (s - 1) = -logDeriv riemannZeta s * Salt.MR.pk y s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hZc : Zc =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz1
    exact Zc_eq_of_ne hz1
  have hdz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd : deriv Zc s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hZc.deriv_eq]
    have h' : HasDerivAt (fun z => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id' s).sub_const 1).mul hdz.hasDerivAt
    rw [h'.deriv]
    ring
  have hld : logDeriv Zc s = 1 / (s - 1) + logDeriv riemannZeta s := by
    rw [logDeriv_apply, logDeriv_apply, hd, Zc_eq_of_ne hs1]
    field_simp
  unfold phiR Salt.MR.pk
  rw [hld]
  field_simp
  ring

end Salt.RH
