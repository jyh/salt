/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Region

/-!
# VMVT-VK — the growth-to-region bridge (growth-agnostic)

`region_of_uniform_growth` is the shared consumer of the landed R8/R9 disc assembly
(`zeta_zero_free_of_disc`) and the growth-to-sphere adapter (`Zc_ratio_sphere_bound`).  Given a
positive-height ζ-zero `ρ` (`ρ.im ≥ 2`), a disc parameter `Θ ≤ 1/2`, width parameters `Lq, dd`
verifying the three closing gates (`hσΘ ∧ hwΘ ∧ hchainC` at `M₀ = 5 Mζ/Θ`), and a **uniform**
growth bound `‖ζ z‖ ≤ Mζ` on the box `Re z ∈ [1−Θ, 2]`, `Im z ∈ [1, 3 ρ.im]` (which contains all
four Borel–Carathéodory spheres, both at height `γ` and at the doubled height `2γ`), the bridge
discharges the four sphere hypotheses and returns `ρ.re ≤ 1 − dd/(7 Lq)`.

This is the freeze's "one assembly, two instantiations": the Littlewood region
(`Salt/Vk/Littlewood.lean`, `zeta_strip_family` at `k ≈ log log t`) and the power region
(`Salt/Vk/PowRegion.lean`, `zeta_growth_pow`) both feed this bridge — only the growth input and the
`(Θ, Lq, dd)` selection differ.  The negative-`γ` half is handled by the callers via
`riemannZeta_conj_zero`.
-/

namespace Salt.Vk

open Complex Metric Set
open scoped Topology

open Salt.SW in
/-- **The growth-to-region bridge** (growth-agnostic).  A positive-height ζ-zero `ρ` with a uniform
growth bound `‖ζ z‖ ≤ Mζ` over the box `Re z ∈ [1−Θ, 2]`, `Im z ∈ [1, 3 ρ.im]` — which contains
every keep/drop Borel–Carathéodory sphere — yields `ρ.re ≤ 1 − dd/(7 Lq)`, provided the three
closing gates hold at `M₀ = 5 Mζ/Θ`.  The four sphere hypotheses of `zeta_zero_free_of_disc` are
discharged by `Zc_ratio_sphere_bound` fed by the box growth. -/
theorem region_of_uniform_growth {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hβ1 : ρ.re < 1)
    {Θ Mζ Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hγ2 : 2 ≤ ρ.im)
    (hMζ : 1 ≤ Mζ) (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq)
    (hσΘ : dd / Lq ≤ Θ / 2) (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * Mζ / Θ))) ≤ Lq / (2 * dd))
    (hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖riemannZeta z‖ ≤ Mζ) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have hγ1 : 1 ≤ |ρ.im| := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ.im)]; linarith
  have hM₀ : (1 : ℝ) ≤ 5 * Mζ / Θ := by
    rw [le_div_iff₀ hΘ0]; nlinarith [hMζ, hΘ12, hΘ0]
  -- the growth-to-sphere discharge over a τ-centered sphere of radius `R ≤ (3/2)Θ`
  have discharge : ∀ (τ R : ℝ), 0 ≤ R → R ≤ 3 / 2 * Θ → 1 ≤ |τ| → ρ.im - 1 + R ≤ τ →
      τ + R ≤ 3 * ρ.im →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 5 * Mζ / Θ := by
    intro τ R hR0 hR hτ hτlo hτhi z hz
    have hzc : ‖z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = R := by
      rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hcre : (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I).re = 1 + Θ / 2 := by simp
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I))
      rw [Complex.sub_re, hcre, hzc] at h; exact h
    have himb : |z.im - τ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I))
      rw [Complex.sub_im, hcim, hzc] at h; exact h
    have hre1 : 1 - Θ ≤ z.re := by have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    have hre2 : z.re ≤ 2 := by have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    have him1 : ρ.im - 1 ≤ z.im := by have := (abs_le.mp himb).1; linarith [hτlo]
    have him2 : z.im ≤ 3 * ρ.im := by have := (abs_le.mp himb).2; linarith [hτhi]
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hτ hMζ hR0 hR hz (hgrowth z hre1 hre2 him1 him2)
  -- radius bookkeeping: both sphere radii are `≤ (3/2)Θ`
  have hR74 : (7 : ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3 : ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR74' : (0 : ℝ) ≤ 7 / 4 * (6 * Θ / 7) := by positivity
  have hR32' : (0 : ℝ) ≤ 3 / 2 * (6 * Θ / 7) := by positivity
  have hγ2τ : (1 : ℝ) ≤ |2 * ρ.im| := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ρ.im)]; linarith
  refine zeta_zero_free_of_disc hρ0 hβ1 hγ1 hΘ0 (by linarith [hΘ12]) hM₀ hdd hddlt hLq0 hσΘ hwΘ
    hchainC ?_ ?_ ?_ ?_
  · exact discharge ρ.im _ hR74' hR74 hγ1 (by nlinarith [hΘ12]) (by nlinarith [hΘ12, hγ2])
  · exact discharge ρ.im _ hR32' hR32 hγ1 (by nlinarith [hΘ12]) (by nlinarith [hΘ12, hγ2])
  · exact discharge (2 * ρ.im) _ hR74' hR74 hγ2τ (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2])
  · exact discharge (2 * ρ.im) _ hR32' hR32 hγ2τ (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2])

end Salt.Vk
