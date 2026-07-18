/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.ZetaPartialFractions

/-!
# VMVT-VK rung R7 — the parametric-radius Landau core (`VK-LANDAU-SCALED`)

`entire_norm_logDeriv_sub_sum_scaled` is the affine-scaled version of
`Salt.SW.entire_norm_logDeriv_sub_sum'`: the Borel–Carathéodory partial-fraction bound with the
sphere/ball radii `7/4, 3/2, 23/20` all multiplied by a free parameter `λ ∈ (0,1]`, and the cost
`120·log(4 M₀)` scaled to `(120/λ)·log(4 M₀)`.

The proof is a verbatim affine transport.  With `A w = c + λ·w`, `B s = (s − c)/λ` (mutually
inverse since `λ ≠ 0`), the precomposition `G = F ∘ A` is entire with center `0`; its spheres of
radius `7/4, 3/2` are `F`'s spheres of radius `(7/4)λ, (3/2)λ` about `c`, so
`entire_norm_logDeriv_sub_sum'` applies to `G` at center `0`.  The zero set, multiplicities, and
analytic remainder transport back by `A`; the extra scalar `∏ λ^{m}` is absorbed into the remainder
`h`, keeping the factorization exact (needed by `mem_zeros_of_factorization_gen`).  Since
`logDeriv F s = λ⁻¹·logDeriv G (B s)` (chain rule) and `∑ m/(s − A ρ) = λ⁻¹·∑ m/(B s − ρ)`, both the
`logDeriv h` identity and the numeric bound scale by `λ⁻¹`.

R7 = LITT-LANDAU, independently valuable: with the landed `zeta_strip_family` it completes the
Littlewood chain at a parametric radius (the hardcoded `7/4 − 3/2` geometry replaced by a free `λ`).
-/

namespace Salt.Vk

open Complex Metric Set

/-- **R7 — the parametric-radius Landau core.**  `Salt.SW.entire_norm_logDeriv_sub_sum'` with the
Borel–Carathéodory radii scaled by a free `λ ∈ (0,1]` and the cost scaled to `(120/λ)·log(4 M₀)`. -/
theorem entire_norm_logDeriv_sub_sum_scaled {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c : ℂ} {M₀ lam : ℝ} (hlam0 : 0 < lam) (hM₀ : 1 ≤ M₀) (hFc : (1 : ℝ) / 4 ≤ ‖F c‖)
    (hsphere74 : ∀ z ∈ sphere c (7 / 4 * lam), ‖F z‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere c (3 / 2 * lam), ‖F z‖ ≤ M₀) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball c (3 / 2 * lam) ∧ F ρ = 0) ∧
      AnalyticOnNhd ℂ h (ball c (3 / 2 * lam)) ∧
      (∀ z ∈ ball c (3 / 2 * lam), h z ≠ 0) ∧
      Set.EqOn F (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2 * lam)) ∧
      (∀ s ∈ ball c (3 / 2 * lam), F s ≠ 0 →
        logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) ∧
      (∀ s, ‖s - c‖ ≤ 23 / 20 * lam → F s ≠ 0 →
        ‖logDeriv F s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (120 / lam) * Real.log (4 * M₀)) := by
  classical
  set L : ℂ := (lam : ℂ) with hLdef
  have hL0 : L ≠ 0 := by rw [hLdef]; exact_mod_cast ne_of_gt hlam0
  have hLnorm : ‖L‖ = lam := by
    rw [hLdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  set A : ℂ → ℂ := fun w => c + L * w with hAdef
  set B : ℂ → ℂ := fun s => (s - c) / L with hBdef
  have hAB : ∀ s, A (B s) = s := by intro s; simp only [hAdef, hBdef]; field_simp; ring
  have hBA : ∀ w, B (A w) = w := by intro w; simp only [hAdef, hBdef]; field_simp; ring
  have hAinj : Function.Injective A := fun x y hxy => by
    simp only [hAdef, add_right_inj] at hxy; exact mul_left_cancel₀ hL0 hxy
  have hA_diff : Differentiable ℂ A := by simp only [hAdef]; fun_prop
  have hB_diff : Differentiable ℂ B := by simp only [hBdef]; fun_prop
  have hderivB : ∀ s, deriv B s = L⁻¹ := by
    intro s
    have hd1 : deriv (fun s : ℂ => s - c) s = 1 := by simp
    simp only [hBdef]; rw [deriv_div_const, hd1, one_div]
  set G : ℂ → ℂ := F ∘ A with hGdef
  have hG_diff : Differentiable ℂ G := hF.comp hA_diff
  have hG0 : G 0 = F c := by simp only [hGdef, Function.comp_apply, hAdef, mul_zero, add_zero]
  have hGeqF : ∀ s, G (B s) = F s := by
    intro s; simp only [hGdef, Function.comp_apply]; rw [hAB]
  -- apply the base at center `0`
  obtain ⟨ZG, mG, hGrem, hZmemG, hanaG, hneG, hEqOnG, hlogG, hnumG⟩ :=
    Salt.SW.entire_norm_logDeriv_sub_sum' (F := G) hG_diff (c := (0 : ℂ)) (M₀ := M₀) hM₀
      (by rw [hG0]; exact hFc)
      (by intro z hz
          have hzn : ‖z‖ = 7 / 4 := mem_sphere_zero_iff_norm.mp hz
          have hmem : A z ∈ sphere c (7 / 4 * lam) := by
            rw [mem_sphere_iff_norm]
            simp only [hAdef, add_sub_cancel_left, norm_mul, hLnorm, hzn]; ring
          simpa only [hGdef, Function.comp_apply] using hsphere74 (A z) hmem)
      (by intro z hz
          have hzn : ‖z‖ = 3 / 2 := mem_sphere_zero_iff_norm.mp hz
          have hmem : A z ∈ sphere c (3 / 2 * lam) := by
            rw [mem_sphere_iff_norm]
            simp only [hAdef, add_sub_cancel_left, norm_mul, hLnorm, hzn]; ring
          simpa only [hGdef, Function.comp_apply] using hsphere32 (A z) hmem)
  -- the transported witnesses
  set kprod : ℂ := ∏ ρ' ∈ ZG, L ^ (mG ρ') with hkprod
  have hkprod0 : kprod ≠ 0 := by
    rw [hkprod, Finset.prod_ne_zero_iff]; exact fun ρ' _ => pow_ne_zero _ hL0
  have hlognn : 0 ≤ Real.log (4 * M₀) := Real.log_nonneg (by nlinarith [hM₀])
  -- `B` maps the scaled ball into the base ball
  have hBmem : ∀ s ∈ ball c (3 / 2 * lam), B s ∈ ball (0 : ℂ) (3 / 2) := by
    intro s hs
    rw [mem_ball, dist_eq_norm, sub_zero]
    have : ‖B s‖ = ‖s - c‖ / lam := by simp only [hBdef, norm_div, hLnorm]
    rw [this, div_lt_iff₀ hlam0]
    have := mem_ball.mp hs; rw [dist_eq_norm] at this; nlinarith [this]
  -- the affine phase-transport identity, shared by the last two conjuncts
  have key_eq : ∀ s : ℂ,
      logDeriv F s - ∑ ρ ∈ ZG.image A, (mG (B ρ) : ℂ) / (s - ρ)
        = L⁻¹ * (logDeriv G (B s) - ∑ ρ' ∈ ZG, (mG ρ' : ℂ) / (B s - ρ')) := by
    intro s
    have hLD : logDeriv F s = L⁻¹ * logDeriv G (B s) := by
      have hFGB : F = G ∘ B := by funext x; simp only [Function.comp_apply, hGeqF]
      rw [show logDeriv F s = logDeriv (G ∘ B) s from by rw [← hFGB]]
      rw [logDeriv_comp (hG_diff (B s)) (hB_diff s), hderivB s]
      ring
    have hSum : ∑ ρ ∈ ZG.image A, (mG (B ρ) : ℂ) / (s - ρ)
        = L⁻¹ * ∑ ρ' ∈ ZG, (mG ρ' : ℂ) / (B s - ρ') := by
      rw [Finset.sum_image (fun x _ y _ hxy => hAinj hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ' _ => ?_)
      have hsA : s - A ρ' = L * (B s - ρ') := by simp only [hAdef, hBdef]; field_simp; ring
      rw [hBA, hsA, div_mul_eq_div_div_swap, div_eq_mul_inv, mul_comm]
    rw [hLD, hSum]; ring
  refine ⟨ZG.image A, fun ρ => mG (B ρ), fun z => kprod⁻¹ * hGrem (B z), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- zeros
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨ρ', hρ'ZG, rfl⟩ := hρ
    obtain ⟨hρ'ball, hGρ'⟩ := hZmemG ρ' hρ'ZG
    refine ⟨?_, hGρ'⟩
    rw [mem_ball, dist_eq_norm]
    have heq : ‖A ρ' - c‖ = lam * ‖ρ'‖ := by
      simp only [hAdef, add_sub_cancel_left, norm_mul, hLnorm]
    rw [heq]
    have : ‖ρ'‖ < 3 / 2 := by rw [← dist_zero_right]; exact mem_ball.mp hρ'ball
    nlinarith [this, hlam0]
  · -- AnalyticOnNhd of `h`
    have hBana : AnalyticOnNhd ℂ B (ball c (3 / 2 * lam)) :=
      hB_diff.differentiableOn.analyticOnNhd isOpen_ball
    have hcomp : AnalyticOnNhd ℂ (hGrem ∘ B) (ball c (3 / 2 * lam)) := hanaG.comp hBana hBmem
    have hkana : AnalyticOnNhd ℂ (fun _ : ℂ => kprod⁻¹) (ball c (3 / 2 * lam)) :=
      analyticOnNhd_const
    exact hkana.mul hcomp
  · -- non-vanishing of `h`
    intro z hz; exact mul_ne_zero (inv_ne_zero hkprod0) (hneG (B z) (hBmem z hz))
  · -- exact factorization
    intro z hz
    have hFz : F z = G (B z) := (hGeqF z).symm
    have hGBz : G (B z) = (∏ ρ' ∈ ZG, (B z - ρ') ^ (mG ρ')) * hGrem (B z) := hEqOnG (hBmem z hz)
    have hprod : (∏ ρ ∈ ZG.image A, (z - ρ) ^ (mG (B ρ)))
        = kprod * ∏ ρ' ∈ ZG, (B z - ρ') ^ (mG ρ') := by
      rw [Finset.prod_image (fun x _ y _ hxy => hAinj hxy), hkprod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun ρ' _ => ?_)
      have hzA : z - A ρ' = L * (B z - ρ') := by simp only [hAdef, hBdef]; field_simp; ring
      rw [hBA, hzA, mul_pow]
    simp only [hFz, hGBz, hprod]
    field_simp
  · -- logDeriv identity
    intro s hs hFs
    have hBs := hBmem s hs
    have hGBs_ne : G (B s) ≠ 0 := by rw [hGeqF s]; exact hFs
    rw [key_eq s, hlogG (B s) hBs hGBs_ne]
    have hhLD : logDeriv (fun z => kprod⁻¹ * hGrem (B z)) s = L⁻¹ * logDeriv hGrem (B s) := by
      rw [show (fun z => kprod⁻¹ * hGrem (B z)) = (fun z => kprod⁻¹ * (hGrem ∘ B) z) from rfl,
        logDeriv_const_mul s kprod⁻¹ (inv_ne_zero hkprod0),
        logDeriv_comp (hanaG (B s) hBs).differentiableAt (hB_diff s), hderivB s]
      ring
    rw [hhLD]
  · -- numeric
    intro s hs hFs
    have hGBs_ne : G (B s) ≠ 0 := by rw [hGeqF s]; exact hFs
    have hBs_norm : ‖B s - 0‖ ≤ 23 / 20 := by
      rw [sub_zero]
      have : ‖B s‖ = ‖s - c‖ / lam := by simp only [hBdef, norm_div, hLnorm]
      rw [this, div_le_iff₀ hlam0]; linarith [hs]
    have hnum := hnumG (B s) hBs_norm hGBs_ne
    rw [key_eq s, norm_mul, norm_inv, hLnorm]
    calc lam⁻¹ * ‖logDeriv G (B s) - ∑ ρ' ∈ ZG, (mG ρ' : ℂ) / (B s - ρ')‖
        ≤ lam⁻¹ * (120 * Real.log (4 * M₀)) :=
          mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = 120 / lam * Real.log (4 * M₀) := by rw [div_mul_eq_mul_div, div_eq_mul_inv]; ring

end Salt.Vk
