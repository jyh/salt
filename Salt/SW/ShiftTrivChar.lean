/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ShiftAssembly
import Salt.SW.ZetaPartialFractions
import Salt.SW.EulerBridge
import Salt.SW.ZeroFreeReal
import Salt.SW.ZetaZeroFree

/-!
# The SW rung, wave S5d — the χ₀ (trivial character) contour-shift variant

Design: `docs/blueprints/sw.md`, wave S5; the flags "SW S5c"/"SW S5d". This module extends the clean
contour-shift bound `Salt.SW.psi1_contour_shift` (S5b) / the exceptional variant
`Salt.SW.psi1_contour_shift_exceptional` (S5c) to the **trivial character**
`χ₀ = (1 : DirichletCharacter ℂ q)`,
whose L-function has a **simple pole at `s = 1`** (inside the box `σ₀ < 1 < c`). The contour shift
picks up the residue there, so the bound reads `‖ψ₁(x, χ₀) − x²/2‖ ≤ (1/2π)·E₀` (main term
**subtracted**).

The mechanism is the exceptional variant's G-trick, with the **pole in place of the zero** and the
**opposite residue sign**. mathlib's `LFunctionTrivChar₁ q` (denote `Wq`) is the *entire* de-poled
trivial L-function: `Wq s = (s−1)·L(χ₀, s)` off `1`, `Wq 1 = ∏_{p∣q}(1−p⁻¹) ≠ 0`
(`LFunctionTrivChar₁_apply_one_ne_zero`), `Differentiable ℂ Wq`
(`differentiable_LFunctionTrivChar₁`).
So near `1`, `−L'/L(χ₀) = −logDeriv Wq + 1/(s−1)`, i.e. the de-singularized integrand
`Gtrue := −logDeriv Wq` is analytic through `1` with **no `Function.update` gluing needed**. The
zeros
of `Wq` (off `1`) are the zeros of `ζ` (the Euler factors `1−p^{−s}` are nonzero on `Re > 0`), so
the
box non-vanishing reduces to the ζ zero-free hypothesis `hzfζ`.

With `A := ker·Gtrue` (analytic on the box, `rectBI A = 0`), `Bfun := ker/(·−1)`
(`rectBI Bfun = 2πi·ker(1) = 2πi·x²/2` via `kernel_residue`) and `F = A + Bfun` off `1` (the pole's
principal part enters with **`+`**, opposite to the zero's `−`), Goursat linearity gives
`rectBI F = 2πi·κ`, `κ = x²/2`, so `‖ψ₁ − κ‖ ≤ (1/2π)·E₀`.

The edge bound on `‖logDeriv L(χ₀)‖` is taken as the named hypothesis `hedge` (PB-floor A): the
concrete constant is `‖logDeriv Zc‖ + ‖logDeriv ∏(1−p^{−s})‖ + 1/(s−1)` — the landed Zc numeric plus
the Euler-correction bound (`norm_logDeriv_eulerCorr_trivChar_le`, proved below for `Re ≥ 9/10`)
plus
the pole term `≤ 1/w` (which needs the pole `w`-separated from the left edge, i.e. `σ₀ + w ≤ 1` —
the
exact mirror of the exceptional variant's `hβsep : σ₀ + w ≤ β₁` with `β₁ = 1`; see the module note).

All results axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no new
axioms,
no `sorry`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set Metric MeromorphicOn Function
  MeasureTheory
open scoped LSeries.notation Topology

namespace Salt.SW

/-! ## 1. The Euler-correction edge bound at the `9/10` threshold -/

/-- **Per-factor Euler bound at `Re ≥ 9/10`.** For a character `ψ` and prime `p`,
`‖logDeriv (1 − ψ(p) p^{−s})‖ ≤ 2·log p` on `Re s ≥ 9/10`. The term is
`ψ(p) log p · p^{−s} / (1 − ψ(p) p^{−s})`, of norm `≤ log p · p^{−σ}/(1 − p^{−σ}) ≤ 2·log p` since
`p^{−σ} ≤ 2^{−9/10} ≤ 2/3` for `p ≥ 2, σ ≥ 9/10`. (Threshold analogue of
`norm_logDeriv_eulerFactor_le`, which needs `σ ≥ 1`.) -/
theorem norm_logDeriv_eulerFactor_le_threshold {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 9 / 10 ≤ s.re) :
    ‖logDeriv (eulerFactor ψ p) s‖ ≤ 2 * Real.log p := by
  have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hLnn : 0 ≤ Real.log p := Real.log_nonneg hP1
  have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := (Complex.ofReal_natCast p).symm
  set pσ : ℝ := (p : ℝ) ^ (-s.re) with hpσ
  have hpσ0 : 0 < pσ := Real.rpow_pos_of_pos hP0 _
  -- `p^{−σ} ≤ 2/3`: from `p^σ ≥ 2^{9/10} ≥ 3/2`.
  have h2910 : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (9 / 10 : ℝ) := by
    have e : ((2 : ℝ) ^ (9 / 10 : ℝ)) ^ (10 : ℕ) = 512 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (9 / 10 : ℝ)) 10,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        show (9 / 10 : ℝ) * ((10 : ℕ) : ℝ) = 9 by norm_num,
        show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    apply le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    rw [e]; norm_num
  have hpσσ : (3 / 2 : ℝ) ≤ (p : ℝ) ^ s.re := by
    have hb1 : (2 : ℝ) ^ (9 / 10 : ℝ) ≤ (2 : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    have hb2 : (2 : ℝ) ^ s.re ≤ (p : ℝ) ^ s.re :=
      Real.rpow_le_rpow (by norm_num) hP2 (by linarith)
    linarith
  have hpσ_23 : pσ ≤ 2 / 3 := by
    have h1 : (1 : ℝ) / ((p : ℝ) ^ s.re) ≤ 1 / (3 / 2) :=
      one_div_le_one_div_of_le (by norm_num) hpσσ
    rw [hpσ, Real.rpow_neg hP0.le, ← one_div]
    linarith [h1, show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num]
  have hden : 0 < 1 - pσ := by linarith
  have hderiv : deriv (eulerFactor ψ p) s = ψ p * (p : ℂ) ^ (-s) * Complex.log p :=
    (hasDerivAt_eulerFactor ψ hp s).deriv
  have hcpow : ‖(p : ℂ) ^ (-s)‖ = pσ := by
    rw [hpσ, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hP0, Complex.neg_re]
  have hlogp : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [hcast, ← Complex.ofReal_log hP0.le, Complex.norm_of_nonneg (Real.log_nonneg hP1)]
  have hnum : ‖deriv (eulerFactor ψ p) s‖ ≤ pσ * Real.log p := by
    rw [hderiv, norm_mul, norm_mul, hcpow, hlogp]
    calc ‖ψ p‖ * pσ * Real.log p ≤ 1 * pσ * Real.log p := by gcongr; exact ψ.norm_le_one _
      _ = pσ * Real.log p := by ring
  have hfac : 1 - pσ ≤ ‖eulerFactor ψ p s‖ := by
    have hX : ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ pσ := by
      rw [norm_mul, hcpow]
      calc ‖ψ p‖ * pσ ≤ 1 * pσ := by gcongr; exact ψ.norm_le_one _
        _ = pσ := one_mul _
    have hsub : ‖(1 : ℂ)‖ - ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ ‖eulerFactor ψ p s‖ := by
      rw [eulerFactor]; exact norm_sub_norm_le _ _
    rw [norm_one] at hsub
    linarith
  have hfac0 : 0 < ‖eulerFactor ψ p s‖ := lt_of_lt_of_le hden hfac
  rw [logDeriv_apply, norm_div, div_le_iff₀ hfac0]
  calc ‖deriv (eulerFactor ψ p) s‖
      ≤ pσ * Real.log p := hnum
    _ ≤ 2 * Real.log p * (1 - pσ) := by
        nlinarith [mul_nonneg hLnn (show (0:ℝ) ≤ 2 - 3 * pσ by linarith), hLnn, hpσ_23]
    _ ≤ 2 * Real.log p * ‖eulerFactor ψ p s‖ := by
        apply mul_le_mul_of_nonneg_left hfac; positivity

/-- **The χ₀ Euler-correction edge bound (`Re ≥ 9/10`).** `‖logDeriv ∏_{p∣q}(1−p^{−s})‖ ≤ 2·log q`.
The finite product `∏_{p∣q}(1−p^{−s})` is `L(χ₀)/ζ`; taking `logDeriv` sums the per-factor bounds
(`norm_logDeriv_eulerFactor_le_threshold` via the mod-1 `eulerFactor`), and
`∑ log p = log(∏ p) ≤ log q` (`Nat.prod_primeFactors_dvd`). -/
theorem norm_logDeriv_eulerCorr_trivChar_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 9 / 10 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s‖
      ≤ 2 * Real.log (q : ℝ) := by
  have hspos : (0 : ℝ) < s.re := by linarith
  have hfac_ne : ∀ p ∈ q.primeFactors, (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp
    have h := eulerFactor_ne_zero (1 : DirichletCharacter ℂ 1)
      (Nat.prime_of_mem_primeFactors hp) hspos
    rwa [eulerFactor_one_eq p] at h
  have hfac_diff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s := by
    intro p hp
    have h := differentiableAt_eulerFactor (1 : DirichletCharacter ℂ 1)
      (Nat.prime_of_mem_primeFactors hp) s
    rwa [eulerFactor_one_eq p] at h
  have hPsum : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s
      = ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    logDeriv_prod hfac_ne hfac_diff
  rw [hPsum]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, 2 * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have h := norm_logDeriv_eulerFactor_le_threshold (1 : DirichletCharacter ℂ 1)
          (Nat.prime_of_mem_primeFactors hp) hs
        rwa [eulerFactor_one_eq p] at h
    _ = 2 * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod, Finset.mul_sum]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
    _ ≤ 2 * Real.log (q : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.log_le_log
        · apply Finset.prod_pos
          exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
            (Nat.prod_primeFactors_dvd q)

/-! ## 1b. The `Zc` edge bound (entire-base numeric + Blaschke count, distance form) -/

/-- `M0zeta` is monotone in `|t₀|`. -/
lemma M0zeta_le_of_abs_le {a b : ℝ} (hab : |a| ≤ b) : M0zeta a ≤ M0zeta b := by
  have hTnn : (0 : ℝ) ≤ b := le_trans (abs_nonneg a) hab
  rw [M0zeta, M0zeta, abs_of_nonneg hTnn]
  nlinarith [abs_nonneg a, hab]

/-- **The `Zc` shifted-contour numeric, distance form.** The `Zc`-analogue of
`Salt.SW.norm_logDeriv_le_of_ball_dist`: for `s` on the shifted contour (`9/10 ≤ Re s ≤ 2`,
`|Im s| ≤ T`) with `Zc s ≠ 0`, if every zero `ρ` of `Zc` in the Borel–Carathéodory ball
`ball (2+iγ) (3/2)` (`γ = Im s`) satisfies `w ≤ ‖s − ρ‖`, then
`‖logDeriv Zc s‖ ≤ 120·log(4·M₀ζ(T)) + (log(4·M₀ζ(T))/log(7/6))/w`. Route: the entire-base numeric
`entire_norm_logDeriv_sub_sum'` (spheres bounded by `Zc_sphere_bound`, center by `Zc_center_lower`),
the Blaschke count `entire_zero_count_le`, and the distance hypothesis `hdist`. -/
lemma norm_logDeriv_Zc_le_of_ball_dist {T w : ℝ} (hw : 0 < w) {s : ℂ}
    (hslb : 9 / 10 ≤ s.re) (hsub : s.re ≤ 2) (hsim : |s.im| ≤ T) (hZcs : Zc s ≠ 0)
    (hdist : ∀ ρ : ℂ, Zc ρ = 0 → ρ ∈ Metric.ball (2 + (s.im : ℂ) * I) (3 / 2) → w ≤ ‖s - ρ‖) :
    ‖logDeriv Zc s‖
      ≤ 120 * Real.log (4 * M0zeta T)
        + (Real.log (4 * M0zeta T) / Real.log (7 / 6)) / w := by
  classical
  set c₀ : ℂ := 2 + (s.im : ℂ) * I with hc₀
  set M₀ : ℝ := M0zeta s.im with hM₀
  set M₀T : ℝ := M0zeta T with hM₀T
  have hM₀1 : 1 ≤ M₀ := one_le_M0zeta s.im
  have hM₀TgeM₀ : M₀ ≤ M₀T := M0zeta_le_of_abs_le hsim
  have hM₀T1 : 1 ≤ M₀T := le_trans hM₀1 hM₀TgeM₀
  have hlog4M₀pos : 0 < Real.log (4 * M₀) := Real.log_pos (by linarith)
  have hlog4M₀Tpos : 0 < Real.log (4 * M₀T) := Real.log_pos (by linarith)
  have hlog4mono : Real.log (4 * M₀) ≤ Real.log (4 * M₀T) :=
    Real.log_le_log (by linarith) (by linarith)
  have hsphere74 : ∀ z ∈ sphere c₀ (7 / 4), ‖Zc z‖ ≤ M₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact Zc_sphere_bound s.im (le_refl _) hz
  have hsphere32 : ∀ z ∈ sphere c₀ (3 / 2), ‖Zc z‖ ≤ M₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz; exact Zc_sphere_bound s.im (by norm_num) hz
  obtain ⟨Z, m, h, hZmem, hana_h, hne_h, hEqOn, hident, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable hM₀1 (Zc_center_lower s.im) hsphere74 hsphere32
  have hsc : ‖s - c₀‖ ≤ 23 / 20 := by
    have hre : (s - c₀).re = s.re - 2 := by rw [hc₀]; simp
    have him : (s - c₀).im = 0 := by rw [hc₀]; simp
    have hnorm : ‖s - c₀‖ = |s.re - 2| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, show (0 : ℝ) ^ 2 = 0 by ring, add_zero,
        Real.sqrt_sq_eq_abs]
    rw [hnorm, abs_of_nonpos (by linarith : s.re - 2 ≤ 0)]; linarith
  have hana_univ : AnalyticOnNhd ℂ Zc univ :=
    Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hana32 : AnalyticOnNhd ℂ Zc (ball c₀ (3 / 2)) := hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ Zc (closedBall c₀ (3 / 2)) := hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z, (divisor Zc (ball c₀ (3 / 2))) ρ = (m ρ : ℤ) := by
    intro ρ hρ
    have hρball := (hZmem ρ hρ).1
    have horder : analyticOrderAt Zc ρ = (m ρ : ℕ∞) :=
      analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρ hρball
    rw [hana32.divisor_apply hρball, horder]; simp
  have hsupp : (Function.support (fun u => divisor Zc (ball c₀ (3 / 2)) u)) ⊆ ↑Z := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρball : ρ ∈ ball c₀ (3 / 2) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hρ0 : Zc ρ = 0 := by
      by_contra hne0
      apply hρ
      rw [hana32.divisor_apply hρball, (hana32 ρ hρball).analyticOrderAt_eq_zero.mpr hne0]; simp
    exact (mem_zeros_of_factorization_gen hne_h hEqOn hρball hρ0).1
  have hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z, (m ρ : ℤ)) = ∑ ρ ∈ Z, divisor Zc (ball c₀ (3 / 2)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ; rw [hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z, divisor Zc (ball c₀ (3 / 2)) ρ)
        = ∑ᶠ u, divisor Zc (ball c₀ (3 / 2)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp).symm
    have hdle : ∀ u : ℂ, divisor Zc (ball c₀ (3 / 2)) u
        ≤ divisor Zc (closedBall c₀ (3 / 2)) u := by
      intro u
      by_cases hu : u ∈ ball c₀ (3 / 2)
      · exact le_of_eq
          (by rw [hana32.divisor_apply hu, hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball :
        (Function.support (fun u => divisor Zc (ball c₀ (3 / 2)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb :
        (Function.support (fun u => divisor Zc (closedBall c₀ (3 / 2)) u)).Finite :=
      (divisor Zc (closedBall c₀ (3 / 2))).finiteSupport (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor Zc (ball c₀ (3 / 2)) u
        ≤ ∑ᶠ u, divisor Zc (closedBall c₀ (3 / 2)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hcountJ := entire_zero_count_le Zc_differentiable (Zc_center_lower s.im) (r := 3 / 2)
      (R := 7 / 4) (M := M₀) (by norm_num) (by norm_num) hM₀1 hsphere74
    calc (∑ ρ ∈ Z, (m ρ : ℝ))
        = ((∑ ρ ∈ Z, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor Zc (ball c₀ (3 / 2)) u : ℤ) : ℝ) := by rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor Zc (closedBall c₀ (3 / 2)) u : ℤ) : ℝ) := by exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 / (3 / 2)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 / (3 / 2) = 7 / 6 by norm_num]
  have hdist' : ∀ ρ ∈ Z, w ≤ ‖s - ρ‖ :=
    fun ρ hρ => hdist ρ (hZmem ρ hρ).2 (hZmem ρ hρ).1
  have hnumbound := hnum s hsc hZcs
  have hSumNorm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / w := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist' ρ hρ
          have hdpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hw hd
          rw [div_le_div_iff₀ hdpos hw]
          nlinarith [Nat.cast_nonneg (α := ℝ) (m ρ), hd]
      _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by rw [Finset.sum_div]
  have hsplit : ‖logDeriv Zc s‖
      ≤ ‖logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
    calc ‖logDeriv Zc s‖
        = ‖(logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hcount' : (∑ ρ ∈ Z, (m ρ : ℝ)) / w ≤ (Real.log (4 * M₀T) / Real.log (7 / 6)) / w := by
    rw [div_le_div_iff_of_pos_right hw]
    apply le_trans hcount
    rw [div_le_div_iff_of_pos_right h76]; exact hlog4mono
  have hnum' : ‖logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 120 * Real.log (4 * M₀T) := by
    calc ‖logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ 120 * Real.log (4 * M₀) := hnumbound
      _ ≤ 120 * Real.log (4 * M₀T) := by linarith [hlog4mono]
  calc ‖logDeriv Zc s‖
      ≤ 120 * Real.log (4 * M₀T) + (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
        linarith [hsplit, hnum', hSumNorm]
    _ ≤ 120 * Real.log (4 * M₀T) + (Real.log (4 * M₀T) / Real.log (7 / 6)) / w := by
        linarith [hcount']

/-! ## 2. The `c`-line integrability of the χ₀ contour integrand -/

/-- The χ₀ contour integrand `F(c+v·I)` is `ℝ`-integrable on the `c`-line (`1 < c ≤ 2`), dominated
by `(1/(c−1)+1)·x^{c+1}·(c²+v²)⁻¹`. The χ₀ variant of `contour_integrand_integrable`: since
`L(χ₀)` is not entire (pole at `1`), continuity of `L(χ₀)`/`deriv L(χ₀)` is taken on the open
half-plane `{Re > 1}` (differentiable there via `differentiableAt_LFunction _ _ (Or.inl _)`) and
composed with the `c`-line; the norm bound `‖logDeriv L(χ₀)‖ ≤ 1/(c−1)+1` is the character-agnostic
`norm_logDeriv_le_of_re`. -/
lemma contour_integrand_integrable_trivChar (q : ℕ) [NeZero q] {x : ℝ} (hx : 1 ≤ x)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) :
    Integrable (fun v : ℝ =>
      (x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
        * (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((c : ℂ) + v * I))) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hcpos : (0 : ℝ) < c := by linarith
  set Lf : ℂ → ℂ := LFunction (1 : DirichletCharacter ℂ q) with hLdef
  have hUopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLana : AnalyticOnNhd ℂ Lf {s : ℂ | 1 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro s hs
    have hsne1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
    exact (differentiableAt_LFunction _ s (Or.inl hsne1)).differentiableWithinAt
  have hLcontU : ContinuousOn Lf {s : ℂ | 1 < s.re} := hLana.continuousOn
  have hdLcontU : ContinuousOn (deriv Lf) {s : ℂ | 1 < s.re} := hLana.deriv.continuousOn
  have hline : Continuous (fun v : ℝ => (c : ℂ) + v * I) := by fun_prop
  have hmaps : ∀ v : ℝ, ((c : ℂ) + v * I) ∈ {s : ℂ | 1 < s.re} := by
    intro v; simp only [Set.mem_setOf_eq]; rw [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    simp; linarith
  have hLne : ∀ v : ℝ, Lf ((c : ℂ) + v * I) ≠ 0 := fun v => by
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    exact LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q)
      (Or.inr (by intro h; rw [h] at hre; simp at hre; linarith)) (by rw [hre]; linarith)
  have hdenne : ∀ v : ℝ, ((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1) ≠ 0 := fun v =>
    mul_ne_zero (s_ne_zero hcpos v) (s1_ne_zero hcpos v)
  have hFcont : Continuous (fun v : ℝ =>
      (x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
        * (-logDeriv Lf ((c : ℂ) + v * I))) := by
    apply Continuous.mul
    · apply Continuous.div
      · exact (by fun_prop : Continuous fun v : ℝ => ((c : ℂ) + v * I) + 1).const_cpow (Or.inl hxC)
      · fun_prop
      · exact hdenne
    · have hrw : (fun v : ℝ => -logDeriv Lf ((c : ℂ) + v * I))
          = fun v : ℝ => -(deriv Lf ((c : ℂ) + v * I) / Lf ((c : ℂ) + v * I)) := by
        funext v; rw [logDeriv_apply]
      rw [hrw]
      exact (((hdLcontU.comp_continuous hline hmaps).div
        (hLcontU.comp_continuous hline hmaps) hLne)).neg
  refine (Integrable.mono'
    ((integrable_inv_c_sq_add_sq hcpos).const_mul (x ^ (c + 1) * (1 / (c - 1) + 1)))
    hFcont.aestronglyMeasurable ?_)
  filter_upwards with v
  have h1 : ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1)‖ = x ^ (c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]; congr 1; simp
  have h2 : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
    norm_inv_denom_le hcpos v
  have hre_v : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
  have h3 : ‖logDeriv Lf ((c : ℂ) + v * I)‖ ≤ 1 / (c - 1) + 1 := by
    have hh := norm_logDeriv_le_of_re (1 : DirichletCharacter ℂ q) (s := (c : ℂ) + v * I)
      (by rw [hre_v]; linarith) (by rw [hre_v]; linarith)
    rwa [hre_v] at hh
  have h3nn : (0 : ℝ) ≤ 1 / (c - 1) + 1 := by positivity
  have hxc1nn : (0 : ℝ) ≤ x ^ (c + 1) := by positivity
  calc ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1) / (((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))
          * (-logDeriv Lf ((c : ℂ) + v * I))‖
      = ‖(x : ℂ) ^ (((c : ℂ) + v * I) + 1)‖ * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
          * ‖logDeriv Lf ((c : ℂ) + v * I)‖ := by
        rw [norm_mul, norm_neg, norm_div, norm_inv, div_eq_mul_inv]
    _ ≤ x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ * (1 / (c - 1) + 1) := by rw [h1]; gcongr
    _ = x ^ (c + 1) * (1 / (c - 1) + 1) * (c ^ 2 + v ^ 2)⁻¹ := by ring

/-! ## 3. Edge-wise additivity of `rectBI` (the residue-carrying `+` split) -/

/-- **Edge-wise linearity of `rectBI` (additive form).** If `F = A + B` pointwise on the four edges
of the rectangle (with `A`, `B` interval-integrable on each edge), then
`rectBI z w F = rectBI z w A + rectBI z w B`. The χ₀ pole variant splits the shifted integrand
`F = ker·(−L'/L)` into the analytic `A = ker·Gtrue` and the residue kernel `B = ker/(·−1)` with a
**`+`** (the pole's principal part enters positively). Mirror of `rectBI_sub_of_edge_eq`. -/
lemma rectBI_add_of_edge_eq {z w : ℂ} {F A B : ℂ → ℂ}
    (hA_bot : IntervalIntegrable (fun x : ℝ => A (↑x + ↑z.im * I)) volume z.re w.re)
    (hA_top : IntervalIntegrable (fun x : ℝ => A (↑x + ↑w.im * I)) volume z.re w.re)
    (hA_rgt : IntervalIntegrable (fun y : ℝ => A (↑w.re + ↑y * I)) volume z.im w.im)
    (hA_lft : IntervalIntegrable (fun y : ℝ => A (↑z.re + ↑y * I)) volume z.im w.im)
    (hB_bot : IntervalIntegrable (fun x : ℝ => B (↑x + ↑z.im * I)) volume z.re w.re)
    (hB_top : IntervalIntegrable (fun x : ℝ => B (↑x + ↑w.im * I)) volume z.re w.re)
    (hB_rgt : IntervalIntegrable (fun y : ℝ => B (↑w.re + ↑y * I)) volume z.im w.im)
    (hB_lft : IntervalIntegrable (fun y : ℝ => B (↑z.re + ↑y * I)) volume z.im w.im)
    (hbot : Set.EqOn (fun x : ℝ => F (↑x + ↑z.im * I))
      (fun x : ℝ => A (↑x + ↑z.im * I) + B (↑x + ↑z.im * I)) (Set.uIcc z.re w.re))
    (htop : Set.EqOn (fun x : ℝ => F (↑x + ↑w.im * I))
      (fun x : ℝ => A (↑x + ↑w.im * I) + B (↑x + ↑w.im * I)) (Set.uIcc z.re w.re))
    (hrgt : Set.EqOn (fun y : ℝ => F (↑w.re + ↑y * I))
      (fun y : ℝ => A (↑w.re + ↑y * I) + B (↑w.re + ↑y * I)) (Set.uIcc z.im w.im))
    (hlft : Set.EqOn (fun y : ℝ => F (↑z.re + ↑y * I))
      (fun y : ℝ => A (↑z.re + ↑y * I) + B (↑z.re + ↑y * I)) (Set.uIcc z.im w.im)) :
    rectBI z w F = rectBI z w A + rectBI z w B := by
  simp only [rectBI]
  rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr htop,
      intervalIntegral.integral_congr hrgt, intervalIntegral.integral_congr hlft,
      intervalIntegral.integral_add hA_bot hB_bot, intervalIntegral.integral_add hA_top hB_top,
      intervalIntegral.integral_add hA_rgt hB_rgt, intervalIntegral.integral_add hA_lft hB_lft]
  ring

/-! ## 4. The χ₀ contour-shift bound -/

set_option maxHeartbeats 2000000 in
-- The χ₀ assembly runs the S5c exceptional argument on the de-singularized integrand `A = ker·Gtrue`
-- (`Gtrue = −logDeriv (LFunctionTrivChar₁ q)`, entire and nonzero at the pole `1`) and re-attaches
-- the χ₀ pole residue `x²/2` via `kernel_residue` at `β = 1`; the copied edge/tail estimates plus
-- the `E`-arithmetic need headroom.
/-- **S5d — the contour-shift bound, χ₀ (trivial character) variant.** For `χ₀ = 1 mod q`, whose
L-function has a simple pole at `s = 1` (inside the box `σ₀ < 1 < c`), the contour shift subtracts
the pole residue `x²/2`: `‖ψ₁(x, χ₀) − x²/2‖ ≤ (1/2π)·E₀`. The edge bound
`‖logDeriv L(χ₀)‖ ≤ B₀` on the box is the named hypothesis `hedge` (dischargeable from the landed
`Zc` numeric + the Euler-correction bound `norm_logDeriv_eulerCorr_trivChar_le` + the pole term
`1/(s−1)`); `E₀` has S5b's clean shape with `B → B₀`. The box non-vanishing reduces to the ζ
zero-free hypothesis `hzfζ` (the Euler factors are nonzero on `Re > 0`, and `LFunctionTrivChar₁ q`
is nonzero at `1`). -/
theorem psi1_contour_shift_trivchar (q : ℕ) [NeZero q] {x : ℝ} (hx : 3 ≤ x) {T σ₀ w B₀ : ℝ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1)
    (hzfζ : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False)
    (hedge : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T → (s.re = σ₀ ∨ |s.im| = T) →
      ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s‖ ≤ B₀) :
    ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x : ℂ) ^ 2 / 2‖ ≤ (1 / (2 * Real.pi)) *
      (2 * ((1 + 1 / Real.log x) - σ₀) * B₀ * x ^ ((1 + 1 / Real.log x) + 1) / T ^ 2
        + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀)
        + (Real.log x + 1) * x ^ ((1 + 1 / Real.log x) + 1) * (2 / T)) := by
  classical
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hlogx1 : (1 : ℝ) < Real.log x := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1)
          (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hcdef
  have hc1 : 1 < c := by
    have h : (0 : ℝ) < 1 / Real.log x := by positivity
    rw [hcdef]; linarith
  have hc2 : c < 2 := by
    have h : 1 / Real.log x < 1 := by rw [div_lt_one hlogxpos]; linarith
    rw [hcdef]; linarith
  have hcpos : (0 : ℝ) < c := by linarith
  have hc_sub : c - 1 = 1 / Real.log x := by rw [hcdef]; ring
  have hσ₀gt : (9 : ℝ) / 10 < σ₀ := by linarith
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  have hσ₀c : σ₀ < c := lt_trans hσ₀1 hc1
  have hTpos : (0 : ℝ) < T := by linarith
  have hB₀nn : (0 : ℝ) ≤ B₀ := by
    have hpt_re : ((σ₀ : ℂ) + (T : ℂ) * I).re = σ₀ := by simp
    have hpt_im : ((σ₀ : ℂ) + (T : ℂ) * I).im = T := by simp
    have := hedge ((σ₀ : ℂ) + (T : ℂ) * I) hpt_re.ge (by rw [hpt_re]; linarith)
      (by rw [hpt_im]; exact le_of_eq (abs_of_pos hTpos)) (Or.inl hpt_re)
    linarith [norm_nonneg (logDeriv (LFunction (1 : DirichletCharacter ℂ q))
      ((σ₀ : ℂ) + (T : ℂ) * I))]
  -- Wf := the entire de-poled trivial L-function; Gtrue = −logDeriv Wf
  set Wf : ℂ → ℂ := LFunctionTrivChar₁ q with hWfdef
  have hWf_diff : Differentiable ℂ Wf := by rw [hWfdef]; exact differentiable_LFunctionTrivChar₁ q
  have hWf1 : Wf 1 ≠ 0 := by rw [hWfdef]; exact LFunctionTrivChar₁_apply_one_ne_zero q
  have hWf_eq : ∀ s : ℂ, s ≠ 1 → Wf s = (s - 1) * LFunction (1 : DirichletCharacter ℂ q) s := by
    intro s hs; rw [hWfdef, LFunctionTrivChar₁, Function.update_of_ne hs]
  -- the box non-vanishing of Wf (reduces to `hzfζ`)
  have hWne_box : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ c → |s.im| ≤ T → Wf s ≠ 0 := by
    intro s hsl hsu hsi
    by_cases hs1 : s = 1
    · rw [hs1]; exact hWf1
    · rw [hWf_eq s hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      by_cases h1 : 1 ≤ s.re
      · exact LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) h1
      · intro h0
        have hspos : (0 : ℝ) < s.re := by linarith
        have hζ : riemannZeta s = 0 := by
          have hmul := LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
          rw [show LFunctionTrivChar q s = LFunction (1 : DirichletCharacter ℂ q) s from rfl,
            h0] at hmul
          have hP : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
            apply Finset.prod_ne_zero_iff.mpr
            intro p hp
            have h := eulerFactor_ne_zero (1 : DirichletCharacter ℂ 1)
              (Nat.prime_of_mem_primeFactors hp) hspos
            rwa [eulerFactor_one_eq p] at h
          exact (mul_eq_zero.mp hmul.symm).resolve_left hP
        exact hzfζ s hζ (by linarith) (not_le.mp h1).le (by linarith)
  -- the log-derivative split identity: logDeriv L(χ₀) = logDeriv Wf − 1/(s−1)  (s≠1, Wf s ≠ 0)
  have hlogL_split : ∀ s : ℂ, s ≠ 1 → Wf s ≠ 0 →
      logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s = logDeriv Wf s - 1 / (s - 1) := by
    intro s hs hWs
    have hs1 : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hloc : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s] (fun z => Wf z / (z - 1)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
      have hz1 : z ≠ 1 := by simpa using hz
      rw [hWf_eq z hz1]; field_simp
    have hlogeq : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
        = logDeriv (fun z => Wf z / (z - 1)) s := by
      rw [logDeriv_apply, logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]
    rw [hlogeq]
    have hd1 : DifferentiableAt ℂ Wf s := hWf_diff s
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
    rw [logDeriv_div s hWs hs1 hd1 hd2]
    congr 1
    rw [logDeriv_apply, deriv_sub_const]; simp
  -- differentiability infrastructure
  have hWf_deriv_diff : Differentiable ℂ (deriv Wf) :=
    differentiableOn_univ.mp
      (hWf_diff.differentiableOn.analyticOnNhd isOpen_univ).deriv.differentiableOn
  have hGt_diff : ∀ s : ℂ, Wf s ≠ 0 → DifferentiableAt ℂ (fun z => -logDeriv Wf z) s := by
    intro s hs
    have hrw : (fun z => -logDeriv Wf z) = fun z => -(deriv Wf z / Wf z) := by
      funext z; rw [logDeriv_apply]
    rw [hrw]; exact (((hWf_deriv_diff s).div (hWf_diff s) hs)).neg
  have hkerAt : ∀ s : ℂ, s ≠ 0 → s + 1 ≠ 0 →
      DifferentiableAt ℂ (fun z => (x : ℂ) ^ (z + 1) / (z * (z + 1))) s := by
    intro s hs0 hs1
    apply DifferentiableAt.div
    · exact (differentiableAt_id.add_const 1).const_cpow (Or.inl hxC)
    · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
    · exact mul_ne_zero hs0 hs1
  -- ℂ∖{1} continuity of L(χ₀) and its derivative (for edge integrability)
  have hLana_ne1 : AnalyticOnNhd ℂ (LFunction (1 : DirichletCharacter ℂ q)) {s : ℂ | s ≠ 1} := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ne
    intro s hs
    exact (differentiableAt_LFunction _ s (Or.inl hs)).differentiableWithinAt
  have hLcont_ne1 : ContinuousOn (LFunction (1 : DirichletCharacter ℂ q)) {s : ℂ | s ≠ 1} :=
    hLana_ne1.continuousOn
  have hdLcont_ne1 :
      ContinuousOn (deriv (LFunction (1 : DirichletCharacter ℂ q))) {s : ℂ | s ≠ 1} :=
    hLana_ne1.deriv.continuousOn
  -- the integrands
  set F : ℂ → ℂ :=
    fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))
      * (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s) with hF
  set A : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) * (-logDeriv Wf s) with hA
  set Bfun : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1)) / (s - (1 : ℂ)) with hBfun
  set κ : ℂ := (x : ℂ) ^ ((1 : ℂ) + 1) / ((1 : ℂ) * ((1 : ℂ) + 1)) with hκ
  have hκ_eq : κ = (x : ℂ) ^ 2 / 2 := by
    rw [hκ, show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; norm_num
  have hFnorm : ∀ s : ℂ, ‖F s‖
      = x ^ (s.re + 1) * ‖(s * (s + 1))⁻¹‖
        * ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s‖ := by
    intro s
    simp only [hF]
    rw [norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re,
      Complex.one_re, div_eq_mul_inv, ← norm_inv]
  -- pointwise splitting F = A + Bfun off 1 (needs Wf s ≠ 0)
  have hAFB : ∀ s : ℂ, s ≠ 1 → Wf s ≠ 0 → F s = A s + Bfun s := by
    intro s hs hWs
    have hsplit := hlogL_split s hs hWs
    simp only [hF, hA, hBfun]
    rw [hsplit]; ring
  -- `≠ 1` facts for edge points
  have him_ne : ∀ (a τ : ℝ), τ ≠ 0 → ((a : ℂ) + (τ : ℂ) * I) ≠ (1 : ℂ) :=
    fun a τ hτ h => hτ (by simpa using congrArg Complex.im h)
  have hre_ne : ∀ (a b : ℝ), a ≠ 1 → ((a : ℂ) + (b : ℂ) * I) ≠ (1 : ℂ) :=
    fun a b ha h => ha (by simpa using congrArg Complex.re h)
  -- the rectangle
  set zc : ℂ := (σ₀ : ℂ) - (T : ℂ) * I with hzc
  set wc : ℂ := (c : ℂ) + (T : ℂ) * I with hwc
  have hzc_re : zc.re = σ₀ := by rw [hzc]; simp
  have hzc_im : zc.im = -T := by rw [hzc]; simp
  have hwc_re : wc.re = c := by rw [hwc]; simp
  have hwc_im : wc.im = T := by rw [hwc]; simp
  -- A is differentiable on the whole box (Gtrue analytic since Wf ≠ 0 on box)
  have hA_diff : DifferentiableOn ℂ A (closedRect zc wc) := by
    intro s hs
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm] at hs
    rw [Set.uIcc_of_le hσ₀c.le] at hs
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hsre, hsim⟩ := hs
    simp only [Set.mem_Icc] at hsre hsim
    have hsim' : |s.im| ≤ T := by rw [abs_le]; exact ⟨hsim.1, hsim.2⟩
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hsre; linarith [hsre.1, hσ₀pos]
    have hs1 : s + 1 ≠ 0 := by
      intro h; have : (s + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hsre.1, hσ₀pos]
    have hWs : Wf s ≠ 0 := hWne_box s hsre.1 hsre.2 hsim'
    have hAs : DifferentiableAt ℂ A s := by
      rw [hA]; exact (hkerAt s hs0 hs1).mul (hGt_diff s hWs)
    exact hAs.differentiableWithinAt
  have hA0 : rectBI zc wc A = 0 := rectBI_eq_zero_of_differentiableOn hA_diff
  -- the residue via kernel_residue at 1
  have hBres : rectBI zc wc Bfun = 2 * ↑Real.pi * I * κ := by
    have hres := kernel_residue (z := zc) (w := wc) (x := x) hxpos (β := (1 : ℂ))
      (by rw [hzc_re]; exact hσ₀pos)
      (by rw [hzc_re, hwc_re]; exact hσ₀c)
      (by rw [hzc_im, hwc_im]; linarith)
      ⟨show zc.re < (1 : ℂ).re by rw [hzc_re, Complex.one_re]; exact hσ₀1,
        show (1 : ℂ).re < wc.re by rw [hwc_re, Complex.one_re]; exact hc1⟩
      ⟨show zc.im < (1 : ℂ).im by rw [hzc_im, Complex.one_im]; linarith,
        show (1 : ℂ).im < wc.im by rw [hwc_im, Complex.one_im]; linarith⟩
    rw [hBfun, hκ]; exact hres
  -- edge integrability and the F = A + Bfun edge identities
  have hedge_int : ∀ (γ : ℝ → ℂ) (a b : ℝ), Continuous γ →
      Set.MapsTo γ (Set.uIcc a b) (closedRect zc wc) →
      (∀ t ∈ Set.uIcc a b, γ t ≠ (1 : ℂ)) →
      IntervalIntegrable (fun t => A (γ t)) volume a b ∧
        IntervalIntegrable (fun t => Bfun (γ t)) volume a b := by
    intro γ a b hγ hmaps hne
    refine ⟨(hA_diff.continuousOn.comp hγ.continuousOn hmaps).intervalIntegrable, ?_⟩
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hmem := hmaps ht
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm, Set.uIcc_of_le hσ₀c.le,
        Set.uIcc_of_le (by linarith : -T ≤ T)] at hmem
    obtain ⟨hre, _⟩ := hmem
    simp only [Set.mem_Icc] at hre
    have h0 : γ t ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre; linarith [hre.1, hσ₀pos]
    have h1 : γ t + 1 ≠ 0 := by
      intro h; have : (γ t + 1).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.one_re] at this; linarith [hre.1, hσ₀pos]
    have hβ : γ t ≠ (1 : ℂ) := hne t ht
    have hBd : DifferentiableAt ℂ Bfun (γ t) := by
      rw [hBfun]
      exact (hkerAt (γ t) h0 h1).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hβ)
    exact ((hBd.continuousAt).comp hγ.continuousAt).continuousWithinAt
  -- the four MapsTo
  have hmaps_bot : Set.MapsTo (fun x : ℝ => (↑x + ↑zc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu; rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑zc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑zc.im * I : ℂ).im = zc.im by simp]; exact left_mem_uIcc
  have hmaps_top : Set.MapsTo (fun x : ℝ => (↑x + ↑wc.im * I : ℂ)) (Set.uIcc zc.re wc.re)
      (closedRect zc wc) := by
    intro u hu; rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑u + ↑wc.im * I : ℂ).re = u by simp]; exact hu
    · rw [show (↑u + ↑wc.im * I : ℂ).im = wc.im by simp]; exact right_mem_uIcc
  have hmaps_rgt : Set.MapsTo (fun y : ℝ => (↑wc.re + ↑y * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv; rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑wc.re + ↑v * I : ℂ).re = wc.re by simp]; exact right_mem_uIcc
    · rw [show (↑wc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hmaps_lft : Set.MapsTo (fun y : ℝ => (↑zc.re + ↑y * I : ℂ)) (Set.uIcc zc.im wc.im)
      (closedRect zc wc) := by
    intro v hv; rw [closedRect, mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [show (↑zc.re + ↑v * I : ℂ).re = zc.re by simp]; exact left_mem_uIcc
    · rw [show (↑zc.re + ↑v * I : ℂ).im = v by simp]; exact hv
  have hne_bot : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑zc.im * I : ℂ) ≠ (1 : ℂ) :=
    fun t _ => him_ne t zc.im (by rw [hzc_im]; linarith)
  have hne_top : ∀ t ∈ Set.uIcc zc.re wc.re, (↑t + ↑wc.im * I : ℂ) ≠ (1 : ℂ) :=
    fun t _ => him_ne t wc.im (by rw [hwc_im]; linarith)
  have hne_rgt : ∀ t ∈ Set.uIcc zc.im wc.im, (↑wc.re + ↑t * I : ℂ) ≠ (1 : ℂ) :=
    fun t _ => hre_ne wc.re t (by rw [hwc_re]; linarith)
  have hne_lft : ∀ t ∈ Set.uIcc zc.im wc.im, (↑zc.re + ↑t * I : ℂ) ≠ (1 : ℂ) :=
    fun t _ => hre_ne zc.re t (by rw [hzc_re]; linarith)
  -- the F = A + Bfun edge identities need Wf ≠ 0 at the edge points (box membership)
  have hWne_edge : ∀ s : ℂ, s ∈ closedRect zc wc → s ≠ (1 : ℂ) → Wf s ≠ 0 := by
    intro s hs _
    rw [closedRect, hzc_re, hzc_im, hwc_re, hwc_im, mem_reProdIm, Set.uIcc_of_le hσ₀c.le,
        Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    obtain ⟨hre, him⟩ := hs
    simp only [Set.mem_Icc] at hre him
    exact hWne_box s hre.1 hre.2 (by rw [abs_le]; exact ⟨him.1, him.2⟩)
  have hAFB_bot : ∀ t ∈ Set.uIcc zc.re wc.re,
      F (↑t + ↑zc.im * I) = A (↑t + ↑zc.im * I) + Bfun (↑t + ↑zc.im * I) := fun t ht =>
    hAFB _ (hne_bot t ht) (hWne_edge _ (hmaps_bot ht) (hne_bot t ht))
  have hAFB_top : ∀ t ∈ Set.uIcc zc.re wc.re,
      F (↑t + ↑wc.im * I) = A (↑t + ↑wc.im * I) + Bfun (↑t + ↑wc.im * I) := fun t ht =>
    hAFB _ (hne_top t ht) (hWne_edge _ (hmaps_top ht) (hne_top t ht))
  have hAFB_rgt : ∀ t ∈ Set.uIcc zc.im wc.im,
      F (↑wc.re + ↑t * I) = A (↑wc.re + ↑t * I) + Bfun (↑wc.re + ↑t * I) := fun t ht =>
    hAFB _ (hne_rgt t ht) (hWne_edge _ (hmaps_rgt ht) (hne_rgt t ht))
  have hAFB_lft : ∀ t ∈ Set.uIcc zc.im wc.im,
      F (↑zc.re + ↑t * I) = A (↑zc.re + ↑t * I) + Bfun (↑zc.re + ↑t * I) := fun t ht =>
    hAFB _ (hne_lft t ht) (hWne_edge _ (hmaps_lft ht) (hne_lft t ht))
  obtain ⟨hA_bot, hB_bot⟩ := hedge_int _ zc.re wc.re (by fun_prop) hmaps_bot hne_bot
  obtain ⟨hA_top, hB_top⟩ := hedge_int _ zc.re wc.re (by fun_prop) hmaps_top hne_top
  obtain ⟨hA_rgt, hB_rgt⟩ := hedge_int _ zc.im wc.im (by fun_prop) hmaps_rgt hne_rgt
  obtain ⟨hA_lft, hB_lft⟩ := hedge_int _ zc.im wc.im (by fun_prop) hmaps_lft hne_lft
  have hlin : rectBI zc wc F = rectBI zc wc A + rectBI zc wc Bfun :=
    rectBI_add_of_edge_eq hA_bot hA_top hA_rgt hA_lft hB_bot hB_top hB_rgt hB_lft
      hAFB_bot hAFB_top hAFB_rgt hAFB_lft
  have hrectF : rectBI zc wc F = (2 * ↑Real.pi * I) * κ := by
    rw [hlin, hA0, hBres]; ring
  rw [rectBI, hzc_re, hzc_im, hwc_re, hwc_im] at hrectF
  set RIGHT : ℂ := ∫ v in (-T)..T, F ((c : ℂ) + v * I) with hRIGHT
  set TOPI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I) with hTOPI
  set BOTI : ℂ := ∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hBOTI
  set LEFT : ℂ := ∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I) with hLEFT
  have hgour2 : I * (RIGHT - (2 * ↑Real.pi : ℂ) * κ) = TOPI - BOTI + I * LEFT := by
    linear_combination hrectF
  have hRnorm : ‖RIGHT - (2 * ↑Real.pi : ℂ) * κ‖ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
    have heq : ‖RIGHT - (2 * ↑Real.pi : ℂ) * κ‖ = ‖TOPI - BOTI + I * LEFT‖ := by
      rw [← hgour2, norm_mul, Complex.norm_I, one_mul]
    rw [heq]
    calc ‖TOPI - BOTI + I * LEFT‖
        ≤ ‖TOPI - BOTI‖ + ‖I * LEFT‖ := norm_add_le _ _
      _ ≤ ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_sub_le TOPI BOTI]
  -- the c-line integrability and the Perron bridge
  have hFint : Integrable (fun v : ℝ => F ((c : ℂ) + v * I)) := by
    simp only [hF]; exact contour_integrand_integrable_trivChar q hx1 hc1 hc2.le
  have hbridge : psi1Chi x (1 : DirichletCharacter ℂ q)
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, F ((c : ℂ) + v * I) := by
    rw [psi1_eq_contour_integral (1 : DirichletCharacter ℂ q) hx1 hc1]
  have htrunc : (∫ v : ℝ, F ((c : ℂ) + v * I))
      = RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I) := by
    rw [hRIGHT, intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T),
      integral_add_compl measurableSet_Ioc hFint]
  -- the horizontal / left / tail edge bounds
  set Cbnd : ℝ := x ^ (c + 1) * B₀ / T ^ 2 with hCbnd
  have hxc1pos : (0 : ℝ) < x ^ (c + 1) := by positivity
  have hCbnd_nn : (0 : ℝ) ≤ Cbnd := by rw [hCbnd]; positivity
  have hhoriz : ∀ (τ : ℝ), |τ| = T → ∀ u ∈ Set.uIoc σ₀ c, ‖F ((u : ℂ) + (τ : ℂ) * I)‖ ≤ Cbnd := by
    intro τ hτ u hu
    rw [Set.uIoc_of_le hσ₀c.le, Set.mem_Ioc] at hu
    have hsre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hsim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hupos : (0 : ℝ) < u := by linarith [hu.1, hσ₀gt]
    have hlogb : ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((u : ℂ) + (τ : ℂ) * I)‖ ≤ B₀ :=
      hedge _ (by rw [hsre]; linarith [hu.1]) (by rw [hsre]; linarith [hu.2])
        (by rw [hsim]; exact le_of_eq hτ) (Or.inr (by rw [hsim]; exact hτ))
    have hden : ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖ ≤ (u ^ 2 + τ ^ 2)⁻¹ :=
      norm_inv_denom_le hupos τ
    have hττ : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    have hxexp : x ^ (u + 1) ≤ x ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hu.2])
    have hinvle : (u ^ 2 + τ ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith [sq_nonneg u])
    rw [hFnorm, hsre]
    calc x ^ (u + 1) * ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1))⁻¹‖
            * ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ x ^ (u + 1) * (u ^ 2 + τ ^ 2)⁻¹ * B₀ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
            (norm_nonneg _) (by positivity)
      _ ≤ x ^ (c + 1) * (T ^ 2)⁻¹ * B₀ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hxexp hinvle (by positivity) (by positivity)) hB₀nn
      _ = Cbnd := by rw [hCbnd]; ring
  have hTOPb : ‖TOPI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hTOPI]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + (T : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz T (abs_of_pos hTpos))
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hBOTb : ‖BOTI‖ ≤ (c - σ₀) * Cbnd := by
    rw [hBOTI]
    have hnegT : |(-T : ℝ)| = T := by rw [abs_neg, abs_of_pos hTpos]
    calc ‖∫ u in σ₀..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ Cbnd * |c - σ₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (hhoriz (-T) hnegT)
      _ = (c - σ₀) * Cbnd := by rw [abs_of_nonneg (by linarith)]; ring
  have hLEFTb : ‖LEFT‖ ≤ B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    rw [hLEFT]
    have hg_int : Integrable (fun v : ℝ => B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹) :=
      (integrable_inv_c_sq_add_sq hσ₀pos).const_mul _
    have hline_left : Continuous (fun v : ℝ => (σ₀ : ℂ) + v * I) := by fun_prop
    have hmaps_ne1 : ∀ v : ℝ, ((σ₀ : ℂ) + v * I) ∈ {s : ℂ | s ≠ 1} := fun v =>
      hre_ne σ₀ v (by linarith)
    have hL_line_cont :
        Continuous (fun v : ℝ => LFunction (1 : DirichletCharacter ℂ q) ((σ₀ : ℂ) + v * I)) :=
      hLcont_ne1.comp_continuous hline_left hmaps_ne1
    have hdL_line_cont : Continuous
        (fun v : ℝ => deriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ₀ : ℂ) + v * I)) :=
      hdLcont_ne1.comp_continuous hline_left hmaps_ne1
    have hFleft_ii : IntervalIntegrable (fun v : ℝ => F ((σ₀ : ℂ) + v * I)) volume (-T) T := by
      simp only [hF]
      apply ContinuousOn.intervalIntegrable
      have hLne : ∀ v ∈ Set.uIcc (-T) T,
          LFunction (1 : DirichletCharacter ℂ q) ((σ₀ : ℂ) + v * I) ≠ 0 := by
        intro v hv
        rw [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] at hv
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
        have hWs := hWne_box _ hsre.ge (by rw [hsre]; linarith)
          (by rw [hsim, abs_le]; exact ⟨hv.1, hv.2⟩)
        intro h0; apply hWs
        rw [hWf_eq _ (hre_ne σ₀ v (by linarith)), h0, mul_zero]
      have hden : ∀ v ∈ Set.uIcc (-T) T,
          ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1) ≠ 0 := by
        intro v _
        have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
        refine mul_ne_zero ?_ ?_
        · intro h; rw [h, Complex.zero_re] at hsre; linarith [hσ₀pos]
        · intro h; have : (((σ₀ : ℂ) + v * I) + 1).re = 0 := by rw [h]; simp
          rw [Complex.add_re, Complex.one_re, hsre] at this; linarith [hσ₀pos]
      apply ContinuousOn.mul
      · apply ContinuousOn.div
        · exact ((by fun_prop : Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) + 1).const_cpow
            (Or.inl hxC)).continuousOn
        · exact (by fun_prop :
            Continuous fun v : ℝ => ((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1)).continuousOn
        · exact hden
      · have hrw : (fun v : ℝ =>
            -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ₀ : ℂ) + v * I))
            = fun v : ℝ =>
              -(deriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ₀ : ℂ) + v * I)
                / LFunction (1 : DirichletCharacter ℂ q) ((σ₀ : ℂ) + v * I)) := by
          funext v; rw [logDeriv_apply]
        rw [hrw]
        exact ((hdL_line_cont.continuousOn.div hL_line_cont.continuousOn hLne)).neg
    have hgnn : ∀ v : ℝ, (0 : ℝ) ≤ B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
      fun v => mul_nonneg (mul_nonneg hB₀nn (by positivity)) (by positivity)
    have hpt : ∀ v ∈ Set.Icc (-T) T,
        ‖F ((σ₀ : ℂ) + v * I)‖ ≤ B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
      intro v hv
      simp only [Set.mem_Icc] at hv
      have hvT : |v| ≤ T := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
      have hsre : ((σ₀ : ℂ) + v * I).re = σ₀ := by simp
      have hsim : ((σ₀ : ℂ) + v * I).im = v := by simp
      have hlogb : ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ₀ : ℂ) + v * I)‖ ≤ B₀ :=
        hedge _ hsre.ge (by rw [hsre]; linarith) (by rw [hsim]; exact hvT) (Or.inl hsre)
      have hden : ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖ ≤ (σ₀ ^ 2 + v ^ 2)⁻¹ :=
        norm_inv_denom_le hσ₀pos v
      rw [hFnorm, hsre]
      calc x ^ (σ₀ + 1) * ‖(((σ₀ : ℂ) + v * I) * (((σ₀ : ℂ) + v * I) + 1))⁻¹‖
              * ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ₀ : ℂ) + v * I)‖
          ≤ x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ * B₀ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
              (norm_nonneg _) (by positivity)
        _ = B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by ring
    calc ‖∫ v in (-T)..T, F ((σ₀ : ℂ) + v * I)‖
        ≤ ∫ v in (-T)..T, ‖F ((σ₀ : ℂ) + v * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ v in (-T)..T, B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ :=
          intervalIntegral.integral_mono_on (by linarith)
            hFleft_ii.norm hg_int.intervalIntegrable hpt
      _ ≤ ∫ v : ℝ, B₀ * x ^ (σ₀ + 1) * (σ₀ ^ 2 + v ^ 2)⁻¹ := by
          rw [intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
          exact setIntegral_le_integral hg_int (Filter.Eventually.of_forall hgnn)
      _ = B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [integral_const_mul, integral_inv_sq_add hσ₀pos]
  have hcompl_meas : MeasurableSet (Set.Ioc (-T) T)ᶜ := measurableSet_Ioc.compl
  have hTAILb : ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
    have hFint_on : IntegrableOn (fun v : ℝ => F ((c : ℂ) + v * I)) (Set.Ioc (-T) T)ᶜ :=
      hFint.integrableOn
    have hg_int : IntegrableOn
        (fun v : ℝ => (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹) (Set.Ioc (-T) T)ᶜ :=
      ((integrable_inv_c_sq_add_sq hcpos).const_mul _).integrableOn
    calc ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
        ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, ‖F ((c : ℂ) + v * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in (Set.Ioc (-T) T)ᶜ, (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by
          refine setIntegral_mono_on hFint_on.norm hg_int hcompl_meas ?_
          intro v _
          have hsre : ((c : ℂ) + v * I).re = c := by simp
          have hLs : LFunction (1 : DirichletCharacter ℂ q) ((c : ℂ) + v * I) ≠ 0 :=
            LFunction_ne_zero_of_one_le_re _ (Or.inr (hre_ne c v (by linarith)))
              (by rw [hsre]; linarith)
          have hlogb : ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((c : ℂ) + v * I)‖
              ≤ Real.log x + 1 := by
            have hle := norm_logDeriv_le_of_re (1 : DirichletCharacter ℂ q) (s := (c : ℂ) + v * I)
              (by rw [hsre]; exact hc1) (by rw [hsre]; linarith)
            rw [hsre, hc_sub, one_div_one_div] at hle
            exact hle
          have hden : ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖ ≤ (c ^ 2 + v ^ 2)⁻¹ :=
            norm_inv_denom_le hcpos v
          rw [hFnorm, hsre]
          calc x ^ (c + 1) * ‖(((c : ℂ) + v * I) * (((c : ℂ) + v * I) + 1))⁻¹‖
                  * ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((c : ℂ) + v * I)‖
              ≤ x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ * (Real.log x + 1) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hden (by positivity)) hlogb
                  (norm_nonneg _) (by positivity)
            _ = (Real.log x + 1) * x ^ (c + 1) * (c ^ 2 + v ^ 2)⁻¹ := by ring
      _ = (Real.log x + 1) * x ^ (c + 1) * ∫ v in (Set.Ioc (-T) T)ᶜ, (c ^ 2 + v ^ 2)⁻¹ := by
          rw [integral_const_mul]
      _ ≤ (Real.log x + 1) * x ^ (c + 1) * (2 / T) :=
          mul_le_mul_of_nonneg_left (tail_lorentzian_le hcpos hTpos) (by positivity)
  have hcombine : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
      ≤ 2 * (c - σ₀) * B₀ * x ^ (c + 1) / T ^ 2 + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
    have hstep : ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
      linarith [hTOPb, hBOTb, hLEFTb]
    calc ‖TOPI‖ + ‖BOTI‖ + ‖LEFT‖
        ≤ (c - σ₀) * Cbnd + (c - σ₀) * Cbnd + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := hstep
      _ = 2 * (c - σ₀) * B₀ * x ^ (c + 1) / T ^ 2 + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
          rw [hCbnd]; ring
  -- final assembly (κ = x²/2 subtracted)
  have hπℂ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkappa : (1 / (2 * Real.pi) : ℝ) • ((2 * ↑Real.pi : ℂ) * κ) = κ := by
    rw [Complex.real_smul]; push_cast; field_simp
  have hcollect : psi1Chi x (1 : DirichletCharacter ℂ q) - κ
      = (1 / (2 * Real.pi)) • ((RIGHT - (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)) := by
    have e1 : (1 / (2 * Real.pi) : ℝ) • ((RIGHT - (2 * ↑Real.pi : ℂ) * κ)
          + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
        = (1 / (2 * Real.pi)) • (RIGHT + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I))
          - (1 / (2 * Real.pi)) • ((2 * ↑Real.pi : ℂ) * κ) := by
      simp only [Complex.real_smul]; ring
    rw [e1, hkappa, ← htrunc, ← hbridge]
  rw [← hκ_eq, hcollect, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖(RIGHT - (2 * ↑Real.pi : ℂ) * κ) + ∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖
      ≤ ‖RIGHT - (2 * ↑Real.pi : ℂ) * κ‖
          + ‖∫ v in (Set.Ioc (-T) T)ᶜ, F ((c : ℂ) + v * I)‖ := norm_add_le _ _
    _ ≤ (2 * (c - σ₀) * B₀ * x ^ (c + 1) / T ^ 2 + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀))
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by
        have h1 : ‖RIGHT - (2 * ↑Real.pi : ℂ) * κ‖
            ≤ 2 * (c - σ₀) * B₀ * x ^ (c + 1) / T ^ 2 + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀) :=
          le_trans hRnorm hcombine
        linarith [h1, hTAILb]
    _ = 2 * (c - σ₀) * B₀ * x ^ (c + 1) / T ^ 2 + B₀ * x ^ (σ₀ + 1) * (Real.pi / σ₀)
          + (Real.log x + 1) * x ^ (c + 1) * (2 / T) := by ring

/-! ## 5. The χ₀ contour-shift bound, edge hypothesis discharged -/

set_option maxHeartbeats 800000 in
-- The discharge threads the `Zc` numeric, the Euler-correction bound and the pole term through one
-- `set`-heavy edge estimate and matches the S5b-shaped `E₀` on `apply`; it needs headroom past the
-- 200000 default.
/-- **S5d — the fully-discharged χ₀ contour-shift bound.** The `hedge` hypothesis of
`psi1_contour_shift_trivchar` is discharged from the landed `Zc` numeric
(`norm_logDeriv_Zc_le_of_ball_dist`), the Euler-correction bound
(`norm_logDeriv_eulerCorr_trivChar_le`) and the pole term `1/(s−1)`, so the edge constant is
`B₀ = 120·log(4·M₀ζ(T)) + (log(4·M₀ζ(T))/log(7/6))/w + 2·log q + 1/w`.

The pole term `1/(s−1)` requires the pole to be `w`-separated from the left edge, i.e.
`σ₀ + w ≤ 1` (`hσ₀w1`) — the exact mirror of the exceptional variant's `hβsep : σ₀ + w ≤ β₁` with
`β₁ = 1` (S6 supplies it, `1` being the pole). Only `hzfζ` (the ζ zero-free region on the box) is
now required. -/
theorem psi1_contour_shift_trivchar_full (q : ℕ) [NeZero q] {x : ℝ} (hx : 3 ≤ x) {T σ₀ w : ℝ}
    (hT : 2 ≤ T) (hw : 0 < w) (hσ₀w : 9 / 10 ≤ σ₀ - w) (hσ₀1 : σ₀ < 1) (hσ₀w1 : σ₀ + w ≤ 1)
    (hzfζ : ∀ ρ : ℂ, riemannZeta ρ = 0 → σ₀ - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 → False) :
    ‖psi1Chi x (1 : DirichletCharacter ℂ q) - (x : ℂ) ^ 2 / 2‖ ≤ (1 / (2 * Real.pi)) *
      (2 * ((1 + 1 / Real.log x) - σ₀)
          * (120 * Real.log (4 * M0zeta T)
             + Real.log (4 * M0zeta T) / Real.log (7 / 6) / w + 2 * Real.log (q : ℝ) + 1 / w)
          * x ^ ((1 + 1 / Real.log x) + 1) / T ^ 2
        + (120 * Real.log (4 * M0zeta T)
             + Real.log (4 * M0zeta T) / Real.log (7 / 6) / w + 2 * Real.log (q : ℝ) + 1 / w)
          * x ^ (σ₀ + 1) * (Real.pi / σ₀)
        + (Real.log x + 1) * x ^ ((1 + 1 / Real.log x) + 1) * (2 / T)) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hσ₀gt : (9 : ℝ) / 10 < σ₀ := by linarith
  have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
  have hwsmall : w < 1 / 10 := by linarith
  -- the Euler-correction product `P`
  set P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)) with hPdef
  refine psi1_contour_shift_trivchar q hx hT hw hσ₀w hσ₀1 hzfζ
    (B₀ := 120 * Real.log (4 * M0zeta T)
      + Real.log (4 * M0zeta T) / Real.log (7 / 6) / w + 2 * Real.log (q : ℝ) + 1 / w) ?_
  intro s hsl hsu hsi hor
  -- `s ≠ 1` and the basic `Re` facts on an edge
  have hs1 : s ≠ 1 := by
    rcases hor with hre | him
    · intro h; rw [h, Complex.one_re] at hre; linarith
    · intro h; rw [h] at him; simp only [Complex.one_im, abs_zero] at him; linarith
  have hspos : (0 : ℝ) < s.re := by linarith
  have hs90 : (9 : ℝ) / 10 ≤ s.re := by linarith
  -- `ζ s ≠ 0` and `Zc s ≠ 0`
  have hζ0 : riemannZeta s ≠ 0 := by
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1
    · intro hz; exact hzfζ s hz (by linarith) (not_le.mp h1).le (by linarith)
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) hζ0
  -- `P s ≠ 0` and differentiability
  have hP0 : P s ≠ 0 := by
    rw [hPdef]; apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have h := eulerFactor_ne_zero (1 : DirichletCharacter ℂ 1)
      (Nat.prime_of_mem_primeFactors hp) hspos
    rwa [eulerFactor_one_eq p] at h
  have hPdiff : DifferentiableAt ℂ P s := by
    rw [hPdef]
    exact DifferentiableAt.fun_finsetProd (fun p hp => by
      have h := differentiableAt_eulerFactor (1 : DirichletCharacter ℂ 1)
        (Nat.prime_of_mem_primeFactors hp) s
      rwa [eulerFactor_one_eq p] at h)
  have hζdiff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  -- the multiplicative split `logDeriv L(χ₀) = logDeriv P + logDeriv ζ`
  have hLmul : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv P s + logDeriv riemannZeta s := by
    have hEq : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s] fun z => P z * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      rw [hPdef]; exact LFunctionTrivChar_eq_mul_riemannZeta (by simpa using hz)
    have hcong : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
        = logDeriv (fun z => P z * riemannZeta z) s := by
      simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_mul s hP0 hζ0 hPdiff hζdiff]
  -- the full decomposition with the ζ pole split
  have hdecomp : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv Zc s + logDeriv P s - 1 / (s - 1) := by
    rw [hLmul, logDeriv_zeta_eq hs1 hζ0]; ring
  -- the distance bound feeding the `Zc` numeric
  have hdist : ∀ ρ : ℂ, Zc ρ = 0 → ρ ∈ Metric.ball (2 + (s.im : ℂ) * I) (3 / 2) → w ≤ ‖s - ρ‖ := by
    intro ρ hρ0 hρball
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Zc_one] at hρ0; exact one_ne_zero hρ0
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hρ0
      exact (mul_eq_zero.mp hρ0).resolve_left (sub_ne_zero.mpr hρ1)
    have hρre1 : ρ.re < 1 := by
      by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hζρ
    have hρim : |ρ.im| ≤ T + 2 := by
      have himdist : |ρ.im - s.im| ≤ 3 / 2 := by
        have h := Complex.abs_im_le_norm (ρ - (2 + (s.im : ℂ) * I))
        have hival : (ρ - (2 + (s.im : ℂ) * I)).im = ρ.im - s.im := by simp
        rw [hival] at h
        have hb : ‖ρ - (2 + (s.im : ℂ) * I)‖ < 3 / 2 := by rw [← dist_eq_norm]; exact hρball
        linarith
      have hh1 := abs_le.mp himdist
      have hh2 := abs_le.mp hsi
      rw [abs_le]; constructor <;> linarith
    have hρre2 : ρ.re ≤ σ₀ - w := by
      by_contra hc
      exact hzfζ ρ hζρ (le_of_lt (not_le.mp hc)) hρre1.le hρim
    have hre := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at hre
    calc w ≤ s.re - ρ.re := by linarith
      _ = |s.re - ρ.re| := (abs_of_nonneg (by linarith)).symm
      _ ≤ ‖s - ρ‖ := hre
  -- the three edge estimates
  have hZcbound : ‖logDeriv Zc s‖
      ≤ 120 * Real.log (4 * M0zeta T) + Real.log (4 * M0zeta T) / Real.log (7 / 6) / w :=
    norm_logDeriv_Zc_le_of_ball_dist hw hs90 hsu hsi hZcs hdist
  have hPbound : ‖logDeriv P s‖ ≤ 2 * Real.log (q : ℝ) := by
    rw [hPdef]; exact norm_logDeriv_eulerCorr_trivChar_le q hs90
  have hs1norm : w ≤ ‖s - 1‖ := by
    rcases hor with hre | him
    · have h := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re, hre] at h
      rw [show |σ₀ - 1| = 1 - σ₀ from by rw [abs_of_nonpos (by linarith)]; ring] at h
      linarith
    · have h := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero, him] at h
      linarith
  have hpolebound : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / w := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hw hs1norm
  -- assemble
  calc ‖logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s‖
      = ‖logDeriv Zc s + logDeriv P s - 1 / (s - 1)‖ := by rw [hdecomp]
    _ ≤ ‖logDeriv Zc s‖ + ‖logDeriv P s‖ + ‖(1 : ℂ) / (s - 1)‖ := by
        calc ‖logDeriv Zc s + logDeriv P s - 1 / (s - 1)‖
            ≤ ‖logDeriv Zc s + logDeriv P s‖ + ‖(1 : ℂ) / (s - 1)‖ := norm_sub_le _ _
          _ ≤ ‖logDeriv Zc s‖ + ‖logDeriv P s‖ + ‖(1 : ℂ) / (s - 1)‖ := by
              linarith [norm_add_le (logDeriv Zc s) (logDeriv P s)]
    _ ≤ 120 * Real.log (4 * M0zeta T) + Real.log (4 * M0zeta T) / Real.log (7 / 6) / w
          + 2 * Real.log (q : ℝ) + 1 / w := by linarith [hZcbound, hPbound, hpolebound]

end Salt.SW
