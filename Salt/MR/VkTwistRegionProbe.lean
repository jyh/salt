/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.PowRegion
import Salt.SW.ZeroFreeReal

/-!
# THE B-PROBE (P-0′) — the growth→region bridge for `L(s,χ)` at VK width

The KMT port's one D-risk (KR-1): ζ's VK-width region
(`Salt.Vk.zeta_zero_free_region_pow_of_growth`, width `c/((log t)^{3/4}(log log t)³)`) is built on
the near-1-line Borel–Carathéodory disc assembly `Salt.Vk.zeta_zero_free_of_disc`.  Does that
assembly run for `L(·,χ)`?  This file answers YES for `χ² ≠ 1`, **conditionally on a strip-growth
hypothesis** (stone A's output, taken here as a named hypothesis — the probe tests the BRIDGE,
not the growth).

## What is actually different from ζ (the three findings)

1. **The pole is not load-bearing in the lower-bound leg.**  ζ's version normalizes
`Zc = (s−1)ζ` (`Salt.SW.Zc`) — not to exploit the pole but to make the base function ENTIRE for
`Salt.Vk.entire_norm_logDeriv_sub_sum_scaled`, at the price of the correction term
`Re(1/(s−1))` in every leg.  `L(·,χ)` for `χ ≠ 1` is already entire
(`differentiable_LFunction`), so the `Zc` apparatus and the correction terms **disappear**.  The
disc's reference-point lower bound is the twisted Möbius series, not the pole:
`‖L(σ+it,χ)⁻¹‖ ≤ 1 + 1/(σ−1)` (`norm_LFunction_inv_cline_le`, the exact mirror of the landed
`Salt.SW.norm_zeta_inv_cline_le`).  ζ's pole survives where it is genuinely needed — in the
**first** 3-4-1 factor `ζ(σ)³` at real `σ`, which is character-free
(`Salt.SW.neg_logDeriv_LFunction_trivChar_le`).

2. **The width law is `Θ/log(M/Θ)`, not `1/log M`.**  `LFunction_zero_free_width_law` isolates it:
from a uniform growth `‖L‖ ≤ M` on the strip of half-width `Θ` the region is
`Re ρ ≤ 1 − Θ/(14·(8Θ + 700·log(20M/Θ)))`.  The VK `3/4` exponent therefore comes from the
GROWTH's `Θ`, and `M` enters only logarithmically — which is what makes the `q`-debit benign
(KR-2, see `LFunction_zero_free_region_vk_shape`).

3. **One hypothesis fewer.**  ζ's assembly needs `1 ≤ |Im ρ|` to bound the two pole correction
terms; the `χ² ≠ 1` assembly needs no height hypothesis at all beyond the growth box.

## The gap list to stone B proper

* the `χ² = 1` arm (the third carrier degenerates to `ζ·∏_{p∣q}(1−p^{−s})`; the conjugate-zero
  trick of `Salt.SW.zero_free_region_real` §1 transports, plus the finite-Euler debit `log q`);
* the honest height floor (here: whatever the growth hypothesis carries — `e^{e^100}`-genre at
  `Salt.MR.vkTwistUB_holds`);
* the carve-out/Siegel fold and the constant stack.
-/

noncomputable section

namespace Salt.MR

open Complex Metric Set DirichletCharacter
open Salt.SW Salt.Vk
open scoped LSeries.notation Topology

/-! ## 1. The reference-point lower bound (the leg ζ takes from its pole's neighbourhood) -/

/-- **The `c`-line inverse bound for `L(·,χ)`** — the exact mirror of `norm_zeta_inv_cline_le`.
For `σ > 1`, `‖L(σ+it,χ)⁻¹‖ ≤ 1 + 1/(σ−1)`, via the twisted Möbius series
`L(χ)⁻¹ = ∑ μ(n)χ(n)n^{−s}` (mathlib `DirichletCharacter.LSeries.mul_mu_eq_one`) majorized
termwise by `∑ n^{−σ} ≤ 1 + 1/(σ−1)` (`tsum_rpow_neg_le`).

This is the leg the freeze feared was pole-anchored.  It is not: no pole, no Euler product, no
Mertens — only `|χ(n)μ(n)| ≤ 1` and absolute convergence. -/
lemma norm_LFunction_inv_cline_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖(LFunction χ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 1 + 1 / (σ - 1) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hre : s.re = σ := by rw [hsdef]; simp
  have hs : 1 < s.re := by rw [hre]; exact hσ
  have hLS : LFunction χ s = LSeries ↗χ s := LFunction_eq_LSeries χ hs
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne : LSeries ↗χ s ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact zero_ne_one hmul
  have hinv : (LSeries ↗χ s)⁻¹ = LSeries (↗χ * ↗ArithmeticFunction.moebius) s :=
    inv_eq_of_mul_eq_one_right hmul
  rw [hLS, hinv]
  -- the majorant
  have hsummable : Summable
      (fun n : ℕ => ‖LSeries.term (↗χ * ↗ArithmeticFunction.moebius) s n‖) :=
    summable_norm_iff.mpr (DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs))
  have hcomp : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (↗χ * ↗ArithmeticFunction.moebius) s n‖ ≤ (n : ℝ) ^ (-σ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.norm_term_eq, if_pos rfl]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    · rw [LSeries.norm_term_eq, if_neg hn, hre, Real.rpow_neg (Nat.cast_nonneg n)]
      have hcm : ‖(↗χ * ↗ArithmeticFunction.moebius : ℕ → ℂ) n‖ ≤ 1 := by
        have hsplit : (↗χ * ↗ArithmeticFunction.moebius : ℕ → ℂ) n
            = (χ (n : ZMod q)) * ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
          simp [Pi.mul_apply]
        rw [hsplit, norm_mul]
        have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
        have h2 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          rw [show (((ArithmeticFunction.moebius n : ℤ) : ℂ))
              = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [norm_nonneg (χ (n : ZMod q)),
          norm_nonneg (((ArithmeticFunction.moebius n : ℤ) : ℂ))]
      have hpow : (0 : ℝ) < (n : ℝ) ^ σ :=
        Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
      rw [div_le_iff₀ hpow, inv_mul_cancel₀ hpow.ne']
      exact hcm
  calc ‖LSeries (↗χ * ↗ArithmeticFunction.moebius) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗ArithmeticFunction.moebius) s n‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := hsummable.tsum_le_tsum hterm hcomp
    _ ≤ 1 + 1 / (σ - 1) := tsum_rpow_neg_le hσ

/-- **The growth-to-sphere adapter for `L(·,χ)`** (mirror of `Salt.Vk.Zc_ratio_sphere_bound`,
with the `‖s−1‖` bookkeeping GONE — `L` is entire, so there is no `(s−1)` factor to cancel).
A pointwise growth bound `‖L(z,χ)‖ ≤ M` yields the normalized bound `‖L z/L c‖ ≤ 5M/Θ` at the
near-1-line center `c = (1+Θ/2)+iτ`, from the reference floor
`‖L(c,χ)‖ ≥ 1/(1+2/Θ) = Θ/(Θ+2)` (`norm_LFunction_inv_cline_le`).

The constant `5` (rather than the sharp `Θ+2 ≤ 5/2`) is chosen to match ζ's `Zc_ratio_sphere_bound`
verbatim, so that the downstream width algebra of `Salt.Vk.zeta_zero_free_pow_core` transports
without a single numeral change. -/
lemma LFunction_ratio_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Θ τ M : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hM : 1 ≤ M) {z : ℂ}
    (hLz : ‖LFunction χ z‖ ≤ M) :
    ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 5 * M / Θ := by
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hcne1 : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; nlinarith [hΘ0]
  have hLc : LFunction χ c ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr hcne1) (by rw [hcre]; nlinarith [hΘ0])
  have hLcpos : 0 < ‖LFunction χ c‖ := norm_pos_iff.mpr hLc
  -- the reference floor `(Θ+2)·‖L c‖ ≥ Θ`
  have hfloor : Θ ≤ (Θ + 2) * ‖LFunction χ c‖ := by
    have hinv := norm_LFunction_inv_cline_le χ (σ := 1 + Θ / 2) (by linarith [hΘ0]) τ
    rw [show ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I = c from rfl, norm_inv,
      show (1 + Θ / 2 : ℝ) - 1 = Θ / 2 from by ring] at hinv
    have h1 : ‖LFunction χ c‖⁻¹ * Θ ≤ Θ + 2 := by
      have hm := mul_le_mul_of_nonneg_right hinv hΘ0.le
      have he : (1 + 1 / (Θ / 2)) * Θ = Θ + 2 := by field_simp
      rwa [he] at hm
    have hmul := mul_le_mul_of_nonneg_right h1 hLcpos.le
    rwa [mul_comm ‖LFunction χ c‖⁻¹ Θ, mul_assoc, inv_mul_cancel₀ hLcpos.ne', mul_one] at hmul
  rw [norm_div, div_le_div_iff₀ hLcpos hΘ0]
  set Lc : ℝ := ‖LFunction χ c‖ with hLcdef
  have hstep : Θ ≤ 5 * Lc := by nlinarith [hfloor, hΘ12, hLcpos]
  calc ‖LFunction χ z‖ * Θ ≤ M * Θ := mul_le_mul_of_nonneg_right hLz hΘ0.le
    _ ≤ M * (5 * Lc) := mul_le_mul_of_nonneg_left hstep (by linarith [hM])
    _ = 5 * M * Lc := by ring

/-! ## 2. The keep-one and drop-all legs at the near-1-line disc -/

/-- **Keep-one at a near-1-line disc, for `L(·,χ)`** (mirror of `Salt.Vk.zeta_keep_one_disc`).
At `c = (1+Θ/2)+iγ` (`γ = Im ρ`, radius `λ = 6Θ/7`) the normalized `G = L(·,χ)/L(c,χ)` is entire
with `G c = 1`, so `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` applies; if the zero `ρ` lies
inside the ball (`Re ρ > 1 − (11/14)Θ`) it is retained:
`Re(−L'/L(σ+iγ,χ)) ≤ (120/λ)·log(4M₀) − 1/(σ − Re ρ)`.

**No `Re(1/(s−1))` term** — that is the pole correction ζ's `Zc` normalization forces and `L`
does not. -/
theorem LFunction_keep_one_disc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Θ σ M₀ : ℝ} (hΘ0 : 0 < Θ) (hM₀ : 1 ≤ M₀) (hσlo : 1 < σ)
    (hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ) (hρnear : 1 - 11 / 14 * Θ < ρ.re)
    (hsphere74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀) :
    (-logDeriv (LFunction χ) ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ (120 / (6 * Θ / 7)) * Real.log (4 * M₀) - 1 / (σ - ρ.re) := by
  set γ : ℝ := ρ.im with hγ
  set lam : ℝ := 6 * Θ / 7 with hlam
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * I with hc
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * I with hs
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hLc : LFunction χ c ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hcre]; nlinarith [hΘ0])
  have hsre : s.re = σ := by rw [hs]; simp
  have hLs : LFunction χ s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hsre]; exact hσlo.le)
  -- the normalized function `G = L/L(c)`, center value `1`; `logDeriv G = logDeriv L`
  have hLdiff : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  have hG_diff : Differentiable ℂ (fun z => LFunction χ z / LFunction χ c) :=
    fun z => (hLdiff z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖LFunction χ c / LFunction χ c‖ := by
    rw [div_self hLc, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => LFunction χ w / LFunction χ c) z
      = logDeriv (LFunction χ) z := by
    intro z
    have hGeq : (fun w => LFunction χ w / LFunction χ c)
        = fun w => (LFunction χ c)⁻¹ * LFunction χ w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (LFunction χ c)⁻¹ (inv_ne_zero hLc)]
  obtain ⟨Z, m, hh, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  -- geometry: `s − c`, `ρ − c`, `s − ρ` are all real (shared imaginary part `γ`)
  have hsc : s - c = ((σ - 1 - Θ / 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
  have hscnorm : ‖s - c‖ ≤ 23 / 20 * lam := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, hlam]
    calc |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := hσc
      _ = 23 / 20 * (6 * Θ / 7) := by ring
  have hGs0 : LFunction χ s / LFunction χ c ≠ 0 := div_ne_zero hLs hLc
  have hnum' := hnum s hscnorm hGs0
  rw [hLDG s] at hnum'
  have hre := neg_re_logDeriv_le hnum'
  -- pull `ρ` into the partial-fraction set
  have hGρ : LFunction χ ρ / LFunction χ c = 0 := by rw [hρ0, zero_div]
  have hρball : ρ ∈ ball c (3 / 2 * lam) := by
    rw [mem_ball, dist_eq_norm]
    have hρc : ρ - c = ((ρ.re - 1 - Θ / 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.sub_re, hcre, Complex.ofReal_re]; ring
      · rw [Complex.sub_im, hc]
        simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
          Complex.ofReal_re, hγ]
    rw [hρc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [hβ1, hΘ0] : ρ.re - 1 - Θ / 2 ≤ 0), hlam]
    nlinarith [hρnear, hΘ0]
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization_gen hne_h hEqOn hρball hGρ
  -- all retained terms have positive real part; the `ρ`-term is retained
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'div : LFunction χ ρ' / LFunction χ c = 0 := (hmemb ρ' hρ').2
    have hρ'0 : LFunction χ ρ' = 0 := (div_eq_zero_iff.mp hρ'div).resolve_right hLc
    have hlt : ρ'.re < 1 := by
      by_contra hcn
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hcn) hρ'0
    rw [Complex.sub_re, hsre]; linarith
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hs, hγ]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hσρpos : 0 < σ - ρ.re := by
    have h := hpos ρ hρZ; rwa [Complex.sub_re, hsre] at h
  have hterm_re : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hsingle : (m ρ : ℝ) * (1 / (s - ρ)).re ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.single_le_sum (term_re_nonneg m hpos) hρZ
  have hlow : 1 / (σ - ρ.re) ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    have hm1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have hnn : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    have h3 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by rw [hterm_re]; nlinarith
    linarith [h3, hsingle]
  linarith [hre, hlow]

/-- **Drop-all at a near-1-line disc, for `L(·,ψ)`** (mirror of `Salt.Vk.zeta_drop_all_disc`):
dropping every partial-fraction zero (each contributes `≥ 0`),
`Re(−L'/L(σ+iτ,ψ)) ≤ (120/λ)·log(4M₀)`.  Used at the doubled height `τ = 2γ` with `ψ = χ²`. -/
theorem LFunction_drop_all_disc {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ1 : ψ ≠ 1)
    {Θ σ M₀ τ : ℝ} (hΘ0 : 0 < Θ) (hM₀ : 1 ≤ M₀) (hσlo : 1 < σ)
    (hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ)
    (hsphere74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖LFunction ψ z / LFunction ψ (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖LFunction ψ z / LFunction ψ (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀) :
    (-logDeriv (LFunction ψ) ((σ : ℂ) + (τ : ℂ) * I)).re
      ≤ (120 / (6 * Θ / 7)) * Real.log (4 * M₀) := by
  set lam : ℝ := 6 * Θ / 7 with hlam
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hLc : LFunction ψ c ≠ 0 :=
    LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by rw [hcre]; nlinarith [hΘ0])
  have hsre : s.re = σ := by rw [hs]; simp
  have hLs : LFunction ψ s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by rw [hsre]; exact hσlo.le)
  have hLdiff : Differentiable ℂ (LFunction ψ) := differentiable_LFunction hψ1
  have hG_diff : Differentiable ℂ (fun z => LFunction ψ z / LFunction ψ c) :=
    fun z => (hLdiff z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖LFunction ψ c / LFunction ψ c‖ := by
    rw [div_self hLc, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => LFunction ψ w / LFunction ψ c) z
      = logDeriv (LFunction ψ) z := by
    intro z
    have hGeq : (fun w => LFunction ψ w / LFunction ψ c)
        = fun w => (LFunction ψ c)⁻¹ * LFunction ψ w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (LFunction ψ c)⁻¹ (inv_ne_zero hLc)]
  obtain ⟨Z, m, hh, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  have hsc : s - c = ((σ - 1 - Θ / 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
  have hscnorm : ‖s - c‖ ≤ 23 / 20 * lam := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, hlam]
    calc |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := hσc
      _ = 23 / 20 * (6 * Θ / 7) := by ring
  have hnum' := hnum s hscnorm (div_ne_zero hLs hLc)
  rw [hLDG s] at hnum'
  have hre := neg_re_logDeriv_le hnum'
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'div : LFunction ψ ρ' / LFunction ψ c = 0 := (hmemb ρ' hρ').2
    have hρ'0 : LFunction ψ ρ' = 0 := (div_eq_zero_iff.mp hρ'div).resolve_right hLc
    have hlt : ρ'.re < 1 := by
      by_contra hcn
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (not_lt.mp hcn) hρ'0
    rw [Complex.sub_re, hsre]; linarith
  have hsum_nn : 0 ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.sum_nonneg (term_re_nonneg m hpos)
  linarith [hre, hsum_nn]

/-! ## 3. The 3-4-1 assembly at the near-1-line disc width (`χ² ≠ 1`) -/

/-- **THE KEY LEMMA — the VK-width 3-4-1 assembly for `L(·,χ)`, `χ² ≠ 1`.**  The exact analogue
of `Salt.Vk.zeta_zero_free_of_disc`, with the SAME gate shapes `(hσΘ, hwΘ, hchainC)` so that the
width algebra of `Salt.Vk.zeta_zero_free_pow_core` transports numeral-for-numeral.

The three legs: `ζ(σ)³`'s pole at real `σ` (`neg_logDeriv_LFunction_trivChar_le` — the ONE place
the pole is load-bearing, and it is character-free), `L(σ+iγ,χ)⁴`'s keep-one
(`LFunction_keep_one_disc`), `L(σ+2iγ,χ²)`'s drop-all (`LFunction_drop_all_disc`); then
`three_four_one_logDeriv` and `zero_free_extraction`.  The Davenport chain is
`4/(σ−β) ≤ 3/(σ−1) + 3 + 5·Cnum` — ζ's `8` becomes `3`, because the two pole corrections
`Re(1/(s₁−1))`, `Re(1/(s₂−1))` are absent.  Consequently **no height hypothesis is needed**
(ζ's assembly needs `1 ≤ |Im ρ|` exactly to bound those two terms). -/
theorem LFunction_zero_free_of_disc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Θ M₀ Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ2 : Θ ≤ 2) (hM₀ : 1 ≤ M₀)
    (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq) (hσΘ : dd / Lq ≤ Θ / 2)
    (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * M₀)) ≤ Lq / (2 * dd))
    (hkeep74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hkeep32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖LFunction χ z / LFunction χ (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hdrop74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (7 / 4 * (6 * Θ / 7)),
        ‖LFunction (χ ^ 2) z
          / LFunction (χ ^ 2) (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀)
    (hdrop32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (3 / 2 * (6 * Θ / 7)),
        ‖LFunction (χ ^ 2) z
          / LFunction (χ ^ 2) (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have h6Θ : (0 : ℝ) < 6 * Θ / 7 := by linarith [hΘ0]
  set Cnum : ℝ := (120 / (6 * Θ / 7)) * Real.log (4 * M₀) with hCnum
  have hCnum0 : 0 ≤ Cnum := by
    rw [hCnum]
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) h6Θ)) (Real.log_nonneg (by nlinarith [hM₀]))
  have hddL : 0 < dd / Lq := div_pos hdd hLq0
  set σ : ℝ := 1 + dd / Lq with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith [hddL]
  have hσ2le : σ ≤ 2 := by rw [hσdef]; linarith [hσΘ, hΘ2]
  have hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := by
    rw [hσdef, abs_of_nonpos (by nlinarith [hσΘ, hddL] : (1 + dd / Lq) - 1 - Θ / 2 ≤ 0)]
    nlinarith [hσΘ, hΘ0, hddL]
  rcases le_or_gt ρ.re (1 - 11 / 14 * Θ) with hout | hin
  · linarith [hwΘ, hout]
  · -- the Davenport chain
    have hA1 := LFunction_keep_one_disc hχ1 hρ0 hβ1 hΘ0 hM₀ hσ1 hσc hin hkeep74 hkeep32
    have hA2 := LFunction_drop_all_disc (ψ := χ ^ 2) hχ2 (τ := 2 * ρ.im) hΘ0 hM₀ hσ1 hσc
      hdrop74 hdrop32
    have hA0 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)).re
        ≤ 1 / (σ - 1) + 1 := neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2le
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C,
        neg_logDeriv_LSeries_eq (χ ^ 2) hσ2C] at h341
    -- align the two disc legs with `s1`, `s2`
    have hs2align : (σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I = s2 := by rw [hs2def]; push_cast; ring
    rw [hs2align] at hA2
    rw [← hCnum] at hA1 hA2
    have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1)) + (8 + 5 * Cnum) := by
      linarith [h341, hA0, hA1, hA2, hCnum0]
    have hchain' : 4 / (dd / Lq + (1 - ρ.re)) ≤ 3 / (dd / Lq) + (1 / (2 * dd)) * Lq := by
      rw [mul_one_div, mul_one_div] at key
      have e1 : σ - ρ.re = dd / Lq + (1 - ρ.re) := by rw [hσdef]; ring
      have e2 : σ - 1 = dd / Lq := by rw [hσdef]; ring
      rw [e1, e2] at key
      have hCLq : (8 : ℝ) + 5 * Cnum ≤ (1 / (2 * dd)) * Lq := by
        rw [div_mul_eq_mul_div, one_mul]; linarith [hchainC]
      linarith [key, hCLq]
    have hCdd : (1 / (2 * dd)) * dd = 1 / 2 := by field_simp
    have hext := zero_free_extraction hLq0 hdd hCdd hβ1 hchain'
    linarith [hext]

/-! ## 4. The box-growth discharge (mirror of `Salt.Vk.region_of_uniform_growth`) -/

/-- **The growth-to-region bridge for `L(·,χ)`, `χ² ≠ 1`** (growth-agnostic).  A positive-height
zero `ρ` of `L(·,χ)` (`Im ρ ≥ 2`) with UNIFORM growth bounds `‖L(z,χ)‖ ≤ M` and
`‖L(z,χ²)‖ ≤ M` on the box `Re z ∈ [1−Θ, 2]`, `Im z ∈ [Im ρ − 1, 3 Im ρ]` — the box containing
all four Borel–Carathéodory spheres, at height `γ` and at the doubled height `2γ` — yields
`Re ρ ≤ 1 − dd/(7 Lq)`, provided the three closing gates hold at `M₀ = 5M/Θ`.

Same statement shape as ζ's `region_of_uniform_growth`, minus the `1 ≤ |Im ρ|` leg. -/
theorem LFunction_region_of_uniform_growth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Θ M Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hγ2 : 2 ≤ ρ.im)
    (hM : 1 ≤ M) (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq)
    (hσΘ : dd / Lq ≤ Θ / 2) (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * M / Θ))) ≤ Lq / (2 * dd))
    (hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction χ z‖ ≤ M)
    (hgrowth2 : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction (χ ^ 2) z‖ ≤ M) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have hM₀ : (1 : ℝ) ≤ 5 * M / Θ := by
    rw [le_div_iff₀ hΘ0]; nlinarith [hM, hΘ12, hΘ0]
  -- the sphere geometry: any point of a `τ`-centered sphere of radius `R ≤ (3/2)Θ` sits in the box
  have box : ∀ (τ R : ℝ), 0 ≤ R → R ≤ 3 / 2 * Θ → ρ.im - 1 + R ≤ τ → τ + R ≤ 3 * ρ.im →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
        (1 - Θ ≤ z.re ∧ z.re ≤ 2) ∧ (ρ.im - 1 ≤ z.im ∧ z.im ≤ 3 * ρ.im) := by
    intro τ R hR0 hR hτlo hτhi z hz
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
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    · have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    · have := (abs_le.mp himb).1; linarith [hτlo]
    · have := (abs_le.mp himb).2; linarith [hτhi]
  -- radius bookkeeping (identical to ζ's)
  have hR74 : (7 : ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3 : ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR74' : (0 : ℝ) ≤ 7 / 4 * (6 * Θ / 7) := by positivity
  have hR32' : (0 : ℝ) ≤ 3 / 2 * (6 * Θ / 7) := by positivity
  refine LFunction_zero_free_of_disc hχ1 hχ2 hρ0 hβ1 hΘ0 (by linarith [hΘ12]) hM₀ hdd hddlt
    hLq0 hσΘ hwΘ hchainC ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box ρ.im _ hR74' hR74 (by nlinarith [hΘ12])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound χ hΘ0 hΘ12 hM (hgrowth z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box ρ.im _ hR32' hR32 (by nlinarith [hΘ12])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound χ hΘ0 hΘ12 hM (hgrowth z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box (2 * ρ.im) _ hR74' hR74 (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound (χ ^ 2) hΘ0 hΘ12 hM (hgrowth2 z h1 h2 h3 h4)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := box (2 * ρ.im) _ hR32' hR32 (by nlinarith [hΘ12, hγ2])
      (by nlinarith [hΘ12, hγ2]) z hz
    exact LFunction_ratio_bound (χ ^ 2) hΘ0 hΘ12 hM (hgrowth2 z h1 h2 h3 h4)

/-! ## 5. THE WIDTH LAW — `width = Θ/log(M/Θ)` (the KR-2 reconciliation) -/

/-- **THE WIDTH LAW.**  With the gates discharged by the canonical `Lq` choice
`Lq = 8 + 700·(1/Θ)·log(20M/Θ)` (the shape `Salt.Vk.zeta_zero_free_pow_core` uses, where
`hchainC` holds by DEFINITION with equality), the region for `L(·,χ)`, `χ² ≠ 1`, reads

  `Re ρ ≤ 1 − Θ/(14·(8Θ + 700·log(20M/Θ)))`.

**This is the answer to KR-2.**  The width is the STRIP HALF-WIDTH `Θ` divided by a logarithm of
the growth-to-width ratio.  Consequently the growth constant `M` — where the twisted Fourier
completion's `q^{3/2}(1+log q)` lives — enters the width only through `log M`, i.e. ADDITIVELY as
`(3/2)log q` inside the denominator, never multiplicatively.  The `3/4` exponent of the VK width
comes entirely from `Θ`, i.e. from the growth's `σ`-dependence, exactly as for ζ. -/
theorem LFunction_zero_free_width_law {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Θ M : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hγ2 : 2 ≤ ρ.im) (hM : 1 ≤ M)
    (hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction χ z‖ ≤ M)
    (hgrowth2 : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction (χ ^ 2) z‖ ≤ M) :
    ρ.re ≤ 1 - Θ / (14 * (8 * Θ + 700 * Real.log (20 * M / Θ))) := by
  set Pinv : ℝ := 1 / Θ with hPinvdef
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hPinv2 : 2 ≤ Pinv := by
    rw [hPinvdef, le_div_iff₀ hΘ0]; linarith [hΘ12]
  set W : ℝ := Real.log (20 * M / Θ) with hWdef
  have h20 : (40 : ℝ) ≤ 20 * M / Θ := by
    rw [le_div_iff₀ hΘ0]; nlinarith [hM, hΘ12]
  have hW1 : (1 : ℝ) ≤ W := by
    have he : Real.exp 1 ≤ 20 * M / Θ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h20
    rw [hWdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  set Lq : ℝ := 8 + 700 * Pinv * W with hLqdef
  have hLqgeP : Pinv ≤ Lq := by
    rw [hLqdef]
    have hkey : 700 * Pinv * 1 ≤ 700 * Pinv * W :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    nlinarith [hkey, hPinvpos]
  have hLq0 : 0 < Lq := lt_of_lt_of_le hPinvpos hLqgeP
  -- the three gates at `dd = 1/2`
  have hΘPinv : Θ = 1 / Pinv := by
    rw [hPinvdef, one_div_one_div]
  have hσΘ : (1 : ℝ) / 2 / Lq ≤ Θ / 2 := by
    rw [hΘPinv, div_div, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hLqgeP])
  have hwΘ : (1 : ℝ) / 2 / (7 * Lq) ≤ 11 / 14 * Θ := by
    rw [hΘPinv, mul_one_div, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hLqgeP, hPinvpos, hLq0]
  have hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * (5 * M / Θ)))
      ≤ Lq / (2 * (1 / 2)) := by
    have h1 : (120 : ℝ) / (6 * Θ / 7) = 140 * Pinv := by
      rw [hΘPinv]; field_simp; ring
    have h2 : (4 : ℝ) * (5 * M / Θ) = 20 * M / Θ := by ring
    rw [h1, h2, ← hWdef, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, hLqdef]
    exact le_of_eq (by ring)
  have hreg := LFunction_region_of_uniform_growth hχ1 hχ2 hρ0 hβ1 (Θ := Θ) (M := M) (Lq := Lq)
    (dd := 1 / 2) hΘ0 hΘ12 hγ2 hM (by norm_num) (by norm_num) hLq0 hσΘ hwΘ hchainC
    hgrowth hgrowth2
  -- `dd/(7Lq) = 1/(14 Lq) = Θ/(14(8Θ + 700 W))`
  have hden : 0 < 8 * Θ + 700 * W := by nlinarith [hΘ0, hW1]
  have hEq : (1 : ℝ) / 2 / (7 * Lq) = Θ / (14 * (8 * Θ + 700 * W)) := by
    rw [hLqdef, hPinvdef]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [hWdef] at hEq
  rw [← hEq]
  exact hreg

/-! ## 6. The VK shape (`q`-graded) — the KR-2 arithmetic made explicit -/

set_option maxHeartbeats 1600000 in
/-- **The width arithmetic** (pure real analysis, no L-function content).  At the landed q-free
half-width `Θ = vkTheta t` (`t = 3γ`, so `L3 = log 3γ ∈ [Lg, 2 Lg]`, `ℓ3 = log L3 ∈ [ℓ, 2ℓ]`) and a
`vkProfile`-genre growth `M = Cq·L3^{3/4}·ℓ3⁴`, the ratio inside the width law's logarithm is
`20M/Θ = 20000·Cq·(L3^{3/4})²·ℓ3⁶`, so

  `log(20M/Θ) = log(20000 Cq) + (3/2)·ℓ3 + 6·log ℓ3 ≤ (A + 5)·ℓ`

under the `q`-scale gate `log(20000 Cq) ≤ A·ℓ`.  **That is the whole of KR-2**: the growth's
`q^{3/2}(1+log q)` is inside `Cq`, hence inside a LOGARITHM, hence an additive `(3/2)log q` in the
denominator — never a factor on the width.  The width therefore keeps ζ's shape
`1/(Lg^{3/4}·ℓ³)` with a constant linear in `A`. -/
private lemma vk_width_shape {Lg ℓ L3 ℓ3 Θ M Cq A : ℝ}
    (hLg3 : 3 ≤ Lg) (hℓ1100 : 1100 ≤ ℓ)
    (hL3lb : Lg ≤ L3) (hL3ub : L3 ≤ 2 * Lg) (hℓ3def : ℓ3 = Real.log L3)
    (hℓ3lb : ℓ ≤ ℓ3) (hℓ3ub : ℓ3 ≤ 2 * ℓ)
    (hCq : 1 ≤ Cq) (hA1 : 1 ≤ A) (hgate : Real.log (20000 * Cq) ≤ A * ℓ)
    (hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)))
    (hMval : M = Cq * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (4 : ℕ)) :
    0 < Θ ∧ Θ ≤ 1 / 2 ∧ 1 ≤ M ∧
      (1 / (10 ^ 8 * (A + 5))) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ Θ / (14 * (8 * Θ + 700 * Real.log (20 * M / Θ))) := by
  have hLg0 : 0 < Lg := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hL30 : 0 < L3 := by linarith
  have hℓ31100 : 1100 ≤ ℓ3 := by linarith
  have hℓ30 : 0 < ℓ3 := by linarith
  have hCqpos : (0 : ℝ) < Cq := by linarith
  have h20000Cq : (0 : ℝ) < 20000 * Cq := by linarith
  have hL34pos : 0 < L3 ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL30 _
  have hL31 : (1 : ℝ) ≤ L3 ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hℓ3sq1 : (1 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := one_le_pow₀ (by linarith)
  have hℓ3q1 : (1 : ℝ) ≤ ℓ3 ^ (4 : ℕ) := one_le_pow₀ (by linarith)
  have hLg34nn : 0 ≤ Lg ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hLg0.le _
  -- `Θ = 1/Pinv`, `Pinv = 1000 L3^{3/4} ℓ3²`
  set Pinv : ℝ := 1000 * L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ) with hPinvdef
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  have hPinv2 : 2 ≤ Pinv := by rw [hPinvdef]; nlinarith [hL31, hℓ3sq1]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv, div_le_div_iff₀ hPinvpos (by norm_num)]; linarith
  have hM1 : 1 ≤ M := by
    rw [hMval]
    have h1 : (1 : ℝ) ≤ Cq * L3 ^ ((3 : ℝ) / 4) := by nlinarith [hCq, hL31]
    nlinarith [h1, hℓ3q1]
  refine ⟨hΘ0, hΘ12, hM1, ?_⟩
  -- the logarithm: `log(20M/Θ) = log(20000 Cq) + (3/2) ℓ3 + 6 log ℓ3`
  set W : ℝ := Real.log (20 * M / Θ) with hWdef
  have hWeq : W = Real.log (20000 * Cq) + (3 / 2) * ℓ3 + 6 * Real.log ℓ3 := by
    have h20M : 20 * M / Θ
        = 20000 * Cq * (L3 ^ ((3 : ℝ) / 4)) ^ (2 : ℕ) * ℓ3 ^ (6 : ℕ) := by
      rw [hMval, hΘval]
      field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
      ring
    rw [hWdef, h20M,
      Real.log_mul (mul_ne_zero (ne_of_gt h20000Cq) (pow_ne_zero 2 (ne_of_gt hL34pos)))
        (pow_ne_zero 6 (ne_of_gt hℓ30)),
      Real.log_mul (ne_of_gt h20000Cq) (pow_ne_zero 2 (ne_of_gt hL34pos)),
      Real.log_pow, Real.log_pow, Real.log_rpow hL30, ← hℓ3def]
    push_cast; ring
  have hlogℓ3le : 6 * Real.log ℓ3 ≤ ℓ3 := by
    have h1 : Real.log ℓ3 ≤ 2 * Real.sqrt ℓ3 := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hℓ30)
      rw [Real.log_sqrt hℓ30.le] at h
      linarith [Real.sqrt_nonneg ℓ3]
    have h2 : (33 : ℝ) ≤ Real.sqrt ℓ3 := by
      have h := Real.sqrt_le_sqrt (show (1089 : ℝ) ≤ ℓ3 by linarith)
      rwa [show (1089 : ℝ) = 33 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 33)] at h
    have h3 : Real.sqrt ℓ3 ^ 2 = ℓ3 := Real.sq_sqrt hℓ30.le
    nlinarith [h1, h2, h3, Real.sqrt_nonneg ℓ3]
  have hWub : W ≤ (A + 5) * ℓ := by rw [hWeq]; linarith
  have hW1 : (1 : ℝ) ≤ W := by
    have h20 : (40 : ℝ) ≤ 20 * M / Θ := by
      rw [le_div_iff₀ hΘ0]; nlinarith [hM1, hΘ12]
    have he : Real.exp 1 ≤ 20 * M / Θ :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h20
    rw [hWdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  -- `Pinv ≤ 8000 Lg^{3/4} ℓ²` and `8Θ + 700 W ≤ 704 (A+5) ℓ`
  have hL34le : L3 ^ ((3 : ℝ) / 4) ≤ 2 * Lg ^ ((3 : ℝ) / 4) := by
    have h1 : L3 ^ ((3 : ℝ) / 4) ≤ (2 * Lg) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hL30.le hL3ub (by norm_num)
    have h2 : (2 * Lg) ^ ((3 : ℝ) / 4) = 2 ^ ((3 : ℝ) / 4) * Lg ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hLg0.le
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [h2] at h1; nlinarith [h1, h3, hLg34nn]
  have hℓ3sqle : ℓ3 ^ (2 : ℕ) ≤ 4 * ℓ ^ (2 : ℕ) := by
    calc ℓ3 ^ (2 : ℕ) ≤ (2 * ℓ) ^ (2 : ℕ) := pow_le_pow_left₀ hℓ30.le hℓ3ub 2
      _ = 4 * ℓ ^ (2 : ℕ) := by ring
  have hPinvle : Pinv ≤ 8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by
    have hℓ3nn : (0 : ℝ) ≤ ℓ3 ^ (2 : ℕ) := by positivity
    have hprod := mul_le_mul hL34le hℓ3sqle hℓ3nn
      (by positivity : (0:ℝ) ≤ 2 * Lg ^ ((3:ℝ)/4))
    calc Pinv = 1000 * (L3 ^ ((3 : ℝ) / 4) * ℓ3 ^ (2 : ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * Lg ^ ((3 : ℝ) / 4)) * (4 * ℓ ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ)) := by ring
  set den : ℝ := 8 * Θ + 700 * W with hdendef
  have hden0 : 0 < den := by rw [hdendef]; nlinarith [hΘ0, hW1]
  have hdenub : den ≤ 704 * ((A + 5) * ℓ) := by
    rw [hdendef]; nlinarith [hΘ12, hW1, hWub]
  -- the final comparison
  set D : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hℓ3' : ℓ ^ (2 : ℕ) * ℓ = ℓ ^ (3 : ℕ) := by ring
  have step : 14 * den * Pinv ≤ 10 ^ 8 * (A + 5) * D := by
    calc 14 * den * Pinv
        ≤ 14 * (704 * ((A + 5) * ℓ)) * (8000 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (2 : ℕ))) := by
          apply mul_le_mul (by linarith [hdenub]) hPinvle hPinvpos.le (by positivity)
      _ = 78848000 * (A + 5) * (Lg ^ ((3 : ℝ) / 4) * (ℓ ^ (2 : ℕ) * ℓ)) := by ring
      _ = 78848000 * (A + 5) * D := by rw [hℓ3', hDdef]
      _ ≤ 10 ^ 8 * (A + 5) * D := by nlinarith [hDpos, hA1]
  have hΘPinv1 : Θ * Pinv = 1 := by
    rw [hΘPinv]; field_simp
  have hcmp : (1 : ℝ) / (10 ^ 8 * (A + 5) * D) ≤ Θ / (14 * den) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Θ * (14 * den * Pinv) = 14 * den := by
      rw [show Θ * (14 * den * Pinv) = (14 * den) * (Θ * Pinv) from by ring, hΘPinv1, mul_one]
    rw [one_mul, ← h1]
    exact mul_le_mul_of_nonneg_left step hΘ0.le
  have heq : (1 / (10 ^ 8 * (A + 5))) * (1 / D) = 1 / (10 ^ 8 * (A + 5) * D) := by
    rw [div_mul_div_comm, one_mul]
  rw [heq]
  exact hcmp

/-- **The VK-shaped region for `L(·,χ)`, `χ² ≠ 1`, `q`-graded.**  The width law instantiated at
the landed q-free strip half-width `Θ = vkTheta (3 Im ρ)` (`Salt.Vk.vkTheta`) and a growth ceiling
`M ≤ Cq·(log 3γ)^{3/4}(log log 3γ)⁴` of the `Salt.MR.vkProfile` genre, under the `q`-scale gate
`log(20000·Cq) ≤ A·log log Im ρ`:

  `Re ρ ≤ 1 − (1/(10⁸·(A+5)))/((log Im ρ)^{3/4}(log log Im ρ)³)`

— **exactly ζ's shape (`Salt.Vk.zeta_zero_free_region_pow_of_growth`), with a constant linear in
`A` and nothing else changed.**  At the port's `q ≤ (log H)^12` and
`Cq = 10⁷ q^{3/2}(1+log q)·vkEulerCorr q` one gets `A ≈ 18` (so `c ≈ 1/(2.3·10⁹)`), a `≈ 2×`
debit against ζ's own `1/10⁹`.  **KR-2 is benign: the Fourier completion's `q^{3/2}` reaches the
width only through `log`, i.e. additively, and never touches the `3/4`.**

The height floor `1100 ≤ log log Im ρ` is the SAME floor ζ's own core
(`Salt.Vk.zeta_zero_free_pow_core`) carries; sharpening it is stone B proper's business. -/
theorem LFunction_zero_free_region_vk_shape {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ1 : ρ.re < 1)
    {Cq A : ℝ} (hA1 : 1 ≤ A) (hCq : 1 ≤ Cq)
    (hLg3 : 3 ≤ Real.log ρ.im) (hℓ1100 : 1100 ≤ Real.log (Real.log ρ.im))
    (hγ2 : 2 ≤ ρ.im)
    (hgate : Real.log (20000 * Cq) ≤ A * Real.log (Real.log ρ.im))
    (hgrowth : ∀ z : ℂ, 1 - vkTheta (3 * ρ.im) ≤ z.re → z.re ≤ 2 →
        ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction χ z‖ ≤ Cq * (Real.log (3 * ρ.im)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (3 * ρ.im))) ^ (4 : ℕ))
    (hgrowth2 : ∀ z : ℂ, 1 - vkTheta (3 * ρ.im) ≤ z.re → z.re ≤ 2 →
        ρ.im - 1 ≤ z.im → z.im ≤ 3 * ρ.im →
        ‖LFunction (χ ^ 2) z‖ ≤ Cq * (Real.log (3 * ρ.im)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (3 * ρ.im))) ^ (4 : ℕ)) :
    ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 5)))
      * (1 / ((Real.log ρ.im) ^ ((3 : ℝ) / 4) * (Real.log (Real.log ρ.im)) ^ (3 : ℕ))) := by
  have hγpos : 0 < ρ.im := by linarith
  set Lg : ℝ := Real.log ρ.im with hLgdef
  set ell : ℝ := Real.log Lg with hedef
  set L3 : ℝ := Real.log (3 * ρ.im) with hL3def
  set ell3 : ℝ := Real.log L3 with he3def
  have hLg0 : 0 < Lg := by linarith
  have he0 : 0 < ell := by linarith
  -- `L3 = log 3 + Lg ∈ [Lg, 2 Lg]`, `ell3 ∈ [ell, 2 ell]`
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by
    rw [hL3def, Real.log_mul (by norm_num) hγpos.ne']
  have hL3lb : Lg ≤ L3 := by
    rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith
  have hL30 : 0 < L3 := by linarith
  have he3lb : ell ≤ ell3 := by rw [he3def, hedef]; exact Real.log_le_log hLg0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have he3ub : ell3 ≤ 2 * ell := by
    rw [he3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ell := by rw [Real.log_mul (by norm_num) hLg0.ne', ← hedef]
      _ ≤ 2 * ell := by linarith
  -- the half-width and the growth ceiling, in `vkTheta`'s own shape
  set Θ : ℝ := vkTheta (3 * ρ.im) with hΘdef
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3 : ℝ) / 4) * ell3 ^ (2 : ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← he3def]
  set M : ℝ := Cq * L3 ^ ((3 : ℝ) / 4) * ell3 ^ (4 : ℕ) with hMdef
  obtain ⟨hΘ0, hΘ12, hM1, hshape⟩ := vk_width_shape hLg3 hℓ1100 hL3lb hL3ub he3def he3lb
    he3ub hCq hA1 hgate hΘval hMdef
  have hwl := LFunction_zero_free_width_law hχ1 hχ2 hρ0 hβ1 hΘ0 hΘ12 hγ2 hM1 hgrowth hgrowth2
  linarith [hwl, hshape]

end Salt.MR

end
