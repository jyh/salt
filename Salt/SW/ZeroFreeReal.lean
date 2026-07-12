/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZeroFree
import Salt.SW.ZetaPartialFractions

/-!
# The SW rung, node S3d-b — the zero-free region for real characters at complex zeros

Design: `docs/blueprints/sw.md`, wave S3; the flag "SW S3d" in `docs/blueprints/flags.md`.
This module closes case (b) of the quantitative zero-free region (Davenport §14): for a
**real** primitive character (`χ² = 1`, `χ ≠ 1`), every **complex** zero (`Im ρ ≠ 0`) obeys
`Re ρ ≤ 1 − c₀/log(q(|Im ρ|+2))`, and combines it with the S3d complex-character case
(`zero_free_region_primitive`) into the S5-facing `zero_free_region_all`. Only the real
exceptional (Siegel) zeros escape; those are S3e's (Landau–Page) business.

## The two differences from case (a)

1. **The 3-4-1 third term is the principal character.** `χ² = 1` turns the third carrier into
   `−L'/L(σ+2iγ, χ₀)`, whose pole at `1` must be kept honest at complex `s`:
   `L(·,χ₀) = P·ζ` (`LFunctionTrivChar_eq_mul_riemannZeta`), the Z2ζ bound
   `Re(−ζ'/ζ(σ+2iγ)) ≤ Re(1/(s−1)) + 1080 log(|γ|+2)` (`zeta_neg_re_logDeriv_le`), and the
   finite Euler correction `‖logDeriv P‖ ≤ log q` (the mod-1 `eulerFactor` per-factor bound).
2. **The conjugate zero.** `χ² = 1` forces `χ(n) ∈ {0, ±1}`, so the Dirichlet coefficients are
   real and `L(χ, conj s) = conj L(χ, s)` (`LFunction_conj`, by the series on `Re s > 1` and
   the identity theorem); hence `conj ρ` is also a zero. When `|γ| < σ−1` the conjugate lies in
   the partial-fraction ball and its retained term `(σ−β)/((σ−β)²+4γ²) ≥ 1/(5(σ−β))` beats the
   pole's `≤ 1/(σ−1)`, restoring the 3-4-1 margin as `24/5 > 4`.

## The Davenport arithmetic (at `σ = 1 + δ/L`, `δ = 1/15856`, `L = log(q(|γ|+2))`)

All growth terms collapse to `3964·L = (1/4)/(σ−1)`. Case (i) `|γ| ≥ σ−1` (keep one zero;
pole `≤ (1/4)/(σ−1)`): `4/(σ−β) ≤ (7/2)/(σ−1)` gives `1−β ≥ δ/(7L)`. Case (ii) `|γ| < σ−1`
(keep the conjugate pair; pole `≤ 1/(σ−1)`): `(24/5)/(σ−β) ≤ (17/4)/(σ−1)` gives
`1−β ≥ (11/85)·δ/L`. Both dominate `c₀/L` with **`c₀ = δ/8 = 1/126848`**.
-/

namespace Salt.SW

open Complex DirichletCharacter Filter Metric
open scoped LSeries.notation Topology

/-! ## 1. Real characters are conjugation-stable; the conjugate zero -/

/-- A quadratic character (`χ² = 1`) takes real values (`±1` on units, `0` off the units), so
complex conjugation fixes every value: `conj (χ a) = χ a`. -/
lemma conj_apply_eq_of_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1)
    (a : ZMod q) : (starRingEnd ℂ) (χ a) = χ a := by
  by_cases hu : IsUnit a
  · have hsq' : χ a ^ 2 = 1 := by
      have h1 : (χ ^ 2) a = 1 := by rw [hsq, MulChar.one_apply hu]
      rw [← h1, MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0) a]
    have hfac : (χ a - 1) * (χ a + 1) = 0 := by linear_combination hsq'
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h, map_one]
    · rw [eq_neg_of_add_eq_zero_left h]; simp
  · rw [MulChar.map_nonunit χ hu, map_zero]

/-- `conj (n^{conj s}) = n^s` for a natural base (`arg n = 0 ≠ π`). -/
lemma conj_natCast_cpow (n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ ((starRingEnd ℂ) s)) = (n : ℂ) ^ s := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
  rw [Complex.cpow_conj _ _ harg, Complex.conj_conj, map_natCast]

/-- **The conjugation functional equation for real characters.** For `χ ≠ 1` with `χ² = 1`,
`L(χ, conj s) = conj (L(χ, s))`: the Dirichlet coefficients are real
(`conj_apply_eq_of_sq_eq_one`), so `conj ∘ L(χ) ∘ conj` agrees with `L(χ)` on the series
half-plane `Re s > 1`; both are entire (`differentiable_LFunction`), and the identity theorem
extends the agreement to all of `ℂ`. -/
lemma LFunction_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    (hsq : χ ^ 2 = 1) (s : ℂ) :
    LFunction χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (LFunction χ s) := by
  have hLdiff : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  -- the composed conjugate is entire
  have hFdiff : Differentiable ℂ
      (fun z => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z))) := by
    intro z
    have h1 : DifferentiableAt ℂ (LFunction χ) ((starRingEnd ℂ) z) := hLdiff _
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2
  -- agreement with `L(χ)` on the series half-plane
  have hser : ∀ z : ℂ, 1 < z.re →
      (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ z := by
    intro z hz
    have hzc : 1 < ((starRingEnd ℂ) z).re := by rwa [Complex.conj_re]
    have hterm : ∀ n : ℕ, (starRingEnd ℂ) (LSeries.term ↗χ ((starRingEnd ℂ) z) n)
        = LSeries.term ↗χ z n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
          conj_apply_eq_of_sq_eq_one hsq, conj_natCast_cpow]
    rw [LFunction_eq_LSeries χ hzc, LFunction_eq_LSeries χ hz]
    calc (starRingEnd ℂ) (LSeries ↗χ ((starRingEnd ℂ) z))
        = ∑' n, (starRingEnd ℂ) (LSeries.term ↗χ ((starRingEnd ℂ) z) n) := by
          rw [show LSeries ↗χ ((starRingEnd ℂ) z)
              = ∑' n, LSeries.term ↗χ ((starRingEnd ℂ) z) n from rfl, Complex.conj_tsum]
      _ = ∑' n, LSeries.term ↗χ z n := tsum_congr hterm
      _ = LSeries ↗χ z := rfl
  -- identity theorem on `ℂ`
  have hana_F : AnalyticOnNhd ℂ
      (fun z => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z))) Set.univ :=
    hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hana_L : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    hLdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ z := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
    have hgt : ∀ᶠ z in 𝓝 (2 : ℂ),
        (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) z)) = LFunction χ z := by
      filter_upwards [hopen1.mem_nhds h2'] with z hz
      exact hser z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have heqOn := hana_F.eqOn_of_preconnected_of_frequently_eq hana_L
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) hfreq
  have hFs : (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) s)) = LFunction χ s :=
    heqOn (Set.mem_univ s)
  have hconj := congrArg (starRingEnd ℂ) hFs
  rwa [Complex.conj_conj] at hconj

/-- Zeros of a real character's L-function come in conjugate pairs. -/
lemma LFunction_conj_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    (hsq : χ ^ 2 = 1) {ρ : ℂ} (hρ : LFunction χ ρ = 0) :
    LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  rw [LFunction_conj hχ1 hsq ρ, hρ, map_zero]

/-! ## 2. The trivial-character log-derivative bound at complex `s` (the 3-4-1 third term) -/

/-- The χ₀ Euler-correction factor `1 − p^{−s}` is the `eulerFactor` of the trivial character
mod `1` (whose value at every `p` is `1`) — this reuses the EulerBridge per-factor machinery. -/
lemma eulerFactor_one_eq (p : ℕ) :
    eulerFactor (1 : DirichletCharacter ℂ 1) p = fun s : ℂ => 1 - (p : ℂ) ^ (-s) := by
  funext s
  rw [eulerFactor, MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- **S3d-b, term 3.** At `s = σ + 2iγ` with `1 < σ ≤ 2`,
`Re(−L'/L(s, χ₀)) ≤ Re(1/(s−1)) + 1080·log(|γ|+2) + log q` — the honest complex pole term.
Route: `L(·,χ₀) = P·ζ` near `s` (`LFunctionTrivChar_eq_mul_riemannZeta`), the Z2ζ bound
`zeta_neg_re_logDeriv_le` for the ζ part, and `‖logDeriv P s‖ ≤ Σ_{p∣q} log p ≤ log q` for the
finite Euler correction (per-factor bound via the mod-1 `eulerFactor`). -/
lemma neg_re_logDeriv_trivChar_complex_le (q : ℕ) [NeZero q] {σ γ : ℝ}
    (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℂ) + 2 * (γ : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + 2 * (γ : ℂ) * I) - 1)).re + 1080 * Real.log (|γ| + 2)
        + Real.log (q : ℝ) := by
  set s : ℂ := (σ : ℂ) + 2 * (γ : ℂ) * I with hs
  have hsre : s.re = σ := by
    rw [hs]; simp [Complex.add_re, Complex.mul_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hσC.le
  have hspos : (0 : ℝ) < s.re := by linarith
  -- per-factor facts at `s`, via the mod-1 eulerFactor machinery
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
  set P : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)) with hPdef
  have hP0 : P s ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac_ne
  have hPdiff : DifferentiableAt ℂ P s := DifferentiableAt.fun_finsetProd hfac_diff
  have hζdiff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  -- the multiplicative split `logDeriv L(χ₀) = logDeriv P + logDeriv ζ` at `s`
  have hLmul : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv P s + logDeriv riemannZeta s := by
    have hEq : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        fun z => P z * riemannZeta z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      rw [hPdef]
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by simpa using hz)
    have hcong : logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s
        = logDeriv (fun z => P z * riemannZeta z) s := by
      simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_mul s hP0 hζ0 hPdiff hζdiff]
  -- the Euler correction: `‖logDeriv P s‖ ≤ log q`
  have hPsum : logDeriv P s
      = ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s := by
    rw [hPdef]
    exact logDeriv_prod hfac_ne hfac_diff
  have hPbound : ‖logDeriv P s‖ ≤ Real.log (q : ℝ) := by
    rw [hPsum]
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
          apply Finset.sum_le_sum
          intro p hp
          have h := norm_logDeriv_eulerFactor_le (1 : DirichletCharacter ℂ 1)
            (Nat.prime_of_mem_primeFactors hp) (le_of_lt hσC)
          rwa [eulerFactor_one_eq p] at h
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
      _ ≤ Real.log (q : ℝ) := by
          apply Real.log_le_log
          · apply Finset.prod_pos
            exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  -- assemble with the Z2ζ bound
  have hζbound : (-logDeriv riemannZeta s).re
      ≤ (1 / (s - 1)).re + 1080 * Real.log (|γ| + 2) := by
    have h := zeta_neg_re_logDeriv_le h1 h2 (γ := γ)
    rw [← hs] at h
    exact h
  have hPre : (-logDeriv P s).re ≤ Real.log (q : ℝ) := by
    have h := (Complex.abs_re_le_norm (logDeriv P s)).trans hPbound
    rw [Complex.neg_re]
    linarith [(abs_le.mp h).1]
  have hsplit : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s).re
      = (-logDeriv riemannZeta s).re + (-logDeriv P s).re := by
    rw [hLmul, neg_add, Complex.add_re, Complex.neg_re, Complex.neg_re]
    ring
  rw [hsplit]
  linarith [hζbound, hPre]

/-! ## 3. The keep-two-zeros bound (the conjugate pair retained) -/

/-- **Keep-two-zeros bound.** For a primitive `ψ` mod `q ≥ 2` with a complex zero `ρ`
(`3/4 ≤ Re ρ < 1`, `0 < |Im ρ| ≤ 1/4`) whose conjugate is also a zero, at `s = σ + i·Im ρ`
(`1 < σ < 2`) both `ρ` and `conj ρ` lie in the partial-fraction zero set
(`|conj ρ − c|² ≤ 25/16 + 1/4 < 9/4`), so both positive terms are retained:
`(−L'/L(s))·re ≤ 120·log(4M₀) − 1/(σ−β) − (σ−β)/((σ−β)² + 4γ²)`. -/
lemma neg_reLogDeriv_le_keep_two {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ.IsPrimitive) (hf : 2 ≤ q) {ρ : ℂ} (hρ0 : LFunction ψ ρ = 0)
    (hρc0 : LFunction ψ ((starRingEnd ℂ) ρ) = 0)
    (hβge : 3 / 4 ≤ ρ.re) (hβ1 : ρ.re < 1) (hγ0 : ρ.im ≠ 0) (hγ4 : |ρ.im| ≤ 1 / 4)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    (-logDeriv (LFunction ψ) ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
        - 1 / (σ - ρ.re)
        - (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
  have hψ1 : ψ ≠ 1 := ne_one_of_isPrimitive ψ hψ hf
  obtain ⟨Z, m, h, hZmem, -, hne_h, hEqOn, -, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' ψ hψ hf ρ.im
  set c : ℂ := 2 + (ρ.im : ℂ) * I with hcdef
  set s : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hsdef
  have hsc : ‖s - c‖ ≤ 23 / 20 := by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hsdef, hcdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hsre : (1 : ℝ) < s.re := by rw [hsdef]; simpa using hσ1
  have hLs : LFunction ψ s ≠ 0 := LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (le_of_lt hsre)
  have hre := neg_re_logDeriv_le (hnum s hsc hLs)
  -- `ρ` in the ball
  have hρball : ρ ∈ ball c (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hsub : ρ - c = ((ρ.re - 2 : ℝ) : ℂ) := by
      rw [hcdef]; apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)]
    linarith
  -- `conj ρ` in the ball: `(2−β)² + 4γ² ≤ 25/16 + 1/4 < 9/4`
  have hρcball : (starRingEnd ℂ) ρ ∈ ball c (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hre' : ((starRingEnd ℂ) ρ - c).re = ρ.re - 2 := by
      rw [hcdef]
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
    have him' : ((starRingEnd ℂ) ρ - c).im = -ρ.im - ρ.im := by
      rw [hcdef]
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
    have hsq' : ‖(starRingEnd ℂ) ρ - c‖ ^ 2 ≤ 29 / 16 := by
      have hns := Complex.normSq_eq_norm_sq ((starRingEnd ℂ) ρ - c)
      rw [Complex.normSq_apply, hre', him'] at hns
      rw [← hns]
      have hγsq : ρ.im * ρ.im ≤ 1 / 16 := by
        have h1 := mul_self_le_mul_self (abs_nonneg ρ.im) hγ4
        rw [abs_mul_abs_self] at h1
        linarith
      nlinarith [hβge, hβ1]
    nlinarith [norm_nonneg ((starRingEnd ℂ) ρ - c), hsq']
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization hne_h hEqOn hρball hρ0
  obtain ⟨hρcZ, hmρc⟩ := mem_zeros_of_factorization hne_h hEqOn hρcball hρc0
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : LFunction ψ ρ' = 0 := (hZmem ρ' hρ').2
    have hlt : ρ'.re < 1 := by
      by_contra hc
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (not_lt.mp hc) hρ'0
    rw [Complex.sub_re]; linarith [hsre]
  have hρne : ρ ≠ (starRingEnd ℂ) ρ := by
    intro heq
    exact hγ0 (Complex.conj_eq_iff_im.mp heq.symm)
  have hσρpos : 0 < σ - ρ.re := by linarith
  -- the two retained real parts
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hsdef]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have hterm1 : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  have hterm2 : (1 / (s - (starRingEnd ℂ) ρ)).re
      = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
    have hre2 : (s - (starRingEnd ℂ) ρ).re = σ - ρ.re := by
      rw [hsdef]
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
    have him2 : (s - (starRingEnd ℂ) ρ).im = 2 * ρ.im := by
      rw [hsdef]
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
      ring
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hre2, him2]
    ring
  -- pair sum lower bound
  have hpairsub : ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ) ⊆ Z := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hρZ
    · rw [Finset.mem_singleton] at hx; subst hx; exact hρcZ
  have hpair_le : ∑ ρ' ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ), (m ρ' : ℝ) * (1 / (s - ρ')).re
      ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hpairsub
      (fun x hxZ _ => term_re_nonneg m hpos x hxZ)
  have hpair_eq : ∑ ρ' ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ), (m ρ' : ℝ) * (1 / (s - ρ')).re
      = (m ρ : ℝ) * (1 / (s - ρ)).re
        + (m ((starRingEnd ℂ) ρ) : ℝ) * (1 / (s - (starRingEnd ℂ) ρ)).re := by
    rw [Finset.sum_insert (by simpa using hρne), Finset.sum_singleton]
  -- each retained term dominates its unit-multiplicity value
  have hv1 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by
    have h1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have h2 : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    rw [hterm1]; nlinarith
  have hv2 : (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2)
      ≤ (m ((starRingEnd ℂ) ρ) : ℝ) * (1 / (s - (starRingEnd ℂ) ρ)).re := by
    have h1 : (1 : ℝ) ≤ (m ((starRingEnd ℂ) ρ) : ℝ) := by exact_mod_cast hmρc
    have hden : (0 : ℝ) < (σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2 := by
      nlinarith [pow_pos hσρpos 2, sq_nonneg ρ.im]
    have h2 : (0 : ℝ) ≤ (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) :=
      le_of_lt (div_pos hσρpos hden)
    rw [hterm2]; nlinarith
  have hlow : 1 / (σ - ρ.re) + (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2)
      ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    rw [hpair_eq] at hpair_le
    linarith [hv1, hv2, hpair_le]
  linarith [hre, hlow]

/-! ## 4. The generic extraction -/

/-- The generic Davenport extraction: from `A/(θ+(1−β)) ≤ B/θ` (`θ, B > 0`, `β < 1`),
`1−β ≥ ((A−B)/B)·θ`. (Cross-multiply and rearrange; used with `A > B`.) -/
lemma zero_free_extraction2 {θ β A B : ℝ} (hθ : 0 < θ) (hB : 0 < B) (hβ : β < 1)
    (hchain : A / (θ + (1 - β)) ≤ B / θ) :
    (A - B) / B * θ ≤ 1 - β := by
  have hη : 0 < θ + (1 - β) := by linarith
  rw [div_le_div_iff₀ hη hθ] at hchain
  rw [div_mul_eq_mul_div, div_le_iff₀ hB]
  nlinarith [hchain]

/-! ## 5. The zero-free region for real primitive characters at complex zeros -/

set_option maxHeartbeats 800000 in
-- The 3-4-1 assembly rewrites heavy `DirichletCharacter.LFunction` terms at three points and
-- runs a two-case Davenport chain in one declaration; it needs more than the default budget.
/-- **S3d-b — the quantitative zero-free region, real-character complex-zero case
(Davenport §14).** There is an explicit constant `c₀ > 0` such that for every real primitive
Dirichlet character `χ` mod `q` (`χ² = 1`, `χ ≠ 1`), every zero `ρ` of `L(·,χ)` with
`Re ρ ≥ 1/2` and `Im ρ ≠ 0` satisfies `Re ρ ≤ 1 − c₀ / log(q(|Im ρ| + 2))`.
Here **`c₀ = 1/126848`** (`δ = 1/15856`, `c₀ = δ/8`).

Route: the 3-4-1 at `σ = 1 + δ/L`; the third term is the principal character
(`neg_re_logDeriv_trivChar_complex_le`, honest pole `Re(1/(σ−1+2iγ))`); the growth terms
collapse to `3964·L = (1/4)/(σ−1)`. Case `|γ| ≥ σ−1`: the pole is `≤ (1/4)/(σ−1)` and the
keep-one bound closes `4/(σ−β) ≤ (7/2)/(σ−1)`. Case `|γ| < σ−1`: the conjugate zero
(`LFunction_conj_zero`) is retained too (`neg_reLogDeriv_le_keep_two`), its term
`≥ 1/(5(σ−β))` beats the pole's `≤ 1/(σ−1)`, closing `(24/5)/(σ−β) ≤ (17/4)/(σ−1)`. -/
theorem zero_free_region_real :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 = 1 → χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.im ≠ 0 →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  refine ⟨1 / 126848, by norm_num, ?_⟩
  intro q hNe χ hχ hsq hχ1 ρ hzero _hre hγ0
  -- basics (mirror S3d)
  have hcond : χ.conductor = q := hχ
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1
    have hqne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set Lval : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLdef
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * (|ρ.im| + 2) := by
    nlinarith [abs_nonneg ρ.im, hqR2,
      mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
  have hexp4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp4
  have hL1 : (1 : ℝ) ≤ Lval := le_trans h4 (Real.log_le_log (by norm_num) hQ4)
  have hLpos : (0 : ℝ) < Lval := by linarith
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hzero
  rcases le_or_gt ρ.re (3 / 4) with hβle | hβgt
  · -- trivial branch: `Re ρ ≤ 3/4 ≤ 1 − c₀/L`
    have hc0 : (1 / 126848 : ℝ) / Lval ≤ 1 / 126848 := by
      rw [div_le_iff₀ hLpos]; nlinarith [hL1]
    linarith [hc0, hβle]
  · -- the 3-4-1 machinery
    set dd : ℝ := 1 / 15856 with hdddef
    have hddpos : (0 : ℝ) < dd := by norm_num
    have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
    set σ : ℝ := 1 + dd / Lval with hσdef
    have hddL : dd / Lval ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
    have hθpos : 0 < dd / Lval := div_pos hddpos hLpos
    have hσ1 : 1 < σ := by rw [hσdef]; linarith
    have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
    -- the 3-4-1 positivity with the third character rewritten to `χ₀`
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    rw [hsq] at h341
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ2C] at h341
    -- opaque names for the three log-derivative real parts (keeps the arithmetic light)
    set T0 : ℝ := (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)).re
      with hT0def
    set T1 : ℝ := (-logDeriv (LFunction χ) s1).re with hT1def
    set T2 : ℝ := (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s2).re with hT2def
    -- A₀ : the χ₀ pole bound at real `σ`
    have hA0 : T0 ≤ 1 / (σ - 1) + 1 := by
      have h := neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2.le
      rwa [← hT0def] at h
    -- A₂ : the χ₀ bound at complex `s₂`, with the pole real part evaluated
    have hpole_eval : (1 / (s2 - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) := by
      have hre2 : (s2 - 1).re = σ - 1 := by
        rw [hs2def]
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have him2 : (s2 - 1).im = 2 * ρ.im := by
        rw [hs2def]
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [one_div, Complex.inv_re, Complex.normSq_apply, hre2, him2]
      ring
    have hA2 : T2 ≤ (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2)
        + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ) := by
      have h := neg_re_logDeriv_trivChar_complex_le q hσ1 hσ2.le (γ := ρ.im)
      rw [← hs2def, hpole_eval] at h
      rwa [← hT2def] at h
    clear_value T0 T1 T2
    -- the growth collapses
    have hB1 : 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
        * (1 + Real.log (q : ℝ)))) ≤ 720 * Lval := by
      have := log_four_M0_le (f := q) (q := q) (t := ρ.im) (γ := ρ.im) hq2 le_rfl hq2
        (by linarith [abs_nonneg ρ.im])
      rw [← hLdef] at this; linarith [this]
    have hlogq : Real.log (q : ℝ) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by linarith)
      nlinarith [abs_nonneg ρ.im, hqR2,
        mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
    have hlogγ : Real.log (|ρ.im| + 2) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg ρ.im, hqR2]
    -- the growth-to-pole conversion `3964·L = (1/4)/(σ−1)`
    have hθL : σ - 1 = dd / Lval := by rw [hσdef]; ring
    have hσ1' : (0 : ℝ) < σ - 1 := by linarith
    have hLB : Lval * (σ - 1) = dd := by
      rw [hθL]; field_simp
    have hLdd' : 3964 * Lval = 1 / 4 * (1 / (σ - 1)) := by
      rw [mul_one_div, eq_div_iff (ne_of_gt hσ1')]
      calc 3964 * Lval * (σ - 1) = 3964 * (Lval * (σ - 1)) := by ring
        _ = 3964 * dd := by rw [hLB]
        _ = 1 / 4 := by rw [hdddef]; norm_num
    rcases le_or_gt (σ - 1) |ρ.im| with hcase | hcase
    · -- Case (i): `|γ| ≥ σ−1`; keep one zero; the pole is `≤ (1/4)/(σ−1)`
      have hA1 : T1 ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
          * (1 + Real.log (q : ℝ)))) - 1 / (σ - ρ.re) := by
        have h := neg_reLogDeriv_le_keep χ hχ hq2 hzero (by linarith : 1 / 2 < ρ.re)
          hβ1 hσ1 hσ2
        rw [← hs1def] at h
        rwa [← hT1def] at h
      have hγsq : (σ - 1) * (σ - 1) ≤ ρ.im * ρ.im := by
        have h1 := mul_self_le_mul_self hσ1'.le hcase
        rwa [abs_mul_abs_self] at h1
      have hpole : (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) ≤ 1 / 4 * (1 / (σ - 1)) := by
        have hden : (0 : ℝ) < (σ - 1) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hσ1' 2, sq_nonneg ρ.im]
        rw [mul_one_div, div_le_div_iff₀ hden hσ1']
        nlinarith [hγsq]
      have hA2' : T2 ≤ 1 / 4 * (1 / (σ - 1)) + 1080 * Real.log (|ρ.im| + 2)
          + Real.log (q : ℝ) := by
        linarith [hA2, hpole]
      have hstep : 4 * (1 / (σ - ρ.re))
          ≤ 3 * (1 / (σ - 1)) + 1 / 4 * (1 / (σ - 1))
            + (3 + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
              + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
                  * (1 + Real.log (q : ℝ)))))) := by
        linarith [h341, hA0, hA1, hA2']
      have hcollapse : (3 : ℝ) + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
          + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
              * (1 + Real.log (q : ℝ))))) ≤ 3964 * Lval := by
        linarith [hB1, hlogq, hlogγ, hL1]
      have hchain : 4 * (1 / (σ - ρ.re)) ≤ 7 / 2 * (1 / (σ - 1)) := by
        linarith [hstep, hcollapse, hLdd']
      have hchain' : 4 / (dd / Lval + (1 - ρ.re)) ≤ (7 / 2) / (dd / Lval) := by
        rw [mul_one_div, mul_one_div] at hchain
        have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
        rw [e1, hθL] at hchain
        exact hchain
      have hext := zero_free_extraction2 hθpos (by norm_num : (0:ℝ) < 7 / 2) hβ1 hchain'
      rw [hdddef] at hext
      have hh : (1 / 126848 : ℝ) / Lval ≤ (4 - 7 / 2) / (7 / 2) * (1 / 15856 / Lval) := by
        have heq : (4 - 7 / 2 : ℝ) / (7 / 2) * (1 / 15856 / Lval) = 1 / 110992 / Lval := by
          ring
        rw [heq, div_le_div_iff_of_pos_right hLpos]
        norm_num
      linarith [hext, hh]
    · -- Case (ii): `|γ| < σ−1 ≤ δ`; keep the conjugate pair; the pole is `≤ 1/(σ−1)`
      have hγ4 : |ρ.im| ≤ 1 / 4 := by
        have hddq : σ - 1 ≤ dd := by rw [hθL]; exact hddL
        rw [hdddef] at hddq
        linarith [hcase]
      have hρc0 : LFunction χ ((starRingEnd ℂ) ρ) = 0 := LFunction_conj_zero hχ1 hsq hzero
      have hA1 : T1 ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
          * (1 + Real.log (q : ℝ)))) - 1 / (σ - ρ.re)
            - (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
        have h := neg_reLogDeriv_le_keep_two χ hχ hq2 hzero hρc0 (le_of_lt hβgt) hβ1
          hγ0 hγ4 hσ1 hσ2
        rw [← hs1def] at h
        rwa [← hT1def] at h
      have hηpos : (0 : ℝ) < σ - ρ.re := by linarith
      have hγsq : ρ.im * ρ.im ≤ (σ - 1) * (σ - 1) := by
        have h1 : |ρ.im| * |ρ.im| ≤ (σ - 1) * (σ - 1) :=
          mul_self_le_mul_self (abs_nonneg ρ.im) hcase.le
        rwa [abs_mul_abs_self] at h1
      have hθη : σ - 1 ≤ σ - ρ.re := by linarith
      have hconj_ge : 1 / (5 * (σ - ρ.re))
          ≤ (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
        have hden : (0 : ℝ) < (σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hηpos 2, sq_nonneg ρ.im]
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 5 * (σ - ρ.re)) hden]
        nlinarith [hγsq, mul_self_le_mul_self hσ1'.le hθη]
      have hbridge : (1 : ℝ) / 5 * (1 / (σ - ρ.re)) = 1 / (5 * (σ - ρ.re)) := by
        rw [div_mul_div_comm, one_mul]
      have hpole : (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) ≤ 1 / (σ - 1) := by
        have hden : (0 : ℝ) < (σ - 1) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hσ1' 2, sq_nonneg ρ.im]
        rw [div_le_div_iff₀ hden hσ1']
        nlinarith [sq_nonneg ρ.im]
      have hA2' : T2 ≤ 1 / (σ - 1) + 1080 * Real.log (|ρ.im| + 2)
          + Real.log (q : ℝ) := by
        linarith [hA2, hpole]
      have hstep : 24 / 5 * (1 / (σ - ρ.re))
          ≤ 4 * (1 / (σ - 1))
            + (3 + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
              + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
                  * (1 + Real.log (q : ℝ)))))) := by
        linarith [h341, hA0, hA1, hA2', hconj_ge, hbridge]
      have hcollapse : (3 : ℝ) + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
          + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
              * (1 + Real.log (q : ℝ))))) ≤ 3964 * Lval := by
        linarith [hB1, hlogq, hlogγ, hL1]
      have hchain : 24 / 5 * (1 / (σ - ρ.re)) ≤ 17 / 4 * (1 / (σ - 1)) := by
        linarith [hstep, hcollapse, hLdd']
      have hchain' : (24 / 5) / (dd / Lval + (1 - ρ.re)) ≤ (17 / 4) / (dd / Lval) := by
        rw [mul_one_div, mul_one_div] at hchain
        have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
        rw [e1, hθL] at hchain
        exact hchain
      have hext := zero_free_extraction2 hθpos (by norm_num : (0:ℝ) < 17 / 4) hβ1 hchain'
      rw [hdddef] at hext
      have hh : (1 / 126848 : ℝ) / Lval
          ≤ (24 / 5 - 17 / 4) / (17 / 4) * (1 / 15856 / Lval) := by
        have heq : (24 / 5 - 17 / 4 : ℝ) / (17 / 4) * (1 / 15856 / Lval)
            = 11 / 1347760 / Lval := by
          ring
        rw [heq, div_le_div_iff_of_pos_right hLpos]
        norm_num
      linarith [hext, hh]

/-! ## 6. The combined S5-facing region -/

/-- **S3d ∪ S3d-b — the combined zero-free region for primitive characters.** One constant
`c₀ > 0` covers both the complex-character case (`χ² ≠ 1`, any zero) and the real-character
complex-zero case (`χ² = 1`, `Im ρ ≠ 0`): every zero of `L(·,χ)` with `Re ρ ≥ 1/2` that is not
a real zero of a real character (Siegel territory, S3e) obeys
`Re ρ ≤ 1 − c₀/log(q(|Im ρ|+2))`. `c₀ = min(1/50456, 1/126848) = 1/126848`. -/
theorem zero_free_region_all :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := zero_free_region_primitive
  obtain ⟨c₂, hc₂, h₂⟩ := zero_free_region_real
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro q hNe χ hχ hχ1 ρ hzero hre hor
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hLpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos
    nlinarith [abs_nonneg ρ.im, hq1]
  by_cases hsq : χ ^ 2 = 1
  · have hγ : ρ.im ≠ 0 := by
      rcases hor with h | h
      · exact absurd hsq h
      · exact h
    have hb := h₂ q χ hχ hsq hχ1 hzero hre hγ
    have hmin : min c₁ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      rw [div_le_div_iff_of_pos_right hLpos]
      exact min_le_right c₁ c₂
    linarith [hb, hmin]
  · have hb := h₁ q χ hχ hsq hzero hre
    have hmin : min c₁ c₂ / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ c₁ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      rw [div_le_div_iff_of_pos_right hLpos]
      exact min_le_left c₁ c₂
    linarith [hb, hmin]

/-- **The imprimitive extension of the combined region.** For any `χ mod q` (`χ ≠ 1`), if the
primitive inducing character is non-real or the zero is complex, the region holds at modulus
`q`: the zero transfers to the conductor (`LFunction_eq_zero_iff_primitive`),
`zero_free_region_all` fires there, and `log(f₁(|γ|+2)) ≤ log(q(|γ|+2))` weakens the region
back to `q`. -/
theorem zero_free_region_all' :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := zero_free_region_all
  refine ⟨c₀, hc₀pos, ?_⟩
  intro q hNe χ hχ1 ρ hzero hre hor
  have hρre_pos : 0 < ρ.re := by linarith
  have hzero1 : LFunction χ.primitiveCharacter ρ = 0 :=
    (LFunction_eq_zero_iff_primitive χ hρre_pos (Or.inl hχ1)).mp hzero
  have hf1 : χ.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive χ
  have hχ1' : χ.primitiveCharacter ≠ 1 := fun h =>
    hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
  have hbound := hc₀ χ.conductor χ.primitiveCharacter hf1 hχ1' hzero1 hre hor
  -- modulus monotonicity of the log denominator
  have hf1q : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level χ)
  have hf1_1 : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  set Lf : ℝ := Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) with hLfdef
  set Lq : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLqdef
  have hf1R : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hf1_1
  have hcondR : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hf1q
  have hLf_pos : 0 < Lf := by
    rw [hLfdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1R]
  have hLq_pos : 0 < Lq := by
    rw [hLqdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1R, hcondR]
  have hLfq : Lf ≤ Lq := by
    rw [hLfdef, hLqdef]
    apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im, hf1R])
    exact mul_le_mul_of_nonneg_right hcondR (by positivity)
  have hmono : c₀ / Lq ≤ c₀ / Lf := by
    rw [div_le_div_iff₀ hLq_pos hLf_pos]
    exact mul_le_mul_of_nonneg_left hLfq hc₀pos.le
  linarith [hbound, hmono]

end Salt.SW
