/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.JutilaDetector
import Salt.SW.PseudoCharH
import Salt.SW.DHBalance
import Salt.MR.HalaszWeighted

/-!
# B2 W9b — Jutila's residue block `B(s, χ₀)` (the (ξ,η) device's analytic core)

Jutila 1977, pp.52–53, specialised to a single primitive `χ` and written with the twice-smoothed
Riesz kernel `K(u) = (1 − u)²₊` in place of `e^{−u}`. The Halász weight of (3.3) is

    b_n = n⁻¹ · (Σ'_{r ≤ R} r⁻¹ ψ_r(n))² · (K(n/N) − K(n/M)),        `M ≤ N`     (`jutilaB`)

and the series Lemma 7 puts on its right side, `B(s) = Σ_n b_n χ₀(n) n^{−s}` (the character
`conj(χ)·χ = χ₀`, `halaszBTsum_eq`), is evaluated by ONE contour shift:

    B(s; N, M) = E(χ₀) · resKernel s N M · Σ'_r φ(r)/r²  +  I(s; N, M),   (`halaszBTsum_jutilaB_eq`)

`E(χ₀) = ∏_{p ∣ q}(1 − p⁻¹)`, `resKernel s N M = K̃(−s)(N^{−s} − M^{−s})` with
`K̃(w) = 2/(w(w+1)(w+2))` and the removable point `s = 0` filled by `dslope` (value `log(N/M)`),
and `I(s; N, M)` the `(r, r', d)`-sum of the integrals on `Re(1 + s + w) = 1/2`, where
`‖I(s)‖ ≤ 73·qT·M^{−1/2}·(R(1 + log R))²` for `|Im s| ≤ 2T` (`norm_jutilaI_le`).

## The mechanism, staged

(i) Expand the square of the `r`-sum and apply Lemma 2 in its filter form
(`pseudoChar_mul_eq_sum_hCoef_filter`): `ψ_rψ_{r'}(n) = Σ_{d ∣ rr', d ∣ n} h(d; r, r')`; put
`n = dm`;
`χ₀(dm) = χ₀(m)` since `(d, q) = 1`. (ii) The `m`-series is the twice-smoothed sum with the
trivial character — the factor `d^{−1−s}` leaves the series FIRST (`tsum_trivChar_mul_cpow_eq`), and
`kernel_identity_2` + `kernel_sum_swap_2` give the Mellin integral of
`2((N/d)^w − (M/d)^w)·L(1 + s + w, χ₀)/(w(w+1)(w+2))` on `Re w = 1` (`resIntegrand`).
(iii) The contour node: shift to `Re w = −1/2 − Re s`. Inside, the ONLY singularity is the pole of
`L(·, χ₀)` at `w = −s`: `w = 0` is REMOVABLE (the kernel difference vanishes there — this is why the
`M`-term exists), `w = −1, −2` lie left of the line. With mathlib's ENTIRE regularisation
`LFunctionTrivChar₁ q u = (u − 1)·L(u, χ₀)` the integrand is `(dslope ψ 0)(w)/(w − (−s))` for the
holomorphic `ψ(w) = 2((N/d)^w − (M/d)^w)·LFunctionTrivChar₁ q (1 + s + w)/((w+1)(w+2))`
(`resPhi`), and the Cauchy integral formula on the rectangle (`rectBI_cif_eq`) gives the residue
`(dslope ψ 0)(−s)` — at `s = 0` it is `ψ'(0)`, Jutila's "interpreted as `log(N/M)`", with no case
split. (iv) The residue's `d^{−1−s}(N/d)^{−s} = d⁻¹N^{−s}` cancels the `d^{s}`, and Lemma 3
(`hCoef_sum_div_eq`) collapses `Σ_d h(d; r, r')/d` to `δ_{r,r'} φ(r)`. (v) On the shifted line
`‖L(1 + s + w, χ₀)‖ ≤ q·‖ζ(1/2 + it')‖ ≤ q(7/2 + 3|t'|)` (`LFunctionTrivChar_eq_mul_riemannZeta`,
`norm_riemannZeta_le`), the cubic denominator integrates to `π/m²`, `π/m` at
`m = 1/2 − Re s ≥ 29/60`
(the landed W7 rows), and `Σ_{d ∣ rr'} |h(d)| ≤ ∏(p+1)∏(p+1)` (Lemma 3's size) with
`Σ'_{r,r'} (rr')⁻¹∏(p+1)∏(p+1) ≤ (Σ_{r ≤ R} 2^{ω(r)})² ≤ (R(1 + log R))²`.

## The honest label

Every row is an INPUT to W9's assembly (the ratio `J ≪ x^{2−2σ}`), nothing here bears on twin
primes or on the crown's conditions. The `r`-sum on the right is `Σ'_r φ(r)/r² ≤ Σ'_r r⁻¹ = S'`
(`sum_rFilter_totient_div_sq_le`) — the SAME `S'` the detector's floor carries, so `φ(q)/q` cancels
in W9c without any upper bound on the coprime harmonic sum. `E(χ₀)` enters only through `‖E‖ ≤ 1`.
The constants `73`, `7/2 + 3|t|`, `2 + 3‖u‖` are the corpus's (Pólya–Vinogradov-free: ζ's growth
here is `norm_riemannZeta_le`'s partial-fraction bound), not Jutila's. The device's rectangle in
W9c takes `M ≤ z₁` (so the `M`-term is `0` on the detector's range) and `N ≥ 2x` (so `K(n/N) ≥ 1/4`
on `n ≤ x` — the Riesz kernel's own need, where Jutila's `e^{−n/N} ≥ e^{−1}` needs none).

## The measured receipts behind these statements (`h2c-desk/w9_receipts.py`)

The identity at `q = 5`, `R = 6` (`rFilter = {1, 2, 3, 6}`, `E = 4/5`, `Σ'φ(r)/r² = 1.527778`),
THREE WAYS — `B` as the finite sum, the residue block from `resKernel`'s closed form, `I(s)` as the
shifted contour with `L(u, χ₀) = ζ(u)(1 − 5^{−u})` and `ζ` by Hurwitz–Euler–Maclaurin:
`|B − residue − I| = 2.25·10⁻⁷` at `s = 0.3 + 0.7i`, `(N, M) = (40, 8)`; `2.36·10⁻⁸` at
`s = 0.01 + 2i`, `(60, 6)`; `1.07·10⁻⁷` at `s = 0` (the removable point; residue
`E·log 5·Σ' = 1.967091`); `1.01·10⁻⁷` at `s = 0.02`. `|K̃(−s)|·|s| ≤ 1.0255` on `Re s ∈ [0, 1/60]`
(attained at `s = 1/60` real; `1.000` as `s → 0`). At the helm's pass two instruments sharing
nothing with the desk's script confirmed the identity at thirteen further instances (`q = 7`,
`q = 12`, the removable point per `d`), all `≤ 1.3·10⁻⁷`.
`Σ_{r ≤ R} 2^{ω(r)} = 23, 359, 63869 ≤ R(1 + log R) = 33, 560, 102103` at `R = 10, 10², 10⁴`.
-/

open MeasureTheory Complex DirichletCharacter ArithmeticFunction

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-! ### Private helpers (executor-added, above every consumer) -/

/-- Four-factor monotonicity for nonnegative reals (the `mul5_le` of W7, one factor shorter). -/
private lemma mul4_le {a₁ a₂ b₁ b₂ c₁ c₂ e₁ e₂ : ℝ} (ha : 0 ≤ a₁) (hb : 0 ≤ b₁) (hc : 0 ≤ c₁)
    (he : 0 ≤ e₁) (h1 : a₁ ≤ a₂) (h2 : b₁ ≤ b₂) (h3 : c₁ ≤ c₂) (h4 : e₁ ≤ e₂) :
    a₁ * b₁ * c₁ * e₁ ≤ a₂ * b₂ * c₂ * e₂ := by
  have hab : a₁ * b₁ ≤ a₂ * b₂ := mul_le_mul h1 h2 hb (le_trans ha h1)
  have habc : a₁ * b₁ * c₁ ≤ a₂ * b₂ * c₂ :=
    mul_le_mul hab h3 hc (le_trans (mul_nonneg ha hb) hab)
  exact mul_le_mul habc h4 he (le_trans (mul_nonneg (mul_nonneg ha hb) hc) habc)

/-- The edge's kernel factor: for `0 < x ≤ B`, `1/x ≤ B`, `1 ≤ B` and `u ∈ [σ₀, c]`,
`x ^ u ≤ B ^ e` whenever `c ≤ e` and `|σ₀| ≤ e` — the four-way split on the sign of `u` and on
whether the base exceeds `1` (the negative-base discipline's positive half). -/
private lemma rpow_le_max_rpow {x B e u σ₀ c : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hxB : x ≤ B)
    (hxinvB : 1 / x ≤ B) (hu1 : σ₀ ≤ u) (hu2 : u ≤ c) (he1 : c ≤ e) (he2 : |σ₀| ≤ e) :
    x ^ u ≤ B ^ e := by
  have he0 : (0 : ℝ) ≤ e := le_trans (abs_nonneg σ₀) he2
  have hone : (1 : ℝ) ≤ B ^ e := by
    have h := Real.rpow_le_rpow_of_exponent_le hB he0
    rwa [Real.rpow_zero] at h
  rcases le_or_gt 1 x with hx1 | hx1
  · rcases le_or_gt 0 u with hu0 | hu0
    · calc x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx1 hu2
        _ ≤ B ^ c := Real.rpow_le_rpow hx.le hxB (le_trans hu0 hu2)
        _ ≤ B ^ e := Real.rpow_le_rpow_of_exponent_le hB he1
    · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 hu0.le) hone
  · rcases le_or_gt 0 u with hu0 | hu0
    · exact le_trans (Real.rpow_le_one hx.le hx1.le hu0) hone
    · have hσneg : σ₀ < 0 := lt_of_le_of_lt hu1 hu0
      have habs : |σ₀| = -σ₀ := abs_of_neg hσneg
      calc x ^ u ≤ x ^ σ₀ := Real.rpow_le_rpow_of_exponent_ge hx hx1.le hu1
        _ = (1 / x) ^ (-σ₀) := by
            rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]
        _ ≤ B ^ (-σ₀) := Real.rpow_le_rpow (by positivity) hxinvB (by linarith)
        _ ≤ B ^ e := Real.rpow_le_rpow_of_exponent_le hB (by rw [← habs]; exact he2)

/-- `dslope` of a product whose first factor vanishes at the base point. -/
private lemma dslope_mul_of_zero {f g : ℂ → ℂ} {a : ℂ} (hf : f a = 0)
    (hfd : DifferentiableAt ℂ f a) (hgd : DifferentiableAt ℂ g a) (b : ℂ) :
    dslope (fun w => f w * g w) a b = dslope f a b * g b := by
  rcases eq_or_ne b a with rfl | hb
  · rw [dslope_same, dslope_same]
    change deriv (f * g) b = deriv f b * g b
    rw [(hfd.hasDerivAt.mul hgd.hasDerivAt).deriv, hf]
    ring
  · rw [dslope_of_ne _ hb, dslope_of_ne _ hb, slope_def_field, slope_def_field, hf]
    ring

/-- Integrability of the Mellin integrand on a vertical line `Re w = c > 0` with `Re s ≥ 0`:
the `L`-factor is bounded on the line by its own absolutely convergent series (a constant), and
the cubic denominator supplies the decay. -/
private lemma integrable_trivChar_mellin_line (q : ℕ) [NeZero q] {X : ℝ} (hX : 0 < X) {s : ℂ}
    (hs : 0 ≤ s.re) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => 2 * ((X : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      * LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
        * ((c : ℂ) + (t : ℂ) * I + 2))) := by
  have hre : ∀ t : ℝ, (1 + s + ((c : ℂ) + (t : ℂ) * I)).re = 1 + s.re + c := by
    intro t
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
  have hrelt : ∀ t : ℝ, 1 < (1 + s + ((c : ℂ) + (t : ℂ) * I)).re := by
    intro t; rw [hre t]; linarith
  have hne1 : ∀ t : ℝ, (1 + s + ((c : ℂ) + (t : ℂ) * I)) ≠ 1 := by
    intro t hcon
    have h := hrelt t
    rw [hcon, Complex.one_re] at h
    linarith
  have hsum1 : Summable (fun n : ℕ => ‖LSeries.term
      (fun n : ℕ => ((1 : DirichletCharacter ℂ q) n)) (((1 + s.re + c : ℝ)) : ℂ) n‖) := by
    refine summable_norm_iff.mpr ?_
    refine DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ q) ?_
    simpa using (by linarith : (1 : ℝ) < 1 + s.re + c)
  have hC0 : (0 : ℝ) ≤ ∑' n : ℕ, ‖LSeries.term
      (fun n : ℕ => ((1 : DirichletCharacter ℂ q) n)) (((1 + s.re + c : ℝ)) : ℂ) n‖ :=
    tsum_nonneg (fun n => norm_nonneg _)
  have hLbound : ∀ t : ℝ, ‖LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((1 : DirichletCharacter ℂ q) n))
          (((1 + s.re + c : ℝ)) : ℂ) n‖ := by
    intro t
    have hsum2 : Summable (fun n : ℕ => ‖LSeries.term
        (fun n : ℕ => ((1 : DirichletCharacter ℂ q) n))
          (1 + s + ((c : ℂ) + (t : ℂ) * I)) n‖) := by
      refine summable_norm_iff.mpr ?_
      exact DirichletCharacter.LSeriesSummable_of_one_lt_re _ (hrelt t)
    rw [LFunctionTrivChar, LFunction_eq_LSeries _ (hrelt t), LSeries]
    refine (norm_tsum_le_tsum_norm hsum2).trans (le_of_eq ?_)
    refine tsum_congr (fun n => ?_)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre t, Complex.ofReal_re]
  have hXc : ((X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hwc : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) := by fun_prop
  have hLcont : Continuous
      (fun t : ℝ => LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))) := by
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have h1 : ContinuousAt (LFunctionTrivChar q) (1 + s + ((c : ℂ) + (t : ℂ) * I)) :=
      (DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl (hne1 t))).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => 1 + s + ((c : ℂ) + (t : ℂ) * I)) t := by fun_prop
    have h3 : ContinuousAt (LFunctionTrivChar q ∘ fun t : ℝ =>
        1 + s + ((c : ℂ) + (t : ℂ) * I)) t := ContinuousAt.comp h1 h2
    exact h3
  have hdne : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
      * ((c : ℂ) + (t : ℂ) * I + 2) ≠ 0 :=
    fun t => mul_ne_zero (mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)) (s2_ne_zero hc t)
  have hcont : Continuous (fun t : ℝ => 2 * ((X : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      * LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
        * ((c : ℂ) + (t : ℂ) * I + 2))) := by
    refine Continuous.div ?_ ?_ hdne
    · exact (continuous_const.mul (Continuous.const_cpow hwc (Or.inl hXc))).mul hLcont
    · exact (hwc.mul (hwc.add continuous_const)).mul (hwc.add continuous_const)
  refine ((integrable_inv_sq_add_sq_rpow hc).const_mul
    (2 * X ^ c * ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => ((1 : DirichletCharacter ℂ q) n))
      (((1 + s.re + c : ℝ)) : ℂ) n‖)).mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hXc0 : (0 : ℝ) ≤ X ^ c := Real.rpow_nonneg hX.le c
  have hnormeq : ‖2 * ((X : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      * LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
        * ((c : ℂ) + (t : ℂ) * I + 2))‖
      = 2 * X ^ c * ‖LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))‖
        * ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
          * ((c : ℂ) + (t : ℂ) * I + 2))⁻¹‖ := by
    rw [norm_div, norm_mul, norm_mul, norm_ofReal_cpow_vert hX.le hc t, norm_inv,
      (by norm_num : ‖(2 : ℂ)‖ = 2)]
    ring
  rw [hnormeq]
  refine mul_le_mul ?_ (norm_inv_denom2_cubic_le hc t) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hXc0) hC0)
  exact mul_le_mul_of_nonneg_left (hLbound t) (mul_nonneg (by norm_num) hXc0)

/-! ## The objects -/

/-- Jutila's (3.3) weight in the Riesz form: `b_n = n⁻¹(Σ'_r r⁻¹ψ_r(n))²(K(n/N) − K(n/M))`,
`b_0 = 0`. -/
def jutilaB (q : ℕ) (R N M : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (n : ℝ)⁻¹ * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
      * ((max 0 (1 - (n : ℝ) / N)) ^ 2 - (max 0 (1 - (n : ℝ) / M)) ^ 2)

/-- The kernel difference `2((N)^w − (M)^w)/((w + 1)(w + 2))`, vanishing at `w = 0`. -/
def resKernelFun (N M : ℝ) (w : ℂ) : ℂ :=
  2 * ((N : ℂ) ^ w - (M : ℂ) ^ w) / ((w + 1) * (w + 2))

/-- The residue kernel `K̃(−s)·(N^{−s} − M^{−s})` with its removable point filled:
`resKernel s N M = dslope (resKernelFun N M) 0 (−s)` — `= 2(N^{−s} − M^{−s})/((−s)(1 − s)(2 − s))`
for `s ≠ 0`, `= log(N/M)` at `s = 0`. -/
def resKernel (s : ℂ) (N M : ℝ) : ℂ := dslope (resKernelFun N M) 0 (-s)

/-- The holomorphic function of the contour node (W7's `jutilaPhi` with the entire
`LFunctionTrivChar₁` in place of `L(·, χ)` and the kernel DIFFERENCE in place of `x^w`):
`ψ(w) = 2((N/d)^w − (M/d)^w)·LFunctionTrivChar₁ q (1 + s + w)/((w + 1)(w + 2))`; `ψ(0) = 0`. -/
def resPhi (q : ℕ) [NeZero q] (N M : ℝ) (d : ℕ) (s w : ℂ) : ℂ :=
  resKernelFun (N / d) (M / d) w * LFunctionTrivChar₁ q (1 + s + w)

/-- The vertical integrand of the `(d, s)`-term:
`G(w) = 2((N/d)^w − (M/d)^w)·L(1 + s + w, χ₀)/(w(w + 1)(w + 2))`. -/
def resIntegrand (q : ℕ) [NeZero q] (N M : ℝ) (d : ℕ) (s w : ℂ) : ℂ :=
  2 * (((N / d : ℝ) : ℂ) ^ w - ((M / d : ℝ) : ℂ) ^ w) * LFunctionTrivChar q (1 + s + w)
    / (w * (w + 1) * (w + 2))

/-- `I(s; N, M)`: the `(r, r', d)`-sum of the shifted integrals on `Re(1 + s + w) = 1/2`. -/
def jutilaI (q : ℕ) [NeZero q] (R N M : ℝ) (s : ℂ) : ℂ :=
  ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
    * ∑ d ∈ (r * r').divisors, (hCoef selbergPsi r r' d : ℂ) * (d : ℂ) ^ (-(1 : ℂ) - s)
      * ((1 / (2 * Real.pi)) • ∫ t : ℝ,
          resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I))

/-! ## (i) The weight -/

theorem jutilaB_zero (q : ℕ) (R N M : ℝ) : jutilaB q R N M 0 = 0 := by
  simp [jutilaB]

/-- The inline real kernel IS `kern2`, cast once: the row the expansion reads before any `tsum`. -/
theorem jutilaB_ofReal_eq (q : ℕ) (R N M : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (jutilaB q R N M n : ℂ)
      = (n : ℂ)⁻¹ * ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n : ℝ) : ℂ) ^ 2
          * (kern2 ((n : ℝ) / N) - kern2 ((n : ℝ) / M)) := by
  simp only [jutilaB, if_neg hn, kern2]
  push_cast
  ring

theorem jutilaB_nonneg {N M : ℝ} (hM : 0 < M) (hMN : M ≤ N) (q : ℕ) (R : ℝ) (n : ℕ) :
    0 ≤ jutilaB q R N M n := by
  simp only [jutilaB]
  split_ifs with h
  · exact le_rfl
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hdiv : (n : ℝ) / N ≤ (n : ℝ) / M := div_le_div_of_nonneg_left hn0 hM hMN
    have hmax : max 0 (1 - (n : ℝ) / M) ≤ max 0 (1 - (n : ℝ) / N) :=
      max_le_max le_rfl (by linarith)
    have hsq : (max 0 (1 - (n : ℝ) / M)) ^ 2 ≤ (max 0 (1 - (n : ℝ) / N)) ^ 2 :=
      pow_le_pow_left₀ (le_max_left _ _) hmax 2
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hn0) (sq_nonneg _)) (by linarith)

theorem jutilaB_eq_zero_of_le {N M : ℝ} (hM : 0 < M) (hMN : M ≤ N) (q : ℕ) (R : ℝ) {n : ℕ}
    (hn : N ≤ n) : jutilaB q R N M n = 0 := by
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hM hMN
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hN hn
  have hnpos : 0 < n := by exact_mod_cast hn0
  have h1 : (1 : ℝ) ≤ (n : ℝ) / N := (one_le_div hN).mpr hn
  have h2 : (1 : ℝ) ≤ (n : ℝ) / M := (one_le_div hM).mpr (le_trans hMN hn)
  simp only [jutilaB, if_neg hnpos.ne',
    max_eq_left (by linarith : (1 : ℝ) - (n : ℝ) / N ≤ 0),
    max_eq_left (by linarith : (1 : ℝ) - (n : ℝ) / M ≤ 0)]
  ring

/-- On `n ≥ M` the `M`-term vanishes: `b_n = n⁻¹(Σ')²·K(n/N)`. -/
theorem jutilaB_eq_of_le {N M : ℝ} (hM : 0 < M) (q : ℕ) (R : ℝ) {n : ℕ} (hn : M ≤ n) :
    jutilaB q R N M n
      = (n : ℝ)⁻¹ * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
          * (max 0 (1 - (n : ℝ) / N)) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hM hn
  have hnpos : 0 < n := by exact_mod_cast hn0
  have h2 : (1 : ℝ) ≤ (n : ℝ) / M := (one_le_div hM).mpr hn
  simp only [jutilaB, if_neg hnpos.ne',
    max_eq_left (by linarith : (1 : ℝ) - (n : ℝ) / M ≤ 0)]
  ring

theorem jutilaB_pos {N M : ℝ} (hM : 0 < M) (q : ℕ) (R : ℝ) {n : ℕ} (hn : M ≤ n) (hnN : (n : ℝ) < N)
    (hS : ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n ≠ 0) :
    0 < jutilaB q R N M n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hM hn
  have hNpos : (0 : ℝ) < N := lt_trans hn0 hnN
  have hlt : (n : ℝ) / N < 1 := (div_lt_one hNpos).mpr hnN
  rw [jutilaB_eq_of_le hM q R hn, max_eq_right (by linarith : (0 : ℝ) ≤ 1 - (n : ℝ) / N)]
  have hsq : 0 < (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hS) 2
  exact mul_pos (mul_pos (inv_pos.mpr hn0) hsq) (pow_pos (by linarith) 2)

/-! ## (ii) The residue kernel -/

theorem resKernelFun_zero (N M : ℝ) : resKernelFun N M 0 = 0 := by
  simp [resKernelFun]

theorem resKernel_of_ne_zero {s : ℂ} (hs : s ≠ 0) (N M : ℝ) :
    resKernel s N M = 2 * ((N : ℂ) ^ (-s) - (M : ℂ) ^ (-s)) / ((-s) * (1 - s) * (2 - s)) := by
  have hns : (-s) ≠ 0 := neg_ne_zero.mpr hs
  have hden : ((-s) + 1) * ((-s) + 2) * (-s) = (-s) * (1 - s) * (2 - s) := by ring
  simp only [resKernel]
  rw [dslope_of_ne _ hns, slope_def_field, resKernelFun_zero, sub_zero, sub_zero]
  simp only [resKernelFun]
  rw [div_div, hden]

theorem resKernel_zero {N M : ℝ} (hM : 0 < M) (hN : 0 < N) :
    resKernel 0 N M = (Real.log (N / M) : ℂ) := by
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hMc : ((M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  have hg : HasDerivAt (fun w : ℂ => 2 * (((N : ℝ) : ℂ) ^ w - ((M : ℝ) : ℂ) ^ w))
      (2 * (Complex.log ((N : ℝ) : ℂ) - Complex.log ((M : ℝ) : ℂ))) 0 := by
    have h1 := (Complex.hasStrictDerivAt_const_cpow (x := ((N : ℝ) : ℂ)) (y := (0 : ℂ))
      (Or.inl hNc)).hasDerivAt
    have h2 := (Complex.hasStrictDerivAt_const_cpow (x := ((M : ℝ) : ℂ)) (y := (0 : ℂ))
      (Or.inl hMc)).hasDerivAt
    simpa using (h1.sub h2).const_mul (2 : ℂ)
  have hh : HasDerivAt (fun w : ℂ => (w + 1) * (w + 2)) 3 0 := by
    have h1 : HasDerivAt (fun w : ℂ => w + 1) 1 0 := (hasDerivAt_id (0 : ℂ)).add_const 1
    have h2 : HasDerivAt (fun w : ℂ => w + 2) 1 0 := (hasDerivAt_id (0 : ℂ)).add_const 2
    have h3 : (1 : ℂ) * ((0 : ℂ) + 2) + ((0 : ℂ) + 1) * 1 = 3 := by norm_num
    rw [← h3]
    exact h1.mul h2
  have hne : ((0 : ℂ) + 1) * ((0 : ℂ) + 2) ≠ 0 := by norm_num
  have hd : HasDerivAt (resKernelFun N M)
      (Complex.log ((N : ℝ) : ℂ) - Complex.log ((M : ℝ) : ℂ)) 0 := by
    have heq : (2 * (Complex.log ((N : ℝ) : ℂ) - Complex.log ((M : ℝ) : ℂ))
          * (((0 : ℂ) + 1) * ((0 : ℂ) + 2))
          - 2 * (((N : ℝ) : ℂ) ^ (0 : ℂ) - ((M : ℝ) : ℂ) ^ (0 : ℂ)) * 3)
        / (((0 : ℂ) + 1) * ((0 : ℂ) + 2)) ^ 2
        = Complex.log ((N : ℝ) : ℂ) - Complex.log ((M : ℝ) : ℂ) := by
      rw [Complex.cpow_zero, Complex.cpow_zero]
      ring
    rw [← heq]
    exact hg.div hh hne
  simp only [resKernel]
  rw [neg_zero, dslope_same, hd.deriv, Real.log_div hN.ne' hM.ne',
    Complex.ofReal_sub, Complex.ofReal_log hN.le, Complex.ofReal_log hM.le]

/-- The off-diagonal shape: `‖resKernel s N M‖ ≤ 1.0255·2/‖s‖` on `0 ≤ Re s ≤ 1/60`, `1 ≤ M ≤ N`. -/
theorem norm_resKernel_le_div {s : ℂ} (hs' : s ≠ 0) (hs0 : 0 ≤ s.re) (hs : s.re ≤ 1 / 60) {N M : ℝ}
    (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖resKernel s N M‖ ≤ 2 / ((59 / 60) * (119 / 60)) * (2 / ‖s‖) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN : (1 : ℝ) ≤ N := le_trans hM hMN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hspos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hs'
  have hsne : ‖s‖ ≠ 0 := hspos.ne'
  have hNn : ‖((N : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by rw [Complex.neg_re]; linarith)
  have hMn : ‖((M : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hM0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hM (by rw [Complex.neg_re]; linarith)
  have hnum : ‖((N : ℝ) : ℂ) ^ (-s) - ((M : ℝ) : ℂ) ^ (-s)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hd1 : (59 : ℝ) / 60 ≤ ‖(1 : ℂ) - s‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - s)
    rw [show ((1 : ℂ) - s).re = 1 - s.re by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s.re)] at h
    linarith
  have hd2 : (119 : ℝ) / 60 ≤ ‖(2 : ℂ) - s‖ := by
    have h := Complex.abs_re_le_norm ((2 : ℂ) - s)
    rw [show ((2 : ℂ) - s).re = 2 - s.re by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - s.re)] at h
    linarith
  have hD : (0 : ℝ) < ‖s‖ * ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖ := by
    have h1 : (0 : ℝ) < ‖(1 : ℂ) - s‖ := by linarith
    have h2 : (0 : ℝ) < ‖(2 : ℂ) - s‖ := by linarith
    positivity
  have hprod : (59 / 60 : ℝ) * (119 / 60) ≤ ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖ :=
    mul_le_mul hd1 hd2 (by norm_num) (by linarith)
  have hden : (59 / 60 : ℝ) * (119 / 60) * ‖s‖ ≤ ‖s‖ * ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖ := by
    have h2 := mul_le_mul_of_nonneg_right hprod hspos.le
    linarith
  have hR0 : (0 : ℝ) ≤ 2 / ((59 / 60 : ℝ) * (119 / 60)) * (2 / ‖s‖) := by positivity
  have hkey : 2 / ((59 / 60 : ℝ) * (119 / 60)) * (2 / ‖s‖) * ((59 / 60) * (119 / 60) * ‖s‖)
      = 4 := by
    field_simp
    norm_num
  have hstep : (4 : ℝ) ≤ 2 / ((59 / 60 : ℝ) * (119 / 60)) * (2 / ‖s‖)
      * (‖s‖ * ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖) := by
    have h := mul_le_mul_of_nonneg_left hden hR0
    linarith [hkey]
  rw [resKernel_of_ne_zero hs' N M, norm_div]
  simp only [norm_mul, norm_neg]
  rw [(by norm_num : ‖(2 : ℂ)‖ = 2), div_le_iff₀ hD]
  linarith [hnum, hstep]

/-- The diagonal shape (real `s ≥ 0`): `‖resKernel s N M‖ ≤ 1.0255·log(N/M)`. -/
theorem norm_resKernel_le_log {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 60) {N M : ℝ} (hM : 1 ≤ M)
    (hMN : M ≤ N) :
    ‖resKernel (s : ℂ) N M‖ ≤ 2 / ((59 / 60) * (119 / 60)) * Real.log (N / M) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN : (1 : ℝ) ≤ N := le_trans hM hMN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hL : 0 ≤ Real.log (N / M) := Real.log_nonneg ((one_le_div hM0).mpr hMN)
  have hd1 : (59 : ℝ) / 60 ≤ ‖(1 : ℂ) - ((s : ℝ) : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - ((s : ℝ) : ℂ))
    rw [show ((1 : ℂ) - ((s : ℝ) : ℂ)).re = 1 - s by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)] at h
    linarith
  have hd2 : (119 : ℝ) / 60 ≤ ‖(2 : ℂ) - ((s : ℝ) : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((2 : ℂ) - ((s : ℝ) : ℂ))
    rw [show ((2 : ℂ) - ((s : ℝ) : ℂ)).re = 2 - s by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - s)] at h
    linarith
  rcases eq_or_lt_of_le hs0 with hzero | hpos
  · rw [← hzero, Complex.ofReal_zero, resKernel_zero hM0 hN0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hL]
    linarith
  · have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hMa : 0 ≤ Real.log M := Real.log_nonneg hM
    have hLab : Real.log (N / M) = Real.log N - Real.log M := Real.log_div hN0.ne' hM0.ne'
    have hexp : Real.exp (Real.log M * (-s)) - Real.exp (Real.log N * (-s))
        = Real.exp (Real.log M * (-s)) * (1 - Real.exp (-(s * Real.log (N / M)))) := by
      have hlin : Real.log N * (-s) = Real.log M * (-s) + -(s * Real.log (N / M)) := by
        rw [hLab]; ring
      rw [mul_one_sub, ← Real.exp_add, ← hlin]
    have hb1 : Real.exp (Real.log M * (-s)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [hMa, hs0]
    have hb2 : 1 - Real.exp (-(s * Real.log (N / M))) ≤ s * Real.log (N / M) := by
      have h := Real.add_one_le_exp (-(s * Real.log (N / M)))
      linarith
    have hb3 : 0 ≤ 1 - Real.exp (-(s * Real.log (N / M))) := by
      have h : Real.exp (-(s * Real.log (N / M))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [hL, hs0]
      linarith
    have hkey : M ^ (-s) - N ^ (-s) ≤ s * Real.log (N / M) := by
      rw [Real.rpow_def_of_pos hM0, Real.rpow_def_of_pos hN0, hexp]
      calc Real.exp (Real.log M * (-s)) * (1 - Real.exp (-(s * Real.log (N / M))))
          ≤ 1 * (1 - Real.exp (-(s * Real.log (N / M)))) :=
            mul_le_mul_of_nonneg_right hb1 hb3
        _ ≤ s * Real.log (N / M) := by rw [one_mul]; exact hb2
    have hge : 0 ≤ M ^ (-s) - N ^ (-s) := by
      rw [Real.rpow_def_of_pos hM0, Real.rpow_def_of_pos hN0, hexp]
      exact mul_nonneg (Real.exp_pos _).le hb3
    have hcastN : ((N : ℝ) : ℂ) ^ (-((s : ℝ) : ℂ)) = ((N ^ (-s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hN0.le]
    have hcastM : ((M : ℝ) : ℂ) ^ (-((s : ℝ) : ℂ)) = ((M ^ (-s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hM0.le]
    have hnumnorm : ‖((N : ℝ) : ℂ) ^ (-((s : ℝ) : ℂ)) - ((M : ℝ) : ℂ) ^ (-((s : ℝ) : ℂ))‖
        = M ^ (-s) - N ^ (-s) := by
      rw [hcastN, hcastM, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have hsnorm : ‖((s : ℝ) : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    have hD : (0 : ℝ) < s * ‖(1 : ℂ) - ((s : ℝ) : ℂ)‖ * ‖(2 : ℂ) - ((s : ℝ) : ℂ)‖ := by
      have h1 : (0 : ℝ) < ‖(1 : ℂ) - ((s : ℝ) : ℂ)‖ := by linarith
      have h2 : (0 : ℝ) < ‖(2 : ℂ) - ((s : ℝ) : ℂ)‖ := by linarith
      positivity
    have hprod : (59 / 60 : ℝ) * (119 / 60)
        ≤ ‖(1 : ℂ) - ((s : ℝ) : ℂ)‖ * ‖(2 : ℂ) - ((s : ℝ) : ℂ)‖ :=
      mul_le_mul hd1 hd2 (by norm_num) (by linarith)
    have hDlow : s * ((59 : ℝ) / 60) * (119 / 60)
        ≤ s * ‖(1 : ℂ) - ((s : ℝ) : ℂ)‖ * ‖(2 : ℂ) - ((s : ℝ) : ℂ)‖ := by
      have h := mul_le_mul_of_nonneg_left hprod hpos.le
      linarith
    have hKL0 : (0 : ℝ) ≤ 2 / ((59 / 60 : ℝ) * (119 / 60)) * Real.log (N / M) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hDlow hKL0
    have hval : 2 / ((59 / 60 : ℝ) * (119 / 60)) * Real.log (N / M)
        * (s * ((59 : ℝ) / 60) * (119 / 60)) = 2 * (s * Real.log (N / M)) := by
      ring
    rw [resKernel_of_ne_zero hsne N M, norm_div]
    simp only [norm_mul, norm_neg]
    rw [(by norm_num : ‖(2 : ℂ)‖ = 2), hnumnorm, hsnorm, div_le_iff₀ hD]
    linarith [hkey, hmul, hval]

/-- The `d`-collapse: `d^{−1−s}·resKernel s (N/d) (M/d) = d⁻¹·resKernel s N M`. -/
theorem cpow_mul_resKernel_div {d : ℕ} (hd : 0 < d) {N M : ℝ} (hM : 0 < M) (hN : 0 < N) (s : ℂ) :
    (d : ℂ) ^ (-(1 : ℂ) - s) * resKernel s (N / d) (M / d) = (d : ℂ)⁻¹ * resKernel s N M := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : ((d : ℝ)) ≠ 0 := hd0.ne'
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM hd0
  have hone : (d : ℂ) ^ (-(1 : ℂ)) = (d : ℂ)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_one]
  have hdcR : (((d : ℝ)) : ℂ) = (d : ℂ) := by push_cast; ring
  rcases eq_or_ne s 0 with rfl | hs
  · have hNM : (N / (d : ℝ)) / (M / (d : ℝ)) = N / M := by
      rw [div_div_div_comm, div_self hdne, div_one]
    rw [show (-(1 : ℂ) - 0) = -(1 : ℂ) by ring, hone, resKernel_zero hMd hNd,
      resKernel_zero hM hN, hNM]
  · have hNsplit : ((N : ℝ) : ℂ) ^ (-s)
        = ((N / (d : ℝ) : ℝ) : ℂ) ^ (-s) * (((d : ℝ)) : ℂ) ^ (-s) := by
      have hprod : ((N / (d : ℝ) : ℝ) : ℂ) * (((d : ℝ)) : ℂ) = ((N : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      rw [← Complex.mul_cpow_ofReal_nonneg hNd.le hd0.le, hprod]
    have hMsplit : ((M : ℝ) : ℂ) ^ (-s)
        = ((M / (d : ℝ) : ℝ) : ℂ) ^ (-s) * (((d : ℝ)) : ℂ) ^ (-s) := by
      have hprod : ((M / (d : ℝ) : ℝ) : ℂ) * (((d : ℝ)) : ℂ) = ((M : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      rw [← Complex.mul_cpow_ofReal_nonneg hMd.le hd0.le, hprod]
    have hDsplit : (d : ℂ) ^ (-(1 : ℂ) - s) = (d : ℂ)⁻¹ * (((d : ℝ)) : ℂ) ^ (-s) := by
      rw [hdcR, ← hone, ← Complex.cpow_add _ _ hdc]
      congr 1
    rw [resKernel_of_ne_zero hs, resKernel_of_ne_zero hs, hNsplit, hMsplit, hDsplit]
    ring

/-! ## (iii) The trivial character's growth on `Re ≥ 1/2` -/

theorem two_pow_card_primeFactors_le {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℝ) ^ q.primeFactors.card ≤ q := by
  have hle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hleR : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  have h2 : (2 : ℝ) ^ q.primeFactors.card ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  linarith

/-- `‖L(u, χ₀)‖ ≤ q·‖ζ(u)‖` on `Re u ≥ 0`, `u ≠ 1` (`|1 − p^{−u}| ≤ 2`, `2^{ω(q)} ≤ q`). -/
theorem norm_LFunctionTrivChar_le (q : ℕ) [NeZero q] {u : ℂ} (hu : 0 ≤ u.re) (hu1 : u ≠ 1) :
    ‖LFunctionTrivChar q u‖ ≤ (q : ℝ) * ‖riemannZeta u‖ := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rw [LFunctionTrivChar_eq_mul_riemannZeta hu1, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans ?_ (two_pow_card_primeFactors_le hq1)
  rw [Complex.norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
  have hpn : ‖((p : ℕ) : ℂ) ^ (-u)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by rw [Complex.neg_re]; linarith)
  calc ‖(1 : ℂ) - ((p : ℕ) : ℂ) ^ (-u)‖ ≤ ‖(1 : ℂ)‖ + ‖((p : ℕ) : ℂ) ^ (-u)‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-- `norm_riemannZeta_le` on `Re u ≥ 1/2` away from `1`: `‖ζ u‖ ≤ 2 + 3‖u‖` when `‖u − 1‖ ≥ 1/2`. -/
theorem norm_riemannZeta_le_of_half_le {u : ℂ} (hu : 1 / 2 ≤ u.re) (hu1 : 1 / 2 ≤ ‖u - 1‖) :
    ‖riemannZeta u‖ ≤ 2 + 3 * ‖u‖ := by
  have hre : (0 : ℝ) < u.re := by linarith
  have hnpos : (0 : ℝ) < ‖u - 1‖ := by linarith
  have hne : u ≠ 1 := by
    intro hcon
    rw [hcon] at hnpos
    simp at hnpos
  have h := norm_riemannZeta_le hre hne
  have hinv1 : 1 / ‖u - 1‖ ≤ 2 := by
    rw [div_le_iff₀ hnpos]; linarith
  have hinv2 : 1 / u.re ≤ 2 := by
    rw [div_le_iff₀ hre]; linarith
  have hexp : (1 + ‖u - 1‖ * (‖u‖ * (1 + 1 / u.re))) / ‖u - 1‖
      = 1 / ‖u - 1‖ + ‖u‖ * (1 + 1 / u.re) := by
    field_simp
  rw [hexp] at h
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  nlinarith [h, hinv1, hinv2, hu0, mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 2 - 1 / u.re)]

/-- On the critical line: `‖ζ(1/2 + it)‖ ≤ 7/2 + 3|t|` (design v2 F5). -/
theorem norm_riemannZeta_half_le (t : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 7 / 2 + 3 * |t| := by
  have hre : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 := by simp
  have hsub : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - 1).re = -(1 / 2 : ℝ) := by
    rw [Complex.sub_re, hre, Complex.one_re]; norm_num
  have h1 : (1 : ℝ) / 2 ≤ ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - 1‖ := by
    have h := Complex.abs_re_le_norm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - 1)
    rw [hsub, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    linarith
  have h2 : ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ 1 / 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h3 := norm_riemannZeta_le_of_half_le hre.ge h1
  linarith

theorem norm_prod_one_sub_inv_le_one (q : ℕ) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤ 1 := by
  rw [Complex.norm_prod]
  refine Finset.prod_le_one (fun p _ => norm_nonneg _) (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    have h := (div_le_one hppos).mpr hp1
    simpa using h
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hcast : (1 : ℂ) - ((p : ℕ) : ℂ)⁻¹ = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-! ## (iv) The Mellin representation of the `m`-series -/

theorem summable_trivChar_kern2 (q : ℕ) [NeZero q] {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d)
    {s : ℂ} (hs : 0 ≤ s.re) {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℕ => ‖((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)‖
      * (N / d / m) ^ c) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hre : 1 < (((1 + s.re + c : ℝ)) : ℂ).re := by
    simpa using (by linarith : (1 : ℝ) < 1 + s.re + c)
  have hLS : LSeriesSummable (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m))
      (((1 + s.re + c : ℝ)) : ℂ) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ q) hre
  have hnorm : Summable (fun m : ℕ => ‖LSeries.term
      (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m)) (((1 + s.re + c : ℝ)) : ℂ) m‖) :=
    summable_norm_iff.mpr hLS
  have hEq : (fun m : ℕ => ‖((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)‖
        * (N / d / m) ^ c)
      = fun m : ℕ => (N / (d : ℝ)) ^ c * ‖LSeries.term
        (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m)) (((1 + s.re + c : ℝ)) : ℂ) m‖ := by
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [Real.zero_rpow hc.ne']
    · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hre2 : (-(1 : ℂ) - s).re = -(1 + s.re) := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
      rw [LSeries.norm_term_eq, if_neg hm, Complex.ofReal_re,
        Real.div_rpow hx.le (Nat.cast_nonneg m), norm_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm), hre2,
        Real.rpow_neg hm0.le]
      simp only [Real.rpow_add hm0, Real.rpow_one]
      field_simp
  rw [hEq]
  exact hnorm.mul_left ((N / (d : ℝ)) ^ c)

/-- The `d`-factor leaves the `m`-series:
`Σ'_m χ₀(m)(dm)^{−1−s}F(m) = d^{−1−s}·Σ'_m χ₀(m)m^{−1−s}F(m)` (`Nat.cast_mul`,
`mul_cpow_ofReal_nonneg`, `tsum_mul_left`) — the step the design v1 skipped and the verdict's
kill 1 found missing. -/
theorem tsum_trivChar_mul_cpow_eq (q : ℕ) [NeZero q] {d : ℕ} (hd : 0 < d) (s : ℂ) (F : ℕ → ℂ) :
    ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * F m
      = (d : ℂ) ^ (-(1 : ℂ) - s)
        * ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * F m := by
  have hsplit : ∀ m : ℕ, ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
      = (d : ℂ) ^ (-(1 : ℂ) - s) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) := by
    intro m
    have h1 : ((d * m : ℕ) : ℂ) = (((d : ℝ)) : ℂ) * (((m : ℝ)) : ℂ) := by push_cast; ring
    rw [h1, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m),
      Complex.ofReal_natCast, Complex.ofReal_natCast]
  have hd0 : (0 : ℕ) < d := hd
  calc ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * F m
      = ∑' m : ℕ, (d : ℂ) ^ (-(1 : ℂ) - s)
          * (((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * F m) := by
        refine tsum_congr (fun m => ?_)
        rw [hsplit m]; ring
    _ = (d : ℂ) ^ (-(1 : ℂ) - s) * ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m)
          * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * F m := tsum_mul_left

/-- The single-kernel Mellin form: `Σ'_m χ₀(m) m^{−1−s} K(dm/N)
= (1/2π)∫ 2(N/d)^{c+it} L(1 + s + c + it, χ₀)/((c+it)(c+it+1)(c+it+2)) dt` — the `m`-series with
the `d^{−1−s}` OUTSIDE (the verdict's kill 1: with `(dm)^{−1−s}` on the left the row is false by
exactly `d^{−1−s}` for every `d ≥ 2`; LHS/RHS = 1/2, 1/3, 1/5 at `d = 2, 3, 5`, two independent
quadratures). -/
theorem tsum_trivChar_kern2_eq_integral (q : ℕ) [NeZero q] {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d)
    {s : ℂ} (hs : 0 ≤ s.re) {c : ℝ} (hc : 0 < c) :
    ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * kern2 ((d * m : ℝ) / N)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          2 * ((N / d : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
            * LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))
            / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hsne : -(1 : ℂ) - s ≠ 0 := by
    intro hcon
    have hre0 : (-(1 : ℂ) - s).re = 0 := by rw [hcon]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re] at hre0
    linarith
  have hsum := summable_trivChar_kern2 q hN hd hs hc
  have hswap := kernel_sum_swap_2
    (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)) hx hc hsum
  have hIntEq : (∫ t : ℝ, 2 * ((N / d : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        * LFunctionTrivChar q (1 + s + ((c : ℂ) + (t : ℂ) * I))
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
          * ((c : ℂ) + (t : ℂ) * I + 2)))
      = ∫ t : ℝ, 2 * (∑' m : ℕ, (((1 : DirichletCharacter ℂ q) m)
            * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)) * ((N / d / m : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    have hw : ((c : ℂ) + (t : ℂ) * I) ≠ 0 := s_ne_zero hc t
    have hre : 1 < (1 + s + ((c : ℂ) + (t : ℂ) * I)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero]
      linarith
    rw [riesz_tsum_eq (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m)
      * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)) hx.le hw]
    have hfun : (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s))
        = fun m : ℕ => ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-((1 : ℂ) + s)) := by
      funext m
      congr 2
      ring
    rw [hfun, LSeries_mul_natCast_cpow_neg, ← LFunction_eq_LSeries _ hre]
    ring
  rw [hIntEq, ← hswap, Complex.real_smul, ← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [Complex.zero_cpow hsne]
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have hy : (0 : ℝ) < N / (d : ℝ) / (m : ℝ) := div_pos hx hmR
    have hyy : (m : ℝ) / (N / (d : ℝ)) = ((d : ℝ) * (m : ℝ)) / N := by
      rw [div_div_eq_mul_div]; ring
    have hpull : (∫ t : ℝ, 2 * (((1 : DirichletCharacter ℂ q) m)
          * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)) * ((N / d / m : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2)))
        = (((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s))
          * ∫ t : ℝ, 2 * ((N / d / m : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      ring
    have hker := kernel_identity_2 hy hc
    rw [← kern2_value hy, one_div_div, hyy] at hker
    rw [hpull, ← hker, Complex.real_smul]
    ring

/-- The difference of the two kernels: the `m`-series (with `m^{−1−s}`, the `d^{−1−s}` outside)
against `K(dm/N) − K(dm/M)` is the Mellin integral of `resIntegrand` on `Re w = c`. The receipt is
the `d = 2` instance — a `d = 1` check passes the wrong row. -/
theorem tsum_trivChar_kern2_diff_eq_integral (q : ℕ) [NeZero q] {N M : ℝ} (hM : 0 < M) (hN : 0 < N)
    {d : ℕ} (hd : 0 < d) {s : ℂ} (hs : 0 ≤ s.re) {c : ℝ} (hc : 0 < c) :
    ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * (kern2 ((d * m : ℝ) / N) - kern2 ((d * m : ℝ) / M))
      = (1 / (2 * Real.pi)) • ∫ t : ℝ, resIntegrand q N M d s ((c : ℂ) + (t : ℂ) * I) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM hd0
  have hvanish : ∀ X : ℝ, 0 < X → ∀ m : ℕ, ⌈X⌉₊ < m →
      ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * kern2 (((d : ℝ) * (m : ℝ)) / X) = 0 := by
    intro X hX m hm
    have h1 : X ≤ ((⌈X⌉₊ : ℕ) : ℝ) := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hmX : X ≤ (d : ℝ) * (m : ℝ) := by nlinarith
    have hy : (1 : ℝ) ≤ ((d : ℝ) * (m : ℝ)) / X := (one_le_div hX).mpr hmX
    have hk : kern2 (((d : ℝ) * (m : ℝ)) / X) = 0 := by
      simp only [kern2, max_eq_left (by linarith : (1 : ℝ) - ((d : ℝ) * (m : ℝ)) / X ≤ 0)]
      norm_num
    rw [hk, mul_zero]
  have hsN : Summable (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m)
      * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * kern2 (((d : ℝ) * (m : ℝ)) / N)) :=
    summable_of_ne_finset_zero (s := Finset.range (⌈N⌉₊ + 1))
      (fun m hm => hvanish N hN m (by simpa [Nat.lt_succ_iff] using hm))
  have hsM : Summable (fun m : ℕ => ((1 : DirichletCharacter ℂ q) m)
      * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s) * kern2 (((d : ℝ) * (m : ℝ)) / M)) :=
    summable_of_ne_finset_zero (s := Finset.range (⌈M⌉₊ + 1))
      (fun m hm => hvanish M hM m (by simpa [Nat.lt_succ_iff] using hm))
  have hsplit : (∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * (kern2 (((d : ℝ) * (m : ℝ)) / N) - kern2 (((d : ℝ) * (m : ℝ)) / M)))
      = (∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
          * kern2 (((d : ℝ) * (m : ℝ)) / N))
        - ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
          * kern2 (((d : ℝ) * (m : ℝ)) / M) := by
    rw [← hsN.tsum_sub hsM]
    exact tsum_congr (fun m => by ring)
  have hIN := integrable_trivChar_mellin_line q hNd hs hc
  have hIM := integrable_trivChar_mellin_line q hMd hs hc
  rw [hsplit, tsum_trivChar_kern2_eq_integral q hN hd hs hc,
    tsum_trivChar_kern2_eq_integral q hM hd hs hc, ← smul_sub,
    ← MeasureTheory.integral_sub hIN hIM]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [resIntegrand]
  ring

/-! ## (v) The contour node -/

theorem resPhi_differentiableOn (q : ℕ) [NeZero q] {N M : ℝ} (hM : 0 < M) (hN : 0 < N) {d : ℕ}
    (hd : 0 < d) (s : ℂ) :
    DifferentiableOn ℂ (resPhi q N M d s) {w : ℂ | -1 < w.re} := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM hd0
  have hNc : ((N / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNd.ne'
  have hMc : ((M / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMd.ne'
  have hLd : Differentiable ℂ (fun w : ℂ => LFunctionTrivChar₁ q (1 + s + w)) := fun v =>
    (differentiable_LFunctionTrivChar₁ q (1 + s + v)).comp v
      (differentiableAt_id.const_add (1 + s))
  have hunfold : resPhi q N M d s = fun w : ℂ =>
      2 * (((N / (d : ℝ) : ℝ) : ℂ) ^ w - ((M / (d : ℝ) : ℝ) : ℂ) ^ w) / ((w + 1) * (w + 2))
        * LFunctionTrivChar₁ q (1 + s + w) := rfl
  rw [hunfold]
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hden1 : w + 1 ≠ 0 := by
    intro hcon
    have hre : (w + 1).re = w.re + 1 := by simp
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hden2 : w + 2 ≠ 0 := by
    intro hcon
    have hre : (w + 2).re = w.re + 2 := by simp
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have h1 : DifferentiableAt ℂ (fun w : ℂ => ((N / (d : ℝ) : ℝ) : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl hNc)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => ((M / (d : ℝ) : ℝ) : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl hMc)
  exact DifferentiableAt.mul
    (DifferentiableAt.div ((differentiableAt_const 2).mul (h1.sub h2))
      ((differentiableAt_id.add (differentiableAt_const 1)).mul
        (differentiableAt_id.add (differentiableAt_const 2))) (mul_ne_zero hden1 hden2))
    (hLd w)

theorem resPhi_zero (q : ℕ) [NeZero q] (N M : ℝ) (d : ℕ) (s : ℂ) : resPhi q N M d s 0 = 0 := by
  simp only [resPhi, resKernelFun_zero, zero_mul]

/-- `G(w) = (dslope ψ 0)(w)/(w − (−s))` off `w = 0` and `w = −s`. -/
theorem resIntegrand_eq_dslope_div (q : ℕ) [NeZero q] (N M : ℝ) {d : ℕ} (hd : 0 < d) (s : ℂ) {w : ℂ}
    (hw : w ≠ 0) (hws : w + s ≠ 0) :
    resIntegrand q N M d s w = dslope (resPhi q N M d s) 0 w / (w - (-s)) := by
  have _hd : 0 < d := hd
  have hu : (1 : ℂ) + s + w ≠ 1 := by
    intro hcon
    exact hws (by linear_combination hcon)
  have hupd : LFunctionTrivChar₁ q (1 + s + w)
      = (1 + s + w - 1) * LFunctionTrivChar q (1 + s + w) := Function.update_of_ne hu _ _
  rw [dslope_of_ne _ hw, slope_def_field, resPhi_zero, sub_zero, sub_zero]
  simp only [resIntegrand, resPhi, resKernelFun, hupd]
  have h1 : (1 : ℂ) + s + w - 1 = w + s := by ring
  have h2 : w - (-s) = w + s := by ring
  rw [h1, h2]
  field_simp

/-- THE RESIDUE'S VALUE, both branches at once:
`(dslope ψ 0)(−s) = E(χ₀)·resKernel s (N/d) (M/d)` (`s ≠ 0`: `ψ(−s)/(−s)`; `s = 0`: `ψ'(0)`). -/
theorem dslope_resPhi_neg (q : ℕ) [NeZero q] {N M : ℝ} (hM : 0 < M) (hN : 0 < N) {d : ℕ}
    (hd : 0 < d) (s : ℂ) :
    dslope (resPhi q N M d s) 0 (-s)
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) * resKernel s (N / d) (M / d) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM hd0
  have hNc : ((N / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNd.ne'
  have hMc : ((M / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMd.ne'
  have hkfun : resKernelFun (N / (d : ℝ)) (M / (d : ℝ)) = fun w : ℂ =>
      2 * (((N / (d : ℝ) : ℝ) : ℂ) ^ w - ((M / (d : ℝ) : ℝ) : ℂ) ^ w)
        / ((w + 1) * (w + 2)) := rfl
  have hne : ((0 : ℂ) + 1) * ((0 : ℂ) + 2) ≠ 0 := by norm_num
  have hkd : DifferentiableAt ℂ (resKernelFun (N / (d : ℝ)) (M / (d : ℝ))) 0 := by
    rw [hkfun]
    exact DifferentiableAt.div
      ((differentiableAt_const 2).mul
        ((differentiableAt_id.const_cpow (Or.inl hNc)).sub
          (differentiableAt_id.const_cpow (Or.inl hMc))))
      ((differentiableAt_id.add (differentiableAt_const 1)).mul
        (differentiableAt_id.add (differentiableAt_const 2))) hne
  have hLd : DifferentiableAt ℂ (fun w : ℂ => LFunctionTrivChar₁ q (1 + s + w)) 0 :=
    (differentiable_LFunctionTrivChar₁ q (1 + s + 0)).comp 0
      (differentiableAt_id.const_add (1 + s))
  have hunfold : resPhi q N M d s = fun w : ℂ =>
      resKernelFun (N / (d : ℝ)) (M / (d : ℝ)) w * LFunctionTrivChar₁ q (1 + s + w) := rfl
  rw [hunfold, dslope_mul_of_zero (resKernelFun_zero _ _) hkd hLd (-s)]
  have h1 : (1 : ℂ) + s + (-s) = 1 := by ring
  rw [h1]
  simp only [LFunctionTrivChar₁, Function.update_self, resKernel]
  ring

/-- The Cauchy integral formula on the rectangle `[σ₀, c] × [−T', T']` at the interior point
`−s`. -/
theorem rectBI_resPhi_dslope_div_eq (q : ℕ) [NeZero q] {N M : ℝ} (hM : 0 < M) (hN : 0 < N) {d : ℕ}
    (hd : 0 < d) {s : ℂ} {σ₀ c T' : ℝ} (hσ₀ : -1 < σ₀) (hσ₀s : σ₀ < -s.re) (hcs : -s.re < c)
    (hT' : |s.im| < T') :
    rectBI ((σ₀ : ℂ) - (T' : ℂ) * I) ((c : ℂ) + (T' : ℂ) * I)
        (fun w => dslope (resPhi q N M d s) 0 w / (w - (-s)))
      = 2 * (Real.pi : ℂ) * I * dslope (resPhi q N M d s) 0 (-s) := by
  have hTpos : (0 : ℝ) < T' := lt_of_le_of_lt (abs_nonneg s.im) hT'
  have hσc : σ₀ < c := lt_trans hσ₀s hcs
  have hzre : ((σ₀ : ℂ) - (T' : ℂ) * I).re = σ₀ := by simp
  have hzim : ((σ₀ : ℂ) - (T' : ℂ) * I).im = -T' := by simp
  have hwre : ((c : ℂ) + (T' : ℂ) * I).re = c := by simp
  have hwim : ((c : ℂ) + (T' : ℂ) * I).im = T' := by simp
  have hopen : IsOpen {w : ℂ | -1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (0 : ℂ) ∈ {w : ℂ | -1 < w.re} := by
    simp only [Set.mem_setOf_eq, Complex.zero_re]
    norm_num
  have hdsl : DifferentiableOn ℂ (dslope (resPhi q N M d s) 0) {w : ℂ | -1 < w.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds hmem)).mpr
      (resPhi_differentiableOn q hM hN hd s)
  have hsub : closedRect ((σ₀ : ℂ) - (T' : ℂ) * I) ((c : ℂ) + (T' : ℂ) * I)
      ⊆ {w : ℂ | -1 < w.re} := by
    intro v hv
    simp only [closedRect, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le hσc.le] at hv
    exact lt_of_lt_of_le hσ₀ hv.1.1
  have him := abs_lt.mp hT'
  refine rectBI_cif_eq (hdsl.mono hsub) ?_ ?_ ?_ ?_
  · rw [hzre, hwre]; exact hσc
  · rw [hzim, hwim]; linarith
  · rw [hzre, hwre]
    refine ⟨?_, ?_⟩
    · simpa using hσ₀s
    · simpa using hcs
  · rw [hzim, hwim]
    refine ⟨?_, ?_⟩
    · simp only [Complex.neg_im]; linarith [him.2]
    · simp only [Complex.neg_im]; linarith [him.1]

/-- The pointwise bound on the strip `Re(1 + s + w) ≥ 1/2` away from the pole (`‖s + w‖ ≥ 1/2`),
with the kernel factor as the SUM `(N/d)^{Re w} + (M/d)^{Re w}` — on the LEFT line (`Re w < 0`,
`M < N`) the `M`-term is the larger, and a bound by `2(N/d)^{Re w}` is FALSE there by up to
`(1 + (N/M)^{|Re w|})/2` (`1.62` at `(40, 8)`, `Re w = −1/2`): the verdict's kill 13a in the desk's
own first cut, caught by the sweep before the pass. The consumer collapses the sum against the
outer `d^{−1−Re s}` (design v2 §A.7). -/
theorem norm_resIntegrand_le (q : ℕ) [NeZero q] {N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N) {d : ℕ}
    (hd : 0 < d) (s w : ℂ) (hw1 : (1 : ℝ) / 2 ≤ (1 + s + w).re) (hws : 1 / 2 ≤ ‖s + w‖) :
    ‖resIntegrand q N M d s w‖
      ≤ 2 * ((N / d) ^ w.re + (M / d) ^ w.re) * ((q : ℝ) * (2 + 3 * ‖1 + s + w‖))
          * ‖(w * (w + 1) * (w + 2))⁻¹‖ := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN0 hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM0 hd0
  have hu1 : (1 + s + w) ≠ 1 := by
    intro hcon
    have hz : s + w = 0 := by linear_combination hcon
    rw [hz, norm_zero] at hws
    linarith
  have hzeta : ‖riemannZeta (1 + s + w)‖ ≤ 2 + 3 * ‖1 + s + w‖ := by
    refine norm_riemannZeta_le_of_half_le hw1 ?_
    rw [show (1 + s + w) - 1 = s + w by ring]
    exact hws
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hL : ‖LFunctionTrivChar q (1 + s + w)‖ ≤ (q : ℝ) * (2 + 3 * ‖1 + s + w‖) :=
    le_trans (norm_LFunctionTrivChar_le q (by linarith) hu1)
      (mul_le_mul_of_nonneg_left hzeta hq0)
  have hker : ‖((N / (d : ℝ) : ℝ) : ℂ) ^ w - ((M / (d : ℝ) : ℝ) : ℂ) ^ w‖
      ≤ (N / (d : ℝ)) ^ w.re + (M / (d : ℝ)) ^ w.re := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNd, Complex.norm_cpow_eq_rpow_re_of_pos hMd]
  have hkn : (0 : ℝ) ≤ (N / (d : ℝ)) ^ w.re + (M / (d : ℝ)) ^ w.re :=
    add_nonneg (Real.rpow_nonneg hNd.le _) (Real.rpow_nonneg hMd.le _)
  have hnum : ‖2 * (((N / (d : ℝ) : ℝ) : ℂ) ^ w - ((M / (d : ℝ) : ℝ) : ℂ) ^ w)
        * LFunctionTrivChar q (1 + s + w)‖
      ≤ 2 * ((N / (d : ℝ)) ^ w.re + (M / (d : ℝ)) ^ w.re)
        * ((q : ℝ) * (2 + 3 * ‖1 + s + w‖)) := by
    rw [norm_mul, norm_mul, (by norm_num : ‖(2 : ℂ)‖ = 2)]
    refine mul_le_mul ?_ hL (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hker (by norm_num)
  simp only [resIntegrand]
  rw [norm_div, norm_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (norm_nonneg _))

/-- The horizontal edge at height `τ` (`|τ| ≥ 1 + |Im s|`, so `‖u − 1‖ ≥ 1/2` on it — A9b):
`≪ (c − σ₀)·B^{e}·q·(…)/|τ|³` with the kernel factor `B^{e} := (max (N/d) (d/M))^{max c |σ₀|}`,
which dominates BOTH `(N/d)^{u}` and `(M/d)^{u}` for every `u ∈ [σ₀, c]` (`B ≥ 1`; `u ≥ 0` reads
`(N/d)^c`, `u < 0` reads `(d/M)^{|σ₀|}`) — the first cut's `(max 1 (N/d))^c` fails for `d > M`,
`σ₀ < 0` (kill 13a's class). Its size is immaterial: the edge vanishes against `|τ|³`. -/
theorem norm_integral_resIntegrand_edge_le (q : ℕ) [NeZero q] {N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N)
    {d : ℕ} (hd : 0 < d) (s : ℂ) {σ₀ c τ : ℝ} (hσ₀ : (1 : ℝ) / 2 ≤ (1 + s).re + σ₀) (hσc : σ₀ ≤ c)
    (hτ : 1 + |s.im| ≤ |τ|) :
    ‖∫ u in σ₀..c, resIntegrand q N M d s ((u : ℂ) + (τ : ℂ) * I)‖
      ≤ (c - σ₀) * (4 * (max (N / d) (d / M)) ^ (max c |σ₀|)
          * ((q : ℝ) * (2 + 3 * (1 + ‖s‖ + |σ₀| + |c| + |τ|))) / |τ| ^ 3) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN0 hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM0 hd0
  have hτ0 : (0 : ℝ) < |τ| := by linarith [abs_nonneg s.im]
  have hB : (1 : ℝ) ≤ max (N / (d : ℝ)) ((d : ℝ) / M) := by
    rcases le_or_gt 1 (N / (d : ℝ)) with h | h
    · exact le_max_of_le_left h
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ hM0, one_mul]
      have hlt : N < (d : ℝ) := by rw [div_lt_one hd0] at h; exact h
      linarith
  have hNle : N / (d : ℝ) ≤ max (N / (d : ℝ)) ((d : ℝ) / M) := le_max_left _ _
  have hMle : M / (d : ℝ) ≤ max (N / (d : ℝ)) ((d : ℝ) / M) := by
    refine le_trans ?_ (le_max_left _ _)
    have h := mul_le_mul_of_nonneg_right hMN (inv_nonneg.mpr hd0.le)
    rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h
  have hNinv : 1 / (N / (d : ℝ)) ≤ max (N / (d : ℝ)) ((d : ℝ) / M) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [one_div_div]
    exact div_le_div_of_nonneg_left hd0.le hM0 hMN
  have hMinv : 1 / (M / (d : ℝ)) ≤ max (N / (d : ℝ)) ((d : ℝ) / M) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [one_div_div]
  have hec : c ≤ max c |σ₀| := le_max_left _ _
  have heσ : |σ₀| ≤ max c |σ₀| := le_max_right _ _
  have hpt : ∀ u ∈ Set.uIoc σ₀ c,
      ‖resIntegrand q N M d s ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ 4 * (max (N / (d : ℝ)) ((d : ℝ) / M)) ^ (max c |σ₀|)
            * ((q : ℝ) * (2 + 3 * (1 + ‖s‖ + |σ₀| + |c| + |τ|))) / |τ| ^ 3 := by
    intro u hu
    rw [Set.uIoc_of_le hσc] at hu
    obtain ⟨hu1', hu2'⟩ := hu
    have hwre : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have hwim : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hw1 : (1 : ℝ) / 2 ≤ (1 + s + ((u : ℂ) + (τ : ℂ) * I)).re := by
      have hre : (1 + s + ((u : ℂ) + (τ : ℂ) * I)).re = (1 + s).re + u := by simp
      rw [hre]
      have := hu1'.le
      linarith
    have hws : (1 : ℝ) / 2 ≤ ‖s + ((u : ℂ) + (τ : ℂ) * I)‖ := by
      have him : (s + ((u : ℂ) + (τ : ℂ) * I)).im = s.im + τ := by simp
      have h := Complex.abs_im_le_norm (s + ((u : ℂ) + (τ : ℂ) * I))
      rw [him] at h
      have h3 := abs_add_le (s.im + τ) (-s.im)
      rw [abs_neg, show s.im + τ + -s.im = τ by ring] at h3
      linarith
    have hbase := norm_resIntegrand_le q hM hMN hd s ((u : ℂ) + (τ : ℂ) * I) hw1 hws
    rw [hwre] at hbase
    have hkersum : (N / (d : ℝ)) ^ u + (M / (d : ℝ)) ^ u
        ≤ 2 * (max (N / (d : ℝ)) ((d : ℝ) / M)) ^ (max c |σ₀|) := by
      have e1 := rpow_le_max_rpow hNd hB hNle hNinv hu1'.le hu2' hec heσ
      have e2 := rpow_le_max_rpow hMd hB hMle hMinv hu1'.le hu2' hec heσ
      linarith
    have hnb : ‖1 + s + ((u : ℂ) + (τ : ℂ) * I)‖ ≤ 1 + ‖s‖ + |σ₀| + |c| + |τ| := by
      have hA : ‖1 + s + ((u : ℂ) + (τ : ℂ) * I)‖
          ≤ ‖(1 : ℂ)‖ + ‖s‖ + ‖(u : ℂ) + (τ : ℂ) * I‖ := by
        refine le_trans (norm_add_le _ _) ?_
        have := norm_add_le (1 : ℂ) s
        linarith
      have hBb : ‖(u : ℂ) + (τ : ℂ) * I‖ ≤ |u| + |τ| := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
      have hC : |u| ≤ |σ₀| + |c| := by
        rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]; linarith [le_abs_self c, abs_nonneg σ₀]
        · rw [he]; linarith [neg_abs_le σ₀, abs_nonneg c]
      rw [norm_one] at hA
      linarith
    have hcube := norm_inv_denom2_le_abs_im_cube (w := (u : ℂ) + (τ : ℂ) * I)
      (by rw [hwim]; exact abs_pos.mp hτ0)
    rw [hwim] at hcube
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hstep := mul4_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ))
      (b₁ := (N / (d : ℝ)) ^ u + (M / (d : ℝ)) ^ u)
      (b₂ := 2 * (max (N / (d : ℝ)) ((d : ℝ) / M)) ^ (max c |σ₀|))
      (c₁ := (q : ℝ) * (2 + 3 * ‖1 + s + ((u : ℂ) + (τ : ℂ) * I)‖))
      (c₂ := (q : ℝ) * (2 + 3 * (1 + ‖s‖ + |σ₀| + |c| + |τ|)))
      (e₁ := ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1)
        * (((u : ℂ) + (τ : ℂ) * I) + 2))⁻¹‖) (e₂ := (|τ| ^ 3)⁻¹)
      (by norm_num)
      (add_nonneg (Real.rpow_nonneg hNd.le _) (Real.rpow_nonneg hMd.le _))
      (by positivity) (norm_nonneg _) le_rfl hkersum
      (by nlinarith [hq0, hnb]) hcube
    refine (hbase.trans hstep).trans (le_of_eq ?_)
    field_simp
    ring
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (sub_nonneg.mpr hσc)] at hmain
  refine hmain.trans (le_of_eq ?_)
  ring

/-- Integrability on a vertical line `Re w = σ` with `|Re s + σ| ≥ 1/2` and
`m ≤ |σ|, |σ + 1|, |σ + 2|`. -/
theorem integrable_resIntegrand_line (q : ℕ) [NeZero q] {N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N)
    {d : ℕ} (hd : 0 < d) (s : ℂ) {σ m : ℝ} (hσ1 : (1 : ℝ) / 2 ≤ (1 + s).re + σ)
    (hσs : 1 / 2 ≤ |s.re + σ|) (hm : 0 < m) (h0 : m ≤ |σ|) (h1 : m ≤ |σ + 1|) (h2 : m ≤ |σ + 2|) :
    Integrable (fun t : ℝ => resIntegrand q N M d s ((σ : ℂ) + (t : ℂ) * I)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN0 hd0
  have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM0 hd0
  have hNc : ((N / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNd.ne'
  have hMc : ((M / (d : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMd.ne'
  have hwc : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by fun_prop
  have hreline : ∀ t : ℝ, (1 + s + ((σ : ℂ) + (t : ℂ) * I)).re = (1 + s).re + σ := by
    intro t; simp
  have hne1 : ∀ t : ℝ, (1 + s + ((σ : ℂ) + (t : ℂ) * I)) ≠ 1 := by
    intro t hcon
    have hre : (1 + s + ((σ : ℂ) + (t : ℂ) * I)).re = 1 := by rw [hcon, Complex.one_re]
    rw [hreline t] at hre
    have hre1 : (1 + s).re = 1 + s.re := by simp
    rw [hre1] at hre
    have hz : s.re + σ = 0 := by linarith
    rw [hz, abs_zero] at hσs
    linarith
  have hLcont : Continuous
      (fun t : ℝ => LFunctionTrivChar q (1 + s + ((σ : ℂ) + (t : ℂ) * I))) := by
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have h1 : ContinuousAt (LFunctionTrivChar q) (1 + s + ((σ : ℂ) + (t : ℂ) * I)) :=
      (DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl (hne1 t))).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => 1 + s + ((σ : ℂ) + (t : ℂ) * I)) t := by fun_prop
    have h3 : ContinuousAt (LFunctionTrivChar q ∘ fun t : ℝ =>
        1 + s + ((σ : ℂ) + (t : ℂ) * I)) t := ContinuousAt.comp h1 h2
    exact h3
  have hdne : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)
      * ((σ : ℂ) + (t : ℂ) * I + 2) ≠ 0 := by
    intro t
    have e0 : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro hcon
      have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
      rw [hcon] at hre
      simp only [Complex.zero_re] at hre
      rw [← hre, abs_zero] at h0
      linarith
    have e1 : ((σ : ℂ) + (t : ℂ) * I + 1) ≠ 0 := by
      intro hcon
      have hre : ((σ : ℂ) + (t : ℂ) * I + 1).re = σ + 1 := by simp
      rw [hcon] at hre
      simp only [Complex.zero_re] at hre
      rw [← hre, abs_zero] at h1
      linarith
    have e2 : ((σ : ℂ) + (t : ℂ) * I + 2) ≠ 0 := by
      intro hcon
      have hre : ((σ : ℂ) + (t : ℂ) * I + 2).re = σ + 2 := by simp
      rw [hcon] at hre
      simp only [Complex.zero_re] at hre
      rw [← hre, abs_zero] at h2
      linarith
    exact mul_ne_zero (mul_ne_zero e0 e1) e2
  have hcont : Continuous (fun t : ℝ => resIntegrand q N M d s ((σ : ℂ) + (t : ℂ) * I)) := by
    simp only [resIntegrand]
    refine Continuous.div ?_ ?_ hdne
    · exact ((continuous_const.mul ((Continuous.const_cpow hwc (Or.inl hNc)).sub
        (Continuous.const_cpow hwc (Or.inl hMc)))).mul hLcont)
    · exact (hwc.mul (hwc.add continuous_const)).mul (hwc.add continuous_const)
  have hkn : (0 : ℝ) ≤ (N / (d : ℝ)) ^ σ + (M / (d : ℝ)) ^ σ :=
    add_nonneg (Real.rpow_nonneg hNd.le _) (Real.rpow_nonneg hMd.le _)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hg : Integrable (fun t : ℝ =>
      (2 * ((N / (d : ℝ)) ^ σ + (M / (d : ℝ)) ^ σ) * (q : ℝ))
        * ((2 + 3 * (1 + ‖s‖ + |σ|)) * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
          + 3 * (|t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹))) :=
    ((((integrable_inv_sq_add_sq_rpow hm).const_mul (2 + 3 * (1 + ‖s‖ + |σ|))).add
      ((integrable_abs_mul_inv_sq_add_sq_rpow hm).const_mul 3)).const_mul _)
  refine hg.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hwre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have hw1 : (1 : ℝ) / 2 ≤ (1 + s + ((σ : ℂ) + (t : ℂ) * I)).re := by
    rw [hreline t]; linarith
  have hws : (1 : ℝ) / 2 ≤ ‖s + ((σ : ℂ) + (t : ℂ) * I)‖ := by
    have hre : (s + ((σ : ℂ) + (t : ℂ) * I)).re = s.re + σ := by simp
    have h := Complex.abs_re_le_norm (s + ((σ : ℂ) + (t : ℂ) * I))
    rw [hre] at h
    linarith
  have hbase := norm_resIntegrand_le q hM hMN hd s ((σ : ℂ) + (t : ℂ) * I) hw1 hws
  rw [hwre] at hbase
  have hnb : ‖1 + s + ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (1 + ‖s‖ + |σ|) + |t| := by
    have hA : ‖1 + s + ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖(1 : ℂ)‖ + ‖s‖ + ‖(σ : ℂ) + (t : ℂ) * I‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have := norm_add_le (1 : ℂ) s
      linarith
    have hBb : ‖(σ : ℂ) + (t : ℂ) * I‖ ≤ |σ| + |t| := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    rw [norm_one] at hA
    linarith
  have hcube := norm_inv_denom2_cubic_le_of_min hm h0 h1 h2 t
  have hstep := mul4_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ))
    (b₁ := (N / (d : ℝ)) ^ σ + (M / (d : ℝ)) ^ σ)
    (b₂ := (N / (d : ℝ)) ^ σ + (M / (d : ℝ)) ^ σ)
    (c₁ := (q : ℝ) * (2 + 3 * ‖1 + s + ((σ : ℂ) + (t : ℂ) * I)‖))
    (c₂ := (q : ℝ) * (2 + 3 * ((1 + ‖s‖ + |σ|) + |t|)))
    (e₁ := ‖(((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)
      * ((σ : ℂ) + (t : ℂ) * I + 2))⁻¹‖) (e₂ := ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
    (by norm_num) hkn (by positivity) (norm_nonneg _) le_rfl le_rfl
    (by nlinarith [hq0, hnb]) hcube
  refine (hbase.trans hstep).trans (le_of_eq ?_)
  ring

/-- THE SHIFT with the residue:
`(1/2π)∫_{Re w = 1} G = (dslope ψ 0)(−s) + (1/2π)∫_{Re w = −1/2 − Re s} G`. -/
theorem integral_resIntegrand_shift (q : ℕ) [NeZero q] {N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N) {d : ℕ}
    (hd : 0 < d) {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 1 / 60) :
    (1 / (2 * Real.pi)) • (∫ t : ℝ, resIntegrand q N M d s ((1 : ℂ) + (t : ℂ) * I))
      = dslope (resPhi q N M d s) 0 (-s)
        + (1 / (2 * Real.pi)) • ∫ t : ℝ,
            resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hs1re : (1 + s).re = 1 + s.re := by simp
  set σ₀ : ℝ := -1 / 2 - s.re with hσdef
  have hσm1 : (-1 : ℝ) < σ₀ := by rw [hσdef]; linarith
  have hσneg : σ₀ < 0 := by rw [hσdef]; linarith
  have hσc : σ₀ ≤ (1 : ℝ) := by linarith
  have hσ0e : (1 : ℝ) / 2 ≤ (1 + s).re + σ₀ := by rw [hs1re, hσdef]; linarith
  have hce : (1 : ℝ) / 2 ≤ (1 + s).re + 1 := by rw [hs1re]; linarith
  have habsσ0 : |σ₀| = 1 / 2 + s.re := by
    rw [hσdef, abs_of_neg (by linarith : -1 / 2 - s.re < 0)]; ring
  have habsσ1 : |σ₀ + 1| = 1 / 2 - s.re := by
    rw [hσdef, abs_of_pos (by linarith : (0 : ℝ) < -1 / 2 - s.re + 1)]; ring
  have habsσ2 : |σ₀ + 2| = 3 / 2 - s.re := by
    rw [hσdef, abs_of_pos (by linarith : (0 : ℝ) < -1 / 2 - s.re + 2)]; ring
  have hIntC : Integrable (fun t : ℝ => resIntegrand q N M d s ((1 : ℂ) + (t : ℂ) * I)) := by
    have h := integrable_resIntegrand_line q hM hMN hd s (σ := (1 : ℝ)) (m := (1 : ℝ)) hce
      (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re + 1)]; linarith)
      (by norm_num)
      (le_of_eq (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ))).symm)
      (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) + 1)]; norm_num)
      (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) + 2)]; norm_num)
    rw [Complex.ofReal_one] at h
    exact h
  have hIntL : Integrable (fun t : ℝ => resIntegrand q N M d s ((σ₀ : ℂ) + (t : ℂ) * I)) :=
    integrable_resIntegrand_line q hM hMN hd s hσ0e
      (by rw [hσdef, abs_of_nonpos (by linarith : s.re + (-1 / 2 - s.re) ≤ 0)]; linarith)
      (by norm_num : (0 : ℝ) < 29 / 60)
      (by rw [habsσ0]; linarith) (by rw [habsσ1]; linarith) (by rw [habsσ2]; linarith)
  have hRt : Filter.Tendsto (fun T' : ℝ => ∫ y in (-T')..T',
      resIntegrand q N M d s ((1 : ℂ) + (y : ℂ) * I)) Filter.atTop
      (nhds (∫ t : ℝ, resIntegrand q N M d s ((1 : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hIntC Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hLt : Filter.Tendsto (fun T' : ℝ => ∫ y in (-T')..T',
      resIntegrand q N M d s ((σ₀ : ℂ) + (y : ℂ) * I)) Filter.atTop
      (nhds (∫ t : ℝ, resIntegrand q N M d s ((σ₀ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hIntL Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hgtend : Filter.Tendsto (fun T' : ℝ =>
      ((1 - σ₀) * (4 * (max (N / (d : ℝ)) ((d : ℝ) / M)) ^ (max (1 : ℝ) |σ₀|)
          * ((q : ℝ) * (2 + 3 * (1 + ‖s‖ + |σ₀| + |(1 : ℝ)|))))) * (T' ^ 3)⁻¹
      + ((1 - σ₀) * (4 * (max (N / (d : ℝ)) ((d : ℝ) / M)) ^ (max (1 : ℝ) |σ₀|)
          * ((q : ℝ) * 3))) * (T' ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have e3 : Filter.Tendsto (fun T' : ℝ => (T' ^ 3)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num))
    have e2 : Filter.Tendsto (fun T' : ℝ => (T' ^ 2)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num))
    simpa using (e3.const_mul _).add (e2.const_mul _)
  have hTopt : Filter.Tendsto (fun T' : ℝ => ∫ u in σ₀..(1 : ℝ),
      resIntegrand q N M d s ((u : ℂ) + ((T' : ℝ) : ℂ) * I)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgtend
    filter_upwards [Filter.eventually_gt_atTop (1 + |s.im|)] with T' hT'
    have hTpos : (0 : ℝ) < T' := by linarith [abs_nonneg s.im]
    have hTne : T' ≠ 0 := hTpos.ne'
    have hb := norm_integral_resIntegrand_edge_le q hM hMN hd s (σ₀ := σ₀) (c := (1 : ℝ))
      (τ := T') hσ0e hσc (by rw [abs_of_pos hTpos]; linarith)
    rw [abs_of_pos hTpos] at hb
    refine hb.trans (le_of_eq ?_)
    field_simp
    ring
  have hBott : Filter.Tendsto (fun T' : ℝ => ∫ u in σ₀..(1 : ℝ),
      resIntegrand q N M d s ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgtend
    filter_upwards [Filter.eventually_gt_atTop (1 + |s.im|)] with T' hT'
    have hTpos : (0 : ℝ) < T' := by linarith [abs_nonneg s.im]
    have hTne : T' ≠ 0 := hTpos.ne'
    have hb := norm_integral_resIntegrand_edge_le q hM hMN hd s (σ₀ := σ₀) (c := (1 : ℝ))
      (τ := -T') hσ0e hσc (by rw [abs_neg, abs_of_pos hTpos]; linarith)
    rw [abs_neg, abs_of_pos hTpos] at hb
    refine hb.trans (le_of_eq ?_)
    field_simp
    ring
  have hedges : ∀ T' : ℝ, 1 + |s.im| < T' →
      (∫ y in (-T')..T', resIntegrand q N M d s ((1 : ℂ) + (y : ℂ) * I))
        - (∫ y in (-T')..T', resIntegrand q N M d s ((σ₀ : ℂ) + (y : ℂ) * I))
      = 2 * (Real.pi : ℂ) * dslope (resPhi q N M d s) 0 (-s)
        + (-I) * ((∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((T' : ℝ) : ℂ) * I))
          - ∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)) := by
    intro T' hT'
    have hTpos : (0 : ℝ) < T' := by linarith [abs_nonneg s.im]
    have hTim : |s.im| < T' := by linarith
    have hTim2 := abs_lt.mp hTim
    have hrect := rectBI_resPhi_dslope_div_eq q hM0 hN0 hd (σ₀ := σ₀) (c := (1 : ℝ)) (T' := T')
      hσm1 (by rw [hσdef]; linarith) (by linarith) hTim
    have hzre : ((σ₀ : ℂ) - (T' : ℂ) * I).re = σ₀ := by simp
    have hzim : ((σ₀ : ℂ) - (T' : ℂ) * I).im = -T' := by simp
    have hwre : ((1 : ℂ) + (T' : ℂ) * I).re = 1 := by simp
    have hwim : ((1 : ℂ) + (T' : ℂ) * I).im = T' := by simp
    simp only [rectBI, Complex.ofReal_one, hzre, hzim, hwre, hwim] at hrect
    have hb1 : (∫ u in σ₀..(1 : ℝ), dslope (resPhi q N M d s) 0 ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)
          / (((u : ℂ) + ((-T' : ℝ) : ℂ) * I) - (-s)))
        = ∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      refine (resIntegrand_eq_dslope_div q N M hd s ?_ ?_).symm
      · intro hcon
        have him : ((u : ℂ) + ((-T' : ℝ) : ℂ) * I).im = -T' := by simp
        rw [hcon] at him
        simp only [Complex.zero_im] at him
        linarith
      · intro hcon
        have him : (((u : ℂ) + ((-T' : ℝ) : ℂ) * I) + s).im = -T' + s.im := by simp
        rw [hcon] at him
        simp only [Complex.zero_im] at him
        linarith [hTim2.2]
    have hb2 : (∫ u in σ₀..(1 : ℝ), dslope (resPhi q N M d s) 0 ((u : ℂ) + ((T' : ℝ) : ℂ) * I)
          / (((u : ℂ) + ((T' : ℝ) : ℂ) * I) - (-s)))
        = ∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((T' : ℝ) : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      refine (resIntegrand_eq_dslope_div q N M hd s ?_ ?_).symm
      · intro hcon
        have him : ((u : ℂ) + ((T' : ℝ) : ℂ) * I).im = T' := by simp
        rw [hcon] at him
        simp only [Complex.zero_im] at him
        linarith
      · intro hcon
        have him : (((u : ℂ) + ((T' : ℝ) : ℂ) * I) + s).im = T' + s.im := by simp
        rw [hcon] at him
        simp only [Complex.zero_im] at him
        linarith [hTim2.1]
    have hb3 : (∫ y in (-T')..T', dslope (resPhi q N M d s) 0 ((1 : ℂ) + (y : ℂ) * I)
          / (((1 : ℂ) + (y : ℂ) * I) - (-s)))
        = ∫ y in (-T')..T', resIntegrand q N M d s ((1 : ℂ) + (y : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      refine (resIntegrand_eq_dslope_div q N M hd s ?_ ?_).symm
      · intro hcon
        have hre : ((1 : ℂ) + (y : ℂ) * I).re = 1 := by simp
        rw [hcon] at hre
        simp only [Complex.zero_re] at hre
        linarith
      · intro hcon
        have hre : (((1 : ℂ) + (y : ℂ) * I) + s).re = 1 + s.re := by simp
        rw [hcon] at hre
        simp only [Complex.zero_re] at hre
        linarith
    have hb4 : (∫ y in (-T')..T', dslope (resPhi q N M d s) 0 ((σ₀ : ℂ) + (y : ℂ) * I)
          / (((σ₀ : ℂ) + (y : ℂ) * I) - (-s)))
        = ∫ y in (-T')..T', resIntegrand q N M d s ((σ₀ : ℂ) + (y : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      refine (resIntegrand_eq_dslope_div q N M hd s ?_ ?_).symm
      · intro hcon
        have hre : ((σ₀ : ℂ) + (y : ℂ) * I).re = σ₀ := by simp
        rw [hcon] at hre
        simp only [Complex.zero_re] at hre
        linarith
      · intro hcon
        have hre : (((σ₀ : ℂ) + (y : ℂ) * I) + s).re = σ₀ + s.re := by simp
        rw [hcon] at hre
        simp only [Complex.zero_re] at hre
        rw [hσdef] at hre
        linarith
    rw [hb1, hb2, hb3, hb4] at hrect
    set Rv := ∫ y in (-T')..T', resIntegrand q N M d s ((1 : ℂ) + (y : ℂ) * I) with hRv
    set Lv := ∫ y in (-T')..T', resIntegrand q N M d s ((σ₀ : ℂ) + (y : ℂ) * I) with hLv
    set Bv := ∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) with hBv
    set Tv := ∫ u in σ₀..(1 : ℝ), resIntegrand q N M d s ((u : ℂ) + ((T' : ℝ) : ℂ) * I) with hTv
    set ρ := dslope (resPhi q N M d s) 0 (-s) with hρ
    have hII : (-I) * I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    have h3 : I * (Rv - Lv) = 2 * (Real.pi : ℂ) * I * ρ - Bv + Tv := by linear_combination hrect
    calc Rv - Lv = (-I) * (I * (Rv - Lv)) := by rw [← mul_assoc, hII, one_mul]
      _ = (-I) * (2 * (Real.pi : ℂ) * I * ρ - Bv + Tv) := by rw [h3]
      _ = 2 * (Real.pi : ℂ) * ρ + (-I) * (Tv - Bv) := by
          have hkey : (-I) * (2 * (Real.pi : ℂ) * I * ρ) = 2 * (Real.pi : ℂ) * ρ := by
            rw [show (-I) * (2 * (Real.pi : ℂ) * I * ρ) = ((-I) * I) * (2 * (Real.pi : ℂ) * ρ) by
              ring, hII, one_mul]
          linear_combination hkey
  have hdiff1 := hRt.sub hLt
  have hdiff2 : Filter.Tendsto (fun T' : ℝ =>
      (∫ y in (-T')..T', resIntegrand q N M d s ((1 : ℂ) + (y : ℂ) * I))
        - ∫ y in (-T')..T', resIntegrand q N M d s ((σ₀ : ℂ) + (y : ℂ) * I))
      Filter.atTop (nhds (2 * (Real.pi : ℂ) * dslope (resPhi q N M d s) 0 (-s))) := by
    have hTB := (hTopt.sub hBott).const_mul (-I)
    rw [sub_zero, mul_zero] at hTB
    have hsum := (tendsto_const_nhds
      (x := 2 * (Real.pi : ℂ) * dslope (resPhi q N M d s) 0 (-s))
      (f := Filter.atTop (α := ℝ))).add hTB
    rw [add_zero] at hsum
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards [Filter.eventually_gt_atTop (1 + |s.im|)] with T' hT'
    exact (hedges T' hT').symm
  have hfinal := tendsto_nhds_unique hdiff1 hdiff2
  have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hpi : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpine
    push_cast
    field_simp
  rw [Complex.real_smul, Complex.real_smul]
  have hA : (∫ t : ℝ, resIntegrand q N M d s ((1 : ℂ) + (t : ℂ) * I))
      = (∫ t : ℝ, resIntegrand q N M d s ((σ₀ : ℂ) + (t : ℂ) * I))
        + 2 * (Real.pi : ℂ) * dslope (resPhi q N M d s) 0 (-s) := by
    linear_combination hfinal
  rw [hA]
  linear_combination (dslope (resPhi q N M d s) 0 (-s)) * hpi

/-! ## (vi) The expansion and the identity -/

/-- The series is a FINITE sum (`b_n = 0` for `n ≥ N`). -/
theorem halaszBTsum_jutilaB_eq_sum (χ : DirichletCharacter ℂ q) {R N M : ℝ} (hM : 0 < M)
    (hMN : M ≤ N) (s : ℂ) :
    Salt.MR.halaszBTsum (jutilaB q R N M) χ χ s
      = ∑ n ∈ Finset.Icc 1 ⌈N⌉₊,
          (jutilaB q R N M n : ℂ) * (starRingEnd ℂ) (χ n) * χ n * (n : ℂ) ^ (-s) := by
  simp only [Salt.MR.halaszBTsum]
  refine tsum_eq_sum (s := Finset.Icc 1 ⌈N⌉₊) ?_
  intro n hn
  simp only [Finset.mem_Icc, not_and, not_le] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [jutilaB_zero]
    simp
  · have hlt := hn hn0
    have hceil : ((⌈N⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt.le
    have hNn : N ≤ (n : ℝ) := le_trans (Nat.le_ceil N) hceil
    rw [jutilaB_eq_zero_of_le hM hMN q R hNn]
    simp

/-- The `(r, r', d)`-expansion by Lemma 2 in its filter form, with `n = dm` and `χ₀(dm) = χ₀(m)`. -/
theorem halaszBTsum_jutilaB_expand [NeZero q] (χ : DirichletCharacter ℂ q) {R N M : ℝ} (hR : 1 ≤ R)
    (hM : 0 < M) (hMN : M ≤ N) {s : ℂ} (hs : 0 ≤ s.re) :
    Salt.MR.halaszBTsum (jutilaB q R N M) χ χ s
      = ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
          * ∑ d ∈ (r * r').divisors, (hCoef selbergPsi r r' d : ℂ)
            * ∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
                * (kern2 ((d * m : ℝ) / N) - kern2 ((d * m : ℝ) / M)) := by
  have _hR : (1 : ℝ) ≤ R := hR
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM hMN
  have hsne : -(1 : ℂ) - s ≠ 0 := by
    intro hcon
    have h : (-(1 : ℂ) - s).re = 0 := by rw [hcon]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re] at h
    linarith
  have hker0 : ∀ X : ℝ, 0 < X → ∀ x : ℝ, X ≤ x → kern2 (x / X) = 0 := by
    intro X hX x hx
    have h1 : (1 : ℝ) ≤ x / X := (one_le_div hX).mpr hx
    simp only [kern2, max_eq_left (by linarith : (1 : ℝ) - x / X ≤ 0)]
    norm_num
  have hgrp : (χ⁻¹ * χ : DirichletCharacter ℂ q) = 1 := by simp
  have hchar : ∀ n : ℕ, (starRingEnd ℂ) (χ n) * χ n = ((1 : DirichletCharacter ℂ q) n) := by
    intro n
    rw [starRingEnd_apply, MulChar.star_apply', ← MulChar.mul_apply, hgrp]
  have hsq : ∀ n : ℕ, ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n : ℝ) : ℂ) ^ 2
      = ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
          * ((∑ d ∈ (r * r').divisors with d ∣ n, hCoef selbergPsi r r' d : ℝ) : ℂ) := by
    intro n
    have hR2 : (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
        = ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, ((r : ℝ)⁻¹ * (r' : ℝ)⁻¹)
            * ∑ d ∈ (r * r').divisors with d ∣ n, hCoef selbergPsi r r' d := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun r' hr' => ?_))
      simp only [rFilter, Finset.mem_filter] at hr hr'
      rw [← pseudoChar_mul_eq_sum_hCoef_filter selbergPsi_isMultiplicative hr.2.1 hr'.2.1 n]
      ring
    rw [← Complex.ofReal_pow, hR2]
    push_cast
    ring
  have hcop : ∀ r r' : ℕ, r ∈ rFilter q R → r' ∈ rFilter q R → ∀ d : ℕ, d ∣ r * r' → ∀ m : ℕ,
      ((1 : DirichletCharacter ℂ q) ((d * m : ℕ) : ℕ))
        = ((1 : DirichletCharacter ℂ q) ((m : ℕ) : ℕ)) := by
    intro r r' hr hr' d hdvd m
    simp only [rFilter, Finset.mem_filter] at hr hr'
    have hcd : Nat.Coprime d q :=
      Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.mul_left hr.2.2 hr'.2.2)
    have hunit : IsUnit ((d : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime d q).mpr hcd
    rw [Nat.cast_mul, map_mul, MulChar.one_apply hunit, one_mul]
  have hL : ∀ n ∈ Finset.Icc 1 ⌈N⌉₊,
      (jutilaB q R N M n : ℂ) * (starRingEnd ℂ) (χ n) * χ n * (n : ℂ) ^ (-s)
      = ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
          * ((∑ d ∈ (r * r').divisors with d ∣ n, hCoef selbergPsi r r' d : ℝ) : ℂ)
          * (((1 : DirichletCharacter ℂ q) n) * (n : ℂ) ^ (-(1 : ℂ) - s)
            * (kern2 ((n : ℝ) / N) - kern2 ((n : ℝ) / M))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hcinv : (n : ℂ) ^ (-(1 : ℂ)) = (n : ℂ)⁻¹ := by
      rw [Complex.cpow_neg, Complex.cpow_one]
    have hcpow : (n : ℂ)⁻¹ * (n : ℂ) ^ (-s) = (n : ℂ) ^ (-(1 : ℂ) - s) := by
      rw [show (-(1 : ℂ) - s) = (-1) + (-s) by ring, Complex.cpow_add _ _ hnc, hcinv]
    have hstep : (jutilaB q R N M n : ℂ) * (starRingEnd ℂ) (χ n) * χ n * (n : ℂ) ^ (-s)
        = ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n : ℝ) : ℂ) ^ 2
          * (((1 : DirichletCharacter ℂ q) n) * (n : ℂ) ^ (-(1 : ℂ) - s)
            * (kern2 ((n : ℝ) / N) - kern2 ((n : ℝ) / M))) := by
      rw [jutilaB_ofReal_eq q R N M hn0, ← hcpow, ← hchar n]
      ring
    rw [hstep, hsq n, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul]
  rw [halaszBTsum_jutilaB_eq_sum χ hM hMN s, Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r' hr' => ?_)
  have hcast : ∀ n : ℕ,
      ((∑ d ∈ (r * r').divisors with d ∣ n, hCoef selbergPsi r r' d : ℝ) : ℂ)
        = ∑ d ∈ (r * r').divisors with d ∣ n, ((hCoef selbergPsi r r' d : ℝ) : ℂ) := by
    intro n
    push_cast
    ring
  have hpull : ∑ n ∈ Finset.Icc 1 ⌈N⌉₊, (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
        * ((∑ d ∈ (r * r').divisors with d ∣ n, hCoef selbergPsi r r' d : ℝ) : ℂ)
        * (((1 : DirichletCharacter ℂ q) n) * (n : ℂ) ^ (-(1 : ℂ) - s)
          * (kern2 ((n : ℝ) / N) - kern2 ((n : ℝ) / M)))
      = (((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ : ℝ) : ℂ)
        * ∑ n ∈ Finset.Icc 1 ⌈N⌉₊, ∑ d ∈ (r * r').divisors with d ∣ n,
            ((hCoef selbergPsi r r' d : ℝ) : ℂ)
              * (((1 : DirichletCharacter ℂ q) n) * (n : ℂ) ^ (-(1 : ℂ) - s)
                * (kern2 ((n : ℝ) / N) - kern2 ((n : ℝ) / M))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hcast, mul_assoc, Finset.sum_mul]
  have hmem : ∀ x y : ℕ,
      (x ∈ Finset.Icc 1 ⌈N⌉₊ ∧ y ∈ (r * r').divisors.filter (fun d => d ∣ x))
        ↔ (x ∈ (Finset.Icc 1 ⌈N⌉₊).filter (fun n => y ∣ n) ∧ y ∈ (r * r').divisors) := by
    intro x y
    simp only [Finset.mem_filter]
    tauto
  rw [hpull, Finset.sum_comm' hmem]
  congr 1
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.mul_sum]
  congr 1
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvdrr : d ∣ r * r' := (Nat.mem_divisors.mp hd).1
  have htsum : (∑' m : ℕ, ((1 : DirichletCharacter ℂ q) m) * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * (kern2 ((d * m : ℝ) / N) - kern2 ((d * m : ℝ) / M)))
      = ∑ m ∈ Finset.Icc 1 ⌈N⌉₊, ((1 : DirichletCharacter ℂ q) m)
          * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
          * (kern2 ((d * m : ℝ) / N) - kern2 ((d * m : ℝ) / M)) := by
    refine tsum_eq_sum ?_
    intro m hm
    simp only [Finset.mem_Icc, not_and, not_le] at hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [Complex.zero_cpow hsne]
    · have hlt := hm hm0
      have hge : N ≤ (d : ℝ) * (m : ℝ) := by
        have h1 : N ≤ ((⌈N⌉₊ : ℕ) : ℝ) := Nat.le_ceil N
        have h2 : ((⌈N⌉₊ : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hlt
        have h3 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      rw [hker0 N hN0 _ hge, hker0 M hM _ (le_trans hMN hge), sub_self, mul_zero]
  have hGeq : ∀ m : ℕ, ((1 : DirichletCharacter ℂ q) ((d * m : ℕ) : ℕ))
        * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * (kern2 (((d * m : ℕ) : ℝ) / N) - kern2 (((d * m : ℕ) : ℝ) / M))
      = ((1 : DirichletCharacter ℂ q) m) * ((d * m : ℕ) : ℂ) ^ (-(1 : ℂ) - s)
        * (kern2 ((d * m : ℝ) / N) - kern2 ((d * m : ℝ) / M)) := by
    intro m
    have hcast2 : (((d * m : ℕ)) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hcop r r' hr hr' d hdvdrr m, hcast2]
  have himg : ((Finset.Icc 1 ⌈N⌉₊).filter (fun m => d * m ≤ ⌈N⌉₊)).image (fun m => d * m)
      = (Finset.Icc 1 ⌈N⌉₊).filter (fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨m, ⟨⟨hm1, _⟩, hdm⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd0.ne' (by omega)), hdm⟩,
        dvd_mul_right d m⟩
    · rintro ⟨⟨hn1, hn2⟩, hdvd⟩
      refine ⟨n / d, ⟨⟨(Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdvd),
        le_trans (Nat.div_le_self n d) hn2⟩, ?_⟩, ?_⟩
      · rw [Nat.mul_div_cancel' hdvd]; exact hn2
      · rw [Nat.mul_div_cancel' hdvd]
  rw [htsum, ← himg,
    Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd0 hab)]
  simp only [hGeq]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro m hm hmnot
  simp only [Finset.mem_Icc] at hm
  simp only [Finset.mem_filter, Finset.mem_Icc, not_and, not_le] at hmnot
  have hgt : ⌈N⌉₊ < d * m := hmnot hm
  have hge : N ≤ (d : ℝ) * (m : ℝ) := by
    have h1 : N ≤ ((⌈N⌉₊ : ℕ) : ℝ) := Nat.le_ceil N
    have h2 : ((⌈N⌉₊ : ℕ) : ℝ) < ((d * m : ℕ) : ℝ) := by exact_mod_cast hgt
    push_cast at h2
    linarith
  rw [hker0 N hN0 _ hge, hker0 M hM _ (le_trans hMN hge), sub_self, mul_zero]

theorem sum_rFilter_totient_div_sq_le (q : ℕ) (R : ℝ) :
    ∑ r ∈ rFilter q R, (Nat.totient r : ℝ) / (r : ℝ) ^ 2 ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ := by
  refine Finset.sum_le_sum (fun r hr => ?_)
  simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr
  have hr1 : 1 ≤ r := hr.1.1
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hphi : (Nat.totient r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.totient_le r
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) ^ 2)]
  rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul]
  exact hphi

/-- `Σ_{r ≤ R} 2^{ω(r)} ≤ Σ τ(r) ≤ R(1 + log R)`. -/
theorem sum_two_pow_card_primeFactors_le {R : ℝ} (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, (2 : ℝ) ^ r.primeFactors.card ≤ R * (1 + Real.log R) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set n : ℕ := ⌊R⌋₊ with hndef
  have hn1 : 1 ≤ n := by
    rw [hndef]
    exact Nat.le_floor (by exact_mod_cast hR)
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hstep1 : ∀ r : ℕ, 0 < r → (2 : ℝ) ^ r.primeFactors.card ≤ (r.divisors.card : ℝ) := by
    intro r hr
    have hcard : r.primeFactors.powerset.card ≤ r.divisors.card := by
      refine Finset.card_le_card_of_injOn (fun S => ∏ p ∈ S, p) ?_ ?_
      · intro S hS
        rw [Finset.mem_coe, Finset.mem_powerset] at hS
        rw [Finset.mem_coe, Nat.mem_divisors]
        refine ⟨Finset.prod_primes_dvd r ?_ ?_, hr.ne'⟩
        · intro p hp
          exact (Nat.prime_of_mem_primeFactors (hS hp)).prime
        · intro p hp
          exact Nat.dvd_of_mem_primeFactors (hS hp)
      · intro S hS T hT hST
        rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
        have h1 : ∀ p ∈ S, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
        have h2 : ∀ p ∈ T, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
        have hST' : (∏ p ∈ S, p) = ∏ p ∈ T, p := hST
        rw [← Nat.primeFactors_prod h1, ← Nat.primeFactors_prod h2, hST']
    rw [Finset.card_powerset] at hcard
    exact_mod_cast hcard
  have hdiv : ∀ r ∈ Finset.Ioc 0 n,
      ((Finset.Ioc 0 n).filter (fun d => d ∣ r)) = r.divisors := by
    intro r hr
    simp only [Finset.mem_Ioc] at hr
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hk0, hkn⟩, hkdvd⟩
      exact ⟨hkdvd, by omega⟩
    · rintro ⟨hkdvd, hr0⟩
      have hkle : k ≤ r := Nat.le_of_dvd (by omega) hkdvd
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · rw [Nat.zero_dvd] at hkdvd; omega
        · exact h
      exact ⟨⟨hk0, by omega⟩, hkdvd⟩
  have hcomm : ∀ x y : ℕ, (x ∈ Finset.Ioc 0 n ∧ y ∈ (Finset.Ioc 0 n).filter (fun d => d ∣ x))
      ↔ (x ∈ (Finset.Ioc 0 n).filter (fun r => y ∣ r) ∧ y ∈ Finset.Ioc 0 n) := by
    intro x y
    simp only [Finset.mem_filter]
    tauto
  have hsumN : ∑ r ∈ Finset.Ioc 0 n, (r.divisors.card) = ∑ d ∈ Finset.Ioc 0 n, (n / d) := by
    calc ∑ r ∈ Finset.Ioc 0 n, (r.divisors.card)
        = ∑ r ∈ Finset.Ioc 0 n, ((Finset.Ioc 0 n).filter (fun d => d ∣ r)).card :=
          Finset.sum_congr rfl (fun r hr => by rw [hdiv r hr])
      _ = ∑ r ∈ Finset.Ioc 0 n, ∑ _d ∈ (Finset.Ioc 0 n).filter (fun d => d ∣ r), 1 :=
          Finset.sum_congr rfl (fun r _ => Finset.card_eq_sum_ones _)
      _ = ∑ d ∈ Finset.Ioc 0 n, ∑ _r ∈ (Finset.Ioc 0 n).filter (fun r => d ∣ r), 1 :=
          Finset.sum_comm' hcomm
      _ = ∑ d ∈ Finset.Ioc 0 n, ((Finset.Ioc 0 n).filter (fun r => d ∣ r)).card :=
          Finset.sum_congr rfl (fun d _ => (Finset.card_eq_sum_ones _).symm)
      _ = ∑ d ∈ Finset.Ioc 0 n, (n / d) :=
          Finset.sum_congr rfl (fun d _ => Nat.Ioc_filter_dvd_card_eq_div n d)
  have hle : ∀ d : ℕ, ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < (d : ℝ))]
      exact_mod_cast Nat.div_mul_le_self n d
  have hstep2 : ∑ r ∈ Finset.Ioc 0 n, (r.divisors.card : ℝ) ≤ (n : ℝ) * (1 + Real.log n) := by
    have hcast : ∑ r ∈ Finset.Ioc 0 n, ((r.divisors.card : ℕ) : ℝ)
        = ((∑ r ∈ Finset.Ioc 0 n, (r.divisors.card) : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, hsumN]
    push_cast
    refine le_trans (Finset.sum_le_sum (fun d _ => hle d)) ?_
    have hsum2 : ∑ d ∈ Finset.Ioc 0 n, (n : ℝ) / (d : ℝ)
        = (n : ℝ) * ∑ d ∈ Finset.Ioc 0 n, ((d : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by rw [div_eq_mul_inv])
    rw [hsum2, ← hIcc]
    exact mul_le_mul_of_nonneg_left (sum_inv_Icc_le n) (by positivity)
  rw [hIcc]
  refine le_trans (Finset.sum_le_sum (fun r hr => hstep1 r ?_)) ?_
  · simp only [Finset.mem_Ioc] at hr
    exact hr.1
  refine le_trans hstep2 ?_
  have hnR : (n : ℝ) ≤ R := by rw [hndef]; exact Nat.floor_le hR0.le
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog : Real.log (n : ℝ) ≤ Real.log R := Real.log_le_log (by linarith) hnR
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1R
  nlinarith [hnR, hlog, hlogn, hn1R]

/-- `Σ'_{r,r'} (rr')⁻¹·Σ_{d ∣ rr'} |h(d; r, r')| ≤ (R(1 + log R))²`. -/
theorem sum_rFilter_abs_hCoef_le (q : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (r : ℝ)⁻¹ * (r' : ℝ)⁻¹
        * ∑ d ∈ (r * r').divisors, |hCoef selbergPsi r r' d|
      ≤ (R * (1 + Real.log R)) ^ 2 := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hlogR : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR
  have hkey : ∀ r : ℕ, Squarefree r → (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
      ≤ 2 ^ r.primeFactors.card := by
    intro r hr
    have hprodR : (∏ p ∈ r.primeFactors, (p : ℝ)) = (r : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
    have heq : (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
        = ∏ p ∈ r.primeFactors, (((p : ℝ) + 1) / (p : ℝ)) := by
      rw [Finset.prod_div_distrib, hprodR]
      ring
    rw [heq, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      positivity
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      rw [div_le_iff₀ (by linarith)]
      linarith
  have hterm : ∀ r ∈ rFilter q R, ∀ r' ∈ rFilter q R,
      (r : ℝ)⁻¹ * (r' : ℝ)⁻¹ * ∑ d ∈ (r * r').divisors, |hCoef selbergPsi r r' d|
        ≤ (2 : ℝ) ^ r.primeFactors.card * (2 : ℝ) ^ r'.primeFactors.card := by
    intro r hr r' hr'
    simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr hr'
    have hsq : Squarefree r := hr.2.1
    have hsq' : Squarefree r' := hr'.2.1
    have hbound := hCoef_abs_sum_le hsq hsq'
    have hnn : (0 : ℝ) ≤ (r : ℝ)⁻¹ * (r' : ℝ)⁻¹ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hbound hnn
    refine le_trans h1 ?_
    have h2 := hkey r hsq
    have h3 := hkey r' hsq'
    have hp2 : (0 : ℝ) ≤ (r' : ℝ)⁻¹ * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1) := by positivity
    calc (r : ℝ)⁻¹ * (r' : ℝ)⁻¹ * ((∏ p ∈ r.primeFactors, ((p : ℝ) + 1))
            * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1))
        = ((r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1))
          * ((r' : ℝ)⁻¹ * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1)) := by ring
      _ ≤ (2 : ℝ) ^ r.primeFactors.card * (2 : ℝ) ^ r'.primeFactors.card :=
          mul_le_mul h2 h3 hp2 (by positivity)
  refine le_trans (Finset.sum_le_sum (fun r hr =>
    Finset.sum_le_sum (fun r' hr' => hterm r hr r' hr'))) ?_
  rw [← Finset.sum_mul_sum]
  have hsubset : rFilter q R ⊆ Finset.Icc 1 ⌊R⌋₊ := by
    simp only [rFilter]
    exact Finset.filter_subset _ _
  have hsub : ∑ r ∈ rFilter q R, (2 : ℝ) ^ r.primeFactors.card
      ≤ ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, (2 : ℝ) ^ r.primeFactors.card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
  have hb := le_trans hsub (sum_two_pow_card_primeFactors_le hR)
  have hnn : (0 : ℝ) ≤ ∑ r ∈ rFilter q R, (2 : ℝ) ^ r.primeFactors.card :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hRR : (0 : ℝ) ≤ R * (1 + Real.log R) := mul_nonneg hR0.le (by linarith)
  calc (∑ r ∈ rFilter q R, (2 : ℝ) ^ r.primeFactors.card)
        * ∑ r' ∈ rFilter q R, (2 : ℝ) ^ r'.primeFactors.card
      ≤ (R * (1 + Real.log R)) * (R * (1 + Real.log R)) := mul_le_mul hb hb hnn hRR
    _ = (R * (1 + Real.log R)) ^ 2 := by ring

/-- The remainder is small: `‖I(s)‖ ≤ 73·qT·M^{−1/2}·(R(1 + log R))²` for `|Im s| ≤ 2T`, `T ≥ 2`. -/
theorem norm_jutilaI_le [NeZero q] (hq : 2 ≤ q) {R : ℝ} (hR : 1 ≤ R) {N M : ℝ} (hM : 2 ≤ M)
    (hMN : M ≤ N) {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 1 / 60) {T : ℝ} (hT : 2 ≤ T)
    (hsT : |s.im| ≤ 2 * T) :
    ‖jutilaI q R N M s‖ ≤ 73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)) * (R * (1 + Real.log R)) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hT0 : (0 : ℝ) < T := by linarith
  have hm : (0 : ℝ) < 29 / 60 := by norm_num
  have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hs1re : (1 + s).re = 1 + s.re := by simp
  have habsσ0 : |(-1 / 2 - s.re : ℝ)| = 1 / 2 + s.re := by
    rw [abs_of_neg (by linarith : (-1 / 2 - s.re : ℝ) < 0)]; ring
  have habsσ1 : |(-1 / 2 - s.re : ℝ) + 1| = 1 / 2 - s.re := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < -1 / 2 - s.re + 1)]; ring
  have habsσ2 : |(-1 / 2 - s.re : ℝ) + 2| = 3 / 2 - s.re := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < -1 / 2 - s.re + 2)]; ring
  have hnum : 2 * ((7 / 2 + 3 * |s.im|) / (29 / 60 : ℝ) ^ 2 + 3 / (29 / 60 : ℝ)) ≤ 73 * T := by
    have h1 : ((29 / 60 : ℝ)) ^ 2 = 841 / 3600 := by norm_num
    rw [h1]
    linarith [hsT, hT]
  have hd_bound : ∀ d : ℕ, 0 < d →
      ‖(d : ℂ) ^ (-(1 : ℂ) - s)‖
        * ‖((1 / (2 * Real.pi)) • ∫ t : ℝ,
            resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I))‖
      ≤ 73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)) := by
    intro d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hNd : (0 : ℝ) < N / (d : ℝ) := div_pos hN0 hd0
    have hMd : (0 : ℝ) < M / (d : ℝ) := div_pos hM0 hd0
    have hMNd : M / (d : ℝ) ≤ N / (d : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hMN (inv_nonneg.mpr hd0.le)
      rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h
    have hKnn : (0 : ℝ) ≤ (M / (d : ℝ)) ^ (-1 / 2 - s.re) := Real.rpow_nonneg hMd.le _
    have hptw : ∀ t : ℝ,
        ‖resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I)‖
          ≤ (4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
            * ((7 / 2 + 3 * |s.im|) * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
              + 3 * (|t| * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)) := by
      intro t
      have hwre : ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I).re = -1 / 2 - s.re := by simp
      have hre1 : (1 + s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_I_re,
          Complex.ofReal_im, neg_zero, add_zero]
        ring
      have him1 : (1 + s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)).im = s.im + t := by
        simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.mul_I_im,
          Complex.ofReal_re, zero_add]
      have hw1 : (1 : ℝ) / 2 ≤ (1 + s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)).re := by
        rw [hre1]
      have hws : (1 : ℝ) / 2 ≤ ‖s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)‖ := by
        have hre : (s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)).re
            = s.re + (-1 / 2 - s.re) := by simp
        have h := Complex.abs_re_le_norm (s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I))
        rw [hre, abs_of_nonpos (by linarith : s.re + (-1 / 2 - s.re) ≤ 0)] at h
        linarith
      have hbase := norm_resIntegrand_le q hM1 hMN hd s _ hw1 hws
      rw [hwre] at hbase
      have hkersum : (N / (d : ℝ)) ^ (-1 / 2 - s.re) + (M / (d : ℝ)) ^ (-1 / 2 - s.re)
          ≤ 2 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) := by
        have h := Real.rpow_le_rpow_of_nonpos hMd hMNd (by linarith : (-1 / 2 - s.re : ℝ) ≤ 0)
        linarith
      have hnb : ‖1 + s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)‖ ≤ 1 / 2 + |s.im| + |t| := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
        rw [hre1, him1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        linarith [abs_add_le s.im t]
      have hcube := norm_inv_denom2_cubic_le_of_min hm (by rw [habsσ0]; linarith)
        (by rw [habsσ1]; linarith) (by rw [habsσ2]; linarith) t
      have hstep := mul4_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ))
        (b₁ := (N / (d : ℝ)) ^ (-1 / 2 - s.re) + (M / (d : ℝ)) ^ (-1 / 2 - s.re))
        (b₂ := 2 * (M / (d : ℝ)) ^ (-1 / 2 - s.re))
        (c₁ := (q : ℝ) * (2 + 3 * ‖1 + s + ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)‖))
        (c₂ := (q : ℝ) * (2 + 3 * (1 / 2 + |s.im| + |t|)))
        (e₁ := ‖(((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I)
          * ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I + 1)
          * ((((-1 / 2 - s.re : ℝ)) : ℂ) + (t : ℂ) * I + 2))⁻¹‖)
        (e₂ := (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
        (by norm_num)
        (add_nonneg (Real.rpow_nonneg hNd.le _) (Real.rpow_nonneg hMd.le _))
        (by positivity) (norm_nonneg _) le_rfl hkersum (by nlinarith [hq0, hnb]) hcube
      refine (hbase.trans hstep).trans (le_of_eq ?_)
      ring
    have hInt : Integrable (fun t : ℝ =>
        resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I)) :=
      integrable_resIntegrand_line q hM1 hMN hd s (by rw [hs1re]; linarith)
        (by rw [abs_of_nonpos (by linarith : s.re + (-1 / 2 - s.re) ≤ 0)]; linarith)
        hm (by rw [habsσ0]; linarith) (by rw [habsσ1]; linarith) (by rw [habsσ2]; linarith)
    have hIg : Integrable (fun t : ℝ =>
        (4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
          * ((7 / 2 + 3 * |s.im|) * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
            + 3 * (|t| * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹))) :=
      ((((integrable_inv_sq_add_sq_rpow hm).const_mul (7 / 2 + 3 * |s.im|)).add
        ((integrable_abs_mul_inv_sq_add_sq_rpow hm).const_mul 3)).const_mul _)
    have hIval : (∫ t : ℝ, (4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
          * ((7 / 2 + 3 * |s.im|) * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
            + 3 * (|t| * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)))
        = (4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
          * ((7 / 2 + 3 * |s.im|) * (∫ t : ℝ, (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
            + 3 * ∫ t : ℝ, |t| * (((29 / 60 : ℝ) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
        ((integrable_inv_sq_add_sq_rpow hm).const_mul _)
        ((integrable_abs_mul_inv_sq_add_sq_rpow hm).const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hC : (0 : ℝ) ≤ 4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hKnn) hq0
    have hnormint : ‖∫ t : ℝ, resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ (4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
          * ((7 / 2 + 3 * |s.im|) * (Real.pi / (29 / 60 : ℝ) ^ 2)
            + 3 * (Real.pi / (29 / 60 : ℝ))) := by
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
      refine le_trans (MeasureTheory.integral_mono hInt.norm hIg hptw) ?_
      rw [hIval]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have hA : (0 : ℝ) ≤ 7 / 2 + 3 * |s.im| := by positivity
      have h1 := mul_le_mul_of_nonneg_left (integral_inv_sq_add_sq_rpow_le hm) hA
      have h2 := integral_abs_mul_inv_sq_add_sq_rpow_le hm
      linarith
    have hnormd : ‖(d : ℂ) ^ (-(1 : ℂ) - s)‖ = (d : ℝ) ^ (-1 - s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hd]
      congr 1
    have hsmul : ‖((1 / (2 * Real.pi)) • ∫ t : ℝ,
        resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I))‖
        = (1 / (2 * Real.pi)) * ‖∫ t : ℝ,
          resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcancel : (1 / (2 * Real.pi)) * ((4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
          * ((7 / 2 + 3 * |s.im|) * (Real.pi / (29 / 60 : ℝ) ^ 2)
            + 3 * (Real.pi / (29 / 60 : ℝ))))
        = 2 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ)
          * ((7 / 2 + 3 * |s.im|) / (29 / 60 : ℝ) ^ 2 + 3 / (29 / 60 : ℝ)) := by
      field_simp
      ring
    have hcol : (d : ℝ) ^ (-1 - s.re) * (M / (d : ℝ)) ^ (-1 / 2 - s.re) ≤ M ^ (-(1 / 2 : ℝ)) := by
      have hsplit : (M / (d : ℝ)) ^ (-1 / 2 - s.re)
          = M ^ (-1 / 2 - s.re) * ((d : ℝ) ^ (-1 / 2 - s.re))⁻¹ := by
        rw [Real.div_rpow hM0.le hd0.le, div_eq_mul_inv]
      have hdd : (d : ℝ) ^ (-1 - s.re) * ((d : ℝ) ^ (-1 / 2 - s.re))⁻¹
          = (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg hd0.le, ← Real.rpow_add hd0]
        congr 1
        ring
      rw [hsplit]
      calc (d : ℝ) ^ (-1 - s.re) * (M ^ (-1 / 2 - s.re) * ((d : ℝ) ^ (-1 / 2 - s.re))⁻¹)
          = ((d : ℝ) ^ (-1 - s.re) * ((d : ℝ) ^ (-1 / 2 - s.re))⁻¹) * M ^ (-1 / 2 - s.re) := by
            ring
        _ = (d : ℝ) ^ (-(1 / 2 : ℝ)) * M ^ (-1 / 2 - s.re) := by rw [hdd]
        _ ≤ 1 * M ^ (-1 / 2 - s.re) :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_one_of_one_le_of_nonpos hd1 (by norm_num))
              (Real.rpow_nonneg hM0.le _)
        _ = M ^ (-(1 / 2 : ℝ)) * M ^ (-s.re) := by
            rw [one_mul, ← Real.rpow_add hM0]
            congr 1
            ring
        _ ≤ M ^ (-(1 / 2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith))
              (Real.rpow_nonneg hM0.le _)
        _ = M ^ (-(1 / 2 : ℝ)) := mul_one _
    rw [hnormd, hsmul]
    have hA0 : (0 : ℝ) ≤ (7 / 2 + 3 * |s.im|) / (29 / 60 : ℝ) ^ 2 + 3 / (29 / 60 : ℝ) := by
      positivity
    calc (d : ℝ) ^ (-1 - s.re) * ((1 / (2 * Real.pi))
          * ‖∫ t : ℝ, resIntegrand q N M d s (((-1 / 2 - s.re : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ (d : ℝ) ^ (-1 - s.re) * ((1 / (2 * Real.pi))
            * ((4 * (M / (d : ℝ)) ^ (-1 / 2 - s.re) * (q : ℝ))
              * ((7 / 2 + 3 * |s.im|) * (Real.pi / (29 / 60 : ℝ) ^ 2)
                + 3 * (Real.pi / (29 / 60 : ℝ))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnormint (by positivity))
            (Real.rpow_nonneg hd0.le _)
      _ = (d : ℝ) ^ (-1 - s.re) * (M / (d : ℝ)) ^ (-1 / 2 - s.re)
            * (2 * (q : ℝ) * ((7 / 2 + 3 * |s.im|) / (29 / 60 : ℝ) ^ 2
              + 3 / (29 / 60 : ℝ))) := by rw [hcancel]; ring
      _ ≤ M ^ (-(1 / 2 : ℝ)) * (2 * (q : ℝ) * ((7 / 2 + 3 * |s.im|) / (29 / 60 : ℝ) ^ 2
            + 3 / (29 / 60 : ℝ))) :=
          mul_le_mul_of_nonneg_right hcol (by positivity)
      _ ≤ M ^ (-(1 / 2 : ℝ)) * ((q : ℝ) * (73 * T)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hM0.le _)
          have h := mul_le_mul_of_nonneg_left hnum hq0
          linarith
      _ = 73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)) := by ring
  have hC0 : (0 : ℝ) ≤ 73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hq0 hT0.le)) (Real.rpow_nonneg hM0.le _)
  have houter : ‖jutilaI q R N M s‖
      ≤ ∑ r ∈ rFilter q R, ∑ r' ∈ rFilter q R, (r : ℝ)⁻¹ * (r' : ℝ)⁻¹
          * ∑ d ∈ (r * r').divisors,
            |hCoef selbergPsi r r' d| * (73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ))) := by
    simp only [jutilaI]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r' _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹ * (r' : ℝ)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hd_bound d hd0) (abs_nonneg _)
  refine houter.trans ?_
  have hfact : ∀ r r' : ℕ, (r : ℝ)⁻¹ * (r' : ℝ)⁻¹
        * ∑ d ∈ (r * r').divisors,
          |hCoef selbergPsi r r' d| * (73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)))
      = (73 * ((q : ℝ) * T) * M ^ (-(1 / 2 : ℝ)))
        * ((r : ℝ)⁻¹ * (r' : ℝ)⁻¹ * ∑ d ∈ (r * r').divisors, |hCoef selbergPsi r r' d|) := by
    intro r r'
    rw [← Finset.sum_mul]
    ring
  simp only [hfact, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_rFilter_abs_hCoef_le q hR) hC0

/-- **The W9b exit rows** (each INVOKES a frozen row and PRODUCES its value — `rw` with the row,
then `norm_num`): the removable point's value (`log 5`, the `40/8` reduced), and the closed form
at `s = −1` — `(N − M)/3 = 32/3` at `(40, 8)`, the numeral on the right of the `example`. Not
`s = 1`: there both sides are Lean-`0` (the denominator's `(1 − s)`; the dslope's `(w + 1)`) and any
numerator passes (the verdict's kill 12c). -/
example : resKernel 0 40 8 = (Real.log 5 : ℂ) := by
  rw [resKernel_zero (by norm_num) (by norm_num)]; norm_num

example : resKernel (-1) 40 8 = 32 / 3 := by
  rw [resKernel_of_ne_zero (by norm_num) 40 8]; norm_num [Complex.cpow_one]

end Salt.SW
