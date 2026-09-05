/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.PseudoCharEuler
import Salt.SW.CoprimeHarmonic
import Salt.SW.Kernel2
import Salt.SW.BvWeight
import Salt.SW.Growth
import Salt.SW.ContourShift
import Salt.SW.Psi1Identity

/-!
# B2 W7 — Jutila's Lemma 6 (L6): the detected Dirichlet polynomial and its floor at a zero

Jutila 1977, p.50, (2.10)–(2.11), for the Riesz weight `K(u) = (1 − u)²₊` in place of
`e^{−n/X}` (design v2 §1 F5 (ii)): with `a(n) = Σ_{d ∣ n} λ_d` the two-level Barban–Vehov
weight (`bvWeight`), `ψ = μφ` (`selbergPsi`), and `Σ'_{r ≤ R}` over square-free `r` coprime to
`q` (`rFilter`),

    g(s,χ) = Σ_{z₁ < n ≤ x} a(n) χ(n) K(n/x) n^{−s} Σ'_r r⁻¹ ψ_r(n)          (`jutilaDetector`)

satisfies, at every zero `ρ = β + iγ` of `L(s,χ)` with `119/120 ≤ β < 1`, `|γ| ≤ T`,

    ‖g(ρ,χ)‖ ≥ (1 − 1/x)²·(6/π²)·(φ(q)/q)·log R − E,
    E = 25·(T + 2)·√q·(1 + log q)·√z₂·R^{3/2}·x^{1/2 − β}        (`jutilaDetector_floor_at_zero`),

and under F5's corrected table `(ε, b, a₁, a₂, c) = (1/120, 1/10, 3, 7/2, 13/2)` with
`D = qT ≥ 10²⁰` the floor `(3/π²)(φ(q)/q)·log R` (`jutilaDetector_floor_F5`).

## The mechanism, staged

1. The full sum `Σ_{n ≤ x}` splits as the `n = 1` term `K(1/x)·Σ'_r r⁻¹` plus the detector, because
   `a(1) = 1` and `a(n) = 0` on `2 ≤ n ≤ z₁` (W6a's two identities — Lemma 6's first line).
2. Mellin: `K(n/x) = (1/2π)∫ 2 (x/n)^{c+it}/((c+it)(c+it+1)(c+it+2)) dt` (`kernel_identity_2`), the
   dominated swap `kernel_sum_swap_2`, `riesz_tsum_eq`, and the `r`-summed (2.2)
   (`LSeries_jutila_coeff_sum_eq`) give the full sum at `ρ` as ONE vertical integral of
   `2 x^w L(ρ+w,χ) M(ρ+w)/(w(w+1)(w+2))` on `Re w = c > 1 − β`.
3. THE CONTOUR NODE: the shift from `Re w = 2 − β` to `Re w = 1/2 − β` crosses `w = 0`, where the
   singularity is REMOVABLE because `L(ρ,χ) = 0`. The integrand is `dslope φ 0` for
   `φ(w) = 2 x^w L(ρ+w) M(ρ+w)/((w+1)(w+2))` (`φ(0) = 0`), so the landed `rectBI_dslope_eq_zero`
   applies on the tall rectangle; the horizontal edges vanish like `T'^{−2}` against the corpus's
   `(1 + |t|)` growth (`LFunction_growth`, which is why the initial line is `Re(ρ + w) = 2`),
   and the two verticals are taken to improper integrals by `intervalIntegral_tendsto_integral`.
4. On `Re w = 1/2 − β`: `‖M‖ ≤ 2√z₂ R^{3/2}` (`|λ_d| ≤ 1`, `|ψ_r(d)| ≤ (r,d)`, the local
   factor `≤ (r/(r,d))^{3/2}`), the CUBIC decay of the kernel with `m = 59/120` (the least
   distance of `1/2 − β` from `0, −1, −2` on `119/120 ≤ β < 1`), and `∫(m²+t²)^{−3/2} ≤ π/m²`,
   `∫|t|(m²+t²)^{−3/2} ≤ π/m` — the constant `25` is the desk's arithmetic
   `(3/π)·2·[(3/2 + T)π/m² + π/m] = 24.82·T + 49.43 ≤ 25(T + 2)`.
5. The floor is the reverse triangle inequality against W2's uniform L5.

## The honest label

Nothing here bears on twin primes or on the crown's conditions: Lemma 6 is one input of the
density theorem's assembly (W9). The Mellin constant, the growth bound and the kernel decay are
the corpus's own. `LFunction_growth` is the Pólya–Vinogradov grade — `√q(1 + log q)(1 + ‖s‖)`
from Abel summation against `|Σ χ| ≤ √q(1 + log q)` (`Growth.lean:186`, `:400`) — WEAKER than
convexity by `q^{1/4}` and `|t|^{3/4}` on the critical line; Jutila's `(qT)^{(1−σ)/2+ε}` is not
used, and the exponent table absorbs the loss with slack `D^{−71/240}`. So `E` carries
`√q(1 + log q)·(T + 2)` where Jutila has `D^{1/2+ε}`. The threshold `D ≥ 10²⁰` is where the
desk's chain closes with room (it FAILS at `10¹⁸`, ratio `1.09`; closes at `10¹⁹`, ratio `0.58`;
at `10²⁰`, ratio `0.31`). The trivial `φ(q) ≥ 1` does NOT close the corollary;
`q/φ(q) ≤ ω(q) + 1 ≤ log q/log 2 + 1` does.
`ζ` never enters. No `vonMangoldt` detour: the coefficients are products of `moebius`, `totient`
and `χ` values, ℝ-valued and cast once.

## The measured receipts behind these statements (`h2c-desk/w7_receipts.py`)

`max |bvWeight| = 1.000000` over `2 ≤ z₁ < z₂ ≤ 40`, `d ≤ 80`; `max |a(n)|/τ(n) = 1.000000`;
the local-factor bound `∏_{p∣t}(1 + √p) ≤ t^{3/2}` with max ratio `1.000000` on `t ≤ 500` (FALSE
at `t = 0`: `1 ≤ 0`); `Σ_{d ≤ N} d^{−1/2} ≤ 2√N` with max ratio `0.9948`; the cubic negative-line
bound with min ratio `1.000000`; `∫(m²+t²)^{−3/2} = 2/m² = 8.2735 ≤ π/m² = 12.9960`,
`∫|t|(m²+t²)^{−3/2} = 2/m = 4.0678 ≤ π/m = 6.3897`; the split identity at `s = 2`, `x = 12`,
`(z₁, z₂, R) = (4, 16, 6)`, `χ mod 5`: exact to `4.6e−17`, and with the ONE-LEVEL weight
`θ^{(16)}` in place of `λ` it FAILS by `1.72e−2` (`a(2) = a(4) = 1/4`, `a(3) = 0.396`); the Mellin
representation at `ρ = 0.9 + 0.3i`, `c = 1.2`: `1.69276 + 0.02077i` on both sides,
`|diff| = 3.8e−6`.
-/

open MeasureTheory Complex DirichletCharacter ArithmeticFunction

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-! ## The objects -/

/-- The level set of Lemma 6's `r`-sum: square-free `r ≤ R` coprime to `q` — W2's filter, spelled
identically, so `sum_sf_coprime_inv_ge` applies to the `n = 1` term without a reindex. -/
def rFilter (q : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q)

/-- The detector coefficient `a(n)·χ(n)·Σ'_r r⁻¹ ψ_r(n)` — EXACTLY the coefficient of the
`r`-summed (2.2) (`LSeries_jutila_coeff_sum_eq`) at `ξ = bvWeight z₁ z₂`, `f = selbergPsi`,
`S = rFilter q R`; ℝ-valued pieces cast once. -/
def jutilaCoeff (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) (n : ℕ) : ℂ :=
  ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d : ℝ) : ℂ) * χ n
    * ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n : ℝ) : ℂ)

/-- The `r`-averaged mollifier `M(s) = Σ'_r r⁻¹·M(s, χ, ψ_r)` of (2.11), an entire finite Dirichlet
polynomial. -/
def jutilaMollifier (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ : ℂ) * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s

/-- The full smoothed sum `Σ_{n ≤ x} a(n)χ(n)(Σ'_r r⁻¹ψ_r(n)) n^{−s} K(n/x)`. -/
def jutilaFull (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-s) * kern2 ((n : ℝ) / x)

/-- **Jutila's detector** `g(s,χ)` of Lemma 6 with the Riesz weight: the same sum over
`z₁ < n ≤ x`. -/
def jutilaDetector (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc z₁ ⌊x⌋₊, jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-s) * kern2 ((n : ℝ) / x)

/-- The vertical integrand of (2.11): `F(w) = 2 x^w L(ρ+w,χ) M(ρ+w) / (w(w+1)(w+2))`. -/
def jutilaIntegrand [NeZero q] (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) (ρ w : ℂ) : ℂ :=
  2 * (x : ℂ) ^ w * LFunction χ (ρ + w) * jutilaMollifier χ z₁ z₂ R (ρ + w)
    / (w * (w + 1) * (w + 2))

/-- The contour node's analytic function `φ(w) = w·F(w) = 2 x^w L(ρ+w,χ) M(ρ+w) / ((w+1)(w+2))`:
holomorphic on `Re w > −1`, and `φ(0) = 0` at a zero `ρ` — so `F = dslope φ 0` off `0`. -/
def jutilaPhi [NeZero q] (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) (ρ w : ℂ) : ℂ :=
  2 * (x : ℂ) ^ w * LFunction χ (ρ + w) * jutilaMollifier χ z₁ z₂ R (ρ + w) / ((w + 1) * (w + 2))

/-! ## (i) The weight and the split (Lemma 6's first line) -/

theorem abs_bvWeight_le_one {z₁ z₂ d : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) :
    |bvWeight z₁ z₂ d| ≤ 1 := by
  have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one (n := d)
  rcases le_or_gt d z₁ with hd | hd
  · rw [bvWeight_eq_moebius_of_le hz₁ hz hd]
    exact hmu
  rcases le_or_gt d z₂ with hd2 | hd2
  · rw [bvWeight_eq_of_mem hz₁ hz ⟨hd.le, hd2⟩]
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hz₁0 : (0 : ℝ) < (z₁ : ℝ) := by exact_mod_cast (by omega : 0 < z₁)
    have hz₂0 : (0 : ℝ) < (z₂ : ℝ) := by exact_mod_cast (by omega : 0 < z₂)
    have hz₁d : (z₁ : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
    have hdz₂ : (d : ℝ) ≤ (z₂ : ℝ) := by exact_mod_cast hd2
    have hA0 : 0 ≤ Real.log ((z₂ : ℝ) / d) := Real.log_nonneg ((one_le_div hd0).mpr hdz₂)
    have hAB : Real.log ((z₂ : ℝ) / d) ≤ Real.log ((z₂ : ℝ) / z₁) :=
      Real.log_le_log (div_pos hz₂0 hd0) (div_le_div_of_nonneg_left hz₂0.le hz₁0 hz₁d)
    have hB0 : 0 < Real.log ((z₂ : ℝ) / z₁) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hz₁0, one_mul]
      exact_mod_cast hz
    rw [abs_div, abs_mul, abs_of_nonneg hA0, abs_of_pos hB0, div_le_one hB0]
    nlinarith [hmu, hA0, hAB, abs_nonneg ((moebius d : ℤ) : ℝ)]
  · rw [bvWeight_eq_zero_of_gt hz hd2, abs_zero]
    norm_num

theorem abs_sum_bvWeight_divisors_le_card {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) (n : ℕ) :
    |∑ d ∈ n.divisors, bvWeight z₁ z₂ d| ≤ (n.divisors.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ d ∈ n.divisors, |bvWeight z₁ z₂ d| ≤ ∑ _d ∈ n.divisors, (1 : ℝ) :=
    Finset.sum_le_sum (fun d _ => abs_bvWeight_le_one hz₁ hz)
  simpa using h1

theorem jutilaCoeff_zero (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) :
    jutilaCoeff χ z₁ z₂ R 0 = 0 := by
  simp [jutilaCoeff]

theorem jutilaCoeff_one (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂)
    (R : ℝ) :
    jutilaCoeff χ z₁ z₂ R 1 = ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) := by
  have hps : ∀ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r 1 = (r : ℝ)⁻¹ := by
    intro r _
    rw [pseudoChar_one_right selbergPsi_isMultiplicative r, mul_one]
  simp only [jutilaCoeff, sum_bvWeight_divisors_one hz₁ hz, Nat.cast_one, map_one,
    Complex.ofReal_one, one_mul, mul_one]
  rw [Finset.sum_congr rfl hps]

theorem jutilaCoeff_eq_zero_of_le (χ : DirichletCharacter ℂ q) {z₁ z₂ n : ℕ} (hz : z₁ < z₂)
    (h1 : 2 ≤ n) (h2 : n ≤ z₁) (R : ℝ) :
    jutilaCoeff χ z₁ z₂ R n = 0 := by
  simp [jutilaCoeff, sum_bvWeight_divisors_eq_zero hz h1 h2]

theorem jutilaFull_eq_add_detector (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁)
    (hz : z₁ < z₂) (R : ℝ) {x : ℝ} (hx : 1 ≤ x) (s : ℂ) :
    jutilaFull χ z₁ z₂ R x s
      = ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x)
        + jutilaDetector χ z₁ z₂ R x s := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hnotmem : (1 : ℕ) ∉ Finset.Ioc z₁ ⌊x⌋₊ := by
    simp only [Finset.mem_Ioc, not_and, not_le]
    intro h
    omega
  have hsub : insert (1 : ℕ) (Finset.Ioc z₁ ⌊x⌋₊) ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn'
    · exact Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
    · rw [Finset.mem_Ioc] at hn'
      exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  have hzero : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n ∉ insert (1 : ℕ) (Finset.Ioc z₁ ⌊x⌋₊) →
      jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-s) * kern2 ((n : ℝ) / x) = 0 := by
    intro n hn hn2
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_insert] at hn2
    obtain ⟨hne, hIoc⟩ := not_or.mp hn2
    have h2 : n ≤ z₁ := by
      by_contra hcon
      exact hIoc (Finset.mem_Ioc.mpr ⟨not_le.mp hcon, hn.2⟩)
    have h1n : 2 ≤ n := by
      have := hn.1
      omega
    rw [jutilaCoeff_eq_zero_of_le χ hz h1n h2 R, zero_mul, zero_mul]
  simp only [jutilaFull, jutilaDetector]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_insert hnotmem]
  congr 1
  simp only [Nat.cast_one, Complex.one_cpow, mul_one]
  rw [jutilaCoeff_one χ hz₁ hz R]

/-! ### Product monotonicity helpers (nonnegative reals), used from (ii) on -/

private lemma mul2_le {a₁ a₂ b₁ b₂ : ℝ} (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁) (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ ≤ a₂ * b₂ :=
  mul_le_mul ha hb hb0 (ha0.trans ha)

private lemma mul3_le {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁) (hc0 : 0 ≤ c₁)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) : a₁ * b₁ * c₁ ≤ a₂ * b₂ * c₂ :=
  mul2_le (mul_nonneg ha0 hb0) hc0 (mul2_le ha0 hb0 ha hb) hc

private lemma mul4_le {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ} (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁)
    (hc0 : 0 ≤ c₁) (hd0 : 0 ≤ d₁) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂)
    (hd : d₁ ≤ d₂) : a₁ * b₁ * c₁ * d₁ ≤ a₂ * b₂ * c₂ * d₂ :=
  mul2_le (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd0 (mul3_le ha0 hb0 hc0 ha hb hc) hd

private lemma mul5_le {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : ℝ} (ha0 : 0 ≤ a₁) (hb0 : 0 ≤ b₁)
    (hc0 : 0 ≤ c₁) (hd0 : 0 ≤ d₁) (he0 : 0 ≤ e₁) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) (he : e₁ ≤ e₂) :
    a₁ * b₁ * c₁ * d₁ * e₁ ≤ a₂ * b₂ * c₂ * d₂ * e₂ :=
  mul2_le (mul_nonneg (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd0) he0
    (mul4_le ha0 hb0 hc0 hd0 ha hb hc hd) he

private lemma mul6_le {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : ℝ} (ha0 : 0 ≤ a₁)
    (hb0 : 0 ≤ b₁) (hc0 : 0 ≤ c₁) (hd0 : 0 ≤ d₁) (he0 : 0 ≤ e₁) (hf0 : 0 ≤ f₁)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) (he : e₁ ≤ e₂)
    (hf : f₁ ≤ f₂) : a₁ * b₁ * c₁ * d₁ * e₁ * f₁ ≤ a₂ * b₂ * c₂ * d₂ * e₂ * f₂ :=
  mul2_le (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd0) he0) hf0
    (mul5_le ha0 hb0 hc0 hd0 he0 ha hb hc hd he) hf

/-! ## (ii) The sizes on the strip `Re s ≥ 1/2` -/

theorem norm_jutilaLocal_selbergPsi_le (χ : DirichletCharacter ℂ q) {t : ℕ} (ht : t ≠ 0) {s : ℂ}
    (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖jutilaLocal selbergPsi χ t s‖ ≤ (t : ℝ) ^ (3 / 2 : ℝ) := by
  refine (norm_jutilaLocal_le χ selbergPsi t s).trans ?_
  have hstep : ∀ p ∈ t.primeFactors,
      1 + |selbergPsi p - 1| * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (3 / 2 : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have habs : |selbergPsi p - 1| = (p : ℝ) := by
      rw [selbergPsi_apply_prime hpp, show (1 : ℝ) - (p : ℝ) - 1 = -(p : ℝ) by ring, abs_neg,
        abs_of_nonneg hp0.le]
    have hexp : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hmulid : (p : ℝ) * (p : ℝ) ^ (-(1 / 2) : ℝ) = Real.sqrt p := by
      have h1 : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-(1 / 2) : ℝ) = (p : ℝ) ^ ((1 : ℝ) + -(1 / 2)) :=
        (Real.rpow_add hp0 1 (-(1 / 2))).symm
      rw [Real.rpow_one] at h1
      rw [h1, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
    have hv0 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
    have hv1 : (1 : ℝ) ≤ Real.sqrt p := by nlinarith
    have hcube : (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) * Real.sqrt p := by
      have h1 : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ ((1 / 2) : ℝ) = (p : ℝ) ^ ((1 : ℝ) + 1 / 2) :=
        (Real.rpow_add hp0 1 (1 / 2)).symm
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at h1
      rw [show (3 / 2 : ℝ) = (1 : ℝ) + 1 / 2 by norm_num, ← h1]
    rw [habs, hcube]
    have hstep1 : (p : ℝ) * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) * (p : ℝ) ^ (-(1 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_left hexp hp0.le
    rw [hmulid] at hstep1
    nlinarith [hstep1, hv1, hv0, hsq]
  calc ∏ p ∈ t.primeFactors, (1 + |selbergPsi p - 1| * (p : ℝ) ^ (-s.re))
      ≤ ∏ p ∈ t.primeFactors, ((p : ℝ) ^ (3 / 2 : ℝ)) :=
        Finset.prod_le_prod (fun p _ => by positivity) hstep
    _ = (∏ p ∈ t.primeFactors, (p : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.finsetProd_rpow _ _ (fun p _ => by positivity) _
    _ ≤ (t : ℝ) ^ (3 / 2 : ℝ) := by
        refine Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => by positivity)) ?_ (by norm_num)
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ht) (Nat.prod_primeFactors_dvd t)

/-- The telescoping step of `Σ d^{-1/2}` (`GrahamHard2.lean:607`'s recipe, re-derived). -/
private lemma rpow_step_half_aux (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) ^ (-(1 / 2) : ℝ) ≤ 2 * (t + 1) ^ ((1 / 2) : ℝ) - 2 * t ^ ((1 / 2) : ℝ) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hinv : (t + 1) ^ (-(1 / 2) : ℝ) = ((t + 1) ^ ((1 / 2) : ℝ))⁻¹ := Real.rpow_neg ht1.le _
  rw [hinv]
  set a : ℝ := (t + 1) ^ ((1 / 2) : ℝ) with ha
  set b : ℝ := t ^ ((1 / 2) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos ht1 _
  have hb0 : (0 : ℝ) ≤ b := Real.rpow_nonneg ht _
  have ha2 : a ^ 2 = t + 1 := by
    rw [ha, ← Real.rpow_natCast ((t + 1) ^ ((1 / 2) : ℝ)) 2, ← Real.rpow_mul ht1.le]
    norm_num
  have hb2 : b ^ 2 = t := by
    rw [hb, ← Real.rpow_natCast (t ^ ((1 / 2) : ℝ)) 2, ← Real.rpow_mul ht]
    norm_num
  rw [inv_eq_one_div, div_le_iff₀ ha0]
  nlinarith [sq_nonneg (a - b), ha2, hb2]

theorem sum_Icc_rpow_neg_half_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * Real.sqrt N := by
  have key : ∀ M : ℕ, ∑ d ∈ Finset.Icc 1 M, (d : ℝ) ^ (-(1 / 2) : ℝ)
      ≤ 2 * (M : ℝ) ^ ((1 / 2) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih, rpow_step_half_aux (m : ℝ) (by positivity)]
  rw [Real.sqrt_eq_rpow]
  exact key N

theorem norm_jutilaM_selbergPsi_le (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁)
    (hz : z₁ < z₂) {r : ℕ} (hr : r ≠ 0) {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s‖
      ≤ 2 * Real.sqrt z₂ * (r : ℝ) ^ (3 / 2 : ℝ) := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hterm : ∀ d ∈ Finset.Icc 1 z₂,
      ‖((bvWeight z₁ z₂ d : ℝ) : ℂ) * χ d * ((pseudoChar selbergPsi r d : ℝ) : ℂ)
          * (d : ℂ) ^ (-s) * jutilaLocal selbergPsi χ (r / Nat.gcd r d) s‖
        ≤ (r : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : 0 < d := hd.1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    have hg : 0 < Nat.gcd r d := Nat.gcd_pos_of_pos_left d hrpos
    have hgR : (0 : ℝ) < (Nat.gcd r d : ℝ) := by exact_mod_cast hg
    have hg1R : (1 : ℝ) ≤ (Nat.gcd r d : ℝ) := by exact_mod_cast hg
    have hgdvd : Nat.gcd r d ∣ r := Nat.gcd_dvd_left r d
    have ht : r / Nat.gcd r d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hrpos hgdvd) hg).ne'
    have hcast : ((r / Nat.gcd r d : ℕ) : ℝ) = (r : ℝ) / (Nat.gcd r d : ℝ) :=
      Nat.cast_div hgdvd (Nat.cast_ne_zero.mpr hg.ne')
    have hb1 : |bvWeight z₁ z₂ d| ≤ 1 := abs_bvWeight_le_one hz₁ hz
    have hb2 : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hb3 : |pseudoChar selbergPsi r d| ≤ (Nat.gcd r d : ℝ) :=
      abs_pseudoChar_selbergPsi_le r d
    have hb4 : (d : ℝ) ^ (-s.re) ≤ (d : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hd1R (by linarith)
    have hb5 : ‖jutilaLocal selbergPsi χ (r / Nat.gcd r d) s‖
        ≤ ((r / Nat.gcd r d : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      norm_jutilaLocal_selbergPsi_le χ ht hs
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hdpos,
      Complex.neg_re]
    have hkey : |bvWeight z₁ z₂ d| * ‖χ (d : ZMod q)‖ * |pseudoChar selbergPsi r d|
          * (d : ℝ) ^ (-s.re) * ‖jutilaLocal selbergPsi χ (r / Nat.gcd r d) s‖
        ≤ 1 * 1 * (Nat.gcd r d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ)
          * ((r / Nat.gcd r d : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      mul5_le (abs_nonneg _) (norm_nonneg _) (abs_nonneg _) (by positivity) (norm_nonneg _)
        hb1 hb2 hb3 hb4 hb5
    refine hkey.trans ?_
    rw [hcast, Real.div_rpow hrR.le hgR.le]
    have h3 : (0 : ℝ) ≤ (r : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hrR.le _
    have harith : (Nat.gcd r d : ℝ)
        * ((r : ℝ) ^ (3 / 2 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ))
        ≤ (r : ℝ) ^ (3 / 2 : ℝ) := by
      have h1 : (Nat.gcd r d : ℝ) ^ (1 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ)
          = (Nat.gcd r d : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_sub hgR]
        norm_num
      have h2 : (Nat.gcd r d : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hg1R (by norm_num)
      calc (Nat.gcd r d : ℝ) * ((r : ℝ) ^ (3 / 2 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ))
          = (r : ℝ) ^ (3 / 2 : ℝ)
            * ((Nat.gcd r d : ℝ) ^ (1 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ)) := by
            rw [Real.rpow_one]; ring
        _ = (r : ℝ) ^ (3 / 2 : ℝ) * (Nat.gcd r d : ℝ) ^ (-(1 / 2) : ℝ) := by rw [h1]
        _ ≤ (r : ℝ) ^ (3 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 h3
        _ = (r : ℝ) ^ (3 / 2 : ℝ) := mul_one _
    calc 1 * 1 * (Nat.gcd r d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ)
            * ((r : ℝ) ^ (3 / 2 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ))
        = ((Nat.gcd r d : ℝ)
            * ((r : ℝ) ^ (3 / 2 : ℝ) / (Nat.gcd r d : ℝ) ^ (3 / 2 : ℝ)))
          * (d : ℝ) ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ (r : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right harith (by positivity)
  simp only [jutilaM]
  calc ‖∑ d ∈ Finset.Icc 1 z₂, ((bvWeight z₁ z₂ d : ℝ) : ℂ) * χ d
          * ((pseudoChar selbergPsi r d : ℝ) : ℂ) * (d : ℂ) ^ (-s)
          * jutilaLocal selbergPsi χ (r / Nat.gcd r d) s‖
      ≤ ∑ d ∈ Finset.Icc 1 z₂, ‖((bvWeight z₁ z₂ d : ℝ) : ℂ) * χ d
          * ((pseudoChar selbergPsi r d : ℝ) : ℂ) * (d : ℂ) ^ (-s)
          * jutilaLocal selbergPsi χ (r / Nat.gcd r d) s‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 z₂, (r : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (r : ℝ) ^ (3 / 2 : ℝ) * ∑ d ∈ Finset.Icc 1 z₂, (d : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (r : ℝ) ^ (3 / 2 : ℝ) * (2 * Real.sqrt z₂) :=
        mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_half_le z₂) (Real.rpow_nonneg hrR.le _)
    _ = 2 * Real.sqrt z₂ * (r : ℝ) ^ (3 / 2 : ℝ) := by ring

theorem sum_rFilter_inv_mul_rpow_le (q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) := by
  rcases eq_or_lt_of_le hR with hR0 | hR0
  · have hR0' : R = 0 := hR0.symm
    subst hR0'
    simp [rFilter, Real.zero_rpow (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
  · have hcard : ((rFilter q R).card : ℝ) ≤ R := by
      have h1 : (rFilter q R).card ≤ ⌊R⌋₊ := by
        have h2 : (rFilter q R).card ≤ (Finset.Icc 1 ⌊R⌋₊).card := by
          simp only [rFilter]
          exact Finset.card_filter_le _ _
        simpa [Nat.card_Icc] using h2
      calc ((rFilter q R).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h1
        _ ≤ R := Nat.floor_le hR
    have hterm : ∀ r ∈ rFilter q R,
        (r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ R ^ ((1 : ℝ) / 2) := by
      intro r hr
      simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr
      have hr1 : 1 ≤ r := hr.1.1
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      have hid : (r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) = (r : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_neg_one (r : ℝ), ← Real.rpow_add hrpos]
        norm_num
      rw [hid]
      refine Real.rpow_le_rpow hrpos.le ?_ (by norm_num)
      calc (r : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hr.1.2
        _ ≤ R := Nat.floor_le hR
    calc ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ)
        ≤ ∑ _r ∈ rFilter q R, R ^ ((1 : ℝ) / 2) := Finset.sum_le_sum hterm
      _ = ((rFilter q R).card : ℝ) * R ^ ((1 : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ R * R ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hR _)
      _ = R ^ (3 / 2 : ℝ) := by
          have h : R ^ (1 : ℝ) * R ^ ((1 : ℝ) / 2) = R ^ ((1 : ℝ) + 1 / 2) :=
            (Real.rpow_add hR0 _ _).symm
          rw [Real.rpow_one] at h
          rw [h]
          norm_num

theorem norm_jutilaMollifier_le (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁)
    (hz : z₁ < z₂) {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖jutilaMollifier χ z₁ z₂ R s‖ ≤ 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ) := by
  have hterm : ∀ r ∈ rFilter q R,
      ‖((r : ℝ)⁻¹ : ℂ) * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s‖
        ≤ 2 * Real.sqrt z₂ * ((r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ)) := by
    intro r hr
    simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1.1
    have hr0 : r ≠ 0 := by omega
    have hnr : ‖((r : ℝ)⁻¹ : ℂ)‖ = (r : ℝ)⁻¹ := by simp
    rw [norm_mul, hnr]
    calc (r : ℝ)⁻¹ * ‖jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s‖
        ≤ (r : ℝ)⁻¹ * (2 * Real.sqrt z₂ * (r : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (norm_jutilaM_selbergPsi_le χ hz₁ hz hr0 hs) (by positivity)
      _ = 2 * Real.sqrt z₂ * ((r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ)) := by ring
  simp only [jutilaMollifier]
  calc ‖∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ : ℂ) * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s‖
      ≤ ∑ r ∈ rFilter q R, ‖((r : ℝ)⁻¹ : ℂ)
          * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ rFilter q R, 2 * Real.sqrt z₂ * ((r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 2 * Real.sqrt z₂ * ∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_rFilter_inv_mul_rpow_le q hR) (by positivity)

theorem norm_jutilaCoeff_le (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂)
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ‖jutilaCoeff χ z₁ z₂ R n‖ ≤ (n.divisors.card : ℝ) * R := by
  have hb1 : |∑ d ∈ n.divisors, bvWeight z₁ z₂ d| ≤ (n.divisors.card : ℝ) :=
    abs_sum_bvWeight_divisors_le_card hz₁ hz n
  have hb2 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hb3 : |∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n| ≤ R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∀ r ∈ rFilter q R, |(r : ℝ)⁻¹ * pseudoChar selbergPsi r n| ≤ 1 := by
      intro r hr
      simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr
      have hr1 : 1 ≤ r := hr.1.1
      have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)]
      have hgcd : (Nat.gcd r n : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hr1 (Nat.gcd_dvd_left r n)
      have hps := abs_pseudoChar_selbergPsi_le r n
      rw [inv_mul_le_iff₀ hrR, mul_one]
      linarith
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : (rFilter q R).card ≤ ⌊R⌋₊ := by
      have h2 : (rFilter q R).card ≤ (Finset.Icc 1 ⌊R⌋₊).card := by
        simp only [rFilter]
        exact Finset.card_filter_le _ _
      simpa [Nat.card_Icc] using h2
    calc ((rFilter q R).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ R := Nat.floor_le hR
  simp only [jutilaCoeff]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs]
  calc |∑ d ∈ n.divisors, bvWeight z₁ z₂ d| * ‖χ (n : ZMod q)‖
        * |∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n|
      ≤ (n.divisors.card : ℝ) * 1 * R :=
        mul3_le (abs_nonneg _) (norm_nonneg _) (abs_nonneg _) hb1 hb2 hb3
    _ = (n.divisors.card : ℝ) * R := by ring

/-! ## (iii) The Dirichlet series and the Mellin representation -/

/-- The weight is finitely supported at EVERY level — the binder-free form the summability
row reads (`bvWeight_eq_zero_of_gt` needs `z₁ < z₂`). -/
private lemma bvWeight_eq_zero_of_max_lt {z₁ z₂ d : ℕ} (hd : max z₁ z₂ < d) :
    bvWeight z₁ z₂ d = 0 := by
  have h1 : z₁ < d := lt_of_le_of_lt (le_max_left _ _) hd
  have h2 : z₂ < d := lt_of_le_of_lt (le_max_right _ _) hd
  simp [bvWeight, grahamTheta_of_lt h1, grahamTheta_of_lt h2]

theorem LSeriesSummable_jutilaCoeff (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (jutilaCoeff χ z₁ z₂ R) s := by
  have hfun : jutilaCoeff χ z₁ z₂ R
      = ∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ : ℂ) •
          (fun n : ℕ => ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d : ℝ) : ℂ) * χ n
            * ((pseudoChar selbergPsi r n : ℝ) : ℂ)) := by
    funext n
    simp only [jutilaCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [hfun]
  refine LSeriesSummable.sum (fun r hr => ?_)
  have hr0 : r ≠ 0 := by
    simp only [rFilter, Finset.mem_filter, Finset.mem_Icc] at hr
    omega
  exact (LSeriesSummable_jutila_coeff χ selbergPsi hr0 (bvWeight z₁ z₂) (max z₁ z₂)
    (fun d hd => bvWeight_eq_zero_of_max_lt hd) hs).smul _

theorem LSeries_jutilaCoeff_eq [NeZero q] (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz : z₁ < z₂)
    (R : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (jutilaCoeff χ z₁ z₂ R) s = LFunction χ s * jutilaMollifier χ z₁ z₂ R s := by
  have hS : ∀ r ∈ rFilter q R, Squarefree r := by
    intro r hr
    simp only [rFilter, Finset.mem_filter] at hr
    exact hr.2.1
  change LSeries (fun n : ℕ => ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d : ℝ) : ℂ) * χ n
      * ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n : ℝ) : ℂ)) s
    = LFunction χ s * ∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ : ℂ)
        * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s
  exact LSeries_jutila_coeff_sum_eq χ selbergPsi_isMultiplicative (rFilter q R) hS
    (bvWeight z₁ z₂) z₂ (fun d hd => bvWeight_eq_zero_of_gt hz hd) hs

theorem LSeries_mul_natCast_cpow_neg (f : ℕ → ℂ) (ρ s : ℂ) :
    LSeries (fun n => f n * (n : ℂ) ^ (-ρ)) s = LSeries f (ρ + s) := by
  simp only [LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
    ring

theorem summable_jutilaCoeff_kernel (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) {x : ℝ}
    (hx : 0 < x) {ρ : ℂ} {c : ℝ} (hc : 0 < c) (hβc : 1 < ρ.re + c) :
    Summable (fun n : ℕ => ‖jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)‖ * (x / n) ^ c) := by
  have hre : 1 < (((ρ.re + c : ℝ)) : ℂ).re := by simpa using hβc
  have hLS : LSeriesSummable (jutilaCoeff χ z₁ z₂ R) (((ρ.re + c : ℝ)) : ℂ) :=
    LSeriesSummable_jutilaCoeff χ z₁ z₂ R hre
  have hnorm : Summable
      (fun n : ℕ => ‖LSeries.term (jutilaCoeff χ z₁ z₂ R) (((ρ.re + c : ℝ)) : ℂ) n‖) :=
    summable_norm_iff.mpr hLS
  have hEq : (fun n : ℕ => ‖jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)‖ * (x / n) ^ c)
      = fun n : ℕ => x ^ c * ‖LSeries.term (jutilaCoeff χ z₁ z₂ R) (((ρ.re + c : ℝ)) : ℂ) n‖ := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [jutilaCoeff_zero, Real.zero_rpow hc.ne']
    · have hn0 : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re,
        Real.div_rpow hx.le (Nat.cast_nonneg n), norm_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re,
        Real.rpow_neg hn0.le, Real.rpow_add hn0]
      field_simp
  rw [hEq]
  exact hnorm.mul_left (x ^ c)

theorem jutilaFull_eq_tsum (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) {x : ℝ} (hx : 0 < x)
    (s : ℂ) :
    jutilaFull χ z₁ z₂ R x s
      = ∑' n : ℕ, jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-s) * kern2 ((n : ℝ) / x) := by
  simp only [jutilaFull]
  refine (tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) ?_).symm
  intro n hn
  simp only [Finset.mem_Icc, not_and, not_le] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [jutilaCoeff_zero, zero_mul, zero_mul]
  · have hlt := hn hn0
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hlt
    have h1 : (1 : ℝ) ≤ (n : ℝ) / x := (one_le_div hx).mpr hxn.le
    have hk : kern2 ((n : ℝ) / x) = 0 := by
      simp only [kern2, max_eq_left (by linarith : (1 : ℝ) - (n : ℝ) / x ≤ 0)]
      norm_num
    rw [hk, mul_zero]

theorem jutilaFull_mellin [NeZero q] (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz : z₁ < z₂)
    (R : ℝ) {x : ℝ} (hx : 0 < x) {ρ : ℂ} {c : ℝ} (hc : 0 < c) (hβc : 1 < ρ.re + c) :
    jutilaFull χ z₁ z₂ R x ρ
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (t : ℂ) * I) := by
  have hsum : Summable
      (fun n : ℕ => ‖jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)‖ * (x / n) ^ c) :=
    summable_jutilaCoeff_kernel χ z₁ z₂ R hx hc hβc
  have hswap := kernel_sum_swap_2
    (fun n : ℕ => jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)) hx hc hsum
  have hIntEq : (∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, 2 * (∑' n : ℕ, (jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ))
            * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    have hw : ((c : ℂ) + (t : ℂ) * I) ≠ 0 := s_ne_zero hc t
    have hre : 1 < (ρ + ((c : ℂ) + (t : ℂ) * I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
        neg_zero, add_zero]
      exact hβc
    rw [riesz_tsum_eq (fun n : ℕ => jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)) hx.le hw,
      LSeries_mul_natCast_cpow_neg, LSeries_jutilaCoeff_eq χ hz R hre]
    simp only [jutilaIntegrand]
    ring
  rw [hIntEq, ← hswap, jutilaFull_eq_tsum χ z₁ z₂ R hx ρ, Complex.real_smul, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [jutilaCoeff_zero]
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hy : (0 : ℝ) < x / n := div_pos hx hnR
    have hpull : (∫ t : ℝ, 2 * (jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ))
          * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2)))
        = (jutilaCoeff χ z₁ z₂ R n * (n : ℂ) ^ (-ρ)) *
          ∫ t : ℝ, 2 * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      ring
    have hker := kernel_identity_2 hy hc
    rw [← kern2_value hy, one_div_div] at hker
    rw [hpull, ← hker, Complex.real_smul]
    ring

theorem jutilaDetector_mellin [NeZero q] (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁)
    (hz : z₁ < z₂) (R : ℝ) {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} {c : ℝ} (hc : 0 < c)
    (hβc : 1 < ρ.re + c) :
    jutilaDetector χ z₁ z₂ R x ρ
      = (1 / (2 * Real.pi)) • (∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (t : ℂ) * I))
        - ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hsplit := jutilaFull_eq_add_detector χ hz₁ hz R hx ρ
  rw [jutilaFull_mellin χ hz R hx0 hc hβc] at hsplit
  rw [hsplit]
  ring

/-! ## (iv) The contour node: the shift across the removable singularity at `w = 0` -/

theorem jutilaMollifier_differentiable (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R : ℝ) :
    Differentiable ℂ (jutilaMollifier χ z₁ z₂ R) := by
  have hneg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
  have hloc : ∀ t : ℕ, Differentiable ℂ (fun s : ℂ => jutilaLocal selbergPsi χ t s) := by
    intro t
    have hfun : (fun s : ℂ => jutilaLocal selbergPsi χ t s)
        = fun s : ℂ => ∏ p ∈ t.primeFactors,
            (1 + (((selbergPsi p : ℝ) : ℂ) - 1) * χ p * (p : ℂ) ^ (-s)) := rfl
    rw [hfun]
    refine Differentiable.fun_finsetProd (fun p hp => ?_)
    have hp0 : (p : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiable_const _).add
      ((differentiable_const _).mul (hneg.const_cpow (Or.inl hp0)))
  have hMfun : jutilaMollifier χ z₁ z₂ R = fun s : ℂ =>
      ∑ r ∈ rFilter q R, ((r : ℝ)⁻¹ : ℂ) * jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r s := rfl
  rw [hMfun]
  refine Differentiable.fun_sum (fun r _ => ?_)
  refine Differentiable.const_mul ?_ _
  have hjMfun : jutilaM (bvWeight z₁ z₂) z₂ selbergPsi χ r
      = fun s : ℂ => ∑ d ∈ Finset.Icc 1 z₂,
          ((bvWeight z₁ z₂ d : ℝ) : ℂ) * χ d * ((pseudoChar selbergPsi r d : ℝ) : ℂ)
            * (d : ℂ) ^ (-s) * jutilaLocal selbergPsi χ (r / Nat.gcd r d) s := rfl
  rw [hjMfun]
  refine Differentiable.fun_sum (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact ((differentiable_const _).mul (hneg.const_cpow (Or.inl hd0))).mul (hloc _)

theorem jutilaPhi_differentiableOn [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (z₁ z₂ : ℕ) (R : ℝ) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    DifferentiableOn ℂ (jutilaPhi χ z₁ z₂ R x ρ) {w : ℂ | -1 < w.re} := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hMd : Differentiable ℂ (jutilaMollifier χ z₁ z₂ R) :=
    jutilaMollifier_differentiable χ z₁ z₂ R
  have hLd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  have hL2 : Differentiable ℂ (fun w : ℂ => LFunction χ (ρ + w)) := fun v =>
    (hLd (ρ + v)).comp v (differentiableAt_id.const_add ρ)
  have hM2 : Differentiable ℂ (fun w : ℂ => jutilaMollifier χ z₁ z₂ R (ρ + w)) := fun v =>
    (hMd (ρ + v)).comp v (differentiableAt_id.const_add ρ)
  have hφfun : jutilaPhi χ z₁ z₂ R x ρ = fun w : ℂ =>
      2 * (x : ℂ) ^ w * LFunction χ (ρ + w) * jutilaMollifier χ z₁ z₂ R (ρ + w)
        / ((w + 1) * (w + 2)) := rfl
  rw [hφfun]
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl hxne)
  have hd1 : w + 1 ≠ 0 := by
    intro hcon
    have hre : (w + 1).re = w.re + 1 := by simp
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hd2 : w + 2 ≠ 0 := by
    intro hcon
    have hre : (w + 2).re = w.re + 2 := by simp
    rw [hcon] at hre
    simp only [Complex.zero_re] at hre
    linarith
  exact DifferentiableAt.div ((((differentiableAt_const 2).mul h1).mul (hL2 w)).mul (hM2 w))
    ((differentiableAt_id.add (differentiableAt_const 1)).mul
      (differentiableAt_id.add (differentiableAt_const 2))) (mul_ne_zero hd1 hd2)

theorem jutilaPhi_zero [NeZero q] (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) {ρ : ℂ}
    (h0 : LFunction χ ρ = 0) :
    jutilaPhi χ z₁ z₂ R x ρ 0 = 0 := by
  simp [jutilaPhi, h0]

theorem dslope_jutilaPhi_eq [NeZero q] (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x : ℝ) {ρ : ℂ}
    (h0 : LFunction χ ρ = 0) {w : ℂ} (hw : w ≠ 0) :
    dslope (jutilaPhi χ z₁ z₂ R x ρ) 0 w = jutilaIntegrand χ z₁ z₂ R x ρ w := by
  rw [dslope_of_ne _ hw, slope_def_field, jutilaPhi_zero χ z₁ z₂ R x h0, sub_zero, sub_zero]
  simp only [jutilaPhi, jutilaIntegrand]
  rw [div_div]
  ring

theorem rectBI_dslope_jutilaPhi_eq_zero [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (z₁ z₂ : ℕ) (R : ℝ) {x : ℝ} (hx : 0 < x) (ρ : ℂ) {σ₀ c T' : ℝ} (hσ₀ : -1 < σ₀)
    (hσ₀0 : σ₀ < 0) (hc : 0 < c) (hT' : 0 < T') :
    rectBI ((σ₀ : ℂ) - (T' : ℂ) * I) ((c : ℂ) + (T' : ℂ) * I)
      (dslope (jutilaPhi χ z₁ z₂ R x ρ) 0) = 0 := by
  have hσ₀c : σ₀ < c := lt_trans hσ₀0 hc
  have hzre : ((σ₀ : ℂ) - (T' : ℂ) * I).re = σ₀ := by simp
  have hzim : ((σ₀ : ℂ) - (T' : ℂ) * I).im = -T' := by simp
  have hwre : ((c : ℂ) + (T' : ℂ) * I).re = c := by simp
  have hwim : ((c : ℂ) + (T' : ℂ) * I).im = T' := by simp
  refine rectBI_dslope_eq_zero ?_ ?_
  · refine (jutilaPhi_differentiableOn hχ z₁ z₂ R hx ρ).mono ?_
    intro v hv
    simp only [closedRect, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIcc_of_le hσ₀c.le] at hv
    exact lt_of_lt_of_le hσ₀ hv.1.1
  · simp only [openRect, Complex.mem_reProdIm, hzre, hzim, hwre, hwim, Complex.zero_re,
      Complex.zero_im, Set.mem_Ioo, min_eq_left hσ₀c.le, max_eq_right hσ₀c.le,
      min_eq_left (neg_le_self hT'.le), max_eq_right (neg_le_self hT'.le)]
    exact ⟨⟨hσ₀0, hc⟩, ⟨neg_lt_zero.mpr hT', hT'⟩⟩

theorem norm_jutilaIntegrand_le [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ} (hR : 0 ≤ R) {x : ℝ}
    (hx : 0 < x) (ρ w : ℂ) (hw1 : (1 : ℝ) / 2 ≤ (ρ + w).re) (hw2 : (ρ + w).re ≤ 4) :
    ‖jutilaIntegrand χ z₁ z₂ R x ρ w‖
      ≤ 2 * x ^ w.re * (3 * (1 + ‖ρ + w‖) * Real.sqrt q * (1 + Real.log q))
        * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) * ‖(w * (w + 1) * (w + 2))⁻¹‖ := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hL : ‖LFunction χ (ρ + w)‖ ≤ 3 * (1 + ‖ρ + w‖) * Real.sqrt q * (1 + Real.log q) :=
    LFunction_growth χ hχ hq hw1 hw2
  have hM : ‖jutilaMollifier χ z₁ z₂ R (ρ + w)‖ ≤ 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ) :=
    norm_jutilaMollifier_le χ hz₁ hz hR hw1
  simp only [jutilaIntegrand]
  rw [norm_div, norm_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx w,
    show ‖(2 : ℂ)‖ = 2 from by norm_num]
  exact mul4_le (by norm_num) (Real.rpow_nonneg hx.le _) (norm_nonneg _) (norm_nonneg _)
    le_rfl le_rfl hL hM

theorem norm_inv_denom2_le_abs_im_cube {w : ℂ} (hw : w.im ≠ 0) :
    ‖(w * (w + 1) * (w + 2))⁻¹‖ ≤ (|w.im| ^ 3)⁻¹ := by
  have him : 0 < |w.im| := abs_pos.mpr hw
  have h0 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1 : |w.im| ≤ ‖w + 1‖ := by
    have he : (w + 1).im = w.im := by simp
    calc |w.im| = |(w + 1).im| := by rw [he]
      _ ≤ ‖w + 1‖ := Complex.abs_im_le_norm _
  have h2 : |w.im| ≤ ‖w + 2‖ := by
    have he : (w + 2).im = w.im := by simp
    calc |w.im| = |(w + 2).im| := by rw [he]
      _ ≤ ‖w + 2‖ := Complex.abs_im_le_norm _
  rw [norm_inv]
  refine inv_anti₀ (pow_pos him 3) ?_
  rw [norm_mul, norm_mul]
  calc |w.im| ^ 3 = |w.im| * |w.im| * |w.im| := by ring
    _ ≤ ‖w‖ * ‖w + 1‖ * ‖w + 2‖ :=
        mul3_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) h0 h1 h2

theorem norm_integral_jutilaIntegrand_edge_le [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ}
    (hR : 0 ≤ R) {x : ℝ} (hx : 1 ≤ x) (ρ : ℂ) {σ₀ c τ : ℝ} (hσ₀ : (1 : ℝ) / 2 ≤ ρ.re + σ₀)
    (hc : ρ.re + c ≤ 4) (hσc : σ₀ ≤ c) (hτ : τ ≠ 0) :
    ‖∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + (τ : ℂ) * I)‖
      ≤ (c - σ₀) * (2 * x ^ c * (3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) * Real.sqrt q
          * (1 + Real.log q)) * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) / |τ| ^ 3) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hpv : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) := sqrtlog_nonneg hq
  have hpt : ∀ u ∈ Set.uIoc σ₀ c,
      ‖jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + (τ : ℂ) * I)‖
        ≤ 2 * x ^ c * (3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) * Real.sqrt q
            * (1 + Real.log q)) * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) / |τ| ^ 3 := by
    intro u hu
    rw [Set.uIoc_of_le hσc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hwre : (ρ + ((u : ℂ) + (τ : ℂ) * I)).re = ρ.re + u := by simp
    have hw1 : (1 : ℝ) / 2 ≤ (ρ + ((u : ℂ) + (τ : ℂ) * I)).re := by
      rw [hwre]; linarith
    have hw2 : (ρ + ((u : ℂ) + (τ : ℂ) * I)).re ≤ 4 := by
      rw [hwre]; linarith
    refine (norm_jutilaIntegrand_le hχ hq hz₁ hz hR hx0 ρ _ hw1 hw2).trans ?_
    have hure : ((u : ℂ) + (τ : ℂ) * I).re = u := by simp
    have him : ((u : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hcube := norm_inv_denom2_le_abs_im_cube (w := (u : ℂ) + (τ : ℂ) * I)
      (by rw [him]; exact hτ)
    rw [him] at hcube
    have hxu : x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hu2
    have hnb : ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖ ≤ ‖ρ‖ + |σ₀| + |c| + |τ| := by
      have hA : ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖ ≤ ‖ρ‖ + ‖(u : ℂ) + (τ : ℂ) * I‖ :=
        norm_add_le _ _
      have hB : ‖(u : ℂ) + (τ : ℂ) * I‖ ≤ |u| + |τ| := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
      have hC : |u| ≤ |σ₀| + |c| := by
        rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]; linarith [le_abs_self c, abs_nonneg σ₀]
        · rw [he]; linarith [neg_abs_le σ₀, abs_nonneg c]
      linarith
    rw [hure]
    have hbb : 3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q)
        ≤ 3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) * Real.sqrt q * (1 + Real.log q) := by
      have h3 : 3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖)
          ≤ 3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) := by linarith
      calc 3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q)
          = (3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖)) * (Real.sqrt q * (1 + Real.log q)) := by
            ring
        _ ≤ (3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|)) * (Real.sqrt q * (1 + Real.log q)) :=
            mul_le_mul_of_nonneg_right h3 hpv
        _ = 3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) * Real.sqrt q * (1 + Real.log q) := by ring
    have hc0 : (0 : ℝ) ≤ 3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖) * Real.sqrt q
        * (1 + Real.log q) :=
      mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (by linarith)
    have hstep := mul5_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ)) (b₁ := x ^ u) (b₂ := x ^ c)
      (c₁ := 3 * (1 + ‖ρ + ((u : ℂ) + (τ : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q))
      (c₂ := 3 * (1 + ‖ρ‖ + |σ₀| + |c| + |τ|) * Real.sqrt q * (1 + Real.log q))
      (d₁ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) (d₂ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ))
      (e₁ := ‖(((u : ℂ) + (τ : ℂ) * I) * (((u : ℂ) + (τ : ℂ) * I) + 1)
          * (((u : ℂ) + (τ : ℂ) * I) + 2))⁻¹‖) (e₂ := (|τ| ^ 3)⁻¹)
      (by norm_num) (Real.rpow_nonneg hx0.le _) hc0 (by positivity) (norm_nonneg _)
      le_rfl hxu hbb le_rfl hcube
    exact hstep.trans (le_of_eq (div_eq_mul_inv _ _).symm)
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (sub_nonneg.mpr hσc)] at hmain
  refine hmain.trans (le_of_eq ?_)
  ring

theorem norm_inv_denom2_cubic_le_of_min {σ m : ℝ} (hm : 0 < m) (h0 : m ≤ |σ|) (h1 : m ≤ |σ + 1|)
    (h2 : m ≤ |σ + 2|) (t : ℝ) :
    ‖(((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1) * ((σ : ℂ) + (t : ℂ) * I + 2))⁻¹‖
      ≤ ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ := by
  have hS0 : 0 < m ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg t)
  have hA : ‖(σ : ℂ) + (t : ℂ) * I‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hB : ‖(σ : ℂ) + (t : ℂ) * I + 1‖ = Real.sqrt ((σ + 1) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hC : ‖(σ : ℂ) + (t : ℂ) * I + 2‖ = Real.sqrt ((σ + 2) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hcube : (m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ) = Real.sqrt (m ^ 2 + t ^ 2) ^ 3 := by
    have h32 : ((3 : ℝ) / 2) = (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) := by norm_num
    rw [h32, Real.rpow_mul hS0.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs0 : m ^ 2 ≤ σ ^ 2 := by nlinarith [sq_abs σ, abs_nonneg σ, hm.le, h0]
  have hs1 : m ^ 2 ≤ (σ + 1) ^ 2 := by
    nlinarith [sq_abs (σ + 1), abs_nonneg (σ + 1), hm.le, h1]
  have hs2 : m ^ 2 ≤ (σ + 2) ^ 2 := by
    nlinarith [sq_abs (σ + 2), abs_nonneg (σ + 2), hm.le, h2]
  have hprod : (m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ)
      ≤ ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)
          * ((σ : ℂ) + (t : ℂ) * I + 2)‖ := by
    rw [norm_mul, norm_mul, hA, hB, hC, hcube]
    have e0 : (0 : ℝ) ≤ Real.sqrt (m ^ 2 + t ^ 2) := Real.sqrt_nonneg _
    have e1 : Real.sqrt (m ^ 2 + t ^ 2) ≤ Real.sqrt (σ ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have e2 : Real.sqrt (m ^ 2 + t ^ 2) ≤ Real.sqrt ((σ + 1) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have e3 : Real.sqrt (m ^ 2 + t ^ 2) ≤ Real.sqrt ((σ + 2) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    calc Real.sqrt (m ^ 2 + t ^ 2) ^ 3
        = Real.sqrt (m ^ 2 + t ^ 2) * Real.sqrt (m ^ 2 + t ^ 2)
          * Real.sqrt (m ^ 2 + t ^ 2) := by ring
      _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) * Real.sqrt ((σ + 1) ^ 2 + t ^ 2)
          * Real.sqrt ((σ + 2) ^ 2 + t ^ 2) := mul3_le e0 e0 e0 e1 e2 e3
  rw [norm_inv]
  exact inv_anti₀ (Real.rpow_pos_of_pos hS0 _) hprod

private lemma rpow_three_half_dom {m : ℝ} (hm : 0 < m) (t : ℝ) :
    ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ ≤ m⁻¹ * (m ^ 2 + t ^ 2)⁻¹ := by
  have hS : 0 < m ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg t)
  have hsplit : (m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ)
      = (m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2) * (m ^ 2 + t ^ 2) := by
    have h := (Real.rpow_add hS ((1 : ℝ) / 2) 1).symm
    rw [Real.rpow_one] at h
    rw [show (3 / 2 : ℝ) = (1 : ℝ) / 2 + 1 by norm_num, h]
  have hge : m ≤ (m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
      _ ≤ Real.sqrt (m ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  rw [hsplit, mul_inv]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hm hge) (by positivity)

private lemma abs_mul_rpow_three_half_dom {m : ℝ} (hm : 0 < m) (t : ℝ) :
    |t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ ≤ (m ^ 2 + t ^ 2)⁻¹ := by
  have hS : 0 < m ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg t)
  have hsplit : (m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ)
      = (m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2) * (m ^ 2 + t ^ 2) := by
    have h := (Real.rpow_add hS ((1 : ℝ) / 2) 1).symm
    rw [Real.rpow_one] at h
    rw [show (3 / 2 : ℝ) = (1 : ℝ) / 2 + 1 by norm_num, h]
  have hpos : (0 : ℝ) < (m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hS _
  have hge : |t| ≤ (m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
      _ ≤ Real.sqrt (m ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m])
  have h1 : |t| * ((m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, mul_one_div, div_le_one hpos]
    exact hge
  calc |t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
      = (|t| * ((m ^ 2 + t ^ 2) ^ ((1 : ℝ) / 2))⁻¹) * (m ^ 2 + t ^ 2)⁻¹ := by
        rw [hsplit, mul_inv]; ring
    _ ≤ 1 * (m ^ 2 + t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (m ^ 2 + t ^ 2)⁻¹ := one_mul _

private lemma continuous_inv_sq_add_sq_rpow {m : ℝ} (hm : 0 < m) :
    Continuous (fun t : ℝ => ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
  refine Continuous.inv₀ ?_ ?_
  · exact (continuous_const.add (continuous_pow 2)).rpow_const (fun _ => Or.inr (by norm_num))
  · intro t
    exact (Real.rpow_pos_of_pos
      (add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg t)) _).ne'

theorem integrable_inv_sq_add_sq_rpow {m : ℝ} (hm : 0 < m) :
    Integrable (fun t : ℝ => ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
  refine ((integrable_inv_c_sq_add_sq hm).const_mul m⁻¹).mono' ?_ ?_
  · exact (continuous_inv_sq_add_sq_rpow hm).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact rpow_three_half_dom hm t

theorem integrable_abs_mul_inv_sq_add_sq_rpow {m : ℝ} (hm : 0 < m) :
    Integrable (fun t : ℝ => |t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
  refine (integrable_inv_c_sq_add_sq hm).mono' ?_ ?_
  · exact (continuous_abs.mul (continuous_inv_sq_add_sq_rpow hm)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact abs_mul_rpow_three_half_dom hm t

theorem integrable_jutilaIntegrand_line [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ}
    (hR : 0 ≤ R) {x : ℝ} (hx : 0 < x) (ρ : ℂ) {σ m : ℝ} (hσ1 : (1 : ℝ) / 2 ≤ ρ.re + σ)
    (hσ2 : ρ.re + σ ≤ 4) (hm : 0 < m) (h0 : m ≤ |σ|) (h1 : m ≤ |σ + 1|) (h2 : m ≤ |σ + 2|) :
    Integrable (fun t : ℝ => jutilaIntegrand χ z₁ z₂ R x ρ ((σ : ℂ) + (t : ℂ) * I)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hpv : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) := sqrtlog_nonneg hq
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hwc : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by fun_prop
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
  have hcont : Continuous
      (fun t : ℝ => jutilaIntegrand χ z₁ z₂ R x ρ ((σ : ℂ) + (t : ℂ) * I)) := by
    simp only [jutilaIntegrand]
    refine Continuous.div ?_ ?_ hdne
    · refine ((continuous_const.mul (Continuous.const_cpow hwc (Or.inl hxne))).mul ?_).mul ?_
      · exact (differentiable_LFunction hχ1).continuous.comp (continuous_const.add hwc)
      · exact (jutilaMollifier_differentiable χ z₁ z₂ R).continuous.comp
          (continuous_const.add hwc)
    · exact (hwc.mul (hwc.add continuous_const)).mul (hwc.add continuous_const)
  have hg : Integrable (fun t : ℝ =>
      (2 * x ^ σ * (3 * Real.sqrt q * (1 + Real.log q))
        * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
      * ((1 + ‖ρ‖ + |σ|) * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
          + |t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)) :=
    (((integrable_inv_sq_add_sq_rpow hm).const_mul (1 + ‖ρ‖ + |σ|)).add
      (integrable_abs_mul_inv_sq_add_sq_rpow hm)).const_mul _
  refine hg.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hwre : (ρ + ((σ : ℂ) + (t : ℂ) * I)).re = ρ.re + σ := by simp
  have hw1 : (1 : ℝ) / 2 ≤ (ρ + ((σ : ℂ) + (t : ℂ) * I)).re := by rw [hwre]; linarith
  have hw2 : (ρ + ((σ : ℂ) + (t : ℂ) * I)).re ≤ 4 := by rw [hwre]; linarith
  have hure : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have hbase := norm_jutilaIntegrand_le hχ hq hz₁ hz hR hx ρ _ hw1 hw2
  rw [hure] at hbase
  have hcube := norm_inv_denom2_cubic_le_of_min hm h0 h1 h2 t
  have hnb : ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖ ≤ ‖ρ‖ + |σ| + |t| := by
    have hA : ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖ ≤ ‖ρ‖ + ‖(σ : ℂ) + (t : ℂ) * I‖ := norm_add_le _ _
    have hB : ‖(σ : ℂ) + (t : ℂ) * I‖ ≤ |σ| + |t| := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hc0 : (0 : ℝ) ≤ 3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q
      * (1 + Real.log q) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (by linarith)
  have hbb : 3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q)
      ≤ 3 * ((1 + ‖ρ‖ + |σ|) + |t|) * Real.sqrt q * (1 + Real.log q) := by
    have h3 : 3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖)
        ≤ 3 * ((1 + ‖ρ‖ + |σ|) + |t|) := by linarith
    calc 3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q)
        = (3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖)) * (Real.sqrt q * (1 + Real.log q)) := by
          ring
      _ ≤ (3 * ((1 + ‖ρ‖ + |σ|) + |t|)) * (Real.sqrt q * (1 + Real.log q)) :=
          mul_le_mul_of_nonneg_right h3 hpv
      _ = 3 * ((1 + ‖ρ‖ + |σ|) + |t|) * Real.sqrt q * (1 + Real.log q) := by ring
  have hstep := mul5_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ)) (b₁ := x ^ σ) (b₂ := x ^ σ)
    (c₁ := 3 * (1 + ‖ρ + ((σ : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q * (1 + Real.log q))
    (c₂ := 3 * ((1 + ‖ρ‖ + |σ|) + |t|) * Real.sqrt q * (1 + Real.log q))
    (d₁ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) (d₂ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ))
    (e₁ := ‖(((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)
        * ((σ : ℂ) + (t : ℂ) * I + 2))⁻¹‖) (e₂ := ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
    (by norm_num) (Real.rpow_nonneg hx.le _) hc0 (by positivity) (norm_nonneg _)
    le_rfl le_rfl hbb le_rfl hcube
  refine (hbase.trans hstep).trans (le_of_eq ?_)
  ring

theorem integral_jutilaIntegrand_shift [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ}
    (hR : 0 ≤ R) {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (h0 : LFunction χ ρ = 0)
    (hβ : (1 : ℝ) / 2 < ρ.re) (hβ1 : ρ.re < 1) :
    (∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ (((2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I) := by
  set c : ℝ := 2 - ρ.re with hcdef
  set σ₀ : ℝ := 1 / 2 - ρ.re with hσdef
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hcpos : (0 : ℝ) < c := by rw [hcdef]; linarith
  have hσneg : σ₀ < 0 := by rw [hσdef]; linarith
  have hσm1 : (-1 : ℝ) < σ₀ := by rw [hσdef]; linarith
  have hσc : σ₀ ≤ c := by linarith
  have hσ0e : (1 : ℝ) / 2 ≤ ρ.re + σ₀ := by rw [hσdef]; linarith
  have hce : ρ.re + c ≤ 4 := by rw [hcdef]; linarith
  have habs0 : |σ₀| = ρ.re - 1 / 2 := by
    rw [hσdef, abs_of_neg (by linarith : (1 : ℝ) / 2 - ρ.re < 0)]
    ring
  have habs1 : |σ₀ + 1| = 3 / 2 - ρ.re := by
    rw [hσdef, abs_of_pos (by linarith : (0 : ℝ) < 1 / 2 - ρ.re + 1)]
    ring
  have habs2 : |σ₀ + 2| = 5 / 2 - ρ.re := by
    rw [hσdef, abs_of_pos (by linarith : (0 : ℝ) < 1 / 2 - ρ.re + 2)]
    ring
  have hmL : (0 : ℝ) < min (ρ.re - 1 / 2) (3 / 2 - ρ.re) := lt_min (by linarith) (by linarith)
  have hIntC : Integrable
      (fun t : ℝ => jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (t : ℂ) * I)) :=
    integrable_jutilaIntegrand_line hχ hq hz₁ hz hR hx0 ρ (by rw [hcdef]; linarith) hce hcpos
      (le_of_eq (abs_of_pos hcpos).symm)
      (by rw [abs_of_pos (by linarith : (0 : ℝ) < c + 1)]; linarith)
      (by rw [abs_of_pos (by linarith : (0 : ℝ) < c + 2)]; linarith)
  have hIntL : Integrable
      (fun t : ℝ => jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (t : ℂ) * I)) :=
    integrable_jutilaIntegrand_line hχ hq hz₁ hz hR hx0 ρ hσ0e (by rw [hσdef]; linarith) hmL
      (by rw [habs0]; exact min_le_left _ _) (by rw [habs1]; exact min_le_right _ _)
      (by rw [habs2]; exact le_trans (min_le_right _ _) (by linarith))
  have hRt : Filter.Tendsto (fun T' : ℝ => ∫ y in (-T')..T',
      jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (y : ℂ) * I)) Filter.atTop
      (nhds (∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hIntC Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hLt : Filter.Tendsto (fun T' : ℝ => ∫ y in (-T')..T',
      jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (y : ℂ) * I)) Filter.atTop
      (nhds (∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hIntL Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hgtend : Filter.Tendsto (fun T' : ℝ =>
      ((c - σ₀) * (2 * x ^ c * (3 * (1 + ‖ρ‖ + |σ₀| + |c|) * Real.sqrt q * (1 + Real.log q))
          * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))) * (T' ^ 3)⁻¹
      + ((c - σ₀) * (2 * x ^ c * (3 * Real.sqrt q * (1 + Real.log q))
          * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))) * (T' ^ 2)⁻¹)
      Filter.atTop (nhds 0) := by
    have e3 : Filter.Tendsto (fun T' : ℝ => (T' ^ 3)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num))
    have e2 : Filter.Tendsto (fun T' : ℝ => (T' ^ 2)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num))
    simpa using (e3.const_mul _).add (e2.const_mul _)
  have hTopt : Filter.Tendsto (fun T' : ℝ => ∫ u in σ₀..c,
      jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((T' : ℝ) : ℂ) * I)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgtend
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T' hT'
    have hTne : T' ≠ 0 := hT'.ne'
    have hb := norm_integral_jutilaIntegrand_edge_le hχ hq hz₁ hz hR hx ρ hσ0e hce hσc hTne
    rw [abs_of_pos hT'] at hb
    refine hb.trans (le_of_eq ?_)
    field_simp
  have hBott : Filter.Tendsto (fun T' : ℝ => ∫ u in σ₀..c,
      jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgtend
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T' hT'
    have hTne : T' ≠ 0 := hT'.ne'
    have hb := norm_integral_jutilaIntegrand_edge_le hχ hq hz₁ hz hR hx ρ hσ0e hce hσc
      (neg_ne_zero.mpr hTne)
    rw [abs_neg, abs_of_pos hT'] at hb
    refine hb.trans (le_of_eq ?_)
    field_simp
  have hedges : ∀ T' : ℝ, 0 < T' →
      (∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (y : ℂ) * I))
        - (∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (y : ℂ) * I))
      = -I * ((∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((T' : ℝ) : ℂ) * I))
          - ∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)) := by
    intro T' hT'
    have hrect := rectBI_dslope_jutilaPhi_eq_zero hχ1 z₁ z₂ R hx0 ρ hσm1 hσneg hcpos hT'
    have hzre : ((σ₀ : ℂ) - (T' : ℂ) * I).re = σ₀ := by simp
    have hzim : ((σ₀ : ℂ) - (T' : ℂ) * I).im = -T' := by simp
    have hwre : ((c : ℂ) + (T' : ℂ) * I).re = c := by simp
    have hwim : ((c : ℂ) + (T' : ℂ) * I).im = T' := by simp
    simp only [rectBI, hzre, hzim, hwre, hwim] at hrect
    have hb1 : (∫ u in σ₀..c,
        dslope (jutilaPhi χ z₁ z₂ R x ρ) 0 ((u : ℂ) + ((-T' : ℝ) : ℂ) * I))
        = ∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      refine dslope_jutilaPhi_eq χ z₁ z₂ R x h0 ?_
      intro hcon
      have him : ((u : ℂ) + ((-T' : ℝ) : ℂ) * I).im = -T' := by simp
      rw [hcon] at him
      simp only [Complex.zero_im] at him
      linarith
    have hb2 : (∫ u in σ₀..c,
        dslope (jutilaPhi χ z₁ z₂ R x ρ) 0 ((u : ℂ) + ((T' : ℝ) : ℂ) * I))
        = ∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((T' : ℝ) : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      refine dslope_jutilaPhi_eq χ z₁ z₂ R x h0 ?_
      intro hcon
      have him : ((u : ℂ) + ((T' : ℝ) : ℂ) * I).im = T' := by simp
      rw [hcon] at him
      simp only [Complex.zero_im] at him
      linarith
    have hb3 : (∫ y in (-T')..T', dslope (jutilaPhi χ z₁ z₂ R x ρ) 0 ((c : ℂ) + (y : ℂ) * I))
        = ∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (y : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      refine dslope_jutilaPhi_eq χ z₁ z₂ R x h0 ?_
      intro hcon
      have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
      rw [hcon] at hre
      simp only [Complex.zero_re] at hre
      linarith
    have hb4 : (∫ y in (-T')..T', dslope (jutilaPhi χ z₁ z₂ R x ρ) 0 ((σ₀ : ℂ) + (y : ℂ) * I))
        = ∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (y : ℂ) * I) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      refine dslope_jutilaPhi_eq χ z₁ z₂ R x h0 ?_
      intro hcon
      have hre : ((σ₀ : ℂ) + (y : ℂ) * I).re = σ₀ := by simp
      rw [hcon] at hre
      simp only [Complex.zero_re] at hre
      linarith
    rw [hb1, hb2, hb3, hb4] at hrect
    have h3 : I * ((∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (y : ℂ) * I))
          - ∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (y : ℂ) * I))
        = (∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((T' : ℝ) : ℂ) * I))
          - ∫ u in σ₀..c, jutilaIntegrand χ z₁ z₂ R x ρ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) := by
      linear_combination hrect
    rw [← h3, ← mul_assoc, show (-I) * I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg],
      one_mul]
  have hdiff1 := hRt.sub hLt
  have hdiff2 : Filter.Tendsto (fun T' : ℝ =>
      (∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((c : ℂ) + (y : ℂ) * I))
        - ∫ y in (-T')..T', jutilaIntegrand χ z₁ z₂ R x ρ ((σ₀ : ℂ) + (y : ℂ) * I))
      Filter.atTop (nhds 0) := by
    have hTB := (hTopt.sub hBott).const_mul (-I)
    rw [sub_zero, mul_zero] at hTB
    refine Filter.Tendsto.congr' ?_ hTB
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T' hT'
    exact (hedges T' hT').symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff1 hdiff2)

/-! ## (v) The two integrals on the shifted line, and the bound at a zero -/

theorem integral_inv_sq_add_sq {m : ℝ} (hm : 0 < m) :
    ∫ t : ℝ, (m ^ 2 + t ^ 2)⁻¹ = Real.pi / m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hfun : (fun t : ℝ => (m ^ 2 + t ^ 2)⁻¹)
      = fun t : ℝ => (m ^ 2)⁻¹ * (1 + (m⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    have hS : (m ^ 2 + t ^ 2) ≠ 0 :=
      (add_pos_of_pos_of_nonneg (pow_pos hm 2) (sq_nonneg t)).ne'
    field_simp
  rw [hfun, MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) m⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, smul_eq_mul, abs_of_pos hm]
  field_simp

theorem integral_inv_sq_add_sq_rpow_le {m : ℝ} (hm : 0 < m) :
    ∫ t : ℝ, ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ ≤ Real.pi / m ^ 2 := by
  have hmono := MeasureTheory.integral_mono (integrable_inv_sq_add_sq_rpow hm)
    ((integrable_inv_c_sq_add_sq hm).const_mul m⁻¹) (fun t => rpow_three_half_dom hm t)
  rw [MeasureTheory.integral_const_mul, integral_inv_sq_add_sq hm] at hmono
  refine hmono.trans (le_of_eq ?_)
  field_simp

theorem integral_abs_mul_inv_sq_add_sq_rpow_le {m : ℝ} (hm : 0 < m) :
    ∫ t : ℝ, |t| * ((m ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ ≤ Real.pi / m := by
  have hmono := MeasureTheory.integral_mono (integrable_abs_mul_inv_sq_add_sq_rpow hm)
    (integrable_inv_c_sq_add_sq hm) (fun t => abs_mul_rpow_three_half_dom hm t)
  rw [integral_inv_sq_add_sq hm] at hmono
  exact hmono

theorem norm_jutilaFull_le [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ} (hR : 0 ≤ R) {x : ℝ}
    (hx : 1 ≤ x) {ρ : ℂ} (h0 : LFunction χ ρ = 0) (hβ : (119 : ℝ) / 120 ≤ ρ.re) (hβ1 : ρ.re < 1)
    {T : ℝ} (hρT : |ρ.im| ≤ T) :
    ‖jutilaFull χ z₁ z₂ R x ρ‖
      ≤ 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - ρ.re) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hβ' : (1 : ℝ) / 2 < ρ.re := by linarith
  have hT0 : (0 : ℝ) ≤ T := le_trans (abs_nonneg _) hρT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hpv : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) := sqrtlog_nonneg hq
  have hcpos : (0 : ℝ) < 2 - ρ.re := by linarith
  have hm : (0 : ℝ) < 59 / 120 := by norm_num
  have hm0 : (59 : ℝ) / 120 ≤ |1 / 2 - ρ.re| := by
    rw [abs_of_neg (by linarith : (1 : ℝ) / 2 - ρ.re < 0)]
    linarith
  have hm1 : (59 : ℝ) / 120 ≤ |1 / 2 - ρ.re + 1| := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 / 2 - ρ.re + 1)]
    linarith
  have hm2 : (59 : ℝ) / 120 ≤ |1 / 2 - ρ.re + 2| := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 / 2 - ρ.re + 2)]
    linarith
  have hKnn : (0 : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ρ.re) * (3 * Real.sqrt q * (1 + Real.log q))
      * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) := by
    refine mul_nonneg (mul_nonneg (by positivity) ?_) (by positivity)
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
  have hgint : Integrable (fun t : ℝ =>
      (2 * x ^ ((1 : ℝ) / 2 - ρ.re) * (3 * Real.sqrt q * (1 + Real.log q))
        * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
      * ((3 / 2 + T) * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
          + |t| * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)) :=
    (((integrable_inv_sq_add_sq_rpow hm).const_mul (3 / 2 + T)).add
      (integrable_abs_mul_inv_sq_add_sq_rpow hm)).const_mul _
  have hnormle : ‖∫ t : ℝ, jutilaIntegrand χ z₁ z₂ R x ρ
        (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, (2 * x ^ ((1 : ℝ) / 2 - ρ.re) * (3 * Real.sqrt q * (1 + Real.log q))
        * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
      * ((3 / 2 + T) * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
          + |t| * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
    refine MeasureTheory.norm_integral_le_of_norm_le hgint
      (Filter.Eventually.of_forall (fun t => ?_))
    have hwre : (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
        neg_zero, add_zero]
      ring
    have hwim : (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)).im = ρ.im + t := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
        zero_add]
    have hw1 : (1 : ℝ) / 2 ≤ (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)).re :=
      le_of_eq hwre.symm
    have hw2 : (ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)).re ≤ 4 := by
      rw [hwre]; norm_num
    have hbase := norm_jutilaIntegrand_le hχ hq hz₁ hz hR hx0 ρ _ hw1 hw2
    have hure : (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 - ρ.re := by simp
    rw [hure] at hbase
    have hnb : ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 1 / 2 + T + |t| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hwre, hwim, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
      have h1 : |ρ.im + t| ≤ |ρ.im| + |t| := abs_add_le _ _
      linarith
    have hcube := norm_inv_denom2_cubic_le_of_min (σ := 1 / 2 - ρ.re) (m := 59 / 120) hm
      hm0 hm1 hm2 t
    have hc0 : (0 : ℝ) ≤ 3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖)
        * Real.sqrt q * (1 + Real.log q) :=
      mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (by linarith)
    have hbb : 3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q
          * (1 + Real.log q)
        ≤ 3 * (3 / 2 + T + |t|) * Real.sqrt q * (1 + Real.log q) := by
      have h3 : 3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖)
          ≤ 3 * (3 / 2 + T + |t|) := by linarith
      calc 3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q
              * (1 + Real.log q)
          = (3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖))
            * (Real.sqrt q * (1 + Real.log q)) := by ring
        _ ≤ (3 * (3 / 2 + T + |t|)) * (Real.sqrt q * (1 + Real.log q)) :=
            mul_le_mul_of_nonneg_right h3 hpv
        _ = 3 * (3 / 2 + T + |t|) * Real.sqrt q * (1 + Real.log q) := by ring
    have hstep := mul5_le (a₁ := (2 : ℝ)) (a₂ := (2 : ℝ))
      (b₁ := x ^ ((1 : ℝ) / 2 - ρ.re)) (b₂ := x ^ ((1 : ℝ) / 2 - ρ.re))
      (c₁ := 3 * (1 + ‖ρ + (((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)‖) * Real.sqrt q
        * (1 + Real.log q))
      (c₂ := 3 * (3 / 2 + T + |t|) * Real.sqrt q * (1 + Real.log q))
      (d₁ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)) (d₂ := 2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ))
      (e₁ := ‖((((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I)
          * ((((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I) + 1)
          * ((((1 / 2 - ρ.re : ℝ) : ℂ) + (t : ℂ) * I) + 2))⁻¹‖)
      (e₂ := ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
      (by norm_num) (Real.rpow_nonneg hx0.le _) hc0 (by positivity) (norm_nonneg _)
      le_rfl le_rfl hbb le_rfl hcube
    refine (hbase.trans hstep).trans (le_of_eq ?_)
    ring
  have hgeq : (∫ t : ℝ, (2 * x ^ ((1 : ℝ) / 2 - ρ.re) * (3 * Real.sqrt q * (1 + Real.log q))
        * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
      * ((3 / 2 + T) * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹
          + |t| * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹))
      = (2 * x ^ ((1 : ℝ) / 2 - ρ.re) * (3 * Real.sqrt q * (1 + Real.log q))
          * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
        * ((3 / 2 + T) * (∫ t : ℝ, ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹)
          + ∫ t : ℝ, |t| * ((((59 : ℝ) / 120) ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add ((integrable_inv_sq_add_sq_rpow hm).const_mul (3 / 2 + T))
        (integrable_abs_mul_inv_sq_add_sq_rpow hm), MeasureTheory.integral_const_mul]
  have hI1 := integral_inv_sq_add_sq_rpow_le hm
  have hI2 := integral_abs_mul_inv_sq_add_sq_rpow_le hm
  have hfin : 1 / (2 * Real.pi) * ((2 * x ^ ((1 : ℝ) / 2 - ρ.re)
        * (3 * Real.sqrt q * (1 + Real.log q)) * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
      * ((3 / 2 + T) * (Real.pi / ((59 : ℝ) / 120) ^ 2) + Real.pi / ((59 : ℝ) / 120)))
      ≤ 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - ρ.re) := by
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hfac : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q)
        * (Real.sqrt z₂ * R ^ (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2 - ρ.re)) := by
      refine mul_nonneg hpv (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_) ?_)
      · exact Real.rpow_nonneg hR _
      · exact Real.rpow_nonneg hx0.le _
    have hnum : (6 : ℝ) * ((3 / 2 + T) * (120 / 59) ^ 2 + 120 / 59) ≤ 25 * (T + 2) := by
      nlinarith [hT0]
    have heq : 1 / (2 * Real.pi) * ((2 * x ^ ((1 : ℝ) / 2 - ρ.re)
          * (3 * Real.sqrt q * (1 + Real.log q)) * (2 * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)))
        * ((3 / 2 + T) * (Real.pi / ((59 : ℝ) / 120) ^ 2) + Real.pi / ((59 : ℝ) / 120)))
        = (6 * ((3 / 2 + T) * (120 / 59) ^ 2 + 120 / 59))
          * (Real.sqrt q * (1 + Real.log q)
            * (Real.sqrt z₂ * R ^ (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2 - ρ.re))) := by
      field_simp
      ring
    rw [heq]
    calc (6 * ((3 / 2 + T) * (120 / 59) ^ 2 + 120 / 59))
          * (Real.sqrt q * (1 + Real.log q)
            * (Real.sqrt z₂ * R ^ (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2 - ρ.re)))
        ≤ (25 * (T + 2)) * (Real.sqrt q * (1 + Real.log q)
            * (Real.sqrt z₂ * R ^ (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2 - ρ.re))) :=
          mul_le_mul_of_nonneg_right hnum hfac
      _ = 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
            * x ^ ((1 : ℝ) / 2 - ρ.re) := by ring
  rw [jutilaFull_mellin χ hz R hx0 hcpos (by linarith),
    integral_jutilaIntegrand_shift hχ hq hz₁ hz hR hx h0 hβ' hβ1, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  refine le_trans (mul_le_mul_of_nonneg_left hnormle (by positivity)) ?_
  rw [hgeq]
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hKnn)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))) hfin
  have h32 : (0 : ℝ) ≤ 3 / 2 + T := by linarith
  nlinarith [hI1, hI2, h32]

/-! ## (vi) The floor (2.10) -/

theorem jutilaDetector_floor_at_zero [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ} (hR : 1 ≤ R) {x : ℝ}
    (hx : 1 ≤ x) {ρ : ℂ} (h0 : LFunction χ ρ = 0) (hβ : (119 : ℝ) / 120 ≤ ρ.re) (hβ1 : ρ.re < 1)
    {T : ℝ} (hρT : |ρ.im| ≤ T) :
    (1 - 1 / x) ^ 2 * (6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R)
      - 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - ρ.re)
      ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hq1 : 1 ≤ q := by omega
  have hsplit := jutilaFull_eq_add_detector χ hz₁ hz R hx ρ
  have hdet : jutilaDetector χ z₁ z₂ R x ρ
      = jutilaFull χ z₁ z₂ R x ρ
        - ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x) := by
    rw [hsplit]; ring
  have hsum0 : (0 : ℝ) ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun r _ => by positivity)
  have hxx : (0 : ℝ) ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hx0]
    exact hx
  have hker : ‖((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x)‖
      = (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) * (1 - 1 / x) ^ 2 := by
    rw [kern2_value hx0, if_pos hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsum0, norm_pow]
    congr 1
    rw [show (1 : ℂ) - 1 / (x : ℂ) = ((1 - 1 / x : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxx]
  have hrev : (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) * (1 - 1 / x) ^ 2
      - ‖jutilaFull χ z₁ z₂ R x ρ‖ ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
    rw [hdet, ← hker]
    have h := norm_sub_norm_le
      (((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x)) (jutilaFull χ z₁ z₂ R x ρ)
    rw [norm_sub_rev] at h
    linarith
  have hL5 : 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R
      ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ := by
    have h := sum_sf_coprime_inv_ge q R hq1 hR
    simp only [one_div] at h
    exact h
  have hmul : (1 - 1 / x) ^ 2 * (6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R)
      ≤ (1 - 1 / x) ^ 2 * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hL5 (by positivity)
  have hE := norm_jutilaFull_le hχ hq hz₁ hz (le_trans zero_le_one hR) hx h0 hβ hβ1 hρT
  linarith [hrev, hmul, hE]

/-! ## (vii) F5's table as hypotheses: the corollary with the explicit threshold -/

/-- `∏_{p ∈ S} p/(p−1) ≤ |S| + 1`: peel the LARGEST prime, `|S'| ≤ p − 2`. -/
private lemma prod_prime_div_pred_le (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) → ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (S.card : ℝ) + 1 := by
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
      intro hS
      have ha : a.Prime := hS a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have hans : a ∉ s := fun h => lt_irrefl a (hlt a h)
      rw [Finset.prod_insert hans, Finset.card_insert_of_notMem hans]
      have ha2 : 2 ≤ a := ha.two_le
      have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
        intro y hy
        rw [Finset.mem_Icc]
        have hya := hlt y hy
        exact ⟨(hs y hy).two_le, by omega⟩
      have hcard : s.card ≤ a - 2 := by
        have hle := Finset.card_le_card hsub
        rw [Nat.card_Icc] at hle
        omega
      have hca : (s.card : ℝ) + 2 ≤ (a : ℝ) := by
        have hn : s.card + 2 ≤ a := by omega
        exact_mod_cast hn
      have haR : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha.one_lt
      have hIH := ih hs
      have hprodnn : (0 : ℝ) ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
        refine Finset.prod_nonneg (fun p hp => ?_)
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hs p hp).two_le
        exact div_nonneg (by linarith) (by linarith)
      have hfrac : (0 : ℝ) < (a : ℝ) / ((a : ℝ) - 1) := div_pos (by linarith) (by linarith)
      calc (a : ℝ) / ((a : ℝ) - 1) * ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1))
          ≤ (a : ℝ) / ((a : ℝ) - 1) * ((s.card : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hIH hfrac.le
        _ ≤ ((s.card : ℝ) + 1) + 1 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < (a : ℝ) - 1)]
            nlinarith [hca]
        _ = ((s.card + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

theorem div_totient_le_card_primeFactors_add_one (q : ℕ) :
    (q : ℝ) / Nat.totient q ≤ q.primeFactors.card + 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hφR : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hφ
  have hprimes : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprimes p hp).two_le
    linarith
  have hcast : ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p hp => by
      rw [Nat.cast_sub (hprimes p hp).one_le, Nat.cast_one])
  have hkey : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
      = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    calc (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ)
        = ((Nat.totient q * ∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ = ((q * ∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [h]
      _ = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by rw [Nat.cast_mul, hcast]
  have heq : (q : ℝ) / Nat.totient q
      = (∏ p ∈ q.primeFactors, (p : ℝ)) / ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [div_eq_div_iff hφR.ne' hQpos.ne']
    linarith
  rw [heq, ← Finset.prod_div_distrib]
  exact prod_prime_div_pred_le q.primeFactors hprimes

theorem card_primeFactors_le_log_div_log_two (q : ℕ) :
    (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  by_cases hq1 : q = 1
  · subst hq1
    norm_num
  have h2 : (2 : ℕ) ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h3 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have h4 : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast le_trans h2 h3
  have hlog := Real.log_le_log (by positivity) h4
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  linarith

theorem inv_log_le_totient_div {q : ℕ} (hq : 1 ≤ q) :
    1 / (Real.log q / Real.log 2 + 1) ≤ (Nat.totient q : ℝ) / q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hφR : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hφ
  have h1 := div_totient_le_card_primeFactors_add_one q
  have h2 := card_primeFactors_le_log_div_log_two q
  have h3 : (q : ℝ) / Nat.totient q ≤ Real.log q / Real.log 2 + 1 := by linarith
  have h4 : (0 : ℝ) < (q : ℝ) / Nat.totient q := div_pos hq0 hφR
  have h5 := one_div_le_one_div_of_le h4 h3
  rwa [one_div_div] at h5

theorem f5_error_bound {q : ℕ} (hq : 1 ≤ q) {T D R x : ℝ} (hT : 1 ≤ T) (hD : D = q * T)
    (hR : R = D ^ ((1 : ℝ) / 10)) {z₂ : ℕ} (hz₂ : (z₂ : ℝ) ≤ D ^ ((7 : ℝ) / 2))
    (hx : D ^ ((13 : ℝ) / 2) ≤ x) {β : ℝ} (hβ : (119 : ℝ) / 120 ≤ β) (hβ1 : β < 1) :
    25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - β)
      ≤ 75 * (1 + Real.log D) * D ^ (-(71 / 240 : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; nlinarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_rpow hD1 (by norm_num)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hqD : (q : ℝ) ≤ D := by rw [hD]; nlinarith
  have b1 : 25 * (T + 2) ≤ 25 * (3 * T) := by linarith
  have b2 : Real.sqrt q ≤ (q : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (q : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hqpos.le] at h
  have b3 : 1 + Real.log q ≤ 1 + Real.log D := by
    have h := Real.log_le_log hqpos hqD
    linarith
  have b4 : Real.sqrt z₂ ≤ D ^ ((7 : ℝ) / 4) := by
    have hDr : Real.sqrt (D ^ ((7 : ℝ) / 2)) = D ^ ((7 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hDpos.le]
      norm_num
    calc Real.sqrt z₂ ≤ Real.sqrt (D ^ ((7 : ℝ) / 2)) := Real.sqrt_le_sqrt hz₂
      _ = D ^ ((7 : ℝ) / 4) := hDr
  have b5 : R ^ (3 / 2 : ℝ) = D ^ ((3 : ℝ) / 20) := by
    rw [hR, ← Real.rpow_mul hDpos.le]
    norm_num
  have b6 : x ^ ((1 : ℝ) / 2 - β) ≤ D ^ (-(767 / 240) : ℝ) := by
    have e1 : x ^ ((1 : ℝ) / 2 - β) ≤ x ^ (-(59 / 120) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have e2 : (D ^ ((13 : ℝ) / 2)) ^ ((59 : ℝ) / 120) ≤ x ^ ((59 : ℝ) / 120) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hDpos.le _) hx (by norm_num)
    have e3 : x ^ (-(59 / 120) : ℝ) = (x ^ ((59 : ℝ) / 120))⁻¹ := Real.rpow_neg hx0.le _
    have e4 : (D ^ ((13 : ℝ) / 2)) ^ ((59 : ℝ) / 120) = D ^ ((767 : ℝ) / 240) := by
      rw [← Real.rpow_mul hDpos.le]
      norm_num
    have e5 : D ^ (-(767 / 240) : ℝ) = (D ^ ((767 : ℝ) / 240))⁻¹ := Real.rpow_neg hDpos.le _
    rw [e3] at e1
    rw [e4] at e2
    rw [e5]
    exact e1.trans (inv_anti₀ (Real.rpow_pos_of_pos hDpos _) e2)
  have hpw : D ^ ((1 : ℝ)) * D ^ ((7 : ℝ) / 4) * D ^ ((3 : ℝ) / 20)
      * D ^ (-(767 / 240) : ℝ) = D ^ (-(71 / 240) : ℝ) := by
    have p1 : D ^ ((1 : ℝ)) * D ^ ((7 : ℝ) / 4) = D ^ ((1 : ℝ) + 7 / 4) :=
      (Real.rpow_add hDpos _ _).symm
    have p2 : D ^ ((1 : ℝ) + 7 / 4) * D ^ ((3 : ℝ) / 20) = D ^ ((1 : ℝ) + 7 / 4 + 3 / 20) :=
      (Real.rpow_add hDpos _ _).symm
    have p3 : D ^ ((1 : ℝ) + 7 / 4 + 3 / 20) * D ^ (-(767 / 240) : ℝ)
        = D ^ ((1 : ℝ) + 7 / 4 + 3 / 20 + -(767 / 240)) := (Real.rpow_add hDpos _ _).symm
    rw [p1, p2, p3]
    norm_num
  rw [Real.rpow_one] at hpw
  have hfinal : 25 * (3 * T) * (q : ℝ) * (1 + Real.log D) * D ^ ((7 : ℝ) / 4)
        * D ^ ((3 : ℝ) / 20) * D ^ (-(767 / 240) : ℝ)
      = 75 * (1 + Real.log D) * D ^ (-(71 / 240) : ℝ) := by
    calc 25 * (3 * T) * (q : ℝ) * (1 + Real.log D) * D ^ ((7 : ℝ) / 4) * D ^ ((3 : ℝ) / 20)
          * D ^ (-(767 / 240) : ℝ)
        = 75 * (1 + Real.log D) * (((q : ℝ) * T) * D ^ ((7 : ℝ) / 4) * D ^ ((3 : ℝ) / 20)
            * D ^ (-(767 / 240) : ℝ)) := by ring
      _ = 75 * (1 + Real.log D) * (D * D ^ ((7 : ℝ) / 4) * D ^ ((3 : ℝ) / 20)
            * D ^ (-(767 / 240) : ℝ)) := by rw [← hD]
      _ = 75 * (1 + Real.log D) * D ^ (-(71 / 240) : ℝ) := by rw [hpw]
  calc 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - β)
      ≤ 25 * (3 * T) * (q : ℝ) * (1 + Real.log D) * D ^ ((7 : ℝ) / 4) * D ^ ((3 : ℝ) / 20)
        * D ^ (-(767 / 240) : ℝ) :=
        mul6_le (by linarith) (Real.sqrt_nonneg _) (by linarith) (Real.sqrt_nonneg _)
          (by rw [hR]; positivity) (Real.rpow_nonneg hx0.le _) b1 b2 b3 b4 (le_of_eq b5) b6
    _ = 75 * (1 + Real.log D) * D ^ (-(71 / 240) : ℝ) := hfinal

/-- `46 ≤ log 10²⁰` (the `hu46` cut) with NO decimal for `log 10`: `e ≤ 2.72`, `2.72^46 ≤ 10²⁰`. -/
private lemma le_log_ten_pow_twenty : (46 : ℝ) ≤ Real.log ((10 : ℝ) ^ 20) := by
  have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have h1 : Real.exp 46 = Real.exp 1 ^ (46 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h46 : Real.exp 46 ≤ (10 : ℝ) ^ 20 := by
    rw [h1]
    calc Real.exp 1 ^ (46 : ℕ) ≤ (2.72 : ℝ) ^ (46 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le he1 46
      _ ≤ (10 : ℝ) ^ 20 := by norm_num
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact h46

theorem f5_exp_dominates {u : ℝ} (hu : Real.log ((10 : ℝ) ^ 20) ≤ u) :
    5625 * u ≤ Real.exp (71 / 240 * u) := by
  have hu46 : (46 : ℝ) ≤ u := le_trans le_log_ten_pow_twenty hu
  have hexp13 : (442413 : ℝ) ≤ Real.exp 13 := by
    have h1 : Real.exp 13 = Real.exp 1 ^ (13 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h1]
    calc (442413 : ℝ) ≤ (2.7182818283 : ℝ) ^ (13 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (13 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 13
  have hfrac : (193 : ℝ) / 120 ≤ Real.exp (73 / 120) := by
    linarith [Real.add_one_le_exp ((73 : ℝ) / 120)]
  have h46a : (711500 : ℝ) ≤ Real.exp (71 / 240 * 46) := by
    have hsplit : Real.exp (71 / 240 * 46) = Real.exp 13 * Real.exp (73 / 120) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    rw [hsplit]
    calc (711500 : ℝ) ≤ 442413 * (193 / 120) := by norm_num
      _ ≤ Real.exp 13 * Real.exp (73 / 120) :=
          mul_le_mul hexp13 hfrac (by norm_num) (Real.exp_pos 13).le
  have hlin : (1 : ℝ) + 71 / 240 * (u - 46) ≤ Real.exp (71 / 240 * (u - 46)) := by
    linarith [Real.add_one_le_exp (71 / 240 * (u - 46))]
  have hprod : (711500 : ℝ) * (1 + 71 / 240 * (u - 46)) ≤ Real.exp (71 / 240 * u) := by
    have hsplit : Real.exp (71 / 240 * u)
        = Real.exp (71 / 240 * 46) * Real.exp (71 / 240 * (u - 46)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul h46a hlin (by linarith) (Real.exp_pos _).le
  linarith [hprod, hu46]

theorem f5_error_le_main {D : ℝ} (hD : (10 : ℝ) ^ 20 ≤ D) :
    75 * (1 + Real.log D) * D ^ (-(71 / 240 : ℝ))
      ≤ 2 / Real.pi ^ 2 * (1 / (Real.log D / Real.log 2 + 1)) * (Real.log D / 10) := by
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hD
  have hu : Real.log ((10 : ℝ) ^ 20) ≤ Real.log D := Real.log_le_log (by norm_num) hD
  have hu46 : (46 : ℝ) ≤ Real.log D := le_trans le_log_ten_pow_twenty hu
  have hu0 : (0 : ℝ) < Real.log D := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hlog2ne : Real.log 2 ≠ 0 := hlog2pos.ne'
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπ.ne'
  have hπ2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hden : (0 : ℝ) < Real.log D / Real.log 2 + 1 := by positivity
  have hdenne : Real.log D / Real.log 2 + 1 ≠ 0 := hden.ne'
  have hE : (0 : ℝ) < Real.exp (71 / 240 * Real.log D) := Real.exp_pos _
  have hexp := f5_exp_dominates hu
  have hDrpow : D ^ (-(71 / 240 : ℝ)) = (Real.exp (71 / 240 * Real.log D))⁻¹ := by
    rw [Real.rpow_def_of_pos hDpos, ← Real.exp_neg]
    congr 1
    ring
  have h1 : Real.log D / Real.log 2 ≤ 1.4427 * Real.log D := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hu0, hlog2]
  have hf0 : (0 : ℝ) ≤ (1 + Real.log D) * (Real.log D / Real.log 2 + 1) := by positivity
  have hX : (1 + Real.log D) * (Real.log D / Real.log 2 + 1)
      ≤ (1 + Real.log D) * (1.4427 * Real.log D + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hkey : 375 * Real.pi ^ 2 * ((1 + Real.log D) * (Real.log D / Real.log 2 + 1))
      ≤ Real.log D * Real.exp (71 / 240 * Real.log D) := by
    have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ 10 - Real.pi ^ 2) hf0
    have h2 : 375 * Real.pi ^ 2 * ((1 + Real.log D) * (Real.log D / Real.log 2 + 1))
        ≤ 375 * 10 * ((1 + Real.log D) * (1.4427 * Real.log D + 1)) := by
      nlinarith [hprod, hX]
    have h3 : 375 * 10 * ((1 + Real.log D) * (1.4427 * Real.log D + 1))
        ≤ 5625 * Real.log D * Real.log D := by
      nlinarith [hu46, sq_nonneg (Real.log D - 46)]
    have h4 : 5625 * Real.log D * Real.log D
        ≤ Real.log D * Real.exp (71 / 240 * Real.log D) := by
      nlinarith [mul_nonneg hu0.le
        (by linarith : (0 : ℝ) ≤ Real.exp (71 / 240 * Real.log D) - 5625 * Real.log D)]
    linarith
  rw [hDrpow, show (2 : ℝ) / Real.pi ^ 2 * (1 / (Real.log D / Real.log 2 + 1))
        * (Real.log D / 10)
      = Real.log D / (5 * Real.pi ^ 2 * (Real.log D / Real.log 2 + 1)) from by
        field_simp; ring,
    inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ hE (mul_pos (by positivity) hden)]
  nlinarith [hkey]

theorem jutilaDetector_floor_F5 [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {T D R x : ℝ} (hT : 1 ≤ T)
    (hD : D = q * T) (hD0 : (10 : ℝ) ^ 20 ≤ D) (hR : R = D ^ ((1 : ℝ) / 10))
    (hz₂ : (z₂ : ℝ) ≤ D ^ ((7 : ℝ) / 2)) (hx : D ^ ((13 : ℝ) / 2) ≤ x) {ρ : ℂ}
    (h0 : LFunction χ ρ = 0) (hβ : (119 : ℝ) / 120 ≤ ρ.re) (hβ1 : ρ.re < 1) (hρT : |ρ.im| ≤ T) :
    3 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
  have hq1 : 1 ≤ q := by omega
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hD1 : (1 : ℝ) ≤ D := le_trans (by norm_num) hD0
  have hD12 : (12 : ℝ) ≤ D := le_trans (by norm_num) hD0
  have hDpos : (0 : ℝ) < D := by linarith
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]
    exact Real.one_le_rpow hD1 (by norm_num)
  have hxD : D ≤ x := by
    refine le_trans ?_ hx
    have h1 : D ^ (1 : ℝ) ≤ D ^ ((13 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have hx12 : (12 : ℝ) ≤ x := le_trans hD12 hxD
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hfloor := jutilaDetector_floor_at_zero hχ hq hz₁ hz hR1 hx1 h0 hβ hβ1 hρT
  have hE := f5_error_bound hq1 hT hD hR hz₂ hx hβ hβ1
  have hM := f5_error_le_main hD0
  have hφ := inv_log_le_totient_div hq1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hqD : (q : ℝ) ≤ D := by rw [hD]; nlinarith
  have hlogqD : Real.log q ≤ Real.log D :=
    Real.log_le_log (by linarith) hqD
  have hdd : Real.log q / Real.log 2 ≤ Real.log D / Real.log 2 := by
    rw [div_le_div_iff₀ hlog2pos hlog2pos]
    nlinarith
  have hqden : (0 : ℝ) < Real.log q / Real.log 2 + 1 := by
    have hnn : (0 : ℝ) ≤ Real.log q / Real.log 2 := div_nonneg hlogq hlog2pos.le
    linarith
  have hinv : 1 / (Real.log D / Real.log 2 + 1) ≤ 1 / (Real.log q / Real.log 2 + 1) :=
    one_div_le_one_div_of_le hqden (by linarith)
  have hchain : 75 * (1 + Real.log D) * D ^ (-(71 / 240 : ℝ))
      ≤ 2 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) := by
    refine hM.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_
    · exact le_trans hinv hφ
    · linarith
  have hlogR : Real.log R = Real.log D / 10 := by
    rw [hR, Real.log_rpow hDpos]
    ring
  rw [hlogR] at hfloor ⊢
  have h1x : (1 : ℝ) / x ≤ 1 / 12 := by
    rw [div_le_div_iff₀ hxpos (by norm_num)]
    linarith
  have h2x : (11 : ℝ) / 12 ≤ 1 - 1 / x := by linarith
  have hfive : (5 : ℝ) / 6 ≤ (1 - 1 / x) ^ 2 := by
    calc (5 : ℝ) / 6 ≤ (11 / 12 : ℝ) * (11 / 12) := by norm_num
      _ ≤ (1 - 1 / x) * (1 - 1 / x) := mul_le_mul h2x h2x (by norm_num) (by linarith)
      _ = (1 - 1 / x) ^ 2 := by ring
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ,
      W = 1 / Real.pi ^ 2 * (((Nat.totient q : ℝ) / q) * (Real.log D / 10)) := ⟨_, rfl⟩
  have hW : (0 : ℝ) ≤ W := by
    rw [hWdef]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))
  have e6 : 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) = 6 * W := by
    rw [hWdef]; ring
  have e3 : 3 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) = 3 * W := by
    rw [hWdef]; ring
  have e2 : 2 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) = 2 * W := by
    rw [hWdef]; ring
  rw [e6] at hfloor
  rw [e2] at hchain
  rw [e3]
  have hstep : 5 * W ≤ (1 - 1 / x) ^ 2 * (6 * W) := by
    linarith only [mul_nonneg (by linarith only [hfive] :
      (0 : ℝ) ≤ (1 - 1 / x) ^ 2 - 5 / 6) hW]
  linarith only [hfloor, hE, hchain, hstep]

/-! ## The exit rows (§2 of the sub-freeze): each INVOKES a frozen row -/

/-- The split at the smallest live instance (`q = 1`, the trivial character; `z₁ = 2`, `z₂ = 3`,
`R = 1`, `x = 2`, `s = 2`): it INVOKES `jutilaFull_eq_add_detector`. Measured at `x = 12`,
`(4, 16, 6)`, `χ mod 5`: exact to `4.6e−17`; with the one-level weight it fails by `1.7e−2`. -/
example : jutilaFull (1 : DirichletCharacter ℂ 1) 2 3 1 2 2
    = ((∑ r ∈ rFilter 1 1, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / 2)
      + jutilaDetector (1 : DirichletCharacter ℂ 1) 2 3 1 2 2 :=
  jutilaFull_eq_add_detector 1 (by norm_num) (by norm_num) 1 (by norm_num) 2

/-- The F5 numeral at the threshold itself, INVOKING `f5_exp_dominates`: `5625·log 10²⁰ = 259,041`
against `e^{(71/240)·log 10²⁰} = 825,404`. -/
example : 5625 * Real.log ((10 : ℝ) ^ 20) ≤ Real.exp (71 / 240 * Real.log ((10 : ℝ) ^ 20)) :=
  f5_exp_dominates le_rfl

end Salt.SW

end
