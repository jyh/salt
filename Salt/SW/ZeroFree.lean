/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MaxModulus
import Salt.SW.BCBound
import Salt.SW.ThreeFourOne
import Salt.SW.ZetaPole
import Salt.SW.EulerBridge

/-!
# The SW rung, node S3d — the quantitative zero-free region (Davenport §14)

Design: `docs/blueprints/sw.md`, S3 row (the S3 keystone assembly). This module assembles
the S3 sub-nodes (S3a–S3c) and the S2 endpoint (`LFunction_norm_logDeriv_sub_sum'`) into the
classical quantitative zero-free region uniform in `q`.
-/

namespace Salt.SW

open Complex DirichletCharacter Filter Metric
open scoped LSeries.notation Topology

/-! ## 1. The LSeries ↔ LFunction log-derivative bridge (on `Re s > 1`) -/

/-- On `Re s > 1`, the LSeries logarithmic derivative equals the `LFunction` logarithmic
derivative: `−(LSeries ↗ψ)'/(LSeries ↗ψ)(s) = −logDeriv (LFunction ψ)(s)`. This bridges the
`three_four_one_logDeriv` carrier (stated in `LSeries` form) to the `LFunction` objects the
S2/S3 numeric bounds are about. -/
lemma neg_logDeriv_LSeries_eq {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (LSeries ↗ψ) s / LSeries ↗ψ s = -logDeriv (LFunction ψ) s := by
  have h1 : LFunction ψ s = LSeries ↗ψ s := LFunction_eq_LSeries ψ hs
  have h2 : deriv (LFunction ψ) s = deriv (LSeries ↗ψ) s := deriv_LFunction_eq_deriv_LSeries ψ hs
  rw [logDeriv_apply, h1, h2, neg_div]

/-! ## 2. The growth-quantity log bound `log(4 M₀) ≤ 6·L` -/

/-- The growth-sphere quantity feeds into the region as `log(4 M₀(f,t)) = O(log(q(|γ|+2)))`.
Concretely, for `2 ≤ f ≤ q` and `|t| ≤ 2|γ|` (the two instances `f = q, t = γ` and
`f = f₂ ≤ q, t = 2γ` used below),
`log(4·5(4+|t|)√f(1+log f)) ≤ 6·log(q(|γ|+2))`. Route: bound the product by `Q^6`
(`Q = q(|γ|+2)`) factorwise (`20 ≤ Q³`, `4+|t| ≤ Q`, `√f ≤ Q`, `1+log f ≤ f ≤ Q`) and take
logs. -/
lemma log_four_M0_le {f q : ℕ} {t γ : ℝ} (hf2 : 2 ≤ f) (hfq : f ≤ q) (hq2 : 2 ≤ q)
    (ht : |t| ≤ 2 * |γ|) :
    Real.log (4 * (5 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))))
      ≤ 6 * Real.log ((q : ℝ) * (|γ| + 2)) := by
  have hγ0 : (0 : ℝ) ≤ |γ| := abs_nonneg γ
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hf2R : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf2
  have hfqR : (f : ℝ) ≤ (q : ℝ) := by exact_mod_cast hfq
  have hfpos : (0 : ℝ) < (f : ℝ) := by linarith
  set Q : ℝ := (q : ℝ) * (|γ| + 2) with hQ
  have hQ4 : (4 : ℝ) ≤ Q := by
    rw [hQ]; nlinarith [mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) hγ0, hq2R]
  have hQpos : (0 : ℝ) < Q := by linarith
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; nlinarith [hq2R, hγ0]
  have hfQ : (f : ℝ) ≤ Q := le_trans hfqR hqQ
  have hlogf_nn : (0 : ℝ) ≤ Real.log (f : ℝ) := Real.log_nonneg (by linarith)
  -- the four factor bounds
  have hb20 : (20 : ℝ) ≤ Q ^ 3 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hQ4 3)
  have hb1 : (4 + |t|) ≤ Q := by
    rw [hQ]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (q:ℝ) - 2 by linarith) (show (0:ℝ) ≤ |γ| + 2 by linarith),
      ht]
  have hQQ2 : Q ≤ Q ^ 2 := by nlinarith [hQ4]
  have hb2 : Real.sqrt (f : ℝ) ≤ Q := by
    rw [show Q = Real.sqrt (Q ^ 2) from (Real.sqrt_sq hQpos.le).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hfQ, hQQ2])
  have hb3 : (1 + Real.log (f : ℝ)) ≤ Q := by
    have hle : Real.log (f : ℝ) + 1 ≤ (f : ℝ) := by
      have h := Real.add_one_le_exp (Real.log (f : ℝ)); rwa [Real.exp_log hfpos] at h
    linarith [hfQ]
  -- nonnegativities
  have hn1 : (0 : ℝ) ≤ 4 + |t| := by positivity
  have hn2 : (0 : ℝ) ≤ Real.sqrt (f : ℝ) := Real.sqrt_nonneg _
  have hn3 : (0 : ℝ) ≤ 1 + Real.log (f : ℝ) := by linarith [hlogf_nn]
  have hnQ3 : (0 : ℝ) ≤ Q ^ 3 := by positivity
  -- assemble the product bound and take logs
  have hprod : 4 * (5 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) ≤ Q ^ 6 := by
    calc 4 * (5 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)))
        = 20 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) := by ring
      _ ≤ Q ^ 3 * Q * Q * Q :=
          mul_le_mul (mul_le_mul (mul_le_mul hb20 hb1 hn1 hnQ3) hb2 hn2
            (mul_nonneg hnQ3 hQpos.le)) hb3 hn3
            (mul_nonneg (mul_nonneg hnQ3 hQpos.le) hQpos.le)
      _ = Q ^ 6 := by ring
  have hposarg : (0 : ℝ) < 4 * (5 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by
    have : (0 : ℝ) < Real.sqrt (f : ℝ) := Real.sqrt_pos.mpr hfpos
    positivity
  calc Real.log (4 * (5 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))))
      ≤ Real.log (Q ^ 6) := Real.log_le_log hposarg hprod
    _ = 6 * Real.log Q := by rw [Real.log_pow]; push_cast; ring

/-! ## 3. A ball-zero lies in the partial-fraction zero set -/

/-- Given a `LFunction_norm_logDeriv_sub_sum'`-shaped factorization `L = P·h` on `ball c r` with
`h` non-vanishing, any zero `ρ` of `L` inside the ball lies in the finite zero set `Z` with
multiplicity `m ρ ≥ 1`. (`L(ρ) = P(ρ)·h(ρ)`, `h(ρ) ≠ 0` ⟹ `P(ρ) = 0` ⟹ some factor vanishes.) -/
lemma mem_zeros_of_factorization {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {c : ℂ} {r : ℝ} {Z : Finset ℂ} {m : ℂ → ℕ} {h : ℂ → ℂ}
    (hne_h : ∀ z ∈ ball c r, h z ≠ 0)
    (hEqOn : Set.EqOn (LFunction χ) (fun z => (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) (ball c r))
    {ρ : ℂ} (hρball : ρ ∈ ball c r) (hρ0 : LFunction χ ρ = 0) :
    ρ ∈ Z ∧ 1 ≤ m ρ := by
  have hval : LFunction χ ρ = (∏ ρ' ∈ Z, (ρ - ρ') ^ (m ρ')) * h ρ := hEqOn hρball
  rw [hρ0] at hval
  have hhρ : h ρ ≠ 0 := hne_h ρ hρball
  have hP0 : (∏ ρ' ∈ Z, (ρ - ρ') ^ (m ρ')) = 0 :=
    (mul_eq_zero.mp hval.symm).resolve_right hhρ
  rw [Finset.prod_eq_zero_iff] at hP0
  obtain ⟨ρ', hρ'Z, hpow⟩ := hP0
  rw [pow_eq_zero_iff'] at hpow
  obtain ⟨hsub, hm⟩ := hpow
  have hρeq : ρ = ρ' := by rwa [sub_eq_zero] at hsub
  subst hρeq
  exact ⟨hρ'Z, Nat.one_le_iff_ne_zero.mpr hm⟩

/-! ## 4. Nonnegativity of the partial-fraction real-part terms -/

/-- For a point `s` to the right of every `ρ' ∈ Z` (`Re(s − ρ') > 0`, which holds when `Re s > 1`
and all `ρ' ∈ Z` are zeros of an `L`-function, hence `Re ρ' < 1`), each partial-fraction term
`(m ρ')·Re(1/(s−ρ'))` is nonnegative — so the whole sum may be dropped for an upper bound, or a
single zero kept for a lower bound. -/
lemma term_re_nonneg {Z : Finset ℂ} (m : ℂ → ℕ) {s : ℂ}
    (hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re) :
    ∀ ρ' ∈ Z, 0 ≤ (m ρ' : ℝ) * (1 / (s - ρ')).re := by
  intro ρ' hρ'
  refine mul_nonneg (by positivity) ?_
  rw [one_div, Complex.inv_re]
  exact div_nonneg (hpos ρ' hρ').le (Complex.normSq_nonneg _)

/-! ## 5. The numeric extraction (`σ = 1 + dd/L`, `dd = 1/(2C)`) -/

/-- The final Davenport algebra. With `σ = 1 + dd/L` and `C·dd = 1/2`, the 3-4-1 output
`4/(σ−β) ≤ 3/(σ−1) + C·L` forces `1 − β ≥ dd/(7L)`. (Cross-multiply, use `L·(σ−1) = dd`, and
`4B ≤ (7/2)(B+u)` with `B = σ−1`, `u = 1−β`.) -/
lemma zero_free_extraction {Lq β C dd : ℝ}
    (hL : 0 < Lq) (hdd : 0 < dd) (hCdd : C * dd = 1 / 2) (hβ : β < 1)
    (hchain : 4 / (dd / Lq + (1 - β)) ≤ 3 / (dd / Lq) + C * Lq) :
    dd / (7 * Lq) ≤ 1 - β := by
  set B : ℝ := dd / Lq with hBdef
  have hBpos : 0 < B := div_pos hdd hL
  have hBne : B ≠ 0 := ne_of_gt hBpos
  set u : ℝ := 1 - β with hudef
  have hupos : 0 < u := by rw [hudef]; linarith
  have hBupos : 0 < B + u := by linarith
  have hLB : Lq * B = dd := by rw [hBdef]; field_simp
  have hrw : 3 / B + C * Lq = (3 + C * Lq * B) / B := by field_simp
  rw [hrw, div_le_div_iff₀ hBupos hBpos] at hchain
  have hCLB : C * Lq * B = 1 / 2 := by rw [mul_assoc, hLB]; exact hCdd
  rw [hCLB] at hchain
  have hfin : B ≤ 7 * u := by nlinarith [hchain]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 7 * Lq)]
  rw [hBdef, div_le_iff₀ hL] at hfin
  nlinarith [hfin]

/-! ## 6. The two `−Re(L'/L)` bounds from the S2 endpoint -/

/-- **Drop-all-zeros bound.** For a primitive `ψ` mod `q ≥ 2`, at a point `s` in the `23/20`
region of the center `2 + it` with `Re s > 1`, `(−L'/L(s))·Re ≤ 120·log(4 M₀(q,t))`. All
partial-fraction terms `Re(1/(s−ρ'))` are dropped (nonnegative, since `Re ρ' < 1 < Re s`). -/
lemma neg_reLogDeriv_le_drop {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ.IsPrimitive) (hf : 2 ≤ q) (t : ℝ) {s : ℂ}
    (hsc : ‖s - (2 + (t : ℂ) * I)‖ ≤ 23 / 20) (hσ1 : 1 < s.re) :
    (-logDeriv (LFunction ψ) s).re
      ≤ 120 * Real.log (4 * (5 * (4 + |t|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
  obtain ⟨Z, m, h, hZmem, -, -, -, -, hnum⟩ := LFunction_norm_logDeriv_sub_sum' ψ hψ hf t
  have hψ1 : ψ ≠ 1 := ne_one_of_isPrimitive ψ hψ hf
  have hLs : LFunction ψ s ≠ 0 := LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (le_of_lt hσ1)
  have hre := neg_re_logDeriv_le (hnum s hsc hLs)
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : LFunction ψ ρ' = 0 := (hZmem ρ' hρ').2
    have hlt : ρ'.re < 1 := by
      by_contra hc
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (not_lt.mp hc) hρ'0
    rw [Complex.sub_re]; linarith
  have hsum_nn : 0 ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.sum_nonneg (term_re_nonneg m hpos)
  linarith [hre, hsum_nn]

/-- **Keep-one-zero bound.** For a primitive `ψ` mod `q ≥ 2` with a zero `ρ`, `1/2 < Re ρ < 1`,
and `1 < σ < 2`, at `s = σ + i·Im ρ` the zero `ρ` lies in the partial-fraction set, so its
positive term `1/(σ − Re ρ)` is retained:
`(−L'/L(s))·Re ≤ 120·log(4 M₀(q, Im ρ)) − 1/(σ − Re ρ)`. -/
lemma neg_reLogDeriv_le_keep {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ.IsPrimitive) (hf : 2 ≤ q) {ρ : ℂ} (hρ0 : LFunction ψ ρ = 0)
    (hβlt : 1 / 2 < ρ.re) (hβ1 : ρ.re < 1) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    (-logDeriv (LFunction ψ) ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
        - 1 / (σ - ρ.re) := by
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
  have hρball : ρ ∈ ball c (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hsub : ρ - c = ((ρ.re - 2 : ℝ) : ℂ) := by
      rw [hcdef]; apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)]
    linarith
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization hne_h hEqOn hρball hρ0
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : LFunction ψ ρ' = 0 := (hZmem ρ' hρ').2
    have hlt : ρ'.re < 1 := by
      by_contra hc
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (not_lt.mp hc) hρ'0
    rw [Complex.sub_re]; linarith [hsre]
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hsdef]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have hσρpos : 0 < σ - ρ.re := by linarith
  have hterm_re : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hsingle : (m ρ : ℝ) * (1 / (s - ρ)).re ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.single_le_sum (term_re_nonneg m hpos) hρZ
  have hlow : 1 / (σ - ρ.re) ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    have h1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have h2 : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    have h3 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by rw [hterm_re]; nlinarith [h1, h2]
    linarith [h3, hsingle]
  linarith [hre, hlow]

/-! ## 7. The quantitative zero-free region for primitive `χ` with `χ² ≠ 1` -/

/-- **S3d — the quantitative zero-free region (Davenport §14), primitive complex-character case.**
There is an explicit constant `c₀ > 0` such that for every primitive Dirichlet character `χ` mod
`q` with `χ² ≠ 1`, every zero `ρ` of `L(·,χ)` with `Re ρ ≥ 1/2` satisfies
`Re ρ ≤ 1 − c₀ / log(q(|Im ρ| + 2))`. Here `c₀ = 1/50456`.

Route (the 3-4-1 argument made quantitative): at `σ = 1 + δ/L` (`δ = 1/7208`,
`L = log(q(|γ|+2))`), the positivity `three_four_one_logDeriv` combines the pole bound
`Re(−L'/L(σ,χ₀)) ≤ 1/(σ−1)+1` (`neg_logDeriv_LFunction_trivChar_le`), the retained-zero bound
`Re(−L'/L(σ+iγ,χ)) ≤ 120 log(4M₀) − 1/(σ−β)` (`neg_reLogDeriv_le_keep`), and the dropped-zeros
`χ²` bound `Re(−L'/L(σ+2iγ,χ²)) ≤ 120 log(4M₀(f₂)) + log q` (`neg_reLogDeriv_le_drop` on the
primitive `χ²`-inducing character + the `EulerBridge` `≤ log q` correction). All growth terms are
`O(L)` (`log_four_M0_le`); `zero_free_extraction` extracts `1 − β ≥ δ/(7L)`. -/
theorem zero_free_region_primitive :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  refine ⟨1 / 50456, by norm_num, ?_⟩
  intro q hNe χ hχ hsq ρ hzero _hre
  -- basics
  have hχ1 : χ ≠ 1 := fun h => hsq (by rw [h, one_pow])
  have hcond : χ.conductor = q := hχ
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1
    have hqne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set Lval : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLdef
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * (|ρ.im| + 2) := by
    nlinarith [abs_nonneg ρ.im, hqR2, mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
  have hexp4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp4
  have hL1 : (1 : ℝ) ≤ Lval := le_trans h4 (Real.log_le_log (by norm_num) hQ4)
  have hLpos : (0 : ℝ) < Lval := by linarith
  have hLne : Lval ≠ 0 := ne_of_gt hLpos
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hzero
  rcases le_or_gt ρ.re (1 / 2) with hβle | hβgt
  · -- trivial branch: `Re ρ ≤ 1/2 ≤ 1 − c₀/L`
    have hc0 : (1 / 50456 : ℝ) / Lval ≤ 1 / 50456 := by
      rw [div_le_iff₀ hLpos]; nlinarith [hL1]
    linarith [hc0, hβle]
  · -- the 3-4-1 machinery
    set dd : ℝ := 1 / 7208 with hdddef
    have hddpos : (0 : ℝ) < dd := by norm_num
    have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
    set σ : ℝ := 1 + dd / Lval with hσdef
    have hddL : dd / Lval ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
    have hσ1 : 1 < σ := by
      rw [hσdef]
      have hpos : 0 < dd / Lval := div_pos hddpos hLpos
      linarith
    have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
    -- the 3-4-1 positivity and the LSeries → LFunction bridge
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C, neg_logDeriv_LSeries_eq (χ ^ 2) hσ2C] at h341
    -- A₀ : the χ₀ pole bound
    have hA0 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 :=
      neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2.le
    -- A₁ : the retained-zero bound for χ
    have hA1 : (-logDeriv (LFunction χ) s1).re
        ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
          - 1 / (σ - ρ.re) := by
      have h := neg_reLogDeriv_le_keep χ hχ hq2 hzero hβgt hβ1 hσ1 hσ2
      rw [← hs1def] at h; exact h
    -- A₂ : the dropped-zeros bound for χ², via the primitive-inducing character + EulerBridge
    have hf2q : (χ ^ 2).conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level (χ ^ 2))
    have hf22 : 2 ≤ (χ ^ 2).conductor := by
      have hc1 : (χ ^ 2).conductor ≠ 1 := fun h => hsq (eq_one_iff_conductor_eq_one.mpr h)
      have hc0' : (χ ^ 2).conductor ≠ 0 := (χ ^ 2).conductor_ne_zero
      omega
    have hprim : ((χ ^ 2).primitiveCharacter).IsPrimitive := primitiveCharacter_isPrimitive (χ ^ 2)
    have hχ2'ne1 : (χ ^ 2).primitiveCharacter ≠ 1 := ne_one_of_isPrimitive _ hprim hf22
    have hL1s2 : LFunction (χ ^ 2).primitiveCharacter s2 ≠ 0 :=
      LFunction_ne_zero_of_one_le_re (χ ^ 2).primitiveCharacter (Or.inl hχ2'ne1) hσ2C.le
    have hsc2 : ‖s2 - (2 + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ 23 / 20 := by
      have he : s2 - (2 + ((2 * ρ.im : ℝ) : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
        rw [hs2def]; push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
      linarith
    have hdrop := neg_reLogDeriv_le_drop (χ ^ 2).primitiveCharacter hprim hf22 (2 * ρ.im) hsc2 hσ2C
    have hbr := norm_logDeriv_LFunction_sub_primitive_le (χ ^ 2) hσ2C.le hL1s2 (Or.inl hsq)
    have hA2 : (-logDeriv (LFunction (χ ^ 2)) s2).re
        ≤ (-logDeriv (LFunction (χ ^ 2).primitiveCharacter) s2).re + Real.log (q : ℝ) := by
      have habs := (Complex.abs_re_le_norm _).trans hbr
      rw [Complex.sub_re] at habs
      rw [Complex.neg_re, Complex.neg_re]
      linarith [abs_le.mp habs |>.1]
    have hA2full : (-logDeriv (LFunction (χ ^ 2)) s2).re
        ≤ 120 * Real.log (4 * (5 * (4 + |2 * ρ.im|) * Real.sqrt ((χ ^ 2).conductor : ℝ)
            * (1 + Real.log ((χ ^ 2).conductor : ℝ)))) + Real.log (q : ℝ) := by
      linarith [hA2, hdrop]
    -- the growth terms are `O(L)`
    have hB1 : 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
        ≤ 720 * Lval := by
      have := log_four_M0_le (f := q) (q := q) (t := ρ.im) (γ := ρ.im) hq2 le_rfl hq2
        (by linarith [abs_nonneg ρ.im])
      rw [← hLdef] at this; linarith [this]
    have hB2 : 120 * Real.log (4 * (5 * (4 + |2 * ρ.im|) * Real.sqrt ((χ ^ 2).conductor : ℝ)
          * (1 + Real.log ((χ ^ 2).conductor : ℝ)))) ≤ 720 * Lval := by
      have := log_four_M0_le (f := (χ ^ 2).conductor) (q := q) (t := 2 * ρ.im) (γ := ρ.im)
        hf22 hf2q hq2 (by rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num])
      rw [← hLdef] at this; linarith [this]
    have hlogq : Real.log (q : ℝ) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by linarith)
      nlinarith [abs_nonneg ρ.im, hqR2,
        mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
    -- assemble the 3-4-1 chain
    have hrel1 : (4 : ℝ) / (σ - ρ.re) = 4 * (1 / (σ - ρ.re)) := by ring
    have hrel2 : (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
    have hchain : 4 / (σ - ρ.re) ≤ 3 / (σ - 1) + 3604 * Lval := by
      rw [hrel1, hrel2]
      linarith [h341, hA0, hA1, hA2full, hB1, hB2, hlogq, hL1]
    -- the numeric extraction
    have hCdd : (3604 : ℝ) * dd = 1 / 2 := by rw [hdddef]; norm_num
    have hchain' : 4 / (dd / Lval + (1 - ρ.re)) ≤ 3 / (dd / Lval) + 3604 * Lval := by
      have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
      have e2 : σ - 1 = dd / Lval := by rw [hσdef]; ring
      rw [e1, e2] at hchain; exact hchain
    have hfinal := zero_free_extraction hLpos hddpos hCdd hβ1 hchain'
    have heq : (1 / 50456 : ℝ) / Lval = dd / (7 * Lval) := by rw [hdddef]; field_simp; ring
    rw [heq]; linarith [hfinal]

/-! ## 8. The imprimitive extension (via the EulerBridge zero-set transfer) -/

/-- **S3d — the imprimitive corollary.** Dropping primitivity: for every `χ` mod `q` whose
primitive inducing character is non-real (`χ.primitiveCharacter² ≠ 1`), every zero `ρ` of
`L(·,χ)` with `Re ρ ≥ 1/2` obeys `Re ρ ≤ 1 − c₀/log(q(|Im ρ|+2))` (same `c₀ = 1/50456`).
The zero transfers to `L(·, χ.primitiveCharacter)` (`LFunction_eq_zero_iff_primitive`, `Re ρ > 0`),
`zero_free_region_primitive` gives the sharper region at the conductor `f₁ ≤ q`, and
`log(f₁(|γ|+2)) ≤ log(q(|γ|+2))` weakens it to modulus `q`. -/
theorem zero_free_region :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.primitiveCharacter ^ 2 ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := zero_free_region_primitive
  refine ⟨c₀, hc₀pos, ?_⟩
  intro q hNe χ hsq ρ hzero hre
  have hχ1 : χ ≠ 1 := fun h => hsq (by rw [h, primitiveCharacter_one, one_pow])
  have hρre_pos : 0 < ρ.re := by linarith
  have hzero1 : LFunction χ.primitiveCharacter ρ = 0 :=
    (LFunction_eq_zero_iff_primitive χ hρre_pos (Or.inl hχ1)).mp hzero
  have hf1 : χ.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive χ
  have hbound := hc₀ χ.conductor χ.primitiveCharacter hf1 hsq hzero1 hre
  -- conductor facts
  have hf1q : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level χ)
  have hf1_2 : 2 ≤ χ.conductor := by
    have hχ1ne1 : χ.primitiveCharacter ≠ 1 := fun h => hsq (by rw [h, one_pow])
    have hfeq : χ.primitiveCharacter.conductor = χ.conductor := hf1
    have hne1 : χ.primitiveCharacter.conductor ≠ 1 :=
      fun h => hχ1ne1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hfeq] at hne1
    have h0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
    omega
  -- modulus monotonicity of the log denominator
  set Lf : ℝ := Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) with hLfdef
  set Lq : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLqdef
  have hf1_2R : (2 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hf1_2
  have hcondR : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hf1q
  have hLf_pos : 0 < Lf := by
    rw [hLfdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1_2R]
  have hLq_pos : 0 < Lq := by
    rw [hLqdef]; apply Real.log_pos; nlinarith [abs_nonneg ρ.im, hf1_2R, hcondR]
  have hLfq : Lf ≤ Lq := by
    rw [hLfdef, hLqdef]
    apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im, hf1_2R])
    exact mul_le_mul_of_nonneg_right hcondR (by positivity)
  have hmono : c₀ / Lq ≤ c₀ / Lf := by
    rw [div_le_div_iff₀ hLq_pos hLf_pos]
    exact mul_le_mul_of_nonneg_left hLfq hc₀pos.le
  linarith [hbound, hmono]

end Salt.SW
