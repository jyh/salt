/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Defs
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The SW rung, node S3a — the quantitative 3-4-1 positivity inequality

Design: `docs/blueprints/sw.md`, S3 row (the 3-4-1 argument made quantitative).
This module lands the **Λ-series** (logarithmic-derivative) form of the classical
`ζ³L⁴L(χ²)` positivity that powers the zero-free region.

Mathlib's `NumberTheory/LSeries/Nonvanishing.lean` has the *qualitative* 3-4-1 —
but only in the **log** form (`re_log_comb_nonneg'`, a `private` lemma about
`3·Re(-log(1-a)) + 4·Re(-log(1-az)) + Re(-log(1-az²)) ≥ 0`) and packaged as the
product bound `norm_LSeries_product_ge_one` (`‖L³L⁴L‖ ≥ 1`).  Neither is the
`-L'/L` real-part form S3d consumes, so we build the Λ-series version from
scratch, reusing only the general infrastructure (the character unit-norm
computation pattern, the `re_tsum` termwise-real-part step, general cpow lemmas).

## The pointwise heart (`three_four_one_termwise`)

On `Re s > 1`, `(-L'/L)(s, χ) = ∑ₙ Λ(n)·χ(n)·n^{-s}` (S0's re-export of
`LSeries_twist_vonMangoldt_eq`).  For each `n`, writing
`w := χ(n)·n^{-it}` (so `‖w‖ = 1` when `(n,q) = 1`),
```
3·Re(χ₀(n)Λn n^{-σ}) + 4·Re(χ(n)Λn n^{-σ-it}) + Re(χ²(n)Λn n^{-σ-2it})
  = (Λn·n^{-σ})·(3 + 4·Re w + Re w²) = (Λn·n^{-σ})·2·(Re w + 1)² ≥ 0,
```
using `χ₀(n) = 1`, `χ²(n)·n^{-2it} = w²`, and `Re w² = 2(Re w)² − 1` for `‖w‖=1`.
For `(n,q) > 1` all three characters vanish, so the term is `0`.

## Main results

* `three_four_one` — the LSeries/twist carrier (carrier (b)).
* `three_four_one_logDeriv` — the `-L'/L` carrier (carrier (a)); one rewrite off
  the first via S0's `neg_logDeriv_LSeries_eq_LSeries_twist`.

All axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no
new axioms, no `sorry`.
-/

open Complex ArithmeticFunction
open scoped LSeries.notation

noncomputable section
namespace Salt.SW

/-! ## The per-term Dirichlet-coefficient identity -/

/-- **Termwise twist coefficient.**  For `n ≠ 0` and any character `ψ`, the
`LSeries.term` of the twist `↗ψ·↗Λ` at `σ + a·i` factors as the real weight
`Λ(n)/n^σ` times `ψ(n)·n^{-a·i}`.  Pure cpow algebra (`cpow_add`, `cpow_neg`),
valid for every `n ≥ 1`; the character value rides along untouched. -/
private lemma term_char_eq {q : ℕ} (ψ : DirichletCharacter ℂ q) (σ a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (↗ψ * ↗vonMangoldt) ((σ : ℂ) + (a : ℂ) * I) n
      = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ)
          * (ψ (n : ZMod q) * (n : ℂ) ^ (-((a : ℂ) * I))) := by
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : (n : ℂ) ^ (σ : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  have hB : (n : ℂ) ^ ((a : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, Complex.cpow_add _ _ hnc, Complex.cpow_neg,
    Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  field_simp

/-! ## The pointwise 3-4-1 nonnegativity -/

/-- **The pointwise 3-4-1 inequality.**  For every `n`, with `χ₀ = (1)` the trivial
character mod `q`,
`0 ≤ 3·Re(term ↗χ₀↗Λ σ n) + 4·Re(term ↗χ↗Λ (σ+it) n) + Re(term ↗χ²↗Λ (σ+2it) n)`.
Unconditional in `σ` (pure trigonometry `3 + 4cosθ + cos2θ = 2(1+cosθ)²`); the
`Re s > 1` hypothesis is only needed downstream for summability. -/
theorem three_four_one_termwise {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ) n).re
      + 4 * (LSeries.term (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I) n).re
      + (LSeries.term (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero]
  by_cases hu : IsUnit (n : ZMod q)
  · -- Unit case: `χ₀(n) = 1`, `‖χ(n)·n^{-it}‖ = 1`, and the trig identity fires.
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hr0 : (0 : ℝ) ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    set r : ℝ := vonMangoldt n / (n : ℝ) ^ σ with hr
    set w : ℂ := χ (n : ZMod q) * (n : ℂ) ^ (-((t : ℂ) * I)) with hw
    -- `‖w‖ = 1`, hence `w.re² + w.im² = 1`.
    have hwnorm : w.re * w.re + w.im * w.im = 1 := by
      have hn1 : ‖w‖ = 1 := by
        rw [hw, norm_mul, ← hu.unit_spec, DirichletCharacter.unit_norm_eq_one χ hu.unit, one_mul,
          ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos
            (show (0 : ℝ) < (n : ℝ) by exact_mod_cast Nat.pos_of_ne_zero hn0)]
        simp
      have hns := Complex.normSq_eq_norm_sq w
      rw [hn1, Complex.normSq_apply] at hns
      simpa using hns
    -- The three term identities.
    have e0 : LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ) n = (r : ℂ) := by
      rw [LSeries.term_of_ne_zero hn0, Pi.mul_apply, MulChar.one_apply hu, one_mul, hr,
        Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    have e1 : LSeries.term (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I) n = (r : ℂ) * w := by
      rw [term_char_eq χ σ t hn0, hr, hw]
    have e2 : LSeries.term (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I) n
        = (r : ℂ) * w ^ 2 := by
      have h := term_char_eq (χ ^ 2) σ (2 * t) hn0
      rw [show ((2 * t : ℝ) : ℂ) = 2 * (t : ℂ) by push_cast; ring] at h
      rw [h, hr]
      congr 1
      rw [hw, mul_pow, MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0),
        show -(2 * (t : ℂ) * I) = ((2 : ℕ) : ℂ) * (-((t : ℂ) * I)) by push_cast; ring,
        Complex.cpow_nat_mul]
    -- Assemble the trig identity `3 + 4·Re w + Re w² = 2(Re w + 1)²`.
    rw [e0, e1, e2, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hw2 : (w ^ 2).re = w.re * w.re - w.im * w.im := by rw [sq, Complex.mul_re]
    rw [hw2]
    have hwim : w.im * w.im = 1 - w.re * w.re := by linarith [hwnorm]
    rw [hwim]
    nlinarith [hr0, mul_nonneg hr0 (sq_nonneg (w.re + 1))]
  · -- Non-coprime case: all three characters vanish, so every term is `0`.
    simp only [LSeries.term_of_ne_zero hn0, Pi.mul_apply, MulChar.map_nonunit _ hu, zero_mul,
      zero_div, Complex.zero_re, mul_zero, add_zero, le_refl]

/-! ## The summed inequality (carrier (b): the LSeries/twist form) -/

/-- **The quantitative 3-4-1 inequality (LSeries form).**  For `σ > 1` and any `t`,
with `χ₀ = (1 : DirichletCharacter ℂ q)` the trivial character,
```
0 ≤ 3·Re L(↗χ₀·↗Λ, σ) + 4·Re L(↗χ·↗Λ, σ+it) + Re L(↗χ²·↗Λ, σ+2it).
```
Since `L(↗ψ·↗Λ, s) = (−L'/L)(s, ψ)` on `Re s > 1` (S0's re-export), this is the
`ζ³L⁴L(χ²)`-positivity in `−L'/L` real parts.  Route: push `Re` through the three
Dirichlet series (`re_tsum` + twist summability), combine into a single `tsum`,
and apply `three_four_one_termwise` under `tsum_nonneg`. -/
theorem three_four_one {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ)).re
      + 4 * (LSeries (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I)).re
      + (LSeries (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I)).re := by
  have hσ0 : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  have hσ1 : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re := by
    have : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    rw [this]; exact hσ
  have hσ2 : (1 : ℝ) < ((σ : ℂ) + 2 * (t : ℂ) * I).re := by
    have : ((σ : ℂ) + 2 * (t : ℂ) * I).re = σ := by simp
    rw [this]; exact hσ
  -- Absolute convergence of the three twisted L-series (mathlib).
  have S₀ : Summable (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt 1 hσ0
  have S₁ : Summable (LSeries.term (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσ1
  have S₂ : Summable (LSeries.term (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) hσ2
  -- Real parts of the L-series are the tsums of the real parts of the terms.
  have hre₀ : (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) (σ : ℂ) n).re :=
    Complex.re_tsum S₀
  have hre₁ : (LSeries (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I)).re
      = ∑' n, (LSeries.term (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I) n).re :=
    Complex.re_tsum S₁
  have hre₂ : (LSeries (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I)).re
      = ∑' n, (LSeries.term (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I) n).re :=
    Complex.re_tsum S₂
  have hsum₀ := (Complex.hasSum_re S₀.hasSum).summable.mul_left 3
  have hsum₁ := (Complex.hasSum_re S₁.hasSum).summable.mul_left 4
  have hsum₂ := (Complex.hasSum_re S₂.hasSum).summable
  rw [hre₀, hre₁, hre₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun n => three_four_one_termwise χ σ t n

/-! ## The `−L'/L` restatement (carrier (a): what S3d consumes) -/

/-- **The quantitative 3-4-1 inequality (`−L'/L` form).**  The `logDeriv` carrier:
```
0 ≤ 3·Re(−L'/L)(σ, χ₀) + 4·Re(−L'/L)(σ+it, χ) + Re(−L'/L)(σ+2it, χ²).
```
One rewrite off `three_four_one` via S0's `neg_logDeriv_LSeries_eq_LSeries_twist`
(each of the three points has real part `σ > 1`). -/
theorem three_four_one_logDeriv {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    0 ≤ 3 * (-deriv (LSeries ↗(1 : DirichletCharacter ℂ q)) (σ : ℂ)
              / LSeries ↗(1 : DirichletCharacter ℂ q) (σ : ℂ)).re
      + 4 * (-deriv (LSeries ↗χ) ((σ : ℂ) + (t : ℂ) * I)
              / LSeries ↗χ ((σ : ℂ) + (t : ℂ) * I)).re
      + (-deriv (LSeries ↗(χ ^ 2)) ((σ : ℂ) + 2 * (t : ℂ) * I)
              / LSeries ↗(χ ^ 2) ((σ : ℂ) + 2 * (t : ℂ) * I)).re := by
  have hσ0 : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  have hσ1 : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re := by
    have : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    rw [this]; exact hσ
  have hσ2 : (1 : ℝ) < ((σ : ℂ) + 2 * (t : ℂ) * I).re := by
    have : ((σ : ℂ) + 2 * (t : ℂ) * I).re = σ := by simp
    rw [this]; exact hσ
  rw [neg_logDeriv_LSeries_eq_LSeries_twist (1 : DirichletCharacter ℂ q) hσ0,
    neg_logDeriv_LSeries_eq_LSeries_twist χ hσ1,
    neg_logDeriv_LSeries_eq_LSeries_twist (χ ^ 2) hσ2]
  exact three_four_one χ hσ t

end Salt.SW

end
