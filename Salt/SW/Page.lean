/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.ZeroFree
import Salt.SW.ZeroFreeReal

/-!
# The SW rung, node S4c — Page's cross-modulus theorem

Design: `docs/blueprints/sw.md`, S4 wave. This module lands the **cross-modulus** half of
Landau–Page: among two distinct primitive real (quadratic) characters, at most one exceptional
(Siegel) zero can lie in a shared window. Concretely, for primitive real `χ₁ ≠ 1` mod `q₁` and
`χ₂ ≠ 1` mod `q₂` (with `(q₁,χ₁) ≠ (q₂,χ₂)`), the window `[1 − c₂/log(4q₁q₂), 1)` cannot contain a
real zero of both `L(·,χ₁)` and `L(·,χ₂)`.

## Route (the classical 4-fold Page argument)

Work at real `σ ∈ (1, 2]`. Lift `χ₁, χ₂` to characters `χ₁' = changeLevel χ₁`,
`χ₂' = changeLevel χ₂` of the common level `Q = q₁·q₂`, and form `ψ = χ₁'·χ₂'` (mod `Q`).

* **Positivity floor** (`page_positivity`): for real characters `χ₁', χ₂'`,
  `(1 + χ₁'(n))(1 + χ₂'(n)) ≥ 0` pointwise, so
  `0 ≤ Re(−ζ'/ζ) + Re(−L'/L(χ₁')) + Re(−L'/L(χ₂')) + Re(−L'/L(ψ))` at `σ`.
* **Upper bounds**: the ζ term by the S3c pole bound `1/(σ−1) + 1`; the two `χᵢ'` terms keep the
  window zero `βᵢ` (S3e's `neg_reLogDeriv_le_keep` for the primitive `χᵢ` plus the changeLevel
  Euler correction `≤ log Q`); the `ψ` term drops all zeros (`neg_reLogDeriv_le_drop` on its
  primitive inducing character plus the EulerBridge correction `≤ log Q`), which needs `ψ ≠ 1`
  (`product_ne_one`, from distinctness of the two primitive characters).
* **Squeeze** (`page_extraction`): at `σ = 1 + (3c₂)/L`, `L = log(4q₁q₂)`, both `βᵢ ≥ 1 − c₂/L`
  is absurd. The constant is `c₂ = 1/13000`.

## Main results

* `page_positivity` — the 4-fold Λ-series positivity floor.
* `neg_reLogDeriv_changeLevel_le` — the changeLevel Euler correction `Re(−L'/L(χ')) ≤
  Re(−L'/L(χ)) + log Q`.
* `product_ne_one` — the product of two distinct primitive lifts is non-principal.
* `page_cross_modulus` — the S5-facing statement: one exceptional modulus per window.
-/

namespace Salt.SW

open Complex DirichletCharacter Filter Metric ArithmeticFunction
open scoped LSeries.notation Topology

/-! ## 1. The extraction arithmetic -/

/-- **The Page squeeze arithmetic.** With `L ≥ 2`, two positive gaps `x_i = σ − β_i ≤
(4/13000)/L`, and the 4-fold chain `1/x₁ + 1/x₂ ≤ L/(3/13000) + 1 + 2163·L`, we get `False`:
`6500·L` on the left versus `(13000/3 + 2163)·L + 1` on the right, a margin of `(11/3)·L − 1`. -/
private lemma page_extraction {Lq x₁ x₂ : ℝ} (hL : 2 ≤ Lq)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hx₁4 : x₁ ≤ (4 / 13000) / Lq) (hx₂4 : x₂ ≤ (4 / 13000) / Lq)
    (hchain : 1 / x₁ + 1 / x₂ ≤ Lq / (3 / 13000) + 1 + 2163 * Lq) : False := by
  have hLpos : (0 : ℝ) < Lq := by linarith
  have h₁ : 3250 * Lq ≤ 1 / x₁ := by
    rw [le_div_iff₀ hx₁]
    have h4 : x₁ * Lq ≤ 4 / 13000 := (le_div_iff₀ hLpos).mp hx₁4
    nlinarith [h4]
  have h₂ : 3250 * Lq ≤ 1 / x₂ := by
    rw [le_div_iff₀ hx₂]
    have h4 : x₂ * Lq ≤ 4 / 13000 := (le_div_iff₀ hLpos).mp hx₂4
    nlinarith [h4]
  have hval : Lq / (3 / 13000) = (13000 / 3) * Lq := by ring
  rw [hval] at hchain
  linarith [hchain, h₁, h₂]

/-! ## 2. The changeLevel Euler correction on the log-derivative -/

/-- **The changeLevel Euler correction.** For `χ ≠ 1` mod `q` lifted to level `Q` (`q ∣ Q`), on
real `σ > 1`,
`Re(−L'/L(σ, changeLevel χ)) ≤ Re(−L'/L(σ, χ)) + log Q`.
Route: `L(changeLevel χ) = L(χ)·∏_{p∣Q}(1 − χ(p)p^{−s})` (`LFunction_changeLevel`), take
`logDeriv` (`logDeriv_mul`, `logDeriv_prod`), and bound the finite correction by
`Σ_{p∣Q} log p ≤ log Q` (EulerBridge's per-factor bound `norm_logDeriv_eulerFactor_le`). -/
lemma neg_reLogDeriv_changeLevel_le {q Q : ℕ} [NeZero q] [NeZero Q] (hqQ : q ∣ Q)
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) {σ : ℝ} (h1 : 1 < σ) :
    (-logDeriv (LFunction (changeLevel hqQ χ)) (σ : ℂ)).re
      ≤ (-logDeriv (LFunction χ) (σ : ℂ)).re + Real.log (Q : ℝ) := by
  set s : ℂ := (σ : ℂ) with hs
  have hsre : s.re = σ := by rw [hs, Complex.ofReal_re]
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hspos : (0 : ℝ) < s.re := by linarith
  have hLχ0 : LFunction χ s ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hσC.le
  have hfac_ne : ∀ p ∈ Q.primeFactors, eulerFactor χ p s ≠ 0 :=
    fun p hp => eulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) hspos
  have hfac_diff : ∀ p ∈ Q.primeFactors, DifferentiableAt ℂ (eulerFactor χ p) s :=
    fun p hp => differentiableAt_eulerFactor χ (Nat.prime_of_mem_primeFactors hp) s
  set P : ℂ → ℂ := fun z => ∏ p ∈ Q.primeFactors, eulerFactor χ p z with hPdef
  have hP0 : P s ≠ 0 := Finset.prod_ne_zero_iff.mpr hfac_ne
  have hPdiff : DifferentiableAt ℂ P s := DifferentiableAt.fun_finsetProd hfac_diff
  have hLχdiff : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inr hχ1)
  -- multiplicative split
  have hLmul : logDeriv (LFunction (changeLevel hqQ χ)) s
      = logDeriv (LFunction χ) s + logDeriv P s := by
    have hEq : LFunction (changeLevel hqQ χ) =ᶠ[𝓝 s] fun z => LFunction χ z * P z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      rw [hPdef]
      exact LFunction_changeLevel hqQ χ (Or.inr (by simpa using hz))
    have hcong : logDeriv (LFunction (changeLevel hqQ χ)) s
        = logDeriv (fun z => LFunction χ z * P z) s := by
      simp only [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_mul s hLχ0 hP0 hLχdiff hPdiff]
  -- correction bound `‖logDeriv P‖ ≤ log Q`
  have hPsum : logDeriv P s = ∑ p ∈ Q.primeFactors, logDeriv (eulerFactor χ p) s := by
    rw [hPdef]; exact logDeriv_prod hfac_ne hfac_diff
  have hPbound : ‖logDeriv P s‖ ≤ Real.log (Q : ℝ) := by
    rw [hPsum]
    calc ‖∑ p ∈ Q.primeFactors, logDeriv (eulerFactor χ p) s‖
        ≤ ∑ p ∈ Q.primeFactors, ‖logDeriv (eulerFactor χ p) s‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Q.primeFactors, Real.log p :=
          Finset.sum_le_sum (fun p hp =>
            norm_logDeriv_eulerFactor_le χ (Nat.prime_of_mem_primeFactors hp) hσC.le)
      _ = Real.log (∏ p ∈ Q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
      _ ≤ Real.log (Q : ℝ) := by
          apply Real.log_le_log
          · apply Finset.prod_pos
            exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne Q))
              (Nat.prod_primeFactors_dvd Q)
  have hPre : (-logDeriv P s).re ≤ Real.log (Q : ℝ) := by
    have h := (Complex.abs_re_le_norm (logDeriv P s)).trans hPbound
    rw [Complex.neg_re]; linarith [(abs_le.mp h).1]
  have hsplit : (-logDeriv (LFunction (changeLevel hqQ χ)) s).re
      = (-logDeriv (LFunction χ) s).re + (-logDeriv P s).re := by
    rw [hLmul, neg_add, Complex.add_re]
  rw [hsplit]; linarith [hPre]

/-! ## 3. Distinctness ⇒ the product character is non-principal -/

/-- **The product of two distinct primitive lifts is non-principal.** If `χ₁` (mod `q₁`), `χ₂`
(mod `q₂`) are primitive with `χ₂² = 1`, lifted to level `Q`, and the pair `(q₁,χ₁)` differs from
`(q₂,χ₂)`, then `changeLevel χ₁ · changeLevel χ₂ ≠ 1`. (Equal ⇒ `χ₁' = χ₂'` ⇒ equal conductors
`q₁ = q₂` (`conductor_changeLevel`) and, by `changeLevel_injective`, `χ₁ = χ₂`.) -/
lemma product_ne_one {q₁ q₂ Q : ℕ} [NeZero Q] (h₁ : q₁ ∣ Q) (h₂ : q₂ ∣ Q)
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (hsq₂ : χ₂ ^ 2 = 1)
    (hdist : ∀ (h : q₁ = q₂), (h ▸ χ₁) ≠ χ₂) :
    changeLevel h₁ χ₁ * changeLevel h₂ χ₂ ≠ 1 := by
  intro hψ
  have hsq2' : (changeLevel h₂ χ₂) ^ 2 = 1 := by rw [← map_pow, hsq₂, changeLevel_one]
  have haa : changeLevel h₂ χ₂ * changeLevel h₂ χ₂ = 1 := by rw [← sq]; exact hsq2'
  have hself : changeLevel h₂ χ₂ = (changeLevel h₂ χ₂)⁻¹ := mul_eq_one_iff_eq_inv.mp haa
  have hcong : changeLevel h₁ χ₁ = changeLevel h₂ χ₂ :=
    (mul_eq_one_iff_eq_inv.mp hψ).trans hself.symm
  have hq : q₁ = q₂ := by
    have e1 : (changeLevel h₁ χ₁).conductor = χ₁.conductor := conductor_changeLevel χ₁ h₁
    have e2 : (changeLevel h₂ χ₂).conductor = χ₂.conductor := conductor_changeLevel χ₂ h₂
    have hcond₁ : χ₁.conductor = q₁ := hp₁
    have hcond₂ : χ₂.conductor = q₂ := hp₂
    rw [hcong, e2, hcond₂] at e1
    rw [hcond₁] at e1
    exact e1.symm
  subst hq
  have hh : h₂ = h₁ := Subsingleton.elim h₂ h₁
  rw [hh] at hcong
  exact hdist rfl (changeLevel_injective h₁ hcong)

/-! ## 4. The 4-fold positivity floor -/

/-- At real `σ`, the `↗Λ` L-series term is the real number `Λ(n)·n^{−σ}` (cast to `ℂ`). -/
private lemma term_vonMangoldt_eq' (σ : ℝ) (n : ℕ) :
    LSeries.term ↗vonMangoldt (σ : ℂ) n = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

/-- At real `σ`, the twisted term is the real weight `Λ(n)/n^σ` times the character value. -/
private lemma term_char_real_eq {Q : ℕ} (ψ : DirichletCharacter ℂ Q) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (↗ψ * ↗vonMangoldt) (σ : ℂ) n
      = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) * ψ (n : ZMod Q) := by
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, Complex.ofReal_div,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  ring

/-- **The pointwise 4-fold inequality.** For two real characters `χ₁, χ₂` mod `Q`
(`χ₁² = χ₂² = 1`), every term satisfies
`0 ≤ Re(term ↗Λ) + Re(term ↗χ₁↗Λ) + Re(term ↗χ₂↗Λ) + Re(term ↗(χ₁χ₂)↗Λ)`.
Route: on the units `(1 + χ₁(n))(1 + χ₂(n)) ≥ 0` (real values `±1`), off the units the three
character terms vanish and the `ζ` term `Λ(n)/n^σ` is nonnegative. -/
theorem page_termwise {Q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ Q)
    (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term ↗vonMangoldt (σ : ℂ) n).re
      + (LSeries.term (↗χ₁ * ↗vonMangoldt) (σ : ℂ) n).re
      + (LSeries.term (↗χ₂ * ↗vonMangoldt) (σ : ℂ) n).re
      + (LSeries.term (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero]
  · have hr0 : (0 : ℝ) ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    set r : ℝ := vonMangoldt n / (n : ℝ) ^ σ with hr
    have e0 : (LSeries.term ↗vonMangoldt (σ : ℂ) n).re = r := by
      rw [term_vonMangoldt_eq' σ n, Complex.ofReal_re]
    by_cases hu : IsUnit (n : ZMod Q)
    · set a : ℂ := χ₁ (n : ZMod Q) with ha
      set b : ℂ := χ₂ (n : ZMod Q) with hb
      have haim : a.im = 0 := by
        have h := conj_apply_eq_of_sq_eq_one hsq1 (n : ZMod Q)
        rw [← ha] at h
        exact Complex.conj_eq_iff_im.mp h
      have hbim : b.im = 0 := by
        have h := conj_apply_eq_of_sq_eq_one hsq2 (n : ZMod Q)
        rw [← hb] at h
        exact Complex.conj_eq_iff_im.mp h
      have haa : a * a = 1 := by
        have h1 : (χ₁ ^ 2) (n : ZMod Q) = 1 := by rw [hsq1, MulChar.one_apply hu]
        rw [MulChar.pow_apply' χ₁ (by norm_num : (2 : ℕ) ≠ 0) (n : ZMod Q)] at h1
        rw [ha, ← pow_two]; exact h1
      have hbb : b * b = 1 := by
        have h1 : (χ₂ ^ 2) (n : ZMod Q) = 1 := by rw [hsq2, MulChar.one_apply hu]
        rw [MulChar.pow_apply' χ₂ (by norm_num : (2 : ℕ) ≠ 0) (n : ZMod Q)] at h1
        rw [hb, ← pow_two]; exact h1
      have hare : a.re * a.re = 1 := by
        have h := congrArg Complex.re haa
        rwa [Complex.mul_re, haim, mul_zero, sub_zero, Complex.one_re] at h
      have hbre : b.re * b.re = 1 := by
        have h := congrArg Complex.re hbb
        rwa [Complex.mul_re, hbim, mul_zero, sub_zero, Complex.one_re] at h
      have e1 : (LSeries.term (↗χ₁ * ↗vonMangoldt) (σ : ℂ) n).re = r * a.re := by
        rw [term_char_real_eq χ₁ σ hn0, ← ha, ← hr, Complex.re_ofReal_mul]
      have e2 : (LSeries.term (↗χ₂ * ↗vonMangoldt) (σ : ℂ) n).re = r * b.re := by
        rw [term_char_real_eq χ₂ σ hn0, ← hb, ← hr, Complex.re_ofReal_mul]
      have hab : (χ₁ * χ₂) (n : ZMod Q) = a * b := by rw [MulChar.mul_apply, ha, hb]
      have e3 : (LSeries.term (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ) n).re
          = r * (a.re * b.re) := by
        rw [term_char_real_eq (χ₁ * χ₂) σ hn0, hab, ← hr, Complex.re_ofReal_mul, Complex.mul_re,
          haim, zero_mul, sub_zero]
      rw [e0, e1, e2, e3]
      have h1a : (0 : ℝ) ≤ 1 + a.re := by nlinarith [sq_nonneg (a.re + 1), hare]
      have h1b : (0 : ℝ) ≤ 1 + b.re := by nlinarith [sq_nonneg (b.re + 1), hbre]
      nlinarith [mul_nonneg (mul_nonneg hr0 h1a) h1b]
    · have hz1 : (LSeries.term (↗χ₁ * ↗vonMangoldt) (σ : ℂ) n).re = 0 := by
        rw [term_char_real_eq χ₁ σ hn0, MulChar.map_nonunit χ₁ hu, mul_zero, Complex.zero_re]
      have hz2 : (LSeries.term (↗χ₂ * ↗vonMangoldt) (σ : ℂ) n).re = 0 := by
        rw [term_char_real_eq χ₂ σ hn0, MulChar.map_nonunit χ₂ hu, mul_zero, Complex.zero_re]
      have hz3 : (LSeries.term (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ) n).re = 0 := by
        rw [term_char_real_eq (χ₁ * χ₂) σ hn0, MulChar.map_nonunit (χ₁ * χ₂) hu, mul_zero,
          Complex.zero_re]
      rw [e0, hz1, hz2, hz3]; linarith [hr0]

/-- **The 4-fold Λ-series positivity floor.** For real characters `χ₁, χ₂` mod `Q` and `σ > 1`,
`0 ≤ Re L(↗Λ,σ) + Re L(↗χ₁↗Λ,σ) + Re L(↗χ₂↗Λ,σ) + Re L(↗(χ₁χ₂)↗Λ,σ)`. The four terms are
`−ζ'/ζ`, `−L'/L(χ₁)`, `−L'/L(χ₂)`, `−L'/L(χ₁χ₂)` at `σ`. -/
theorem page_positivity {Q : ℕ} [NeZero Q] (χ₁ χ₂ : DirichletCharacter ℂ Q)
    (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries ↗vonMangoldt (σ : ℂ)).re
      + (LSeries (↗χ₁ * ↗vonMangoldt) (σ : ℂ)).re
      + (LSeries (↗χ₂ * ↗vonMangoldt) (σ : ℂ)).re
      + (LSeries (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ)).re := by
  have hσ0 : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  have SΛ : Summable (LSeries.term ↗vonMangoldt (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσ0
  have S₁ : Summable (LSeries.term (↗χ₁ * ↗vonMangoldt) (σ : ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₁ hσ0
  have S₂ : Summable (LSeries.term (↗χ₂ * ↗vonMangoldt) (σ : ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₂ hσ0
  have Sψ : Summable (LSeries.term (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ₁ * χ₂) hσ0
  have hreΛ : (LSeries ↗vonMangoldt (σ : ℂ)).re
      = ∑' n, (LSeries.term ↗vonMangoldt (σ : ℂ) n).re := Complex.re_tsum SΛ
  have hre₁ : (LSeries (↗χ₁ * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗χ₁ * ↗vonMangoldt) (σ : ℂ) n).re := Complex.re_tsum S₁
  have hre₂ : (LSeries (↗χ₂ * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗χ₂ * ↗vonMangoldt) (σ : ℂ) n).re := Complex.re_tsum S₂
  have hreψ : (LSeries (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗(χ₁ * χ₂) * ↗vonMangoldt) (σ : ℂ) n).re := Complex.re_tsum Sψ
  have hsΛ := (Complex.hasSum_re SΛ.hasSum).summable
  have hs₁ := (Complex.hasSum_re S₁.hasSum).summable
  have hs₂ := (Complex.hasSum_re S₂.hasSum).summable
  have hsψ := (Complex.hasSum_re Sψ.hasSum).summable
  rw [hreΛ, hre₁, hre₂, hreψ, ← hsΛ.tsum_add hs₁, ← (hsΛ.add hs₁).tsum_add hs₂,
    ← ((hsΛ.add hs₁).add hs₂).tsum_add hsψ]
  exact tsum_nonneg (fun n => page_termwise χ₁ χ₂ hsq1 hsq2 σ n)

/-! ## 5. The S5-facing cross-modulus theorem -/

set_option maxHeartbeats 1000000 in
-- The 4-fold squeeze rewrites heavy `LFunction`/`logDeriv` terms at four characters and runs the
-- distinctness algebra in one declaration; it needs more than the default heartbeat budget.
/-- **S4c — Page's cross-modulus theorem.** There is an explicit `c₂ > 0` (`c₂ = 1/13000`) such
that for two distinct primitive real (quadratic) Dirichlet characters `χ₁ ≠ 1` mod `q₁`,
`χ₂ ≠ 1` mod `q₂` (distinctness packaged as `∀ (h : q₁ = q₂), h ▸ χ₁ ≠ χ₂`), the window
`1 − c₂/log(4q₁q₂) ≤ β` cannot contain a real zero of **both** `L(·,χ₁)` and `L(·,χ₂)`: if `β₁`
is one for `χ₁`, then `β₂` is not one for `χ₂`. Equivalently `min(β₁,β₂) < 1 − c₂/log(4q₁q₂)` —
at most one exceptional modulus per range. -/
theorem page_cross_modulus : ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
    χ₁.IsPrimitive → χ₂.IsPrimitive → χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
    (∀ (h : q₁ = q₂), (h ▸ χ₁) ≠ χ₂) →
    ∀ {β₁ β₂ : ℝ}, LFunction χ₁ β₁ = 0 → LFunction χ₂ β₂ = 0 →
      1 - c₂ / Real.log (4 * q₁ * q₂) ≤ β₁ → ¬ (1 - c₂ / Real.log (4 * q₁ * q₂) ≤ β₂) := by
  refine ⟨1 / 13000, by norm_num, ?_⟩
  intro q₁ q₂ _ _ χ₁ χ₂ hp₁ hp₂ hsq₁ hsq₂ hχ₁1 hχ₂1 hdist β₁ β₂ hz₁ hz₂ hw₁ hw₂
  -- `q₁, q₂ ≥ 2`
  have hq₁2 : 2 ≤ q₁ := by
    have hc1 : χ₁.conductor ≠ 1 := fun h => hχ₁1 (eq_one_iff_conductor_eq_one.mpr h)
    have hcond : χ₁.conductor = q₁ := hp₁
    rw [hcond] at hc1
    have := NeZero.ne q₁; omega
  have hq₂2 : 2 ≤ q₂ := by
    have hc1 : χ₂.conductor ≠ 1 := fun h => hχ₂1 (eq_one_iff_conductor_eq_one.mpr h)
    have hcond : χ₂.conductor = q₂ := hp₂
    rw [hcond] at hc1
    have := NeZero.ne q₂; omega
  have hq₁R : (2 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁2
  have hq₂R : (2 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂2
  -- the common level `Q = q₁·q₂`
  set Q : ℕ := q₁ * q₂ with hQdef
  haveI : NeZero Q := ⟨by rw [hQdef]; exact Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  have h₁dvd : q₁ ∣ Q := ⟨q₂, hQdef⟩
  have h₂dvd : q₂ ∣ Q := ⟨q₁, by rw [hQdef]; ring⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQ2 : 2 ≤ Q := by
    have h4 : 4 ≤ Q := by rw [hQdef]; exact Nat.mul_le_mul hq₁2 hq₂2
    omega
  set χ₁' : DirichletCharacter ℂ Q := changeLevel h₁dvd χ₁ with hχ₁'def
  set χ₂' : DirichletCharacter ℂ Q := changeLevel h₂dvd χ₂ with hχ₂'def
  have hsq1' : χ₁' ^ 2 = 1 := by rw [hχ₁'def, ← map_pow, hsq₁, changeLevel_one]
  have hsq2' : χ₂' ^ 2 = 1 := by rw [hχ₂'def, ← map_pow, hsq₂, changeLevel_one]
  -- `L = log(4 q₁ q₂) ≥ 2`
  set Lq : ℝ := Real.log (4 * (q₁ : ℝ) * (q₂ : ℝ)) with hLdef
  have hL2 : (2 : ℝ) ≤ Lq := by
    have hexp2 : Real.exp 2 ≤ 8 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have h16 : (16 : ℝ) ≤ 4 * (q₁ : ℝ) * (q₂ : ℝ) := by nlinarith [hq₁R, hq₂R]
    rw [hLdef]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (4 * (q₁ : ℝ) * (q₂ : ℝ)) :=
          Real.log_le_log (Real.exp_pos 2) (by linarith [hexp2, h16])
  have hLpos : (0 : ℝ) < Lq := by linarith [hL2]
  -- window facts
  have hwin : (1 / 13000 : ℝ) / Lq ≤ 1 / 26000 := by rw [div_le_iff₀ hLpos]; nlinarith [hL2]
  have hβ₁1 : β₁ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ₁ (Or.inl hχ₁1)
      (by rw [Complex.ofReal_re]; linarith) hz₁
  have hβ₂1 : β₂ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ₂ (Or.inl hχ₂1)
      (by rw [Complex.ofReal_re]; linarith) hz₂
  have hβ₁half : (1 / 2 : ℝ) < β₁ := by linarith [hw₁, hwin]
  have hβ₂half : (1 / 2 : ℝ) < β₂ := by linarith [hw₂, hwin]
  -- the evaluation point `σ = 1 + (3/13000)/L`
  set σ : ℝ := 1 + (3 / 13000) / Lq with hσdef
  have hσgap : (0 : ℝ) < (3 / 13000) / Lq := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith [hσgap]
  have hσ2 : σ < 2 := by
    have h3 : (3 / 13000 : ℝ) / Lq ≤ 3 / 26000 := by rw [div_le_iff₀ hLpos]; nlinarith [hL2]
    rw [hσdef]; linarith [h3]
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ1
  -- LSeries ↔ `−logDeriv` bridges for the three lifted characters
  have heq1 : LSeries (↗χ₁' * ↗vonMangoldt) (σ : ℂ) = -logDeriv (LFunction χ₁') (σ : ℂ) :=
    (neg_logDeriv_LSeries_eq_LSeries_twist χ₁' hσC).symm.trans (neg_logDeriv_LSeries_eq χ₁' hσC)
  have heq2 : LSeries (↗χ₂' * ↗vonMangoldt) (σ : ℂ) = -logDeriv (LFunction χ₂') (σ : ℂ) :=
    (neg_logDeriv_LSeries_eq_LSeries_twist χ₂' hσC).symm.trans (neg_logDeriv_LSeries_eq χ₂' hσC)
  have heqψ : LSeries (↗(χ₁' * χ₂') * ↗vonMangoldt) (σ : ℂ)
      = -logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ) :=
    (neg_logDeriv_LSeries_eq_LSeries_twist (χ₁' * χ₂') hσC).symm.trans
      (neg_logDeriv_LSeries_eq (χ₁' * χ₂') hσC)
  -- the positivity floor
  have hpos := page_positivity χ₁' χ₂' hsq1' hsq2' hσ1
  rw [heq1, heq2, heqψ] at hpos
  -- ζ upper bound
  have hζ : (LSeries ↗vonMangoldt (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσC]
    exact neg_logDeriv_zeta_le hσ1 hσ2.le
  -- `log Q ≤ L`
  have hlogQ : Real.log (Q : ℝ) ≤ Lq := by
    rw [hLdef]
    apply Real.log_le_log hQpos
    rw [hQdef]; push_cast
    nlinarith [hq₁R, hq₂R, mul_nonneg (show (0 : ℝ) ≤ (q₁ : ℝ) by linarith)
      (show (0 : ℝ) ≤ (q₂ : ℝ) by linarith)]
  -- the χ₁ keep-one bound (real zero β₁) + changeLevel correction + growth
  have hkeep1 := neg_reLogDeriv_le_keep χ₁ hp₁ hq₁2 hz₁
    (by rw [Complex.ofReal_re]; exact hβ₁half) (by rw [Complex.ofReal_re]; exact hβ₁1) hσ1 hσ2
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_zero, zero_mul,
    add_zero] at hkeep1
  have hcl1 : (-logDeriv (LFunction χ₁') (σ : ℂ)).re
      ≤ (-logDeriv (LFunction χ₁) (σ : ℂ)).re + Real.log (Q : ℝ) := by
    rw [hχ₁'def]; exact neg_reLogDeriv_changeLevel_le h₁dvd hχ₁1 hσ1
  have hM1 : 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q₁ : ℝ)
      * (1 + Real.log (q₁ : ℝ)))) ≤ 720 * Lq := by
    have h6 := log_four_M0_le (f := q₁) (q := q₁) (t := 0) (γ := 0) hq₁2 le_rfl hq₁2 (by simp)
    have hmono : Real.log ((q₁ : ℝ) * (|(0 : ℝ)| + 2)) ≤ Lq := by
      rw [hLdef, abs_zero]
      apply Real.log_le_log (by nlinarith [hq₁R])
      nlinarith [hq₁R, hq₂R, mul_nonneg (show (0 : ℝ) ≤ (q₁ : ℝ) by linarith)
        (show (0 : ℝ) ≤ 2 * (q₂ : ℝ) - 1 by linarith)]
    linarith [h6, hmono]
  -- the χ₂ keep-one bound
  have hkeep2 := neg_reLogDeriv_le_keep χ₂ hp₂ hq₂2 hz₂
    (by rw [Complex.ofReal_re]; exact hβ₂half) (by rw [Complex.ofReal_re]; exact hβ₂1) hσ1 hσ2
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_zero, zero_mul,
    add_zero] at hkeep2
  have hcl2 : (-logDeriv (LFunction χ₂') (σ : ℂ)).re
      ≤ (-logDeriv (LFunction χ₂) (σ : ℂ)).re + Real.log (Q : ℝ) := by
    rw [hχ₂'def]; exact neg_reLogDeriv_changeLevel_le h₂dvd hχ₂1 hσ1
  have hM2 : 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q₂ : ℝ)
      * (1 + Real.log (q₂ : ℝ)))) ≤ 720 * Lq := by
    have h6 := log_four_M0_le (f := q₂) (q := q₂) (t := 0) (γ := 0) hq₂2 le_rfl hq₂2 (by simp)
    have hmono : Real.log ((q₂ : ℝ) * (|(0 : ℝ)| + 2)) ≤ Lq := by
      rw [hLdef, abs_zero]
      apply Real.log_le_log (by nlinarith [hq₂R])
      nlinarith [hq₁R, hq₂R, mul_nonneg (show (0 : ℝ) ≤ (q₂ : ℝ) by linarith)
        (show (0 : ℝ) ≤ 2 * (q₁ : ℝ) - 1 by linarith)]
    linarith [h6, hmono]
  -- the ψ drop-all-zeros bound (needs ψ ≠ 1) + EulerBridge correction + growth
  have hψ1 : χ₁' * χ₂' ≠ 1 := by
    rw [hχ₁'def, hχ₂'def]; exact product_ne_one h₁dvd h₂dvd hp₁ hp₂ hsq₂ hdist
  have hfψ2 : 2 ≤ (χ₁' * χ₂').conductor := by
    have hc1 : (χ₁' * χ₂').conductor ≠ 1 := fun h => hψ1 (eq_one_iff_conductor_eq_one.mpr h)
    have := (χ₁' * χ₂').conductor_ne_zero
    omega
  have hψp1 : (χ₁' * χ₂').primitiveCharacter ≠ 1 := fun h => hψ1 (by
    rw [← changeLevel_primitiveCharacter (χ₁' * χ₂'), h, changeLevel_one])
  have hLψp0 : LFunction (χ₁' * χ₂').primitiveCharacter (σ : ℂ) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re (χ₁' * χ₂').primitiveCharacter (Or.inl hψp1) hσC.le
  have hsc0 : ‖(σ : ℂ) - (2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 23 / 20 := by
    have hsub : (σ : ℂ) - (2 + ((0 : ℝ) : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hdrop := neg_reLogDeriv_le_drop (χ₁' * χ₂').primitiveCharacter
    (primitiveCharacter_isPrimitive (χ₁' * χ₂')) hfψ2 0 hsc0 hσC
  have hbridgeψ := norm_logDeriv_LFunction_sub_primitive_le (χ₁' * χ₂') hσC.le hLψp0 (Or.inl hψ1)
  have hCψ : (-logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ)).re
      ≤ 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt ((χ₁' * χ₂').conductor : ℝ)
          * (1 + Real.log ((χ₁' * χ₂').conductor : ℝ)))) + Real.log (Q : ℝ) := by
    have hdle : -(logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ)
        - logDeriv (LFunction (χ₁' * χ₂').primitiveCharacter) (σ : ℂ)).re ≤ Real.log (Q : ℝ) := by
      have h := (Complex.abs_re_le_norm _).trans hbridgeψ
      linarith [(abs_le.mp h).1]
    have heqd : -(logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ))
        = -(logDeriv (LFunction (χ₁' * χ₂').primitiveCharacter) (σ : ℂ))
          - (logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ)
            - logDeriv (LFunction (χ₁' * χ₂').primitiveCharacter) (σ : ℂ)) := by ring
    rw [heqd, Complex.sub_re]
    linarith [hdrop, hdle]
  have hMψ : 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt ((χ₁' * χ₂').conductor : ℝ)
      * (1 + Real.log ((χ₁' * χ₂').conductor : ℝ)))) ≤ 720 * Lq := by
    have hfψQ : (χ₁' * χ₂').conductor ≤ Q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne Q)) (conductor_dvd_level _)
    have h6 := log_four_M0_le (f := (χ₁' * χ₂').conductor) (q := Q) (t := 0) (γ := 0)
      hfψ2 hfψQ hQ2 (by simp)
    have hmono : Real.log ((Q : ℝ) * (|(0 : ℝ)| + 2)) ≤ Lq := by
      rw [hLdef, abs_zero]
      apply Real.log_le_log (by positivity)
      rw [hQdef]; push_cast
      nlinarith [hq₁R, hq₂R, mul_nonneg (show (0 : ℝ) ≤ (q₁ : ℝ) by linarith)
        (show (0 : ℝ) ≤ (q₂ : ℝ) by linarith)]
    linarith [h6, hmono]
  -- abstract the heavy log-derivative atoms so the final `linarith` stays cheap
  set T0 : ℝ := (LSeries ↗vonMangoldt (σ : ℂ)).re
  set T1 : ℝ := (-logDeriv (LFunction χ₁') (σ : ℂ)).re
  set T2 : ℝ := (-logDeriv (LFunction χ₂') (σ : ℂ)).re
  set U1 : ℝ := (-logDeriv (LFunction χ₁) (σ : ℂ)).re
  set U2 : ℝ := (-logDeriv (LFunction χ₂) (σ : ℂ)).re
  set Tψ : ℝ := (-logDeriv (LFunction (χ₁' * χ₂')) (σ : ℂ)).re
  set M1 : ℝ := 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q₁ : ℝ)
    * (1 + Real.log (q₁ : ℝ))))
  set M2 : ℝ := 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt (q₂ : ℝ)
    * (1 + Real.log (q₂ : ℝ))))
  set Mψ : ℝ := 120 * Real.log (4 * (5 * (4 + |(0 : ℝ)|) * Real.sqrt ((χ₁' * χ₂').conductor : ℝ)
    * (1 + Real.log ((χ₁' * χ₂').conductor : ℝ))))
  set LQ : ℝ := Real.log (Q : ℝ)
  clear_value T0 T1 T2 U1 U2 Tψ M1 M2 Mψ LQ
  -- the squeeze
  have hx₁pos : (0 : ℝ) < σ - β₁ := by rw [hσdef]; linarith [hβ₁1, hσgap]
  have hx₂pos : (0 : ℝ) < σ - β₂ := by rw [hσdef]; linarith [hβ₂1, hσgap]
  have hgapsum : (3 / 13000 : ℝ) / Lq + (1 / 13000) / Lq = (4 / 13000) / Lq := by
    rw [← add_div]; norm_num
  have hx₁4 : σ - β₁ ≤ (4 / 13000) / Lq := by rw [hσdef]; linarith [hw₁, hgapsum]
  have hx₂4 : σ - β₂ ≤ (4 / 13000) / Lq := by rw [hσdef]; linarith [hw₂, hgapsum]
  have hσ1val : (1 : ℝ) / (σ - 1) = Lq / (3 / 13000) := by
    rw [show σ - 1 = (3 / 13000) / Lq by rw [hσdef]; ring, one_div_div]
  apply page_extraction hL2 hx₁pos hx₂pos hx₁4 hx₂4
  rw [← hσ1val]
  linarith [hpos, hζ, hcl1, hkeep1, hM1, hlogQ, hcl2, hkeep2, hM2, hCψ, hMψ]

end Salt.SW
