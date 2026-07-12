/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MaxModulus
import Salt.SW.ZeroFree
import Salt.SW.ZetaPole

/-!
# The SW rung, node S3e — Landau's one-exceptional-zero theorem (per modulus)

Design: `docs/blueprints/sw.md`, S3 row. This module lands the **per-modulus** half of
Landau–Page: for a primitive real (quadratic) character `χ ≠ 1` mod `q`, the window
`[1 − c₁/log(4q), 1)` contains **at most one** real zero of `L(·,χ)`, and that zero is
**simple**. The cross-modulus Page half (one exceptional *modulus* per range) is NOT here —
it belongs to the S4 wave.

## Route (Landau's classical two-term argument — no 3-4-1)

Work at real `s = σ ∈ (1, 2)`, center `c = 2` (the S2 endpoint at `t₀ = 0`).

* **Lower** (partial fractions): `LFunction_norm_logDeriv_sub_sum'` + `neg_re_logDeriv_le` give
  `Re(−L'/L(σ)) ≤ 120·log(4M₀) − Σ_{ρ∈Z} m_ρ·Re(1/(σ−ρ))`, and every kept term is `≥ 0`
  (zeros have `Re ρ < 1 < σ`). Two distinct real window zeros `β₁ ≠ β₂` — or one with
  multiplicity `m ≥ 2` — contribute `1/(σ−β₁) + 1/(σ−β₂)` to the sum.
* **Upper** (termwise ζ-majorant): `Re(−L'/L(σ)) = Re Σ Λ(n)χ(n)n^{−σ} ≥ −Σ Λ(n)n^{−σ}
  = Re(ζ'/ζ(σ)) ≥ −(1/(σ−1) + 1)` — `‖χ(n)‖ ≤ 1` termwise plus the S3c pole bound
  `neg_logDeriv_zeta_le`.
* **Squeeze**: `1/(σ−β₁) + 1/(σ−β₂) ≤ 1/(σ−1) + 1 + 120·log(4M₀)`. With `L = log(4q) ≥ 2`
  (`q ≥ 2`), `log(4M₀(q,0)) ≤ 6·log(2q) ≤ 6L` (`log_four_M0_le` at `t = γ = 0`), and
  `σ := 1 + (3/5000)/L`, `β_i ≥ 1 − (1/5000)/L`: the left side is `≥ 2·(5000/4)L = 2500L`
  while the right is `≤ (5000/3)L + 1 + 720L`, and `2500 − 5000/3 − 720 = 340/3 > 1/2 ≥ 1/L`.
  Contradiction. The constant is `c₁ = 1/5000`.

## Main results

* `landau_neg_logDeriv_re_lower` — the termwise ζ-majorant at real `σ`:
  `−(1/(σ−1)+1) ≤ Re(−L'/L(σ,χ))`, any `χ`, `1 < σ ≤ 2`.
* `analyticOrderAt_eq_of_factorization` — an S2-endpoint-shaped factorization identifies its
  multiplicity `m ρ` with the canonical `analyticOrderAt` (the composable order bridge).
* `landau_one_exceptional_at` — the workhorse at the explicit constant `c₁ = 1/5000`:
  two window zeros coincide AND the common zero is simple (`analyticOrderAt = 1`).
* `landau_one_exceptional` — the S4/S5-facing distinctness statement (∃-form).
* `landau_one_exceptional_simple` — the simplicity statement (∃-form), the S5 residue
  extraction's input.
-/

namespace Salt.SW

open Complex Metric DirichletCharacter ArithmeticFunction Filter Set
open scoped LSeries.notation Topology

/-! ## 1. The extraction arithmetic -/

/-- **The Landau squeeze arithmetic.** If `x₁, x₂` are two positive gaps `σ − β_i ≤ (4/5000)/L`
and the partial-fraction squeeze `1/x₁ + 1/x₂ ≤ L/(3/5000) + 1 + 720·L` holds, then `L < 2`.
Contrapositive form: with `L = log(4q) ≥ 2` this is absurd. (`2500·L` on the left vs
`(5000/3 + 720)·L + 1` on the right; the margin is `(340/3)·L − 1 ≥ 680/3 − 1 > 0`.) -/
private lemma landau_extraction {Lq x₁ x₂ : ℝ} (hL : 2 ≤ Lq)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hx₁4 : x₁ ≤ (4 / 5000) / Lq) (hx₂4 : x₂ ≤ (4 / 5000) / Lq)
    (hchain : 1 / x₁ + 1 / x₂ ≤ Lq / (3 / 5000) + 1 + 720 * Lq) : False := by
  have hLpos : (0 : ℝ) < Lq := by linarith
  have h₁ : 1250 * Lq ≤ 1 / x₁ := by
    rw [le_div_iff₀ hx₁]
    have h4 : x₁ * Lq ≤ 4 / 5000 := (le_div_iff₀ hLpos).mp hx₁4
    nlinarith [h4]
  have h₂ : 1250 * Lq ≤ 1 / x₂ := by
    rw [le_div_iff₀ hx₂]
    have h4 : x₂ * Lq ≤ 4 / 5000 := (le_div_iff₀ hLpos).mp hx₂4
    nlinarith [h4]
  have hval : Lq / (3 / 5000) = (5000 / 3) * Lq := by ring
  rw [hval] at hchain
  -- `2500·L ≤ (5000/3)·L + 1 + 720·L` forces `(340/3)·L ≤ 1`, contradicting `L ≥ 2`.
  linarith [hchain, h₁, h₂]

/-! ## 2. The termwise ζ-majorant at real `σ` -/

/-- At real `σ`, the `↗Λ` L-series term is the real number `Λ(n)·n^{−σ}` (cast to `ℂ`). -/
private lemma term_vonMangoldt_eq (σ : ℝ) (n : ℕ) :
    LSeries.term ↗vonMangoldt (σ : ℂ) n
      = ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

/-- **The termwise ζ-majorant (the Landau upper bound).** For **any** Dirichlet character `χ`
mod `q` and real `1 < σ ≤ 2`,
`−(1/(σ−1) + 1) ≤ Re(−L'/L(σ, χ))`.
Route: on `Re s > 1`, `−L'/L(s,χ) = Σ Λ(n)χ(n)n^{−s}` (S0's twist identity + the
LSeries↔LFunction bridge); termwise `Re(Λ(n)χ(n)n^{−σ}) ≥ −Λ(n)n^{−σ}` since `‖χ(n)‖ ≤ 1`;
the majorant series is `−ζ'/ζ(σ)`, bounded by the S3c pole bound `1/(σ−1) + 1`. -/
lemma landau_neg_logDeriv_re_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(1 / (σ - 1) + 1) ≤ (-logDeriv (LFunction χ) (σ : ℂ)).re := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact h1
  have hbridge : -logDeriv (LFunction χ) (σ : ℂ) = LSeries (↗χ * ↗vonMangoldt) (σ : ℂ) :=
    (neg_logDeriv_LSeries_eq χ hσC).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist χ hσC)
  rw [hbridge]
  -- summabilities
  have hSχ : Summable (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσC
  have hSΛ : Summable (LSeries.term ↗vonMangoldt (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσC
  -- the termwise comparison `−(term Λ).re ≤ (term χΛ).re`
  have hterm : ∀ n : ℕ, -(LSeries.term ↗vonMangoldt (σ : ℂ) n).re
      ≤ (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · set a : ℝ := vonMangoldt n / (n : ℝ) ^ σ with ha
      have ha0 : 0 ≤ a :=
        div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
      have hΛval : LSeries.term ↗vonMangoldt (σ : ℂ) n = (a : ℂ) := term_vonMangoldt_eq σ n
      have hΛre : (LSeries.term ↗vonMangoldt (σ : ℂ) n).re = a := by
        rw [hΛval, Complex.ofReal_re]
      have hnorm : ‖LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n‖ ≤ a := by
        have hfac : ‖LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n‖
            = ‖χ (n : ZMod q)‖ * ‖LSeries.term ↗vonMangoldt (σ : ℂ) n‖ := by
          rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Pi.mul_apply,
            mul_div_assoc, norm_mul]
        rw [hfac, hΛval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
        have := DirichletCharacter.norm_le_one χ (n : ZMod q)
        nlinarith [ha0]
      have hre := Complex.abs_re_le_norm (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n)
      rw [hΛre]
      have := abs_le.mp (le_trans hre hnorm)
      linarith [this.1]
  -- sum the comparison
  have hre₁ : (LSeries (↗χ * ↗vonMangoldt) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗χ * ↗vonMangoldt) (σ : ℂ) n).re := Complex.re_tsum hSχ
  have hre₀ : (LSeries ↗vonMangoldt (σ : ℂ)).re
      = ∑' n, (LSeries.term ↗vonMangoldt (σ : ℂ) n).re := Complex.re_tsum hSΛ
  have hs₁ := (Complex.hasSum_re hSχ.hasSum).summable
  have hs₀ := (Complex.hasSum_re hSΛ.hasSum).summable
  have hcmp : -(LSeries ↗vonMangoldt (σ : ℂ)).re ≤ (LSeries (↗χ * ↗vonMangoldt) (σ : ℂ)).re := by
    rw [hre₀, hre₁, ← tsum_neg]
    exact hs₀.neg.tsum_le_tsum hterm hs₁
  -- the ζ pole bound (S3c)
  have hζ : (LSeries ↗vonMangoldt (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσC]
    exact neg_logDeriv_zeta_le h1 h2
  linarith [hcmp, hζ]

/-! ## 3. The order bridge: factorization multiplicity = `analyticOrderAt` -/

/-- **Multiplicity is the analytic order.** Given an S2-endpoint-shaped factorization
`f = (∏_{ρ'∈Z}(·−ρ')^{m ρ'})·h` on `ball c r` with `h` analytic non-vanishing there, the
canonical `analyticOrderAt f ρ` equals the factorization multiplicity `m ρ` at any
`ρ ∈ Z ∩ ball c r`. This converts the endpoint's per-factorization multiplicities into a
factorization-independent statement (any other factorization instance can consume it). -/
lemma analyticOrderAt_eq_of_factorization {f h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    {Z : Finset ℂ} {m : ℂ → ℕ}
    (hana_h : AnalyticOnNhd ℂ h (ball c r))
    (hne_h : ∀ z ∈ ball c r, h z ≠ 0)
    (hEqOn : Set.EqOn f (fun z => (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) (ball c r))
    {ρ : ℂ} (hρZ : ρ ∈ Z) (hρball : ρ ∈ ball c r) :
    analyticOrderAt f ρ = (m ρ : ℕ∞) := by
  classical
  set g : ℂ → ℂ := fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z with hg
  have hprod_ana : AnalyticOnNhd ℂ (fun z => ∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) (ball c r) :=
    Finset.analyticOnNhd_fun_prod (Z.erase ρ) (fun ρ' _ => by
      apply AnalyticOnNhd.pow; exact (analyticOnNhd_id.sub analyticOnNhd_const))
  have hg_ana : AnalyticAt ℂ g ρ := (hprod_ana ρ hρball).mul (hana_h ρ hρball)
  have hg_ne : g ρ ≠ 0 := by
    have hgρ : g ρ = (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ := rfl
    rw [hgρ]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' => ?_) (hne_h ρ hρball)
    exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)
  have hev : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ (m ρ) • g z := by
    filter_upwards [isOpen_ball.mem_nhds hρball] with z hz
    have hval : f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z := hEqOn hz
    have hgz : g z = (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z := rfl
    rw [hval, smul_eq_mul, hgz, ← Finset.mul_prod_erase Z _ hρZ]
    ring
  have hrhs_ana : AnalyticAt ℂ (fun z => (z - ρ) ^ (m ρ) • g z) ρ := by
    simp only [smul_eq_mul]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg_ana
  have hf_ana : AnalyticAt ℂ f ρ := hrhs_ana.congr hev.symm
  exact hf_ana.analyticOrderAt_eq_natCast.mpr ⟨g, hg_ana, hg_ne, hev⟩

/-! ## 4. The workhorse at the explicit constant -/

/-- **S3e, the workhorse (explicit constant `c₁ = 1/5000`).** For a primitive `χ ≠ 1` mod `q`,
any two real zeros `β₁, β₂` of `L(·,χ)` in the window `1 − (1/5000)/log(4q) ≤ β` coincide,
and the common zero is **simple**: `analyticOrderAt (LFunction χ) β₁ = 1`. (Real-valuedness of
`χ` is not needed for the per-modulus statement — the two-term Landau argument only uses
`‖χ(n)‖ ≤ 1`.) -/
theorem landau_one_exceptional_at {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {β₁ β₂ : ℝ} (hz₁ : LFunction χ β₁ = 0) (hz₂ : LFunction χ β₂ = 0)
    (hw₁ : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₁)
    (hw₂ : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₂) :
    β₁ = β₂ ∧ analyticOrderAt (LFunction χ) (β₁ : ℂ) = 1 := by
  -- `q ≥ 2` from primitivity + nontriviality
  have hq2 : 2 ≤ q := by
    have hcond : χ.conductor = q := hχ
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1
    have hqne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set Lq : ℝ := Real.log (4 * (q : ℝ)) with hLdef
  -- `L ≥ 2` (since `4q ≥ 8 > e²`)
  have hL2 : (2 : ℝ) ≤ Lq := by
    have hexp2 : Real.exp 2 ≤ 8 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (4 * (q : ℝ)) :=
          Real.log_le_log (Real.exp_pos 2) (by linarith [hexp2, hqR])
  have hLpos : (0 : ℝ) < Lq := by linarith
  -- window arithmetic
  have hwin : (1 / 5000 : ℝ) / Lq ≤ 1 / 10000 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hβ₁1 : β₁ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by rw [Complex.ofReal_re]; linarith) hz₁
  have hβ₂1 : β₂ < 1 := by
    by_contra hc
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
      (by rw [Complex.ofReal_re]; linarith) hz₂
  have hβ₁gt : (1 / 2 : ℝ) < β₁ := by linarith [hw₁, hwin]
  have hβ₂gt : (1 / 2 : ℝ) < β₂ := by linarith [hw₂, hwin]
  -- the S2 endpoint at `t₀ = 0`
  obtain ⟨Z, m, h, hZmem, hana_h, hne_h, hEqOn, -, hnum⟩ :=
    LFunction_norm_logDeriv_sub_sum' χ hχ hq2 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero]
    at hZmem hana_h hne_h hEqOn hnum
  -- the evaluation point `σ = 1 + (3/5000)/L`
  set σ : ℝ := 1 + (3 / 5000) / Lq with hσdef
  have hσgap : (0 : ℝ) < (3 / 5000) / Lq := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσlt : σ < 2 := by
    have h3 : (3 / 5000 : ℝ) / Lq ≤ 3 / 10000 := by rw [div_le_iff₀ hLpos]; linarith
    rw [hσdef]; linarith
  have hσre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hLs : LFunction χ (σ : ℂ) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hσre]; linarith)
  have hsc : ‖(σ : ℂ) - 2‖ ≤ 23 / 20 := by
    have he : ((σ : ℂ) - 2) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  -- the two `−L'/L` bounds and the kept-sum squeeze
  have hre := neg_re_logDeriv_le (hnum (σ : ℂ) hsc hLs)
  have hlow := landau_neg_logDeriv_re_lower χ hσ1 hσlt.le
  have hM : 120 * Real.log (4 * (5 * 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
      ≤ 720 * Lq := by
    have h6 := log_four_M0_le (f := q) (q := q) (t := 0) (γ := 0) hq2 le_rfl hq2 (by simp)
    simp only [abs_zero, add_zero, zero_add] at h6
    have hmono : Real.log ((q : ℝ) * 2) ≤ Lq := by
      rw [hLdef]
      exact Real.log_le_log (by linarith) (by linarith)
    linarith [h6, hmono]
  have hSum : (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re)
      ≤ 1 / (σ - 1) + 1 + 720 * Lq := by
    have hstep : (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re)
        ≤ 120 * Real.log (4 * (5 * 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
          + (1 / (σ - 1) + 1) := by linarith [hre, hlow]
    calc (∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re)
        ≤ 120 * Real.log (4 * (5 * 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
          + (1 / (σ - 1) + 1) := hstep
      _ ≤ 720 * Lq + (1 / (σ - 1) + 1) := add_le_add hM le_rfl
      _ = 1 / (σ - 1) + 1 + 720 * Lq := by ring
  -- kept terms are nonnegative
  have hpos : ∀ ρ' ∈ Z, 0 < ((σ : ℂ) - ρ').re := by
    intro ρ' hρ'
    have hρ'0 : LFunction χ ρ' = 0 := (hZmem ρ' hρ').2
    have hlt : ρ'.re < 1 := by
      by_contra hc
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hc) hρ'0
    rw [Complex.sub_re, hσre]; linarith
  -- the window zeros lie in the partial-fraction set
  have hball : ∀ {β : ℝ}, 1 / 2 < β → β < 1 → (β : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
    intro β hβgt hβlt
    rw [mem_ball, dist_eq_norm]
    have he : ((β : ℂ) - 2) = ((β - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  obtain ⟨hβ₁Z, hm₁⟩ := mem_zeros_of_factorization hne_h hEqOn (hball hβ₁gt hβ₁1) hz₁
  obtain ⟨hβ₂Z, hm₂⟩ := mem_zeros_of_factorization hne_h hEqOn (hball hβ₂gt hβ₂1) hz₂
  -- real-part computation for the kept terms
  have hterm_re : ∀ β : ℝ, (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    intro β
    have he : ((σ : ℂ) - (β : ℂ)) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
    rw [he, show (1 : ℂ) / ((σ - β : ℝ) : ℂ) = (((1 / (σ - β)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  -- gap bounds
  have hx₁pos : (0 : ℝ) < σ - β₁ := by linarith
  have hx₂pos : (0 : ℝ) < σ - β₂ := by linarith
  have hgapsum : (3 / 5000 : ℝ) / Lq + (1 / 5000) / Lq = (4 / 5000) / Lq := by
    rw [← add_div]; norm_num
  have hx₁4 : σ - β₁ ≤ (4 / 5000) / Lq := by rw [hσdef]; linarith [hw₁, hgapsum]
  have hx₂4 : σ - β₂ ≤ (4 / 5000) / Lq := by rw [hσdef]; linarith [hw₂, hgapsum]
  have hσ1val : 1 / (σ - 1) = Lq / (3 / 5000) := by
    rw [show σ - 1 = (3 / 5000) / Lq by rw [hσdef]; ring, one_div_div]
  -- Claim A: the two window zeros coincide
  have hβeq : β₁ = β₂ := by
    by_contra hne
    have hneC : (β₁ : ℂ) ≠ (β₂ : ℂ) := fun hc => hne (by exact_mod_cast hc)
    have hsub : ({(β₁ : ℂ), (β₂ : ℂ)} : Finset ℂ) ⊆ Z := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hβ₁Z
      · rw [Finset.mem_singleton.mp hx]; exact hβ₂Z
    have hpairsum : ∑ ρ' ∈ ({(β₁ : ℂ), (β₂ : ℂ)} : Finset ℂ),
          (m ρ' : ℝ) * (1 / ((σ : ℂ) - ρ')).re
        = (m (β₁ : ℂ) : ℝ) * (1 / ((σ : ℂ) - (β₁ : ℂ))).re
          + (m (β₂ : ℂ) : ℝ) * (1 / ((σ : ℂ) - (β₂ : ℂ))).re :=
      Finset.sum_pair hneC
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ρ' hρ' _ => term_re_nonneg m hpos ρ' hρ')
    have h₁ : 1 / (σ - β₁) ≤ (m (β₁ : ℂ) : ℝ) * (1 / ((σ : ℂ) - (β₁ : ℂ))).re := by
      rw [hterm_re]
      have hm : (1 : ℝ) ≤ (m (β₁ : ℂ) : ℝ) := by exact_mod_cast hm₁
      nlinarith [one_div_pos.mpr hx₁pos]
    have h₂ : 1 / (σ - β₂) ≤ (m (β₂ : ℂ) : ℝ) * (1 / ((σ : ℂ) - (β₂ : ℂ))).re := by
      rw [hterm_re]
      have hm : (1 : ℝ) ≤ (m (β₂ : ℂ) : ℝ) := by exact_mod_cast hm₂
      nlinarith [one_div_pos.mpr hx₂pos]
    exact landau_extraction hL2 hx₁pos hx₂pos hx₁4 hx₂4
      (by rw [← hσ1val]; linarith [hpairsum, hmono, hSum, h₁, h₂])
  -- Claim B: the common zero is simple
  have hm1 : m (β₁ : ℂ) = 1 := by
    by_contra hnem
    have hm2 : 2 ≤ m (β₁ : ℂ) := by omega
    have hone : 1 / (σ - β₁) + 1 / (σ - β₁)
        ≤ (m (β₁ : ℂ) : ℝ) * (1 / ((σ : ℂ) - (β₁ : ℂ))).re := by
      rw [hterm_re]
      have hm : (2 : ℝ) ≤ (m (β₁ : ℂ) : ℝ) := by exact_mod_cast hm2
      nlinarith [one_div_pos.mpr hx₁pos]
    have hsingle := Finset.single_le_sum (term_re_nonneg m hpos) hβ₁Z
    exact landau_extraction hL2 hx₁pos hx₁pos hx₁4 hx₁4
      (by rw [← hσ1val]; linarith [hone, hsingle, hSum])
  have horder : analyticOrderAt (LFunction χ) (β₁ : ℂ) = (m (β₁ : ℂ) : ℕ∞) :=
    analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hβ₁Z (hball hβ₁gt hβ₁1)
  refine ⟨hβeq, ?_⟩
  rw [horder, hm1, Nat.cast_one]

/-! ## 5. The S4/S5-facing endpoints -/

/-- **S3e — Landau's one-exceptional-zero theorem (per modulus), distinctness half.** There is
an explicit `c₁ > 0` (`c₁ = 1/5000`) such that for every primitive real (quadratic) Dirichlet
character `χ ≠ 1` mod `q`, the window `1 − c₁/log(4q) ≤ β` contains at most one real zero of
`L(·,χ)`: any two such zeros coincide. (`β < 1` is automatic — `L(·,χ)` does not vanish on
`Re s ≥ 1` for `χ ≠ 1`.) The cross-modulus Page half is S4-wave material, not here. -/
theorem landau_one_exceptional :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ {β₁ β₂ : ℝ}, LFunction χ β₁ = 0 → LFunction χ β₂ = 0 →
        1 - c₁ / Real.log (4 * q) ≤ β₁ → 1 - c₁ / Real.log (4 * q) ≤ β₂ → β₁ = β₂ := by
  refine ⟨1 / 5000, by norm_num, ?_⟩
  intro q hNe χ hχ _hsq hχ1 β₁ β₂ hz₁ hz₂ hw₁ hw₂
  exact (landau_one_exceptional_at hχ hχ1 hz₁ hz₂ hw₁ hw₂).1

/-- **S3e — the multiplicity strengthening: the exceptional zero is simple.** Same constant
`c₁ = 1/5000`: any real zero of `L(·,χ)` in the window has `analyticOrderAt = 1` — the
factorization-independent simplicity statement the S5 residue extraction consumes
(`analyticOrderAt_eq_of_factorization` converts it back into any S2-endpoint factorization's
multiplicity `m β = 1`). -/
theorem landau_one_exceptional_simple :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ {β : ℝ}, LFunction χ β = 0 → 1 - c₁ / Real.log (4 * q) ≤ β →
        analyticOrderAt (LFunction χ) (β : ℂ) = 1 := by
  refine ⟨1 / 5000, by norm_num, ?_⟩
  intro q hNe χ hχ _hsq hχ1 β hz hw
  exact (landau_one_exceptional_at hχ hχ1 hz hz hw hw).2

end Salt.SW

