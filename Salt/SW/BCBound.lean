/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.PartialFractions

/-!
# The SW rung, node S2-Z3b — the Borel–Carathéodory numeric `‖h'/h‖ ≤ C·log M₀`

Design: `docs/blueprints/sw.md`, wave S2. This module discharges the numeric estimate that
`Salt/SW/PartialFractions.lean` flagged (`norm_logDeriv_sub_sum_le`'s hypothesis): a bound
`‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ C·log(4 M₀)` on the disk about the comfortable center
`c = 2 + it₀`, where `M₀ = 5(4+|t₀|)√f(1+log f)` is the growth-sphere quantity.

## Route (the classical Landau/Blaschke argument, made explicit)

`LFunction_partialFraction` supplies a factorization `L = P·h` on `ball c (3/2)` with `P` the
polynomial of the (finitely many) zeros `ρ ∈ Z` and `h` analytic non-vanishing, together with the
identity `L'/L − ∑_ρ m_ρ/(s−ρ) = h'/h`. Borel–Carathéodory needs an *upper* bound on
`Re log h`, i.e. on `‖h‖ = ‖L‖/‖P‖`, which fails near the zeros because `‖P‖` has no lower bound.
The classical fix replaces the linear factors `(·−ρ)` by *Blaschke factors* of modulus one on the
boundary circle. Concretely we introduce the **reflected factor**
`reflectedFactor c ρ z = (R² − conj(ρ−c)(z−c))/R` (`R = 3/2`) and set
`g := h · ∏_{ρ∈Z} reflectedFactor c ρ ^ m_ρ = L / B`, where `B` is the Blaschke product. On the
boundary sphere `‖B‖ = 1`, so `‖g‖ = ‖L‖ ≤ M₀` there and (by the maximum-modulus principle)
throughout the disk; `g` is non-vanishing, so it has an analytic logarithm and Borel–Carathéodory
(`Salt.SW.norm_deriv_le_of_re_le`) bounds `‖g'/g‖`. The Blaschke correction
`g'/g − h'/h = (logDeriv of the reflected product)` is an `O(1/R)`-per-zero sum, bounded by
`(∑ m_ρ)/(R − ρ)`, itself `O(log M₀)` via the Jensen count. Adding the two gives the numeric bound.

## Main results

* `reflectedFactor`, `hasDerivAt_reflectedFactor`, `norm_logDeriv_reflectedFactor_le`,
  `logDeriv_reflected_prod` — the Blaschke reflected-factor arithmetic (fully proven).
* `norm_logDeriv_sub_sum_of_blaschke` — the abstract Landau numeric: given a factorization
  `L = P·h` on `ball c (3/2)` satisfying the `PartialFractions` invariants **and** the single
  analytic input `hsup` (the maximum-modulus sup bound `‖g‖ ≤ M₀` on the Blaschke-normalized
  factor `g = h·∏ reflectedFactor^m`), the numeric bound
  `‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4 M₀)` holds for `‖s−c‖ ≤ 23/20`, `L s ≠ 0`. The
  Borel–Carathéodory application and the reflected-pole arithmetic are discharged here.
* `LFunction_norm_logDeriv_sub_sum` — the S2-Z3b target: `LFunction_partialFraction` fed into the
  abstract lemma, exposing `Z`, `m` and the numeric bound **gated by `hsup`**.
* `LFunction_neg_reLogDeriv_le` — the real-part corollary S3 consumes.

## Flag ⟦RETIRED 2026-08-04: SUPERSEDED — the ungated endpoint
LFunction_norm_logDeriv_sub_sum' landed at 910f779 in Salt/SW/MaxModulus.lean;
this flag described only THIS file's gated lemma and mispriced two waves.
Law: a Flag block is a claim about the corpus and goes stale like any
absence assertion.⟧ (historical text follows) (PB-floor boundary — the single remaining analytic input `hsup`)

The one classical step **not** discharged here is `hsup`: the maximum-modulus sup bound
`‖g z‖ ≤ M₀` on `ball c (3/2)` for the Blaschke-normalized `g = h·∏ reflectedFactor^m`. Its proof
needs (i) `‖B‖ = 1` on the boundary sphere (mathlib's
`Complex.norm_canonicalFactor_eval_circle_eq_one`), giving `‖g‖ = ‖L‖ ≤ M₀` there, and (ii) the
maximum-modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`), which needs `g = h·Q`
continuous up to the boundary — `h` is analytic only on the *open* ball, so this needs `h`
re-obtained from a factorization at a slightly larger radius (`8/5`) with the annulus zeros folded
back into `h` (`LFunction_exists_factorization` at radius `8/5`). Everything else — the
reflected-pole arithmetic, the analytic-logarithm construction (`HasPrimitives` +
`logDeriv_eqOn_iff`), and the Borel–Carathéodory application — is discharged unconditionally.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Function DirichletCharacter Set Filter
open scoped Topology

/-! ## 1. The Blaschke reflected factor -/

/-- The **reflected factor** `(R² − conj(ρ−c)(z−c))/R` with `R = 3/2`. Together with the linear
factor `(z−ρ)` it forms the Blaschke factor `R(z−ρ)/(R²−conj(ρ−c)(z−c))` of modulus one on the
boundary circle `|z−c| = R`; its logarithmic derivative supplies the `O(1/R)`-per-zero Blaschke
correction to the partial-fraction sum. -/
noncomputable def reflectedFactor (c ρ : ℂ) : ℂ → ℂ :=
  fun z => ((9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (z - c)) / ((3 : ℂ) / 2)

/-- The reflected factor is affine, with derivative `−conj(ρ−c)/R`. -/
lemma hasDerivAt_reflectedFactor (c ρ z : ℂ) :
    HasDerivAt (reflectedFactor c ρ) (-(starRingEnd ℂ) (ρ - c) / ((3 : ℂ) / 2)) z := by
  have h1 : HasDerivAt (fun z : ℂ => (starRingEnd ℂ) (ρ - c) * (z - c))
      ((starRingEnd ℂ) (ρ - c)) z := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id z).sub_const c).const_mul ((starRingEnd ℂ) (ρ - c))
  have h2 : HasDerivAt (fun z : ℂ => (9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (z - c))
      (-(starRingEnd ℂ) (ρ - c)) z := h1.const_sub ((9 : ℂ) / 4)
  exact h2.div_const ((3 : ℂ) / 2)

/-- The reflected factor is non-vanishing on the disk (both `ρ` and `z` inside radius `R`). -/
lemma reflectedFactor_ne_zero {c ρ z : ℂ} (hρ : ‖ρ - c‖ < 3 / 2) (hz : ‖z - c‖ < 3 / 2) :
    reflectedFactor c ρ z ≠ 0 := by
  rw [reflectedFactor, div_ne_zero_iff]
  refine ⟨fun hnum => ?_, by norm_num⟩
  have heq : ((9 : ℂ) / 4) = (starRingEnd ℂ) (ρ - c) * (z - c) := sub_eq_zero.mp hnum
  have hlt : ‖(starRingEnd ℂ) (ρ - c) * (z - c)‖ < 9 / 4 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [hρ, hz, norm_nonneg (ρ - c), norm_nonneg (z - c)]
  rw [← heq] at hlt
  have hn : ‖(9 : ℂ) / 4‖ = 9 / 4 := by norm_num
  rw [hn] at hlt; linarith

/-- Per-factor logarithmic-derivative bound: `‖logDeriv (reflectedFactor c ρ) s‖ ≤ 20/7`
for `‖ρ−c‖ < R` and `‖s−c‖ ≤ 23/20` — this is `1/(R − ρ)` with `R = 3/2`, `ρ = 23/20`, the
reflected-pole correction per unit multiplicity. -/
lemma norm_logDeriv_reflectedFactor_le {c ρ s : ℂ} (hρ : ‖ρ - c‖ < 3 / 2) (hs : ‖s - c‖ ≤ 23 / 20) :
    ‖logDeriv (reflectedFactor c ρ) s‖ ≤ 20 / 7 := by
  have hval : logDeriv (reflectedFactor c ρ) s
      = -(starRingEnd ℂ) (ρ - c) / ((9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (s - c)) := by
    rw [logDeriv_apply, (hasDerivAt_reflectedFactor c ρ s).deriv]
    rw [show reflectedFactor c ρ s
        = ((9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (s - c)) / ((3 : ℂ) / 2) from rfl]
    rw [div_div_div_cancel_right₀ (by norm_num : ((3 : ℂ) / 2) ≠ 0)]
  rw [hval, norm_div, norm_neg, Complex.norm_conj]
  have hden : (21 : ℝ) / 40 ≤ ‖(9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (s - c)‖ := by
    have h1 : ‖(starRingEnd ℂ) (ρ - c) * (s - c)‖ ≤ 69 / 40 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [hρ, hs, norm_nonneg (ρ - c), norm_nonneg (s - c)]
    have h2 := norm_sub_norm_le ((9 : ℂ) / 4) ((starRingEnd ℂ) (ρ - c) * (s - c))
    have h3 : ‖(9 : ℂ) / 4‖ = 9 / 4 := by norm_num
    rw [h3] at h2; linarith
  have hdenpos : (0 : ℝ) < ‖(9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (s - c)‖ := by linarith
  rw [div_le_iff₀ hdenpos]
  nlinarith [hρ, hden]

/-- Logarithmic derivative of the reflected Blaschke product `∏_{ρ∈Z} (reflectedFactor c ρ)^{m_ρ}`
at `s`, as the multiplicity-weighted sum of per-factor logarithmic derivatives. -/
lemma logDeriv_reflected_prod (Z : Finset ℂ) (m : ℂ → ℕ) (c : ℂ) {s : ℂ}
    (hs : ∀ ρ ∈ Z, reflectedFactor c ρ s ≠ 0) :
    logDeriv (fun z => ∏ ρ ∈ Z, (reflectedFactor c ρ z) ^ (m ρ)) s
      = ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (reflectedFactor c ρ) s := by
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ _
    rw [logDeriv_fun_pow (hasDerivAt_reflectedFactor c ρ s).differentiableAt]
  · intro ρ hρ
    exact pow_ne_zero _ (hs ρ hρ)
  · intro ρ _
    exact ((hasDerivAt_reflectedFactor c ρ s).differentiableAt).pow _

/-! ## 2. The abstract Landau numeric bound (Borel–Carathéodory + reflected poles) -/

/-- **The abstract Landau numeric.** Given a `LFunction_partialFraction`-shaped factorization
`L = (∏_{ρ∈Z}(·−ρ)^{m_ρ})·h` on `ball c (3/2)` with the invariants (`hLc`: `‖L c‖ ≥ 1/4`;
`hmemZ`: zeros inside; `hcount`: the Jensen zero count `∑ m_ρ ≤ log(4M₀)/log(7/6)`; `hana_h`,
`hne_h`, `hEqOn`, `hident`), **and** the single analytic input `hsup` (the Blaschke maximum-modulus
sup bound `‖g‖ ≤ M₀` on the normalized factor `g = h·∏ reflectedFactor^m`), the numeric bound
`‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4 M₀)` holds for `‖s−c‖ ≤ 23/20` with `L s ≠ 0`.

The Borel–Carathéodory application (via the analytic logarithm of `g`, built from `HasPrimitives`
+ `logDeriv_eqOn_iff`) contributes `100·log(4M₀)`; the reflected-pole Blaschke correction
contributes `20·log(4M₀)`. Only `hsup` is left unproven; see the module flag. -/
theorem norm_logDeriv_sub_sum_of_blaschke {L h : ℂ → ℂ} {c : ℂ} {M₀ : ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (hM₀ : 1 ≤ M₀)
    (hLc : (1 : ℝ) / 4 ≤ ‖L c‖)
    (hmemZ : ∀ ρ ∈ Z, ρ ∈ ball c (3 / 2))
    (hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6))
    (hana_h : AnalyticOnNhd ℂ h (ball c (3 / 2)))
    (hne_h : ∀ z ∈ ball c (3 / 2), h z ≠ 0)
    (hEqOn : Set.EqOn L (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z) (ball c (3 / 2)))
    (hident : ∀ s ∈ ball c (3 / 2), L s ≠ 0 →
      logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s)
    (hsup : ∀ z ∈ ball c (3 / 2),
      ‖h z * ∏ ρ ∈ Z, (reflectedFactor c ρ z) ^ (m ρ)‖ ≤ M₀)
    {s : ℂ} (hs : ‖s - c‖ ≤ 23 / 20) (hLs : L s ≠ 0) :
    ‖logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ 120 * Real.log (4 * M₀) := by
  set Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (reflectedFactor c ρ z) ^ (m ρ) with hQdef
  set g : ℂ → ℂ := fun z => h z * Q z with hgdef
  have hLM_nonneg : 0 ≤ Real.log (4 * M₀) := Real.log_nonneg (by nlinarith [hM₀])
  have hLM_pos : 0 < Real.log (4 * M₀) := Real.log_pos (by nlinarith [hM₀])
  have hsball : s ∈ ball c (3 / 2) := by rw [mem_ball, dist_eq_norm]; linarith
  have hcball : c ∈ ball c (3 / 2) := mem_ball_self (by norm_num)
  -- analyticity of `Q`, `g`
  have hrf_ana : ∀ ρ, AnalyticOnNhd ℂ (reflectedFactor c ρ) (ball c (3 / 2)) := by
    intro ρ
    have hden : AnalyticOnNhd ℂ (fun _ : ℂ => (3 : ℂ) / 2) (ball c (3 / 2)) := analyticOnNhd_const
    have hnum : AnalyticOnNhd ℂ (fun z : ℂ => (9 : ℂ) / 4 - (starRingEnd ℂ) (ρ - c) * (z - c))
        (ball c (3 / 2)) :=
      analyticOnNhd_const.sub (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))
    exact hnum.div hden (fun z _ => by norm_num)
  have hQ_ana : AnalyticOnNhd ℂ Q (ball c (3 / 2)) := by
    rw [hQdef]
    exact Finset.analyticOnNhd_fun_prod Z (fun ρ _ => (hrf_ana ρ).pow _)
  have hg_ana : AnalyticOnNhd ℂ g (ball c (3 / 2)) := hana_h.mul hQ_ana
  -- non-vanishing of `Q`, `g`
  have hrf_ne : ∀ ρ ∈ Z, ∀ z ∈ ball c (3 / 2), reflectedFactor c ρ z ≠ 0 := by
    intro ρ hρ z hz
    refine reflectedFactor_ne_zero ?_ ?_
    · have := hmemZ ρ hρ; rwa [mem_ball, dist_eq_norm] at this
    · rwa [mem_ball, dist_eq_norm] at hz
  have hQ_ne : ∀ z ∈ ball c (3 / 2), Q z ≠ 0 := by
    intro z hz
    rw [hQdef]
    exact Finset.prod_ne_zero_iff.mpr (fun ρ hρ => pow_ne_zero _ (hrf_ne ρ hρ z hz))
  have hg_ne : ∀ z ∈ ball c (3 / 2), g z ≠ 0 := fun z hz => mul_ne_zero (hne_h z hz) (hQ_ne z hz)
  have hgc_ne : g c ≠ 0 := hg_ne c hcball
  -- `‖g c‖ ≥ 1/4`
  have hgc_lb : (1 : ℝ) / 4 ≤ ‖g c‖ := by
    have hLcfact : L c = (∏ ρ ∈ Z, (c - ρ) ^ (m ρ)) * h c := hEqOn hcball
    set Pc : ℂ := ∏ ρ ∈ Z, (c - ρ) ^ (m ρ) with hPc
    have hQc_val : Q c = ∏ ρ ∈ Z, ((3 : ℂ) / 2) ^ (m ρ) := by
      rw [hQdef]; apply Finset.prod_congr rfl; intro ρ _
      rw [show reflectedFactor c ρ c = (3 : ℂ) / 2 by
        rw [reflectedFactor, sub_self, mul_zero, sub_zero]; norm_num]
    have hnormQc : ‖Q c‖ = ∏ ρ ∈ Z, (3 / 2 : ℝ) ^ (m ρ) := by
      rw [hQc_val, norm_prod]; apply Finset.prod_congr rfl; intro ρ _; rw [norm_pow]; norm_num
    have hnormPc_le : ‖Pc‖ ≤ ∏ ρ ∈ Z, (3 / 2 : ℝ) ^ (m ρ) := by
      rw [hPc, norm_prod]
      apply Finset.prod_le_prod (fun ρ _ => norm_nonneg _)
      intro ρ hρ
      rw [norm_pow]
      have hb : ‖c - ρ‖ ≤ 3 / 2 := by
        have := hmemZ ρ hρ; rw [mem_ball, dist_eq_norm] at this
        rw [norm_sub_rev]; linarith
      gcongr
    have hgcPc : g c * Pc = Q c * L c := by rw [hgdef, hLcfact, hPc]; ring
    have hPc_ne : Pc ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hLcfact
      rw [hLcfact, norm_zero] at hLc
      linarith
    have hnorms : ‖g c‖ * ‖Pc‖ = ‖Q c‖ * ‖L c‖ := by rw [← norm_mul, ← norm_mul, hgcPc]
    have hPcpos : 0 < ‖Pc‖ := norm_pos_iff.mpr hPc_ne
    have hfinal : ‖Pc‖ * ‖L c‖ ≤ ‖g c‖ * ‖Pc‖ := by
      rw [hnorms, hnormQc]
      exact mul_le_mul_of_nonneg_right hnormPc_le (norm_nonneg _)
    have hle : ‖L c‖ ≤ ‖g c‖ := by
      have h' : ‖L c‖ * ‖Pc‖ ≤ ‖g c‖ * ‖Pc‖ := by rw [mul_comm ‖L c‖ ‖Pc‖]; exact hfinal
      exact le_of_mul_le_mul_right h' hPcpos
    linarith
  -- `logDeriv g` differentiable on the ball
  have hlogg_diff : DifferentiableOn ℂ (logDeriv g) (ball c (3 / 2)) := by
    have hderiv_ana : AnalyticOnNhd ℂ (deriv g) (ball c (3 / 2)) := hg_ana.deriv
    have hdiv : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c (3 / 2)) :=
      hderiv_ana.differentiableOn.div hg_ana.differentiableOn hg_ne
    have heq : logDeriv g = fun z => deriv g z / g z := by funext z; exact logDeriv_apply g z
    rw [heq]; exact hdiv
  -- the analytic logarithm `G` of `g`
  obtain ⟨G, hGc, hGderiv⟩ := (hlogg_diff.isExactOn_ball).with_val_at c 0
  have hg_diffOn : DifferentiableOn ℂ g (ball c (3 / 2)) := hg_ana.differentiableOn
  have hψ_diff : DifferentiableOn ℂ (fun z => Complex.exp (G z)) (ball c (3 / 2)) :=
    fun z hz => ((hGderiv z hz).cexp).differentiableAt.differentiableWithinAt
  have hψ_ne : ∀ z ∈ ball c (3 / 2), Complex.exp (G z) ≠ 0 := fun z _ => Complex.exp_ne_zero _
  have hlogEq : Set.EqOn (logDeriv (fun z => Complex.exp (G z))) (logDeriv g) (ball c (3 / 2)) := by
    intro z hz
    have hd : HasDerivAt (fun w => Complex.exp (G w)) (Complex.exp (G z) * logDeriv g z) z :=
      (hGderiv z hz).cexp
    rw [logDeriv_apply, hd.deriv]
    change Complex.exp (G z) * logDeriv g z / Complex.exp (G z) = logDeriv g z
    rw [mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero (G z)), mul_one]
  obtain ⟨z₀, hz₀ne, hz₀eq⟩ :=
    (logDeriv_eqOn_iff hψ_diff hg_diffOn isOpen_ball (convex_ball c (3 / 2)).isPreconnected
      hg_ne hψ_ne).mp hlogEq
  have hzeq : (1 : ℂ) = z₀ * g c := by
    have h := hz₀eq hcball
    simpa [Pi.smul_apply, smul_eq_mul, hGc, Complex.exp_zero] using h
  have hz₀norm : ‖z₀‖ = ‖g c‖⁻¹ := by
    have h1 : ‖z₀‖ * ‖g c‖ = 1 := by rw [← norm_mul, ← hzeq, norm_one]
    rw [inv_eq_one_div, eq_div_iff (norm_ne_zero_iff.mpr hgc_ne)]
    exact h1
  have hRe : ∀ z ∈ ball c (3 / 2), (G z).re = Real.log (‖g z‖ / ‖g c‖) := by
    intro z hz
    have h1 : Complex.exp (G z) = z₀ * g z := by
      have := hz₀eq hz; simpa [Pi.smul_apply, smul_eq_mul] using this
    have h2 : Real.exp ((G z).re) = ‖g z‖ / ‖g c‖ := by
      have h3 := congrArg norm h1
      rw [Complex.norm_exp, norm_mul, hz₀norm] at h3
      rw [h3]; ring
    rw [← Real.log_exp ((G z).re), h2]
  -- shift to `0`-centered `G̃` for Borel–Carathéodory
  have hmap : ∀ ζ ∈ ball (0 : ℂ) (3 / 2), c + ζ ∈ ball c (3 / 2) := by
    intro ζ hζ; rw [mem_ball_zero_iff] at hζ; rw [mem_ball, dist_eq_norm]
    simpa [add_sub_cancel_left] using hζ
  have hgt0 : (fun ζ => G (c + ζ)) 0 = 0 := by simpa using hGc
  have hgt_diff : DifferentiableOn ℂ (fun ζ => G (c + ζ)) (ball (0 : ℂ) (3 / 2)) := by
    intro ζ hζ
    exact ((hGderiv (c + ζ) (hmap ζ hζ)).comp_const_add c ζ).differentiableAt.differentiableWithinAt
  have hgtM : ∀ ζ ∈ ball (0 : ℂ) (3 / 2), (G (c + ζ)).re ≤ Real.log (4 * M₀) := by
    intro ζ hζ
    have hcζ := hmap ζ hζ
    have hgcpos : (0 : ℝ) < ‖g c‖ := norm_pos_iff.mpr hgc_ne
    rw [hRe (c + ζ) hcζ]
    apply Real.log_le_log (div_pos (norm_pos_iff.mpr (hg_ne (c + ζ) hcζ)) hgcpos)
    rw [div_le_iff₀ hgcpos]
    have h1 : ‖g (c + ζ)‖ ≤ M₀ := by
      have := hsup (c + ζ) hcζ; simpa [hgdef, hQdef] using this
    nlinarith [h1, hgc_lb, hM₀,
      mul_nonneg (by linarith [hgc_lb] : (0 : ℝ) ≤ ‖g c‖ - 1 / 4)
        (by linarith [hM₀] : (0 : ℝ) ≤ M₀)]
  -- Borel–Carathéodory: `‖logDeriv g s‖ ≤ 100·log(4M₀)`
  have hsc_ball : s - c ∈ ball (0 : ℂ) (3 / 2) := by rw [mem_ball_zero_iff]; linarith
  have hbc := norm_deriv_le_of_re_le (M := Real.log (4 * M₀)) (R := 3 / 2) (ρ := 23 / 20)
    (s := 1 / 10) (w := s - c) hLM_pos hgt_diff hgt0 hgtM (by norm_num) hs (by norm_num)
  have hderiv_eq : deriv (fun ζ => G (c + ζ)) (s - c) = logDeriv g s := by
    have h : deriv (fun ζ => G (c + ζ)) (s - c) = deriv G (c + (s - c)) :=
      deriv_comp_const_add G c (s - c)
    rw [h, show c + (s - c) = s by ring, (hGderiv s hsball).deriv]
  rw [hderiv_eq] at hbc
  have hBC : ‖logDeriv g s‖ ≤ 100 * Real.log (4 * M₀) := by
    refine le_trans hbc (le_of_eq ?_)
    rw [div_eq_iff (by norm_num : ((1 : ℝ) / 10) * (3 / 2 - 23 / 20 - 1 / 10) ≠ 0)]
    ring
  -- reflected-pole bound: `‖logDeriv Q s‖ ≤ 20·log(4M₀)`
  have hlogQ : logDeriv Q s = ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (reflectedFactor c ρ) s := by
    rw [hQdef]
    exact logDeriv_reflected_prod Z m c (fun ρ hρ => hrf_ne ρ hρ s hsball)
  have hlog76 : (1 : ℝ) / 7 ≤ Real.log (7 / 6) := by
    have h1 : Real.log (6 / 7) ≤ 6 / 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (7 / 6) = -Real.log (6 / 7) := by
      rw [show (7 : ℝ) / 6 = (6 / 7)⁻¹ by norm_num, Real.log_inv]
    rw [h2]; linarith
  have hReflected : ‖logDeriv Q s‖ ≤ 20 * Real.log (4 * M₀) := by
    have hstep1 : ‖logDeriv Q s‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (20 / 7) := by
      rw [hlogQ]
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact norm_logDeriv_reflectedFactor_le (by
        have := hmemZ ρ hρ; rwa [mem_ball, dist_eq_norm] at this) hs
    have hstep2 : (∑ ρ ∈ Z, (m ρ : ℝ) * (20 / 7)) = (20 / 7) * (∑ ρ ∈ Z, (m ρ : ℝ)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring
    rw [hstep2] at hstep1
    have hSum_le : (20 / 7) * (∑ ρ ∈ Z, (m ρ : ℝ))
        ≤ (20 / 7) * (Real.log (4 * M₀) / Real.log (7 / 6)) :=
      mul_le_mul_of_nonneg_left hcount (by norm_num)
    have hDiv_le : (20 / 7) * (Real.log (4 * M₀) / Real.log (7 / 6)) ≤ 20 * Real.log (4 * M₀) := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log (7 / 6))]
      nlinarith [hlog76, hLM_nonneg]
    linarith
  -- assemble
  rw [hident s hsball hLs]
  have hsplit : logDeriv h s = logDeriv g s - logDeriv Q s := by
    have hmul : logDeriv g s = logDeriv h s + logDeriv Q s := by
      rw [hgdef]
      exact logDeriv_mul s (hne_h s hsball) (hQ_ne s hsball)
        (hana_h.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hsball))
        (hQ_ana.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hsball))
    rw [hmul]; ring
  rw [hsplit]
  calc ‖logDeriv g s - logDeriv Q s‖ ≤ ‖logDeriv g s‖ + ‖logDeriv Q s‖ := norm_sub_le _ _
    _ ≤ 100 * Real.log (4 * M₀) + 20 * Real.log (4 * M₀) := add_le_add hBC hReflected
    _ = 120 * Real.log (4 * M₀) := by ring

/-! ## 3. The S2-Z3b target on the disk about `c = 2 + it₀` -/

/-- **S2-Z3b — the L'/L numeric near the 1-line.** For a primitive Dirichlet character `χ` mod
`f ≥ 2` and `t₀ ∈ ℝ`, on the disk `ball (2 + it₀) (3/2)` there is a finite set `Z` of zeros of
`L(·,χ)` (multiplicities `m`) and an analytic non-vanishing remainder `h` with the
`LFunction_partialFraction` invariants, and — **gated by** the Blaschke maximum-modulus sup bound
`hsup` (see module flag) — the numeric bound
`‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ 120·log(4·M₀)` for `‖s − (2+it₀)‖ ≤ 23/20`, `L s ≠ 0`, with
`M₀ = 5(4+|t₀|)√f(1+log f)` the growth-sphere quantity (`O(log(f(|t₀|+2)))`). The evaluation
region covers the S3 box `{1−1/8 ≤ Re s ≤ 2, |Im s − t₀| ≤ 1/8}` (radius `√(82)/8 < 23/20`). -/
theorem LFunction_norm_logDeriv_sub_sum {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t₀ : ℝ) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2) ∧ LFunction χ ρ = 0) ∧
      AnalyticOnNhd ℂ h (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ z ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), h z ≠ 0) ∧
      Set.EqOn (LFunction χ) (fun z => (∏ ρ ∈ Z, (z - ρ) ^ (m ρ)) * h z)
        (ball (2 + (t₀ : ℂ) * I) (3 / 2)) ∧
      (∀ s ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2), LFunction χ s ≠ 0 →
        logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = logDeriv h s) ∧
      ((∀ z ∈ ball (2 + (t₀ : ℂ) * I) (3 / 2),
          ‖h z * ∏ ρ ∈ Z, (reflectedFactor (2 + (t₀ : ℂ) * I) ρ z) ^ (m ρ)‖
            ≤ 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f)) →
        ∀ s, ‖s - (2 + (t₀ : ℂ) * I)‖ ≤ 23 / 20 → LFunction χ s ≠ 0 →
          ‖logDeriv (LFunction χ) s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
            ≤ 120 * Real.log (4 * (5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f)))) := by
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  set M₀ : ℝ := 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) with hM₀
  have hcre : c.re = 2 := by rw [hc]; simp
  have hLc : (1 : ℝ) / 4 ≤ ‖LFunction χ c‖ := LFunction_center_lower χ (le_of_eq hcre.symm)
  -- `1 ≤ M₀` (identical to the `LFunction_partialFraction` argument)
  have hlog2 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ f))
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; exact_mod_cast (by omega : 1 ≤ f)
  have hM₀1 : 1 ≤ M₀ := by
    have ha : (4 : ℝ) ≤ 4 + |t₀| := by linarith [abs_nonneg t₀]
    have hp1nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) := by linarith
    have p2 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by
      nlinarith [mul_nonneg hp1nn (by linarith [hsqrt1] : (0 : ℝ) ≤ Real.sqrt f - 1)]
    have hp2nn : (0 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f := by linarith
    have p3 : (20 : ℝ) ≤ 5 * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f) := by
      nlinarith [mul_nonneg hp2nn (by linarith [hlog2] : (0 : ℝ) ≤ (1 + Real.log f) - 1)]
    rw [hM₀]; linarith [p3]
  obtain ⟨Z, m, h, hmemZ, hcount, hana_h, hne_h, hEqOn, hident⟩ :=
    LFunction_partialFraction χ hχ hf t₀
  refine ⟨Z, m, h, hmemZ, hana_h, hne_h, hEqOn, hident, ?_⟩
  intro hsup s hs hLs
  exact norm_logDeriv_sub_sum_of_blaschke hM₀1 hLc (fun ρ hρ => (hmemZ ρ hρ).1) hcount hana_h hne_h
    hEqOn hident hsup hs hLs

/-! ## 4. The real-part corollary (the S3 consumable) -/

/-- **The real-part transfer** S3 consumes. A norm bound `‖L'/L(s) − ∑_ρ m_ρ/(s−ρ)‖ ≤ B` yields
the one-sided real-part bound `(−L'/L(s)).re ≤ B − ∑_ρ m_ρ·Re(1/(s−ρ))` (taking real parts; the
zeros' `Re(1/(s−ρ))` terms are then discarded/kept by sign in the zero-free-region argument). -/
theorem neg_re_logDeriv_le {L : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {s : ℂ} {B : ℝ}
    (hbound : ‖logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ B) :
    (-(logDeriv L s)).re ≤ B - ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re := by
  set w : ℂ := logDeriv L s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) with hw
  have hre : -B ≤ w.re := by
    have h2 : |w.re| ≤ B := le_trans (Complex.abs_re_le_norm w) hbound
    linarith [abs_le.mp h2]
  have hsum_re : (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [show (m ρ : ℂ) / (s - ρ) = (m ρ : ℂ) * (1 / (s - ρ)) by ring, Complex.mul_re]
    simp [Complex.natCast_re, Complex.natCast_im]
  have hwre : w.re = (logDeriv L s).re - (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re := by
    rw [hw, Complex.sub_re]
  rw [hwre, hsum_re] at hre
  rw [Complex.neg_re]
  linarith

end Salt.SW

