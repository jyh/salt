/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszRepAsm

/-!
# HALASZ-INFRA — the `hfactor` inner factorization (`HalaszFactor`)

The scoper-executor file for the campaign's SOLE remaining residual: `hfactor`, the
hypothesis of `prop21_analog` (`Salt/MR/HalaszRepAsm.lean`).  `hfactor` re-expresses
the seam Dirichlet series contour `∫_t 𝒟(c₀+it)·hatKernel` as the `(α,β)` double
integral `prop21RHS` of the four-factor product `𝒮(s-α-β)·𝓛(s+β)·P(s-β)·P(s+β)`
against the centered hat kernel, up to the error `E`.

Source: GHS (`docs/sources/1706.03749v1.pdf`) Lemma 2.1 (p.8), Lemma 2.2 (p.8),
Lemmas 2.3–2.5 (pp.9–10), and the **Proof of Proposition 2.1** (p.11).

## THE R1 DISSOLUTION VERDICT (page-anchored) — PARTIAL

GHS's Prop 2.1 proof (p.11, verbatim): "begin with the identity in Lemma 2.2,
replacing the inner integral in (2.3) by (2.5); truncate obtaining the error in
Lemma 2.5; the terms in (2.4) are bounded by Lemma 2.4; finally replace β by 2β."

The `(α,β)` double integral **spine DOES dissolve** into landed rungs — the #255
pattern holds on the analytic skeleton:

* **β-FTC** (`∫₀^{2η} 𝓛'(s+α+β) dβ = 𝓛(s+α+2η) − 𝓛(s+α)`, GHS p.8) is exactly
  `shifted_dirichlet_ftc` at `g := restrictAbove y g` (its integrand
  `L(λ_lin g')·L(ℓ g') = −𝓛'` by `ellLin_lseries_deriv`).
* the Term-B algebra `(𝓛'/𝓛)(s+α)·𝓛(s+α) = 𝓛'(s+α)` (GHS p.8) is again
  `ellLin_lseries_deriv` (product form, no division), enabling the
* **α-FTC** (`∫₀^η 𝓛'(s+α) dα = 𝓛(s+η) − 𝓛(s)`) — again `shifted_dirichlet_ftc`.
* `𝒮·𝓛 = F` recombination is `lseries_ellLin_eq_smooth_mul_large` / `ellLin_split`.
* the outer contour→sum (Perron) is `hat_contour_rep` / `prop21_contour_leg`.
* **Lemma 2.5 (truncation error `O(x(log x)^κ/T)`) DISSOLVES**: the hat kernel is
  an EXACT full-line representation (K2'), so there is no `T`-truncation at all.

So the double integral is `shifted_dirichlet_ftc` applied ONCE PER VARIABLE plus
constant-prefactor pull-outs and the `𝒮/𝓛` split — all landed.  This file lands
`largeSeries_ftc_double_beta`, the concrete witness: the inner β-integral of the
`(α,β)` double integral collapses to the `𝓛` endpoint difference under the outer
α-integral, entirely from `shifted_dirichlet_ftc`.

## THE RESISTANCE (what does NOT dissolve) — the named analytic core

`hfactor` is **NOT** pure C-assembly.  Three cores resist re-application of landed
rungs, one of them genuinely:

1. **THE SHIU SECONDARY BOUND (Lemma 2.4 + Lemma 2.3, pp.9)** — the NAMED CORE,
   priced **C/D**.  The two extra terms of (2.4)
   (`∑_{mn≤x} s(m)ℓ(n)/n^η` and `∫₀^η ∑_{mkn≤x} s(m)Λ_ℓ(k)ℓ(n)…`) are bounded by
   GHS Lemma 2.4 via Shiu's Brun–Titchmarsh for the class `C(κ)` (Lemma 2.3,
   `≪ (z/φ(q))·(1/log x)·exp(∑|f(p)|/p)`).  The corpus has Shiu **only for τ**
   (`sum_tau_in_ap_le`: `∑τ(n) ≤ C(z/φ(q))·log z`, `shiu_moment_sq`) — which gives
   `log`-GROWTH, the WRONG DIRECTION: τ-domination loses the crucial `1/log`
   SAVING that Lemma 2.4's `x/log x` requires.  The general 1-bounded-multiplicative
   Brun–Titchmarsh is absent from mathlib and the corpus.  This is the genuine
   residual inside `hfactor`.
2. **THE WINDOW-TRUNCATION / TAILORING (§2.2, pp.9–10)** — priced **C**, but
   entangled with #1: replacing `𝓛'/𝓛(s+α) → −∑_{y<n<x/y}Λ_ℓ(n)n^{-(s+α)}`
   (the log-derivative is `ellLin_lseries_deriv`, LANDED; the support cut `y<n<x/y`
   from `abcd≤x` + large-prime support is a finite argument) — the truncation
   DEFECT is exactly the secondary terms of #1.
3. **THE CHANGE-OF-VARIABLES + CENTERING** — priced **B/C**, landable.  The
   symmetrizing substitution `c_{α,β}=c₀-α-β/2` + `β→2β` (GHS p.10) reaching the
   symmetric (2.1) shifts, and the `n^{-it₀}` centering (a full-line `t`-translation
   change-of-variables; the `twistCoeff`/`dpoly_shift` pattern of `HalaszCore` is
   the template but is `private` there).  `𝒮` and `P` are FINITE (entire) so the
   shifted evaluations `𝒮(s-α-β)` at `Re<1` are well-defined — this dissolves the
   REF-A F1 abscissa concern in the hat-kernel form (only `𝓛(s+β)`, `Re>1`, needs
   convergence, which `+β` preserves).

## RE-PRICE

`hfactor` = **C-ladder-with-one-named-C/D-core**.  The analytic spine (α,β double
integral collapse) is C-assembly of landed rungs (`#255` confirmed on the
skeleton).  The single genuine core is the **multiplicative-function Shiu /
Brun–Titchmarsh secondary bound** (GHS Lemma 2.4/2.3), absent from the corpus in
the required `1/log`-saving direction — the panel item.  Desmoothing is landed
(`prop21_desmooth_reduction`); truncation dissolves (exact hat kernel).
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## The spine witness — the β-collapse of the `(α,β)` double integral

`largeSeries_ftc_double_beta` is the concrete evidence for the R1 dissolution
verdict: the inner (β) integral of the `(α,β)` double integral collapses to the
`𝓛` (large-series) endpoint difference, uniformly under the outer α-integral,
purely from the landed `shifted_dirichlet_ftc` at the large datum `restrictAbove y g`
(whose integrand is `−𝓛'` by `ellLin_lseries_deriv`).  This is GHS's β-FTC step
(`∫₀^η 𝓛'(w+α+β) dβ = 𝓛(w+α) − 𝓛(w+α+η)`, p.8) exhibited inside the double
integral — the β-half of "`shifted_dirichlet_ftc` applied once per variable". -/

/-- **Spine witness (β-collapse).**  For the large series `𝓛 = largeSeries y g`
(`= LSeries (ellLin (restrictAbove y g))`), the inner β-integral of the `(α,β)`
double integral of `L(λ_lin (restrictAbove y g))(w+α+β)·𝓛(w+α+β)` collapses, under
the outer α-integral, to the α-integral of the `𝓛` endpoint difference
`𝓛(w+α) − 𝓛(w+α+η)`.  Direct consequence of `shifted_dirichlet_ftc` at the large
datum (base `w+α`), applied pointwise in α via `intervalIntegral.integral_congr`. -/
theorem largeSeries_ftc_double_beta (y : ℝ) (g : ℕ → ℂ)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) {η : ℝ} (hη : 0 ≤ η) :
    ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        LSeries (lambdaLin (restrictAbove y g)) ((w + (α : ℂ)) + (β : ℂ))
          * largeSeries y g ((w + (α : ℂ)) + (β : ℂ))
      = ∫ α in (0 : ℝ)..η,
          (largeSeries y g (w + (α : ℂ))
            - largeSeries y g ((w + (α : ℂ)) + (η : ℂ))) := by
  refine intervalIntegral.integral_congr (fun α hα => ?_)
  have hα0 : 0 ≤ α := by
    rcases Set.mem_uIcc.mp hα with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hwα : 1 < (w + (α : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have key := shifted_dirichlet_ftc (restrictAbove y g) (restrictAbove_norm_le hg) hwα hη
  simpa only [largeSeries] using key

end Salt.MR
