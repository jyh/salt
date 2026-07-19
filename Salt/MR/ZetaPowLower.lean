/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.GrowthPow
import Salt.Vk.PowRegion
import Salt.SW.ZetaLowerShallow

/-!
# MR-gate node S2 — `zeta_pow_lower` (POW-LOWER)  [COMPLETE — Blocks A + B green]

Target (the pow-grade region → ζ lower bound):
```
theorem zeta_pow_lower : ∃ c' T₁ : ℝ, 0 < c' ∧ 3 ≤ T₁ ∧
    ∀ (d' t : ℝ), 0 ≤ d' → d' ≤ 1 → T₁ ≤ |t| →
      c' / ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ))
        ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖
```
`L := log|t|`, `ℓ := loglog|t|`, region width `η := c·L^(-3/4)·ℓ^(-3)`
(`Salt.Vk.zeta_zero_free_region_pow`), cut `w := η/ℓ = c·L^(-3/4)·ℓ^(-4)`.

## STATUS
COMPLETE (MR-W2, 2026-07-18): `zeta_pow_lower` is proven sorry-free.  Block A
(`zeta_pow_lower_far` + keystones, wave 1) composes with Block B (this wave):
`near_norm_logDeriv_Zc_le` (the normalized scaled-Landau zero-counting core) →
`zeta_near_bound_core`/`zeta_near_logDeriv_bound` (the pow-region discharge,
honest `C_L = 400`) → `zeta_near_bridge` (the keystone-K FTC bridge) → assembly.
Realized constant `c' = e^{-400}·(1/10⁹)/32` at `T₁ = exp(exp(8·log(20000·K)+1100))
+ t₀ + 4`-grade; only the SHAPE `L^{3/4}ℓ⁴` is load-bearing downstream.

## The proof design (corrected: the dominant term is elementary, NOT the transport)

Split on `w := c·L^(-3/4)·ℓ^(-4)` (the region cut, matching the frozen `ℓ^4`):

* **Block A (`d' ≥ w`) — GREEN, `zeta_pow_lower_far`, unconditional.**  A pure
  monotonicity argument. Let `φ(v) := log‖ζ(v+it)‖ + log‖ζ(v)‖` on `[1+d', 2]`.
  Its derivative is `Re(ζ'/ζ)(v+it) + ζ'/ζ(v)`, and the Dirichlet bound
  `Re(ζ'/ζ)(v+it) ≤ -ζ'/ζ(v)` (`zeta_dirichlet_re_le`) makes `φ' ≤ 0`, so `φ` is
  antitone: `‖ζ(σ+it)‖ ≥ ‖ζ(2+it)‖·‖ζ(2)‖/‖ζ(σ)‖`. With the `Re ≥ 2` anchor
  (`zeta_norm_ge`, `≥ 1/4`) and the pole bound `‖ζ(σ)‖ ≤ 1+1/(σ-1)`
  (`zeta_real_upper`) this yields `‖ζ((1+d')+it)‖ ≥ d'/32`, hence `≥ w/32` when
  `d' ≥ w`. **This uses NO zero-free region, NO growth bound — just the Dirichlet
  series (`Re > 1`) and the pole.** It is the freeze's `log(1/w)` term, and it lives
  entirely on the real axis (the correction to the freeze's transport framing).

* **Block B (`d' < w`) — the remaining gap.**  Bridge from `d' = w` (where Block A
  gives the floor `w/32`) down to `d' ∈ [0, w)` at cost `O(1)`: it suffices to show
  `|log‖ζ((1+d')+it)‖ − log‖ζ((1+w)+it)‖| ≤ C` for a constant `C`, i.e.
  `∫_{1+d'}^{1+w} |Re(ζ'/ζ)(u+it)| du ≤ C`. On `[1, 1+w]` the naive Dirichlet bound
  `-ζ'/ζ(u) ~ 1/(u-1)` DIVERGES, so here — and ONLY here — the pow region enters:
  every zero has `Re ρ ≤ 1-η`, so `|Re(ζ'/ζ)(u+it)| ≤ Σ_ρ 1/η + V ≤ C_L·ℓ/η`
  (`V` the normalized-Landau numeric), and length `w = η/ℓ` gives `∫ ≤ C_L·ℓ/η·w =
  C_L = O(1)`.  This is the hard `~400–600` line zero-counting block; see below.

## Block B — the remaining sub-lemmas (exact statements + sources)

1. `zeta_near_re_logDeriv_abs_le` :  for `1 ≤ u ≤ 1+w`, `T₀ ≤ |t|`,
   `|Re(logDeriv ζ (u+it))| ≤ C_L·ℓ/η`.  Build from `entire_norm_logDeriv_sub_sum_scaled`
   (`Salt.Vk.Landau`) applied to the NORMALIZED `F = Zc/Zc(c)` (so `M₀` is the RATIO
   `sup‖Zc‖/‖Zc(c)‖`, giving `log(4M₀) ~ ℓ`, NOT `~ L`), plus `Σ_ρ m_ρ ≤ log(4M₀)/log(R/r)`
   (`entire_zero_count_le`, `ZetaPartialFractions`) and the per-zero `Re(1/(s-ρ)) ≤ 1/(u-Re ρ)
   ≤ 1/η` from `Salt.Vk.zeta_zero_free_region_pow` (`u ≥ 1 ≥ Re ρ + η`). THE hard block.
2. `zeta_near_bridge` :  `|log‖ζ((1+d')+it)‖ − log‖ζ((1+w)+it)‖| ≤ C_L`.  The FTC /
   monotone-modulus integral of (1) over `[1+d', 1+w]` (length `≤ w`) via
   `hasDerivAt_log_norm_zeta` (green, below) + `intervalIntegral.norm_integral_le_of_norm_le`.
3. `pow_cut_shape` + assembly :  `w = c·L^(-3/4)·ℓ^(-4)`, `T₁ := T₀+1`; combine Block A
   (`d' ≥ w`) and Block B (`d' < w`) into `zeta_pow_lower`.  rpow/log bookkeeping.

## Constant audit
Block A realizes `c' = 1/32` on the `d' ≥ w` half (unconditional). Block B's `C_L`
is `O(1)` (freeze design `≈ 7`; corpus-literal disc radii `≈ 30`), so the assembled
`c' = exp(−C_L)/32`-grade; shape `L^(3/4)·ℓ^4` intact. The loglog power `4 = 3
(region) + 1 (the `w = η/ℓ` cut)`.  The two green keystones (`zeta_dirichlet_re_le`,
`hasDerivAt_log_norm_zeta`) are the reusable analytic core BOTH blocks consume.
-/

namespace Salt.MR

open Complex ArithmeticFunction Metric Set MeromorphicOn Function Filter Salt.SW Salt.Vk
open scoped LSeries.notation

/-- **The far anchor.**  `‖ζ(2 + it)‖ ≥ 1/4`.  The fixed high-σ anchor of the
monotonicity argument (thin wrapper over `Salt.SW.zeta_norm_ge`, `Re(2+it) = 2 ≥ 2`). -/
lemma zeta_pow_anchor (t : ℝ) :
    (1 : ℝ) / 4 ≤ ‖riemannZeta ((2 : ℝ) + (t : ℝ) * Complex.I)‖ := by
  refine Salt.SW.zeta_norm_ge ?_
  simp

/-- **Region destructuring.**  `Salt.Vk.zeta_zero_free_region_pow`: a width `c > 0` and
threshold `T₀ ≥ 3` with every ζ-zero `ρ` of height `|Im ρ| ≥ T₀` obeying
`Re ρ ≤ 1 − c/((log|Im ρ|)^{3/4}·(loglog|Im ρ|)³)`.  Consumed by Block B sub-lemma 1
to get `u − Re ρ ≥ η` for `u ≥ 1`. -/
lemma pow_region_width :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
  Salt.Vk.zeta_zero_free_region_pow

/-- **KEYSTONE D (the Dirichlet real-part bound).**  For real `u > 1` and any `t`,
`Re(ζ'/ζ(u+it)) ≤ −ζ'/ζ(u)` (the real value).  From `ζ'/ζ(s) = −∑ Λ(n)n^(−s)`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`): `Re` of a convergent Dirichlet
series is `≤` its norm `≤` the same series at the real point `u`. -/
lemma zeta_dirichlet_re_le {u t : ℝ} (hu : 1 < u) :
    (logDeriv riemannZeta ((u:ℂ) + (t:ℂ) * I)).re ≤ -(logDeriv riemannZeta (u:ℂ)).re := by
  set s : ℂ := (u:ℂ) + (t:ℂ) * I with hs
  have hsre : s.re = u := by rw [hs]; simp
  have hsgt : (1:ℝ) < s.re := by rw [hsre]; exact hu
  have hugt : (1:ℝ) < ((u:ℂ)).re := by simpa using hu
  have key : ∀ w : ℂ, 1 < w.re → (logDeriv riemannZeta w).re = -(LSeries (↗Λ) w).re := by
    intro w hw
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw, logDeriv_apply, neg_div,
      Complex.neg_re, neg_neg]
  rw [key s hsgt, key (u:ℂ) hugt, neg_neg]
  have hsum_s : Summable (fun n => LSeries.term (↗Λ) s n) := LSeriesSummable_vonMangoldt hsgt
  have hsum_u : Summable (fun n => LSeries.term (↗Λ) (u:ℂ) n) := LSeriesSummable_vonMangoldt hugt
  have hnorm_eq : ∀ n, ‖LSeries.term (↗Λ) s n‖ = ‖LSeries.term (↗Λ) (u:ℂ) n‖ := by
    intro n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre, Complex.ofReal_re]
  have hterm_re : ∀ n, (LSeries.term (↗Λ) (u:ℂ) n).re = ‖LSeries.term (↗Λ) (u:ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : ((n:ℂ)) ^ (u:ℂ) = (((n:ℝ) ^ u : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
      change (((Λ n : ℝ):ℂ) / ((n:ℂ) ^ (u:ℂ))).re = ‖((Λ n:ℝ):ℂ) / ((n:ℂ) ^ (u:ℂ))‖
      have hnn : (0:ℝ) ≤ Λ n / (n:ℝ)^u := div_nonneg vonMangoldt_nonneg (by positivity)
      rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hnn]
  have hLu_re : (LSeries (↗Λ) (u:ℂ)).re = ∑' n, ‖LSeries.term (↗Λ) (u:ℂ) n‖ := by
    rw [LSeries, Complex.re_tsum hsum_u]; exact tsum_congr hterm_re
  have hLs_norm : ‖LSeries (↗Λ) s‖ ≤ ∑' n, ‖LSeries.term (↗Λ) (u:ℂ) n‖ := by
    rw [LSeries]
    calc ‖∑' n, LSeries.term (↗Λ) s n‖
        ≤ ∑' n, ‖LSeries.term (↗Λ) s n‖ := norm_tsum_le_tsum_norm hsum_s.norm
      _ = ∑' n, ‖LSeries.term (↗Λ) (u:ℂ) n‖ := tsum_congr hnorm_eq
  have hneg : -(LSeries (↗Λ) s).re ≤ ‖LSeries (↗Λ) s‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hLu_re]; linarith [hneg, hLs_norm]

/-- **KEYSTONE K (the log-modulus derivative).**  `d/dv log‖ζ(v+it)‖ = Re(ζ'/ζ(v+it))`,
built component-wise (via the real/imag parts) to sidestep the branch cut where `ζ` is
a negative real.  Valid wherever `ζ(v+it) ≠ 0` and `v+it ≠ 1`. -/
lemma hasDerivAt_log_norm_zeta {u t : ℝ}
    (hne : riemannZeta ((u : ℂ) + (t : ℂ) * I) ≠ 0) (hpt : (u : ℂ) + (t : ℂ) * I ≠ 1) :
    HasDerivAt (fun v : ℝ => Real.log ‖riemannZeta ((v:ℂ) + (t:ℂ) * I)‖)
      ((logDeriv riemannZeta ((u:ℂ) + (t:ℂ) * I)).re) u := by
  set s : ℂ := (u:ℂ) + (t:ℂ) * I with hs
  have he : HasDerivAt (fun v : ℝ => riemannZeta ((v:ℂ) + (t:ℂ) * I)) (deriv riemannZeta s) u := by
    have h1 : HasDerivAt (fun w : ℂ => w + (t:ℂ) * I) 1 (u:ℂ) := (hasDerivAt_id _).add_const _
    have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
      (differentiableAt_riemannZeta hpt).hasDerivAt
    have hE : HasDerivAt (fun w : ℂ => riemannZeta (w + (t:ℂ) * I)) (deriv riemannZeta s)
        (u:ℂ) := by
      have hcomp := h2.comp (u:ℂ) h1
      rw [mul_one] at hcomp
      exact hcomp
    exact hE.comp_ofReal
  have hre : HasDerivAt (fun v : ℝ => (riemannZeta ((v:ℂ) + (t:ℂ) * I)).re)
      ((deriv riemannZeta s).re) u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u he
  have him : HasDerivAt (fun v : ℝ => (riemannZeta ((v:ℂ) + (t:ℂ) * I)).im)
      ((deriv riemannZeta s).im) u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u he
  set g : ℝ → ℝ := fun v => (riemannZeta ((v:ℂ)+(t:ℂ)*I)).re * (riemannZeta ((v:ℂ)+(t:ℂ)*I)).re
    + (riemannZeta ((v:ℂ)+(t:ℂ)*I)).im * (riemannZeta ((v:ℂ)+(t:ℂ)*I)).im with hg
  have hgderiv : HasDerivAt g
      (((deriv riemannZeta s).re * (riemannZeta s).re
          + (riemannZeta s).re * (deriv riemannZeta s).re)
       + ((deriv riemannZeta s).im * (riemannZeta s).im
          + (riemannZeta s).im * (deriv riemannZeta s).im)) u :=
    (hre.mul hre).add (him.mul him)
  have hgu : g u = Complex.normSq (riemannZeta s) := by
    rw [hg, Complex.normSq_apply]
  have hgne : g u ≠ 0 := by rw [hgu]; exact (Complex.normSq_pos.mpr hne).ne'
  have hlogg : HasDerivAt (fun v => Real.log (g v)) _ u := hgderiv.log hgne
  have hhalf := hlogg.const_mul (1/2 : ℝ)
  have hfun : (fun v : ℝ => Real.log ‖riemannZeta ((v:ℂ)+(t:ℂ)*I)‖)
      = fun v => (1/2 : ℝ) * Real.log (g v) := by
    funext v
    have hnn : (0:ℝ) ≤ g v := by rw [hg]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have : ‖riemannZeta ((v:ℂ)+(t:ℂ)*I)‖ = Real.sqrt (g v) := by
      rw [hg, Complex.norm_def, Complex.normSq_apply]
    rw [this, Real.log_sqrt hnn]; ring
  rw [hfun]
  have hval : (logDeriv riemannZeta s).re = 1 / 2 *
      (((deriv riemannZeta s).re * (riemannZeta s).re
          + (riemannZeta s).re * (deriv riemannZeta s).re
        + ((deriv riemannZeta s).im * (riemannZeta s).im
           + (riemannZeta s).im * (deriv riemannZeta s).im)) / g u) := by
    rw [logDeriv_apply, Complex.div_re, hgu, Complex.normSq_apply]; field_simp; ring
  rw [hval]; exact hhalf

/-- **The horizontal monotone-modulus bound (Block A core).**  For `1 < u ≤ 2`,
`2 ≤ |t|`, the function `v ↦ log‖ζ(v+it)‖ + log‖ζ(v)‖` is antitone on `[u, 2]`
(derivative `≤ 0` by keystone D), giving
`log‖ζ(2+it)‖ + log‖ζ(2)‖ − log‖ζ(u)‖ ≤ log‖ζ(u+it)‖`. -/
lemma zeta_horiz_lower {u t : ℝ} (hu1 : 1 < u) (hu2 : u ≤ 2) (ht : 2 ≤ |t|) :
    Real.log ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ + Real.log ‖riemannZeta ((2:ℝ):ℂ)‖
      - Real.log ‖riemannZeta ((u:ℝ):ℂ)‖
      ≤ Real.log ‖riemannZeta ((u:ℝ) + (t:ℂ) * I)‖ := by
  set φ : ℝ → ℝ := fun v => Real.log ‖riemannZeta ((v:ℂ) + (t:ℂ) * I)‖
    + Real.log ‖riemannZeta ((v:ℂ))‖ with hφdef
  have hφ : ∀ v : ℝ, 1 < v → HasDerivAt φ
      ((logDeriv riemannZeta ((v:ℂ) + (t:ℂ) * I)).re + (logDeriv riemannZeta ((v:ℂ))).re) v := by
    intro v hv
    have hre_pt : ((v:ℂ) + (t:ℂ) * I).re = v := by simp
    have hzne1 : (v:ℂ) + (t:ℂ) * I ≠ 1 := by
      intro h
      have him : ((v:ℂ) + (t:ℂ) * I).im = (1:ℂ).im := by rw [h]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.one_im] at him
      norm_num at him; rw [him] at ht; norm_num at ht
    have hzne0 : riemannZeta ((v:ℂ) + (t:ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hre_pt]; linarith)
    have hvne1 : (v:ℂ) ≠ 1 := by
      intro h; rw [show (1:ℂ) = ((1:ℝ):ℂ) by norm_num] at h
      exact absurd (Complex.ofReal_injective h) (by linarith)
    have hvne0 : riemannZeta ((v:ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith)
    have hK1 := hasDerivAt_log_norm_zeta hzne0 hzne1
    have hK2 : HasDerivAt (fun v : ℝ => Real.log ‖riemannZeta ((v:ℂ))‖)
        ((logDeriv riemannZeta ((v:ℂ))).re) v := by
      have h0 := hasDerivAt_log_norm_zeta (t := 0) (u := v) (by simpa using hvne0)
        (by simpa using hvne1)
      simpa using h0
    exact hK1.add hK2
  have hcont : ContinuousOn φ (Set.Icc u 2) := fun v hv =>
    (hφ v (lt_of_lt_of_le hu1 hv.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc u 2)) := by
    rw [interior_Icc]; intro v hv
    exact (hφ v (lt_trans hu1 hv.1)).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ v ∈ interior (Set.Icc u 2), deriv φ v ≤ 0 := by
    rw [interior_Icc]; intro v hv
    have hv1 : 1 < v := lt_trans hu1 hv.1
    rw [(hφ v hv1).deriv]
    linarith [zeta_dirichlet_re_le (u := v) (t := t) hv1]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc u 2) hcont hdiff hnonpos
  have hres := hanti (Set.left_mem_Icc.mpr hu2) (Set.right_mem_Icc.mpr hu2) hu2
  simp only [hφdef] at hres
  linarith [hres]

/-- **Block A — `zeta_pow_lower_far`.**  Unconditional: for `0 < d' ≤ 1`, `2 ≤ |t|`,
`d'/32 ≤ ‖ζ((1+d')+it)‖`.  Exponentiate `zeta_horiz_lower` and feed the `Re ≥ 2`
anchor (`≥ 1/4`) and the pole bound `‖ζ(1+d')‖ ≤ 1+1/d'` (`zeta_real_upper`).
This closes the whole target on the `d' ≥ w` half (`w = c·L^(-3/4)·ℓ^(-4)`). -/
lemma zeta_pow_lower_far {d' t : ℝ} (hd0 : 0 < d') (hd1 : d' ≤ 1) (ht : 2 ≤ |t|) :
    (1/32 : ℝ) * d' ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖ := by
  show (1/32 : ℝ) * d' ≤ ‖riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)‖
  set u : ℝ := 1 + d' with hu
  have hu1 : 1 < u := by rw [hu]; linarith
  have hu2 : u ≤ 2 := by rw [hu]; linarith
  have hb : (1:ℝ)/4 ≤ ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ := Salt.SW.zeta_norm_ge (by simp)
  have hc : (1:ℝ)/4 ≤ ‖riemannZeta ((2:ℝ):ℂ)‖ := Salt.SW.zeta_norm_ge (by simp)
  have hdub : ‖riemannZeta ((u:ℝ):ℂ)‖ ≤ 1 + 1 / (u - 1) := Salt.SW.zeta_real_upper hu1
  have hbpos : 0 < ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ := by linarith
  have hcpos : 0 < ‖riemannZeta ((2:ℝ):ℂ)‖ := by linarith
  have hdpos : 0 < ‖riemannZeta ((u:ℝ):ℂ)‖ := by
    rw [norm_pos_iff]; exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith)
  have hapos : 0 < ‖riemannZeta ((u:ℝ) + (t:ℂ) * I)‖ := by
    rw [norm_pos_iff]
    refine riemannZeta_ne_zero_of_one_le_re ?_
    have : ((u:ℂ) + (t:ℂ) * I).re = u := by simp
    rw [this]; linarith
  have hlog := zeta_horiz_lower hu1 hu2 ht
  have hlogc : Real.log ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ + Real.log ‖riemannZeta ((2:ℝ):ℂ)‖
      - Real.log ‖riemannZeta ((u:ℝ):ℂ)‖
      = Real.log (‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ * ‖riemannZeta ((2:ℝ):ℂ)‖
        / ‖riemannZeta ((u:ℝ):ℂ)‖) := by
    rw [Real.log_div (by positivity) (ne_of_gt hdpos),
      Real.log_mul (ne_of_gt hbpos) (ne_of_gt hcpos)]
  rw [hlogc] at hlog
  have hquot : ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ * ‖riemannZeta ((2:ℝ):ℂ)‖
      / ‖riemannZeta ((u:ℝ):ℂ)‖ ≤ ‖riemannZeta ((u:ℝ) + (t:ℂ) * I)‖ := by
    rwa [Real.log_le_log_iff (by positivity) hapos] at hlog
  have hd_ub : ‖riemannZeta ((u:ℝ):ℂ)‖ ≤ 1 + 1 / d' := by
    have : u - 1 = d' := by rw [hu]; ring
    rwa [this] at hdub
  have hquot2 : (1/32 : ℝ) * d' ≤ ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ * ‖riemannZeta ((2:ℝ):ℂ)‖
      / ‖riemannZeta ((u:ℝ):ℂ)‖ := by
    rw [le_div_iff₀ hdpos]
    have hbc : (1/4 : ℝ) * (1/4) ≤ ‖riemannZeta ((2:ℝ) + (t:ℂ) * I)‖ * ‖riemannZeta ((2:ℝ):ℂ)‖ :=
      mul_le_mul hb hc (by norm_num) (by linarith)
    have hprod : d' * ‖riemannZeta ((u:ℝ):ℂ)‖ ≤ d' + 1 := by
      have h1 : d' * ‖riemannZeta ((u:ℝ):ℂ)‖ ≤ d' * (1 + 1 / d') :=
        mul_le_mul_of_nonneg_left hd_ub hd0.le
      have h2 : d' * (1 + 1 / d') = d' + 1 := by field_simp
      linarith [h1, h2]
    nlinarith [hbc, hprod, hd1]
  linarith [hquot, hquot2]

/-! ## Block B — the near-region zero-counting bridge (`d' < w`) -/

/-- **Block B core — the normalized scaled-Landau norm bound.**  At the near-1-line disc
`c₀ = (1+Θ/2)+iτ` (scale `λ = 6Θ/7`) run on the NORMALIZED `F = Zc/Zc(c₀)` (center value `1`,
so `M₀ = sup‖Zc/Zc(c₀)‖` is the RATIO — `log(4M₀) ~ ℓ`, not `~ L`): the scaled Landau numeric
(`entire_norm_logDeriv_sub_sum_scaled`) + the Blaschke count (`entire_zero_count_le`, ratio `7/6`)
+ a min-distance hypothesis `hdist` (`w ≤ ‖s−ρ‖` for every disc-zero, supplied by the pow region)
give `‖logDeriv Zc s‖ ≤ (120/λ)·log(4M₀) + (log(4M₀)/log(7/6))/w`.  The normalized analog of
`Salt.SW.norm_logDeriv_Zc_le_of_ball_dist`, riding the scaled core. -/
lemma near_norm_logDeriv_Zc_le {Θ M₀ w τ : ℝ} {s : ℂ}
    (hΘ0 : 0 < Θ) (hM₀ : 1 ≤ M₀) (hw : 0 < w)
    (hsc : ‖s - (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 23 / 20 * (6 * Θ / 7))
    (hZcs : Zc s ≠ 0)
    (hsphere74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hdist : ∀ ρ : ℂ, Zc ρ = 0 →
        ρ ∈ ball (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (3 / 2 * (6 * Θ / 7)) → w ≤ ‖s - ρ‖) :
    ‖logDeriv Zc s‖ ≤ (120 / (6 * Θ / 7)) * Real.log (4 * M₀)
        + (Real.log (4 * M₀) / Real.log (7 / 6)) / w := by
  classical
  set lam : ℝ := 6 * Θ / 7 with hlam
  set c₀ : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc₀
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hcre : c₀.re = 1 + Θ / 2 := by rw [hc₀]; simp
  have hcne : c₀ ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; nlinarith [hΘ0]
  have hζc : riemannZeta c₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; nlinarith [hΘ0])
  have hZcc0 : Zc c₀ ≠ 0 := by rw [Zc_eq_of_ne hcne]; exact mul_ne_zero (sub_ne_zero.mpr hcne) hζc
  have hG_diff : Differentiable ℂ (fun z => Zc z / Zc c₀) :=
    fun z => (Zc_differentiable z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖Zc c₀ / Zc c₀‖ := by rw [div_self hZcc0, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => Zc w / Zc c₀) z = logDeriv Zc z := by
    intro z
    have hGeq : (fun w => Zc w / Zc c₀) = fun w => (Zc c₀)⁻¹ * Zc w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (Zc c₀)⁻¹ (inv_ne_zero hZcc0)]
  obtain ⟨Z, m, hh, hmemb, hana_h, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  have hGs0 : Zc s / Zc c₀ ≠ 0 := div_ne_zero hZcs hZcc0
  have hnum' := hnum s hsc hGs0
  rw [hLDG s] at hnum'
  -- the Blaschke count `∑_{ρ∈Z} m_ρ ≤ log(4M₀)/log(7/6)`
  have hana_univ : AnalyticOnNhd ℂ (fun z => Zc z / Zc c₀) univ :=
    hG_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hana32 : AnalyticOnNhd ℂ (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) :=
    hana_univ.mono (subset_univ _)
  have hana_cb : AnalyticOnNhd ℂ (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam)) :=
    hana_univ.mono (subset_univ _)
  have hloc : ∀ ρ ∈ Z, (divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam))) ρ = (m ρ : ℤ) := by
    intro ρ hρ
    have hρball := (hmemb ρ hρ).1
    have horder : analyticOrderAt (fun z => Zc z / Zc c₀) ρ = (m ρ : ℕ∞) :=
      analyticOrderAt_eq_of_factorization hana_h hne_h hEqOn hρ hρball
    rw [hana32.divisor_apply hρball, horder]; simp
  have hsupp : (Function.support
      (fun u => divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u)) ⊆ ↑Z := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    have hρball : ρ ∈ ball c₀ (3 / 2 * lam) := by
      by_contra hn
      exact hρ (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hn)
    have hρ0 : (fun z => Zc z / Zc c₀) ρ = 0 := by
      by_contra hne0
      apply hρ
      rw [hana32.divisor_apply hρball, (hana32 ρ hρball).analyticOrderAt_eq_zero.mpr hne0]; simp
    exact (mem_zeros_of_factorization_gen hne_h hEqOn hρball hρ0).1
  have hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ Real.log (4 * M₀) / Real.log (7 / 6) := by
    have e1 : (∑ ρ ∈ Z, (m ρ : ℤ))
        = ∑ ρ ∈ Z, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) ρ := by
      apply Finset.sum_congr rfl; intro ρ hρ; rw [hloc ρ hρ]
    have e2 : (∑ ρ ∈ Z, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) ρ)
        = ∑ᶠ u, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u :=
      (finsum_eq_finsetSum_of_support_subset _ hsupp).symm
    have hdle : ∀ u : ℂ, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u
        ≤ divisor (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam)) u := by
      intro u
      by_cases hu : u ∈ ball c₀ (3 / 2 * lam)
      · exact le_of_eq
          (by rw [hana32.divisor_apply hu, hana_cb.divisor_apply (ball_subset_closedBall hu)])
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
        exact hana_cb.divisor_nonneg u
    have hfin_ball : (Function.support
        (fun u => divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u)).Finite :=
      divisor_ball_support_finite hana_cb.meromorphicOn
    have hfin_cb : (Function.support
        (fun u => divisor (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam)) u)).Finite :=
      (divisor (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam))).finiteSupport
        (isCompact_closedBall _ _)
    have hmono : ∑ᶠ u, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u
        ≤ ∑ᶠ u, divisor (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam)) u :=
      finsum_le_finsum' hfin_ball hfin_cb hdle
    have hcountJ := entire_zero_count_le hG_diff hGc_floor (r := 3 / 2 * lam)
      (R := 7 / 4 * lam) (M := M₀) (by linarith [hlam0]) (by linarith [hlam0]) hM₀ hsphere74
    calc (∑ ρ ∈ Z, (m ρ : ℝ))
        = ((∑ ρ ∈ Z, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((∑ᶠ u, divisor (fun z => Zc z / Zc c₀) (ball c₀ (3 / 2 * lam)) u : ℤ) : ℝ) := by
          rw [e1, e2]
      _ ≤ ((∑ᶠ u, divisor (fun z => Zc z / Zc c₀) (closedBall c₀ (3 / 2 * lam)) u : ℤ) : ℝ) := by
          exact_mod_cast hmono
      _ ≤ Real.log (4 * M₀) / Real.log (7 / 4 * lam / (3 / 2 * lam)) := hcountJ
      _ = Real.log (4 * M₀) / Real.log (7 / 6) := by
          rw [show (7 : ℝ) / 4 * lam / (3 / 2 * lam) = 7 / 6 by
            rw [mul_div_mul_right _ _ (ne_of_gt hlam0)]; norm_num]
  -- the min-distance sum bound `‖∑ m_ρ/(s−ρ)‖ ≤ (∑ m_ρ)/w`
  have hdist' : ∀ ρ ∈ Z, w ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have h1 := hmemb ρ hρ
    have hZcρ : Zc ρ = 0 := by
      have hFρ : Zc ρ / Zc c₀ = 0 := h1.2
      exact (div_eq_zero_iff.mp hFρ).resolve_right hZcc0
    exact hdist ρ hZcρ h1.1
  have hSumNorm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / w := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist' ρ hρ
          have hdpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hw hd
          rw [div_le_div_iff₀ hdpos hw]
          nlinarith [Nat.cast_nonneg (α := ℝ) (m ρ), hd]
      _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by rw [Finset.sum_div]
  have h76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hcount' : (∑ ρ ∈ Z, (m ρ : ℝ)) / w ≤ (Real.log (4 * M₀) / Real.log (7 / 6)) / w := by
    rw [div_le_div_iff_of_pos_right hw]; exact hcount
  have hsplit : ‖logDeriv Zc s‖
      ≤ ‖logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by
    calc ‖logDeriv Zc s‖
        = ‖(logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hlamval : (120 : ℝ) / lam = 120 / (6 * Θ / 7) := by rw [hlam]
  calc ‖logDeriv Zc s‖
      ≤ (120 / lam) * Real.log (4 * M₀) + (∑ ρ ∈ Z, (m ρ : ℝ)) / w := by
        linarith [hsplit, hnum', hSumNorm]
    _ ≤ (120 / (6 * Θ / 7)) * Real.log (4 * M₀)
          + (Real.log (4 * M₀) / Real.log (7 / 6)) / w := by rw [← hlamval]; linarith [hcount']

private lemma pow_height_facts {A x : ℝ} (hA : 1100 ≤ A)
    (hx : Real.exp (Real.exp A) ≤ x) :
    3 ≤ Real.log x ∧ A ≤ Real.log (Real.log x) := by
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  have hlogE : Real.log (Real.exp (Real.exp A)) = Real.exp A := Real.log_exp _
  have hlogx : Real.exp A ≤ Real.log x := by rw [← hlogE]; exact Real.log_le_log hEpos hx
  have hexp2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hexpA3 : (3:ℝ) ≤ Real.exp A := le_trans hexp2 (Real.exp_le_exp.mpr (by linarith [hA]))
  refine ⟨le_trans hexpA3 hlogx, ?_⟩
  calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
    _ ≤ Real.log (Real.log x) := Real.log_le_log (Real.exp_pos A) hlogx

set_option maxHeartbeats 12800000 in
-- The core threads the whole normalized-Landau discharge + the width numerics through one
-- ~200-line declaration; the default budget dies in the closing arithmetic.
/-- The positive-height core of `zeta_near_logDeriv_bound`: at height `γ` above the (astronomically
lazy) threshold, `‖logDeriv ζ(v+iγ)‖ ≤ 400·(log γ)^{3/4}(loglog γ)^4/(1/10⁹)` for `v` in the near
strip.  Rides `near_norm_logDeriv_Zc_le`; the min-distance comes from `zeta_zero_free_pow_core`. -/
private lemma zeta_near_bound_core {K t₀K : ℝ} (hK : 1 ≤ K) (ht₀K : 3 ≤ t₀K)
    (hg : ∀ σ t : ℝ, t₀K ≤ t → 1 - vkTheta t ≤ σ → σ ≤ 3 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * Real.log t)
    (γ v : ℝ)
    (hγ : Real.exp (Real.exp (8 * Real.log (20000 * K) + 1100)) + t₀K + 3 ≤ γ)
    (hv1 : 1 ≤ v)
    (hcut : v ≤ 1 + (1 / 10 ^ 9) / ((Real.log γ) ^ ((3:ℝ)/4) * (Real.log (Real.log γ)) ^ (4:ℕ))) :
    ‖logDeriv riemannZeta ((v:ℂ) + (γ:ℂ) * Complex.I)‖
      ≤ 400 * ((Real.log γ) ^ ((3:ℝ)/4) * (Real.log (Real.log γ)) ^ (4:ℕ)) / (1 / 10 ^ 9) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0:ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  -- height thresholds (raw, pre-set)
  have hγim : Real.exp (Real.exp A) + t₀K + 3 ≤ γ := hγ
  have hσimE : Real.exp (Real.exp A) ≤ γ := by linarith [ht₀K, hγim]
  have hγpos : 0 < γ := lt_of_lt_of_le hEpos hσimE
  have hγ2 : (2:ℝ) ≤ γ := by linarith [hEpos, ht₀K, hγim]
  have hexpA1 : 1 < Real.exp A := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith [hA1100])
  have hEe : Real.exp 1 < Real.exp (Real.exp A) := Real.exp_lt_exp.mpr hexpA1
  have hγe : Real.exp 1 < γ - 1 := by linarith [hEe, hγim, ht₀K, hEpos]
  have hγt₀ : t₀K ≤ γ - 1 := by linarith [hEpos, hγim]
  have hfactsγ := pow_height_facts hA1100 hσimE
  -- abbreviations
  set Lg : ℝ := Real.log γ with hLdef
  set ℓ : ℝ := Real.log Lg with hℓdef
  have hL3 : (3:ℝ) ≤ Lg := hfactsγ.1
  have hℓA : A ≤ ℓ := hfactsγ.2
  have hℓ1100 : (1100:ℝ) ≤ ℓ := le_trans hA1100 hℓA
  have hL0 : 0 < Lg := by linarith [hL3]
  have hℓ0 : 0 < ℓ := by linarith [hℓ1100]
  -- log 3γ facts
  set L3 : ℝ := Real.log (3 * γ) with hL3def
  have hlog3le2 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)]
  have hL3eq : L3 = Real.log 3 + Lg := by rw [hL3def, Real.log_mul (by norm_num) hγpos.ne']
  have hL3lb : Lg ≤ L3 := by rw [hL3eq]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hL3ub : L3 ≤ 2 * Lg := by rw [hL3eq]; linarith [hlog3le2, hL3]
  have hL30 : 0 < L3 := by linarith [hL3lb, hL0]
  set ℓ3 : ℝ := Real.log L3 with hℓ3def
  have hℓ3lb : ℓ ≤ ℓ3 := by rw [hℓ3def, hℓdef]; exact Real.log_le_log hL0 hL3lb
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  have hℓ3ub : ℓ3 ≤ 2 * ℓ := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne', ← hℓdef]
      _ ≤ 2 * ℓ := by linarith [hlog2le1, hℓ1100]
  have hℓ3tight : ℓ3 ≤ ℓ + 1 := by
    rw [hℓ3def]
    calc Real.log L3 ≤ Real.log (2 * Lg) := Real.log_le_log hL30 hL3ub
      _ = Real.log 2 + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne', ← hℓdef]
      _ ≤ ℓ + 1 := by linarith [hlog2le1]
  have hℓ30 : 0 < ℓ3 := by linarith [hℓ3lb, hℓ0]
  have hℓ31100 : (1100:ℝ) ≤ ℓ3 := by linarith [hℓ3lb, hℓ1100]
  -- region parameters
  set Θ : ℝ := vkTheta (3 * γ) with hΘdef
  set Pinv : ℝ := 1000 * L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ) with hPinvdef
  have hL34pos : 0 < L3 ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos hL30 _
  have hPinvpos : 0 < Pinv := by rw [hPinvdef]; positivity
  have hΘval : Θ = 1 / 1000 / (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by
    rw [hΘdef, vkTheta, ← hL3def, ← hℓ3def]
  have hΘPinv : Θ = 1 / Pinv := by
    rw [eq_div_iff (ne_of_gt hPinvpos), hΘval, hPinvdef]
    field_simp [ne_of_gt hL34pos, ne_of_gt hℓ30]
  have hΘ0 : 0 < Θ := by rw [hΘPinv]; positivity
  set Mζ : ℝ := K * L3 with hMζdef
  have hMζpos : 0 < Mζ := by rw [hMζdef]; positivity
  have hMζ1 : (1:ℝ) ≤ Mζ := by rw [hMζdef]; nlinarith [hK, hL3lb, hL3]
  have hPinv2 : (2:ℝ) ≤ Pinv := by
    rw [hPinvdef]
    have h1 : (1:ℝ) ≤ L3 ^ ((3:ℝ)/4) := Real.one_le_rpow (by linarith [hL3lb, hL3]) (by norm_num)
    have h2 : (1:ℝ) ≤ ℓ3 ^ (2:ℕ) := one_le_pow₀ (by linarith [hℓ31100])
    nlinarith [h1, h2]
  have hΘ12 : Θ ≤ 1 / 2 := by
    rw [hΘPinv]; rw [div_le_div_iff₀ hPinvpos (by norm_num)]; linarith [hPinv2]
  -- box growth
  have hgrowth : ∀ z : ℂ, 1 - Θ ≤ z.re → z.re ≤ 2 → γ - 1 ≤ z.im → z.im ≤ 3 * γ →
      ‖riemannZeta z‖ ≤ Mζ := by
    intro z h1 h2 h3 h4
    rw [hΘdef] at h1; rw [hMζdef]
    exact pow_uniform_growth hK ht₀K hg hγe hγt₀ z h1 h2 h3 h4
  -- W and its bound
  set W : ℝ := Real.log (20 * Pinv * Mζ) with hWdef
  have hWeq : W = Real.log (20000 * K) + (7 / 4) * ℓ3 + 2 * Real.log ℓ3 := by
    have hPinvne : Pinv ≠ 0 := ne_of_gt hPinvpos
    have hL3ne : L3 ≠ 0 := ne_of_gt hL30
    have hℓ3ne : ℓ3 ≠ 0 := ne_of_gt hℓ30
    have h20000 : Real.log (20000 * K) = Real.log 20 + Real.log 1000 + Real.log K := by
      rw [show (20000:ℝ) * K = 20 * 1000 * K by ring, Real.log_mul (by norm_num) hKpos.ne',
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hWdef, Real.log_mul (by positivity) (ne_of_gt hMζpos),
      Real.log_mul (by norm_num) hPinvne, hMζdef, Real.log_mul hKpos.ne' hL3ne,
      hPinvdef, Real.log_mul (by positivity) (pow_ne_zero 2 hℓ3ne),
      Real.log_mul (by norm_num) (ne_of_gt hL34pos), Real.log_rpow hL30, Real.log_pow,
      ← hℓ3def, h20000]
    push_cast; ring
  have hlog20K : Real.log (20000 * K) ≤ ℓ / 8 := by rw [hAdef] at hℓA; linarith
  have hlogℓ3le : Real.log ℓ3 ≤ ℓ3 := by linarith [Real.log_le_sub_one_of_pos hℓ30]
  have hWub : W ≤ 8 * ℓ := by
    rw [hWeq]; linarith [hlog20K, hℓ3ub, hlogℓ3le]
  have hW0 : 0 ≤ W := by
    rw [hWdef]; apply Real.log_nonneg
    nlinarith [hPinv2, hMζ1, hMζpos, hPinvpos]
  -- Pinv width bound
  have hL34le : L3 ^ ((3:ℝ)/4) ≤ 2 * Lg ^ ((3:ℝ)/4) := by
    have h1 : L3 ^ ((3:ℝ)/4) ≤ (2 * Lg) ^ ((3:ℝ)/4) := Real.rpow_le_rpow hL30.le hL3ub (by norm_num)
    have h2 : (2 * Lg) ^ ((3:ℝ)/4) = 2 ^ ((3:ℝ)/4) * Lg ^ ((3:ℝ)/4) :=
      Real.mul_rpow (by norm_num) hL0.le
    have h3 : (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 := by
      calc (2:ℝ) ^ ((3:ℝ)/4) ≤ (2:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hL34nn : 0 ≤ Lg ^ ((3:ℝ)/4) := Real.rpow_nonneg hL0.le _
    rw [h2] at h1; nlinarith [h1, h3, hL34nn]
  have hℓ3sqle : ℓ3 ^ (2:ℕ) ≤ 4 * ℓ ^ (2:ℕ) := by
    have := pow_le_pow_left₀ hℓ30.le hℓ3ub 2
    calc ℓ3 ^ (2:ℕ) ≤ (2 * ℓ) ^ (2:ℕ) := this
      _ = 4 * ℓ ^ (2:ℕ) := by ring
  have hPinvle : Pinv ≤ 8000 * (Lg ^ ((3:ℝ)/4) * ℓ ^ (2:ℕ)) := by
    have hℓ3nn : (0:ℝ) ≤ ℓ3 ^ (2:ℕ) := by positivity
    have hprod := mul_le_mul hL34le hℓ3sqle hℓ3nn (by positivity : (0:ℝ) ≤ 2 * Lg ^ ((3:ℝ)/4))
    calc Pinv = 1000 * (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (2:ℕ)) := by rw [hPinvdef]; ring
      _ ≤ 1000 * ((2 * Lg ^ ((3:ℝ)/4)) * (4 * ℓ ^ (2:ℕ))) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8000 * (Lg ^ ((3:ℝ)/4) * ℓ ^ (2:ℕ)) := by ring
  -- name the frozen scale factor
  set P : ℝ := Lg ^ ((3:ℝ)/4) with hPdef
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hP1 : (1:ℝ) ≤ P := Real.one_le_rpow (by linarith [hL3]) (by norm_num)
  -- the point
  set s : ℂ := (v:ℂ) + (γ:ℂ) * Complex.I with hsdef
  have hγ1 : (1:ℝ) ≤ |γ| := by rw [abs_of_nonneg hγpos.le]; linarith [hγ2]
  -- sphere discharge (mirror of RegionGrowth's `discharge`, height γ)
  have hsph : ∀ R : ℝ, 0 ≤ R → R ≤ 3 / 2 * Θ →
      ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R,
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 5 * Mζ / Θ := by
    intro R hR0 hR z hz
    have hzc : ‖z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ = R := by
      rw [← dist_eq_norm, ← mem_sphere]; exact hz
    have hcre : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).re = 1 + Θ / 2 := by simp
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have hreb : |z.re - (1 + Θ / 2)| ≤ R := by
      have h := Complex.abs_re_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_re, hcre, hzc] at h; exact h
    have himb : |z.im - γ| ≤ R := by
      have h := Complex.abs_im_le_norm (z - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim, hzc] at h; exact h
    have hre1 : 1 - Θ ≤ z.re := by have := (abs_le.mp hreb).1; nlinarith [hR, hΘ12]
    have hre2 : z.re ≤ 2 := by have := (abs_le.mp hreb).2; nlinarith [hR, hΘ12]
    have him1 : γ - 1 ≤ z.im := by have := (abs_le.mp himb).1; nlinarith [hR, hΘ12]
    have him2 : z.im ≤ 3 * γ := by have := (abs_le.mp himb).2; nlinarith [hR, hΘ12, hγ2]
    exact Zc_ratio_sphere_bound hΘ0 hΘ12 hγ1 hMζ1 hR0 hR hz (hgrowth z hre1 hre2 him1 him2)
  have hR74 : (7:ℝ) / 4 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hR32 : (3:ℝ) / 2 * (6 * Θ / 7) ≤ 3 / 2 * Θ := by nlinarith [hΘ0]
  have hsphere74 := hsph (7 / 4 * (6 * Θ / 7)) (by positivity) hR74
  have hsphere32 := hsph (3 / 2 * (6 * Θ / 7)) (by positivity) hR32
  have hM₀1 : (1:ℝ) ≤ 5 * Mζ / Θ := by rw [le_div_iff₀ hΘ0]; nlinarith [hMζ1, hΘ12, hΘ0]
  -- cut ≤ Θ/2 and the centering bound
  have hcut_le : (1 / 10 ^ 9) / (P * ℓ ^ (4:ℕ)) ≤ Θ / 2 := by
    have hℓ24 : ℓ ^ (2:ℕ) ≤ ℓ ^ (4:ℕ) := pow_le_pow_right₀ (by linarith [hℓ1100]) (by norm_num)
    have hkey : P * ℓ ^ (2:ℕ) ≤ P * ℓ ^ (4:ℕ) := mul_le_mul_of_nonneg_left hℓ24 hP0.le
    have hstep2 : 1 / (16000 * (P * ℓ ^ (2:ℕ))) ≤ Θ / 2 := by
      rw [hΘPinv, div_div]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hPinvle])
    refine le_trans ?_ hstep2
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith [hkey, mul_pos hP0 (pow_pos hℓ0 4)])
  have hsc : ‖s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 23 / 20 * (6 * Θ / 7) := by
    have hsub : s - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        = ((v - (1 + Θ / 2) : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    refine ⟨by nlinarith [hv1, hΘ0], by nlinarith [hcut, hcut_le, hΘ0]⟩
  have hs1 : s ≠ 1 := by
    rw [hsdef]; intro h
    have := congrArg Complex.im h; simp at this; linarith [hγ2, this]
  have hζs : riemannZeta s ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    have hvre : ((v:ℂ) + (γ:ℂ) * Complex.I).re = v := by simp
    rw [hsdef, hvre]; exact hv1
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) hζs
  -- the min-distance
  set w : ℝ := (1 / 10 ^ 9) / (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ)) with hwdef
  have hw0 : 0 < w := by
    rw [hwdef]; apply div_pos (by norm_num)
    exact mul_pos (Real.rpow_pos_of_pos hL30 _) (pow_pos hℓ30 3)
  have hdist : ∀ ρ : ℂ, Zc ρ = 0 →
      ρ ∈ ball (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (3 / 2 * (6 * Θ / 7)) →
        w ≤ ‖s - ρ‖ := by
    intro ρ hZcρ hρball
    rw [mem_ball, dist_eq_norm] at hρball
    have hcim : (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    have himb : |ρ.im - γ| ≤ 3 / 2 * (6 * Θ / 7) := by
      have h := Complex.abs_im_le_norm (ρ - (((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      rw [Complex.sub_im, hcim] at h; linarith [h, hρball]
    have hrad : 3 / 2 * (6 * Θ / 7) ≤ 9 / 14 := by nlinarith [hΘ12, hΘ0]
    have hρim_lb : γ - 1 ≤ ρ.im := by have := (abs_le.mp himb).1; linarith [hrad]
    have hρim_ub : ρ.im ≤ 3 * γ := by have := (abs_le.mp himb).2; linarith [hrad, hγ2]
    have hρimpos : 0 < ρ.im := by linarith [hρim_lb, hγ2]
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρimpos; simp at hρimpos
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hZcρ
      exact (mul_eq_zero.mp hZcρ).resolve_left (sub_ne_zero.mpr hρ1)
    have hρre1 : ρ.re < 1 := by
      by_contra hc; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hζρ
    have hργe : Real.exp 1 < ρ.im - 1 := by linarith [hγe, hρim_lb]
    have hργt₀ : t₀K ≤ ρ.im - 1 := by linarith [hγt₀, hρim_lb]
    have hρE : Real.exp (Real.exp A) ≤ ρ.im := by linarith [hγim, hρim_lb, ht₀K]
    have hfactsρ := pow_height_facts hA1100 hρE
    have hρL3 : (3:ℝ) ≤ Real.log ρ.im := hfactsρ.1
    have hρℓK : 8 * Real.log (20000 * K) + 1100 ≤ Real.log (Real.log ρ.im) := by
      have h := hfactsρ.2; rw [hAdef] at h; exact h
    have hcore_ρ := zeta_zero_free_pow_core hK ht₀K hg hζρ hρre1
      (by linarith [hρim_lb, hγ2] : (2:ℝ) ≤ ρ.im) hργe hργt₀ hρL3 hρℓK
    -- denominator monotonicity: ρ.im ≤ 3γ
    have hlogρpos : 0 < Real.log ρ.im := by linarith [hρL3]
    have hlogρ_le : Real.log ρ.im ≤ L3 := by rw [hL3def]; exact Real.log_le_log hρimpos hρim_ub
    have hloglogρ_le : Real.log (Real.log ρ.im) ≤ ℓ3 := by
      rw [hℓ3def]; exact Real.log_le_log hlogρpos hlogρ_le
    have hloglogρnn : 0 ≤ Real.log (Real.log ρ.im) := Real.log_nonneg (by linarith [hρL3])
    have hden_mono : (Real.log ρ.im) ^ ((3:ℝ)/4) * (Real.log (Real.log ρ.im)) ^ (3:ℕ)
        ≤ L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ) :=
      mul_le_mul (Real.rpow_le_rpow hlogρpos.le hlogρ_le (by norm_num))
        (pow_le_pow_left₀ hloglogρnn hloglogρ_le 3) (by positivity)
        (Real.rpow_nonneg hL30.le _)
    have hρden_pos : 0 < (Real.log ρ.im) ^ ((3:ℝ)/4) * (Real.log (Real.log ρ.im)) ^ (3:ℕ) := by
      apply mul_pos (Real.rpow_pos_of_pos hlogρpos _)
      apply pow_pos; linarith [hρℓK, Real.log_nonneg (show (1:ℝ) ≤ 20000 * K by nlinarith [hK])]
    have hwidth_ρ : w ≤ 1 - ρ.re := by
      have hrw : (1 / 10 ^ 9) * (1 / ((Real.log ρ.im) ^ ((3:ℝ)/4)
          * (Real.log (Real.log ρ.im)) ^ (3:ℕ))) ≤ 1 - ρ.re := by linarith [hcore_ρ]
      rw [hwdef]
      refine le_trans ?_ hrw
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) hρden_pos hden_mono
    have hsre : s.re = v := by rw [hsdef]; simp
    have hdist_re : w ≤ s.re - ρ.re := by rw [hsre]; linarith [hwidth_ρ, hv1]
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re] at h
    linarith [h, le_abs_self (s.re - ρ.re), hdist_re]
  -- run the near-region lemma
  have hnear := near_norm_logDeriv_Zc_le hΘ0 hM₀1 hw0 hsc hZcs hsphere74 hsphere32 hdist
  have h140 : (120:ℝ) / (6 * Θ / 7) = 140 * Pinv := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have h4M : (4:ℝ) * (5 * Mζ / Θ) = 20 * Pinv * Mζ := by
    rw [hΘPinv]; field_simp [ne_of_gt hPinvpos]; ring
  have hlog4M : Real.log (4 * (5 * Mζ / Θ)) = W := by rw [h4M]
  rw [h140, hlog4M] at hnear
  -- convert to ζ
  have hpole : logDeriv riemannZeta s = logDeriv Zc s - 1 / (s - 1) := logDeriv_zeta_eq hs1 hζs
  have hpole_norm : ‖(1:ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hsm1 : (1:ℝ) ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = γ := by rw [hsdef]; simp
      rw [him, abs_of_nonneg hγpos.le] at h; linarith [hγ2, h]
    rw [div_le_one (by linarith [hsm1])]; exact hsm1
  have hLDζ : ‖logDeriv riemannZeta s‖ ≤ 140 * Pinv * W + (W / Real.log (7/6)) / w + 1 := by
    rw [hpole]
    calc ‖logDeriv Zc s - 1 / (s - 1)‖ ≤ ‖logDeriv Zc s‖ + ‖(1:ℂ) / (s - 1)‖ := norm_sub_le _ _
      _ ≤ (140 * Pinv * W + (W / Real.log (7/6)) / w) + 1 := by linarith [hnear, hpole_norm]
  -- final numeric bound
  have h76pos : 0 < Real.log (7/6) := Real.log_pos (by norm_num)
  have h76ge : (1:ℝ) / 7 ≤ Real.log (7/6) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6/7 by norm_num)
    rw [show (6:ℝ)/7 = (7/6)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hDpos : 0 < P * ℓ ^ (4:ℕ) := by positivity
  have hD1 : (1:ℝ) ≤ P * ℓ ^ (4:ℕ) := by
    have h2 : (1:ℝ) ≤ ℓ ^ (4:ℕ) := one_le_pow₀ (by linarith [hℓ1100])
    nlinarith [hP1, h2]
  have hcRpos : (0:ℝ) < 1 / 10 ^ 9 := by norm_num
  have hT3 : (1:ℝ) ≤ (P * ℓ ^ (4:ℕ)) / (1 / 10 ^ 9) := by
    rw [le_div_iff₀ hcRpos]; nlinarith [hD1]
  have hT1 : 140 * Pinv * W ≤ (P * ℓ ^ (4:ℕ)) / (1 / 10 ^ 9) := by
    rw [le_div_iff₀ hcRpos]
    have hPW : Pinv * W ≤ 64000 * (P * ℓ ^ (3:ℕ)) := by
      have h := mul_le_mul hPinvle hWub hW0 (by positivity)
      calc Pinv * W ≤ (8000 * (P * ℓ ^ (2:ℕ))) * (8 * ℓ) := h
        _ = 64000 * (P * ℓ ^ (3:ℕ)) := by ring
    have hPl3pos : 0 < P * ℓ ^ (3:ℕ) := mul_pos hP0 (pow_pos hℓ0 3)
    have h1 : 140 * (Pinv * W) ≤ 140 * (64000 * (P * ℓ ^ (3:ℕ))) :=
      mul_le_mul_of_nonneg_left hPW (by norm_num)
    calc 140 * Pinv * W * (1 / 10 ^ 9)
        = (140 * (Pinv * W)) * (1 / 10 ^ 9) := by ring
      _ ≤ (140 * (64000 * (P * ℓ ^ (3:ℕ)))) * (1 / 10 ^ 9) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = (8960000 / 1000000000) * (P * ℓ ^ (3:ℕ)) := by ring
      _ ≤ 1100 * (P * ℓ ^ (3:ℕ)) :=
          mul_le_mul_of_nonneg_right (by norm_num) hPl3pos.le
      _ ≤ ℓ * (P * ℓ ^ (3:ℕ)) := mul_le_mul_of_nonneg_right hℓ1100 hPl3pos.le
      _ = P * ℓ ^ (4:ℕ) := by ring
  have hℓ3cube : ℓ3 ^ (3:ℕ) ≤ 2 * ℓ ^ (3:ℕ) := by
    have h1 : ℓ3 ^ (3:ℕ) ≤ (ℓ + 1) ^ (3:ℕ) := pow_le_pow_left₀ hℓ30.le hℓ3tight 3
    have h2 : (ℓ + 1) ^ (3:ℕ) ≤ 2 * ℓ ^ (3:ℕ) := by
      nlinarith [mul_nonneg (by linarith [hℓ1100] : (0:ℝ) ≤ ℓ - 1100) (sq_nonneg ℓ),
        mul_nonneg (by linarith [hℓ1100] : (0:ℝ) ≤ ℓ - 1100) hℓ0.le, hℓ1100]
    linarith [h1, h2]
  have hdenom3 : L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ) ≤ 4 * (P * ℓ ^ (3:ℕ)) := by
    have h := mul_le_mul hL34le hℓ3cube (by positivity) (by positivity)
    calc L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ) ≤ (2 * P) * (2 * ℓ ^ (3:ℕ)) := h
      _ = 4 * (P * ℓ ^ (3:ℕ)) := by ring
  have hWlog : W / Real.log (7/6) ≤ 56 * ℓ := by
    rw [div_le_iff₀ h76pos]
    nlinarith [hWub, mul_nonneg hℓ0.le (sub_nonneg.mpr h76ge)]
  have hnum : (W / Real.log (7/6)) * (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ)) ≤ 398 * (P * ℓ ^ (4:ℕ)) := by
    have hd3nn : 0 ≤ L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ) :=
      mul_nonneg (Real.rpow_nonneg hL30.le _) (pow_nonneg hℓ30.le 3)
    calc (W / Real.log (7/6)) * (L3 ^ ((3:ℝ)/4) * ℓ3 ^ (3:ℕ))
        ≤ (56 * ℓ) * (4 * (P * ℓ ^ (3:ℕ))) :=
          mul_le_mul hWlog hdenom3 hd3nn (by positivity)
      _ = 224 * (P * ℓ ^ (4:ℕ)) := by ring
      _ ≤ 398 * (P * ℓ ^ (4:ℕ)) := by nlinarith [hDpos]
  have hT2 : (W / Real.log (7/6)) / w ≤ 398 * ((P * ℓ ^ (4:ℕ)) / (1 / 10 ^ 9)) := by
    rw [hwdef, div_div_eq_mul_div, ← mul_div_assoc]
    gcongr
  -- combine
  rw [show (400:ℝ) * (P * ℓ ^ (4:ℕ)) / (1 / 10 ^ 9) = 400 * ((P * ℓ ^ (4:ℕ)) / (1 / 10 ^ 9)) from by
    rw [mul_div_assoc]]
  linarith [hLDζ, hT1, hT2, hT3]

/-- **Block B — the near-region logDeriv bound (discharge).**  For `|t| ≥ T₀` and `u` in the
near strip `[1, 1+w]` with cut `w = cR/((log|t|)^{3/4}(loglog|t|)^4)`, the ζ log-derivative is
bounded by `C_L/w`, i.e. `‖logDeriv ζ(u+it)‖ ≤ C_L·(log|t|)^{3/4}(loglog|t|)^4/cR`.  Rides
`near_norm_logDeriv_Zc_le` on the pow-region disc (scale `Θ = vkTheta(3|t|)`); `cR = 1/10⁹` the
region width constant.  Records the honest `C_L = 400`. -/
lemma zeta_near_logDeriv_bound :
    ∃ cR T₀ : ℝ, 0 < cR ∧ cR ≤ 1 ∧ 3 ≤ T₀ ∧
      (∀ t : ℝ, T₀ ≤ |t| → 1 ≤ Real.log (Real.log |t|)) ∧
      ∀ t u : ℝ, T₀ ≤ |t| → 1 ≤ u →
        u ≤ 1 + cR / ((Real.log |t|) ^ ((3:ℝ)/4) * (Real.log (Real.log |t|)) ^ (4:ℕ)) →
        ‖logDeriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ 400 * ((Real.log |t|) ^ ((3:ℝ)/4) * (Real.log (Real.log |t|)) ^ (4:ℕ)) / cR := by
  obtain ⟨K, t₀K, hK, ht₀K, hg⟩ := Salt.Vk.zeta_growth_pow
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set A : ℝ := 8 * Real.log (20000 * K) + 1100 with hAdef
  have hA1100 : 1100 ≤ A := by
    have : (0:ℝ) ≤ Real.log (20000 * K) := Real.log_nonneg (by nlinarith [hK])
    rw [hAdef]; linarith
  have hEpos : 0 < Real.exp (Real.exp A) := Real.exp_pos _
  set T₀ : ℝ := Real.exp (Real.exp A) + t₀K + 4 with hT₀def
  have hT₀3 : (3:ℝ) ≤ T₀ := by rw [hT₀def]; linarith [hEpos, ht₀K]
  refine ⟨1 / 10 ^ 9, T₀, by norm_num, by norm_num, hT₀3, ?_, ?_⟩
  · intro t ht
    have hx : Real.exp (Real.exp A) ≤ |t| :=
      le_trans (by rw [hT₀def]; linarith [ht₀K]) ht
    linarith [le_trans hA1100 (pow_height_facts hA1100 hx).2]
  · intro t u ht hu1 hu2
    have hLDconj : ∀ w : ℂ, w ≠ 1 →
        ‖logDeriv riemannZeta ((starRingEnd ℂ) w)‖ = ‖logDeriv riemannZeta w‖ := by
      intro w hw
      have hcw : (starRingEnd ℂ) w ≠ 1 := by
        intro h; apply hw
        have := congrArg (starRingEnd ℂ) h; rwa [Complex.conj_conj, map_one] at this
      have hderiv : deriv riemannZeta ((starRingEnd ℂ) w)
          = (starRingEnd ℂ) (deriv riemannZeta w) := by
        have hw' : HasDerivAt riemannZeta (deriv riemannZeta w) w :=
          (differentiableAt_riemannZeta hw).hasDerivAt
        have href := hw'.conj_conj
        have hEq : (⇑(starRingEnd ℂ) ∘ riemannZeta ∘ ⇑(starRingEnd ℂ))
            =ᶠ[nhds ((starRingEnd ℂ) w)] riemannZeta := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hcw] with z hz
          simp only [Function.comp_apply]
          rw [riemannZeta_conj (show z ≠ 1 from hz), Complex.conj_conj]
        exact (hEq.hasDerivAt_iff.mp href).deriv
      have hζcw : riemannZeta ((starRingEnd ℂ) w) = (starRingEnd ℂ) (riemannZeta w) :=
        riemannZeta_conj hw
      rw [logDeriv_apply, logDeriv_apply, hderiv, hζcw, ← map_div₀, Complex.norm_conj]
    have hγ' : Real.exp (Real.exp A) + t₀K + 3 ≤ |t| := by rw [hT₀def] at ht; linarith [ht₀K]
    have hbound := zeta_near_bound_core hK ht₀K hg |t| u hγ' hu1 hu2
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0] at hbound ⊢; exact hbound
    · have ht0' : t < 0 := not_le.mp ht0
      rw [abs_of_neg ht0'] at hbound ⊢
      set w₀ : ℂ := (u:ℂ) + (t:ℂ) * Complex.I with hw₀def
      have hw₀1 : w₀ ≠ 1 := by
        rw [hw₀def]; intro h
        have := congrArg Complex.im h; simp at this; linarith [ht0']
      have hconj_pt : (u:ℂ) + ((-t : ℝ):ℂ) * Complex.I = (starRingEnd ℂ) w₀ := by
        rw [hw₀def]
        simp only [Complex.ofReal_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [hconj_pt, hLDconj w₀ hw₀1] at hbound
      exact hbound

/-- **Block B — the FTC bridge.**  Integrating keystone K (`hasDerivAt_log_norm_zeta`) over the
segment `[a,b]` at height `t` (`|t| ≥ 3`, `a ≥ 1`): given a uniform bound `Bnd` on
`‖logDeriv ζ(v+it)‖` on `[a,b]`, `log‖ζ(b+it)‖ − log‖ζ(a+it)‖ ≤ (b−a)·Bnd`. -/
lemma zeta_near_bridge {t a b Bnd : ℝ} (hab : a ≤ b) (h1a : 1 ≤ a) (ht : 3 ≤ |t|)
    (hnear : ∀ v : ℝ, a ≤ v → v ≤ b →
        ‖logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ ≤ Bnd) :
    Real.log ‖riemannZeta ((b : ℝ) + (t : ℂ) * I)‖
        - Real.log ‖riemannZeta ((a : ℝ) + (t : ℂ) * I)‖ ≤ (b - a) * Bnd := by
  have htne : (t : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hzne0 : ∀ v : ℝ, v ∈ uIcc a b → riemannZeta ((v : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact riemannZeta_ne_zero_of_one_le_re (by simp only [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; nlinarith [hv.1, h1a])
  have hzne1 : ∀ v : ℝ, ((v : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro v h
    have him : ((v : ℂ) + (t : ℂ) * I).im = (1 : ℂ).im := by rw [h]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.one_im] at him
    norm_num at him
    exact htne him
  have hpt : ∀ v : ℝ, v ∈ uIcc a b →
      HasDerivAt (fun w : ℝ => Real.log ‖riemannZeta ((w : ℂ) + (t : ℂ) * I)‖)
        ((logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re) v :=
    fun v hv => hasDerivAt_log_norm_zeta (hzne0 v hv) (hzne1 v)
  -- continuity of the derivative for integrability
  have hUopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hζdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hζana : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := hζdiff.analyticOnNhd hUopen
  have hline : Continuous (fun v : ℝ => (v : ℂ) + (t : ℂ) * I) := by fun_prop
  have hmaps : ∀ v : ℝ, ((v : ℂ) + (t : ℂ) * I) ∈ {s : ℂ | s ≠ 1} := fun v => hzne1 v
  have hdc : ContinuousOn (fun v : ℝ => deriv riemannZeta ((v : ℂ) + (t : ℂ) * I)) (uIcc a b) :=
    (hζana.deriv.continuousOn).comp hline.continuousOn (fun v _ => hmaps v)
  have hζc : ContinuousOn (fun v : ℝ => riemannZeta ((v : ℂ) + (t : ℂ) * I)) (uIcc a b) :=
    (hζana.continuousOn).comp hline.continuousOn (fun v _ => hmaps v)
  have hcontD : ContinuousOn (fun v : ℝ => (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re)
      (uIcc a b) := by
    have hLD : ContinuousOn (fun v : ℝ => logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I))
        (uIcc a b) := by
      simp only [logDeriv_apply]
      exact hdc.div hζc (fun v hv => hzne0 v hv)
    exact Complex.continuous_re.comp_continuousOn hLD
  have hint : IntervalIntegrable
      (fun v : ℝ => (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re) MeasureTheory.volume a b :=
    hcontD.intervalIntegrable
  have hFTC : ∫ v in a..b, (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re
      = Real.log ‖riemannZeta ((b : ℝ) + (t : ℂ) * I)‖
        - Real.log ‖riemannZeta ((a : ℝ) + (t : ℂ) * I)‖ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hpt hint
  have hbnd : ∀ v ∈ Icc a b, (logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)).re ≤ Bnd := by
    intro v hv
    exact le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (hnear v hv.1 hv.2)
  have hmono := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hbnd
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [← hFTC]; exact hmono

/-- **S2 — `zeta_pow_lower` (POW-LOWER).**  Block A (`d' ≥ w`, unconditional `d'/32`) composed
with Block B (`d' < w`, the near bridge at cost `≤ 400`), `w = cR·L^{-3/4}ℓ^{-4}` the region cut.
`c' = e^{-400}·cR/32` (honest crude `C_L = 400`; tight design ≈ 7).  Statement-identical to the
`hpow` slot of `Salt.MR.zeta_lower_all_t_of_pow`. -/
theorem zeta_pow_lower : ∃ c' T₁ : ℝ, 0 < c' ∧ 3 ≤ T₁ ∧
    ∀ (d' t : ℝ), 0 ≤ d' → d' ≤ 1 → T₁ ≤ |t| →
      c' / ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ))
        ≤ ‖riemannZeta ((1 + d' : ℝ) + (t : ℝ) * Complex.I)‖ := by
  obtain ⟨cR, T₀, hcR0, hcR1, hT₀3, hℓ1, hnear⟩ := zeta_near_logDeriv_bound
  refine ⟨Real.exp (-400) * (cR / 32), T₀, by positivity, hT₀3, ?_⟩
  intro d' t hd0 hd1 hT
  have habs3 : (3 : ℝ) ≤ |t| := le_trans hT₀3 hT
  have hexp1lt3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hLpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hL1 : (1 : ℝ) < Real.log |t| := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp1lt3
      _ ≤ Real.log |t| := Real.log_le_log (by norm_num) habs3
  have hℓ1' : (1 : ℝ) ≤ Real.log (Real.log |t|) := hℓ1 t hT
  have hℓpos : (0 : ℝ) < Real.log (Real.log |t|) := lt_of_lt_of_le one_pos hℓ1'
  set D : ℝ := (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ) with hDdef
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hDrpow1 : (1 : ℝ) ≤ (Real.log |t|) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow hL1.le (by norm_num)
  have hDpow1 : (1 : ℝ) ≤ (Real.log (Real.log |t|)) ^ (4 : ℕ) := one_le_pow₀ hℓ1'
  have hD1 : (1 : ℝ) ≤ D := by rw [hDdef]; nlinarith [hDrpow1, hDpow1]
  set w : ℝ := cR / D with hwdef
  have hw0 : 0 < w := div_pos hcR0 hD0
  have hw1 : w ≤ 1 := le_trans (div_le_self hcR0.le hD1) hcR1
  have he400 : Real.exp (-400) ≤ 1 := by
    have := Real.exp_monotone (show (-400 : ℝ) ≤ 0 by norm_num)
    rwa [Real.exp_zero] at this
  have he400pos : 0 < Real.exp (-400) := Real.exp_pos _
  rcases le_or_gt w d' with hle | hlt
  · -- FAR case `d' ≥ w` : Block A
    have hd0' : 0 < d' := lt_of_lt_of_le hw0 hle
    have hfar := zeta_pow_lower_far hd0' hd1 (by linarith [habs3] : 2 ≤ |t|)
    have hstep : Real.exp (-400) * (cR / 32) / D ≤ (1 / 32) * d' := by
      have hc'D : Real.exp (-400) * (cR / 32) / D = Real.exp (-400) * w / 32 := by
        rw [hwdef]; ring
      rw [hc'D]
      have h1 : Real.exp (-400) * w / 32 ≤ w / 32 := by nlinarith [he400, hw0.le]
      linarith [h1, hle]
    exact le_trans hstep hfar
  · -- NEAR case `d' < w` : the bridge from `1+d'` up to `1+w`
    have hfarW := zeta_pow_lower_far hw0 hw1 (by linarith [habs3] : 2 ≤ |t|)
    have hnear' : ∀ v : ℝ, (1 + d') ≤ v → v ≤ (1 + w) →
        ‖logDeriv riemannZeta ((v : ℂ) + (t : ℂ) * I)‖ ≤ 400 * D / cR := by
      intro v hv1 hv2
      have hv1' : 1 ≤ v := by linarith [hd0]
      have hv2' : v ≤ 1 + cR / D := by rw [hwdef] at hv2; exact hv2
      have hb := hnear t v hT hv1' (by rw [← hDdef]; exact hv2')
      rwa [← hDdef] at hb
    have hbridge := zeta_near_bridge (t := t) (a := 1 + d') (b := 1 + w) (Bnd := 400 * D / cR)
      (by linarith [hlt]) (by linarith [hd0]) habs3 hnear'
    have hlen : ((1 + w) - (1 + d')) * (400 * D / cR) ≤ 400 := by
      have hwB : w * (400 * D / cR) = 400 := by
        rw [hwdef]; field_simp
      have hmul : ((1 + w) - (1 + d')) * (400 * D / cR) ≤ w * (400 * D / cR) :=
        mul_le_mul_of_nonneg_right (by linarith [hd0]) (by positivity)
      linarith [hmul, hwB]
    have hbr2 : Real.log ‖riemannZeta ((1 + w : ℝ) + (t : ℂ) * I)‖
        - Real.log ‖riemannZeta ((1 + d' : ℝ) + (t : ℂ) * I)‖ ≤ 400 := le_trans hbridge hlen
    have hζDpos : 0 < ‖riemannZeta ((1 + d' : ℝ) + (t : ℂ) * I)‖ := by
      rw [norm_pos_iff]
      exact riemannZeta_ne_zero_of_one_le_re (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im]; nlinarith [hd0])
    have hwlog : Real.log ((1 / 32) * w) ≤ Real.log ‖riemannZeta ((1 + w : ℝ) + (t : ℂ) * I)‖ :=
      Real.log_le_log (by positivity) hfarW
    have hgoalpos : 0 < Real.exp (-400) * (cR / 32) / D := by positivity
    have hc'eq : Real.log (Real.exp (-400) * (cR / 32) / D)
        = Real.log ((1 / 32) * w) - 400 := by
      rw [hwdef,
        show Real.exp (-400) * (cR / 32) / D = Real.exp (-400) * ((1 / 32) * (cR / D)) by ring,
        Real.log_mul (ne_of_gt he400pos) (by positivity), Real.log_exp]
      ring
    have hloggoal : Real.log (Real.exp (-400) * (cR / 32) / D)
        ≤ Real.log ‖riemannZeta ((1 + d' : ℝ) + (t : ℂ) * I)‖ := by
      rw [hc'eq]; linarith [hwlog, hbr2]
    have := (Real.log_le_log_iff hgoalpos hζDpos).mp hloggoal
    exact this

end Salt.MR
