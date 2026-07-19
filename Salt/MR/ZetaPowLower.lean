/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.GrowthPow
import Salt.SW.ZetaLowerShallow

/-!
# MR-gate wave 1, node S2 — `zeta_pow_lower` (POW-LOWER)  [PARTIAL / Block A green]

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
`zeta_pow_lower` itself is NOT yet proven (no `sorry`; it is simply omitted). What
IS proven, sorry-free and unconditionally, is **Block A** — the dominant `d' ≥ w`
half of the whole argument — plus its two analytic keystones. The remaining gap is
**Block B**, the `d' < w` near-region `O(1)` bridge, decomposed precisely below.

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

open Complex ArithmeticFunction
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

end Salt.MR
