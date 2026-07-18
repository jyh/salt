/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Landau
import Salt.SW.ZetaZeroFree
import Salt.SW.MobiusRateClose

/-!
# VMVT-VK rungs R8/R9 — the ζ-disc 3-4-1 chain and the power / Littlewood zero-free regions

This module hosts the shared assembly machinery for the power zero-free region
(`zeta_zero_free_region_pow`, θ = 3/4) and its Zeno sibling the Littlewood region.  Both consume
the same 3-4-1 keep-one chain at a parametric radius through `entire_norm_logDeriv_sub_sum_scaled`
(R7); they differ only in the growth input feeding the sphere bound.

Opening piece: the freeze `[G]` **negative-γ conjugation shim** `riemannZeta_conj`.  The growth
statements are for `t ≥ t₀ > 0`, but ζ-zeros carry either `Im` sign; `ζ(conj s) = conj(ζ s)`
reflects the negative-γ discs onto the positive-γ growth bound.  No `riemannZeta_conj` exists in
mathlib, so it is built here from the punctured-plane identity theorem.
-/

namespace Salt.Vk

open Complex Metric Set
open scoped Topology

/-! ## The negative-γ conjugation shim (freeze `[G]` graft) -/

/-- **ζ conjugation** (`[G]` neg-γ shim).  `ζ(conj s) = conj(ζ s)` for `s ≠ 1`.

Both `ζ` and `z ↦ conj(ζ(conj z))` are analytic on the punctured plane `{1}ᶜ` and agree on the
half-plane `Re s > 1` (the Dirichlet coefficients `1/nˢ` are real, so `conj` commutes through the
series via `Complex.conj_tsum`); the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) extends the agreement to all of `{1}ᶜ`. -/
lemma riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  -- `conj` preserves the punctured plane `{1}ᶜ`
  have hconj_ne : ∀ {z : ℂ}, z ≠ 1 → (starRingEnd ℂ) z ≠ 1 := by
    intro z hz h
    exact hz (by have := congrArg (starRingEnd ℂ) h; rwa [Complex.conj_conj, map_one] at this)
  -- `F z = conj(ζ(conj z))` is differentiable, hence analytic, on `{1}ᶜ`
  have hFdiff : DifferentiableOn ℂ
      (fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z))) {1}ᶜ := by
    intro z hz
    have hz1 : z ≠ 1 := hz
    have h1 : DifferentiableAt ℂ riemannZeta ((starRingEnd ℂ) z) :=
      differentiableAt_riemannZeta (hconj_ne hz1)
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hana_F : AnalyticOnNhd ℂ
      (fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z))) {1}ᶜ :=
    hFdiff.analyticOnNhd isOpen_compl_singleton
  have hana_L : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := analyticOn_riemannZeta
  -- agreement on the series half-plane `Re s > 1`
  have hser : ∀ z : ℂ, 1 < z.re →
      (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) = riemannZeta z := by
    intro z hz
    have hzc : 1 < ((starRingEnd ℂ) z).re := by rwa [Complex.conj_re]
    rw [zeta_eq_tsum_one_div_nat_cpow hzc, zeta_eq_tsum_one_div_nat_cpow hz, Complex.conj_tsum]
    refine tsum_congr (fun n => ?_)
    rw [map_div₀, map_one]
    congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
    rw [Complex.cpow_conj _ _ harg, Complex.conj_conj, map_natCast]
  -- frequently-eq at the reference point `2 ∈ {1}ᶜ`
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) = riemannZeta z := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
    have hgt : ∀ᶠ z in 𝓝 (2 : ℂ),
        (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) = riemannZeta z := by
      filter_upwards [hopen1.mem_nhds h2'] with z hz using hser z hz
    exact (hgt.filter_mono nhdsWithin_le_nhds).frequently
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]; norm_num
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have heqOn := hana_F.eqOn_of_preconnected_of_frequently_eq hana_L hpre h2mem hfreq
  have hFs : (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s)) = riemannZeta s :=
    heqOn (by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hs)
  have hconj := congrArg (starRingEnd ℂ) hFs
  rwa [Complex.conj_conj] at hconj

/-- Zeros of `ζ` come in conjugate pairs (the reflection of the neg-γ shim). -/
lemma riemannZeta_conj_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0) :
    riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
  rw [riemannZeta_conj hρ1, hρ, map_zero]

/-! ## The growth-to-sphere adapter (growth-agnostic, feeds the disc lemmas) -/

open Salt.SW in
/-- **Growth-to-sphere adapter.**  On the disc `c = (1+Θ/2)+iτ` (radius `R ≤ (3/2)Θ`,
`Θ ≤ 1/2`, `|τ| ≥ 1`), a pointwise growth bound `‖ζ z‖ ≤ Mζ` on the sphere yields the normalized
bound `‖Zc z/Zc c‖ ≤ 5 Mζ/Θ` fed to `zeta_keep_one_disc`/`zeta_drop_all_disc`.

The `‖z−1‖ ≈ ‖c−1‖ ≈ |τ|` factor cancels in the ratio; the center floor
`‖ζ c‖ ≥ (Θ/2)/(1+Θ/2)` comes from the landed Dirichlet-series inverse bound
`Salt.SW.norm_zeta_inv_cline_le` (`‖ζ⁻¹‖ ≤ 1+1/(σ−1)`) — no Euler-product audit needed. -/
lemma Zc_ratio_sphere_bound {Θ τ Mζ R : ℝ} (hΘ0 : 0 < Θ) (hΘ12 : Θ ≤ 1 / 2) (hτ : 1 ≤ |τ|)
    (hMζ : 1 ≤ Mζ) (hR0 : 0 ≤ R) (hR : R ≤ 3 / 2 * Θ)
    {z : ℂ} (hz : z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R)
    (hζz : ‖riemannZeta z‖ ≤ Mζ) :
    ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ 5 * Mζ / Θ := by
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc
  rw [mem_sphere, dist_eq_norm] at hz
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hcne : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; nlinarith [hΘ0]
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; nlinarith [hΘ0])
  -- `‖c − 1‖ ≥ |τ| ≥ 1`
  have hc1im : (c - 1).im = τ := by
    rw [hc]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re]
  have hn1 : (1 : ℝ) ≤ ‖c - 1‖ := by
    have h := Complex.abs_im_le_norm (c - 1); rw [hc1im] at h; linarith [hτ]
  -- `z ≠ 1` (since `‖z − 1‖ ≥ ‖c − 1‖ − R ≥ 1 − (3/2)Θ ≥ 1/4`)
  have hz1lb : (1 : ℝ) / 4 ≤ ‖z - 1‖ := by
    have htri : ‖c - 1‖ ≤ ‖z - 1‖ + ‖z - c‖ := by
      calc ‖c - 1‖ = ‖(z - 1) - (z - c)‖ := by ring_nf
        _ ≤ ‖z - 1‖ + ‖z - c‖ := norm_sub_le _ _
    rw [hz] at htri; nlinarith [htri, hn1, hR, hΘ12]
  have hzne1 : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hz1lb; linarith
  -- numerator: `‖Zc z‖ ≤ (R + ‖c−1‖)·Mζ`
  have hznum : ‖Zc z‖ ≤ (R + ‖c - 1‖) * Mζ := by
    rw [Zc_eq_of_ne hzne1, norm_mul]
    have hz1 : ‖z - 1‖ ≤ R + ‖c - 1‖ := by
      calc ‖z - 1‖ = ‖(z - c) + (c - 1)‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c - 1‖ := norm_add_le _ _
        _ = R + ‖c - 1‖ := by rw [hz]
    exact mul_le_mul hz1 hζz (norm_nonneg _) (by positivity)
  -- denominator: `‖Zc c‖ = ‖c−1‖·‖ζ c‖`, and `(Θ+2)·‖ζ c‖ ≥ Θ`
  have hζcpos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hζc
  have hLc : Θ ≤ (Θ + 2) * ‖riemannZeta c‖ := by
    have hinv := norm_zeta_inv_cline_le (σ := 1 + Θ / 2) (by linarith [hΘ0]) τ
    rw [show ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I = c from rfl, norm_inv,
      show (1 + Θ / 2 : ℝ) - 1 = Θ / 2 from by ring] at hinv
    -- hinv : ‖ζ c‖⁻¹ ≤ 1 + 1/(Θ/2)
    have h1 : ‖riemannZeta c‖⁻¹ * Θ ≤ Θ + 2 := by
      have hm := mul_le_mul_of_nonneg_right hinv hΘ0.le
      have he : (1 + 1 / (Θ / 2)) * Θ = Θ + 2 := by field_simp
      rwa [he] at hm
    have hmul := mul_le_mul_of_nonneg_right h1 hζcpos.le
    rwa [mul_comm ‖riemannZeta c‖⁻¹ Θ, mul_assoc, inv_mul_cancel₀ hζcpos.ne', mul_one] at hmul
  have hZccpos : 0 < ‖Zc c‖ := by
    rw [Zc_eq_of_ne hcne, norm_mul]
    exact mul_pos (lt_of_lt_of_le one_pos hn1) hζcpos
  -- assemble the ratio bound
  rw [norm_div, div_le_div_iff₀ hZccpos hΘ0]
  have hZcc_eq : ‖Zc c‖ = ‖c - 1‖ * ‖riemannZeta c‖ := by rw [Zc_eq_of_ne hcne, norm_mul]
  set n : ℝ := ‖c - 1‖ with hndef
  set L : ℝ := ‖riemannZeta c‖ with hLdef
  rw [hZcc_eq]
  -- `‖Zc z‖·Θ ≤ 5 Mζ·(n·L)`
  have hkey : (R + n) * Mζ * Θ ≤ 5 * Mζ * (n * L) := by
    have hstep : (R + n) * Θ ≤ 5 * (n * L) := by
      have hLmul : Θ * n ≤ (Θ + 2) * (n * L) := by nlinarith [hLc, lt_of_lt_of_le one_pos hn1]
      nlinarith [hLmul, hR, hΘ12, hΘ0, lt_of_lt_of_le one_pos hn1, hR0]
    nlinarith [mul_le_mul_of_nonneg_left hstep (by linarith [hMζ] : (0 : ℝ) ≤ Mζ)]
  calc ‖Zc z‖ * Θ ≤ (R + n) * Mζ * Θ := by
        apply mul_le_mul_of_nonneg_right _ hΘ0.le; rw [hndef]; exact hznum
    _ ≤ 5 * Mζ * (n * L) := hkey

/-! ## R8 core — the keep-one ζ log-derivative bound at a near-1-line disc -/

open Salt.SW in
/-- **R8 keep-one at a near-1-line disc.**  At the disc `c = (1+Θ/2) + iγ` (`γ = Im ρ`, radius
`λ = 6Θ/7`), the normalized function `G = Zc/(Zc c)` has center value `1` and satisfies the
scaled Borel–Carathéodory bound (R7 `entire_norm_logDeriv_sub_sum_scaled`).  If the zero `ρ`
lies inside the ball (`Re ρ > 1 − (11/14)Θ`) then it is retained, giving
`Re(−ζ'/ζ(σ+iγ)) ≤ Re(1/(s−1)) + (120/λ)·log(4 M₀) − 1/(σ − Re ρ)`.

The `|γ|`-factor of `Zc = (s−1)ζ` cancels in the ratio `G`, so `log(4 M₀)` is `O(log log t)`-grade
(not `O(log t)`), which is what widens the region.  The sphere bounds on `G` are hypotheses,
discharged per region from the growth input (`zeta_strip_family` / `zeta_growth_pow`). -/
theorem zeta_keep_one_disc {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hβ1 : ρ.re < 1)
    {Θ σ M₀ : ℝ} (hΘ0 : 0 < Θ) (hM₀ : 1 ≤ M₀) (hσlo : 1 < σ)
    (hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ) (hρnear : 1 - 11 / 14 * Θ < ρ.re)
    (hsphere74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀) :
    (-logDeriv riemannZeta ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + (ρ.im : ℂ) * I) - 1)).re
        + (120 / (6 * Θ / 7)) * Real.log (4 * M₀) - 1 / (σ - ρ.re) := by
  set γ : ℝ := ρ.im with hγ
  set lam : ℝ := 6 * Θ / 7 with hlam
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (γ : ℂ) * I with hc
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * I with hs
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hcne : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; nlinarith [hΘ0]
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; nlinarith [hΘ0])
  have hZcc0 : Zc c ≠ 0 := by rw [Zc_eq_of_ne hcne]; exact mul_ne_zero (sub_ne_zero.mpr hcne) hζc
  have hsre : s.re = σ := by rw [hs]; simp
  have hsne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hsre; nlinarith [hσlo]
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; exact hσlo.le)
  have hZcs0 : Zc s ≠ 0 := by rw [Zc_eq_of_ne hsne1]; exact mul_ne_zero (sub_ne_zero.mpr hsne1) hζs
  -- the normalized function `G = Zc/(Zc c)`, center value `1`; `logDeriv G = logDeriv Zc`
  have hG_diff : Differentiable ℂ (fun z => Zc z / Zc c) :=
    fun z => (Zc_differentiable z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖Zc c / Zc c‖ := by rw [div_self hZcc0, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => Zc w / Zc c) z = logDeriv Zc z := by
    intro z
    have hGeq : (fun w => Zc w / Zc c) = fun w => (Zc c)⁻¹ * Zc w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (Zc c)⁻¹ (inv_ne_zero hZcc0)]
  -- apply R7 (scaled Landau) to `G`
  obtain ⟨Z, m, hh, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  -- geometry: `s − c`, `ρ − c`, `s − ρ` are all real (shared imaginary part `γ`)
  have hsc : s - c = ((σ - 1 - Θ / 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
  have hscnorm : ‖s - c‖ ≤ 23 / 20 * lam := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, hlam]
    calc |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := hσc
      _ = 23 / 20 * (6 * Θ / 7) := by ring
  have hGs0 : Zc s / Zc c ≠ 0 := div_ne_zero hZcs0 hZcc0
  have hnum' := hnum s hscnorm hGs0
  rw [hLDG s] at hnum'
  have hre := neg_re_logDeriv_le hnum'
  -- pull `ρ` into the partial-fraction set
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hβ1; norm_num at hβ1
  have hZcρ : Zc ρ = 0 := by rw [Zc_eq_of_ne hρ1, hρ0, mul_zero]
  have hGρ : Zc ρ / Zc c = 0 := by rw [hZcρ, zero_div]
  have hρball : ρ ∈ ball c (3 / 2 * lam) := by
    rw [mem_ball, dist_eq_norm]
    have hρc : ρ - c = ((ρ.re - 1 - Θ / 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.sub_re, hcre, Complex.ofReal_re]; ring
      · rw [Complex.sub_im, hc]
        simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_im,
          Complex.ofReal_re, hγ]
    rw [hρc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [hβ1, hΘ0] : ρ.re - 1 - Θ / 2 ≤ 0), hlam]
    nlinarith [hρnear, hΘ0]
  obtain ⟨hρZ, hmρ⟩ := mem_zeros_of_factorization_gen hne_h hEqOn hρball hGρ
  -- all retained terms have positive real part; the `ρ`-term is retained
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'div : Zc ρ' / Zc c = 0 := (hmemb ρ' hρ').2
    have hρ'0 : Zc ρ' = 0 := by
      rcases div_eq_zero_iff.mp hρ'div with h | h
      · exact h
      · exact absurd h hZcc0
    have hρ'1 : ρ' ≠ 1 := fun h => by rw [h, Zc_one] at hρ'0; exact one_ne_zero hρ'0
    have hζρ' : riemannZeta ρ' = 0 := by
      rw [Zc_eq_of_ne hρ'1] at hρ'0; exact (mul_eq_zero.mp hρ'0).resolve_left (sub_ne_zero.mpr hρ'1)
    have hlt : ρ'.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ'
    rw [Complex.sub_re, hsre]; linarith
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hs, hγ]; apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hσρpos : 0 < σ - ρ.re := by
    have h := hpos ρ hρZ; rwa [Complex.sub_re, hsre] at h
  have hterm_re : (1 / (s - ρ)).re = 1 / (σ - ρ.re) := by
    rw [hsρ, show (1 : ℂ) / ((σ - ρ.re : ℝ) : ℂ) = (((1 / (σ - ρ.re)) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hsingle : (m ρ : ℝ) * (1 / (s - ρ)).re ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.single_le_sum (term_re_nonneg m hpos) hρZ
  have hlow : 1 / (σ - ρ.re) ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re := by
    have hm1 : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmρ
    have hnn : (0 : ℝ) ≤ 1 / (σ - ρ.re) := by positivity
    have h3 : 1 / (σ - ρ.re) ≤ (m ρ : ℝ) * (1 / (s - ρ)).re := by rw [hterm_re]; nlinarith
    linarith [h3, hsingle]
  -- the pole split, then assemble
  have hsplit := neg_logDeriv_zeta_split hsne1 hζs
  rw [hsplit]
  linarith [hre, hlow]

open Salt.SW in
/-- **R8 drop-all at a near-1-line disc.**  At the disc `c = (1+Θ/2) + iτ` (radius `λ = 6Θ/7`),
dropping every partial-fraction zero (each contributes `≥ 0`):
`Re(−ζ'/ζ(σ+iτ)) ≤ Re(1/(s−1)) + (120/λ)·log(4 M₀)`.  Used at the doubled height `τ = 2γ`. -/
theorem zeta_drop_all_disc {Θ σ M₀ τ : ℝ} (hΘ0 : 0 < Θ) (hM₀ : 1 ≤ M₀) (hσlo : 1 < σ)
    (hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ)
    (hsphere74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hsphere32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ M₀) :
    (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I)).re
      ≤ (1 / (((σ : ℂ) + (τ : ℂ) * I) - 1)).re + (120 / (6 * Θ / 7)) * Real.log (4 * M₀) := by
  set lam : ℝ := 6 * Θ / 7 with hlam
  set c : ℂ := ((1 + Θ / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hcre : c.re = 1 + Θ / 2 := by rw [hc]; simp
  have hcne : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; nlinarith [hΘ0]
  have hζc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; nlinarith [hΘ0])
  have hZcc0 : Zc c ≠ 0 := by rw [Zc_eq_of_ne hcne]; exact mul_ne_zero (sub_ne_zero.mpr hcne) hζc
  have hsre : s.re = σ := by rw [hs]; simp
  have hsne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hsre; nlinarith [hσlo]
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; exact hσlo.le)
  have hZcs0 : Zc s ≠ 0 := by rw [Zc_eq_of_ne hsne1]; exact mul_ne_zero (sub_ne_zero.mpr hsne1) hζs
  have hG_diff : Differentiable ℂ (fun z => Zc z / Zc c) :=
    fun z => (Zc_differentiable z).div_const _
  have hGc_floor : (1 : ℝ) / 4 ≤ ‖Zc c / Zc c‖ := by rw [div_self hZcc0, norm_one]; norm_num
  have hLDG : ∀ z, logDeriv (fun w => Zc w / Zc c) z = logDeriv Zc z := by
    intro z
    have hGeq : (fun w => Zc w / Zc c) = fun w => (Zc c)⁻¹ * Zc w := by funext w; ring
    rw [hGeq, logDeriv_const_mul z (Zc c)⁻¹ (inv_ne_zero hZcc0)]
  obtain ⟨Z, m, hh, hmemb, -, hne_h, hEqOn, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum_scaled hG_diff hlam0 hM₀ hGc_floor hsphere74 hsphere32
  have hsc : s - c = ((σ - 1 - Θ / 2 : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
  have hscnorm : ‖s - c‖ ≤ 23 / 20 * lam := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, hlam]
    calc |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := hσc
      _ = 23 / 20 * (6 * Θ / 7) := by ring
  have hnum' := hnum s hscnorm (div_ne_zero hZcs0 hZcc0)
  rw [hLDG s] at hnum'
  have hre := neg_re_logDeriv_le hnum'
  -- every retained term is nonnegative, so the whole sum is dropped
  have hpos : ∀ ρ' ∈ Z, 0 < (s - ρ').re := by
    intro ρ' hρ'
    have hρ'div : Zc ρ' / Zc c = 0 := (hmemb ρ' hρ').2
    have hρ'0 : Zc ρ' = 0 := (div_eq_zero_iff.mp hρ'div).resolve_right hZcc0
    have hρ'1 : ρ' ≠ 1 := fun h => by rw [h, Zc_one] at hρ'0; exact one_ne_zero hρ'0
    have hζρ' : riemannZeta ρ' = 0 := by
      rw [Zc_eq_of_ne hρ'1] at hρ'0; exact (mul_eq_zero.mp hρ'0).resolve_left (sub_ne_zero.mpr hρ'1)
    have hlt : ρ'.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ'
    rw [Complex.sub_re, hsre]; linarith
  have hsum_nn : 0 ≤ ∑ ρ' ∈ Z, (m ρ' : ℝ) * (1 / (s - ρ')).re :=
    Finset.sum_nonneg (term_re_nonneg m hpos)
  have hsplit := neg_logDeriv_zeta_split hsne1 hζs
  rw [hsplit]
  linarith [hre, hsum_nn]

/-! ## R9 core — the 3-4-1 assembly at the near-1-line disc width -/

open Salt.SW DirichletCharacter in
/-- **R9 — the disc 3-4-1 assembly (per-zero).**  Combining the keep-one bound (`zeta_keep_one_disc`
at `s₁ = σ+iγ`), the drop-all bound (`zeta_drop_all_disc` at `s₂ = σ+2iγ`), the real-`σ` pole bound
(`neg_logDeriv_zeta_le`) and `three_four_one_logDeriv`, then `zero_free_extraction`, gives
`ρ.re ≤ 1 − dd/(7 Lq)` for any ζ-zero `ρ` of height `|γ| ≥ 1`.

The width scale `Lq`, the offset `dd`, the disc size `Θ` and the sphere bound `M₀` are parameters;
the chain closes when `8 + 5·(120/λ)·log(4 M₀) ≤ Lq/(2 dd)` (`hchainC`), with `λ = 6Θ/7`.  This is
the shared assembly for the power (`Lq = L^{3/4}(log L)³`) and Littlewood regions — only the sphere
bounds (from the growth input) and the `Lq`/`Θ`/`M₀` relations differ. -/
theorem zeta_zero_free_of_disc {ρ : ℂ} (hρ0 : riemannZeta ρ = 0) (hβ1 : ρ.re < 1)
    (hγ1 : 1 ≤ |ρ.im|) {Θ M₀ Lq dd : ℝ} (hΘ0 : 0 < Θ) (hΘ2 : Θ ≤ 2) (hM₀ : 1 ≤ M₀)
    (hdd : 0 < dd) (hddlt : dd < 1) (hLq0 : 0 < Lq) (hσΘ : dd / Lq ≤ Θ / 2)
    (hwΘ : dd / (7 * Lq) ≤ 11 / 14 * Θ)
    (hchainC : 8 + 5 * ((120 / (6 * Θ / 7)) * Real.log (4 * M₀)) ≤ Lq / (2 * dd))
    (hkeep74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hkeep32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I) (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * I)‖ ≤ M₀)
    (hdrop74 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (7 / 4 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀)
    (hdrop32 : ∀ z ∈ sphere (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)
        (3 / 2 * (6 * Θ / 7)),
        ‖Zc z / Zc (((1 + Θ / 2 : ℝ) : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ M₀) :
    ρ.re ≤ 1 - dd / (7 * Lq) := by
  have h6Θ : (0 : ℝ) < 6 * Θ / 7 := by linarith [hΘ0]
  set Cnum : ℝ := (120 / (6 * Θ / 7)) * Real.log (4 * M₀) with hCnum
  have hCnum0 : 0 ≤ Cnum := by
    rw [hCnum]
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) h6Θ)) (Real.log_nonneg (by nlinarith [hM₀]))
  have hddL : 0 < dd / Lq := div_pos hdd hLq0
  set σ : ℝ := 1 + dd / Lq with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith [hddL]
  have hσ2le : σ ≤ 2 := by rw [hσdef]; linarith [hσΘ, hΘ2]
  have hσc : |σ - 1 - Θ / 2| ≤ 69 / 70 * Θ := by
    rw [hσdef, abs_of_nonpos (by nlinarith [hσΘ, hddL] : (1 + dd / Lq) - 1 - Θ / 2 ≤ 0)]
    nlinarith [hσΘ, hΘ0, hddL]
  -- the two easy cases: `ρ` outside the disc, else the keep-one chain
  rcases le_or_gt ρ.re (1 - 11 / 14 * Θ) with hout | hin
  · linarith [hwΘ, hout]
  · -- the Davenport chain
    have hA1 := zeta_keep_one_disc hρ0 hβ1 hΘ0 hM₀ hσ1 hσc hin hkeep74 hkeep32
    have hA2 := zeta_drop_all_disc (τ := 2 * ρ.im) hΘ0 hM₀ hσ1 hσc hdrop74 hdrop32
    have hA0 : (-logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
      rw [logDeriv_apply, ← neg_div]; exact neg_logDeriv_zeta_le hσ1 hσ2le
    -- 3-4-1 at the trivial character mod 1
    have h341 := three_four_one_logDeriv (1 : DirichletCharacter ℂ 1) hσ1 ρ.im
    rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h341
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ0C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ1C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ 1) hσ2C] at h341
    simp only [LFunction_modOne_eq] at h341
    -- align `A2` with `s2 = σ + 2iγ`
    have hs2align : (σ : ℂ) + ((2 * ρ.im : ℝ) : ℂ) * I = s2 := by rw [hs2def]; push_cast; ring
    rw [hs2align] at hA2
    -- pole real parts `≤ 1` (heights `|γ| ≥ 1`, `|2γ| ≥ 2`)
    have hP1 : (1 / (s1 - 1)).re ≤ 1 := by
      have him : (s1 - 1).im = ρ.im := by
        rw [hs1def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (1 : ℝ) ≤ ‖s1 - 1‖ := by
        have h := Complex.abs_im_le_norm (s1 - 1); rw [him] at h; linarith [hγ1]
      calc (1 / (s1 - 1)).re ≤ ‖1 / (s1 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s1 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s1 - 1‖)]; exact hn
    have hP2 : (1 / (s2 - 1)).re ≤ 1 := by
      have him : (s2 - 1).im = 2 * ρ.im := by
        rw [hs2def]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have hn : (1 : ℝ) ≤ ‖s2 - 1‖ := by
        have h := Complex.abs_im_le_norm (s2 - 1); rw [him] at h
        have h2 : (2 : ℝ) * |ρ.im| = |2 * ρ.im| := by rw [abs_mul]; norm_num
        nlinarith [hγ1, h, h2, abs_nonneg (2 * ρ.im)]
      calc (1 / (s2 - 1)).re ≤ ‖1 / (s2 - 1)‖ :=
            le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
        _ = 1 / ‖s2 - 1‖ := by rw [norm_div, norm_one]
        _ ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < ‖s2 - 1‖)]; exact hn
    -- the Davenport chain `4/(σ−β) ≤ 3/(σ−1) + 8 + 5 Cnum`
    have key : 4 * (1 / (σ - ρ.re)) ≤ 3 * (1 / (σ - 1)) + (8 + 5 * Cnum) := by
      rw [← hCnum] at hA1 hA2
      linarith [h341, hA0, hA1, hA2, hP1, hP2]
    have hchain' : 4 / (dd / Lq + (1 - ρ.re)) ≤ 3 / (dd / Lq) + (1 / (2 * dd)) * Lq := by
      rw [mul_one_div, mul_one_div] at key
      have e1 : σ - ρ.re = dd / Lq + (1 - ρ.re) := by rw [hσdef]; ring
      have e2 : σ - 1 = dd / Lq := by rw [hσdef]; ring
      rw [e1, e2] at key
      have hCLq : (8 : ℝ) + 5 * Cnum ≤ (1 / (2 * dd)) * Lq := by
        rw [div_mul_eq_mul_div, one_mul]; linarith [hchainC]
      linarith [key, hCLq]
    have hCdd : (1 / (2 * dd)) * dd = 1 / 2 := by field_simp
    have hext := zero_free_extraction hLq0 hdd hCdd hβ1 hchain'
    linarith [hext]

end Salt.Vk
