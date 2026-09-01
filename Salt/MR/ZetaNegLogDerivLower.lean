/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.SW.ZetaPartialFractions
import Salt.SW.ZetaZeroFree
import Salt.MR.HalaszPrimesCore

/-!
# A4F H2 — the LOWER near-1-line bound for `Re(−ζ′/ζ)` (the dVP variant)

The mirror of the landed `Salt.SW.zeta_neg_re_logDeriv_le`: on `1 < σ ≤ 2`, at `s = σ + 2γi`,

`Re(−ζ′/ζ(s)) ≥ Re(1/(s−1)) − C·log²(|γ|+2)`.

The upper direction dropped the partial-fraction zero terms (each `Re(1/(s−ρ)) ≥ 0`); the
lower direction must BOUND them, and the mechanism is the CENTRE COMPARISON: one invocation
of the S2 pipeline (`entire_norm_logDeriv_sub_sum'` at the centre `c = 2 + 2γi`) supplies a
single zero set `Z` used at BOTH evaluation points — the same-witness discipline.

* At the centre, `‖ζ′/ζ(c)‖` is Dirichlet-series bounded (`norm_logDeriv_zeta_cline_le` at
  the line `Re = 2`, then `sum_vonMangoldt_le_pole_add_Zc` at the real point `2` — the
  latter's `‖logDeriv Zc 2‖` is a single fixed real, carried inside the `∃ C`), so the
  centred zero sum is `O(log(|γ|+2))`; each centre term is `≥ 4/9` (the ball has radius
  `3/2` and zeros sit left of `Re = 1`), so the zero COUNT is `O(log(|γ|+2))`.
* At `s`, each term is `≤ 1/(σ−β)`, and the ZERO-FREE REGION (`zeta_zero_free_region` —
  ball zeros have `Re ρ ≥ 1/2`, so its hypothesis is free) gives
  `σ−β ≥ 1−β ≥ c₃/log(|Im ρ|+2) ≥ c₃/(2·log(|γ|+2))`.

Count `× ` per-zero `= O(log²)` — **the log² shape is the honest ceiling of this mechanism**
(a per-zero bound below `≍ log` is not available at this supply), and the A4F assembly
absorbs any fixed power of `log` on the bounded-height range where this bound is consumed.

⛔ The zero-COUNT alone cannot bound the dropped sum (the per-zero factor is where the
zero-free input is forced); this file takes the count AND the separation, per the
commissioning fold.
-/

namespace Salt.MR

open Complex (I)
open Salt.SW Metric ArithmeticFunction

set_option maxHeartbeats 1000000 in
-- one pipeline invocation plus two large `linarith` closes over monomial atoms in
-- `c₃⁻¹`, `L`, `Z₂`; the default budget times out in the final chain
/-- **H2 (below-`T₀` arm).**  The de la Vallée Poussin–variant LOWER bound: there is `C ≥ 0`
with `Re(1/(s−1)) − C·log²(|γ|+2) ≤ Re(−ζ′/ζ(s))` at `s = σ + 2γi` for all `1 < σ ≤ 2` and
all real `γ`.  Mirror of `Salt.SW.zeta_neg_re_logDeriv_le`; see the module doc for the
centre-comparison mechanism. -/
theorem zeta_neg_re_logDeriv_ge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ γ : ℝ), 1 < σ → σ ≤ 2 →
      (1 / (((σ : ℂ) + 2 * (γ : ℂ) * I) - 1)).re - C * Real.log (|γ| + 2) ^ 2
        ≤ (-logDeriv riemannZeta ((σ : ℂ) + 2 * (γ : ℂ) * I)).re := by
  obtain ⟨c₃, hc₃pos, hzf⟩ := Salt.SW.zeta_zero_free_region
  set Z₂ : ℝ := ‖logDeriv Zc ((2 : ℝ) : ℂ)‖ with hZ₂def
  have hZ₂0 : 0 ≤ Z₂ := norm_nonneg _
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨9 / (2 * c₃) * ((2 + Z₂) / Real.log 2 + 1080) + 1080 / Real.log 2, by positivity, ?_⟩
  intro σ γ h1 h2
  set t₀ : ℝ := 2 * γ with ht₀
  set s : ℂ := (σ : ℂ) + 2 * (γ : ℂ) * I with hs
  set c : ℂ := 2 + (t₀ : ℂ) * I with hc
  set L : ℝ := Real.log (|γ| + 2) with hL
  have hLlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ])
  have hLpos : 0 < L := lt_of_lt_of_le hlog2 hLlog2
  -- geometry of `s` and `c`
  have hsceq : s = (σ : ℂ) + (t₀ : ℂ) * I := by rw [hs, ht₀]; push_cast; ring
  have hsre : s.re = σ := by rw [hsceq]; simp
  have hσC : (1 : ℝ) < s.re := by rw [hsre]; exact h1
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hσC; norm_num at hσC
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hσC)
  have hcre : c.re = 2 := by rw [hc]; simp
  have hcim : c.im = t₀ := by rw [hc]; simp
  have hc_ne1 : c ≠ 1 := fun h => by rw [h, Complex.one_re] at hcre; norm_num at hcre
  have hζc : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; norm_num)
  have hZcs : Zc s ≠ 0 := by
    rw [Zc_eq_of_ne hs_ne1]; exact mul_ne_zero (sub_ne_zero.mpr hs_ne1) hζs
  have hZcc : Zc c ≠ 0 := by
    rw [Zc_eq_of_ne hc_ne1]; exact mul_ne_zero (sub_ne_zero.mpr hc_ne1) hζc
  -- ONE pipeline invocation at the centre; `Z` is shared by both evaluation points
  have hsphere74 : ∀ z ∈ sphere c (7 / 4), ‖Zc z‖ ≤ M0zeta t₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz
    exact Zc_sphere_bound t₀ (le_refl _) hz
  have hsphere32 : ∀ z ∈ sphere c (3 / 2), ‖Zc z‖ ≤ M0zeta t₀ := by
    intro z hz; rw [mem_sphere, dist_eq_norm] at hz
    exact Zc_sphere_bound t₀ (by norm_num) hz
  obtain ⟨Z, m, h, hmemb, -, -, -, -, hnum⟩ :=
    entire_norm_logDeriv_sub_sum' Zc_differentiable (one_le_M0zeta t₀) (Zc_center_lower t₀)
      hsphere74 hsphere32
  -- the M₀ collapse (as in the landed sibling)
  have hM0log : 120 * Real.log (4 * M0zeta t₀) ≤ 1080 * L := by
    have hcoll := log_4M0zeta_le γ
    rw [ht₀, hL]
    nlinarith [hcoll]
  have hM0nn : 0 ≤ 120 * Real.log (4 * M0zeta t₀) := by
    have h1M : (1 : ℝ) ≤ M0zeta t₀ := one_le_M0zeta t₀
    have : (0 : ℝ) ≤ Real.log (4 * M0zeta t₀) := Real.log_nonneg (by nlinarith)
    linarith
  -- the shared zero facts
  have hzero_facts : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re < 1 ∧ ‖ρ - c‖ < 3 / 2 := by
    intro ρ hρ
    obtain ⟨hball, hZcρ⟩ := hmemb ρ hρ
    have hρ1 : ρ ≠ 1 := fun hh => by rw [hh, Zc_one] at hZcρ; exact one_ne_zero hZcρ
    have hζρ : riemannZeta ρ = 0 := by
      rw [Zc_eq_of_ne hρ1] at hZcρ
      exact (mul_eq_zero.mp hZcρ).resolve_left (sub_ne_zero.mpr hρ1)
    have hρre1 : ρ.re < 1 := by
      by_contra hcn; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcn) hζρ
    exact ⟨hζρ, hρre1, by rw [← dist_eq_norm]; exact mem_ball.mp hball⟩
  -- ## the centre: `‖logDeriv Zc c‖ ≤ 2 + Z₂`, Dirichlet-series grade
  have hZcc_norm : ‖logDeriv Zc c‖ ≤ 2 + Z₂ := by
    have hζsplit := logDeriv_zeta_eq hc_ne1 hζc
    have hZceq : logDeriv Zc c = logDeriv riemannZeta c + 1 / (c - 1) := by
      rw [hζsplit]; ring
    have hpolec : ‖(1 : ℂ) / (c - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have hre1 : (c - 1).re = 1 := by rw [Complex.sub_re, hcre, Complex.one_re]; norm_num
      have hge := Complex.abs_re_le_norm (c - 1)
      rw [hre1] at hge
      have h1n : (1 : ℝ) ≤ ‖c - 1‖ := le_trans (by norm_num) hge
      rw [div_le_one (by linarith)]
      exact h1n
    have hcline : ‖logDeriv riemannZeta c‖ ≤ ∑' n, vonMangoldt n / (n : ℝ) ^ (2 : ℝ) := by
      have hb := norm_logDeriv_zeta_cline_le (c := 2) (by norm_num) t₀
      have h2c : (((2 : ℝ)) : ℂ) = (2 : ℂ) := by norm_num
      rw [h2c] at hb
      rw [hc]
      exact hb
    have hpole2 : ∑' n, vonMangoldt n / (n : ℝ) ^ (2 : ℝ) ≤ 1 / (2 - 1) + Z₂ := by
      have := sum_vonMangoldt_le_pole_add_Zc (x := 2) (by norm_num)
      rw [hZ₂def]
      exact this
    calc ‖logDeriv Zc c‖ = ‖logDeriv riemannZeta c + 1 / (c - 1)‖ := by rw [hZceq]
      _ ≤ ‖logDeriv riemannZeta c‖ + ‖(1 : ℂ) / (c - 1)‖ := norm_add_le _ _
      _ ≤ (1 / (2 - 1) + Z₂) + 1 := by
          have := le_trans hcline hpole2
          linarith [hpolec]
      _ = 2 + Z₂ := by ring
  -- ## the centred zero sum is `O(L)`
  have hnumc := hnum c (by rw [sub_self, norm_zero]; norm_num) hZcc
  have hreSum_c : (∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)).re
      = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (c - ρ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [div_eq_mul_inv, Complex.mul_re, one_div]
    simp
  have hsumc : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (c - ρ)).re ≤ (2 + Z₂) + 1080 * L := by
    have hnormS : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)‖
        ≤ ‖logDeriv Zc c‖ + 120 * Real.log (4 * M0zeta t₀) := by
      have htri : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)‖
          ≤ ‖logDeriv Zc c‖ + ‖logDeriv Zc c - ∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)‖ := by
        have := norm_sub_le (logDeriv Zc c)
          (logDeriv Zc c - ∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ))
        simpa using this
      linarith [hnumc]
    have hre_le : (∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)).re
        ≤ ‖∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)‖ := Complex.re_le_norm _
    rw [← hreSum_c]
    linarith [hZcc_norm, hM0log]
  -- ## each centre term is `≥ 4/9`, so the count is `O(L)`
  have hterm_c : ∀ ρ ∈ Z, (4 : ℝ) / 9 ≤ (1 / (c - ρ)).re := by
    intro ρ hρ
    obtain ⟨-, hρre1, hball⟩ := hzero_facts ρ hρ
    have hcρre : 1 < (c - ρ).re := by
      rw [Complex.sub_re, hcre]; linarith
    have hne : c - ρ ≠ 0 := fun hh => by
      rw [hh, Complex.zero_re] at hcρre; norm_num at hcρre
    have hnormSq_lt : Complex.normSq (c - ρ) < 9 / 4 := by
      rw [Complex.normSq_eq_norm_sq]
      have hnorm : ‖c - ρ‖ < 3 / 2 := by
        rw [show c - ρ = -(ρ - c) by ring, norm_neg]; exact hball
      nlinarith [norm_nonneg (c - ρ)]
    have hnormSq_pos : 0 < Complex.normSq (c - ρ) := Complex.normSq_pos.mpr hne
    rw [one_div, Complex.inv_re]
    calc (4 : ℝ) / 9 = 1 / (9 / 4) := by norm_num
      _ ≤ (c - ρ).re / Complex.normSq (c - ρ) :=
          div_le_div₀ (by linarith) (by linarith) hnormSq_pos (le_of_lt hnormSq_lt)
  have hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ 9 / 4 * ((2 + Z₂) + 1080 * L) := by
    have h49 : (4 : ℝ) / 9 * ∑ ρ ∈ Z, (m ρ : ℝ)
        ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (c - ρ)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      rw [mul_comm ((4 : ℝ) / 9)]
      exact mul_le_mul_of_nonneg_left (hterm_c ρ hρ) (Nat.cast_nonneg _)
    linarith [hsumc]
  -- ## each `s`-term is `≤ (2/c₃)·L`, by the zero-free separation
  have hterm_s : ∀ ρ ∈ Z, (1 / (s - ρ)).re ≤ 2 / c₃ * L := by
    intro ρ hρ
    obtain ⟨hζρ, hρre1, hball⟩ := hzero_facts ρ hρ
    -- `Re ρ ≥ 1/2` from the ball, so the zero-free region applies hypothesis-free
    have hre_half : (1 : ℝ) / 2 ≤ ρ.re := by
      have hg := Complex.abs_re_le_norm (ρ - c)
      rw [Complex.sub_re, hcre] at hg
      have := abs_le.mp (le_of_lt (lt_of_le_of_lt hg hball))
      linarith [this.1]
    have hβ := hzf hζρ hre_half
    have him : |ρ.im| ≤ |t₀| + 3 / 2 := by
      have hg := Complex.abs_im_le_norm (ρ - c)
      rw [Complex.sub_im, hcim] at hg
      have habs := abs_sub_abs_le_abs_sub ρ.im t₀
      linarith [lt_of_le_of_lt hg hball]
    have hLρpos : 0 < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hLρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      have habs2γ : |t₀| = 2 * |γ| := by rw [ht₀, abs_mul]; norm_num
      have hstep : |ρ.im| + 2 ≤ (|γ| + 2) ^ 2 := by
        rw [habs2γ] at him
        nlinarith [abs_nonneg γ]
      calc Real.log (|ρ.im| + 2) ≤ Real.log ((|γ| + 2) ^ 2) :=
            Real.log_le_log (by positivity) hstep
        _ = 2 * L := by rw [Real.log_pow, hL]; push_cast; ring
    have hgap : c₃ / Real.log (|ρ.im| + 2) ≤ σ - ρ.re := by linarith [hβ]
    have hgappos : 0 < σ - ρ.re := lt_of_lt_of_le (div_pos hc₃pos hLρpos) hgap
    have hsρre : (s - ρ).re = σ - ρ.re := by rw [Complex.sub_re, hsre]
    have hre_bound : (1 / (s - ρ)).re ≤ 1 / (σ - ρ.re) := by
      rw [one_div, Complex.inv_re, hsρre]
      have hnsq : (σ - ρ.re) ^ 2 ≤ Complex.normSq (s - ρ) := by
        rw [Complex.normSq_apply, hsρre]
        nlinarith [sq_nonneg (s - ρ).im]
      calc (σ - ρ.re) / Complex.normSq (s - ρ) ≤ (σ - ρ.re) / (σ - ρ.re) ^ 2 :=
            div_le_div_of_nonneg_left hgappos.le (by positivity) hnsq
        _ = 1 / (σ - ρ.re) := by
            rw [sq]
            field_simp
    have hsep : 1 / (σ - ρ.re) ≤ Real.log (|ρ.im| + 2) / c₃ := by
      rw [div_le_div_iff₀ hgappos hc₃pos]
      have := (div_le_iff₀ hLρpos).mp hgap
      nlinarith [this]
    calc (1 / (s - ρ)).re ≤ 1 / (σ - ρ.re) := hre_bound
      _ ≤ Real.log (|ρ.im| + 2) / c₃ := hsep
      _ ≤ 2 * L / c₃ := by
          have := mul_le_mul_of_nonneg_right hLρ (inv_nonneg.mpr hc₃pos.le)
          simpa [div_eq_mul_inv] using this
      _ = 2 / c₃ * L := by ring
  -- ## the `s`-side zero sum is `O(L²)`
  have h2c₃L : (0 : ℝ) ≤ 2 / c₃ * L :=
    mul_nonneg (div_nonneg (by norm_num) hc₃pos.le) hLpos.le
  have hsums : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re
      ≤ 2 / c₃ * L * (9 / 4 * ((2 + Z₂) + 1080 * L)) := by
    have hstep : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re
        ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (2 / c₃ * L) := by
      refine Finset.sum_le_sum fun ρ hρ => ?_
      exact mul_le_mul_of_nonneg_left (hterm_s ρ hρ) (Nat.cast_nonneg _)
    have hfact : ∑ ρ ∈ Z, (m ρ : ℝ) * (2 / c₃ * L) = 2 / c₃ * L * ∑ ρ ∈ Z, (m ρ : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [hfact] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hcount h2c₃L)
  -- ## assemble at `s`
  have hnums := hnum s (by
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by rw [hsceq, hc]; push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith) hZcs
  have hreSum_s : (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
      = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [div_eq_mul_inv, Complex.mul_re, one_div]
    simp
  have hres : -(∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re) - 120 * Real.log (4 * M0zeta t₀)
      ≤ (-logDeriv Zc s).re := by
    have hreE : (logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
        ≤ 120 * Real.log (4 * M0zeta t₀) :=
      le_trans (Complex.re_le_norm _) hnums
    have hlin : (-logDeriv Zc s).re
        = -(logDeriv Zc s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
          - (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re := by
      rw [Complex.neg_re, Complex.sub_re]; ring
    rw [hlin, hreSum_s]
    linarith [hreE]
  -- ## the `L²` absorption and the close
  have habsorb : 2 / c₃ * L * (9 / 4 * ((2 + Z₂) + 1080 * L)) + 1080 * L
      ≤ (9 / (2 * c₃) * ((2 + Z₂) / Real.log 2 + 1080) + 1080 / Real.log 2) * L ^ 2 := by
    have hZ2L : (2 + Z₂) ≤ (2 + Z₂) / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [hLlog2, hZ₂0]
    have hLL : L ≤ L ^ 2 / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      nlinarith [hLlog2, hLpos]
    have hbig : (2 + Z₂) + 1080 * L ≤ ((2 + Z₂) / Real.log 2 + 1080) * L := by
      nlinarith [hZ2L]
    have hc₃L : (0 : ℝ) ≤ 9 / (2 * c₃) * L :=
      mul_nonneg (div_nonneg (by norm_num) (by linarith)) hLpos.le
    have hstep1 : 2 / c₃ * L * (9 / 4 * ((2 + Z₂) + 1080 * L))
        ≤ 9 / (2 * c₃) * L * (((2 + Z₂) / Real.log 2 + 1080) * L) := by
      have hh := mul_le_mul_of_nonneg_left hbig hc₃L
      calc 2 / c₃ * L * (9 / 4 * ((2 + Z₂) + 1080 * L))
          = 9 / (2 * c₃) * L * ((2 + Z₂) + 1080 * L) := by ring
        _ ≤ 9 / (2 * c₃) * L * (((2 + Z₂) / Real.log 2 + 1080) * L) := hh
    have hstep2 : (1080 : ℝ) * L ≤ 1080 / Real.log 2 * L ^ 2 := by
      have := mul_le_mul_of_nonneg_left hLL (by norm_num : (0 : ℝ) ≤ 1080)
      calc (1080 : ℝ) * L ≤ 1080 * (L ^ 2 / Real.log 2) := this
        _ = 1080 / Real.log 2 * L ^ 2 := by ring
    calc 2 / c₃ * L * (9 / 4 * ((2 + Z₂) + 1080 * L)) + 1080 * L
        ≤ 9 / (2 * c₃) * L * (((2 + Z₂) / Real.log 2 + 1080) * L)
          + 1080 / Real.log 2 * L ^ 2 := by linarith
      _ = (9 / (2 * c₃) * ((2 + Z₂) / Real.log 2 + 1080) + 1080 / Real.log 2) * L ^ 2 := by
          ring
  have hsplit := neg_logDeriv_zeta_split hs_ne1 hζs
  rw [hsplit]
  have hchain : -((9 / (2 * c₃) * ((2 + Z₂) / Real.log 2 + 1080) + 1080 / Real.log 2) * L ^ 2)
      ≤ (-logDeriv Zc s).re := by
    have h1080L : 120 * Real.log (4 * M0zeta t₀) ≤ 1080 * L := hM0log
    linarith [hres, hsums, habsorb]
  linarith [hchain]

end Salt.MR
