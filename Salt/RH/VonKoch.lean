/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.Targets
import Salt.SW.ZetaPartialFractions
import Salt.MR.ZetaLowerAllT
import Salt.MR.TwistedEdge

/-!
# O106 row R1 — von Koch from RH: the analytic inputs (nodes N1, N2)

The route (the O106 plan, addendum 3, frozen after a three-refuter pass): bound `ζ′/ζ` near the
critical line by the λ-scaled Landau engine centred at `7/5 + it` with `λ = 79/100`. Its outer
sphere has radius `553/400` (`= 7/4 · λ`), so it stays in `Re ≥ 7/400 > 0`, where the landed growth
bound `Salt.SW.Zc_growth` applies, and no growth bound left of the critical line is needed.

* **N1** `zc_sphere_growth` — on any sphere about `7/5 + it` of radius `≤ 553/400`,
  `‖Zc z‖ ≤ 60 (|t| + 5)²`.
* **N2** `zc_centre_lower` — `‖Zc (7/5 + it)‖ ≥ c / ((log(|t|+3))^{3/4} (log log(|t|+16))^4)`.
-/

namespace Salt.RH

open Complex Salt.SW

/-- **N1.** Sphere growth of `Zc` about `7/5 + it`, for every radius up to `553/400`. -/
theorem zc_sphere_growth (t : ℝ) {r : ℝ} (hr : r ≤ 553 / 400) {z : ℂ}
    (hz : z ∈ Metric.sphere ((7 / 5 : ℂ) + (t : ℂ) * I) r) :
    ‖Zc z‖ ≤ 60 * (|t| + 5) ^ 2 := by
  have hd : ‖z - ((7 / 5 : ℂ) + (t : ℂ) * I)‖ = r := by
    simpa [dist_eq_norm] using hz
  have hre : |z.re - 7 / 5| ≤ r := by
    have h := Complex.abs_re_le_norm (z - ((7 / 5 : ℂ) + (t : ℂ) * I))
    rw [hd] at h
    simpa using h
  have him : |z.im - t| ≤ r := by
    have h := Complex.abs_im_le_norm (z - ((7 / 5 : ℂ) + (t : ℂ) * I))
    rw [hd] at h
    simpa using h
  have hre_lo : 7 / 400 ≤ z.re := by
    have := (abs_le.mp hre).1
    linarith
  have hre_hi : z.re ≤ 3 := by
    have := (abs_le.mp hre).2
    linarith
  have him_le : |z.im| ≤ |t| + 2 := by
    have h1 : |z.im| ≤ |z.im - t| + |t| := by
      have := abs_add_le (z.im - t) t
      simpa using this
    linarith
  have hpos : 0 < z.re := by linarith
  have hg := Zc_growth hpos
  set a : ℝ := |t| + 5 with ha
  have ha1 : 1 ≤ a := by have := abs_nonneg t; linarith
  have hz_le : ‖z‖ ≤ a := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    have : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith, hre_hi⟩
    linarith
  have hz1_le : ‖z - 1‖ ≤ a := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    have hr1 : |(z - 1).re| ≤ 2 := by
      rw [Complex.sub_re, Complex.one_re]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hi1 : |(z - 1).im| = |z.im| := by simp
    linarith
  have hinv : 1 + 1 / z.re ≤ 59 := by
    have : 1 / z.re ≤ 400 / 7 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      linarith
    linarith
  have hprod : ‖z - 1‖ * (‖z‖ * (1 + 1 / z.re)) ≤ a * (a * 59) := by
    have h0 : 0 ≤ 1 + 1 / z.re := by positivity
    gcongr
  nlinarith

/-- **N2.** A lower bound for `Zc` at the centre `7/5 + it`, uniform in `t`. -/
theorem zc_centre_lower : ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
    c / ((Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ))
      ≤ ‖Zc ((7 / 5 : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨c'', hc'', hlow⟩ := Salt.MR.zeta_lower_all_t
  refine ⟨2 / 5 * c'', by positivity, fun t => ?_⟩
  have hs : ((7 / 5 : ℂ) + (t : ℂ) * I) = (((1 + 2 / 5 : ℝ) : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  have hne : ((7 / 5 : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  rw [Zc_eq_of_ne hne, norm_mul]
  have hz := hlow (2 / 5) t (by norm_num) (by norm_num) (by norm_num)
  rw [← hs] at hz
  have h1 : (2 / 5 : ℝ) ≤ ‖(7 / 5 : ℂ) + (t : ℂ) * I - 1‖ := by
    have h := Complex.abs_re_le_norm ((7 / 5 : ℂ) + (t : ℂ) * I - 1)
    have hre : ((7 / 5 : ℂ) + (t : ℂ) * I - 1).re = 2 / 5 := by simp; norm_num
    rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)] at h
    exact h
  have hD : 0 < (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (|t| + 16))) ^ (4 : ℕ) := by
    have hl3 : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
    have hl16 : 1 < Real.log (|t| + 16) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := Real.exp_one_lt_d9
      have := abs_nonneg t
      linarith
    have hll : 0 < Real.log (Real.log (|t| + 16)) := Real.log_pos hl16
    positivity
  rw [mul_div_assoc]
  exact mul_le_mul h1 hz (by positivity) (norm_nonneg _)

/-! ## RH, read on `Zc` -/

/-- Under RH, a zero of `Zc` in `Re > 0` lies on the critical line. -/
theorem zc_zero_re_half (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : Zc ρ = 0) (hre : 0 < ρ.re) :
    ρ.re = 1 / 2 := by
  have h1 : ρ ≠ 1 := by
    rintro rfl
    rw [Zc_one] at hρ
    exact one_ne_zero hρ
  rw [Zc_eq_of_ne h1] at hρ
  have hz : riemannZeta ρ = 0 := by
    rcases mul_eq_zero.mp hρ with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h
  refine hRH ρ hz ?_ h1
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp at this
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

/-- Under RH, `Zc` does not vanish on `Re > 1/2`. -/
theorem zc_ne_zero_of_half_lt (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    Zc s ≠ 0 := by
  intro h
  have := zc_zero_re_half hRH h (by linarith)
  linarith

/-- The crude form of N2's lower bound: `c / (|t|+16)^5`. -/
theorem zc_centre_lower_crude : ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
    c / (|t| + 16) ^ 5 ≤ ‖Zc ((7 / 5 : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨c, hc, hlow⟩ := zc_centre_lower
  refine ⟨c, hc, fun t => le_trans ?_ (hlow t)⟩
  have ht0 := abs_nonneg t
  set u : ℝ := |t| + 16 with hu
  have hu1 : 1 ≤ u := by linarith
  have hL3 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hL3u : Real.log (|t| + 3) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |t| + 3 by positivity)
    linarith
  have hA : (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) ≤ u :=
    le_trans (Real.rpow_le_self_of_one_le hL3 (by norm_num)) hL3u
  have hl16 : 1 < Real.log u := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hB0 : 0 < Real.log (Real.log u) := Real.log_pos hl16
  have hBu : Real.log (Real.log u) ≤ u := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log u by linarith)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < u by linarith)
    linarith
  have hA0 : 0 < (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) := by positivity
  have hD : (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log u)) ^ (4 : ℕ) ≤ u ^ 5 := by
    have : (Real.log (Real.log u)) ^ (4 : ℕ) ≤ u ^ 4 := pow_le_pow_left₀ hB0.le hBu 4
    calc (Real.log (|t| + 3)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log u)) ^ (4 : ℕ)
        ≤ u * u ^ 4 := mul_le_mul hA this (by positivity) (by linarith)
      _ = u ^ 5 := by ring
  exact div_le_div_of_nonneg_left hc.le (by positivity) hD

/-! ## N3 — the ζ′/ζ bound near the critical line, under RH -/

/-- **N3.** Under RH, for `1/2 < Re s ≤ 23/10`,
`‖logDeriv Zc s‖ ≤ K · log(|Im s| + 3) · (1 + 1/(Re s − 1/2))`. -/
theorem zc_logDeriv_near_half (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv Zc s‖ ≤ K * Real.log (|s.im| + 3) * (1 + 1 / (s.re - 1 / 2)) := by
  obtain ⟨c, hc, hlow⟩ := zc_centre_lower_crude
  set C₀ : ℝ := Real.log (4 * (1 + 60 / c)) + 7 * Real.log 6 with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have h1 : 0 ≤ Real.log (4 * (1 + 60 / c)) := Real.log_nonneg (by
      have : 0 ≤ 60 / c := by positivity
      linarith)
    have h2 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith
  have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  set K : ℝ := (C₀ + 7) * (120 / (79 / 100) + 1 / Real.log (7 / 6)) with hK
  refine ⟨K, by positivity, fun s hs1 hs2 => ?_⟩
  set t : ℝ := s.im with ht
  set w : ℝ := s.re - 1 / 2 with hw
  have hw0 : 0 < w := by linarith
  set c₀ : ℂ := (7 / 5 : ℂ) + (t : ℂ) * I with hc₀
  have ht0 := abs_nonneg t
  set u : ℝ := |t| + 16 with hu
  set M : ℝ := 60 * (|t| + 5) ^ 2 * u ^ 5 / c with hM
  have hM0 : 0 ≤ M := by positivity
  set M₀ : ℝ := 1 + M with hM₀
  have hκ := hlow t
  have hZc0 : 0 < ‖Zc c₀‖ := lt_of_lt_of_le (by positivity) hκ
  have hZc0' : Zc c₀ ≠ 0 := norm_pos_iff.mp hZc0
  have hsphere : ∀ r : ℝ, r ≤ 553 / 400 → ∀ z ∈ Metric.sphere c₀ r, ‖Zc z / Zc c₀‖ ≤ M₀ := by
    intro r hr z hz
    rw [norm_div]
    have hg := zc_sphere_growth t hr hz
    have : ‖Zc z‖ / ‖Zc c₀‖ ≤ 60 * (|t| + 5) ^ 2 / (c / u ^ 5) :=
      div_le_div₀ (by positivity) hg (by positivity) hκ
    have hM' : 60 * (|t| + 5) ^ 2 / (c / u ^ 5) = M := by
      rw [hM]; field_simp
    linarith
  have hsc : ‖s - c₀‖ ≤ 23 / 20 * (79 / 100) := by
    have hsc' : s - c₀ = ((s.re - 7 / 5 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc₀, ht]
    rw [hsc', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist : ∀ ρ : ℂ, Zc ρ = 0 → ρ ∈ Metric.ball c₀ (3 / 2 * (79 / 100)) → w ≤ ‖s - ρ‖ := by
    intro ρ hρ hball
    have hb : ‖ρ - c₀‖ < 3 / 2 * (79 / 100) := by simpa [dist_eq_norm] using hball
    have hre : 0 < ρ.re := by
      have h := Complex.abs_re_le_norm (ρ - c₀)
      have : (ρ - c₀).re = ρ.re - 7 / 5 := by simp [hc₀]
      rw [this] at h
      have := (abs_le.mp (le_trans h hb.le)).1
      linarith
    have hhalf := zc_zero_re_half hRH hρ hre
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re, hhalf] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  have hmain := Salt.MR.near_norm_logDeriv_entire_le Zc_differentiable (lam := 79 / 100)
    (M₀ := M₀) (w := w) (c₀ := c₀) (s := s) (by norm_num) (by linarith) hw0 hZc0' hsc
    (zc_ne_zero_of_half_lt hRH hs1)
    (hsphere _ (by norm_num)) (hsphere _ (by norm_num)) hdist
  -- the size of `log (4 M₀)`
  set L : ℝ := Real.log (|t| + 3) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hu1 : 1 ≤ u := by linarith
  have h4M : 4 * M₀ ≤ 4 * (1 + 60 / c) * u ^ 7 := by
    have hp : (|t| + 5) ^ 2 * u ^ 5 ≤ u ^ 7 := by
      have : (|t| + 5) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc (|t| + 5) ^ 2 * u ^ 5 ≤ u ^ 2 * u ^ 5 := by gcongr
        _ = u ^ 7 := by ring
    have h1 : (1 : ℝ) ≤ u ^ 7 := one_le_pow₀ hu1
    have hM' : M ≤ 60 / c * u ^ 7 := by
      have : 60 / c * ((|t| + 5) ^ 2 * u ^ 5) ≤ 60 / c * u ^ 7 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      calc M = 60 / c * ((|t| + 5) ^ 2 * u ^ 5) := by rw [hM]; ring
        _ ≤ 60 / c * u ^ 7 := this
    nlinarith
  have hlogu : Real.log u ≤ Real.log 6 + L := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hX0 : 0 ≤ Real.log (4 * M₀) := Real.log_nonneg (by linarith)
  have hX : Real.log (4 * M₀) ≤ (C₀ + 7) * L := by
    have h1 : Real.log (4 * M₀) ≤ Real.log (4 * (1 + 60 / c) * u ^ 7) :=
      Real.log_le_log (by positivity) h4M
    have h2 : Real.log (4 * (1 + 60 / c) * u ^ 7)
        = Real.log (4 * (1 + 60 / c)) + 7 * Real.log u := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [h2] at h1
    nlinarith
  -- assemble
  have hfin : (120 / (79 / 100)) * Real.log (4 * M₀)
      + (Real.log (4 * M₀) / Real.log (7 / 6)) / w ≤ K * L * (1 + 1 / w) := by
    have hw' : 0 < 1 / w := by positivity
    have e1 : (120 / (79 / 100)) * Real.log (4 * M₀) ≤ (120 / (79 / 100)) * ((C₀ + 7) * L) :=
      mul_le_mul_of_nonneg_left hX (by norm_num)
    have e2 : (Real.log (4 * M₀) / Real.log (7 / 6)) / w
        ≤ ((C₀ + 7) * L / Real.log (7 / 6)) / w := by
      gcongr
    have e3 : K * L * (1 + 1 / w)
        = (120 / (79 / 100)) * ((C₀ + 7) * L) + ((C₀ + 7) * L / Real.log (7 / 6)) / w
          + (120 / (79 / 100)) * ((C₀ + 7) * L) * (1 / w)
          + ((C₀ + 7) * L / Real.log (7 / 6)) := by
      rw [hK]; field_simp; ring
    have e4 : 0 ≤ (120 / (79 / 100)) * ((C₀ + 7) * L) * (1 / w)
        + ((C₀ + 7) * L / Real.log (7 / 6)) := by positivity
    linarith
  linarith

end Salt.RH
