/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.VonKoch
import Salt.SW.StripConvergence
import Salt.MR.ChiLLower
import Salt.MR.VkMidSharp

/-!
# O106 row R5b — the analytic inputs for `L(s, χ)` (nodes M1, M2, M3)

The ζ-side nodes N1–N3 (`Salt.RH.VonKoch`) ported to a non-principal Dirichlet character `χ` mod
`q`. `L(·, χ)` is entire for `χ ≠ 1`, so no `Zc`-style pole normalization is needed, and the same
λ-scaled Landau engine (`Salt.MR.near_norm_logDeriv_entire_le`, centre `7/5 + it`, `λ = 79/100`)
applies. The modulus enters only through `log q`.

* **M1** `LFunction_sphere_growth` — on any sphere about `7/5 + it` of radius `≤ 553/400`,
  `‖L(z, χ)‖ ≤ 61 q (|t| + 5)`.
* **M2** `LFunction_centre_lower` — `‖L(7/5 + it, χ)‖ ≥ 1/80`.
* **M3** `LFunction_logDeriv_near_half` — under `GRHDirichlet`, for `1/2 < Re s ≤ 23/10`,
  `‖logDeriv L(·, χ) s‖ ≤ K · log(q(|Im s| + 3)) · (1 + 1/(Re s − 1/2))`, `K` absolute.
-/

namespace Salt.RH

open Complex DirichletCharacter

/-- A non-principal character has modulus at least `2`. -/
theorem two_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    2 ≤ q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  by_contra h
  have hq1 : q = 1 := by omega
  exact hχ (level_one' χ hq1)

/-- **M1.** Sphere growth of `L(·, χ)` about `7/5 + it`, for every radius up to `553/400`. -/
theorem LFunction_sphere_growth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (t : ℝ) {r : ℝ} (hr : r ≤ 553 / 400) {z : ℂ}
    (hz : z ∈ Metric.sphere ((7 / 5 : ℂ) + (t : ℂ) * I) r) :
    ‖LFunction χ z‖ ≤ 61 * q * (|t| + 5) := by
  have hq2 := two_le_of_ne_one hχ
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
  set a : ℝ := |t| + 5 with ha
  have ha1 : 1 ≤ a := by have := abs_nonneg t; linarith
  have hz_le : ‖z‖ ≤ a := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    have : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith, hre_hi⟩
    linarith
  have hinv : 1 + 1 / z.re ≤ 59 := by
    have : 1 / z.re ≤ 400 / 7 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      linarith
    linarith
  have htail := Salt.SW.norm_LFunction_sub_partial_le χ hχ hq2
    (Salt.MR.norm_char_partial_sum_le χ hχ) hpos (N := 1) le_rfl
  have hpart : (∑ n ∈ Finset.Icc (1 : ℕ) 1, χ ((n : ℕ) : ZMod q) * ((n : ℕ) : ℂ) ^ (-z)) = 1 := by
    simp
  rw [hpart] at htail
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hN : ((1 : ℕ) : ℝ) ^ (-z.re) = 1 := by simp
  rw [hN, mul_one] at htail
  have hL : ‖LFunction χ z‖ ≤ 1 + q * (1 + ‖z‖ * (1 + 1 / z.re)) := by
    have h2 : ‖LFunction χ z‖ ≤ ‖LFunction χ z - 1‖ + 1 := by
      have := norm_sub_norm_le (LFunction χ z) 1
      rw [norm_one] at this
      linarith
    linarith
  have hprod : ‖z‖ * (1 + 1 / z.re) ≤ a * 59 := by
    have h0 : 0 ≤ 1 + 1 / z.re := by positivity
    exact mul_le_mul hz_le hinv h0 (by linarith)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have : (q : ℝ) * (1 + ‖z‖ * (1 + 1 / z.re)) ≤ q * (1 + a * 59) :=
    mul_le_mul_of_nonneg_left (by linarith) hq0
  nlinarith

/-- **M2.** The centre lower bound: `‖L(7/5 + it, χ)‖ ≥ 1/80`, for every character and every `t`. -/
theorem LFunction_centre_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 80 : ℝ) ≤ ‖LFunction χ ((7 / 5 : ℂ) + (t : ℂ) * I)‖ := by
  have h := Salt.MR.LFunction_near_one_lower χ (d := 2 / 5) (t := t) (by norm_num) (by norm_num)
  have hs : (((1 + 2 / 5 : ℝ) : ℝ) : ℂ) + (t : ℂ) * I = (7 / 5 : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  rw [hs] at h
  linarith

/-! ## GRH, read on `L(·, χ)` -/

/-- Under GRH, a zero of `L(·, χ)` (`χ ≠ 1`) in `Re > 0` lies on the critical line. -/
theorem LFunction_zero_re_half (hGRH : GRHDirichlet) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ} (hρ : LFunction χ ρ = 0)
    (hre : 0 < ρ.re) : ρ.re = 1 / 2 := by
  rcases lt_or_ge ρ.re 1 with h1 | h1
  · exact hGRH q χ ρ hρ hre h1
  · exact absurd hρ (LFunction_ne_zero_of_one_le_re χ (.inl hχ) h1)

/-- Under GRH, `L(·, χ)` (`χ ≠ 1`) does not vanish on `Re > 1/2`. -/
theorem LFunction_ne_zero_of_half_lt (hGRH : GRHDirichlet) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    LFunction χ s ≠ 0 := by
  intro h
  have := LFunction_zero_re_half hGRH hχ h (by linarith)
  linarith

/-! ## M3 — the bound on `logDeriv L(·, χ)` near the critical line, under GRH -/

/-- **M3.** Under GRH, for every `χ ≠ 1` mod `q` and `1/2 < Re s ≤ 23/10`,
`‖logDeriv L(·, χ) s‖ ≤ K · log(q(|Im s| + 3)) · (1 + 1/(Re s − 1/2))`, with `K` absolute. -/
theorem LFunction_logDeriv_near_half (hGRH : GRHDirichlet) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
        ‖logDeriv (LFunction χ) s‖
          ≤ K * Real.log (q * (|s.im| + 3)) * (1 + 1 / (s.re - 1 / 2)) := by
  set C₀ : ℝ := Real.log 39048 + 1 with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have : 0 ≤ Real.log 39048 := Real.log_nonneg (by norm_num)
    linarith
  have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  set K : ℝ := C₀ * (120 / (79 / 100) + 1 / Real.log (7 / 6)) with hK
  have hK0 : 0 < K := by
    have : 0 < C₀ := by
      have : 0 ≤ Real.log 39048 := Real.log_nonneg (by norm_num)
      linarith
    positivity
  refine ⟨K, hK0, fun q _ χ hχ s hs1 hs2 => ?_⟩
  have hq2 := two_le_of_ne_one hχ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  set t : ℝ := s.im with ht
  set w : ℝ := s.re - 1 / 2 with hw
  have hw0 : 0 < w := by linarith
  set c₀ : ℂ := (7 / 5 : ℂ) + (t : ℂ) * I with hc₀
  have ht0 := abs_nonneg t
  set a : ℝ := |t| + 5 with ha
  set M₀ : ℝ := 1 + 80 * (61 * q * a) with hM₀
  have hκ := LFunction_centre_lower χ t
  have hL0 : 0 < ‖LFunction χ c₀‖ := lt_of_lt_of_le (by norm_num) hκ
  have hL0' : LFunction χ c₀ ≠ 0 := norm_pos_iff.mp hL0
  have hsphere : ∀ r : ℝ, r ≤ 553 / 400 → ∀ z ∈ Metric.sphere c₀ r,
      ‖LFunction χ z / LFunction χ c₀‖ ≤ M₀ := by
    intro r hr z hz
    rw [norm_div]
    have hg := LFunction_sphere_growth hχ t hr hz
    have : ‖LFunction χ z‖ / ‖LFunction χ c₀‖ ≤ 61 * q * a / (1 / 80) :=
      div_le_div₀ (by positivity) hg (by norm_num) hκ
    have hM' : 61 * q * a / (1 / 80 : ℝ) = 80 * (61 * q * a) := by ring
    linarith
  have hsc : ‖s - c₀‖ ≤ 23 / 20 * (79 / 100) := by
    have hsc' : s - c₀ = ((s.re - 7 / 5 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc₀, ht]
    rw [hsc', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ ∈ Metric.ball c₀ (3 / 2 * (79 / 100)) →
      w ≤ ‖s - ρ‖ := by
    intro ρ hρ hball
    have hb : ‖ρ - c₀‖ < 3 / 2 * (79 / 100) := by simpa [dist_eq_norm] using hball
    have hre : 0 < ρ.re := by
      have h := Complex.abs_re_le_norm (ρ - c₀)
      have : (ρ - c₀).re = ρ.re - 7 / 5 := by simp [hc₀]
      rw [this] at h
      have := (abs_le.mp (le_trans h hb.le)).1
      linarith
    have hhalf := LFunction_zero_re_half hGRH hχ hρ hre
    have h := Complex.abs_re_le_norm (s - ρ)
    rw [Complex.sub_re, hhalf] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  have hM₀1 : 1 ≤ M₀ := by
    have : 0 ≤ 80 * (61 * q * a) := by positivity
    linarith
  have hmain := Salt.MR.near_norm_logDeriv_entire_le (differentiable_LFunction hχ)
    (lam := 79 / 100) (M₀ := M₀) (w := w) (c₀ := c₀) (s := s) (by norm_num) hM₀1 hw0 hL0' hsc
    (LFunction_ne_zero_of_half_lt hGRH hχ hs1)
    (hsphere _ (by norm_num)) (hsphere _ (by norm_num)) hdist
  -- the size of `log (4 M₀)`
  set L : ℝ := Real.log (q * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have h4M : 4 * M₀ ≤ 39048 * (q * (|t| + 3)) := by
    have ha2 : a ≤ 2 * (|t| + 3) := by rw [ha]; linarith
    have hqa : 1 ≤ q * a := by nlinarith
    have : q * a ≤ q * (2 * (|t| + 3)) := mul_le_mul_of_nonneg_left ha2 (by linarith)
    rw [hM₀]
    nlinarith
  have hX0 : 0 ≤ Real.log (4 * M₀) := Real.log_nonneg (by linarith)
  have hX : Real.log (4 * M₀) ≤ C₀ * L := by
    have h1 : Real.log (4 * M₀) ≤ Real.log (39048 * (q * (|t| + 3))) :=
      Real.log_le_log (by positivity) h4M
    rw [Real.log_mul (x := (39048 : ℝ)) (y := (q : ℝ) * (|t| + 3)) (by norm_num) (by positivity),
      ← hL] at h1
    have : 0 ≤ Real.log 39048 := Real.log_nonneg (by norm_num)
    rw [hC₀]
    nlinarith
  -- assemble
  have hfin : (120 / (79 / 100)) * Real.log (4 * M₀)
      + (Real.log (4 * M₀) / Real.log (7 / 6)) / w ≤ K * L * (1 + 1 / w) := by
    have e1 : (120 / (79 / 100)) * Real.log (4 * M₀) ≤ (120 / (79 / 100)) * (C₀ * L) :=
      mul_le_mul_of_nonneg_left hX (by norm_num)
    have e2 : (Real.log (4 * M₀) / Real.log (7 / 6)) / w
        ≤ (C₀ * L / Real.log (7 / 6)) / w := by
      gcongr
    have e3 : K * L * (1 + 1 / w)
        = (120 / (79 / 100)) * (C₀ * L) + (C₀ * L / Real.log (7 / 6)) / w
          + (120 / (79 / 100)) * (C₀ * L) * (1 / w)
          + (C₀ * L / Real.log (7 / 6)) := by
      rw [hK]; field_simp; ring
    have e4 : 0 ≤ (120 / (79 / 100)) * (C₀ * L) * (1 / w)
        + (C₀ * L / Real.log (7 / 6)) := by
      have : 0 ≤ C₀ * L := by positivity
      positivity
    linarith
  linarith

end Salt.RH
