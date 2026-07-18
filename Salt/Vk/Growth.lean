/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaApprox

/-!
# VMVT-VK rung R6 (front end) — the approximate-formula O(1) reduction (`VK-GROWTH` stone 1)

`zeta_sub_dirichlet_bound` is the front end of the R6 growth ladder: at the truncation
`N = ⌈t²⌉`, on the strip `3/4 ≤ σ ≤ 3` and `t ≥ 100`, the ζ error and pole terms of the
approximate functional equation `Salt.ExpSum.norm_zeta_sub_approx_le` are both `O(1)`, so ζ is
within an absolute constant of its length-`⌈t²⌉` Dirichlet partial sum:

  `‖ζ(σ+it) − ∑_{n ≤ ⌈t²⌉} n^{−(σ+it)}‖ ≤ 4`.

This isolates the *analytic* head of R6 from the *arithmetic* body (the dyadic bound on the
Dirichlet sum via the phase-sum bounds of R5b + the landed tiles, tracked in
`docs/blueprints/flags.md`).  Error `‖s‖·N^{−σ}/σ`: `‖s‖ ≤ σ+t`, `N^{−σ} ≤ t^{−3/2}`, cancels to
`t^{−1/2}`-grade.  Pole `N^{1−σ}/‖s−1‖`: `‖s−1‖ ≥ t`, `N^{1−σ} ≤ (2t²)^{1/4}`, so `t^{−1/2}`-grade.
-/

namespace Salt.Vk

open Complex Salt.ExpSum

/-- **R6 front end — the approximate-formula O(1) reduction.**  On `3/4 ≤ σ ≤ 3`, `t ≥ 100`, ζ is
within `4` of its length-`⌈t²⌉` Dirichlet partial sum. -/
theorem zeta_sub_dirichlet_bound {σ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ3 : σ ≤ 3) (ht : 100 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)
        - ∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ 4 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have htpos : 0 < t := by linarith
  have hσpos : 0 < σ := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
  have hNt2 : t ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNt2u : (N : ℝ) ≤ 2 * t ^ 2 := by
    rw [hNdef]
    calc (⌈t ^ 2⌉₊ : ℝ) ≤ t ^ 2 + 1 := le_of_lt (Nat.ceil_lt_add_one (by positivity))
      _ ≤ 2 * t ^ 2 := by nlinarith [ht1]
  have hN1 : 1 ≤ N := by rw [hNdef, Nat.one_le_ceil_iff]; positivity
  have hNRpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the approximate functional equation
  have happrox := norm_zeta_sub_approx_le (s := s) (by rw [hsre]; exact hσpos)
    (by rw [hsim]; exact htpos) (N := N) hN1
  rw [hsre] at happrox
  -- crude rpow facts
  have hsqrt10 : (10 : ℝ) ≤ t ^ (1 / 2 : ℝ) := by
    have h100 : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, ← Real.rpow_natCast (10 : ℝ) 2,
        ← Real.rpow_mul (by norm_num)]; norm_num
    calc (10 : ℝ) = (100 : ℝ) ^ (1 / 2 : ℝ) := h100.symm
      _ ≤ t ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) ht (by norm_num)
  have hthalf : t ^ (-(1 / 2) : ℝ) ≤ 1 / 10 := by
    rw [Real.rpow_neg htpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos htpos _) (by norm_num)]
    rw [one_div, inv_inv]; exact hsqrt10
  -- ‖s‖ ≤ σ + t
  have hsnorm : ‖s‖ ≤ σ + t := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre, hsim, abs_of_pos hσpos, abs_of_pos htpos] at h; exact h
  -- ‖s − 1‖ ≥ t
  have hs1norm : t ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, hsim, Complex.one_im, sub_zero, abs_of_pos htpos] at h; exact h
  -- error term: N^{−σ} ≤ t^{−3/2}
  have hNσ : (N : ℝ) ^ (-σ) ≤ t ^ (-(3 / 2) : ℝ) := by
    have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(3 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR1 (by linarith)
    have h2 : (N : ℝ) ^ (-(3 / 4) : ℝ) ≤ (t ^ 2) ^ (-(3 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ht2pos hNt2 (by norm_num)
    have h3 : (t ^ 2) ^ (-(3 / 4) : ℝ) = t ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htpos.le]; norm_num
    rw [← h3]; exact le_trans h1 h2
  have httcancel : t * t ^ (-(3 / 2) : ℝ) = t ^ (-(1 / 2) : ℝ) := by
    have h : t ^ (1 : ℝ) * t ^ (-(3 / 2) : ℝ) = t ^ ((1 : ℝ) + -(3 / 2)) :=
      (Real.rpow_add htpos 1 (-(3 / 2))).symm
    rw [Real.rpow_one] at h; rw [h]; norm_num
  have herr : ‖s‖ * (N : ℝ) ^ (-σ) / σ ≤ 2 := by
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hNRpos.le _
    have hpost : (0 : ℝ) ≤ t ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg htpos.le _
    have hst : ‖s‖ * (N : ℝ) ^ (-σ) ≤ (σ + t) * t ^ (-(3 / 2) : ℝ) :=
      mul_le_mul hsnorm hNσ hnn (by positivity)
    have hchain : (σ + t) * t ^ (-(3 / 2) : ℝ) ≤ 2 * t ^ (-(1 / 2) : ℝ) := by
      calc (σ + t) * t ^ (-(3 / 2) : ℝ) ≤ (2 * t) * t ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hpost
        _ = 2 * (t * t ^ (-(3 / 2) : ℝ)) := by ring
        _ = 2 * t ^ (-(1 / 2) : ℝ) := by rw [httcancel]
    rw [div_le_iff₀ hσpos]
    calc ‖s‖ * (N : ℝ) ^ (-σ) ≤ 2 * t ^ (-(1 / 2) : ℝ) := le_trans hst hchain
      _ ≤ 2 * (1 / 10) := by nlinarith [hthalf]
      _ ≤ 2 * σ := by nlinarith [hσ]
  -- pole term: ‖N^{1−s}/(s−1)‖ = N^{1−σ}/‖s−1‖ ≤ 2
  have hpolenorm : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ = (N : ℝ) ^ (1 - σ) / ‖s - 1‖ := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega) (1 - s)]
    congr 2
    rw [Complex.sub_re, hsre, Complex.one_re]
  have hN1σ : (N : ℝ) ^ (1 - σ) ≤ 2 * t ^ (1 / 2 : ℝ) := by
    have h1 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR1 (by linarith)
    have h2 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (2 * t ^ 2) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hNRpos.le hNt2u (by norm_num)
    have h3 : (2 * t ^ 2) ^ (1 / 4 : ℝ) ≤ 2 * t ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      have h2q : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have ht2q : (t ^ 2) ^ (1 / 4 : ℝ) = t ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htpos.le]; norm_num
      rw [ht2q]
      have hnnt : (0 : ℝ) ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg htpos.le _
      nlinarith [h2q, hnnt]
    exact le_trans h1 (le_trans h2 h3)
  have hpole : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 2 := by
    rw [hpolenorm, div_le_iff₀ (lt_of_lt_of_le htpos hs1norm)]
    calc (N : ℝ) ^ (1 - σ) ≤ 2 * t ^ (1 / 2 : ℝ) := hN1σ
      _ = 2 * t ^ (1 / 2 : ℝ) := rfl
      _ ≤ 2 * ‖s - 1‖ := by
          have hnn : (0 : ℝ) ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg htpos.le _
          -- t^{1/2} ≤ t ≤ ‖s−1‖
          have hle1 : t ^ (1 / 2 : ℝ) ≤ t := by
            calc t ^ (1 / 2 : ℝ) ≤ t ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
              _ = t := Real.rpow_one t
          nlinarith [hle1, hs1norm]
  -- assemble: ‖ζ − D‖ ≤ ‖ζ − D − pole‖ + ‖pole‖ ≤ 2 + 2 = 4
  have htri : ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
      ≤ ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)‖
        + ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ := by
    have := norm_add_le
      (riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1))
      ((N : ℂ) ^ (1 - s) / (s - 1))
    simpa using this
  calc ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
      ≤ ‖s‖ * (N : ℝ) ^ (-σ) / σ + 2 := by
        refine le_trans htri (add_le_add happrox hpole)
    _ ≤ 2 + 2 := by linarith [herr]
    _ = 4 := by norm_num

end Salt.Vk
