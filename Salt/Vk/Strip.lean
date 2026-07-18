/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.DerivTest
import Salt.ExpSum.ZetaBlock

/-!
# VMVT-VK rung R10 — the strip-covering patch (`VK-STRIP-PATCH`, LITT-COVER stone-3)

`zeta_block_strip` covers the diagonal strip `N ≤ t ≤ 27π·N` — where `t` is comparable to the
block scale `N`, the regime the first-derivative (Kušmin) tile and the VK block machine do not
reach — with a second-derivative (van der Corput) `√N`-grade bound:
`‖∑_{N < n ≤ 2N} eR(phi t n)‖ ≤ 112·√N`.

The ζ-phase `phi t n = −(t/2π)·log n` has second difference
`d²(n) = (t/2π)·(2 log(n+1) − log(n+2) − log n) = (t/2π)·log(1 + 1/(n(n+2)))`, sandwiched in
`[(t/2π)/(n+1)², (t/2π)/(n(n+2))]` by `Real.log_le_sub_one_of_pos` applied to the ratio and its
reciprocal.  With `μ = (t/2π)/(4N²)` and spread constant `c = 4` this feeds
`Salt.ExpSum.vdC_2nd_ZR` (the ℤ/`eR` second-derivative test), whose output `8(4N√μ + 1/√μ) =
16√(t/2π) + 16N/√(t/2π)` is `≤ 112√N` throughout the strip (`t/2π ≤ 16N` and `N ≤ 9·t/2π`).

R10 = LITT-COVER stone-3, independently valuable: it closes the last (`≤ 7`-block) seam of the
dyadic zeta growth ladder at the height where `t ≍ N`.
-/

namespace Salt.Vk

open Salt.ExpSum Real Finset

/-- The ζ-phase second difference, upper half: `2 log(m+1) − log(m+2) − log m ≤ 1/(m(m+2))`
(via `log(1 + 1/(m(m+2))) ≤ 1/(m(m+2))`). -/
lemma log_2diff_upper {m : ℝ} (hm : 0 < m) :
    2 * Real.log (m + 1) - Real.log (m + 2) - Real.log m ≤ 1 / (m * (m + 2)) := by
  have h2 : (0 : ℝ) < m + 2 := by linarith
  have hcombine : 2 * Real.log (m + 1) - Real.log (m + 2) - Real.log m
      = Real.log ((m + 1) ^ 2 / (m * (m + 2))) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (ne_of_gt hm) (ne_of_gt h2),
      Real.log_pow]
    push_cast; ring
  rw [hcombine]
  have hpos : (0 : ℝ) < (m + 1) ^ 2 / (m * (m + 2)) := by positivity
  have hle := Real.log_le_sub_one_of_pos hpos
  have heq : (m + 1) ^ 2 / (m * (m + 2)) - 1 = 1 / (m * (m + 2)) := by field_simp; ring
  rw [heq] at hle; exact hle

/-- The ζ-phase second difference, lower half: `1/(m+1)² ≤ 2 log(m+1) − log(m+2) − log m`
(via `log((m+1)²/(m(m+2)))⁻¹ ≤ (m(m+2)/(m+1)²) − 1 = −1/(m+1)²`). -/
lemma log_2diff_lower {m : ℝ} (hm : 0 < m) :
    1 / (m + 1) ^ 2 ≤ 2 * Real.log (m + 1) - Real.log (m + 2) - Real.log m := by
  have h2 : (0 : ℝ) < m + 2 := by linarith
  have hcombine : 2 * Real.log (m + 1) - Real.log (m + 2) - Real.log m
      = Real.log ((m + 1) ^ 2 / (m * (m + 2))) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (ne_of_gt hm) (ne_of_gt h2),
      Real.log_pow]
    push_cast; ring
  rw [hcombine]
  have hpos : (0 : ℝ) < m * (m + 2) / (m + 1) ^ 2 := by positivity
  have hle := Real.log_le_sub_one_of_pos hpos
  have hinv : Real.log (m * (m + 2) / (m + 1) ^ 2)
      = -Real.log ((m + 1) ^ 2 / (m * (m + 2))) := by
    rw [← Real.log_inv ((m + 1) ^ 2 / (m * (m + 2))), inv_div]
  have heq : m * (m + 2) / (m + 1) ^ 2 - 1 = -(1 / (m + 1) ^ 2) := by field_simp; ring
  rw [hinv, heq] at hle; linarith [hle]

/-- **R10 — the strip-covering patch.**  On the diagonal strip `N ≤ t ≤ 27π·N`, the ζ-phase block
sum obeys the second-derivative `√N`-grade bound `‖∑_{N < n ≤ 2N} eR(phi t n)‖ ≤ 112·√N`. -/
theorem zeta_block_strip {t : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ 27 * π * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖ ≤ 112 * Real.sqrt (N : ℝ) := by
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0R
  have htpos : 0 < t := by linarith
  have hπpos : 0 < π := Real.pi_pos
  set A : ℝ := t / (2 * π) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set μ : ℝ := A / (4 * (N : ℝ) ^ 2) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  -- the second-difference identity for the ζ-phase
  have hd2 : ∀ n : ℤ, (phi t (n + 2) - phi t (n + 1)) - (phi t (n + 1) - phi t n)
      = A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
    intro n; simp only [Salt.ExpSum.phi, ← hA]; push_cast; ring
  -- the two second-difference bounds feeding the vdC test
  have hlb : ∀ n : ℤ, (N : ℤ) < n → n < 2 * N →
      μ ≤ (phi t (n + 2) - phi t (n + 1)) - (phi t (n + 1) - phi t n) := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (N : ℝ) + 1 ≤ (n : ℝ) := by
      have : (N : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hll := log_2diff_lower hmpos
    have hnu : (n : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : n + 1 ≤ 2 * (N : ℤ) := by omega
      exact_mod_cast this
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith [hnu, hN0R]
    have hstep1 : μ ≤ A / ((n : ℝ) + 1) ^ 2 := by
      rw [hμ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hsq, hA0.le]
    have heq2 : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
    have hstep2 : A / ((n : ℝ) + 1) ^ 2
        ≤ A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hll hA0.le
    linarith [hstep1, hstep2]
  have hub : ∀ n : ℤ, (N : ℤ) < n → n < 2 * N →
      (phi t (n + 2) - phi t (n + 1)) - (phi t (n + 1) - phi t n) ≤ 4 * μ := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (N : ℝ) + 1 ≤ (n : ℝ) := by
      have : (N : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlu := log_2diff_upper hmpos
    have hNsq : (N : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 2) := by nlinarith [hnR1, hN0R]
    have heq2 : A / ((n : ℝ) * ((n : ℝ) + 2)) = A * (1 / ((n : ℝ) * ((n : ℝ) + 2))) := by ring
    have hstep1 : A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ))
        ≤ A / ((n : ℝ) * ((n : ℝ) + 2)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hlu hA0.le
    have h4μ : 4 * μ = A / (N : ℝ) ^ 2 := by rw [hμ]; ring
    have hstep2 : A / ((n : ℝ) * ((n : ℝ) + 2)) ≤ 4 * μ := by
      rw [h4μ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hNsq, hA0.le]
    linarith [hstep1, hstep2]
  -- the vdC second-derivative test
  have hab : (N : ℤ) ≤ 2 * N := by omega
  have hvdc := vdC_2nd_ZR (phi t) (N : ℤ) (2 * N) μ 4 hab hμ0 (by norm_num) hlb hub
  refine le_trans hvdc ?_
  -- sqrt algebra: 8(4N√μ + 1/√μ) = 16√A + 16N/√A ≤ 112√N
  have hsm : Real.sqrt μ = Real.sqrt A / (2 * (N : ℝ)) := by
    rw [hμ, show A / (4 * (N : ℝ) ^ 2) = A * (1 / (2 * (N : ℝ))) ^ 2 from by field_simp; ring,
      Real.sqrt_mul hA0.le, Real.sqrt_sq (by positivity)]
    ring
  have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hterm1 : 4 * (N : ℝ) * Real.sqrt μ = 2 * Real.sqrt A := by rw [hsm]; field_simp; ring
  have hterm2 : 1 / Real.sqrt μ = 2 * (N : ℝ) / Real.sqrt A := by rw [hsm, one_div, inv_div]
  have hc : ((2 * (N : ℤ) : ℤ) : ℝ) - ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  -- bound (a): 2√A ≤ 8√N  (from A ≤ 16N)
  have hb1 : 2 * Real.sqrt A ≤ 8 * Real.sqrt (N : ℝ) := by
    have hAle16 : A ≤ 16 * (N : ℝ) := by
      rw [hA, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)]; nlinarith [htN, hπpos, hN0R]
    have h16 : Real.sqrt (16 * (N : ℝ)) = 4 * Real.sqrt N := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
        show Real.sqrt 16 = 4 from by
          rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    have : Real.sqrt A ≤ 4 * Real.sqrt N :=
      le_trans (Real.sqrt_le_sqrt hAle16) (le_of_eq h16)
    linarith
  -- bound (b): 2N/√A ≤ 6√N  (from N ≤ 9A)
  have hb2 : 2 * (N : ℝ) / Real.sqrt A ≤ 6 * Real.sqrt (N : ℝ) := by
    have h2pi9 : 2 * π ≤ 9 := by nlinarith [Real.pi_le_four]
    have hNle9 : (N : ℝ) ≤ 9 * A := by
      rw [hA, show (9 : ℝ) * (t / (2 * π)) = 9 * t / (2 * π) from by ring,
        le_div_iff₀ (by positivity)]
      nlinarith [hNt, h2pi9, hN0R]
    have hb2' : (N : ℝ) / Real.sqrt A ≤ 3 * Real.sqrt N := by
      have h1 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt A := by positivity
      have h2 : (0 : ℝ) ≤ 3 * Real.sqrt N := by positivity
      have hsq : ((N : ℝ) / Real.sqrt A) ^ 2 ≤ (3 * Real.sqrt N) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hA0.le, mul_pow, Real.sq_sqrt hN0R.le, div_le_iff₀ hA0]
        nlinarith [hNle9, hN0R]
      calc (N : ℝ) / Real.sqrt A = Real.sqrt (((N : ℝ) / Real.sqrt A) ^ 2) := (Real.sqrt_sq h1).symm
        _ ≤ Real.sqrt ((3 * Real.sqrt N) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 3 * Real.sqrt N := Real.sqrt_sq h2
    rw [mul_div_assoc]; linarith [hb2']
  rw [hc, hterm1, hterm2]
  linarith [hb1, hb2]

end Salt.Vk
