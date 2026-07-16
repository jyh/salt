/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.ZetaPartialFractions

/-!
# The vertical log bound for `ζ` near the 1-line (SW node A2a / N1)

Design: `docs/exploration/s2-trackA-design.md` (node A2a/N1). This module supplies the sharp
"polynomial-in-`log`" size bound

`‖ζ(σ + it)‖ ≤ C · log(|t|+2)`  on the range  `1 − 1/log(|t|+2) ≤ σ`,  `2 ≤ |t|`,

feeding the 3-4-1 lower-bound route (T-lo). Mathlib has **no** complex `ζ` growth bound on vertical
strips; the polynomial `M0zeta` in `Salt/SW/ZetaPartialFractions.lean` is the wrong shape near
`Re = 1`. We refine it by the classical truncated-series / Euler–Maclaurin estimate: with the pole
subtracted (`Zc_eq_series`), `ζ(s) = 1/(s−1) + ∑'_{m≥1} dTerm s m`, and cutting the Abel tail at
`N ~ |t|` gives

`ζ(s) = ∑_{n=1}^{N} n^{−s} + (N+1)^{1−s}/(s−1) + ∑_{m>N} dTerm s m`.

On `n ≤ N ~ |t|` and `σ ≥ 1 − 1/log(|t|+2)` each `n^{1−σ} ≤ e`, so the main sum is `≤ e(1+log N)`
(mathlib's `harmonic_le_one_add_log`); the boundary term is `≤ e/|t|`; the truncation remainder is
`‖s‖·N^{−σ}/σ = O(1)` (the `‖s‖ ~ |t|` cancels the `N^{−σ} ~ e/|t|`). The constants are free.

III.3″ witness (as designed): at `t = 10⁶`, `σ = 1 − 1/13.8`, the main sum `≤ e·(1+log 10⁶) ≈ 40`,
and the assembled `C = 36` clears it against `log(10⁶+2) ≈ 13.8` (`36·13.8 ≈ 497 ≥ 40 + O(1)`).

## Mathlib consumed
* `harmonic_le_one_add_log`, `AntitoneOn.sum_le_integral_Ico`, `integral_rpow`,
  `Real.tsum_le_of_sum_range_le`, `norm_natCast_cpow_of_pos`, `Complex.norm_le_abs_re_add_abs_im`,
  `Real.exp_one_lt_d9`, `Real.log_two_gt_d9`.
* Reused scaffolding (`Salt.SW`): `Zc_eq_series`, `dTerm_split`, `intPow_ftc`, `intPow_ii`,
  `dTerm_norm_le`, `dTerm_norm_summable`, `dTerm_summable_shift`.
-/

namespace Salt.SW

open Complex Set Filter intervalIntegral MeasureTheory Finset
open scoped Topology

/-! ## Elementary `rpow` facts near the 1-line -/

/-- If `1 ≤ x`, `log x ≤ L`, and `(1−σ)·L ≤ 1`, then `x^{1−σ} ≤ e`.  (On `n ≤ N ~ |t|` with
`σ ≥ 1 − 1/L` this is `n^{1−σ} ≤ N^{1/L} ≤ e`.) -/
lemma rpow_one_sub_le_exp {x σ L : ℝ} (hx1 : 1 ≤ x) (hℓL : Real.log x ≤ L)
    (haL : (1 - σ) * L ≤ 1) : x ^ (1 - σ) ≤ Real.exp 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hℓ0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  rcases le_or_gt (1 - σ) 0 with hane | hapos
  · nlinarith [mul_nonneg (neg_nonneg.mpr hane) hℓ0]
  · nlinarith [mul_le_mul_of_nonneg_left hℓL (le_of_lt hapos), haL]

/-- The `n^{−σ} ≤ e·n^{−1}` refinement used on the main sum and the truncation remainder. -/
lemma rpow_neg_le_exp_mul_inv {x σ L : ℝ} (hx1 : 1 ≤ x) (hℓL : Real.log x ≤ L)
    (haL : (1 - σ) * L ≤ 1) : x ^ (-σ) ≤ Real.exp 1 * x⁻¹ := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hsplit : x ^ (-σ) = x ^ (1 - σ) * x⁻¹ := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0, show (1 - σ) + (-1) = -σ by ring]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (rpow_one_sub_le_exp hx1 hℓL haL) (inv_nonneg.mpr hx0.le)

/-- The truncation-remainder `p`-series tail bound: `∑'_{n} (n+N+1)^{−(σ+1)} ≤ N^{−σ}/σ`
(integral comparison, `AntitoneOn.sum_le_integral_Ico` + `integral_rpow`). -/
lemma tail_psum_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1)) ≤ (N : ℝ) ^ (-σ) / σ := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : -(σ + 1) < -1 := by linarith
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) (fun K => ?_)
  -- Antitonicity of `u ↦ u^{−(σ+1)}` on `[N, N+K]`.
  have hf_anti : AntitoneOn (fun u : ℝ => u ^ (-(σ + 1))) (Set.Icc (N : ℝ) ((N + K : ℕ) : ℝ)) := by
    intro u hu v hv huv
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_trans hNR hu.1)) huv (by linarith)
  have hsum_int := AntitoneOn.sum_le_integral_Ico (a := N) (b := N + K)
    (f := fun u : ℝ => u ^ (-(σ + 1))) (Nat.le_add_right N K) hf_anti
  -- reindex the range-`K` sum to `Ico N (N+K)`
  have hreindex : ∑ n ∈ Finset.range K, ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1))
      = ∑ i ∈ Finset.Ico N (N + K), ((i + 1 : ℕ) : ℝ) ^ (-(σ + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega
  -- integrand hypotheses for `integral_rpow`
  have hrne : -(σ + 1) ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (N : ℝ) ((N + K : ℕ) : ℝ) := by
    intro hmem
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_add_right N K), Set.mem_Icc] at hmem
    linarith [hmem.1]
  calc ∑ n ∈ Finset.range K, ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1))
      = ∑ i ∈ Finset.Ico N (N + K), ((i + 1 : ℕ) : ℝ) ^ (-(σ + 1)) := hreindex
    _ ≤ ∫ x in (N : ℝ)..((N + K : ℕ) : ℝ), x ^ (-(σ + 1)) := hsum_int
    _ = (((N + K : ℕ) : ℝ) ^ (-(σ + 1) + 1) - (N : ℝ) ^ (-(σ + 1) + 1)) / (-(σ + 1) + 1) :=
        integral_rpow (Or.inr ⟨hrne, h0⟩)
    _ ≤ (N : ℝ) ^ (-σ) / σ := by
        rw [show -(σ + 1) + 1 = -σ by ring]
        have heq : (((N + K : ℕ) : ℝ) ^ (-σ) - (N : ℝ) ^ (-σ)) / (-σ)
            = ((N : ℝ) ^ (-σ) - ((N + K : ℕ) : ℝ) ^ (-σ)) / σ := by
          rw [div_neg, ← neg_div, neg_sub]
        rw [heq]
        apply div_le_div_of_nonneg_right _ hσ.le
        have : (0 : ℝ) ≤ ((N + K : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
        linarith

/-! ## The vertical log bound -/

set_option maxHeartbeats 1000000 in
-- The truncated-series identity and all three size bounds are one elaboration unit; the default
-- 200k heartbeats do not cover it.
/-- **The vertical log bound for `ζ` near the 1-line (node A2a / N1).**  For `σ` in the sharp
range `1 − 1/log(|t|+2) ≤ σ` (no upper bound — for `σ ≥ 1` the estimate degrades gracefully) and
`2 ≤ |t|`, `‖ζ(σ+it)‖ ≤ 36·log(|t|+2)`.

Route (the recon's truncated series):
`ζ(s) = ∑_{n≤N} n^{−s} + (N+1)^{1−s}/(s−1) + ∑_{m>N} dTerm s m` with `N = ⌊|t|⌋`; the main sum is
`≤ e(1+log N)` (`rpow_one_sub_le_exp` + `harmonic_le_one_add_log`), the boundary term `≤ e/|t| ≤ e`,
the truncation remainder `‖s‖·N^{−σ}/σ ≤ 9e` (`tail_psum_le`). -/
theorem zeta_log_bound :
    ∃ C : ℝ, ∀ (σ t : ℝ), 1 - 1 / Real.log (|t| + 2) ≤ σ → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + 2) := by
  refine ⟨36, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set L : ℝ := Real.log (|t| + 2) with hL
  have hsre : s.re = σ := by rw [hs]; simp [Complex.add_re, Complex.mul_re]
  have hsim : s.im = t := by rw [hs]; simp [Complex.add_im, Complex.mul_im]
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  have hs_ne1 : s ≠ 1 := by
    intro h; apply ht0; have h2 := hsim; rw [h] at h2; simpa using h2.symm
  -- Facts about `L = log(|t|+2)`.
  have hLge_log4 : Real.log 4 ≤ L := by rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hlog4 : (4 : ℝ) / 3 < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; nlinarith [h2]
  have hLge43 : (4 : ℝ) / 3 ≤ L := le_of_lt (lt_of_lt_of_le hlog4 hLge_log4)
  have hLpos : 0 < L := by linarith
  have hLge1 : (1 : ℝ) ≤ L := by linarith
  -- Facts about `σ`.
  have hσ14 : (1 : ℝ) / 4 ≤ σ := by
    have h34 : 1 / L ≤ 3 / 4 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hσpos : 0 < σ := by linarith
  have haL : (1 - σ) * L ≤ 1 := by
    have h1σ : 1 - σ ≤ 1 / L := by linarith
    calc (1 - σ) * L ≤ (1 / L) * L := mul_le_mul_of_nonneg_right h1σ hLpos.le
      _ = 1 := by field_simp
  have hσ0 : 0 < s.re := by rw [hsre]; exact hσpos
  -- The cut `N = ⌊|t|⌋`.
  set N : ℕ := ⌊|t|⌋₊ with hN_def
  have hNle : (N : ℝ) ≤ |t| := by rw [hN_def]; exact Nat.floor_le (abs_nonneg t)
  have hNlt : |t| < (N : ℝ) + 1 := by rw [hN_def]; exact Nat.lt_floor_add_one |t|
  have hN1 : 1 ≤ N := by
    rw [hN_def]; exact Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ |t| by linarith))
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNhalf : |t| / 2 ≤ (N : ℝ) := by linarith
  have hlogN : Real.log (N : ℝ) ≤ L := by
    rw [hL]; exact Real.log_le_log hNpos (by linarith)
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) (by linarith)
  -- The truncated identity `ζ(s) = Main + Boundary + Tail`.
  have hZcser : Zc s = 1 + (s - 1) * ∑' n : ℕ, dTerm s (n + 1) := Zc_eq_series s hσ0
  have hZcval : Zc s = (s - 1) * riemannZeta s := Zc_eq_of_ne hs_ne1
  have hs1ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne1
  have h1sne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun h => hs_ne1 h.symm)
  have hzeta : riemannZeta s = 1 / (s - 1) + ∑' n : ℕ, dTerm s (n + 1) := by
    have h : (s - 1) * riemannZeta s = 1 + (s - 1) * ∑' n : ℕ, dTerm s (n + 1) := by
      rw [← hZcval, hZcser]
    field_simp
    linear_combination h
  have hRsplit : (∑ n ∈ Finset.range N, dTerm s (n + 1)) + ∑' n : ℕ, dTerm s (n + N + 1)
      = ∑' n : ℕ, dTerm s (n + 1) := (dTerm_summable_shift s hσ0).sum_add_tsum_nat_add N
  have hPeq : (∑ n ∈ Finset.range N, dTerm s (n + 1))
      = (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..((N : ℝ) + 1), (u : ℂ) ^ (-s) := by
    rw [Finset.sum_congr rfl (fun n _ => dTerm_split s (Nat.le_add_left 1 n)),
      Finset.sum_sub_distrib]
    congr 1
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => (k : ℝ) + 1)
      (f := fun u : ℝ => (u : ℂ) ^ (-s)) (n := N)
      (fun k _ => by exact intPow_ii s (by positivity) (by positivity))
    simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at hadj
    rw [← hadj]
    apply Finset.sum_congr rfl
    intro k _
    congr 1 <;> push_cast <;> ring
  have hIntg := intPow_ftc s hs_ne1 (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith)
  have hident : riemannZeta s
      = (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
        + (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
        + ∑' n : ℕ, dTerm s (n + N + 1) := by
    rw [hzeta, ← hRsplit, hPeq, hIntg]
    field_simp
    ring
  -- Triangle inequality.
  have htri : ‖riemannZeta s‖
      ≤ ‖∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)‖
        + ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
        + ‖∑' n : ℕ, dTerm s (n + N + 1)‖ := by
    rw [hident]
    calc ‖(∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
            + (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)
            + ∑' n : ℕ, dTerm s (n + N + 1)‖
        ≤ ‖(∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
            + (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
          + ‖∑' n : ℕ, dTerm s (n + N + 1)‖ := norm_add_le _ _
      _ ≤ _ := by
          have := norm_add_le (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s))
            ((((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1))
          linarith
  -- (A) the main sum.
  have hMain : ‖∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp 1 * (1 + L) := by
    have hterm : ∀ n ∈ Finset.range N,
        ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp 1 * ((n + 1 : ℕ) : ℝ)⁻¹ := by
      intro n hn
      rw [norm_natCast_cpow_of_pos (Nat.succ_pos n) (-s), Complex.neg_re, hsre]
      refine rpow_neg_le_exp_mul_inv ?_ ?_ haL
      · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      · rw [hL]
        apply Real.log_le_log (by positivity)
        have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
        have hle : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
        linarith
    calc ‖∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.range N, ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, Real.exp 1 * ((n + 1 : ℕ) : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = Real.exp 1 * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ := by rw [← Finset.mul_sum]
      _ = Real.exp 1 * (harmonic N : ℝ) := by
          congr 1
          simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ Real.exp 1 * (1 + L) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
          have h2 : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
          linarith
  -- (B) the boundary term.
  have hbNpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hden : |t| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero, hsim] at h
    exact h
  have hbpos : (0 : ℝ) < ‖s - 1‖ := by linarith
  have hnum : ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbNpos, Complex.sub_re, Complex.one_re, hsre]
  have hnum_le : ((N : ℝ) + 1) ^ (1 - σ) ≤ Real.exp 1 :=
    rpow_one_sub_le_exp (by linarith) hlogN1 haL
  have hB : ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ Real.exp 1 := by
    rw [norm_div, hnum, div_le_iff₀ hbpos]
    exact hnum_le.trans (le_mul_of_one_le_right (Real.exp_pos 1).le (by linarith))
  -- (C) the truncation remainder.
  have hTsummable : Summable (fun n : ℕ => ‖dTerm s (n + N + 1)‖) :=
    (summable_nat_add_iff N).2 (dTerm_norm_summable s hσ0)
  have hpsum_summable : Summable (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1))) := by
    have hbase : Summable (fun m : ℕ => (m : ℝ) ^ (-(σ + 1))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (summable_nat_add_iff (N + 1)).2 hbase
  have hTerm : ∀ n : ℕ, ‖dTerm s (n + N + 1)‖ ≤ ‖s‖ * ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1)) := by
    intro n
    have h := dTerm_norm_le s hσ0 (m := n + N + 1) (by omega)
    rwa [hsre] at h
  have hchain : ‖∑' n : ℕ, dTerm s (n + N + 1)‖ ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) := by
    calc ‖∑' n : ℕ, dTerm s (n + N + 1)‖
        ≤ ∑' n : ℕ, ‖dTerm s (n + N + 1)‖ := norm_tsum_le_tsum_norm hTsummable
      _ ≤ ∑' n : ℕ, ‖s‖ * ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1)) :=
          hTsummable.tsum_le_tsum hTerm (hpsum_summable.mul_left _)
      _ = ‖s‖ * ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-(σ + 1)) := tsum_mul_left
      _ ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) :=
          mul_le_mul_of_nonneg_left (tail_psum_le hσpos hN1) (norm_nonneg s)
  have hsn : ‖s‖ ≤ σ + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre, hsim, abs_of_pos hσpos] at h
    exact h
  have hNσ : (N : ℝ) ^ (-σ) ≤ Real.exp 1 * (N : ℝ)⁻¹ := rpow_neg_le_exp_mul_inv hNR hlogN haL
  have hNσ2 : (N : ℝ) * (N : ℝ) ^ (-σ) ≤ Real.exp 1 := by
    calc (N : ℝ) * (N : ℝ) ^ (-σ) ≤ (N : ℝ) * (Real.exp 1 * (N : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hNσ hNpos.le
      _ = Real.exp 1 := by field_simp
  have key : σ + |t| ≤ 9 * ((N : ℝ) * σ) := by
    nlinarith [hσ14, hNhalf, ht, mul_nonneg (show (0 : ℝ) ≤ 9 * (N : ℝ) - 1 by linarith)
      (show (0 : ℝ) ≤ σ - 1 / 4 by linarith)]
  have hTailbound : ‖s‖ * ((N : ℝ) ^ (-σ) / σ) ≤ 9 * Real.exp 1 := by
    rw [← mul_div_assoc, div_le_iff₀ hσpos]
    calc ‖s‖ * (N : ℝ) ^ (-σ)
        ≤ (σ + |t|) * (N : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hsn (Real.rpow_nonneg hNpos.le _)
      _ ≤ (9 * ((N : ℝ) * σ)) * (N : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right key (Real.rpow_nonneg hNpos.le _)
      _ = 9 * σ * ((N : ℝ) * (N : ℝ) ^ (-σ)) := by ring
      _ ≤ 9 * σ * Real.exp 1 := mul_le_mul_of_nonneg_left hNσ2 (by linarith)
      _ = 9 * Real.exp 1 * σ := by ring
  have hTail : ‖∑' n : ℕ, dTerm s (n + N + 1)‖ ≤ 9 * Real.exp 1 := le_trans hchain hTailbound
  -- Assemble: `‖ζ‖ ≤ eL + 11e ≤ 36 L`.
  have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  nlinarith [htri, hMain, hB, hTail, he3, hLge1, hLpos,
    mul_nonneg (show (0 : ℝ) ≤ 3 - Real.exp 1 by linarith) hLpos.le,
    mul_nonneg (show (0 : ℝ) ≤ 33 by norm_num) (show (0 : ℝ) ≤ L - 1 by linarith)]

end Salt.SW
