/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LandauOdd

/-!
# The sawtooth value `hurwitzZetaOdd x 0 = 1/2 − x`

`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean` computes `hurwitzZeta x (−k)` in terms of
Bernoulli polynomials for every `k ≠ 0`, and records in its own TODO that the `k = 0` case is
missing because it "requires Fourier series which are only conditionally convergent".  This file
closes that case for the ODD part, which is the only half `Salt/MR/LandauOdd.lean` needs:

  `hurwitzZetaOdd x 0 = 1/2 − x`  for `x ∈ (0,1)`   (`sawtoothOdd`, i.e. `SawtoothOdd`).

The interval must be open: `hurwitzZetaOdd` is odd on `ℝ/ℤ`, so its value at `0` is `0`.

## The route

Mathlib's odd functional equation `HurwitzZeta.hurwitzZetaOdd_one_sub` at `s = 1` gives
`hurwitzZetaOdd x 0 = sinZeta x 1 / π`, so everything reduces to the boundary value of the sine
zeta function, i.e. to the classical sawtooth Fourier series

  `∑_{n ≥ 1} sin (2πnx) / n = π (1/2 − x)`   (`tendsto_sum_sin_div_nat`),

together with a bridge from that conditionally convergent series to the analytic continuation
`sinZeta x 1`.  Both halves run off the same elementary estimate, **Abel's inequality**
(`abs_sum_mul_le_of_bounded`): if the partial sums of `u` are bounded by `B` and `b` is
nonnegative and antitone, then `|∑_{n < M} u n * b n| ≤ B * b 0`.

* §1 Abel's inequality, and its shifted form (a tail bound).
* §2 `tendsto_tsum_div_rpow`: an Abel limit theorem for Dirichlet series with bounded partial
  sums — `∑ u n / (n+1)^σ → ∑ u n / (n+1)` as `σ → 1⁺`.  This is the bridge mathlib lacks, and it
  is what lets a conditionally convergent series reach the analytic continuation.
* §3 the geometry of `1 − e^{2πix}` (polar form, argument, bounded partial sums of `sin`).
* §4 the sawtooth series itself: Dirichlet's test gives convergence, and mathlib's Abel limit
  theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) transfers the value from the power
  series `∑ z^n / n = −log (1 − z)`.
* §5 `sinZeta x 1 = π (1/2 − x)`, then `hurwitzZetaOdd_apply_zero`, and — combining with mathlib's
  `hurwitzZetaEven_apply_zero` — the full `hurwitzZeta_apply_zero : hurwitzZeta x 0 = 1/2 − x`.
* §6 `sawtoothOdd`, and the unconditional instances of the conditional chain of `LandauOdd`.

Nothing in §§1–5 is specific to the Salt program: they are stated for mathlib and could be
upstreamed verbatim (`hurwitzZetaOdd_apply_zero` is exactly mathlib's missing `k = 0` case, and
`hurwitzZeta_apply_zero` closes the TODO of `HurwitzZetaValues.lean` — on `Ioo 0 1`; see the note
there about the endpoint `x = 0`, where the `k = 0` formula genuinely fails).
-/

namespace Salt.MR

open Complex Filter Topology Finset

open scoped Real

/-! ## §1 — Abel's inequality -/

section AbelInequality

variable {u b : ℕ → ℝ} {B : ℝ}

/-- **Abel's inequality.**  If the partial sums of `u` are bounded by `B` and `b` is a
nonnegative antitone sequence, then `|∑_{n < M} u n * b n| ≤ B * b 0`. -/
theorem abs_sum_mul_le_of_bounded (hS : ∀ N, |∑ n ∈ range N, u n| ≤ B)
    (hb0 : ∀ n, 0 ≤ b n) (hbanti : Antitone b) (M : ℕ) :
    |∑ n ∈ range M, u n * b n| ≤ B * b 0 := by
  have hB : (0 : ℝ) ≤ B := by simpa using hS 0
  have key : ∑ n ∈ range M, u n * b n =
      b (M - 1) * (∑ i ∈ range M, u i)
        - ∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j := by
    have h := Finset.sum_range_by_parts b u M
    simp only [smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have h1 : |b (M - 1) * ∑ i ∈ range M, u i| ≤ B * b (M - 1) := by
    rw [abs_mul, abs_of_nonneg (hb0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS M) (hb0 _)
  have h2 : |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
      ≤ B * (b 0 - b (M - 1)) := by
    calc |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
        ≤ ∑ i ∈ range (M - 1), |(b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (M - 1), (b i - b (i + 1)) * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hbanti (Nat.le_succ i))), neg_sub]
          exact mul_le_mul_of_nonneg_left (hS _) (by linarith [hbanti (Nat.le_succ i)])
      _ = (b 0 - b (M - 1)) * B := by rw [← Finset.sum_mul, Finset.sum_range_sub' b (M - 1)]
      _ = B * (b 0 - b (M - 1)) := mul_comm _ _
  rw [key]
  calc |b (M - 1) * (∑ i ∈ range M, u i)
        - ∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j|
      ≤ |b (M - 1) * ∑ i ∈ range M, u i|
        + |∑ i ∈ range (M - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), u j| := abs_sub _ _
    _ ≤ B * b (M - 1) + B * (b 0 - b (M - 1)) := add_le_add h1 h2
    _ = B * b 0 := by ring

/-- The tail form of Abel's inequality: the block of the series starting at `N` is bounded by
`2 B b N`. -/
theorem abs_sum_shift_mul_le_of_bounded (hS : ∀ N, |∑ n ∈ range N, u n| ≤ B)
    (hb0 : ∀ n, 0 ≤ b n) (hbanti : Antitone b) (N M : ℕ) :
    |∑ n ∈ range M, u (n + N) * b (n + N)| ≤ 2 * B * b N := by
  have hS' : ∀ K, |∑ n ∈ range K, u (n + N)| ≤ 2 * B := by
    intro K
    have e1 : ∑ n ∈ Finset.Ico N (N + K), u n = ∑ n ∈ range K, u (n + N) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    have e2 : ∑ n ∈ range N, u n + ∑ n ∈ Finset.Ico N (N + K), u n = ∑ n ∈ range (N + K), u n :=
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_right N K)
    have e3 : ∑ n ∈ range K, u (n + N) = (∑ n ∈ range (N + K), u n) - ∑ n ∈ range N, u n := by
      rw [← e1, ← e2]; ring
    rw [e3]
    calc |(∑ n ∈ range (N + K), u n) - ∑ n ∈ range N, u n|
        ≤ |∑ n ∈ range (N + K), u n| + |∑ n ∈ range N, u n| := abs_sub _ _
      _ ≤ B + B := add_le_add (hS _) (hS _)
      _ = 2 * B := by ring
  have h := abs_sum_mul_le_of_bounded (u := fun n => u (n + N)) (b := fun n => b (n + N)) hS'
    (fun n => hb0 _) (fun i j hij => hbanti (by omega)) M
  simpa using h

end AbelInequality

/-! ## §2 — an Abel limit theorem for Dirichlet series

A Dirichlet series whose coefficients have bounded partial sums converges absolutely for `σ > 1`,
and its value there tends, as `σ → 1⁺`, to the (conditionally convergent) sum at `σ = 1`.  The
proof is three ε-thirds: the tails at `σ` and at `1` are each `≤ 2B/(N+1)` by Abel's inequality,
and the head is a finite sum, hence continuous in `σ`. -/

set_option maxHeartbeats 400000 in
-- one long ε-argument (two tail bounds, a head continuity, and the `key` split) in a single
-- declaration; splitting it would mean threading a dozen hypotheses through helper lemmas
/-- **Abel's limit theorem for Dirichlet series.** -/
theorem tendsto_tsum_div_rpow {u : ℕ → ℝ} {B T : ℝ}
    (hS : ∀ N, |∑ n ∈ range N, u n| ≤ B)
    (hT : Tendsto (fun N => ∑ n ∈ range N, u n / ((n : ℝ) + 1)) atTop (𝓝 T)) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, u n / ((n : ℝ) + 1) ^ σ) (𝓝[>] (1 : ℝ)) (𝓝 T) := by
  have hB : (0 : ℝ) ≤ B := by simpa using hS 0
  set b : ℝ → ℕ → ℝ := fun σ n => (((n : ℝ) + 1) ^ σ)⁻¹ with hbdef
  have hbpos : ∀ σ : ℝ, ∀ n, 0 < b σ n := fun σ n => by
    simp only [hbdef]
    positivity
  have hbanti : ∀ σ : ℝ, 0 ≤ σ → Antitone (b σ) := by
    intro σ hσ i j hij
    simp only [hbdef]
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) σ)
      (Real.rpow_le_rpow (by positivity) hij' hσ)
  have hbone : ∀ n : ℕ, b 1 n = 1 / ((n : ℝ) + 1) := by
    intro n
    simp [hbdef, Real.rpow_one, one_div]
  have hble : ∀ σ : ℝ, 1 ≤ σ → ∀ n : ℕ, b σ n ≤ 1 / ((n : ℝ) + 1) := by
    intro σ hσ n
    have h1 : ((n : ℝ) + 1) ^ (1 : ℝ) ≤ ((n : ℝ) + 1) ^ σ :=
      Real.rpow_le_rpow_of_exponent_le (by simp) hσ
    rw [Real.rpow_one] at h1
    simp only [hbdef, one_div]
    exact inv_anti₀ (by positivity) h1
  have hu2 : ∀ n, |u n| ≤ 2 * B := by
    intro n
    have h1 : u n = (∑ k ∈ range (n + 1), u k) - ∑ k ∈ range n, u k := by
      rw [Finset.sum_range_succ]; ring
    rw [h1]
    calc |(∑ k ∈ range (n + 1), u k) - ∑ k ∈ range n, u k|
        ≤ |∑ k ∈ range (n + 1), u k| + |∑ k ∈ range n, u k| := abs_sub _ _
      _ ≤ B + B := add_le_add (hS _) (hS _)
      _ = 2 * B := by ring
  have hsummable : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => u n / ((n : ℝ) + 1) ^ σ) := by
    intro σ hσ
    have hg : Summable (fun n : ℕ => 2 * B * b σ n) := by
      refine Summable.mul_left _ ?_
      have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) := Real.summable_one_div_nat_rpow.mpr hσ
      have h1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ σ) :=
        (summable_nat_add_iff 1).mpr h0
      refine h1.congr fun n => ?_
      simp only [hbdef, one_div]
      push_cast
      rfl
    refine Summable.of_norm_bounded hg fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (by positivity) σ),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hu2 n) (le_of_lt (hbpos σ n))
  -- the tail at exponent `σ`
  have htail : ∀ σ : ℝ, 1 < σ → ∀ N : ℕ,
      |∑' i : ℕ, u (i + N) / (((i + N : ℕ) : ℝ) + 1) ^ σ| ≤ 2 * B * b σ N := by
    intro σ hσ N
    have hsh : Summable (fun i : ℕ => u (i + N) / (((i + N : ℕ) : ℝ) + 1) ^ σ) :=
      (summable_nat_add_iff N).mpr (hsummable σ hσ)
    refine le_of_tendsto hsh.hasSum.tendsto_sum_nat.abs (Eventually.of_forall fun M => ?_)
    have heq : ∑ i ∈ range M, u (i + N) / (((i + N : ℕ) : ℝ) + 1) ^ σ
        = ∑ i ∈ range M, u (i + N) * b σ (i + N) :=
      Finset.sum_congr rfl fun i _ => by simp only [hbdef, div_eq_mul_inv]
    rw [heq]
    exact abs_sum_shift_mul_le_of_bounded (u := u) (b := b σ) hS
      (fun n => (hbpos σ n).le) (hbanti σ (by linarith)) N M
  -- the tail at exponent `1`
  have htail1 : ∀ N : ℕ, |T - ∑ n ∈ range N, u n / ((n : ℝ) + 1)| ≤ 2 * B * b 1 N := by
    intro N
    have hlim : Tendsto (fun M => (∑ n ∈ range (M + N), u n / ((n : ℝ) + 1))
        - ∑ n ∈ range N, u n / ((n : ℝ) + 1)) atTop
        (𝓝 (T - ∑ n ∈ range N, u n / ((n : ℝ) + 1))) :=
      Tendsto.sub_const (hT.comp (Filter.tendsto_add_atTop_nat N)) _
    refine le_of_tendsto hlim.abs (Eventually.of_forall fun M => ?_)
    have e1 : ∑ n ∈ Finset.Ico N (M + N), u n / ((n : ℝ) + 1)
        = ∑ i ∈ range M, u (i + N) * b 1 (i + N) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hbone, mul_one_div, add_comm N i]
    have e2 : ∑ n ∈ range N, u n / ((n : ℝ) + 1)
        + ∑ n ∈ Finset.Ico N (M + N), u n / ((n : ℝ) + 1)
        = ∑ n ∈ range (M + N), u n / ((n : ℝ) + 1) :=
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left N M)
    have e3 : (∑ n ∈ range (M + N), u n / ((n : ℝ) + 1)) - ∑ n ∈ range N, u n / ((n : ℝ) + 1)
        = ∑ i ∈ range M, u (i + N) * b 1 (i + N) := by
      rw [← e2, ← e1]; ring
    rw [e3]
    exact abs_sum_shift_mul_le_of_bounded (u := u) (b := b 1) hS
      (fun n => (hbpos 1 n).le) (hbanti 1 zero_le_one) N M
  -- the head/tail split
  have key : ∀ (N : ℕ) (σ : ℝ), 1 < σ →
      |(∑' n : ℕ, u n / ((n : ℝ) + 1) ^ σ) - T|
        ≤ |(∑ n ∈ range N, u n / ((n : ℝ) + 1) ^ σ) - ∑ n ∈ range N, u n / ((n : ℝ) + 1)|
          + 4 * B * (1 / ((N : ℝ) + 1)) := by
    intro N σ hσ
    have hsplit := (hsummable σ hσ).sum_add_tsum_nat_add N
    set A := ∑ n ∈ range N, u n / ((n : ℝ) + 1) ^ σ with hA
    set C := ∑ n ∈ range N, u n / ((n : ℝ) + 1) with hC
    set R := ∑' i : ℕ, u (i + N) / (((i + N : ℕ) : ℝ) + 1) ^ σ with hR
    have h1 : (∑' n : ℕ, u n / ((n : ℝ) + 1) ^ σ) = A + R := hsplit.symm
    have h2 : |R| ≤ 2 * B * b σ N := htail σ hσ N
    have h3 : |T - C| ≤ 2 * B * b 1 N := htail1 N
    have h4 : 2 * B * b σ N + 2 * B * b 1 N ≤ 4 * B * (1 / ((N : ℝ) + 1)) := by
      have hσ1 : b σ N ≤ 1 / ((N : ℝ) + 1) := hble σ hσ.le N
      have h11 : b 1 N = 1 / ((N : ℝ) + 1) := hbone N
      have hstep : 2 * B * b σ N ≤ 2 * B * (1 / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hσ1 (by linarith)
      rw [h11] at *
      linarith
    have h5 : A + R - T = (A - C) + R - (T - C) := by ring
    rw [h1, h5]
    calc |(A - C) + R - (T - C)| ≤ |(A - C) + R| + |T - C| := abs_sub _ _
      _ ≤ (|A - C| + |R|) + |T - C| := by gcongr; exact abs_add_le _ _
      _ ≤ |A - C| + (2 * B * b σ N + 2 * B * b 1 N) := by linarith
      _ ≤ |A - C| + 4 * B * (1 / ((N : ℝ) + 1)) := by linarith
  -- the ε argument
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 4 * B * (1 / ((N : ℝ) + 1)) < ε / 2 := by
    have h0 : Tendsto (fun N : ℕ => 4 * B * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 * B)
      rwa [mul_zero] at h
    exact (h0.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
  have hhead : ContinuousAt (fun σ : ℝ => ∑ n ∈ range N, u n / ((n : ℝ) + 1) ^ σ) 1 := by
    refine Continuous.continuousAt (continuous_finsetSum _ fun n _ => ?_)
    refine continuous_const.div ?_ (fun σ => by positivity)
    exact continuous_iff_continuousAt.mpr fun σ => Real.continuousAt_const_rpow (by positivity)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hhead (ε / 2) (by positivity)
  refine ⟨δ, hδ0, fun σ hσmem hσdist => ?_⟩
  have hσ : 1 < σ := hσmem
  have hd : |(∑ n ∈ range N, u n / ((n : ℝ) + 1) ^ σ)
      - ∑ n ∈ range N, u n / ((n : ℝ) + 1)| < ε / 2 := by
    have h := hδ hσdist
    rw [Real.dist_eq] at h
    have he : ∑ n ∈ range N, u n / ((n : ℝ) + 1) ^ (1 : ℝ)
        = ∑ n ∈ range N, u n / ((n : ℝ) + 1) :=
      Finset.sum_congr rfl fun n _ => by rw [Real.rpow_one]
    rw [← he]
    exact h
  rw [Real.dist_eq]
  linarith [key N σ hσ]

/-! ## §3 — the geometry of `1 − e^{2πix}` -/

section Geometry

variable {x : ℝ}

/-- The `n`-th power of `e^{2πix}` has imaginary part `sin (2πnx)`. -/
theorem exp_pow_im (x : ℝ) (n : ℕ) :
    ((Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)) ^ n).im = Real.sin (2 * Real.pi * x * n) := by
  rw [← Complex.exp_nat_mul,
    show ((n : ℂ) * (((2 * Real.pi * x : ℝ) : ℂ) * I))
      = (((2 * Real.pi * x * n : ℝ) : ℂ)) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

/-- `sin (πx) > 0` on `(0,1)`. -/
theorem sin_pi_mul_pos (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < Real.sin (Real.pi * x) := by
  obtain ⟨hx0, hx1⟩ := hx
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  nlinarith [Real.pi_pos]

/-- The half-angle identity `1 − cos (2πx) = 2 sin²(πx)`. -/
theorem one_sub_cos_two_pi_mul (x : ℝ) :
    1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul']
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

/-- **The polar form of `1 − e^{2πix}`** for `x ∈ (0,1)`: modulus `2 sin (πx) > 0`, argument
`πx − π/2 ∈ (−π/2, π/2)`. -/
theorem one_sub_exp_eq (x : ℝ) :
    1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)
      = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ)
        * (Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ)
          + Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * I) := by
  have h1 : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    linarith [one_sub_cos_two_pi_mul x]
  have h2 : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.sin_two_mul]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, h1, h2]
  push_cast
  ring

theorem norm_one_sub_exp (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ‖1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)‖ = 2 * Real.sin (Real.pi * x) := by
  rw [one_sub_exp_eq x, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith [sin_pi_mul_pos hx])]

theorem exp_ne_one (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) ≠ 1 := by
  intro h
  have hn := norm_one_sub_exp hx
  rw [h, sub_self, norm_zero] at hn
  linarith [sin_pi_mul_pos hx]

/-- **The partial sums of `sin (2πnx)` are bounded**, uniformly in `N`. -/
theorem abs_sum_sin_le (hx : x ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    |∑ n ∈ range N, Real.sin (2 * Real.pi * x * n)| ≤ 1 / Real.sin (Real.pi * x) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hzne : z ≠ 1 := exp_ne_one hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have heq : ∑ n ∈ range N, Real.sin (2 * Real.pi * x * n) = (∑ n ∈ range N, z ^ n).im := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun n _ => (exp_pow_im x n).symm
  rw [heq]
  refine le_trans (Complex.abs_im_le_norm _) ?_
  rw [geom_sum_eq hzne, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hnz, one_pow, norm_one]
    norm_num
  have hden : ‖z - 1‖ = 2 * Real.sin (Real.pi * x) := by
    rw [← norm_neg, neg_sub]
    exact norm_one_sub_exp hx
  rw [hden, div_le_div_iff₀ (by linarith) hsin]
  nlinarith

/-- The `n`-th power of `e^{2πix}` has real part `cos (2πnx)`. -/
theorem exp_pow_re (x : ℝ) (n : ℕ) :
    ((Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)) ^ n).re
      = Real.cos (2 * Real.pi * x * n) := by
  rw [← Complex.exp_nat_mul,
    show ((n : ℂ) * (((2 * Real.pi * x : ℝ) : ℂ) * I))
      = (((2 * Real.pi * x * n : ℝ) : ℂ)) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- **The partial sums of `cos (2πnx)` are bounded**, uniformly in `N`. -/
theorem abs_sum_cos_le (hx : x ∈ Set.Ioo (0 : ℝ) 1) (N : ℕ) :
    |∑ n ∈ range N, Real.cos (2 * Real.pi * x * n)| ≤ 1 / Real.sin (Real.pi * x) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hzne : z ≠ 1 := exp_ne_one hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have heq : ∑ n ∈ range N, Real.cos (2 * Real.pi * x * n)
      = (∑ n ∈ range N, z ^ n).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => (exp_pow_re x n).symm
  rw [heq]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [geom_sum_eq hzne, norm_div]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_pow, hnz, one_pow, norm_one]
    norm_num
  have hden : ‖z - 1‖ = 2 * Real.sin (Real.pi * x) := by
    rw [← norm_neg, neg_sub]
    exact norm_one_sub_exp hx
  rw [hden, div_le_div_iff₀ (by linarith) hsin]
  nlinarith


end Geometry

/-! ## §4 — the sawtooth Fourier series -/

/-- **The sawtooth Fourier series** `∑_{n ≥ 1} sin (2πnx) / n = π (1/2 − x)` on `(0,1)`, stated as
a limit of partial sums: the series is only conditionally convergent, so this is deliberately NOT
a `tsum` statement. -/
theorem tendsto_sum_sin_div_nat {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N => ∑ n ∈ range N, Real.sin (2 * Real.pi * x * n) / n) atTop
      (𝓝 (Real.pi * (1 / 2 - x))) := by
  set c : ℕ → ℝ := fun n => Real.sin (2 * Real.pi * x * n) with hc
  set f : ℕ → ℝ := fun n => c n / n with hf
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  -- Step 1: convergence, by Dirichlet's test.
  have hbdd : ∀ n : ℕ, ‖∑ i ∈ range n, c (i + 1)‖ ≤ 1 / Real.sin (Real.pi * x) := by
    intro n
    have h : ∑ i ∈ range n, c (i + 1) = ∑ i ∈ range (n + 1), c i := by
      rw [Finset.sum_range_succ' c n]
      simp [hc]
    rw [Real.norm_eq_abs, h]
    exact abs_sum_sin_le hx (n + 1)
  have hanti : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    simp only [one_div]
    exact inv_anti₀ (by positivity) hij'
  have hzero : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hbdd
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcauchy
  simp only [smul_eq_mul] at hT
  have hTf : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 T) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine hT.congr fun N => ?_
    rw [Finset.sum_range_succ' f N]
    have h0 : f 0 = 0 := by simp [hf, hc]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    push_cast
    ring
  -- Step 2: Abel's limit theorem transfers the value from the power series.
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hTf
  have hval : ∀ r : ℝ, |r| < 1 →
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).im := by
    intro r hr
    have hnorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, hnz, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hr
    have H2 := Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hnorm)
    have hcongr : ∀ n : ℕ, (((r : ℂ) * z) ^ n / (n : ℂ)).im = f n * r ^ n := by
      intro n
      have e : ((r : ℂ) * z) ^ n / (n : ℂ) = (((r ^ n / n : ℝ)) : ℂ) * z ^ n := by
        push_cast
        ring
      rw [e, Complex.im_ofReal_mul, exp_pow_im x n]
      simp only [hf, hc]
      ring
    have H3 : HasSum (fun n : ℕ => f n * r ^ n) (-(Complex.log (1 - (r : ℂ) * z))).im :=
      H2.congr_fun fun n => (hcongr n).symm
    rw [H3.tsum_eq, Complex.neg_im]
  have heventually : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).im := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), -1 < r :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
    filter_upwards [h1, h2] with r hr1 hr2
    exact hval r (abs_lt.mpr ⟨hr2, hr1⟩)
  have habel' : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) (𝓝[<] (1 : ℝ)) (𝓝 T) :=
    habel.congr' heventually
  -- Step 3: the limit of the right-hand side, by continuity of `log` at `1 − z`.
  have hpolar : 1 - z = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ)
      * (Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ)
        + Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * I) := one_sub_exp_eq x
  have hre : (1 - z).re = 1 - Real.cos (2 * Real.pi * x) := by
    rw [hz, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre, one_sub_cos_two_pi_mul]
    positivity
  have hcont : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) (𝓝[<] (1 : ℝ))
      (𝓝 (-(Complex.log (1 - z)).im)) := by
    have h1 : ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * z) 1 :=
      continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have h2 : ContinuousAt (fun r : ℝ => Complex.log (1 - (r : ℂ) * z)) 1 := by
      refine h1.clog ?_
      rw [Complex.ofReal_one, one_mul]
      exact hslit
    have h3 : ContinuousAt (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).im) 1 :=
      ContinuousAt.neg (ContinuousAt.comp (g := Complex.im)
        Complex.continuous_im.continuousAt h2)
    have h4 := (h3.continuousWithinAt (s := Set.Iio (1 : ℝ))).tendsto
    rw [Complex.ofReal_one, one_mul] at h4
    exact h4
  -- Step 4: the argument of `1 − z`.
  have harg : (Complex.log (1 - z)).im = Real.pi * x - Real.pi / 2 := by
    rw [Complex.log_im, hpolar]
    refine Complex.arg_mul_cos_add_sin_mul_I (by linarith) (Set.mem_Ioc.mpr ⟨?_, ?_⟩)
    · nlinarith [Real.pi_pos, hx.1, hx.2]
    · nlinarith [Real.pi_pos, hx.1, hx.2]
  have hTval : T = Real.pi * (1 / 2 - x) := by
    have h := tendsto_nhds_unique habel' hcont
    rw [harg] at h
    linarith
  rw [← hTval]
  exact hTf

/-! ## §5 — the boundary value of `sinZeta`, and mathlib's missing `k = 0` case -/

/-- **The boundary value of the sine zeta function**: `sinZeta x 1 = π (1/2 − x)` for
`x ∈ (0,1)`.  This is the `k = 0` case of `HurwitzZeta.sinZeta_two_mul_nat_add_one`, which mathlib
states only for `k ≠ 0`. -/
theorem sinZeta_apply_one {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.sinZeta (x : UnitAddCircle) 1 = ((Real.pi * (1 / 2 - x) : ℝ) : ℂ) := by
  set c : ℕ → ℝ := fun n => Real.sin (2 * Real.pi * x * n) with hc
  set T : ℝ := Real.pi * (1 / 2 - x) with hTdef
  have hc0 : c 0 = 0 := by simp [hc]
  -- (a) absolute convergence for `σ > 1`
  have hsummable : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => c n / (n : ℝ) ^ σ) := by
    intro σ hσ
    refine Summable.of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hσ) fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, Real.zero_rpow (by linarith : σ ≠ 0)]
    · have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) σ
      have habs : |c n| ≤ 1 := by
        simp only [hc]
        exact Real.abs_sin_le_one _
      rw [div_le_div_iff₀ hpos hpos]
      nlinarith
  -- (b) the Dirichlet series tends to `T` as `σ → 1⁺`
  have hshiftsum : ∀ σ : ℝ, 1 < σ →
      ∑' n : ℕ, c n / (n : ℝ) ^ σ = ∑' n : ℕ, c (n + 1) / ((n : ℝ) + 1) ^ σ := by
    intro σ hσ
    rw [(hsummable σ hσ).tsum_eq_zero_add]
    have h0 : c 0 / (((0 : ℕ) : ℝ)) ^ σ = 0 := by simp [hc0]
    rw [h0, zero_add]
    exact tsum_congr fun n => by push_cast; ring_nf
  have hlim : Tendsto (fun σ : ℝ => ∑' n : ℕ, c n / (n : ℝ) ^ σ) (𝓝[>] (1 : ℝ)) (𝓝 T) := by
    have hS : ∀ N, |∑ n ∈ range N, c (n + 1)| ≤ 1 / Real.sin (Real.pi * x) := by
      intro N
      have h : ∑ i ∈ range N, c (i + 1) = ∑ i ∈ range (N + 1), c i := by
        rw [Finset.sum_range_succ' c N]
        simp [hc]
      rw [h]
      exact abs_sum_sin_le hx (N + 1)
    have hTT : Tendsto (fun N => ∑ n ∈ range N, c (n + 1) / ((n : ℝ) + 1)) atTop (𝓝 T) := by
      have hbase := tendsto_sum_sin_div_nat hx
      rw [← Filter.tendsto_add_atTop_iff_nat 1] at hbase
      refine hbase.congr fun N => ?_
      rw [Finset.sum_range_succ' (fun n : ℕ => Real.sin (2 * Real.pi * x * n) / n) N]
      simp only [Nat.cast_zero, mul_zero, Real.sin_zero, zero_div, add_zero]
      exact Finset.sum_congr rfl fun i _ => by simp only [hc]; push_cast; ring
    have hmain := tendsto_tsum_div_rpow hS hTT
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hshiftsum σ hσ).symm
  -- (c) the same limit, computed through the analytic continuation
  have hcast : ∀ σ : ℝ, 1 < σ →
      HurwitzZeta.sinZeta (x : UnitAddCircle) (σ : ℂ)
        = ((∑' n : ℕ, c n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
    have H := HurwitzZeta.hasSum_nat_sinZeta x hs
    have H2 : HasSum (fun n : ℕ => ((c n / (n : ℝ) ^ σ : ℝ) : ℂ))
        (((∑' n : ℕ, c n / (n : ℝ) ^ σ : ℝ) : ℂ)) :=
      Complex.hasSum_ofReal.mpr (hsummable σ hσ).hasSum
    refine H.unique (H2.congr_fun fun n => ?_)
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    norm_cast
  have hcont : Tendsto (fun σ : ℝ => HurwitzZeta.sinZeta (x : UnitAddCircle) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (HurwitzZeta.sinZeta (x : UnitAddCircle) 1)) := by
    have h2 : ContinuousAt (HurwitzZeta.sinZeta (x : UnitAddCircle)) (((1 : ℝ) : ℂ)) :=
      (HurwitzZeta.differentiableAt_sinZeta _).continuous.continuousAt
    have h1 : ContinuousAt (fun σ : ℝ => HurwitzZeta.sinZeta (x : UnitAddCircle) (σ : ℂ)) 1 :=
      h2.comp Complex.continuous_ofReal.continuousAt
    have h3 := h1.continuousWithinAt (s := Set.Ioi (1 : ℝ))
    simpa using h3.tendsto
  have hcont2 : Tendsto (fun σ : ℝ => HurwitzZeta.sinZeta (x : UnitAddCircle) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((T : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.continuousAt (x := T)).tendsto.comp hlim
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hcast σ hσ).symm
  exact tendsto_nhds_unique hcont hcont2

/-- **Mathlib's missing `k = 0` case, odd part**: `hurwitzZetaOdd x 0 = 1/2 − x` on `(0,1)`.
The functional equation `hurwitzZetaOdd_one_sub` at `s = 1` reduces it to `sinZeta x 1`. -/
theorem hurwitzZetaOdd_apply_zero {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  have hs : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have h1 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h1
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfe := HurwitzZeta.hurwitzZetaOdd_one_sub (x : UnitAddCircle) hs
  rw [show (1 : ℂ) - 1 = 0 by ring] at hfe
  rw [hfe, sinZeta_apply_one hx, Complex.cpow_neg_one, Complex.Gamma_one,
    show ((Real.pi : ℂ) * 1 / 2) = (Real.pi : ℂ) / 2 by ring, Complex.sin_pi_div_two]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- The coercion `ℝ → ℝ/ℤ` is nonzero on `(0,1)`. -/
theorem coe_unitAddCircle_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ((x : UnitAddCircle)) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  obtain ⟨h0, h1⟩ := hx
  rw [← hn] at h0 h1
  have hp : (0 : ℤ) < n := by exact_mod_cast h0
  have hq : n < 1 := by exact_mod_cast h1
  omega

/-- **Mathlib's missing `k = 0` case, in full**: `hurwitzZeta x 0 = 1/2 − x` on `(0,1)`, i.e. the
`k = 0` instance of `HurwitzZeta.hurwitzZeta_neg_nat` (whose value there is
`−bernoulli₁(x) = 1/2 − x`).  Note the interval: mathlib states `hurwitzZeta_neg_nat` on the CLOSED
`Icc 0 1`, but at `k = 0` the left endpoint fails (`hurwitzZeta 0 0 = riemannZeta 0 = −1/2`, not
`1/2`), because the even part jumps there (`hurwitzZetaEven_apply_zero`).  The correct `k = 0`
domain is `Ioc 0 1`; `Ioo 0 1` is what the odd half supports and all the present application
needs. -/
theorem hurwitzZeta_apply_zero {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  rw [HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZetaEven_apply_zero,
    if_neg (coe_unitAddCircle_ne_zero hx), hurwitzZetaOdd_apply_zero hx, zero_add]

/-! ## §5b — the cosine twins: the boundary value of `cosZeta`

The `cos` counterparts of §4 and §5.  `cosZeta_apply_one` is genuinely absent from mathlib
and is NOT a template port of its sine sibling: `cosZeta` is not entire — at `a = 0` it IS
`ζ`, whose pole sits at the very `s = 1` being evaluated — so the proof must discharge
`(x : UnitAddCircle) ≠ 0`, an obligation the sine template never incurs.  That asymmetry is
the even/odd split this campaign runs on. -/

/-- **The cosine companion of the sawtooth series** `∑_{n ≥ 1} cos (2πnx) / n = −log (2 sin πx)`
on `(0,1)`, stated as a limit of partial sums: conditionally convergent, so deliberately NOT a
`tsum`.

Template: `tendsto_sum_sin_div_nat` (:358), step for step, with `re` for `im` — EXCEPT step 4,
which is *shorter* here. The sine proof must compute an **argument** (polar form, then
`arg_mul_cos_add_sin_mul_I` with two `nlinarith` side goals); `Complex.log_re` gives
`log ‖1 − z‖` directly, and `‖1 − z‖ = 2 sin (πx)` is the already-landed `norm_one_sub_exp`. -/
theorem tendsto_sum_cos_div_nat {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N => ∑ n ∈ range N, Real.cos (2 * Real.pi * x * n) / n) atTop
      (𝓝 (-Real.log (2 * Real.sin (Real.pi * x)))) := by
  set c : ℕ → ℝ := fun n => Real.cos (2 * Real.pi * x * n) with hc
  set f : ℕ → ℝ := fun n => c n / n with hf
  set z : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I) with hz
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have hnz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  -- Step 1: convergence, by Dirichlet's test.  (Consumes E0.)
  -- NB the small end: `c 0 = cos 0 = 1`, not `0` as in the sine template, so the shifted sum is
  -- `S_{n+1} − 1` and E0's bound does NOT transfer verbatim.  Dirichlet's test needs only SOME
  -- uniform bound (the value of `T` comes from Abel, never from here), so `+ 1` is free.
  have hbdd : ∀ n : ℕ, ‖∑ i ∈ range n, c (i + 1)‖ ≤ 1 / Real.sin (Real.pi * x) + 1 := by
    intro n
    have h : ∑ i ∈ range n, c (i + 1) = ∑ i ∈ range (n + 1), c i - 1 := by
      rw [Finset.sum_range_succ' c n]
      simp [hc]
    rw [Real.norm_eq_abs, h]
    have hb := abs_sum_cos_le hx (n + 1)
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  have hanti : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    simp only [one_div]
    exact inv_anti₀ (by positivity) hij'
  have hzero : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcauchy := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hbdd
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcauchy
  simp only [smul_eq_mul] at hT
  have hTf : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 T) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine hT.congr fun N => ?_
    rw [Finset.sum_range_succ' f N]
    have h0 : f 0 = 0 := by simp [hf, hc]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    push_cast
    ring
  -- Step 2: Abel's limit theorem transfers the value from the power series.
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hTf
  have hval : ∀ r : ℝ, |r| < 1 →
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).re := by
    intro r hr
    have hnorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, hnz, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hr
    have H2 := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hnorm)
    have hcongr : ∀ n : ℕ, (((r : ℂ) * z) ^ n / (n : ℂ)).re = f n * r ^ n := by
      intro n
      have e : ((r : ℂ) * z) ^ n / (n : ℂ) = (((r ^ n / n : ℝ)) : ℂ) * z ^ n := by
        push_cast
        ring
      rw [e, Complex.re_ofReal_mul, exp_pow_re x n]
      simp only [hf, hc]
      ring
    have H3 : HasSum (fun n : ℕ => f n * r ^ n) (-(Complex.log (1 - (r : ℂ) * z))).re :=
      H2.congr_fun fun n => (hcongr n).symm
    rw [H3.tsum_eq, Complex.neg_re]
  have heventually : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∑' n : ℕ, f n * r ^ n = -(Complex.log (1 - (r : ℂ) * z)).re := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), -1 < r :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
    filter_upwards [h1, h2] with r hr1 hr2
    exact hval r (abs_lt.mpr ⟨hr2, hr1⟩)
  have habel' : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).re) (𝓝[<] (1 : ℝ)) (𝓝 T) :=
    habel.congr' heventually
  -- Step 3: the limit of the right-hand side, by continuity of `log` at `1 − z`.
  have hre : (1 - z).re = 1 - Real.cos (2 * Real.pi * x) := by
    rw [hz, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre, one_sub_cos_two_pi_mul]
    positivity
  have hcont : Tendsto (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).re) (𝓝[<] (1 : ℝ))
      (𝓝 (-(Complex.log (1 - z)).re)) := by
    have h1 : ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ) * z) 1 :=
      continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have h2 : ContinuousAt (fun r : ℝ => Complex.log (1 - (r : ℂ) * z)) 1 := by
      refine h1.clog ?_
      rw [Complex.ofReal_one, one_mul]
      exact hslit
    have h3 : ContinuousAt (fun r : ℝ => -(Complex.log (1 - (r : ℂ) * z)).re) 1 :=
      ContinuousAt.neg (ContinuousAt.comp (g := Complex.re)
        Complex.continuous_re.continuousAt h2)
    have h4 := (h3.continuousWithinAt (s := Set.Iio (1 : ℝ))).tendsto
    rw [Complex.ofReal_one, one_mul] at h4
    exact h4
  -- Step 4: the MODULUS of `1 − z` — two lines, where the sine twin needs an argument.
  have hlogre : (Complex.log (1 - z)).re = Real.log (2 * Real.sin (Real.pi * x)) := by
    rw [Complex.log_re, norm_one_sub_exp hx]
  have hTval : T = -Real.log (2 * Real.sin (Real.pi * x)) := by
    have h := tendsto_nhds_unique habel' hcont
    rw [hlogre] at h
    linarith
  rw [← hTval]
  exact hTf

/-- **The boundary value of the cosine zeta function**: `cosZeta x 1 = −log (2 sin πx)` for
`x ∈ (0,1)`.  The `k = 0` case, absent from mathlib as priced.

⚠️ This is NOT the sine template with `cos` written in.  `cosZeta` is not entire: at `a = 0` it is
`ζ`, whose pole sits at exactly the `s = 1` this theorem evaluates.  mathlib's signatures record
that asymmetry — `differentiableAt_sinZeta (a) : Differentiable ℂ (sinZeta a)` (everywhere, despite
the name) versus `differentiableAt_cosZeta (a) {s} (hs' : s ≠ 1 ∨ a ≠ 0) : DifferentiableAt ℂ … s`
— so the port must discharge `(x : UnitAddCircle) ≠ 0` and use `.continuousAt`, not
`.continuous.continuousAt`.  The same even/odd parity asymmetry the campaign runs on. -/
theorem cosZeta_apply_one {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.cosZeta (x : UnitAddCircle) 1
      = ((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ) := by
  set c : ℕ → ℝ := fun n => Real.cos (2 * Real.pi * x * n) with hc
  set T : ℝ := -Real.log (2 * Real.sin (Real.pi * x)) with hTdef
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have hc0 : c 0 = 1 := by simp [hc]
  -- the obligation the sine template never incurs: `ζ`'s pole is at this very point.
  have hane : (x : UnitAddCircle) ≠ 0 := by
    rw [Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico (Set.mem_Ico.mpr ⟨le_of_lt hx.1, hx.2⟩)]
    exact ne_of_gt hx.1
  -- (a) absolute convergence for `σ > 1`
  have hsummable : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => c n / (n : ℝ) ^ σ) := by
    intro σ hσ
    refine Summable.of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hσ) fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, Real.zero_rpow (by linarith : σ ≠ 0)]
    · have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) σ
      have habs : |c n| ≤ 1 := by
        simp only [hc]
        exact Real.abs_cos_le_one _
      rw [div_le_div_iff₀ hpos hpos]
      nlinarith
  -- (b) the Dirichlet series tends to `T` as `σ → 1⁺`
  have hshiftsum : ∀ σ : ℝ, 1 < σ →
      ∑' n : ℕ, c n / (n : ℝ) ^ σ = ∑' n : ℕ, c (n + 1) / ((n : ℝ) + 1) ^ σ := by
    intro σ hσ
    rw [(hsummable σ hσ).tsum_eq_zero_add]
    have h0 : c 0 / (((0 : ℕ) : ℝ)) ^ σ = 0 := by
      simp [hc0, Real.zero_rpow (by linarith : σ ≠ 0)]
    rw [h0, zero_add]
    exact tsum_congr fun n => by push_cast; ring_nf
  have hlim : Tendsto (fun σ : ℝ => ∑' n : ℕ, c n / (n : ℝ) ^ σ) (𝓝[>] (1 : ℝ)) (𝓝 T) := by
    -- again the small end: `c 0 = 1`, so the shifted sum is `S − 1` and the bound needs `+ 1`.
    have hS : ∀ N, |∑ n ∈ range N, c (n + 1)| ≤ 1 / Real.sin (Real.pi * x) + 1 := by
      intro N
      have h : ∑ i ∈ range N, c (i + 1) = ∑ i ∈ range (N + 1), c i - 1 := by
        rw [Finset.sum_range_succ' c N]
        simp [hc]
      rw [h]
      have hb := abs_sum_cos_le hx (N + 1)
      rw [abs_le] at hb ⊢
      constructor <;> linarith [hb.1, hb.2]
    have hTT : Tendsto (fun N => ∑ n ∈ range N, c (n + 1) / ((n : ℝ) + 1)) atTop (𝓝 T) := by
      have hbase := tendsto_sum_cos_div_nat hx
      rw [← Filter.tendsto_add_atTop_iff_nat 1] at hbase
      refine hbase.congr fun N => ?_
      rw [Finset.sum_range_succ' (fun n : ℕ => Real.cos (2 * Real.pi * x * n) / n) N]
      simp only [Nat.cast_zero, mul_zero, Real.cos_zero, div_zero, add_zero]
      exact Finset.sum_congr rfl fun i _ => by simp only [hc]; push_cast; ring
    have hmain := tendsto_tsum_div_rpow hS hTT
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hshiftsum σ hσ).symm
  -- (c) the same limit, computed through the analytic continuation
  have hcast : ∀ σ : ℝ, 1 < σ →
      HurwitzZeta.cosZeta (x : UnitAddCircle) (σ : ℂ)
        = ((∑' n : ℕ, c n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
    have H := HurwitzZeta.hasSum_nat_cosZeta x hs
    have H2 : HasSum (fun n : ℕ => ((c n / (n : ℝ) ^ σ : ℝ) : ℂ))
        (((∑' n : ℕ, c n / (n : ℝ) ^ σ : ℝ) : ℂ)) :=
      Complex.hasSum_ofReal.mpr (hsummable σ hσ).hasSum
    refine H.unique (H2.congr_fun fun n => ?_)
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    norm_cast
  have hcont : Tendsto (fun σ : ℝ => HurwitzZeta.cosZeta (x : UnitAddCircle) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (HurwitzZeta.cosZeta (x : UnitAddCircle) 1)) := by
    have h2 : ContinuousAt (HurwitzZeta.cosZeta (x : UnitAddCircle)) (((1 : ℝ) : ℂ)) :=
      (HurwitzZeta.differentiableAt_cosZeta _ (Or.inr hane)).continuousAt
    have h1 : ContinuousAt (fun σ : ℝ => HurwitzZeta.cosZeta (x : UnitAddCircle) (σ : ℂ)) 1 :=
      h2.comp Complex.continuous_ofReal.continuousAt
    have h3 := h1.continuousWithinAt (s := Set.Ioi (1 : ℝ))
    simpa using h3.tendsto
  have hcont2 : Tendsto (fun σ : ℝ => HurwitzZeta.cosZeta (x : UnitAddCircle) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((T : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.continuousAt (x := T)).tendsto.comp hlim
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hcast σ hσ).symm
  exact tendsto_nhds_unique hcont hcont2


/-! ## §6 — the unconditional instances of `LandauOdd`'s conditional chain -/

/-- **THE ZENO, DISCHARGED.**  `SawtoothOdd` holds. -/
theorem sawtoothOdd : SawtoothOdd := fun _ hx => hurwitzZetaOdd_apply_zero hx

/-- **The odd-`χ` production, unconditional**: `π·N^{−5/2} ≤ (L(1,χ)).re` at every real
nonprincipal odd `χ`. -/
theorem L1_lower_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hodd : χ.Odd) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    Real.pi / (N : ℝ) ^ (5 / 2 : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re :=
  L1_lower_odd_of_sawtooth sawtoothOdd hodd hsq hχ1

/-- **`O-3`, unconditional.** -/
theorem l1LowerOddEffective_pi : L1LowerOddEffective Real.pi (5 / 2) :=
  l1LowerOddEffective_of_sawtooth sawtoothOdd

/-- **`O-3` normalised to `c = 1`, unconditional.** -/
theorem l1LowerOddEffective_one : L1LowerOddEffective 1 (5 / 2) :=
  l1LowerOddEffective_one_of_sawtooth sawtoothOdd

end Salt.MR
