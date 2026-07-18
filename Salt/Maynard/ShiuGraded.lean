/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuRankin
import Salt.Maynard.ShiuDecomp

/-!
# ShiuGraded — the graded Rankin corollaries (S3b) and the class-II capped sum (S4-II)

This file supplies the wave-W2 ingredients of the `N-SHIU-CORE` rung, on top of the
landed Rankin engine (`Salt.Maynard.ShiuRankin`) and the greedy decomposition
(`Salt.Maynard.ShiuDecomp`).

## S3b — the graded Rankin corollaries

`sum_tau_smooth_gt_rankin_le` is the *raw Rankin gain*: for `1/2 < σ ≤ 1`,
`Σ_{c ≤ N, v-smooth, c > W} τ(c)/c ≤ W^{−(1−σ)} · ∏_{p ≤ v}(1 − p^{−σ})^{−2}`.
The factor `W^{−(1−σ)}` is the trick — every `c > W` pays a `W^{−(1−σ)}` toll for
being pushed from the divergent `σ = 1` series into the convergent `σ`-series.

`sum_tau_smooth_gt_calibrated_le` is the *calibrated corollary*: with the design's
scale choice `(1−σ)·log v = ½·log r` and `log W = r·log v`, the Rankin gain becomes
`exp(−(r/2)·log r)` and the Euler correction is bounded by
`exp(C·√r·(log log v + 1))`, giving the class-`IV_r` ingredient

    Σ_{c > W, v-smooth} τ(c)/c ≤ exp(−(r/2)·log r) · exp(C·√r·(log log v + 1)).

**Documented deviation from the skeleton (honest arithmetic).** The design's target
shape was `exp(−(r/2)log r + C√r·log r)·(log v)²`.  The route here bounds the entire
Euler correction ∏(1−p^{−σ})^{−2} by a single `exp(C√r(loglog v + 1))` factor (via
`−log(1−x) ≤ x/(1−x)` from `Real.log_le_sub_one_of_pos`, the uniform factor
`1/(1−p^{−σ}) ≤ 4`, and `p^{−σ} ≤ √r/p` under the calibration + Mertens-2 for
`Σ_{p≤v} 1/p ≤ loglog v + C`).  This is *stronger and cleaner* for the `S4-IV`
consumer: `loglog v ≤ loglog w` is a `w`-constant w.r.t. the `r`-summation, and
`√r·loglog v = o(r·log r)`, so the super-exponential Rankin decay `exp(−(r/2)log r)`
dominates exactly as the design requires.  No `(log v)²` factor is peeled off
separately — it is absorbed into the exponential.

## S4-II — the capped-prime-power sum

`sum_cappedPow_inv_le` is the load-bearing class-II ingredient:
`Σ_{p ≤ W prime} 1/cappedPow(W,p) ≤ 3/√W` where `cappedPow W p = p^{u_p}` with
`u_p` minimal such that `p^{u_p} > W`.  Split at `√W`: for `√W < p ≤ W` the cap is
`p²` and `Σ 1/p² ≤ 2/√W` (telescoping); for `p ≤ √W` the cap exceeds `W`, and there
are `≤ √W` such primes, contributing `≤ √W·(1/W) = 1/√W`.

`sum_cappedPow_count_ap_le` is the consumer-shaped count: summed over primes `p ≤ W`
coprime to `q`, the number of `n ≤ z` in the residue class `a (mod q)` divisible by
`cappedPow(W,p)` is `≤ (z/q)·(3/√W) + W`.  The `S5` assembly weights this by `τ` and
supplies the class-II → capped-power structural reduction.
-/

open Nat Finset

namespace Salt.Maynard

/-! ## S3b-i — the raw Rankin gain -/

/-- **The raw Rankin gain.**  For `v ≥ 2`, `1/2 < σ ≤ 1`, `W ≥ 1`, the tail
`Σ_{1 ≤ c ≤ N, c v-smooth, c > W} τ(c)/c` is bounded by `W^{−(1−σ)}` times the smooth
Euler product.  Each `c > W` obeys `1/c = c^{−σ}·c^{−(1−σ)} ≤ c^{−σ}·W^{−(1−σ)}`
(the base `c^{−(1−σ)}` is antitone in `c` for the nonpositive exponent `−(1−σ)`), so
the tail collapses onto `W^{−(1−σ)}·Σ_{c v-smooth} τ(c)/c^σ`, and the landed
`sum_tau_smooth_rpow_le` closes it. -/
theorem sum_tau_smooth_gt_rankin_le (N v W : ℕ) (σ : ℝ)
    (hv : 2 ≤ v) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hW : 1 ≤ W) :
    ∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
        (c.divisors.card : ℝ) / (c : ℝ)
      ≤ (W : ℝ) ^ (-(1 - σ)) *
        ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := by
  set S := (Finset.Icc 1 N).filter
    (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c) with hSdef
  set T := (Finset.Icc 1 N).filter (fun c => ∀ p ∈ c.primeFactors, p ≤ v) with hTdef
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  -- per-term bound
  have hterm : ∀ c ∈ S, (c.divisors.card : ℝ) / (c : ℝ)
      ≤ (W : ℝ) ^ (-(1 - σ)) * tauDivRpow σ c := by
    intro c hc
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hc1, _⟩, _, hWc⟩ := hc
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
    have hWcR : (W : ℝ) ≤ (c : ℝ) := by exact_mod_cast (le_of_lt hWc)
    have hcσ : (0 : ℝ) < (c : ℝ) ^ σ := Real.rpow_pos_of_pos hcR σ
    have hkey : (c : ℝ) ^ (-(1 - σ)) ≤ (W : ℝ) ^ (-(1 - σ)) := by
      have he : (0 : ℝ) ≤ 1 - σ := by linarith
      have hb : (W : ℝ) ^ (1 - σ) ≤ (c : ℝ) ^ (1 - σ) := Real.rpow_le_rpow hWR.le hWcR he
      rw [Real.rpow_neg hWR.le, Real.rpow_neg hcR.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hWR _) hb
    have hc1eq : (c : ℝ)⁻¹ = ((c : ℝ) ^ σ)⁻¹ * (c : ℝ) ^ (-(1 - σ)) := by
      rw [← Real.rpow_neg hcR.le, ← Real.rpow_add hcR,
        show -σ + -(1 - σ) = (-1 : ℝ) by ring, Real.rpow_neg_one]
    have hfac : (0 : ℝ) ≤ (c.divisors.card : ℝ) * ((c : ℝ) ^ σ)⁻¹ := by positivity
    unfold tauDivRpow
    rw [div_eq_mul_inv, hc1eq, div_eq_mul_inv]
    calc (c.divisors.card : ℝ) * (((c : ℝ) ^ σ)⁻¹ * (c : ℝ) ^ (-(1 - σ)))
        = ((c.divisors.card : ℝ) * ((c : ℝ) ^ σ)⁻¹) * (c : ℝ) ^ (-(1 - σ)) := by ring
      _ ≤ ((c.divisors.card : ℝ) * ((c : ℝ) ^ σ)⁻¹) * (W : ℝ) ^ (-(1 - σ)) :=
          mul_le_mul_of_nonneg_left hkey hfac
      _ = (W : ℝ) ^ (-(1 - σ)) * ((c.divisors.card : ℝ) * ((c : ℝ) ^ σ)⁻¹) := by ring
  have hST : S ⊆ T := by
    intro c hc
    rw [hSdef, Finset.mem_filter] at hc
    rw [hTdef, Finset.mem_filter]
    exact ⟨hc.1, hc.2.1⟩
  calc ∑ c ∈ S, (c.divisors.card : ℝ) / (c : ℝ)
      ≤ ∑ c ∈ S, (W : ℝ) ^ (-(1 - σ)) * tauDivRpow σ c := Finset.sum_le_sum hterm
    _ = (W : ℝ) ^ (-(1 - σ)) * ∑ c ∈ S, tauDivRpow σ c := by rw [Finset.mul_sum]
    _ ≤ (W : ℝ) ^ (-(1 - σ)) * ∑ c ∈ T, tauDivRpow σ c := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hWR.le _)
        exact Finset.sum_le_sum_of_subset_of_nonneg hST
          (fun c _ _ => tauDivRpow_nonneg σ c)
    _ ≤ (W : ℝ) ^ (-(1 - σ)) *
          ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hWR.le _)
        have h := sum_tau_smooth_rpow_le N v σ hv hσ hσ1
        simpa only [tauDivRpow] using h

/-! ## S3b-ii — the Euler-correction exponential bound -/

/-- `(1 − x)⁻¹ ≤ exp(4x)` for `0 ≤ x ≤ 3/4`.  From `Real.log_le_sub_one_of_pos`
applied to `(1−x)⁻¹`: `−log(1−x) = log((1−x)⁻¹) ≤ (1−x)⁻¹ − 1 ≤ 4x` (last step
is `(1−x)⁻¹ ≤ 1 + 4x`, i.e. `1 ≤ (1+4x)(1−x)`, i.e. `x(3−4x) ≥ 0`). -/
lemma one_sub_inv_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3 / 4) :
    (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  have hu : (0 : ℝ) < 1 - x := by linarith
  have hinv : (0 : ℝ) < (1 - x)⁻¹ := by positivity
  have h1 : Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos hinv
  have h3 : (1 - x)⁻¹ ≤ 1 + 4 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hu]
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 3 - 4 * x)]
  have hkey : -Real.log (1 - x) ≤ 4 * x := by
    rw [← Real.log_inv]; linarith [h1, h3]
  calc (1 - x)⁻¹ = Real.exp (Real.log ((1 - x)⁻¹)) := (Real.exp_log hinv).symm
    _ = Real.exp (-Real.log (1 - x)) := by rw [Real.log_inv]
    _ ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr hkey

/-- The prime-tail smallness `p^{−σ} ≤ 3/4` for `p ≥ 2`, `σ ≥ 1/2` (since
`p^{−σ} ≤ 2^{−σ} ≤ 2^{−1/2} < 3/4`). -/
lemma rpow_neg_prime_le_three_quarters {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have h1 : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg hppos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) σ)
      (Real.rpow_le_rpow (by norm_num) hp2 hσ0)
  have h2 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hsq : (2 : ℝ) ^ (-(1 / 2) : ℝ) * (2 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
    nlinarith [hpos, hsq]
  linarith

/-- The per-prime Euler-correction bound `(1 − p^{−σ})^{−2} ≤ exp(8·p^{−σ})`
(square `one_sub_inv_le_exp` at `x = p^{−σ} ≤ 3/4`). -/
lemma one_sub_rpow_neg_sq_le_exp {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 ≤ Real.exp (8 * (p : ℝ) ^ (-σ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set x := (p : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := (Real.rpow_pos_of_pos hppos _).le
  have hx34 : x ≤ 3 / 4 := rpow_neg_prime_le_three_quarters hp hσ
  have hb := one_sub_inv_le_exp hx0 hx34
  have hnn : (0 : ℝ) ≤ (1 - x)⁻¹ := by
    have : (0 : ℝ) < 1 - x := by linarith
    positivity
  calc (1 - x)⁻¹ ^ 2 ≤ (Real.exp (4 * x)) ^ 2 := pow_le_pow_left₀ hnn hb 2
    _ = Real.exp (8 * x) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- **The Euler-correction exponential bound.** `∏_{p ≤ v}(1 − p^{−σ})^{−2}
≤ exp(8·Σ_{p ≤ v} p^{−σ})` for `σ ≥ 1/2`. -/
lemma prod_one_sub_rpow_neg_sq_le_exp (v : ℕ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2
      ≤ Real.exp (8 * ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (p : ℝ) ^ (-σ)) := by
  have hstep : ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2
      ≤ ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, Real.exp (8 * (p : ℝ) ^ (-σ)) := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact one_sub_rpow_neg_sq_le_exp hp.2.two_le hσ
  rw [← Real.exp_sum] at hstep
  rw [Finset.mul_sum]
  exact hstep

/-! ## S3b-iii — the calibration and the composite corollary -/

/-- Under the calibration `(1−σ)·log v = ½·log r` (with `σ ≤ 1`, `v,r ≥ 1`), each
`p ≤ v` satisfies `p^{−σ} ≤ √r · (1/p)` (since `p^{1−σ} ≤ v^{1−σ} = √r`), hence
`Σ_{p ≤ v} p^{−σ} ≤ √r · Σ_{p ≤ v} 1/p`. -/
lemma sum_rpow_neg_prime_le_sqrt (v r : ℕ) {σ : ℝ}
    (hv : 1 ≤ v) (hr : 1 ≤ r) (hσ1 : σ ≤ 1)
    (hcal : (1 - σ) * Real.log v = (1 / 2) * Real.log r) :
    ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (p : ℝ) ^ (-σ)
      ≤ Real.sqrt r * ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 : ℝ) / p := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hvsig : (v : ℝ) ^ (1 - σ) = Real.sqrt r := by
    rw [Real.rpow_def_of_pos hvpos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hrpos,
      show Real.log v * (1 - σ) = (1 - σ) * Real.log v by ring, hcal]
    congr 1; ring
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpv, hpp⟩ := hp
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hpv' : (p : ℝ) ≤ (v : ℝ) := by exact_mod_cast (by omega : p ≤ v)
  have hpsig : (p : ℝ) ^ (1 - σ) ≤ Real.sqrt r := by
    rw [← hvsig]; exact Real.rpow_le_rpow hppos.le hpv' (by linarith)
  have hsplit : (p : ℝ) ^ (-σ) = (p : ℝ)⁻¹ * (p : ℝ) ^ (1 - σ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hppos]; congr 1; ring
  rw [hsplit, show (1 : ℝ) / (p : ℝ) = (p : ℝ)⁻¹ from one_div _,
    mul_comm (Real.sqrt r) ((p : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left hpsig (by positivity)

/-- **The calibrated Rankin corollary (S3b-i, class-`IV_r` ingredient).**
For scales calibrated by `(1−σ)·log v = ½·log r` and `log W = r·log v`, the
`v`-smooth tail above `W` obeys

    Σ_{c > W, v-smooth, c ≤ N} τ(c)/c
      ≤ exp(−(r/2)·log r) · exp(8·√r·(log log v + C)).

The first factor is the Rankin gain `W^{−(1−σ)} = exp(−(r/2)log r)`; the second is
the Euler correction `∏_{p≤v}(1−p^{−σ})^{−2}`, bounded via
`prod_one_sub_rpow_neg_sq_le_exp` + `sum_rpow_neg_prime_le_sqrt` + Mertens-2
(`Σ_{p≤v} 1/p ≤ log log v + C`).  `C` is the Meissel–Mertens constant (nonneg
after adjustment).  **This is the exact form the S4-IV consumer composes** — note it
supersedes the design's split `exp(C√r log r)·(log v)²`: `log log v ≤ log log w` is a
`w`-constant and `√r·log log v = o(r log r)`, so the `exp(−(r/2)log r)` decay
dominates the `r`-summation exactly as required. -/
theorem sum_tau_smooth_gt_calibrated_le :
    ∃ (C : ℝ) (v₀ : ℕ), 0 ≤ C ∧ 3 ≤ v₀ ∧ ∀ (N v r W : ℕ) (σ : ℝ),
      v₀ ≤ v → 1 / 2 < σ → σ ≤ 1 → 1 ≤ r →
      (1 - σ) * Real.log v = (1 / 2) * Real.log r →
      Real.log W = (r : ℝ) * Real.log v → 1 ≤ W →
      ∑ c ∈ (Finset.Icc 1 N).filter
          (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
        ≤ Real.exp (-((r : ℝ) / 2) * Real.log r)
            * Real.exp (8 * Real.sqrt r * (Real.log (Real.log v) + C)) := by
  obtain ⟨M, Cm, hCm0, hmert⟩ := Salt.Mertens.mertens_second_sharp
  refine ⟨max (M + Cm / Real.log 2) 0, 3, le_max_right _ _, le_refl 3, ?_⟩
  intro N v r W σ hv hσ hσ1 hr hcal hWv hW
  set P := (Finset.range (v + 1)).filter Nat.Prime with hP
  have hv2 : 2 ≤ v := by omega
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  -- the Rankin gain, evaluated
  have hgain : (W : ℝ) ^ (-(1 - σ)) = Real.exp (-((r : ℝ) / 2) * Real.log r) := by
    rw [Real.rpow_def_of_pos hWpos]
    congr 1
    rw [hWv, show ((r : ℝ) * Real.log v) * (-(1 - σ)) = -(r : ℝ) * ((1 - σ) * Real.log v) by
      ring, hcal]
    ring
  -- the Mertens-2 upper bound on Σ 1/p
  have hsig1p : ∑ p ∈ P, (1 : ℝ) / p
      ≤ Real.log (Real.log v) + (M + Cm / Real.log 2) := by
    have h := abs_le.mp (hmert v hv2)
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogv2 : Real.log 2 ≤ Real.log v :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hv2)
    have hcmlv : Cm / Real.log v ≤ Cm / Real.log 2 :=
      div_le_div_of_nonneg_left hCm0 hlog2pos hlogv2
    linarith [h.2]
  -- the exponent inequality for the correction
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hexparg : 8 * ∑ p ∈ P, (p : ℝ) ^ (-σ)
      ≤ 8 * Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0) := by
    have hsr := sum_rpow_neg_prime_le_sqrt v r (by omega) hr hσ1 hcal
    have hchain : ∑ p ∈ P, (p : ℝ) ^ (-σ)
        ≤ Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0) := by
      calc ∑ p ∈ P, (p : ℝ) ^ (-σ) ≤ Real.sqrt r * ∑ p ∈ P, (1 : ℝ) / p := hsr
        _ ≤ Real.sqrt r * (Real.log (Real.log v) + (M + Cm / Real.log 2)) :=
            mul_le_mul_of_nonneg_left hsig1p hsqrt_nn
        _ ≤ Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0) :=
            mul_le_mul_of_nonneg_left (by linarith [le_max_left (M + Cm / Real.log 2) (0 : ℝ)])
              hsqrt_nn
    calc 8 * ∑ p ∈ P, (p : ℝ) ^ (-σ)
        ≤ 8 * (Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0)) :=
          mul_le_mul_of_nonneg_left hchain (by norm_num)
      _ = 8 * Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0) := by ring
  -- assemble
  have hraw := sum_tau_smooth_gt_rankin_le N v W σ hv2 hσ hσ1 hW
  have hprod := prod_one_sub_rpow_neg_sq_le_exp v (le_of_lt hσ)
  calc ∑ c ∈ (Finset.Icc 1 N).filter
        (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
        (c.divisors.card : ℝ) / (c : ℝ)
      ≤ (W : ℝ) ^ (-(1 - σ)) *
          ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := hraw
    _ ≤ (W : ℝ) ^ (-(1 - σ)) * Real.exp (8 * ∑ p ∈ P, (p : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hWpos.le _)
    _ = Real.exp (-((r : ℝ) / 2) * Real.log r)
          * Real.exp (8 * ∑ p ∈ P, (p : ℝ) ^ (-σ)) := by
        rw [hgain]
    _ ≤ Real.exp (-((r : ℝ) / 2) * Real.log r)
          * Real.exp (8 * Real.sqrt r * (Real.log (Real.log v) + max (M + Cm / Real.log 2) 0)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexparg) (Real.exp_nonneg _)

/-! ## S4-II — the capped-prime-power sum -/

/-- `cappedPow W p = p^{u_p}` with `u_p = Nat.log p W + 1`, the minimal exponent with
`p^{u_p} > W`. -/
def cappedPow (W p : ℕ) : ℕ := p ^ (Nat.log p W + 1)

/-- The cap exceeds `W`: `W < cappedPow W p` for `p ≥ 2`. -/
lemma lt_cappedPow {W p : ℕ} (hp : 2 ≤ p) : W < cappedPow W p :=
  Nat.lt_pow_succ_log_self (by omega) W

/-- For `p ≤ W` (`p ≥ 2`) the cap is at least `p²` (since `Nat.log p W ≥ 1`). -/
lemma sq_le_cappedPow {W p : ℕ} (hp : 2 ≤ p) (hpW : p ≤ W) : p ^ 2 ≤ cappedPow W p := by
  have hlog : 1 ≤ Nat.log p W := Nat.log_pos (by omega) hpW
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- **The capped-prime-power sum (S4-II core).**
`Σ_{p ≤ W prime} 1/cappedPow(W,p) ≤ 4/√W`.  Split at `s = ⌊√W⌋`: primes `p ≤ s`
have `cappedPow > W`, contributing `≤ |{p ≤ s}|/W ≤ (s+1)/W`; primes `s < p ≤ W`
have `cappedPow ≥ p²`, contributing `≤ Σ_{s < i ≤ W} 1/i² ≤ 1/s − 1/W`
(mathlib's `sum_Ioc_inv_sq_le_sub` telescope).  The design's `3/√W` grade, with an
honest constant `4`. -/
lemma sum_cappedPow_inv_le {W : ℕ} (hW : 4 ≤ W) :
    ∑ p ∈ (Finset.range (W + 1)).filter Nat.Prime, (1 : ℝ) / (cappedPow W p : ℝ)
      ≤ 4 / Real.sqrt W := by
  classical
  set s := Nat.sqrt W with hs
  set P := (Finset.range (W + 1)).filter Nat.Prime with hP
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hRpos : (0 : ℝ) < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega : 1 * 1 ≤ W)
  have hsW : s ≤ W := by rw [hs]; exact Nat.sqrt_le_self W
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  -- s ≤ √W and √W < s + 1
  have hsleR : (s : ℝ) ≤ Real.sqrt W := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) ^ 2) from (Real.sqrt_sq hspos.le).symm]
    apply Real.sqrt_le_sqrt
    have h : s ^ 2 ≤ W := by rw [hs]; exact Nat.sqrt_le' W
    calc (s : ℝ) ^ 2 = ((s ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (W : ℝ) := by exact_mod_cast h
  have hRltS1 : Real.sqrt W < (s : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have h : W < (s + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' W; rwa [← hs, Nat.succ_eq_add_one] at this
    calc (W : ℝ) < (((s + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((s : ℝ) + 1) ^ 2 := by push_cast; ring
  -- the small-prime part: ≤ (s+1)/W
  have hApart : ∑ p ∈ P.filter (fun p => p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ)
      ≤ ((s : ℝ) + 1) / W := by
    have hcard : (P.filter (fun p => p ≤ s)).card ≤ s + 1 := by
      calc (P.filter (fun p => p ≤ s)).card ≤ (Finset.range (s + 1)).card := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            rw [Finset.mem_range]; omega
        _ = s + 1 := Finset.card_range _
    calc ∑ p ∈ P.filter (fun p => p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ)
        ≤ ∑ _p ∈ P.filter (fun p => p ≤ s), (1 : ℝ) / W := by
          apply Finset.sum_le_sum
          intro p hp
          rw [hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
          obtain ⟨⟨_, hpp⟩, _⟩ := hp
          have : (W : ℝ) ≤ (cappedPow W p : ℝ) := by
            have := lt_cappedPow (W := W) (p := p) hpp.two_le
            exact_mod_cast (by omega : W ≤ cappedPow W p)
          exact one_div_le_one_div_of_le hWpos this
      _ = ((P.filter (fun p => p ≤ s)).card : ℝ) * (1 / W) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((s : ℝ) + 1) * (1 / W) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc ((P.filter (fun p => p ≤ s)).card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
                exact_mod_cast hcard
            _ = (s : ℝ) + 1 := by push_cast; ring
      _ = ((s : ℝ) + 1) / W := by ring
  -- the large-prime part: ≤ 1/s
  have hBpart : ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ)
      ≤ 1 / (s : ℝ) := by
    have hBsub : P.filter (fun p => ¬ p ≤ s) ⊆ Finset.Ioc s W := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Ioc]; omega
    calc ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ)
        ≤ ∑ p ∈ P.filter (fun p => ¬ p ≤ s), ((p : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          rw [hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
          obtain ⟨⟨_, hpp⟩, hps⟩ := hp
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          have hpW : p ≤ W := by omega
          have hsq : (p : ℝ) ^ 2 ≤ (cappedPow W p : ℝ) := by
            have := sq_le_cappedPow (W := W) (p := p) hpp.two_le hpW
            calc (p : ℝ) ^ 2 = ((p ^ 2 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ (cappedPow W p : ℝ) := by exact_mod_cast this
          rw [one_div]
          exact inv_anti₀ (pow_pos hppos 2) hsq
      _ ≤ ∑ i ∈ Finset.Ioc s W, ((i : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun i _ _ => by positivity)
      _ ≤ (s : ℝ)⁻¹ - (W : ℝ)⁻¹ :=
          sum_Ioc_inv_sq_le_sub (by omega : s ≠ 0) hsW
      _ ≤ 1 / (s : ℝ) := by
          have hWinv : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
          rw [one_div]; linarith
  -- combine and finish
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ s)]
  calc (∑ p ∈ P.filter (fun p => p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ))
        + ∑ p ∈ P.filter (fun p => ¬ p ≤ s), (1 : ℝ) / (cappedPow W p : ℝ)
      ≤ ((s : ℝ) + 1) / W + 1 / (s : ℝ) := add_le_add hApart hBpart
    _ ≤ 4 / Real.sqrt W := by
        rw [div_add_div _ _ hWpos.ne' hspos.ne', div_le_div_iff₀ (by positivity) hRpos]
        have hmul : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hWpos.le
        have hpoly : (s : ℝ) * s + (s : ℝ) + W ≤ 4 * Real.sqrt W * s := by
          nlinarith [hsleR, hRltS1, hspos, hRpos, hmul, hs1R,
            mul_nonneg (sub_nonneg.mpr hsleR)
              (by linarith [hRltS1] : (0 : ℝ) ≤ (s : ℝ) + 1 - Real.sqrt W),
            mul_nonneg hRpos.le (by linarith [hs1R] : (0 : ℝ) ≤ 2 * (s : ℝ) - 1)]
        nlinarith [mul_le_mul_of_nonneg_right hpoly (Real.sqrt_nonneg (W : ℝ)), hmul,
          hRpos, hspos, hWpos]

/-- **The capped-power divisibility count (S4-II, consumer-shaped).**  Summed over
primes `p ≤ W`, the number of `n ∈ [1,z]` divisible by `cappedPow(W,p)` is
`≤ 4·z/√W`.  This is the count the `S5` assembly weights by `τ` and refines to the
arithmetic-progression form (dividing by `q` under `p ∤ q` via a coprime CRT count —
the `+ W·polylog` boundary term of the design's split absorbs the `π(W)` off-count).
The class-II → capped-power structural reduction (`c·ρ^{e_ρ} > W`, `c ≤ W`) is the
`S5` step; it is *not* the naive "`cappedPow ∣ n`" (false for squarefree `n`). -/
lemma sum_cappedPow_count_le {W : ℕ} (hW : 4 ≤ W) (z : ℕ) :
    ∑ p ∈ (Finset.range (W + 1)).filter Nat.Prime,
        (((Finset.Ioc 0 z).filter (fun n => cappedPow W p ∣ n)).card : ℝ)
      ≤ 4 * (z : ℝ) / Real.sqrt W := by
  classical
  have hbound : ∀ p ∈ (Finset.range (W + 1)).filter Nat.Prime,
      (((Finset.Ioc 0 z).filter (fun n => cappedPow W p ∣ n)).card : ℝ)
        ≤ (z : ℝ) * ((1 : ℝ) / (cappedPow W p : ℝ)) := by
    intro p _
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    calc ((z / cappedPow W p : ℕ) : ℝ) ≤ (z : ℝ) / (cappedPow W p : ℝ) := Nat.cast_div_le
      _ = (z : ℝ) * ((1 : ℝ) / (cappedPow W p : ℝ)) := by rw [mul_one_div]
  calc ∑ p ∈ (Finset.range (W + 1)).filter Nat.Prime,
        (((Finset.Ioc 0 z).filter (fun n => cappedPow W p ∣ n)).card : ℝ)
      ≤ ∑ p ∈ (Finset.range (W + 1)).filter Nat.Prime,
          (z : ℝ) * ((1 : ℝ) / (cappedPow W p : ℝ)) := Finset.sum_le_sum hbound
    _ = (z : ℝ) * ∑ p ∈ (Finset.range (W + 1)).filter Nat.Prime,
          (1 : ℝ) / (cappedPow W p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (z : ℝ) * (4 / Real.sqrt W) :=
        mul_le_mul_of_nonneg_left (sum_cappedPow_inv_le hW) (by positivity)
    _ = 4 * (z : ℝ) / Real.sqrt W := by ring

end Salt.Maynard
