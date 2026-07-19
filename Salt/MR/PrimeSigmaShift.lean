/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.NonPret

/-!
# MR-gate S8/MR-CORE wave 1, stone H0 — the prime `σ`-shift and Euler-oscillation bridge

Rung card (S8 MR-CORE FREEZE v2, H0 `PrimeSigmaShift`): the elementary comparison
between the `σ = 1` truncated prime sums `∑_{p≤x} …/p` and the shifted full prime
sums `∑'_p …·p^{-1-1/log x}` that turns the log-Euler product of `ζ` into the
truncated pretentious-distance sum.  Feeds S5's `lambda_nonpret_of_bridge`
(NonPret.lean:114) and the LOG-EULER-OSC flagged node.

Rungs (freeze §WAVE 1 [H0], numerals binding, `−C·logloglog` carried in-statement):
* `mertens_first_upper` (R0.1) — the real-`x` Mertens-1 upper bound, a wrapper on
  the LANDED `sum_log_div_prime_le` (Maynard/Mertens.lean:152).
* `sigma_shift` (R0.3) — `∑_{p≤x}(p^{-1} − p^{-1-δ}) ≤ δ·∑_{p≤x}(log p)/p` at
  `δ = 1/log x`, cashed out to an absolute constant via R0.1.
* `prime_tail_shift` (R0.2) — `∑_{p>x} p^{-1-1/log x} = O(1)` via
  `mertens_second_sharp` (Second.lean:216) + dyadic Abel.
* `euler_osc_truncation` (R0.4) — TWO-SIDED, all 1-bounded `g`:
  `|∑'_p Re(g p)·p^{-1-1/log x} − ∑_{p≤x} Re(g p)/p| ≤ C`.
* `euler_osc_bridge` (R0.5) — `|∑_{p≤x} cos(t·log p)/p − log‖ζ(1+1/log x+it)‖| ≤ K`
  for `e ≤ x`, with the λ-side `≥` and `D(1)`-side `≤` corollaries.

Exit stones: `log_euler_osc_zeta` (LOG-EULER-OSC) + `euler_osc_bridge_le`.

D5 source pins: consumes only LANDED corpus surfaces (MR v4 / MRT v3 unaffected).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## R0.1 — the real-`x` Mertens first-theorem upper bound (`mertens_first_upper`) -/

/-- **Mertens' first theorem, upper bound (real cutoff).**  For `1 ≤ x`,
`∑_{p ≤ x} (log p)/p ≤ log x + (log 4 + 4)`.  A class-A wrapper on the LANDED
`Salt.Maynard.sum_log_div_prime_le` (Maynard/Mertens.lean:152): the integer bound
`≤ log⌊x⌋ + (log 4 + 4)` composed with `log⌊x⌋ ≤ log x`.  (No mathlib Mertens-1
upper bound exists — grepped `Mathlib/NumberTheory/SumPrimeReciprocals.lean` and
the `vonMangoldt` corpus; only the reciprocal-sum divergence is present.) -/
theorem mertens_first_upper {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log x + (Real.log 4 + 4) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hbase := Salt.Maynard.sum_log_div_prime_le hfloor
  have hxpos : (0 : ℝ) < x := by linarith
  have hfle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hfpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hfpos hfle
  linarith

/-! ## R0.3 — the `σ`-shift head comparison (`sigma_shift`) -/

/-- **Per-prime `σ`-shift, upper.**  For `1 ≤ y` and `0 ≤ δ`,
`y^{-1} − y^{-1-δ} ≤ δ·(log y)/y`.  Proof: `y^{-1-δ} = y^{-1}·e^{-δ log y}` and
`1 − e^{-δ log y} ≤ δ log y` (`Real.one_sub_le_exp_neg`). -/
theorem sigma_shift_term_le {y δ : ℝ} (hy : 1 ≤ y) :
    y⁻¹ - y ^ (-1 - δ : ℝ) ≤ δ * Real.log y / y := by
  have hypos : (0 : ℝ) < y := by linarith
  have hyne : y ≠ 0 := hypos.ne'
  have hyinv : (0 : ℝ) < y⁻¹ := by positivity
  have hpow : y ^ (-δ : ℝ) = Real.exp (-(δ * Real.log y)) := by
    rw [Real.rpow_def_of_pos hypos]; congr 1; ring
  have hge : 1 - δ * Real.log y ≤ y ^ (-δ : ℝ) := by
    rw [hpow]; exact Real.one_sub_le_exp_neg (δ * Real.log y)
  have hsplit : y ^ (-1 - δ : ℝ) = y⁻¹ * y ^ (-δ : ℝ) := by
    rw [show (-1 - δ : ℝ) = (-1 : ℝ) + (-δ) from by ring, Real.rpow_add hypos,
      Real.rpow_neg_one]
  rw [hsplit]
  have hmul : y⁻¹ * (1 - δ * Real.log y) ≤ y⁻¹ * y ^ (-δ : ℝ) :=
    mul_le_mul_of_nonneg_left hge hyinv.le
  calc y⁻¹ - y⁻¹ * y ^ (-δ : ℝ)
      ≤ y⁻¹ - y⁻¹ * (1 - δ * Real.log y) := by linarith
    _ = δ * Real.log y / y := by field_simp; ring

/-- **Per-prime `σ`-shift, lower (nonnegativity).**  For `1 ≤ y` and `0 ≤ δ`,
`0 ≤ y^{-1} − y^{-1-δ}` — the shifted power is `≤` the unshifted one. -/
theorem sigma_shift_term_nonneg {y δ : ℝ} (hy : 1 ≤ y) (hδ : 0 ≤ δ) :
    0 ≤ y⁻¹ - y ^ (-1 - δ : ℝ) := by
  have hmono : y ^ (-1 - δ : ℝ) ≤ y ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith [hδ])
  rw [Real.rpow_neg_one] at hmono
  linarith

/-- **The `σ`-shift head bound (R0.3, `sigma_shift`).**  At `δ = 1/log x`, for
`e ≤ x`, `∑_{p≤x}(p^{-1} − p^{-1-δ}) ≤ 1 + (log 4 + 4)`.  Per-prime
`p^{-1} − p^{-1-δ} ≤ δ·(log p)/p` (`sigma_shift_term_le`), summed and bounded by
`δ·(log x + (log 4 + 4))` (`mertens_first_upper`); at `δ = 1/log x` the leading
`δ·log x = 1` and the residual `(log 4 + 4)/log x ≤ log 4 + 4`. -/
theorem sigma_shift {x : ℝ} (hx : Real.exp 1 ≤ x) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        ((p : ℝ)⁻¹ - (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
      ≤ 1 + (Real.log 4 + 4) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hδ0 : 0 ≤ 1 / Real.log x := div_nonneg (by norm_num) hLpos.le
  -- termwise: p^{-1} − p^{-1-δ} ≤ δ·(log p)/p
  have hterm : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
      ((p : ℝ)⁻¹ - (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
        ≤ (1 / Real.log x) * (Real.log p / p) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpy : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
    have := sigma_shift_term_le (δ := 1 / Real.log x) hpy
    rw [mul_div_assoc] at this; linarith
  have hsum_le : ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        ((p : ℝ)⁻¹ - (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
      ≤ ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          (1 / Real.log x) * (Real.log p / p) :=
    Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum_le
  have hmert := mertens_first_upper hx1
  have hδlog : (1 / Real.log x) * Real.log x = 1 := by
    rw [one_div, inv_mul_cancel₀ hLpos.ne']
  have hbound : (1 / Real.log x)
        * (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p)
      ≤ (1 / Real.log x) * (Real.log x + (Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left hmert hδ0
  have hexpand : (1 / Real.log x) * (Real.log x + (Real.log 4 + 4))
      = 1 + (1 / Real.log x) * (Real.log 4 + 4) := by rw [mul_add, hδlog]
  have hresid : (1 / Real.log x) * (Real.log 4 + 4) ≤ Real.log 4 + 4 := by
    have hδ1 : 1 / Real.log x ≤ 1 := (div_le_one hLpos).mpr hlogx1
    exact mul_le_of_le_one_left (by positivity) hδ1
  linarith [hsum_le, hbound, hexpand, hresid]

/-! ## R0.2 tail + R0.4 — the shifted-vs-truncated Euler-oscillation comparison

The full shifted prime sum `∑'_p Re(g p)·p^{-1-δ}` (over ALL primes, `δ = 1/log x`)
and the truncated unshifted sum `∑_{p≤x} Re(g p)/p` differ by `O(1)`, for every
1-bounded `g`.  The head shift is `sigma_shift` (R0.3); the `p>x` tail is R0.2
(`prime_tail_shift`), carried here as the named hypothesis `htail`. -/

/-- The `p > x` tail of the shifted prime series, as an `ℕ`-indexed tail of the
prime-indicator, at exponent `-1-δ`.  R0.2 (`prime_tail_shift`) bounds this by an
absolute constant. -/
noncomputable def primeTailShift (δ : ℝ) (N : ℕ) : ℝ :=
  ∑' i : ℕ, Set.indicator {p : ℕ | Nat.Prime p}
    (fun p => (p : ℝ) ^ (-1 - δ : ℝ)) (i + N)

/-- Summability of the prime-indicator shifted series (`δ > 0`). -/
theorem summable_indicator_prime_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable (Set.indicator {p : ℕ | Nat.Prime p} (fun p => (p : ℝ) ^ (-1 - δ : ℝ))) :=
  Summable.of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) n)
    (fun n => Set.indicator_le_self' (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) n)
    (Real.summable_nat_rpow.mpr (by linarith))

/-- The `g`-weighted shifted prime-indicator series is summable (`δ > 0`,
`g` 1-bounded), majorised by the unweighted one. -/
theorem summable_indicator_prime_re_rpow {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Summable (Set.indicator {p : ℕ | Nat.Prime p}
      (fun p => (g p).re * (p : ℝ) ^ (-1 - δ : ℝ))) := by
  refine Summable.of_norm_bounded (summable_indicator_prime_rpow hδ) (fun n => ?_)
  rw [Real.norm_eq_abs, Set.indicator_apply, Set.indicator_apply]
  by_cases hn : n ∈ {p : ℕ | Nat.Prime p}
  · simp only [if_pos hn]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (le_trans (Complex.abs_re_le_norm _) (hg n))
  · simp only [if_neg hn, abs_zero, le_refl]

/-- The head-shift piece of R0.4: the truncated shifted head minus the truncated
unshifted sum is `O(1)` (bounded by `1 + (log 4 + 4)`), via `sigma_shift` (R0.3)
and `|Re(g p)| ≤ ‖g p‖ ≤ 1`. -/
theorem euler_osc_head_shift {x : ℝ} (hx : Real.exp 1 ≤ x)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1) :
    |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
        - ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (g p).re / p|
      ≤ 1 + (Real.log 4 + 4) := by
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hδ0 : 0 ≤ 1 / Real.log x := div_nonneg (by norm_num) hLpos.le
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_)) (sigma_shift hx)
  rw [Finset.mem_filter] at hp
  have hp2 : 2 ≤ p := hp.2.two_le
  have hpy : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
  have hnn : 0 ≤ (p : ℝ)⁻¹ - (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) :=
    sigma_shift_term_nonneg hpy hδ0
  have hre : |(g p).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) (hg p)
  have hfac : (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) - (g p).re / p
      = (g p).re * ((p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) - (p : ℝ)⁻¹) := by ring
  rw [hfac, abs_mul]
  calc |(g p).re| * |(p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) - (p : ℝ)⁻¹|
      ≤ 1 * |(p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) - (p : ℝ)⁻¹| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg _)
    _ = (p : ℝ)⁻¹ - (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) := by
        rw [one_mul, abs_sub_comm, abs_of_nonneg hnn]

/-- The tail piece of R0.4: the `p > x` tail of the `g`-weighted shifted series is
bounded in absolute value by the (`g`-free) tail constant `Ctail` from R0.2, using
`|Re(g p)| ≤ 1` termwise. -/
theorem euler_osc_tail {δ : ℝ} (hδ : 0 < δ) (N : ℕ) {Ctail : ℝ}
    (htail : ∑' i : ℕ, Set.indicator {p : ℕ | Nat.Prime p}
        (fun p => (p : ℝ) ^ (-1 - δ : ℝ)) (i + N) ≤ Ctail)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1) :
    |∑' i : ℕ, Set.indicator {p : ℕ | Nat.Prime p}
        (fun p => (g p).re * (p : ℝ) ^ (-1 - δ : ℝ)) (i + N)| ≤ Ctail := by
  set F := Set.indicator {p : ℕ | Nat.Prime p}
    (fun p => (g p).re * (p : ℝ) ^ (-1 - δ : ℝ)) with hFdef
  set G := Set.indicator {p : ℕ | Nat.Prime p}
    (fun p => (p : ℝ) ^ (-1 - δ : ℝ)) with hGdef
  have hF : Summable F := summable_indicator_prime_re_rpow hg hδ
  have hG : Summable G := summable_indicator_prime_rpow hδ
  have hFG : ∀ n, |F n| ≤ G n := by
    intro n; rw [hFdef, hGdef, Set.indicator_apply, Set.indicator_apply]
    by_cases hn : n ∈ {p : ℕ | Nat.Prime p}
    · simp only [if_pos hn]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (le_trans (Complex.abs_re_le_norm _) (hg n))
    · simp only [if_neg hn, abs_zero, le_refl]
  have hFN : Summable (fun i => F (i + N)) := (summable_nat_add_iff N).mpr hF
  have hGN : Summable (fun i => G (i + N)) := (summable_nat_add_iff N).mpr hG
  have hnormsum : Summable (fun i => ‖F (i + N)‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_iff.mpr hFN
  calc |∑' i, F (i + N)|
      = ‖∑' i, F (i + N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖F (i + N)‖ := norm_tsum_le_tsum_norm hnormsum
    _ = ∑' i, |F (i + N)| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑' i, G (i + N) := (summable_abs_iff.mpr hFN).tsum_le_tsum (fun i => hFG (i + N)) hGN
    _ ≤ Ctail := htail

/-- **The Euler-oscillation truncation (R0.4, `euler_osc_truncation`), TWO-SIDED.**
For every 1-bounded `g` and `e ≤ x`, at `δ = 1/log x`,
`|∑'_p Re(g p)·p^{-1-δ} − ∑_{p≤x} Re(g p)/p| ≤ Ctail + (1 + (log 4 + 4))`, where
`Ctail` bounds the `p>x` tail (R0.2 hypothesis `htail`).  Assembled from the tail
(`euler_osc_tail`, bounded by `htail`) and the head `σ`-shift
(`euler_osc_head_shift`, i.e. `sigma_shift` R0.3). -/
theorem euler_osc_truncation {x : ℝ} (hx : Real.exp 1 ≤ x) {Ctail : ℝ}
    (htail : primeTailShift (1 / Real.log x) (⌊x⌋₊ + 1) ≤ Ctail)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1) :
    |(∑' p : Nat.Primes, (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
        - ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (g p).re / p|
      ≤ Ctail + (1 + (Real.log 4 + 4)) := by
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hδpos : (0 : ℝ) < 1 / Real.log x := by rw [one_div]; exact inv_pos.mpr hLpos
  have hF : Summable (Set.indicator {p : ℕ | Nat.Prime p}
      (fun p => (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))) :=
    summable_indicator_prime_re_rpow hg hδpos
  have hfull : (∑' p : Nat.Primes, (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
      = ∑' n, Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) n := by
    rw [← tsum_subtype {p : ℕ | Nat.Prime p}
      (fun n : ℕ => (g n).re * (n : ℝ) ^ (-1 - 1 / Real.log x : ℝ))]; rfl
  have hsplit := (Summable.sum_add_tsum_nat_add (⌊x⌋₊ + 1) hF).symm
  have hhead : (∑ n ∈ Finset.range (⌊x⌋₊ + 1), Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) n)
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by
      rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq])
  rw [hfull, hsplit, hhead]
  unfold primeTailShift at htail
  have htl := euler_osc_tail hδpos (⌊x⌋₊ + 1) htail g hg
  have hhd := euler_osc_head_shift hx g hg
  have hregroup : (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
        + (∑' i, Set.indicator {p : ℕ | Nat.Prime p}
            (fun p => (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) (i + (⌊x⌋₊ + 1)))
        - ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (g p).re / p
      = (∑' i, Set.indicator {p : ℕ | Nat.Prime p}
            (fun p => (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) (i + (⌊x⌋₊ + 1)))
        + ((∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
              (g p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))
            - ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (g p).re / p) := by ring
  rw [hregroup]
  exact le_trans (abs_add_le _ _) (by linarith [htl, hhd])

/-! ## R0.5 — the two-sided Euler-oscillation ζ-bridge (`euler_osc_bridge`) -/

/-- The (`s`-independent) Euler `k≥2` remainder constant, `∑'_p p^{-2}`. -/
noncomputable def cpeel : ℝ := ∑' p : Nat.Primes, (1 : ℝ) / (p : ℝ) ^ 2

theorem cpeel_summable : Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ) ^ 2) := by
  refine (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).congr (fun p => ?_)
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num, Real.rpow_neg (Nat.cast_nonneg _),
    Real.rpow_natCast, one_div]

/-- **Per-prime Euler `k≥2` peel bound.**  For prime `p ≥ 2` and `1 ≤ Re s`,
`|Re(−log(1−p^{−s})) − Re(p^{−s})| ≤ 1/p²`.  From mathlib's Taylor remainder
`norm_log_one_sub_inv_sub_self_le` (`‖log(1−z)⁻¹ − z‖ ≤ ‖z‖²(1−‖z‖)⁻¹/2`), with
`z = p^{−s}` and `‖z‖ = p^{−Re s} ≤ 1/2`.  (Freeze cited `prime_power_tail_le`;
the mathlib Taylor bound subsumes it — see NOTES.) -/
theorem peel_term_bound {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    |(-Complex.log (1 - (p : ℂ) ^ (-s))).re - ((p : ℂ) ^ (-s)).re| ≤ 1 / (p : ℝ) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hpge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  set z : ℂ := (p : ℂ) ^ (-s) with hz
  have hsre0 : (-s).re ≠ 0 := by rw [Complex.neg_re]; linarith
  have hnormz : ‖z‖ = (p : ℝ) ^ (-s.re) := by
    rw [hz, Complex.norm_natCast_cpow_of_re_ne_zero _ hsre0, Complex.neg_re]
  have hnormle : ‖z‖ ≤ 1 / (p : ℝ) := by
    rw [hnormz]
    calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
  have hnn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hhalf : ‖z‖ ≤ 1 / 2 := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpge2
    linarith
  have hnlt1 : ‖z‖ < 1 := by linarith
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    have h := Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg])
    simpa [sub_eq_add_neg] using h
  have hlogeq : -Complex.log (1 - z) = Complex.log (1 - z)⁻¹ :=
    (Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)).symm
  have hbnd := Complex.norm_log_one_sub_inv_sub_self_le hnlt1
  have hre : (-Complex.log (1 - z)).re - z.re = ((-Complex.log (1 - z)) - z).re := by
    rw [Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [hlogeq]
  refine le_trans hbnd ?_
  have hden : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hsq : ‖z‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hnn hnormle 2
  have hkey : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have hz2 : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
    nlinarith [hden, hz2]
  have hfin : (1 / (p : ℝ)) ^ 2 = 1 / (p : ℝ) ^ 2 := by rw [div_pow, one_pow]
  linarith [hkey, hsq, hfin.le, hfin.ge]

/-- The real part of `p^{−s}` at `s = σ + it` is `p^{−σ}·cos(t·log p)`. -/
theorem cpow_neg_re {p : ℕ} (hp : 2 ≤ p) (σ t : ℝ) :
    ((p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (p : ℝ) ^ (-σ : ℝ) * Real.cos (t * Real.log p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : (0 : ℕ) < p).ne'
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  rw [Complex.cpow_def_of_ne_zero hp0, hlog, Complex.exp_re]
  have hre : (((Real.log p : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = -(Real.log p * σ) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]; ring
  have him : (((Real.log p : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))).im
      = -(Real.log p * t) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]; ring
  rw [hre, him, Real.cos_neg, Real.rpow_def_of_pos hppos]
  congr 1 <;> congr 1 <;> ring

/-- The `n^{it}` twist is 1-bounded: `‖costwist t n‖ = 1`. -/
theorem costwist_norm (t : ℝ) (n : ℕ) : ‖costwist t n‖ = 1 := by
  unfold costwist; exact Complex.norm_exp_ofReal_mul_I _

/-- **The Euler `k≥2` peel, summed.**  For `1 < Re s`,
`|∑'_p Re(−log(1−p^{−s})) − ∑'_p Re(p^{−s})| ≤ cpeel`.  Both sides are summable
(from `Nat.Primes.summable_rpow` + `Summable.clog_one_sub`, via `reCLM`), and the
difference is bounded termwise by `peel_term_bound`. -/
theorem peel_sum_bound {s : ℂ} (hs : 1 < s.re) :
    |(∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re)
        - ∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re| ≤ cpeel := by
  have hb : ∀ p : Nat.Primes, ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ ((-s).re) := fun p => by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero _
      (by rw [Complex.neg_re]; exact ne_of_lt (by linarith))]
  have hfs : Summable (fun p : Nat.Primes => (p : ℂ) ^ (-s)) :=
    ((Nat.Primes.summable_rpow.mpr (by rw [Complex.neg_re]; linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hb).of_norm
  have hsum : Summable (fun p : Nat.Primes => -Complex.log (1 - (p : ℂ) ^ (-s))) :=
    hfs.clog_one_sub.neg
  have hA : Summable (fun p : Nat.Primes => (-Complex.log (1 - (p : ℂ) ^ (-s))).re) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.summable hsum
  have hB : Summable (fun p : Nat.Primes => ((p : ℂ) ^ (-s)).re) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.summable hfs
  have hdiff := hA.sub hB
  rw [← Summable.tsum_sub hA hB]
  calc |∑' p : Nat.Primes, ((-Complex.log (1 - (p : ℂ) ^ (-s))).re - ((p : ℂ) ^ (-s)).re)|
      = ‖∑' p : Nat.Primes,
          ((-Complex.log (1 - (p : ℂ) ^ (-s))).re - ((p : ℂ) ^ (-s)).re)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' p : Nat.Primes,
          ‖(-Complex.log (1 - (p : ℂ) ^ (-s))).re - ((p : ℂ) ^ (-s)).re‖ :=
        norm_tsum_le_tsum_norm
          (by simpa only [Real.norm_eq_abs] using summable_abs_iff.mpr hdiff)
    _ = ∑' p : Nat.Primes,
          |(-Complex.log (1 - (p : ℂ) ^ (-s))).re - ((p : ℂ) ^ (-s)).re| := by
        simp only [Real.norm_eq_abs]
    _ ≤ ∑' p : Nat.Primes, 1 / (p : ℝ) ^ 2 :=
        (summable_abs_iff.mpr hdiff).tsum_le_tsum
          (fun p => peel_term_bound p.2.two_le (le_of_lt hs)) cpeel_summable
    _ = cpeel := rfl

/-- **R0.2 residual (named).**  The uniform `p>x` tail bound `∑_{p>x} p^{-1-1/log x}
= O(1)`, packaged as a `Prop`.  This is `prime_tail_shift` (freeze [B,250], dyadic
Abel) — the single analytic residual of this file (see NOTES: C-grade-in-Lean). -/
def PrimeTailShiftBounded : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, Real.exp 1 ≤ x →
    primeTailShift (1 / Real.log x) (⌊x⌋₊ + 1) ≤ C

/-- **The two-sided Euler-oscillation ζ-bridge (R0.5 core).**  Given the R0.2 tail
bound, for `e ≤ x` and all `t`,
`|∑_{p≤x} cos(t·log p)/p − log‖ζ(1+1/log x+it)‖| ≤ K` with a UNIFORM `K`.
Assembled from `log_norm_zeta_eq_re_tsum` (the log-Euler product), the `k≥2` peel
(`peel_sum_bound`), the `p^{-s}`↔`costwist` real-part identity (`cpow_neg_re`), and
`euler_osc_truncation` (R0.4) at `g = costwist t`.  `K = cpeel + (Ctail + (1+log4+4))`. -/
theorem euler_osc_bridge (hPTS : PrimeTailShiftBounded) :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (t * Real.log p) / (p : ℝ))
          - Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖|
        ≤ K := by
  obtain ⟨Ctail, hCtail⟩ := hPTS
  refine ⟨cpeel + (Ctail + (1 + (Real.log 4 + 4))), fun x t hx => ?_⟩
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  set s : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + 1 / Real.log x := by
    rw [hsdef]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hs1 : 1 < s.re := by rw [hsre]; have : (0:ℝ) < 1 / Real.log x := by positivity
                            linarith
  have hzeta := log_norm_zeta_eq_re_tsum hs1
  have htsumeq : (∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re)
      = ∑' p : Nat.Primes, (costwist t p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) := by
    refine tsum_congr (fun p => ?_)
    rw [hsdef, cpow_neg_re p.2.two_le (1 + 1 / Real.log x) t, costwist_re,
      show (-1 - 1 / Real.log x : ℝ) = -(1 + 1 / Real.log x) from by ring]
    ring
  have hR04 := euler_osc_truncation hx (hCtail x hx) (costwist t)
    (fun p => le_of_eq (costwist_norm t p))
  have htrunc : (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        (costwist t p).re / (p : ℝ))
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
          Real.cos (t * Real.log p) / (p : ℝ) :=
    Finset.sum_congr rfl (fun p _ => by rw [costwist_re])
  have hpeel := peel_sum_bound hs1
  rw [hzeta, ← htrunc]
  calc |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
              (costwist t p).re / (p : ℝ))
          - ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re|
      ≤ |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
              (costwist t p).re / (p : ℝ))
            - ∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re|
          + |(∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re)
            - ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re| :=
        abs_sub_le _ _ _
    _ ≤ (Ctail + (1 + (Real.log 4 + 4))) + cpeel := by
        apply add_le_add
        · rw [htsumeq, abs_sub_comm]; exact hR04
        · rw [abs_sub_comm]; exact hpeel
    _ = cpeel + (Ctail + (1 + (Real.log 4 + 4))) := by ring

/-- **Exit stone — `euler_osc_bridge_le` (the `D(1)`-side `≤` corollary).**  Given
the R0.2 tail bound, for `e ≤ x` and all `t`,
`log‖ζ(1+1/log x+it)‖ ≤ ∑_{p≤x} cos(t·log p)/p + K` uniformly.  This is the
upper-side of `euler_osc_bridge` used by the `D(1)` region argument. -/
theorem euler_osc_bridge_le (hPTS : PrimeTailShiftBounded) :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
              Real.cos (t * Real.log p) / (p : ℝ)) + K := by
  obtain ⟨K, hK⟩ := euler_osc_bridge hPTS
  exact ⟨K, fun x t hx => by linarith [(abs_le.mp (hK x t hx)).1]⟩

/-- **Exit stone — `log_euler_osc_zeta` (closes the LOG-EULER-OSC flagged node).**
Given the R0.2 tail bound, for `e ≤ x` and all `t`, the truncated oscillation sum
is controlled by the log-modulus of ζ on the `1+1/log x` line:
`∑_{p≤x} cos(t·log p)/p ≤ log‖ζ(1+1/log x+it)‖ + K` uniformly.  This is the λ-side
`≥` direction of the two-sided `euler_osc_bridge` (the log-Euler-oscillation
identity, modulo `O(1)`), the H0 half of NonPret.lean:114's Euler bridge. -/
theorem log_euler_osc_zeta (hPTS : PrimeTailShiftBounded) :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (t * Real.log p) / (p : ℝ))
        ≤ Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ)
            + (t : ℝ) * Complex.I)‖ + K := by
  obtain ⟨K, hK⟩ := euler_osc_bridge hPTS
  exact ⟨K, fun x t hx => by linarith [(abs_le.mp (hK x t hx)).2]⟩

end Salt.MR
