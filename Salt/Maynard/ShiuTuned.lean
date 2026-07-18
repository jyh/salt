/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuClasses
import Salt.Maynard.Mertens

/-!
# ShiuTuned — the tuned-shift graded Rankin (NEW-1) and the smooth-prefix tail (NEW-2)

This file supplies the corrected class-III/IV route of the `N-SHIU-CORE` rung, on
top of the landed Rankin engine (`Salt.Maynard.ShiuRankin`), the graded corollaries
(`Salt.Maynard.ShiuGraded`), and the assembly infrastructure
(`Salt.Maynard.ShiuClasses`).

## NEW-1 — the tuned graded Rankin (Shiu's Lemma 4, eq. (25))

The r-decay is manufactured on the LARGE SMOOTH PREFIX c-sum via the *tuned* Rankin
shift `δ = 1 − r·log r/(4·log z)` (not a fixed shift). With the scales
`W = z^{1/2}` and `v = z^{1/r}` this turns the raw gain `W^{δ−1}` into
`exp(−(1/8)·r·log r)` — factorial-scale decay — while the Euler correction
`v^{1−δ} = r^{1/4}` stays subexponential. The mechanism:

* (i) the W-cut: `Σ_{c>W} τ/c ≤ W^{δ−1}·Σ_c τ(c)/c^δ` (landed `sum_tau_smooth_gt_rankin_le`);
* (ii) the *tight* Euler bound `Σ_c τ(c)/c^δ ≤ ∏(1−p^{−δ})^{−2} ≤ exp(2·Σ_{p≤v}p^{−δ} + C)`
  (factor 2, not the lossy 8 — needed to hit `(log z)²` not `(log z)⁸`);
* (iii) the correction split `Σ_{p≤v}p^{−δ} = Σ 1/p + Σ(p^{−δ}−1/p)` with the telescope
  `Σ_{p≤v}(p^{−δ}−1/p) ≤ (1−δ)·v^{1−δ}·(log v + C₀)` (via `e^t−1 ≤ t·e^t` + Mertens-1);
* (iv) the tuned choice `δ = 1 − r·log r/(4·log z)`.

## NEW-2 — the dyadic smooth-prefix tail (class III's kill)

Smooth-number sparsity: a large `y₀`-smooth prefix `c > W = z^{1/2}` is
`z^{−power}`-sparse, so `Σ_{W<c, c y₀-smooth} 1/c` carries a genuine power-of-`z`
saving via the same tuned-shift Rankin trick on the count.
-/

open Nat Finset

namespace Salt.Maynard

/-! ## NEW-1 §(ii) — the tight Euler correction (factor 2, not 8) -/

/-- **The tight per-prime Euler bound.** `(1 − p^{−σ})^{−2} ≤ exp(2·p^{−σ} + 8·(p^{−σ})²)`
for `p ≥ 2`, `σ ≥ 1/2`.  Unlike the lossy `one_sub_rpow_neg_sq_le_exp` (factor 8 on the
linear term), this keeps the linear coefficient at the *correct* value `2` and pushes
the slack into the quadratic term `(p^{−σ})²`, whose prime-sum is `O(1)` for `σ ≥ 3/4`.
From `−log(1−x) ≤ x/(1−x) ≤ x + 4x²` (valid for `x ≤ 3/4`). -/
lemma one_sub_rpow_neg_sq_le_exp_tight {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 ≤ Real.exp (2 * (p : ℝ) ^ (-σ) + 8 * ((p : ℝ) ^ (-σ)) ^ 2) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  set x := (p : ℝ) ^ (-σ) with hx
  have hx0 : 0 ≤ x := (Real.rpow_pos_of_pos hppos _).le
  have hx34 : x ≤ 3 / 4 := rpow_neg_prime_le_three_quarters hp hσ
  have hu : (0 : ℝ) < 1 - x := by linarith
  -- `−log(1−x) ≤ x + 4x²`
  have hlog : -Real.log (1 - x) ≤ x + 4 * x ^ 2 := by
    have h1 : Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h1
    have h2 : (1 - x)⁻¹ - 1 ≤ x + 4 * x ^ 2 := by
      rw [inv_eq_one_div, div_sub_one hu.ne', div_le_iff₀ hu]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 3 - 4 * x)]
    linarith
  have hinv_exp : (1 - x)⁻¹ = Real.exp (-Real.log (1 - x)) := by
    rw [← Real.log_inv, Real.exp_log (by positivity)]
  calc (1 - x)⁻¹ ^ 2 = Real.exp (2 * (-Real.log (1 - x))) := by
        rw [hinv_exp, pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (x + 4 * x ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 * x + 8 * x ^ 2) := by congr 1; ring

/-- The quadratic tail `((p:ℝ)^{−σ})² = (p:ℝ)^{−2σ} ≤ 1/(p:ℝ)^{3/2}` for `σ ≥ 3/4`, `p ≥ 2`. -/
lemma rpow_neg_sq_le_rpow_three_half {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 3 / 4 ≤ σ) :
    ((p : ℝ) ^ (-σ)) ^ 2 ≤ 1 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have heq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hppos.le]
    congr 1; push_cast; ring
  rw [heq, one_div, ← Real.rpow_neg hppos.le]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- **The `O(1)` quadratic prime-tail.** `Σ_{p ≤ v} (p^{−σ})² ≤ ζ(3/2)` (a fixed finite
constant) for `σ ≥ 3/4`.  Bounds each term by `1/p^{3/2}`, extends to all `n ≤ v`, and
compares the partial sum to the convergent `∑' n, 1/n^{3/2}`. -/
lemma sum_rpow_neg_sq_le_zeta (v : ℕ) {σ : ℝ} (hσ : 3 / 4 ≤ σ) :
    ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, ((p : ℝ) ^ (-σ)) ^ 2
      ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hsummable : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n; positivity
  calc ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, ((p : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, 1 / (p : ℝ) ^ (3 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        exact rpow_neg_sq_le_rpow_three_half hp.2.two_le hσ
    _ ≤ ∑ n ∈ Finset.range (v + 1), 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => hnn n)
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
        Summable.sum_le_tsum _ (fun i _ => hnn i) hsummable

/-- **The tight product Euler bound.** `∏_{p ≤ v}(1−p^{−σ})^{−2} ≤ exp(2·Σ_{p≤v}p^{−σ} + 8ζ(3/2))`
for `σ ≥ 3/4`.  The linear coefficient is the *correct* `2`; the constant `8·ζ(3/2)` absorbs
the quadratic tail. -/
lemma prod_one_sub_rpow_neg_sq_le_exp_tight (v : ℕ) {σ : ℝ} (hσ : 3 / 4 ≤ σ) :
    ∏ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2
      ≤ Real.exp (2 * ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (p : ℝ) ^ (-σ)
          + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  set P := (Finset.range (v + 1)).filter Nat.Prime with hP
  have hstep : ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2
      ≤ ∏ p ∈ P, Real.exp (2 * (p : ℝ) ^ (-σ) + 8 * ((p : ℝ) ^ (-σ)) ^ 2) := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      rw [hP, Finset.mem_filter] at hp
      exact one_sub_rpow_neg_sq_le_exp_tight hp.2.two_le (by linarith)
  rw [← Real.exp_sum] at hstep
  refine le_trans hstep (Real.exp_le_exp.mpr ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hquad : 8 * ∑ p ∈ P, ((p : ℝ) ^ (-σ)) ^ 2 ≤ 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left (sum_rpow_neg_sq_le_zeta v hσ) (by norm_num)
  linarith [hquad]

/-! ## NEW-1 §(iii) — the correction telescope -/

/-- `p^{1−σ} − 1 ≤ (1−σ)·log p·p^{1−σ}` for `p ≥ 2`, `σ ≤ 1`.  This is `e^t − 1 ≤ t·e^t`
at `t = (1−σ)·log p ≥ 0` (from `1 − t ≤ e^{−t}`, i.e. `Real.add_one_le_exp`). -/
lemma rpow_sub_one_le {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (_hσ1 : σ ≤ 1) :
    (p : ℝ) ^ (1 - σ) - 1 ≤ (1 - σ) * Real.log p * (p : ℝ) ^ (1 - σ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  set t := (1 - σ) * Real.log p with ht
  have hrp : (p : ℝ) ^ (1 - σ) = Real.exp t := by
    rw [Real.rpow_def_of_pos hppos, ht]; congr 1; ring
  have hexp : Real.exp t - 1 ≤ t * Real.exp t := by
    have h := Real.add_one_le_exp (-t)
    have hep := Real.exp_pos t
    have hmul : (1 - t) * Real.exp t ≤ 1 := by
      calc (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
            mul_le_mul_of_nonneg_right (by linarith) hep.le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hexpand : (1 - t) * Real.exp t = Real.exp t - t * Real.exp t := by ring
    linarith [hmul, hexpand]
  rw [hrp]; exact hexp

/-- **The correction telescope.** `Σ_{p ≤ v}(p^{−σ} − 1/p) ≤ (1−σ)·v^{1−σ}·(log v + C₀)`
with `C₀ = log 4 + 4` (the Mertens-1 constant).  Each term is
`p⁻¹(p^{1−σ}−1) ≤ (1−σ)·v^{1−σ}·(log p / p)` (via `rpow_sub_one_le` + `p^{1−σ} ≤ v^{1−σ}`),
summed by the landed Mertens-1 upper bound `sum_log_div_prime_le`. -/
lemma sum_rpow_neg_sub_inv_le (v : ℕ) {σ : ℝ} (hv : 1 ≤ v) (_hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)
      ≤ (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log v + (Real.log 4 + 4)) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hterm : ∀ p ∈ (Finset.range (v + 1)).filter Nat.Prime,
      (p : ℝ) ^ (-σ) - (p : ℝ)⁻¹ ≤ (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log p / p) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpv, hpp⟩ := hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1R
    have hlogdiv : (0 : ℝ) ≤ Real.log p / p := div_nonneg hlogp hppos.le
    have hpvR : (p : ℝ) ≤ (v : ℝ) := by exact_mod_cast (by omega : p ≤ v)
    have hsub : (p : ℝ) ^ (-σ) - (p : ℝ)⁻¹ = (p : ℝ)⁻¹ * ((p : ℝ) ^ (1 - σ) - 1) := by
      have h1 : (p : ℝ)⁻¹ * (p : ℝ) ^ (1 - σ) = (p : ℝ) ^ (-σ) := by
        rw [← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hppos]; congr 1; ring
      rw [mul_sub, mul_one, h1]
    have hpow := rpow_sub_one_le hp2 hσ1
    have hpvpow : (p : ℝ) ^ (1 - σ) ≤ (v : ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow hppos.le hpvR (by linarith)
    rw [hsub]
    calc (p : ℝ)⁻¹ * ((p : ℝ) ^ (1 - σ) - 1)
        ≤ (p : ℝ)⁻¹ * ((1 - σ) * Real.log p * (p : ℝ) ^ (1 - σ)) := by
          gcongr
      _ = (1 - σ) * (p : ℝ) ^ (1 - σ) * (Real.log p / p) := by rw [div_eq_mul_inv]; ring
      _ ≤ (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log p / p) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpvpow (by linarith : (0 : ℝ) ≤ 1 - σ)) hlogdiv
  calc ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)
      ≤ ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime,
          (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = (1 - σ) * (v : ℝ) ^ (1 - σ)
          * ∑ p ∈ (Finset.range (v + 1)).filter Nat.Prime, (Real.log p / p) := by
        rw [Finset.mul_sum]
    _ ≤ (1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log v + (Real.log 4 + 4)) :=
        mul_le_mul_of_nonneg_left (sum_log_div_prime_le hv)
          (mul_nonneg (by linarith) (Real.rpow_nonneg hvpos.le _))

/-! ## NEW-1 — the tuned graded Rankin (Shiu's Lemma 4, eq. (25)) -/

/-- **NEW-1 — the tuned graded Rankin.**  With `W = z^{1/2}`, `v = z^{1/r}`, and the
*tuned* shift `σ = δ = 1 − r·log r/(4·log z)` (in the honest range `r·log r ≤ log z`,
which forces `δ ≥ 3/4`), the large `v`-smooth prefix sum decays factorially:

    Σ_{c > W, v-smooth, c ≤ N} τ(c)/c
      ≤ exp(−(1/8)·r·log r + r^{1/4}·(log r/2 + C₀))
          · exp(2·Σ_{p ≤ z} 1/p + Ce).

The first factor is the r-decay (`W^{δ−1} = exp(−(1/8) r log r)`, factorial-scale;
the r-independent Euler correction `v^{1−δ} = r^{1/4}` sits subexponentially in the
exponent). The second is the z-main-term `exp(2·Σ_{p≤z}1/p) ≍ (log z)²`, uniform in r.
Composes the landed W-cut (`sum_tau_smooth_gt_rankin_le`), the tight Euler bound
(`prod_one_sub_rpow_neg_sq_le_exp_tight`), and the correction telescope
(`sum_rpow_neg_sub_inv_le`) with the tuning arithmetic. -/
theorem sum_tau_smooth_gt_tuned_le :
    ∃ (Ce C₀ : ℝ), 0 ≤ Ce ∧ 0 ≤ C₀ ∧
    ∀ (N z r v W : ℕ) (σ : ℝ),
      3 ≤ v → 2 ≤ r → 1 ≤ W → 1 < z →
      (r : ℝ) * Real.log r ≤ Real.log z →
      Real.log W = (1 / 2) * Real.log z →
      (r : ℝ) * Real.log v = Real.log z →
      σ = 1 - (r : ℝ) * Real.log r / (4 * Real.log z) →
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
        ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
              + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + C₀))
          * Real.exp (2 * ∑ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Ce) := by
  refine ⟨8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ), (Real.log 4 + 4) / 2, ?_, ?_, ?_⟩
  · have hz : (0 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
      tsum_nonneg (fun n => by positivity)
    linarith
  · have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  intro N z r v W σ hv hr hW hz hrange hlogW hlogv hσ
  have hv2 : 2 ≤ v := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by positivity
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hlogr : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr)
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hvpos : (0 : ℝ) < (v : ℝ) := by positivity
  have hlzne : Real.log z ≠ 0 := hlogz.ne'
  -- the tuning identities
  have h1σ : 1 - σ = (r : ℝ) * Real.log r / (4 * Real.log z) := by rw [hσ]; ring
  have h1σ_nn : (0 : ℝ) ≤ 1 - σ :=
    h1σ ▸ div_nonneg (mul_nonneg hrpos.le hlogr.le) (by positivity)
  have h1σ_le : 1 - σ ≤ 1 / 4 := by
    rw [h1σ, div_le_iff₀ (by positivity)]; linarith [hrange]
  have hσ1 : σ ≤ 1 := by linarith [h1σ_nn]
  have hσ_lb : (3 : ℝ) / 4 ≤ σ := by linarith [h1σ_le]
  have hσ_gt : 1 / 2 < σ := by linarith [hσ_lb]
  have hlv : Real.log v = Real.log z / r := by
    rw [eq_div_iff hrpos.ne']; linear_combination hlogv
  -- Rankin gain: W^{−(1−σ)} = exp(−(1/8) r log r)
  have hgain : (W : ℝ) ^ (-(1 - σ)) = Real.exp (-((r : ℝ) * Real.log r) / 8) := by
    rw [Real.rpow_def_of_pos hWpos]; congr 1
    rw [hlogW, h1σ]; field_simp; ring
  -- (1−σ)·log v = log r / 4
  have hσlogv : (1 - σ) * Real.log v = Real.log r / 4 := by
    rw [h1σ, hlv]; field_simp
  -- v^{1−σ} = r^{1/4}
  have hv1σ : (v : ℝ) ^ (1 - σ) = (r : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hvpos, Real.rpow_def_of_pos hrpos]; congr 1
    rw [mul_comm (Real.log v) (1 - σ), hσlogv]; ring
  -- v ≤ z (for the main-term extension)
  have hvz : v ≤ z := by
    have hlogvz : Real.log v ≤ Real.log z := by
      rw [hlv]; exact div_le_self hlogz.le (by exact_mod_cast (by omega : 1 ≤ r))
    have hvzR : (v : ℝ) ≤ (z : ℝ) := by
      have := Real.exp_le_exp.mpr hlogvz
      rwa [Real.exp_log hvpos, Real.exp_log hzpos] at this
    exact_mod_cast hvzR
  -- the correction sub-bound
  have hr4nn : (0 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hrpos.le _
  have hl4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hpiece_a : 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * Real.log v
      = (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2) := by
    rw [show 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * Real.log v
        = 2 * (r : ℝ) ^ (1 / 4 : ℝ) * ((1 - σ) * Real.log v) by ring, hσlogv]; ring
  have hsubbound : 2 * ((1 - σ) * (v : ℝ) ^ (1 - σ) * (Real.log v + (Real.log 4 + 4)))
      ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2) := by
    rw [hv1σ]
    have hpiece_b : 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log 4 + 4)
        ≤ (r : ℝ) ^ (1 / 4 : ℝ) * ((Real.log 4 + 4) / 2) := by
      rw [show 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log 4 + 4)
          = (r : ℝ) ^ (1 / 4 : ℝ) * (2 * (1 - σ) * (Real.log 4 + 4)) by ring]
      apply mul_le_mul_of_nonneg_left _ hr4nn
      nlinarith [h1σ_le, hl4]
    have expand : 2 * ((1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log v + (Real.log 4 + 4)))
        = 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * Real.log v
          + 2 * (1 - σ) * (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log 4 + 4) := by ring
    rw [expand, hpiece_a, mul_add]
    linarith [hpiece_b]
  -- the exponent inequality (2·Σ_{v} p^{−σ} folded to the main term + decay correction)
  set Ppv := (Finset.range (v + 1)).filter Nat.Prime with hPpv
  set Ppz := (Finset.range (z + 1)).filter Nat.Prime with hPpz
  have hcorr := sum_rpow_neg_sub_inv_le v (by omega : 1 ≤ v) (by linarith : 0 ≤ σ) hσ1
  rw [← hPpv] at hcorr
  have hexp_bound : 2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ)
      ≤ (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2)
        + 2 * ∑ p ∈ Ppz, (p : ℝ)⁻¹ := by
    have hsub : ∑ p ∈ Ppv, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)
        = ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) - ∑ p ∈ Ppv, (p : ℝ)⁻¹ := by
      rw [Finset.sum_sub_distrib]
    have hsubset : Ppv ⊆ Ppz := by
      rw [hPpv, hPpz]
      apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hmain_ext : ∑ p ∈ Ppv, (p : ℝ)⁻¹ ≤ ∑ p ∈ Ppz, (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ => by positivity)
    linarith [hcorr, hsub, hmain_ext, hsubbound]
  -- assemble
  have hraw := sum_tau_smooth_gt_rankin_le N v W σ hv2 hσ_gt hσ1 hW
  have hprod := prod_one_sub_rpow_neg_sq_le_exp_tight v hσ_lb
  rw [← hPpv] at hraw hprod
  rw [← Real.exp_add]
  calc ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
      ≤ (W : ℝ) ^ (-(1 - σ)) * ∏ p ∈ Ppv, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := hraw
    _ ≤ (W : ℝ) ^ (-(1 - σ))
          * Real.exp (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hWpos.le _)
    _ = Real.exp (-((r : ℝ) * Real.log r) / 8)
          * Real.exp (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [hgain]
    _ = Real.exp (-((r : ℝ) * Real.log r) / 8
          + (2 * ∑ p ∈ Ppv, (p : ℝ) ^ (-σ) + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ))) := by
        rw [← Real.exp_add]
    _ ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
          + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + (Real.log 4 + 4) / 2)
          + (2 * ∑ p ∈ Ppz, (p : ℝ)⁻¹ + 8 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ))) := by
        apply Real.exp_le_exp.mpr; linarith [hexp_bound]

/-! ## NEW-2 — the dyadic smooth-prefix tail (class III's kill) -/

/-- **NEW-2 — the smooth-prefix tail.**  The *unweighted* large-smooth-prefix sum
`Σ_{c > W, y₀-smooth, c ≤ N} 1/c` carries the SAME tuned-Rankin decay as NEW-1.  When
the smooth bound `v = y₀ = z^{1/r}` is polylog-grade, `r = u = log z/log y₀` is large and
`exp(−(1/8)·r·log r) = u^{−u/8}` is the de Bruijn `ρ(u)`-grade — a genuine
power-of-`z` saving (smooth-number sparsity).  A direct corollary of NEW-1 via `1 ≤ τ(c)`
(the plain count is dominated by the `τ`-weighted count).  This is the class-III kill:
no `τ(d)` weight is paid, and the large smooth prefix is `z^{−power}`-sparse. -/
theorem sum_smooth_gt_tuned_le :
    ∃ (Ce C₀ : ℝ), 0 ≤ Ce ∧ 0 ≤ C₀ ∧
    ∀ (N z r v W : ℕ) (σ : ℝ),
      3 ≤ v → 2 ≤ r → 1 ≤ W → 1 < z →
      (r : ℝ) * Real.log r ≤ Real.log z →
      Real.log W = (1 / 2) * Real.log z →
      (r : ℝ) * Real.log v = Real.log z →
      σ = 1 - (r : ℝ) * Real.log r / (4 * Real.log z) →
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (1 : ℝ) / (c : ℝ)
        ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
              + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + C₀))
          * Real.exp (2 * ∑ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Ce) := by
  obtain ⟨Ce, C₀, hCe, hC₀, hbound⟩ := sum_tau_smooth_gt_tuned_le
  refine ⟨Ce, C₀, hCe, hC₀, ?_⟩
  intro N z r v W σ hv hr hW hz hrange hlogW hlogv hσ
  refine le_trans ?_ (hbound N z r v W σ hv hr hW hz hrange hlogW hlogv hσ)
  apply Finset.sum_le_sum
  intro c hc
  rw [Finset.mem_filter, Finset.mem_Icc] at hc
  have hc0 : c ≠ 0 := by omega
  have htau : (1 : ℝ) ≤ (c.divisors.card : ℝ) := by
    have : 1 ≤ c.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hc0⟩
    exact_mod_cast this
  gcongr

end Salt.Maynard
