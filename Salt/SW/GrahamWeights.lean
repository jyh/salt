/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Graham / Barban–Vehov mollifier weights `θ_d = μ(d)·log(z/d)/log z`

Design: `docs/exploration/s3-hb3-design.md`, node **DH-2b-i** (the product-detector
freeze, HB-ENGINE WP2). This module is the FIRST leg of the frozen DH-2b product
detector `D = Σ_n dhA(n)·(Σ_{d ∣ n, d ≤ z} θ_d)²·K(n/x)` (Benli §§4–5): the
elementary weight algebra the contour assembly (DH-2b-ii) consumes.

## Objects

* `grahamTheta z d = μ(d)·log(z/d)/log z` supported on `d ≤ z` (`grahamTheta`).
  The classical Graham/Barban–Vehov mollifier weight, `θ₁ = 1`, `|θ_d| ≤ 1`.
  **Squarefree support is automatic** — `μ(d) = 0` off squarefree, so no explicit
  `Squarefree` guard is needed (the guard is just the level cap `d ≤ z`).

## Facts landed

* `grahamTheta_one`, `abs_grahamTheta_le_one`, support lemmas.
* `sq_sum_grahamTheta` — the square-expansion identity `(Σ θ_d)² = Σ_d Σ_e θ_d θ_e`
  (the raw double sum DH-2b-ii consumes; `Finset.sum_mul_sum`).
* `grahamTheta_floor` — the `n = 1` floor seam `(Σ_{d ∣ 1} θ_d)² = 1`.
* The two crude G-sums the contour needs (constants free, polylog grade):
  `sum_abs_grahamTheta_div_le` (`Σ_{d ≤ z} |θ_d|/d ≤ 1 + log z`, harmonic × `|θ|≤1`),
  `sum_abs_grahamTheta_rpow_le` (the σ-weighted variant, `≤ z^{1-σ}(1+log z)`) and
  `abs_sum_grahamTheta_div_le` (the Benli-4.1 value bound at `1`, CRUDE `≤ 1+log z`).

**Named residuals (per the DH-2b-i freeze — NOT required for the partial landing):**
(1) the lcm-collection regroup of the double sum `Σ_{m ∣ n}(Σ_{lcm(d,e)=m} θ_d θ_e)`
    (the raw double sum + the crude G-sums suffice for the contour bound); and
(2) the SHARP Barban–Vehov cancellation `Σ_{d ≤ z} θ_d/d ≍ 1/log z` (the crude
    `≤ 1 + log z` bound is used at first pass; the `1/log z` gain via Abel against
    the corpus's Möbius-sum machinery — `Salt.SW.MobiusRate` — is a bonus, unbuilt).

This is elementary weight groundwork: it carries no conditional-correlation content
(that lives in the SiegelSequence-gated detector assembly, DH-2b-ii and beyond).
-/

namespace Salt.SW

open ArithmeticFunction

/-- **The Graham / Barban–Vehov mollifier weight** `θ_d = μ(d)·log(z/d)/log z`,
    supported on `d ≤ z`. Squarefree support is automatic via `μ` (no explicit
    `Squarefree` guard — `μ(d) = 0` off squarefree, and `μ(0) = 0` kills `d = 0`). -/
noncomputable def grahamTheta (z d : ℕ) : ℝ :=
  if d ≤ z then (moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) else 0

/-- On the support `d ≤ z`, `θ_d` is the explicit ratio. -/
lemma grahamTheta_of_le {z d : ℕ} (h : d ≤ z) :
    grahamTheta z d =
      (moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) := by
  simp only [grahamTheta, if_pos h]

/-- Off the level cap (`z < d`), `θ_d = 0`. -/
lemma grahamTheta_of_lt {z d : ℕ} (h : z < d) : grahamTheta z d = 0 := by
  simp only [grahamTheta, if_neg (not_le.mpr h)]

/-- `θ_0 = 0` (via `μ(0) = 0`). -/
@[simp] lemma grahamTheta_zero (z : ℕ) : grahamTheta z 0 = 0 := by
  rw [grahamTheta_of_le (Nat.zero_le z)]; simp

/-- **`θ₁ = 1`** (`log(z/1)/log z = 1`, using `log z ≠ 0` for `z ≥ 2`). -/
lemma grahamTheta_one {z : ℕ} (hz : 2 ≤ z) : grahamTheta z 1 = 1 := by
  have h1z : (1 : ℕ) ≤ z := by omega
  have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : Real.log (z : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hzR)
  rw [grahamTheta_of_le h1z]
  simp only [Nat.cast_one, moebius_apply_one, Int.cast_one, one_mul, div_one]
  rw [div_self hlogz]

/-- **`|θ_d| ≤ 1`** — `|μ(d)| ≤ 1` and `0 ≤ log(z/d) ≤ log z` for `1 ≤ d ≤ z`. -/
lemma abs_grahamTheta_le_one {z : ℕ} (hz : 2 ≤ z) (d : ℕ) : |grahamTheta z d| ≤ 1 := by
  by_cases hdz : d ≤ z
  · rcases Nat.eq_zero_or_pos d with rfl | hd1
    · rw [grahamTheta_zero]; simp
    · have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
      have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hzR
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      have hdz' : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast hdz
      have hzd1 : (1 : ℝ) ≤ (z : ℝ) / (d : ℝ) := (one_le_div hd0).mpr hdz'
      have hlog_nonneg : 0 ≤ Real.log ((z : ℝ) / (d : ℝ)) := Real.log_nonneg hzd1
      have hzdz : (z : ℝ) / (d : ℝ) ≤ (z : ℝ) := div_le_self (by linarith) h1d
      have hlog_le : Real.log ((z : ℝ) / (d : ℝ)) ≤ Real.log (z : ℝ) :=
        Real.log_le_log (by positivity) hzdz
      have ht0 : 0 ≤ Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) :=
        div_nonneg hlog_nonneg hlogz.le
      have ht1 : Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ) ≤ 1 :=
        (div_le_one hlogz).mpr hlog_le
      have hμ : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
      rw [grahamTheta_of_le hdz, mul_div_assoc, abs_mul, abs_of_nonneg ht0]
      calc |((moebius d : ℤ) : ℝ)| * (Real.log ((z : ℝ) / (d : ℝ)) / Real.log (z : ℝ))
          ≤ 1 * 1 := mul_le_mul hμ ht1 ht0 (by norm_num)
        _ = 1 := one_mul 1
  · rw [grahamTheta_of_lt (not_le.mp hdz)]; simp

/-- **The square-expansion identity** (`Finset.sum_mul_sum`): the raw double sum the
    contour assembly (DH-2b-ii) consumes. Stated over an arbitrary index set `S`; the
    intended `S` is `n.divisors.filter (· ≤ z)`, but `θ`'s support makes the filter
    cosmetic (`grahamSum_filter_eq`). -/
lemma sq_sum_grahamTheta (z : ℕ) (S : Finset ℕ) :
    (∑ d ∈ S, grahamTheta z d) ^ 2
      = ∑ d ∈ S, ∑ e ∈ S, grahamTheta z d * grahamTheta z e := by
  rw [sq, Finset.sum_mul_sum]

/-- The level filter `(· ≤ z)` is cosmetic on a divisor sum: `θ` already vanishes for
    `d > z`, so `Σ_{d ∣ n, d ≤ z} θ_d = Σ_{d ∣ n} θ_d`. -/
lemma grahamSum_filter_eq (n z : ℕ) :
    ∑ d ∈ n.divisors.filter (· ≤ z), grahamTheta z d
      = ∑ d ∈ n.divisors, grahamTheta z d := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnd
  have hlt : ¬ (d ≤ z) := fun h => hnd (Finset.mem_filter.mpr ⟨hd, h⟩)
  exact grahamTheta_of_lt (not_le.mp hlt)

/-- **The `n = 1` floor seam** `(Σ_{d ∣ 1} θ_d)² = 1`: the divisors of `1` are `{1}`
    and `θ₁ = 1`, so the square (the sieve positivity of the detector `D`) is `1`. -/
lemma grahamTheta_floor {z : ℕ} (hz : 2 ≤ z) :
    (∑ d ∈ (1 : ℕ).divisors, grahamTheta z d) ^ 2 = 1 := by
  rw [Nat.divisors_one, Finset.sum_singleton, grahamTheta_one hz]; norm_num

/-- The harmonic bound `Σ_{d=1}^{n} 1/d ≤ 1 + log n`, from mathlib's
    `harmonic_le_one_add_log` recast onto `Finset.Icc 1 n`. -/
lemma sum_inv_Icc_le (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ ≤ 1 + Real.log (n : ℝ) := by
  have h := harmonic_le_one_add_log n
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

/-- **G-sum 1** `Σ_{d=1}^{z} |θ_d|/d ≤ 1 + log z` — the harmonic sum times `|θ_d| ≤ 1`. -/
lemma sum_abs_grahamTheta_div_le {z : ℕ} (hz : 2 ≤ z) :
    ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| / (d : ℝ) ≤ 1 + Real.log (z : ℝ) := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_Icc_le z)
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
  rw [inv_eq_one_div]
  gcongr
  exact abs_grahamTheta_le_one hz d

/-- **G-sum 2 (the σ-weighted contour variant)** `Σ_{d=1}^{z} |θ_d|/d^σ ≤
    z^{1-σ}·(1 + log z)` for `0 < σ ≤ 1`. Termwise `d^{-σ} = d^{-1}·d^{1-σ} ≤
    d^{-1}·z^{1-σ}` (since `d ≤ z` and `1-σ ≥ 0`); then G-sum 1. -/
lemma sum_abs_grahamTheta_rpow_le {z : ℕ} (hz : 2 ≤ z) {σ : ℝ}
    (_hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| / (d : ℝ) ^ σ
      ≤ (z : ℝ) ^ (1 - σ) * (1 + Real.log (z : ℝ)) := by
  have hz1σ : (0 : ℝ) ≤ 1 - σ := by linarith
  calc ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| / (d : ℝ) ^ σ
      ≤ ∑ d ∈ Finset.Icc 1 z, (z : ℝ) ^ (1 - σ) * (|grahamTheta z d| / (d : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
        have hdz : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast hd.2
        have hdσ0 : (0 : ℝ) < (d : ℝ) ^ σ := Real.rpow_pos_of_pos hd0 σ
        have hbase : (d : ℝ) ^ (1 - σ) ≤ (z : ℝ) ^ (1 - σ) :=
          Real.rpow_le_rpow hd0.le hdz hz1σ
        have heq : |grahamTheta z d| / (d : ℝ) ^ σ
            = (d : ℝ) ^ (1 - σ) * |grahamTheta z d| / (d : ℝ) := by
          rw [div_eq_div_iff hdσ0.ne' hd0.ne', mul_right_comm, ← Real.rpow_add hd0,
            show (1 - σ) + σ = (1 : ℝ) from by ring, Real.rpow_one,
            mul_comm |grahamTheta z d| ((d : ℝ))]
        calc |grahamTheta z d| / (d : ℝ) ^ σ
            = (d : ℝ) ^ (1 - σ) * |grahamTheta z d| / (d : ℝ) := heq
          _ = (d : ℝ) ^ (1 - σ) * (|grahamTheta z d| / (d : ℝ)) := by rw [mul_div_assoc]
          _ ≤ (z : ℝ) ^ (1 - σ) * (|grahamTheta z d| / (d : ℝ)) :=
              mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = (z : ℝ) ^ (1 - σ) * ∑ d ∈ Finset.Icc 1 z, |grahamTheta z d| / (d : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (z : ℝ) ^ (1 - σ) * (1 + Real.log (z : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_abs_grahamTheta_div_le hz) (by positivity)

/-- **G-sum 3 (the Benli-4.1 value bound at `1`, CRUDE)** `|Σ_{d=1}^{z} θ_d/d| ≤
    1 + log z`. The sharp Barban–Vehov cancellation is `≍ 1/log z`; the crude bound
    (triangle inequality + G-sum 1) suffices for the first-pass contour balance. -/
lemma abs_sum_grahamTheta_div_le {z : ℕ} (hz : 2 ≤ z) :
    |∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ)| ≤ 1 + Real.log (z : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (le_of_eq ?_) (sum_abs_grahamTheta_div_le hz)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ))]

end Salt.SW
