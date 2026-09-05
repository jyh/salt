/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.GrahamWeights

/-!
# ARM B part B2, wave **W6a** — Jutila's TWO-LEVEL Barban–Vehov weight

Jutila 1977, §2, (2.5)/(2.6): the two-level mollifier weight

    λ_d = μ(d)                              for  d ≤ z₁,
    λ_d = μ(d)·log(z₂/d)/log(z₂/z₁)         for  z₁ ≤ d ≤ z₂,
    λ_d = 0                                 for  z₂ < d,

**built here as a linear combination of the landed ONE-level Graham weight**
`grahamTheta z d = μ(d)·log(z/d)/log z` (`GrahamWeights.lean:57`):

    λ_d = (log z₂ · θ^{(z₂)}_d − log z₁ · θ^{(z₁)}_d) / log(z₂/z₁).

That is `bvWeight` below, and the three case rows (`bvWeight_eq_moebius_of_le`,
`bvWeight_eq_of_mem`, `bvWeight_eq_zero_of_gt`) say the combination IS (2.5)/(2.6).

## Why this node fires now, alone

Lemma 6's proof (p.50) OPENS on the weight's two divisor identities — *"First of all
note that a₁ = 1 and a_n = 0 for 2 ≤ n ≤ z₁"* — where `a_n = Σ_{d ∣ n} λ_d`. Those are
`sum_bvWeight_divisors_one` and `sum_bvWeight_divisors_eq_zero`, and they are
elementary: for `2 ≤ n ≤ z₁` every divisor of `n` sits in the low range, so `λ_d = μ(d)`
there and `Σ_{d ∣ n} μ(d) = 0` (`moebius_mul_coe_zeta` evaluated at `n`) finishes it.
**No `Λ` / `vonMangoldt` anywhere:** the value of `Σ_{d∣n} μ(d)·log d` is never needed,
only that the two levels contribute it identically — and taking the low range through
`bvWeight_eq_moebius_of_le` never forms it at all.

Lemma 4's MEAN bound `Σ_{n ≤ x} a_n² ≪ x/log(z₂/z₁)` — the analytic keystone — is
wave W6b's, in `Salt/SW/GrahamMean.lean`; nothing here depends on it.

## Why the hypotheses are where they are

Jutila's standing constraint at (2.5) is `1 < z₁ < z₂`. It is not decoration: with
Lean's `0/0 = 0` and `log 0 = 0` conventions the rows are FALSE without it, and these
are the witnesses (computed at the seat):

* `bvWeight 2 2 1 = 0 ≠ 1 = μ(1)` — at `z₁ = z₂` the denominator `log(z₂/z₁) = log 1 = 0`
  collapses everything to `0`. Kills `_eq_moebius_of_le` AND `_divisors_one`; that is why
  both carry `z₁ < z₂`.
* `bvWeight 5 2 3 = −log(5/3)/log(5/2) = −0.5575 ≠ 0` — with `z₂ < z₁` the "high" range
  is not empty of `θ^{(z₁)}`. Kills `_eq_zero_of_gt`; hence its `z₁ < z₂`.
* `Σ_{d ∣ 6} bvWeight 6 2 d = −log 2/log 3 = −0.6309 ≠ 0` — same inversion inside a
  divisor sum. Kills `_divisors_eq_zero`; hence its `z₁ < z₂`.
* `_eq_of_mem` held in every one of these, but its proof READS `2 ≤ z₁` (through
  `log z₂ ≠ 0`), so the binder stays.

`2 ≤ z₁` sits on the three rows whose proofs read it (`log z₁ ≠ 0`, `log z₂ ≠ 0`,
`grahamTheta_one`), is DERIVED on `_divisors_eq_zero` (from `2 ≤ n ≤ z₁`), and is
ABSENT on `_eq_zero_of_gt`, where nothing reads it — an unread binder is a linter
warning, and salt's rule is no new warnings.

## The object at the exit values `z₁ = 4`, `z₂ = 16`

`bvWeight 4 16 d` for `d = 1 … 16`:
`1, −1, −1, 0, −0.839, 0.708, −0.596, 0, 0, 0.339, −0.270, 0, −0.150, 0.096, 0.047, 0`
— `μ(d)` exactly on `d ≤ 4`, the log-ramp on `4 ≤ d ≤ 16`, `0` past `16`; and
`Σ_{d ∣ 4} = 0`, `Σ_{d ∣ 1} = 1`. The `example`s at the end of the file check five of
these rows through the theorems, and one (`Σ_{d ∣ 4} = 0`) straight from the definition.
-/

namespace Salt.SW

open ArithmeticFunction

/-- **Jutila's two-level Barban–Vehov weight** (2.5)/(2.6): `λ_d = μ(d)` for `d ≤ z₁`,
`μ(d)·log(z₂/d)/log(z₂/z₁)` on `z₁ ≤ d ≤ z₂`, `0` beyond — written as the linear
combination `(log z₂·θ^{(z₂)}_d − log z₁·θ^{(z₁)}_d)/log(z₂/z₁)` of the landed one-level
`grahamTheta`. The three case rows below verify the equality with (2.5)/(2.6) under
Jutila's standing `1 < z₁ < z₂`. -/
noncomputable def bvWeight (z₁ z₂ d : ℕ) : ℝ :=
  (Real.log z₂ * grahamTheta z₂ d - Real.log z₁ * grahamTheta z₁ d) / Real.log ((z₂ : ℝ) / z₁)

/-- **(2.5), the low range**: `λ_d = μ(d)` for `d ≤ z₁` (`d = z₁` included). Both levels
carry `d`, the `log d` terms cancel, and the numerator is exactly `μ(d)(log z₂ − log z₁)`. -/
theorem bvWeight_eq_moebius_of_le {z₁ z₂ d : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) (hd : d ≤ z₁) :
    bvWeight z₁ z₂ d = (moebius d : ℝ) := by
  have h1z₁ : (1 : ℝ) < (z₁ : ℝ) := by exact_mod_cast (by omega : 1 < z₁)
  have h1z₂ : (1 : ℝ) < (z₂ : ℝ) := by exact_mod_cast (by omega : 1 < z₂)
  have hl₁ : 0 < Real.log (z₁ : ℝ) := Real.log_pos h1z₁
  have hl₂ : 0 < Real.log (z₂ : ℝ) := Real.log_pos h1z₂
  have hlt : Real.log (z₁ : ℝ) < Real.log (z₂ : ℝ) :=
    Real.log_lt_log (by linarith) (by exact_mod_cast hz)
  have hne₁ : Real.log (z₁ : ℝ) ≠ 0 := ne_of_gt hl₁
  have hne₂ : Real.log (z₂ : ℝ) ≠ 0 := ne_of_gt hl₂
  have hnesub : Real.log (z₂ : ℝ) - Real.log (z₁ : ℝ) ≠ 0 := sub_ne_zero_of_ne hlt.ne'
  have hdiv : Real.log ((z₂ : ℝ) / (z₁ : ℝ)) = Real.log (z₂ : ℝ) - Real.log (z₁ : ℝ) :=
    Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hcancel : ∀ L x : ℝ, L ≠ 0 → L * (x / L) = x := by
    intro L x hL
    field_simp
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · simp [bvWeight]
  · have hdz₂ : d ≤ z₂ := by omega
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hlogd₂ : Real.log ((z₂ : ℝ) / (d : ℝ)) = Real.log (z₂ : ℝ) - Real.log (d : ℝ) :=
      Real.log_div (ne_of_gt (by linarith)) (ne_of_gt hd0)
    have hlogd₁ : Real.log ((z₁ : ℝ) / (d : ℝ)) = Real.log (z₁ : ℝ) - Real.log (d : ℝ) :=
      Real.log_div (ne_of_gt (by linarith)) (ne_of_gt hd0)
    simp only [bvWeight, grahamTheta_of_le hdz₂, grahamTheta_of_le hd, hlogd₂, hlogd₁, hdiv]
    rw [hcancel _ _ hne₂, hcancel _ _ hne₁, div_eq_iff hnesub]
    ring

/-- **(2.5), the high range**: `λ_d = 0` for `z₂ < d`. Both levels are off their support
(`z₁ < z₂ < d`), so the numerator vanishes. No `2 ≤ z₁` here — nothing reads it. -/
theorem bvWeight_eq_zero_of_gt {z₁ z₂ d : ℕ} (hz : z₁ < z₂) (hd : z₂ < d) :
    bvWeight z₁ z₂ d = 0 := by
  simp [bvWeight, grahamTheta_of_lt hd, grahamTheta_of_lt (lt_trans hz hd)]

/-- **(2.6), the ramp**: `λ_d = μ(d)·log(z₂/d)/log(z₂/z₁)` on `z₁ ≤ d ≤ z₂`. The `z₁`-level
weight is `0` throughout: at `d = z₁` because `log(z₁/z₁) = log 1 = 0`, and above it
because `d` is off the support. -/
theorem bvWeight_eq_of_mem {z₁ z₂ d : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) (h : z₁ ≤ d ∧ d ≤ z₂) :
    bvWeight z₁ z₂ d
      = (moebius d : ℝ) * Real.log ((z₂ : ℝ) / d) / Real.log ((z₂ : ℝ) / z₁) := by
  obtain ⟨hd1, hd2⟩ := h
  have h1z₁ : (1 : ℝ) < (z₁ : ℝ) := by exact_mod_cast (by omega : 1 < z₁)
  have h1z₂ : (1 : ℝ) < (z₂ : ℝ) := by exact_mod_cast (by omega : 1 < z₂)
  have hne₂ : Real.log (z₂ : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1z₂)
  have hθ₁ : grahamTheta z₁ d = 0 := by
    rcases lt_or_eq_of_le hd1 with hlt | heq
    · exact grahamTheta_of_lt hlt
    · rw [← heq, grahamTheta_of_le (le_refl z₁), div_self (ne_of_gt (by linarith : (0:ℝ) < (z₁:ℝ))),
        Real.log_one, mul_zero, zero_div]
  have hcancel : ∀ L x : ℝ, L ≠ 0 → L * (x / L) = x := by
    intro L x hL
    field_simp
  simp only [bvWeight, hθ₁, grahamTheta_of_le hd2, mul_zero, sub_zero]
  rw [hcancel _ _ hne₂, mul_div_assoc]

/-- **`a_n = 0` on `2 ≤ n ≤ z₁`** (Lemma 6's opening line, p.50): every divisor of such an
`n` lies in the low range, where `λ_d = μ(d)`, and `Σ_{d ∣ n} μ(d) = 0` for `n ≥ 2`.
`2 ≤ z₁` is DERIVED here from `2 ≤ n ≤ z₁`, not bound. -/
theorem sum_bvWeight_divisors_eq_zero {z₁ z₂ n : ℕ} (hz : z₁ < z₂) (h1 : 2 ≤ n) (h2 : n ≤ z₁) :
    ∑ d ∈ n.divisors, bvWeight z₁ z₂ d = 0 := by
  have hz₁ : 2 ≤ z₁ := le_trans h1 h2
  have hrow : ∀ d ∈ n.divisors, bvWeight z₁ z₂ d = ((moebius d : ℤ) : ℝ) := by
    intro d hd
    exact bvWeight_eq_moebius_of_le hz₁ hz (le_trans (Nat.divisor_le hd) h2)
  have hint : ∑ d ∈ n.divisors, (moebius d : ℤ) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply, if_neg (by omega : ¬ n = 1)]
  have hcast : ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ)
      = ((∑ d ∈ n.divisors, (moebius d : ℤ) : ℤ) : ℝ) := by push_cast; rfl
  rw [Finset.sum_congr rfl hrow, hcast, hint, Int.cast_zero]

/-- **`a_1 = 1`** (Lemma 6's opening line, p.50): `divisors 1 = {1}` and `λ_1 = μ(1) = 1`
through the low-range row. -/
theorem sum_bvWeight_divisors_one {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) :
    ∑ d ∈ (1 : ℕ).divisors, bvWeight z₁ z₂ d = 1 := by
  rw [Nat.divisors_one, Finset.sum_singleton,
    bvWeight_eq_moebius_of_le hz₁ hz (by omega : 1 ≤ z₁), moebius_apply_one, Int.cast_one]

/-! ## The exit test at `z₁ = 4`, `z₂ = 16` -/

-- **(a) the five rows, discharged BY the theorems.** `Σ_{d ∣ 4} λ_d = 0` and
-- `Σ_{d ∣ 1} λ_d = 1` are Lemma 6's two identities; `λ_3 = μ(3) = −1` is (2.5) low;
-- `λ_17 = 0` is (2.5) high; `λ_8 = 0` is (2.6) at a non-squarefree `d` (`μ(8) = 0`).
example : ∑ d ∈ (4 : ℕ).divisors, bvWeight 4 16 d = 0 :=
  sum_bvWeight_divisors_eq_zero (by norm_num) (by norm_num) (by norm_num)

example : ∑ d ∈ (1 : ℕ).divisors, bvWeight 4 16 d = 1 :=
  sum_bvWeight_divisors_one (by norm_num) (by norm_num)

example : bvWeight 4 16 3 = -1 := by
  rw [bvWeight_eq_moebius_of_le (by norm_num) (by norm_num) (by norm_num),
    moebius_apply_prime Nat.prime_three]
  norm_num

example : bvWeight 4 16 17 = 0 :=
  bvWeight_eq_zero_of_gt (by norm_num) (by norm_num)

example : bvWeight 4 16 8 = 0 := by
  have hnsf : ¬ Squarefree (8 : ℕ) := by
    intro h
    have h2 := h 2 (by decide)
    rw [Nat.isUnit_iff] at h2
    norm_num at h2
  rw [bvWeight_eq_of_mem (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩,
    moebius_eq_zero_of_not_squarefree hnsf]
  norm_num

-- **(b) one row computed DIRECTLY from the definition**, independent of the five
-- theorems: `divisors 4 = {1, 2, 4}`, and with `L = log 2`,
-- `λ_1 = (4L·1 − 2L·1)/(2L) = 1`, `λ_2 = (4L·(−3L/4L) − 2L·(−L/2L))/(2L) = (−3L + L)/(2L) = −1`,
-- `λ_4 = 0` (`μ(4) = 0`) — so the sum is `1 − 1 + 0 = 0`.
example : ∑ d ∈ (4 : ℕ).divisors, bvWeight 4 16 d = 0 := by
  have hLne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have e16 : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have e4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have l8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have l4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hμ2 : ((moebius 2 : ℤ) : ℝ) = -1 := by
    rw [moebius_apply_prime Nat.prime_two]
    norm_num
  have hμ4 : ((moebius 4 : ℤ) : ℝ) = 0 := by
    have hnsf : ¬ Squarefree (4 : ℕ) := by
      intro h
      have h2 := h 2 (by decide)
      rw [Nat.isUnit_iff] at h2
      norm_num at h2
    rw [moebius_eq_zero_of_not_squarefree hnsf]
    norm_num
  have b1 : bvWeight 4 16 1 = 1 := by
    simp only [bvWeight, grahamTheta_one (by norm_num : 2 ≤ 16),
      grahamTheta_one (by norm_num : 2 ≤ 4), mul_one]
    rw [show ((16 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 4 by norm_num, e16, e4, l4,
      show (4 : ℝ) * Real.log 2 - 2 * Real.log 2 = 2 * Real.log 2 by ring,
      div_self (mul_ne_zero (by norm_num) hLne)]
  have b2 : bvWeight 4 16 2 = -1 := by
    simp only [bvWeight, grahamTheta_of_le (by norm_num : (2 : ℕ) ≤ 16),
      grahamTheta_of_le (by norm_num : (2 : ℕ) ≤ 4)]
    rw [show ((16 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 8 by norm_num,
      show ((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 2 by norm_num,
      show ((16 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 4 by norm_num, e16, e4, l8, l4, hμ2]
    field_simp
    ring
  have b4 : bvWeight 4 16 4 = 0 := by
    simp only [bvWeight, grahamTheta_of_le (by norm_num : (4 : ℕ) ≤ 16),
      grahamTheta_of_le (by norm_num : (4 : ℕ) ≤ 4), hμ4]
    simp
  rw [show (4 : ℕ).divisors = {1, 2, 4} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, b1, b2, b4]
  norm_num

end Salt.SW
