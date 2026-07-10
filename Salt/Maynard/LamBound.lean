/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.KSieve
import Salt.Maynard.Diagonal

/-!
# A crude per-tuple size bound on the Selberg weight `λ` (blueprint N2.3)

The Maynard weights `λ` are `lam k R W y d = (∏ᵢ μ(dᵢ)·dᵢ) · wSum`, where
`wSum` is a divisor-shifted `y`-sum over the sieve support (see
`Salt.Maynard.Diagonal`). This file records the crude absolute bound

    `|λ(d)| ≤ (∏ᵢ dᵢ) · Σ_{r ∈ 𝒟} |y(r)| / ∏ᵢ φ(rᵢ)`

used downstream to package the `Cₖ (1 + log R)^k` shape. The proof is a
two-factor split: `|∏ μ(dᵢ)dᵢ| ≤ ∏ dᵢ` (from `|μ| ≤ 1`) times the triangle
inequality `|wSum| ≤ Σ |y(r)|/∏φ(rᵢ)` (dropping the guard).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- The Möbius–times–index coordinate product is bounded in absolute value by
the plain product of indices, since `|μ n| ≤ 1` and each `dᵢ ≥ 0`. -/
theorem abs_prod_moebius_mul_le {k : ℕ} (d : Fin k → ℕ) :
    |∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ)| ≤ ∏ i, (d i : ℝ) := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _; exact abs_nonneg _
  · intro i _
    rw [abs_mul]
    have hμ : |((μ (d i) : ℤ) : ℝ)| ≤ 1 := by
      have : |((μ (d i) : ℤ) : ℝ)| = ((|μ (d i)| : ℤ) : ℝ) := by
        rw [← Int.cast_abs]
      rw [this]
      have := ArithmeticFunction.abs_moebius_le_one (n := d i)
      exact_mod_cast this
    have hd : |(d i : ℝ)| = (d i : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [hd]
    calc |((μ (d i) : ℤ) : ℝ)| * (d i : ℝ)
        ≤ 1 * (d i : ℝ) := by
          apply mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg _)
      _ = (d i : ℝ) := one_mul _

/-- The divisor-shifted `y`-sum `wSum` is bounded in absolute value by the
full `y`-weight sum over the sieve support: apply the triangle inequality and
drop the divisibility guard. -/
theorem abs_wSum_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (u : Fin k → ℕ) :
    |wSum k R W y u|
      ≤ ∑ r ∈ kSieveIndex k R W, |y r| / ∏ i, (Nat.totient (r i) : ℝ) := by
  rw [wSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro r _
  have hΦnn : (0 : ℝ) ≤ ∏ i, (Nat.totient (r i) : ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  by_cases h : ∀ i, u i ∣ r i
  · rw [if_pos h, abs_div, abs_of_nonneg hΦnn]
  · rw [if_neg h, abs_zero]
    exact div_nonneg (abs_nonneg _) hΦnn

/-- **N2.3 — crude per-tuple bound on the Selberg weight `λ`.** The weight is
controlled coordinatewise by `∏ᵢ dᵢ` times the total `y`-weight over the sieve
support. -/
theorem lam_abs_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) :
    |lam k R W y d|
      ≤ (∏ i, (d i : ℝ)) * ∑ r ∈ kSieveIndex k R W, |y r| / ∏ i, (Nat.totient (r i) : ℝ) := by
  rw [lam, abs_mul]
  apply mul_le_mul
  · exact abs_prod_moebius_mul_le d
  · exact abs_wSum_le k R W y d
  · exact abs_nonneg _
  · exact Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)

/-- **N2.3 corollary — the `y_max·(1+log R)^k` packaging hook.** With
`ymax` an upper bound for `|y r|` on the support, `|λ(d)|` is bounded by
`(∏ᵢ dᵢ)·ymax·Σ_{r} 1/∏φ(rᵢ)`. The remaining `Σ 1/∏φ ≤ (1+log R)^k`-type
estimate is downstream packaging (not part of this raw node). -/
theorem lam_abs_le_of_bounded (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ)
    (ymax : ℝ) (hymax : ∀ r ∈ kSieveIndex k R W, |y r| ≤ ymax) :
    |lam k R W y d|
      ≤ (∏ i, (d i : ℝ)) * (ymax * ∑ r ∈ kSieveIndex k R W, 1 / ∏ i, (Nat.totient (r i) : ℝ)) := by
  refine (lam_abs_le k R W y d).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hΦnn : (0 : ℝ) ≤ ∏ i, (Nat.totient (r i) : ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
  exact mul_le_mul_of_nonneg_right (hymax r hr) (inv_nonneg.mpr hΦnn)

end Salt.Maynard
