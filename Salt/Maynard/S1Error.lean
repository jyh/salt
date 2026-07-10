/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.KSieve
import Salt.Maynard.Diagonal
import Salt.Maynard.LamBound

/-!
# The S₁ trivial error sum (blueprint N4.2)

N4.1 supplies an `O(1)` count-error for each pair `(d, e)` in the sieve
support. Summed over `(d, e)` weighted by `|λ_d λ_e|`, the total trivial
error is bounded by

    `2^(k+1) · (Σ_{d ∈ 𝒟} |λ(d)|)²`.

The load-bearing content is the **factorization** `s1_trivial_error_le`: a
clean `Finset.sum_mul_sum` identity turning the weighted double sum into a
square of a single sum times the fixed count-error constant `2^(k+1)`.

We then record an explicit polynomial-in-`R` bound on the single sum
`Σ_{d ∈ 𝒟} |λ(d)|` via the N2.3 per-tuple bound `lam_abs_le` and the two
crude size facts `∏ᵢ dᵢ < R` (support constraint) and `|𝒟| ≤ R^k` (the
sieve index is a subset of `(range R)^k`):

    `Σ_{d ∈ 𝒟} |λ(d)| ≤ R^(k+1) · (Σ_r |y r| / ∏ᵢ φ(rᵢ))`.

This is `o(N)` against the `N^{3/5}` headroom for `R = N^{1/5}` (the caller
only needs *some* polynomial-in-`R` bound; the sharp `(log R)^{2k} R²` shape
is downstream packaging, not this node).
-/

open Finset

namespace Salt.Maynard

/-- **N4.2 — the S₁ trivial-error factorization (load-bearing).** The double
sum of `|λ(d)|·|λ(e)|` against the fixed N4.1 count-error constant `2^(k+1)`
factors as `2^(k+1)` times the square of the single sum `Σ_d |λ(d)|`. This is
the `Finset.sum_mul_sum` identity that lets the caller reduce the trivial
error to a *single* `λ`-sum bound (`sum_abs_lam_le` below). -/
theorem s1_trivial_error_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        |lam k R W y d| * |lam k R W y e| * (2 ^ (k + 1) : ℝ)
      ≤ 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W, |lam k R W y d|) ^ 2 := by
  apply le_of_eq
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- **N4.2 — explicit single-sum bound.** `Σ_{d ∈ 𝒟} |λ(d)|` is bounded by
`R^(k+1)` times the total `y`-weight `Σ_r |y r| / ∏ᵢ φ(rᵢ)`. Route: the N2.3
per-tuple bound `|λ(d)| ≤ (∏ᵢ dᵢ)·Σ|y|/∏φ`, then `∏ᵢ dᵢ < R` (support) and
`|𝒟| ≤ R^k` (`kSieveIndex ⊆ (range R)^k`) give `Σ_d ∏ᵢ dᵢ ≤ R^k·R = R^(k+1)`.
A genuine, non-vacuous, polynomial-in-`R` bound of the correct shape. -/
theorem sum_abs_lam_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    ∑ d ∈ kSieveIndex k R W, |lam k R W y d|
      ≤ (R : ℝ) ^ (k + 1)
          * ∑ r ∈ kSieveIndex k R W, |y r| / ∏ i, (Nat.totient (r i) : ℝ) := by
  set S := ∑ r ∈ kSieveIndex k R W, |y r| / ∏ i, (Nat.totient (r i) : ℝ) with hS
  have hSnn : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro r _
    exact div_nonneg (abs_nonneg _)
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  -- Step 1: bound each `|λ(d)|` by `(∏ᵢ dᵢ)·S` (N2.3), sum, pull `S` out.
  have step1 : ∑ d ∈ kSieveIndex k R W, |lam k R W y d|
      ≤ (∑ d ∈ kSieveIndex k R W, ∏ i, (d i : ℝ)) * S := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    exact lam_abs_le k R W y d
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ hSnn
  -- Step 2: `Σ_d ∏ᵢ dᵢ ≤ R^(k+1)`.
  -- Card of the sieve index is ≤ R^k (subset of `(range R)^k`).
  have hcard : (kSieveIndex k R W).card ≤ R ^ k := by
    calc (kSieveIndex k R W).card
        ≤ (Fintype.piFinset (fun _ : Fin k => Finset.range R)).card :=
          Finset.card_filter_le _ _
      _ = R ^ k := by
          rw [Fintype.card_piFinset_const, Finset.card_range]
  calc ∑ d ∈ kSieveIndex k R W, ∏ i, (d i : ℝ)
      ≤ ∑ _d ∈ kSieveIndex k R W, (R : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [mem_kSieveIndex_iff] at hd
        have hlt : (∏ i, d i) < R := hd.2.2.2
        have : ((∏ i, d i : ℕ) : ℝ) < (R : ℝ) := by exact_mod_cast hlt
        rw [Nat.cast_prod] at this
        exact le_of_lt this
    _ = (kSieveIndex k R W).card • (R : ℝ) := by rw [Finset.sum_const]
    _ = ((kSieveIndex k R W).card : ℝ) * (R : ℝ) := by rw [nsmul_eq_mul]
    _ ≤ (R : ℝ) ^ k * (R : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        calc ((kSieveIndex k R W).card : ℝ) ≤ ((R ^ k : ℕ) : ℝ) := by exact_mod_cast hcard
          _ = (R : ℝ) ^ k := by push_cast; ring
    _ = (R : ℝ) ^ (k + 1) := by rw [pow_succ]

end Salt.Maynard
