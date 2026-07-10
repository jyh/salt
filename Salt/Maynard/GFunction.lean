/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom

/-!
# N2.6 — the `g`/`φ` comparison lemmas (Maynard track)

`g` is Maynard's totally-multiplicative function with `g(p) = p − 2`. On a
squarefree `r` it equals `∏_{p ∣ r} (p − 2)`; we take that product as the
definition (`gMult`). This file proves the two per-prime comparison estimates
that N5.5 consumes, stated over `ℝ`:

* `gMult_le_totient` — `g(r) ≤ φ(r)` (per prime `p − 2 ≤ p − 1`);
* `totient_cubed_le_gMult_mul` — `φ(r)³ ≤ g(r)·r²` (per prime
  `(p−1)³ ≤ (p−2)·p²`, i.e. `p² ≥ 3p − 1`, true for `p ≥ 3`).

Both hold for squarefree `r` all of whose prime factors are `≥ 3` (least prime
factor `≥ 3`, i.e. `r` odd). Route: `totient_squarefree` +
`Nat.prod_primeFactors_of_squarefree` turn `φ`, `r`, `g` into products over
`r.primeFactors`; push to `ℝ`, then `Finset.prod_le_prod` termwise with the
per-prime inequality by `nlinarith`.
-/

open Finset

namespace Salt.Maynard

/-- `g(r) = ∏_{p ∣ r} (p − 2)` — the S₂ diagonalization denominator (N2.5). On
squarefree `r` this is Maynard's totally-multiplicative `g` with `g(p) = p − 2`. -/
def gMult (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors, (p - 2)

/-- Real-cast form of `gMult`: each `ℕ`-subtraction `p − 2` becomes `(p:ℝ) − 2`,
valid because every prime factor is `≥ 3 ≥ 2`. -/
lemma gMult_cast {r : ℕ} (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 2) := by
  rw [gMult, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have h2 : 2 ≤ p := le_trans (by norm_num) (hodd p hp)
  push_cast [Nat.cast_sub h2]
  ring

/-- `g(r) ≤ φ(r)` for squarefree `r` with least prime factor `≥ 3`
(per prime `p − 2 ≤ p − 1`). -/
theorem gMult_le_totient {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) ≤ (Nat.totient r : ℝ) := by
  rw [gMult_cast hodd, totient_squarefree_cast hr]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · -- `0 ≤ p − 2`
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    linarith
  · -- `p − 2 ≤ p − 1`
    linarith

/-- `φ(r)³ ≤ g(r)·r²` for squarefree `r` with least prime factor `≥ 3`
(per prime `(p−1)³ ≤ (p−2)·p²`, i.e. `p² ≥ 3p − 1`, true for `p ≥ 3`). -/
theorem totient_cubed_le_gMult_mul {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (Nat.totient r : ℝ) ^ 3 ≤ (gMult r : ℝ) * (r : ℝ) ^ 2 := by
  -- Cast `r` itself to the product of its prime factors.
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [totient_squarefree_cast hr, gMult_cast hodd, hrprod]
  -- LHS: `(∏ (p-1))^3 = ∏ (p-1)^3`.
  rw [← Finset.prod_pow]
  -- RHS: `(∏ (p-2)) * (∏ p)^2 = (∏ (p-2)) * (∏ p^2) = ∏ (p-2) * p^2`.
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · -- `0 ≤ (p - 1)^3`
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    positivity
  · -- `(p - 1)^3 ≤ (p - 2) * p^2`
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    nlinarith [hp3, sq_nonneg ((p : ℝ) - 1)]

end Salt.Maynard
