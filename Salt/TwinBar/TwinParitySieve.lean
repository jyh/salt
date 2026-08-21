/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.Wall
import Salt.Chen.BrunEll1
import Salt.BrunLower.MertensDischarge
import Salt.BrunLower.TwinInstance

/-!
# The Liouville-twisted twin sieve (λ-BV wave 1, node B0)

Design: `seat/briefs/2026-08-20-lambda-bv-block-v6-FIRE.md` (§2, row B0).

`twinParitySieve N P hP` is the mathlib `BoundingSieve` that sifts the twin
values `n(n+2)`, `n ∈ [1,N]`, by the primes dividing the squarefree `P`, with
the **parity pin** in the weights: `w(m) = 1 − λ(m)`, `λ` the Liouville
function.  Everything except the weights (and hence the total mass) is the
landed `Salt.TwinSieve.sieve` of `Salt/Brun/Sieve.lean`: the same support, the
same twin density `ν = ρ/·`, whose three multiplicativity/positivity proof
obligations are discharged by reusing the `Salt.TwinSieve` proof terms
verbatim (the `Salt/HB/PairInstance.lean` pattern).

## The third-regime fence

`totalMass` is pinned to the **sum form** `∑ m ∈ support, weights m`, NOT to a
closed form.  The export `twinParitySieve_totalMass` reads it as
`N − ∑_{n ∈ [1,N]} λ(n(n+2))`; keeping the field itself in sum form is what
makes that export a statement about the sieve rather than a definition.  With
the `sMinus` idiom (`totalMass := N`) the `d = 1` atom would degenerate to a
two-point Chowla statement — see F-THIRD-REGIME in the design block.

## Main results

* `twinParitySieve` — the ten-field `BoundingSieve`.
* `twinParitySieve_totalMass` — the total mass as `N − ∑ λ(n(n+2))`.
* `twinParitySieve_prodPrimes`, `twinParitySieve_nu` — `rfl` simp lemmas that
  the downstream main-term transfers consume.
-/

open ArithmeticFunction Finset

namespace Salt.TwinBar

/-- **B0**: the Liouville-twisted twin `BoundingSieve`.  Support, modulus and
density are the landed twin sieve's; the weights carry the parity pin
`1 − λ(m)`, and `totalMass` is their honest sum over the support. -/
noncomputable def twinParitySieve (N P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Icc 1 N).image (fun n => n * (n + 2))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => 1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)
  weights_nonneg := fun m => by have := liouville_real_le m; linarith
  totalMass := ∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
    (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ))
  nu := Salt.TwinSieve.nu
  nu_mult := Salt.TwinSieve.nu_mult
  nu_pos_of_prime := fun p hp _ => Salt.TwinSieve.nu_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => Salt.TwinSieve.nu_lt_one_of_prime p hp

variable {N P : ℕ} {hP : Squarefree P}

/-- The sieve's modulus is `P` (definitionally). -/
@[simp] theorem twinParitySieve_prodPrimes : (twinParitySieve N P hP).prodPrimes = P := rfl

/-- The sieve's density is the landed twin density `ρ/·` (definitionally). -/
@[simp] theorem twinParitySieve_nu :
    (twinParitySieve N P hP).nu = Salt.TwinSieve.nu := rfl

/-- **B0 export**: the total mass is `N − ∑_{n ∈ [1,N]} λ(n(n+2))`.  The `1`s
contribute `#[1,N] = N` and the `λ`s transport across the injection
`n ↦ n(n+2)`. -/
theorem twinParitySieve_totalMass :
    (twinParitySieve N P hP).totalMass
      = (N : ℝ) - ∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) := by
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ))) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  norm_num

end Salt.TwinBar
