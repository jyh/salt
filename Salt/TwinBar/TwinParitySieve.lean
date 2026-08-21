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

## Node B1 — the remainder split and the named arithmetic input

* `L N d` — the Liouville sum over the twin values `n(n+2)`, `n ∈ [1,N]`, that
  `d` divides.  `L N 1` is the full sum.
* `rem_split` — for EVERY `d` (no side condition): the twisted sieve's
  remainder is the landed twin remainder `_root_.rem d N` minus the Liouville
  discrepancy `L N d − ν(d)·L N 1`.  At `d = 0` both sides are `0`, and the
  proof needs no case split: `ring` sees `(d : ℝ)⁻¹` as an atom.
* `LiouvilleTwinDisp N P lvl B` — the named arithmetic input: the discrepancy
  summed over `d ∣ P` below the level is at most `B`.  Its shape is
  `rosserRemainder`'s **verbatim** — an `ite` over the FULL divisor index, not
  a `filter` — so that B3 can pair the two term-by-term under
  `Finset.sum_le_sum`.  Wave 1 claims nothing about `B`.
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

/-! ## λ-BV wave 1, node B1 — the remainder split and the arithmetic input -/

/-- **B1**: the Liouville sum over the twin values `n(n+2)`, `n ∈ [1,N]`, whose
product is divisible by `d`.  `L N 0 = 0` (no `n ≥ 1` has `0 ∣ n(n+2)`) and
`L N 1 = ∑_{n ∈ [1,N]} λ(n(n+2))` is the full sum. -/
noncomputable def L (N d : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
    ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)

/-- `L N 1` is the unfiltered Liouville sum, since `1 ∣ n(n+2)` always. -/
theorem L_one : L N 1
    = ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) := by
  rw [L, Finset.filter_true_of_mem (fun n _ => one_dvd _)]

/-- The twisted sieve's weighted count of multiples of `d`: the honest
progression count `#{n ∈ [1,N] : d ∣ n(n+2)}` minus the Liouville sum `L N d`
(the parity pin `w = 1 − λ` splits the summand). -/
theorem twinParitySieve_multSum (d : ℕ) :
    (twinParitySieve N P hP).multSum d
      = (((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - L N d := by
  rw [L]
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      if d ∣ m then (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    ← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **B1**: the remainder split, for EVERY `d` — no side condition.  The
twisted sieve's remainder is the landed twin remainder `_root_.rem d N` minus
the Liouville discrepancy `L N d − ν(d)·L N 1`.  Both the multiplicity count
and the `ν(d)·N` main term are shared with the untwisted sieve; the parity pin
contributes exactly the discrepancy.  At `d = 0` every term is `0` and the
identity holds with no case split (`ν 0 = 0`, `L N 0 = 0`, `rem 0 N = 0`). -/
theorem rem_split (d : ℕ) :
    (twinParitySieve N P hP).rem d
      = _root_.rem d N - (L N d - Salt.TwinSieve.nu d * L N 1) := by
  rw [BoundingSieve.rem, twinParitySieve_multSum, twinParitySieve_nu,
    twinParitySieve_totalMass, ← L_one, _root_.rem, Salt.TwinSieve.nu_apply]
  ring

/-- **B1**: the named arithmetic input of the λ-BV block — a Bombieri–
Vinogradov statement for the Liouville discrepancy of the twin values.  The
shape is `Salt.Chen.rosserRemainder`'s verbatim (an `ite` over the full divisor
index of `P`, not a `filter`), so that the assembly can pair the two sums
term-by-term.  Wave 1 asserts nothing about `B`: it is a parameter. -/
def LiouvilleTwinDisp (N P : ℕ) (lvl B : ℝ) : Prop :=
  ∑ d ∈ P.divisors, (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0) ≤ B

end Salt.TwinBar
