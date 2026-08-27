/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.Wall
import Salt.SW.CoprimeBV
import Salt.Chen.BrunEll1
import Salt.BrunLower.MertensDischarge
import Salt.BrunLower.TwinInstance
import Salt.Maynard.GehPp2

/-!
# The Liouville-twisted twin sieve (λ-BV wave 1, node B0)

Design: `2026-08-20-lambda-bv-block-v6-FIRE.md` (§2, row B0).

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

/-! ## λ-BV wave 1, node B2 — the ten Props of `brun_lower_ell1` at `twinParitySieve` -/

/-- **B2 (`htotalMass`)**: the twisted total mass is nonnegative.  Every weight
`1 − λ(m)` is, because `λ(m) ≤ 1` pointwise (`liouville_real_le`,
`Salt/TwinBar/ParityWall.lean:98`).  This is the ONLY bound wave 1 places on a Liouville
sum, and it is the pointwise-trivial one — no sign, no size, no cancellation
(F-THIRD-REGIME). -/
theorem twinParitySieve_totalMass_nonneg :
    0 ≤ (twinParitySieve N P hP).totalMass := by
  change 0 ≤ ∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
    (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ))
  exact Finset.sum_nonneg fun m _ => by have := liouville_real_le m; linarith

/-- **B2 (`hz`)**: the NAMED threshold form.  `brun_lower_ell1` asks only for `1 < z`;
wave 1 carries the far stronger `z ≥ z₀ = exp(exp(100/λ))` of
`Salt/BrunLower/MertensDischarge.lean:63` (at `λ = 1/4` that is `loglog z ≥ 400`), because
`hMert_twin` needs it.  This is the one-line step down to the door's own hypothesis. -/
theorem one_lt_of_zThresh {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : Salt.BrunLower.zThresh lam ≤ z) : 1 < z := by
  have h2 := (Salt.BrunLower.zThresh_facts hlam hlam' hz).2.2.2.2.2.2
  linarith

/-- **B2 (`hMert`)**: PM2 (`hMert_twin`, `Salt/BrunLower/MertensDischarge.lean:602`) at the
twisted sieve.  `Wratio` reads only `prodPrimes` and `nu` (`Salt/BrunLower/WRatio.lean:85`,
`windowPrimes` at :77), and for `twinParitySieve` both are DEFINITIONALLY the landed twin
sieve's — so the twisted statement IS the landed `hMert_twinSieve`'s (:660) after a bare
`change` (a `show` here is defeq-only too, but trips the `linter.style.show` gate), with no
transfer lemma, no `simp` and no re-proof.  In particular the `ν(2) ≤ 1/2` and
`ν(p) ≤ 2/p` obligations are already discharged there. -/
theorem twinParitySieve_hMert {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : Salt.BrunLower.zThresh lam ≤ z)
    (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    ∀ n ∈ Finset.Icc 1 (Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin lam z) z),
      Real.log (Salt.BrunLower.Wratio (twinParitySieve N P hP)
          (Salt.BrunLower.LamTwin lam z) z n) ≤ (n : ℝ) * (2 * lam) := by
  change ∀ n ∈ Finset.Icc 1 (Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin lam z) z),
      Real.log (Salt.BrunLower.Wratio (Salt.TwinSieve.sieve N P hP)
          (Salt.BrunLower.LamTwin lam z) z n) ≤ (n : ℝ) * (2 * lam)
  exact Salt.BrunLower.hMert_twinSieve hP hlam hlam' hz hpz

/-- **B2 — the ten Props discharged**: `Salt.Chen.brun_lower_ell1`
(`Salt/Chen/BrunEll1.lean:191`) instantiated at `twinParitySieve`, at the primary
operating point `b = 1`, `λ = 1/4`, `Λ = LamTwin (1/4) z`, `κ = 2λ` (F-OPERATING-POINT).

Seven of the ten hypotheses are discharged in place — `hb`/`hlam` by `norm_num`,
`h12` by the landed `Salt.HB.lam_exp_lt_one` (`Salt/HB/RosserDim4.lean:740`), `hLam` by
`Salt.BrunLower.LamTwin_pos` (`MertensDischarge.lean:124`), `hkappa` by `le_rfl` at
`κ = 2λ`, `htotalMass` by `twinParitySieve_totalMass_nonneg`, `hMert` by
`twinParitySieve_hMert`.  `hQ`, `hz` and `hzprimes` stay PARAMETERS, with `hz` in the
named `zThresh` form (it is what `hMert` consumes; `1 < z` is derived from it through
`one_lt_of_zThresh`).  `hzprimes` passes through definitionally — the sieve's `prodPrimes`
is `P` by `rfl`.

The cut keeps its ℕ-truncated-subtraction shape and is reduced at `b = 1` by `omega`
(F-LEVEL): `2b−2+1 = 1` and `2b−2+2r−1 = 2r−1` with `r = minLevel Λ z`.  No ℝ restatement
of the exponent is made, and the level stays symbolic in `Q` — wave 1 pins no numeral.

Scope: this is the DOOR, not a twin-prime claim.  The right-hand `siftedSum` is bounded
BELOW by a main term minus `rosserRemainder`, and nothing here bounds that remainder. -/
theorem twinParitySieve_brun_lower_ell1 {z : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    (twinParitySieve N P hP).totalMass * Salt.BrunLower.W (twinParitySieve N P hP)
        * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
            / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
      - Salt.Chen.rosserRemainder (twinParitySieve N P hP)
          (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
                * Real.log z)
              * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                  - 1 : ℕ)))
      ≤ (twinParitySieve N P hP).siftedSum := by
  have h := Salt.Chen.brun_lower_ell1 (twinParitySieve N P hP)
    (lam := 1 / 4) (Lam := Salt.BrunLower.LamTwin (1 / 4) z) (z := z)
    (kappa := 2 * (1 / 4)) (b := 1) Q hQ le_rfl (by norm_num)
    (Salt.HB.lam_exp_lt_one (by norm_num) le_rfl)
    (Salt.BrunLower.LamTwin_pos (by norm_num) le_rfl hz)
    (one_lt_of_zThresh (by norm_num) le_rfl hz)
    twinParitySieve_totalMass_nonneg (fun p hp => hzprimes p hp) le_rfl
    (twinParitySieve_hMert (by norm_num) le_rfl hz hzprimes)
  have e1 : (2 * 1 - 2 + 1 : ℕ) = 1 := by omega
  have e2 : (2 * 1 - 2 + 2 * Salt.BrunLower.minLevel
        (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 : ℕ)
      = 2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 := by omega
  rw [e1, e2, Nat.cast_one] at h
  exact h

/-! ## λ-BV wave 1, node B3 — the explicit remainder majorant and the assembly -/

/-- **B3**: the explicit majorant for the UNTWISTED half of `rem_split` — the landed twin
remainder `_root_.rem d N` summed over the divisors of `P` below a level.  It is the `2^ω`
divisor bound `sum_two_pow_omega_le` (`Salt/Maynard/GehPp2.lean:113`, a **root-level**
declaration: that file carries no `namespace`) read at the level's floor,
`⌊lvl⌋₊·(1 + log ⌊lvl⌋₊)`.  No Liouville input enters here — the parity pin's entire
contribution is the OTHER half of the split, and it is named, not bounded. -/
noncomputable def Btwin (lvl : ℝ) : ℝ := (⌊lvl⌋₊ : ℝ) * (1 + Real.log (⌊lvl⌋₊ : ℝ))

/-- **B3**: the landed twin remainder, summed over `d ∣ P` below the level, is at most
`Btwin lvl`.  The chain is `rem_abs_le` (`Salt/Brun/M2.lean:241`, `|rem d| ≤ ρ(d)`) →
`rho_squarefree_le` (`:206`, `ρ(d) ≤ 2^ω(d)` for squarefree `d`, and every `d ∣ P` is
squarefree) → the re-index of `Salt/Brun/M5Assembly.lean:209-239` (`Finset.sum_filter`, then
`Finset.sum_le_sum_of_subset_of_nonneg` onto the level's initial segment) →
`sum_two_pow_omega_le`.  The `2^ω` route replaces that idiom's `3^ω` constant; the N4.2 `y⁴`
step of `M5Assembly.lean:240` is NOT used. -/
theorem twinRem_sum_le (hPsq : Squarefree P) {lvl : ℝ} (hlvl : 1 ≤ lvl) :
    (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |_root_.rem d N| else 0) ≤ Btwin lvl := by
  have hfl : 1 ≤ ⌊lvl⌋₊ := Nat.le_floor (by exact_mod_cast hlvl)
  have hsub : P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl) ⊆ Finset.Icc 1 ⌊lvl⌋₊ := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2.le⟩
  have hstep1 : (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |_root_.rem d N| else 0)
      = ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), |_root_.rem d N| := by
    rw [Finset.sum_filter]
  have hstep2 : (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), |_root_.rem d N|)
      ≤ ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), (2 : ℝ) ^ _root_.omega d := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have h1 : |_root_.rem d N| ≤ (rho d : ℝ) :=
      rem_abs_le d N (Nat.pos_of_mem_divisors hd.1).ne'
    have h2 : (rho d : ℝ) ≤ (2 : ℝ) ^ _root_.omega d := by
      exact_mod_cast rho_squarefree_le d
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd.1) hPsq)
    linarith
  have hstep3 : (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), (2 : ℝ) ^ _root_.omega d)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊lvl⌋₊, (2 : ℝ) ^ _root_.omega q := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro d _ _
    positivity
  have hstep4 : (∑ q ∈ Finset.Icc 1 ⌊lvl⌋₊, (2 : ℝ) ^ _root_.omega q) ≤ Btwin lvl := by
    rw [Btwin]
    exact _root_.sum_two_pow_omega_le ⌊lvl⌋₊ hfl
  rw [hstep1]
  linarith

/-- **B3 — the assembly.**  The twisted Rosser remainder is at most `Btwin lvl + B`, for any
`B` the named arithmetic input `LiouvilleTwinDisp` supplies.  Term-by-term through the landed
`rem_split` (`:131`) and the triangle inequality, then `Finset.sum_le_sum` — the two sums pair
because `LiouvilleTwinDisp` was given `rosserRemainder`'s shape verbatim (an `ite` over the
FULL divisor index, not a `filter`).  The idiom is `goldBVSum_le_split`
(`Salt/Goldbach/A1.lean:286`, body from `:293`); the second landed instance is
`switchSieve_rosserRemainder_split_le` (`Salt/Chen/SwitchBV.lean:316`, body from `:321`).

Scope: still a DOOR.  `Btwin` is explicit and unconditional, but `B` is a PARAMETER — wave 1
asserts nothing about its size, and nothing here is a twin-prime claim. -/
theorem twinParitySieve_rosserRemainder_le {lvl B : ℝ} (hlvl : 1 ≤ lvl)
    (hdisp : LiouvilleTwinDisp N P lvl B) :
    Salt.Chen.rosserRemainder (twinParitySieve N P hP) lvl ≤ Btwin lvl + B := by
  have hsplit : Salt.Chen.rosserRemainder (twinParitySieve N P hP) lvl
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |_root_.rem d N| else 0)
        + ∑ d ∈ P.divisors,
            (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0) := by
    rw [Salt.Chen.rosserRemainder, twinParitySieve_prodPrimes, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h : (d : ℝ) < lvl
    · rw [if_pos h, if_pos h, if_pos h, rem_split d]
      exact abs_sub _ _
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have h1 : (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |_root_.rem d N| else 0) ≤ Btwin lvl :=
    twinRem_sum_le hP hlvl
  have h2 : (∑ d ∈ P.divisors,
      (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0)) ≤ B := hdisp
  linarith

/-! ## λ-BV wave 1, node B4 — the level's floor and the terminal -/

/-- **B4 (the glue)** — the DANGLING INTERFACE between the two green halves, which no
build reports: B3's consumer `twinParitySieve_rosserRemainder_le` (`:292`) demands
`1 ≤ lvl`, and B2's producer `twinParitySieve_brun_lower_ell1` (`:206`) carries the level
`Q · (exp(…·log z) · 2^(2r−1))` — nothing in the tree supplied `1 ≤` that product.

Each of the three factors is `≥ 1` on its own, so no size input is needed and `minLevel`'s
own lower bound (`Salt/BrunLower/Defs.lean:114`) is NOT consumed: `2 ^ k ≥ 1` holds for
every `k : ℕ`, truncation included.  `Q` is the door's own `hQ`; the exponent is
nonnegative because `LamTwin (1/4) z > 0` (`MertensDischarge.lean:124`) makes
`(exp Λ − 1)⁻¹ > 0`, and `1 < z` (`one_lt_of_zThresh`, `:164`) makes `log z ≥ 0`. -/
theorem one_le_ell1_level {z : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z) :
    1 ≤ Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
          * Real.log z)
        * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 : ℕ)) := by
  have hz1 : (1 : ℝ) < z := one_lt_of_zThresh (by norm_num) le_rfl hz
  have hLam : 0 < Salt.BrunLower.LamTwin (1 / 4) z :=
    Salt.BrunLower.LamTwin_pos (by norm_num) le_rfl hz
  have hexpLam : 1 < Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) := by
    have h := Real.add_one_le_exp (Salt.BrunLower.LamTwin (1 / 4) z)
    linarith
  have hinv : 0 < (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹ :=
    inv_pos.mpr (by linarith)
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hexpE : 1 ≤ Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
      * Real.log z) := Real.one_le_exp (mul_nonneg (by linarith) hlogz)
  have hpow : (1 : ℝ) ≤ 2 ^ (2 * Salt.BrunLower.minLevel
      (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 : ℕ) := one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le hQ (one_le_mul_of_one_le_of_one_le hexpE hpow)

/-- **B4 — the terminal of λ-BV wave 1.**  Given the named arithmetic input
`LiouvilleTwinDisp` at the ℓ¹ door's own level, EITHER the parity-pinned main term is
capped by the explicit majorant `Btwin` plus the input's `B`, OR the twisted sifted sum is
strictly positive.  The skeleton is `le_or_gt` on `siftedSum` and `linarith`: B2's door
gives `mainTerm − rosserRemainder ≤ siftedSum` and B3's assembly gives
`rosserRemainder ≤ Btwin + B`, and the glue `one_le_ell1_level` is what lets the second be
applied at the first's level.

The level is kept in the RAW ℕ-truncated form B2's door carries — no ℝ restatement of the
exponent, no numeral pinned.  `B` is a PARAMETER: wave 1 asserts NOTHING about the size of
the arithmetic input, so neither disjunct is a twin-prime claim.  The right disjunct is the
survivor branch — `0 < siftedSum` with weights `1 − λ` and support `∋ m ≥ 3` yields a
sifted `m` with `Ω(m)` odd — but that Chowla-conversion lemma is NAMED, not built here. -/
theorem twin_parity_survivor_or_chowla_of_liouvilleTwinDisp {z B : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hdisp : LiouvilleTwinDisp N P
      (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) B) :
    (twinParitySieve N P hP).totalMass * Salt.BrunLower.W (twinParitySieve N P hP)
          * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
              / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
        ≤ Btwin (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
              * Real.log z)
            * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                - 1 : ℕ))) + B
      ∨ 0 < (twinParitySieve N P hP).siftedSum := by
  have hdoor := twinParitySieve_brun_lower_ell1 (N := N) (P := P) (hP := hP) (z := z) Q hQ hz
    hzprimes
  have hrem := twinParitySieve_rosserRemainder_le (N := N) (P := P) (hP := hP)
    (one_le_ell1_level (z := z) Q hQ hz) hdisp
  rcases le_or_gt (twinParitySieve N P hP).siftedSum 0 with hs | hs
  · exact Or.inl (by linarith)
  · exact Or.inr hs

/-! ## The QUANTITATIVE pre-terminal — the extraction repair (λ-BV wave-2 §7 verdict 4)

The terminal above ends `rcases le_or_gt siftedSum 0` and returns `Or.inr hs` on the survivor
branch: **the size is thrown away.**  The wave-2 §3 refuter pass named that as an extraction
repair to *"adopt in any consumer"*, and it is route-independent — it survived the verdicts that
killed §3's log-collapse wave, because it is a statement about the LANDED ℓ¹ chain and not about
the log-rebase at all.

Both lemmas below are the SAME three landed pieces composed — `twinParitySieve_brun_lower_ell1`
(the door, `:206`), `twinParitySieve_rosserRemainder_le` (the ℓ¹ split, `:292`) and
`one_le_ell1_level` (`:323`) — with no `le_or_gt` and nothing discarded.  ⛔ **The landed terminal
is NOT edited and NOT replaced**; this is a strengthening beside it.
-/

/-- **The quantitative pre-terminal** (`twinParitySieve_siftedSum_lower_of_liouvilleTwinDisp`) —
the same hypotheses as the terminal, but concluding a LOWER BOUND on the sifted sum instead of a
disjunction:

    `mainTerm − (Btwin lvl + B) ≤ siftedSum` .

The terminal's disjunction follows from this in two lines (`le_or_gt` on `siftedSum`, then
`linarith`), so nothing is lost; what is GAINED is the margin, which the disjunction destroys.
A consumer that only learns `0 < siftedSum` cannot tell a survivor count of `1` from one of
`N/log N`, and every downstream quantitative question needs the difference.

⛔ **Still a DOOR, exactly as its three inputs are.** `B` is a PARAMETER and wave 1 asserts
nothing about its size; `Btwin` is explicit and unconditional but the bound is only useful when
the arithmetic input beats it. **This is not a twin-prime claim and no positivity is asserted
here** — see the margin form below for the conditional that is. -/
theorem twinParitySieve_siftedSum_lower_of_liouvilleTwinDisp {z B : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hdisp : LiouvilleTwinDisp N P
      (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) B) :
    (twinParitySieve N P hP).totalMass * Salt.BrunLower.W (twinParitySieve N P hP)
          * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
              / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
        - (Btwin (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
              * Real.log z)
            * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                - 1 : ℕ))) + B)
      ≤ (twinParitySieve N P hP).siftedSum := by
  have hdoor := twinParitySieve_brun_lower_ell1 (N := N) (P := P) (hP := hP) (z := z) Q hQ hz
    hzprimes
  have hrem := twinParitySieve_rosserRemainder_le (N := N) (P := P) (hP := hP)
    (one_le_ell1_level (z := z) Q hQ hz) hdisp
  linarith

/-- **The margin form** (`twinParitySieve_siftedSum_pos_of_margin`) — what the size actually buys.

Where the terminal offers a disjunction whose right branch a consumer must SELECT by refuting the
left one, this offers the survivor branch DIRECTLY, gated on an explicit strict margin

    `Btwin lvl + B < mainTerm` .

That is the shape a wave-2 consumer wants: the arithmetic input's job is stated as ONE inequality
to beat, rather than as a disjunct to eliminate.  *The disjunction and this are equivalent given
the lemma above; they are not equivalent as INTERFACES, and the refuters' "adopt in any consumer"
is about the interface.*

⛔ **The margin is a HYPOTHESIS and nothing here supplies it.**  Wave 1 asserts nothing about `B`,
so this is a door in exactly the sense its inputs are — **no twin-prime claim, and no landing here
may be read as producing a survivor.** -/
theorem twinParitySieve_siftedSum_pos_of_margin {z B : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hdisp : LiouvilleTwinDisp N P
      (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) B)
    (hmargin : Btwin (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) + B
        < (twinParitySieve N P hP).totalMass * Salt.BrunLower.W (twinParitySieve N P hP)
            * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
                / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))) :
    0 < (twinParitySieve N P hP).siftedSum := by
  have hlow := twinParitySieve_siftedSum_lower_of_liouvilleTwinDisp (N := N) (P := P) (hP := hP)
    (z := z) (B := B) Q hQ hz hzprimes hdisp
  linarith

/-! ## The `d = 1` ladder row — λ-BV wave-2 §7 verdict 4, second extraction repair

`LiouvilleTwinDisp` sums `|L N d − ν(d)·L N 1|` over the divisors of `P`.  **The `d = 1` row of
that sum is IDENTICALLY ZERO**, because `ν(1) = 1` and the row collapses to `|L N 1 − L N 1|`.

The wave-2 refuter pass named this to correct a reading of the supply ladder: *"the h-fork-at-2
object lives in `totalMass` and in every row's `ν(d)·L(N,1)` tail, NOT at `d = 1`."*  A reader
pricing the ladder row-by-row will look at `d = 1`, see the full Liouville sum `L N 1`, and price
the two-point correlation there — **but that row costs nothing; the correlation is paid in the
`ν(d)·L N 1` TAIL of every OTHER row.**  ⇒ *A row that mentions the hard object is not a row that
demands it.*

Like the quantitative pre-terminal above, this is route-independent: it is a statement about the
LANDED `LiouvilleTwinDisp` and survives the verdicts that killed §3's log-rebase.
-/

/-- `ν(1) = 1` — the density's value at the empty modulus, from multiplicativity.  Stated because
the `d = 1` row's collapse depends on it and `Salt.TwinSieve` carries no `nu_one`. -/
theorem nu_one : Salt.TwinSieve.nu 1 = 1 :=
  Salt.TwinSieve.nu_mult.map_one

/-- **The `d = 1` row vanishes.**  `|L N 1 − ν(1)·L N 1| = 0`. -/
theorem twinDisp_row_one (N : ℕ) :
    |L N 1 - Salt.TwinSieve.nu 1 * L N 1| = 0 := by
  rw [nu_one, one_mul, sub_self, abs_zero]

/-- ⭐ **THE REFORMULATION THE VANISHING BUYS** — `LiouvilleTwinDisp` is a demand on `d ≥ 2`
ALONE.  The sum over `P.divisors` equals the sum over `P.divisors.erase 1`, so a supplier owes
nothing at `d = 1` and every ladder pricing should start at `d = 2`.

`P ≠ 0` comes from `hP : Squarefree P` (`Nat.Squarefree` forbids `0`), which is why the statement
needs no extra hypothesis. -/
theorem liouvilleTwinDisp_sum_erase_one (N P : ℕ) (hP : Squarefree P) (lvl : ℝ) :
    (∑ d ∈ P.divisors,
        (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0))
      = ∑ d ∈ P.divisors.erase 1,
          (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have h1 : (1 : ℕ) ∈ P.divisors := Nat.one_mem_divisors.mpr hP0
  rw [← Finset.sum_erase_add _ _ h1]
  have hzero : (if ((1 : ℕ) : ℝ) < lvl then |L N 1 - Salt.TwinSieve.nu 1 * L N 1| else 0) = 0 := by
    by_cases h : ((1 : ℕ) : ℝ) < lvl
    · rw [if_pos h, twinDisp_row_one]
    · rw [if_neg h]
  rw [hzero, add_zero]

/-- **`LiouvilleTwinDisp` restated on `d ≥ 2`**, the form a supply ladder should be priced
against.  ⛔ This is a RESTATEMENT, not a weakening: the two sides are equal, not merely
comparable, so nothing is given up by adopting it. -/
theorem liouvilleTwinDisp_iff_erase_one (N P : ℕ) (hP : Squarefree P) (lvl B : ℝ) :
    LiouvilleTwinDisp N P lvl B
      ↔ (∑ d ∈ P.divisors.erase 1,
          (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0)) ≤ B := by
  rw [LiouvilleTwinDisp, liouvilleTwinDisp_sum_erase_one N P hP lvl]

/-! ## The log-weight comparison — λ-BV wave-2 §7 verdict 4, the *"unnamed B node"*

The log-rebase writes each divisor atom as a sum over an affine form: `n = d·m + r` with
`1 ≤ r ≤ d`, so the log world's natural weight `1/n` becomes `1/(d·m + r)` while the atom is
indexed by `m` and wants the weight `1/m`.  §7's verdict 4 named the comparison between them as
an unnamed `B` node; it is the lemma below, and the answer is **a factor of exactly 2, uniform in
`d`, `m` and `r`**:

    `d·m ≤ d·m + r ≤ d·(m+1) ≤ 2·d·m`   (the right step is `m + 1 ≤ 2m`, i.e. `1 ≤ m`).

⛔ **The two hypotheses are both load-bearing and neither is cosmetic.**  `r ≤ d` is what bounds
the offset by one stride — without it the offset is unbounded and no constant exists.  `1 ≤ m` is
what turns `m + 1` into `2m` — at `m = 0` the left comparison fails outright (`0 ≤ r`, and the
`1/m` side is undefined anyway).  *The residue-class decomposition supplies both: `r` ranges over a
residue system mod `d`, and `m` starts at 1.*

⛔ **SCOPE — this is an INGREDIENT, not a wiring.**  It is pure arithmetic on the weights; it
mentions no Liouville sum, no atom and no consumer, and **nothing in the corpus consumes it yet**.
Like the other two verdict-4 repairs it is route-independent — but it earns its place by being the
constant the log-rebase pricing needs, not by being connected. -/

/-- **The log-weight comparison, two-sided.**  For `1 ≤ m` and `r ≤ d`, the affine-form log weight
`1/(d·m + r)` sits between `1/(2·d·m)` and `1/(d·m)`. -/
theorem logWeight_affine_le {d m r : ℕ} (hd : 0 < d) (hm : 0 < m) (hr : r ≤ d) :
    (1 : ℝ) / (2 * ((d : ℝ) * (m : ℝ))) ≤ 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ))
      ∧ (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)) ≤ 1 / ((d : ℝ) * (m : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrd : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast hr
  have hdm : (0 : ℝ) < (d : ℝ) * (m : ℝ) := mul_pos hd0 hm0
  have hden : (0 : ℝ) < (d : ℝ) * (m : ℝ) + (r : ℝ) := by linarith
  constructor
  · -- `d·m + r ≤ 2·d·m`, from `r ≤ d ≤ d·m`
    have hdle : (d : ℝ) ≤ (d : ℝ) * (m : ℝ) := by nlinarith
    exact one_div_le_one_div_of_le hden (by linarith)
  · -- `d·m ≤ d·m + r`
    exact one_div_le_one_div_of_le hdm (by linarith)

/-- **The same comparison in the `1/m` normalisation** — the shape a per-atom pricing reads:
the affine-form log weight is `(1/d)·(1/m)` up to a factor 2, with BOTH constants explicit.

⭐ This is the form that makes the log-rebase's per-atom bookkeeping a CONSTANT rather than a
schedule: the `d`-dependence is exactly the factor `1/d` that the divisor sum already carries, and
what is left over is bounded by 2 uniformly. -/
theorem logWeight_affine_le_div {d m r : ℕ} (hd : 0 < d) (hm : 0 < m) (hr : r ≤ d) :
    (1 : ℝ) / (2 * (d : ℝ)) * (1 / (m : ℝ)) ≤ 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ))
      ∧ (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)) ≤ 1 / (d : ℝ) * (1 / (m : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := logWeight_affine_le hd hm hr
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have e1 : (1 : ℝ) / (2 * (d : ℝ)) * (1 / (m : ℝ)) = 1 / (2 * ((d : ℝ) * (m : ℝ))) := by
    field_simp
  have e2 : (1 : ℝ) / (d : ℝ) * (1 / (m : ℝ)) = 1 / ((d : ℝ) * (m : ℝ)) := by
    field_simp
  exact ⟨by rw [e1]; exact hlo, by rw [e2]; exact hhi⟩

/-! ## The tail-mass infinitude argument — λ-BV wave-2 §7 verdict 4

§7's verdict 4 records this as *"infinitude via the tail-mass argument (genuinely EASIER in the log
world — the one argument FOR the rebase nobody made)"*.  The core is route-independent and belongs
here rather than in any log-world file: **a nonnegative weight whose partial sums are unbounded
cannot be supported on a finite set.**

⭐ **WHY IT IS THE ARGUMENT *FOR* THE REBASE.**  A positivity statement `0 < siftedSum` at each `N`
gives a survivor `≤ N` for each `N` and **does not give infinitely many survivors** — the witnesses
could all be the same `n`.  What upgrades one-per-`N` to infinitude is the observation that any
FIXED finite set contributes a BOUNDED amount of weight, so an unbounded mass cannot be carried by
finitely many terms.  In the log world the mass grows like `log N` **unconditionally** (the
subtracted two-point sum is Tao's own theorem), which is precisely the divergence this lemma
consumes; in the flat world the corresponding divergence is what the campaign is trying to prove.
*The rebase does not make this lemma easier — it makes its HYPOTHESIS available.*

⛔ **SCOPE.**  This is the abstract step ONLY.  It takes the divergence as a hypothesis and
supplies nothing toward it; **no landing here produces a survivor, and nothing in the corpus
consumes it yet.**
-/

/-- **The tail-mass infinitude step.**  A nonnegative weight whose partial sums over `range N` are
unbounded has infinite support.

The proof is the contrapositive in one move: on a finite support the partial sums are all bounded
by the total over that support, because the terms off it are zero and the terms on it are
nonnegative. -/
theorem support_infinite_of_partialSums_unbounded {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hunb : ∀ M : ℝ, ∃ N : ℕ, M < ∑ n ∈ Finset.range N, w n) :
    {n : ℕ | w n ≠ 0}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hunb (∑ n ∈ hfin.toFinset, w n)
  have hsub : ((Finset.range N).filter (fun n => w n ≠ 0)) ⊆ hfin.toFinset := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Set.Finite.mem_toFinset]
    exact hn.2
  have hle : (∑ n ∈ (Finset.range N).filter (fun n => w n ≠ 0), w n)
      ≤ ∑ n ∈ hfin.toFinset, w n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)
  rw [Finset.sum_filter_ne_zero] at hle
  linarith

/-- **The step in the shape a positivity chain hands it** — an unbounded LOWER bound suffices.

A consumer typically owns `f N ≤ ∑_{n < N} w n` for a divergent `f` (in the log world,
`f N = (1−o(1))·log N`), not the raw unboundedness.  This takes that shape directly. -/
theorem support_infinite_of_lower_unbounded {w : ℕ → ℝ} {f : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hlow : ∀ N : ℕ, f N ≤ ∑ n ∈ Finset.range N, w n)
    (hdiv : ∀ M : ℝ, ∃ N : ℕ, M < f N) :
    {n : ℕ | w n ≠ 0}.Infinite := by
  refine support_infinite_of_partialSums_unbounded hw (fun M => ?_)
  obtain ⟨N, hN⟩ := hdiv M
  exact ⟨N, lt_of_lt_of_le hN (hlow N)⟩

/-! ## The harmonic-progression count — λ-BV wave-2 §3(3)'s *"NEW small node"*

§3 of the wave-2 block named this as *"the log-count error per class of the harmonic progression
sum is O(1) (elementary; the NEW small node — 'harmonic-progression count', B-class)"*, and §7's
refuter pass VERIFIED it with an **absolute constant `C₀ = 1`, derived**.  It is one of the two §3
claims the pass upheld (the other being that no `N` is smuggled); the collapse ARGUMENT around it
died, the ESTIMATE did not.

Summing the pointwise weight comparison above over `m ∈ [1, M]` gives the per-class statement the
ladder actually reads, and composing with the landed harmonic bound `∑_{m≤M} 1/m ≤ 1 + log M`
(`Salt.TwinBar.sum_inv_Icc_le`, `Wall.lean:219`) pins the constant at **1** — the refuters' `C₀`,
now on the page rather than in a verdict.

⛔ **SCOPE.**  These are estimates on the WEIGHTS, uniform in the residue `r` and the modulus `d`.
They name no Liouville sum and no atom, and **nothing in the corpus consumes them yet** — the
log-rebase they serve is design-tier and its §3 route is refuted.  Landing them is worth it because
**the estimate is route-independent**: any log-world pricing of an affine-form atom needs exactly
this comparison, and the refuters had already checked the constant.
-/

/-- **The harmonic-progression count, upper.**  For `1 ≤ r ≤ d` the affine-form log weights over
`m ∈ [1, M]` sum to at most `(1/d)·(1 + log M)`.

The constant is **1**, absolute — §7's derived `C₀` — and it is `Salt.TwinBar.sum_inv_Icc_le`'s,
not a new estimate. -/
theorem sum_inv_affine_le {d r : ℕ} (hd : 0 < d) (hr : r ≤ d) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
      ≤ (1 / (d : ℝ)) * (1 + Real.log M) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hstep : (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (d : ℝ)) * (1 / (m : ℝ)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact (logWeight_affine_le_div hd (by omega) hr).2
  have hharm : (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)) ≤ 1 + Real.log M := by
    simpa only [one_div] using sum_inv_Icc_le M
  calc (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (d : ℝ)) * (1 / (m : ℝ)) := hstep
    _ = (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ (1 / (d : ℝ)) * (1 + Real.log M) := by
        exact mul_le_mul_of_nonneg_left hharm (by positivity)

/-- **The harmonic-progression count, lower** — the other side of the same sandwich, at the factor
`2` the weight comparison costs.  Together with `sum_inv_affine_le` this is the per-class estimate
in both directions, so a pricing that needs the atom to be NON-negligible has it too.

⭐ **Both bounds carry `1/d` and NOTHING else `d`-dependent**, which is the content: the modulus
enters exactly as the factor the divisor sum already carries, uniformly in the residue `r`. -/
theorem sum_inv_affine_ge {d r : ℕ} (hd : 0 < d) (hr : r ≤ d) (M : ℕ) :
    (1 / (2 * (d : ℝ))) * (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  exact (logWeight_affine_le_div hd (by omega) hr).1

/-! ## The twin-value Möbius unfolding — the DIRECT route's skeleton

§7's verdict 2 ruled wave-1's sieve chain **strictly dominated** for the log-world prize: *"at
fixed `z` the sifted log-mass is a finite Möbius sum over the SAME atoms: needs only the
harmonic-count node + the Tao atoms, no BoundingSieve, no door, no `Btwin`"*, and *"if
Tao-1.2-in-Lean ever lands, the DIRECT MÖBIUS route is the consumer."*  This is that route's
bookkeeping, and it is exact — an identity, not a sieve bound.

⛔ **WHY THE LANDED STONE DOES NOT SERVE.**  `Salt.SW.sum_coprime_eq_moebius_multiples`
(`SW/CoprimeBV.lean:98`) is the same classical unfolding, but it sifts the **INDEX** `d` and
reindexes the inner sums by `d = k·e`.  Here the sifting condition is on the **VALUE** `n(n+2)`,
and that reindex does not transport: `k ∣ n(n+2)` does not put `n` in an arithmetic progression of
the shape the stone needs.  ⇒ *Same identity, different variable, and the difference is exactly the
step that fails.*  What DOES transport is the pointwise Möbius collapse, reused below from
`Salt.SW.sum_divisors_moebius_real` rather than re-derived.

⛔ **SCOPE — bookkeeping, and nothing consumes it yet.**  It is `w`-generic and says nothing about
Liouville, about `z`, or about any estimate; the ATOMS on its right-hand side are the open object
(the Tao Theorem 1.2 campaign, §7's disposition, Captain-gated).  **Landing this does not advance
the prize; it removes the only non-Tao Lean prerequisite §7 named.** ⚠️ On today's own census this
name would read as a dead branch until an atom supplier arrives — recorded here so the reading is
not a surprise. -/

/-- **The twin-value Möbius unfolding.**  For squarefree `P` and any weight `w`, the sum over
`n ∈ [1,N]` whose twin value `n(n+2)` is coprime to `P` unfolds exactly over the divisors of `P`:

    `∑_{n ≤ N, (n(n+2), P) = 1} w n  =  ∑_{d ∣ P} μ(d) · ∑_{n ≤ N, d ∣ n(n+2)} w n` .

The right-hand inner sums are precisely the objects `L`/`LiouvilleTwinDisp` already index, which is
what makes this the direct route's skeleton rather than a new decomposition. -/
theorem sum_twinCoprime_eq_moebius_divisors (N P : ℕ) (hP : Squarefree P) (w : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P), w n)
      = ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), w n := by
  have hP0 : P ≠ 0 := hP.ne_zero
  -- divisors of `P` that divide `m` are exactly the divisors of `gcd P m`
  have hset : ∀ m : ℕ, P.divisors.filter (fun k => k ∣ m) = (Nat.gcd P m).divisors := by
    intro m
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hgcd0 : Nat.gcd P m ≠ 0 := by
      have : 0 < Nat.gcd P m := Nat.gcd_pos_of_pos_left m (Nat.pos_of_ne_zero hP0)
      omega
    exact ⟨fun ⟨⟨hkP, _⟩, hkm⟩ => ⟨⟨hkP, hkm⟩, hgcd0⟩,
           fun ⟨⟨hkP, hkm⟩, _⟩ => ⟨⟨hkP, hP0⟩, hkm⟩⟩
  -- the pointwise collapse, at the twin VALUE
  have hpt : ∀ n : ℕ,
      (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * (if d ∣ n * (n + 2) then w n else 0))
        = if Nat.Coprime (n * (n + 2)) P then w n else 0 := by
    intro n
    have hrw : (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * (if d ∣ n * (n + 2) then w n else 0))
        = w n * ∑ d ∈ P.divisors.filter (fun k => k ∣ n * (n + 2)),
            (ArithmeticFunction.moebius d : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> ring)
    rw [hrw, hset (n * (n + 2)), Salt.SW.sum_divisors_moebius_real]
    by_cases hc : Nat.Coprime (n * (n + 2)) P
    · have hg1 : Nat.gcd P (n * (n + 2)) = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_pos hg1, if_pos hc, mul_one]
    · have hg1 : ¬ Nat.gcd P (n * (n + 2)) = 1 := by rw [Nat.gcd_comm]; exact hc
      rw [if_neg hg1, if_neg hc, mul_zero]
  -- assemble: turn both sides into filtered sums and swap
  calc (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P), w n)
      = ∑ n ∈ Finset.Icc 1 N, (if Nat.Coprime (n * (n + 2)) P then w n else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℝ) * (if d ∣ n * (n + 2) then w n else 0) := by
        exact Finset.sum_congr rfl (fun n _ => (hpt n).symm)
    _ = ∑ d ∈ P.divisors, ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * (if d ∣ n * (n + 2) then w n else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), w n := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum, Finset.sum_filter]
        exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> ring)

/-! ## Every `d ≥ 2` atom carries TWO objects at TWO strengths — verdict 4's last entry

§7's verdict 4 closes with *"the `d = 1` ladder row is IDENTICALLY ZERO … every `d ≥ 2` atom
carries TWO objects at TWO strengths"*.  The first half is `twinDisp_row_one` above; this is the
second, and it is the one I had glossed as an observation rather than a node.

The row `|L N d − ν(d)·L N 1|` **names two different Liouville sums**: the `d`-restricted
`L N d`, whose supply is a correlation estimate at stride `d`, and the FULL `L N 1`, whose supply
is the stride-1 (unrestricted) estimate.  They are objects of **different strengths**, and a
supplier that can only reach one of them is not stuck: the triangle inequality prices the row as
two INDEPENDENT demands.

⭐ **That is the content — an interface fact, not an estimate.** Without it a reader prices each
row as a demand on a DIFFERENCE, which is strictly harder than the conjunction of the two bounds
and needlessly couples the two strengths.
-/

/-- `0 ≤ ν(d)` for every `d` — the density is a ratio of nonnegatives. -/
theorem nu_nonneg (d : ℕ) : 0 ≤ Salt.TwinSieve.nu d := by
  rw [Salt.TwinSieve.nu_apply]
  positivity

/-- **Every ladder row splits into its two objects.**  `|L N d − ν(d)·L N 1| ≤ |L N d| +
ν(d)·|L N 1|`, so a supplier may meet the row by bounding the two Liouville sums SEPARATELY, each
at its own strength, instead of bounding their difference. -/
theorem twinDisp_row_le_two_objects (N d : ℕ) :
    |L N d - Salt.TwinSieve.nu d * L N 1|
      ≤ |L N d| + Salt.TwinSieve.nu d * |L N 1| := by
  have h := abs_sub (L N d) (Salt.TwinSieve.nu d * L N 1)
  have habs : |Salt.TwinSieve.nu d * L N 1| = Salt.TwinSieve.nu d * |L N 1| := by
    rw [abs_mul, abs_of_nonneg (nu_nonneg d)]
  linarith [h, habs.le, habs.ge]

/-- **The whole discrepancy input, priced as two independent families.**  `LiouvilleTwinDisp` is
implied by separate bounds on the two objects, summed over the level.

⛔ This is a SUFFICIENT condition, not an equivalence: it discards the cancellation between
`L N d` and `ν(d)·L N 1` that the difference form retains.  A supplier that CAN exploit that
cancellation should use `LiouvilleTwinDisp` directly — this exists so that one which cannot is
not blocked. -/
theorem liouvilleTwinDisp_of_two_objects {N P : ℕ} {lvl B₁ B₂ : ℝ}
    (h₁ : (∑ d ∈ P.divisors, (if (d : ℝ) < lvl then |L N d| else 0)) ≤ B₁)
    (h₂ : (∑ d ∈ P.divisors,
            (if (d : ℝ) < lvl then Salt.TwinSieve.nu d * |L N 1| else 0)) ≤ B₂) :
    LiouvilleTwinDisp N P lvl (B₁ + B₂) := by
  have hsplit : (∑ d ∈ P.divisors,
        (if (d : ℝ) < lvl then |L N d - Salt.TwinSieve.nu d * L N 1| else 0))
      ≤ (∑ d ∈ P.divisors, (if (d : ℝ) < lvl then |L N d| else 0))
        + ∑ d ∈ P.divisors,
            (if (d : ℝ) < lvl then Salt.TwinSieve.nu d * |L N 1| else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h : (d : ℝ) < lvl
    · rw [if_pos h, if_pos h, if_pos h]
      exact twinDisp_row_le_two_objects N d
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  exact le_trans hsplit (by linarith)

end Salt.TwinBar
