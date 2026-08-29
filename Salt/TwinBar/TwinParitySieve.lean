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

/-! ## The log-world twin mass, split — isolating exactly what the Tao campaign must supply

§3(1) of the wave-2 block writes the log-rebased total mass as
`Σ_{n≤N}(1 − λ(n)λ(n+2))/n = H_N − Σ λ(n)λ(n+2)/n`, and observes that the SUBTRACTED sum is
**Tao's own theorem** (1509.05422; forms `(1,0),(1,2)`, determinant `2 ≠ 0`) and therefore
`o(log N)` — so `totalMass_log = (1−o(1))·log N` unconditionally.

§7 killed the COLLAPSE ARGUMENT built on that, not the DECOMPOSITION.  What is landed here is the
decomposition alone, with no asymptotics and no claim about either piece:

* the **identity** `λ(n(n+2)) = λ(n)·λ(n+2)` — complete multiplicativity, which is what turns the
  corpus's `liouville (n*(n+2))` spelling into Tao's two-point correlation at shift `2`;
* the **split** of the log-weighted mass into a harmonic head and that correlation.

⭐ **Why this is worth landing while the campaign is unruled:** it puts the boundary between what
the corpus HAS and what the Tao campaign must SUPPLY on the page, in the kernel, as an equation.
The head is `Salt.TwinBar.sum_inv_Icc_le`'s object; the tail is the Tao atom and nothing else.
⛔ **SCOPE: an identity.** No estimate, no asymptotic, no `o(1)`; neither piece is bounded here,
and nothing consumes it yet (12c's census will read it as a dead branch until the atom arrives).
-/

/-- **`λ(n(n+2)) = λ(n)·λ(n+2)`** — complete multiplicativity, no coprimality needed.  This is the
step that turns the corpus's twin-value spelling into the two-point correlation at shift `2` that
Tao's theorem is about. -/
theorem liouville_twinProd_mul (n : ℕ) :
    (ArithmeticFunction.liouville (n * (n + 2)) : ℤ)
      = (ArithmeticFunction.liouville n : ℤ) * (ArithmeticFunction.liouville (n + 2) : ℤ) :=
  ArithmeticFunction.liouville_apply_mul n (n + 2)

/-- **The log-world twin mass splits into a harmonic head and a two-point correlation.**

    `Σ_{n≤N} (1 − λ(n(n+2)))/n  =  Σ_{n≤N} 1/n  −  Σ_{n≤N} λ(n(n+2))/n`

The head is bounded by `sum_inv_Icc_le`; the tail is the object the Tao campaign supplies. -/
theorem sum_logTwin_split (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
        - ∑ n ∈ Finset.Icc 1 N,
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [sub_div]

/-- **The same split with the correlation written at Tao's shape** — `λ(n)·λ(n+2)` rather than
`λ(n(n+2))`.  Composing the two lemmas above; stated so a consumer reading Tao's theorem does not
have to re-derive the multiplicativity step at the seam. -/
theorem sum_logTwin_split_shift (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
        - ∑ n ∈ Finset.Icc 1 N,
            (((ArithmeticFunction.liouville n : ℤ) : ℝ)
              * ((ArithmeticFunction.liouville (n + 2) : ℤ) : ℝ)) / (n : ℝ) := by
  rw [sum_logTwin_split N]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [liouville_twinProd_mul n]
  push_cast
  ring

/-! ## The harmonic LOWER bound — the divergence the tail-mass step consumes

`Salt.TwinBar.sum_inv_Icc_le` (`Wall.lean:219`) gives `∑_{d≤n} 1/d ≤ 1 + log n`.  The corpus has no
matching LOWER bound over `Icc 1 n` (`harmonic_window_bounds`, `LogMeasure.lean:115`, is two-sided
but over `Ioc (x/ω) x` — a different range), and the lower bound is the half the log-world argument
actually needs: it is what makes the head DIVERGE, which is the hypothesis
`support_infinite_of_lower_unbounded` above takes.

The sharp telescoping form is proved, `log(n+1) ≤ ∑`, with the weaker `log n ≤ ∑` as its corollary.
-/

/-- **The harmonic lower bound, sharp form:** `log(n+1) ≤ ∑_{d=1}^{n} 1/d`.

Telescoping the other way from `sum_inv_Icc_le`: each step needs
`log(m+2) − log(m+1) ≤ 1/(m+1)`, which is `Real.log_le_sub_one_of_pos` at `(m+2)/(m+1)`.
⛔ The sharp `n+1` is not cosmetic — the naive `log n ≤ ∑` cannot be proved by this induction,
because the step would demand `log(1 + 1/m) ≤ 1/(m+1)`, which is FALSE. -/
theorem log_succ_le_sum_inv_Icc (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hstep : Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) ≤ ((m : ℝ) + 1)⁻¹ := by
      have hdiv : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
          ≤ ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
          = Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) :=
        Real.log_div (ne_of_gt hm2) (ne_of_gt hm1)
      have harith : ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 = ((m : ℝ) + 1)⁻¹ := by
        field_simp
        ring
      rw [hlog, harith] at hdiv
      exact hdiv
    have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
    have hinv : (((m + 1 : ℕ) : ℝ))⁻¹ = ((m : ℝ) + 1)⁻¹ := by push_cast; ring_nf
    rw [hcast, hinv]
    linarith [ih, hstep]

/-- **The harmonic lower bound, plain form:** `log n ≤ ∑_{d=1}^{n} 1/d`, from the sharp one by
monotonicity of `log`. -/
theorem log_le_sum_inv_Icc (n : ℕ) :
    Real.log (n : ℝ) ≤ ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ := by
  refine le_trans ?_ (log_succ_le_sum_inv_Icc n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact Real.log_le_log hn0 (by linarith)

/-- **The head diverges** — the hypothesis shape `support_infinite_of_lower_unbounded` takes.
For every bound `M` there is an `N` whose harmonic sum exceeds it. -/
theorem sum_inv_Icc_unbounded (M : ℝ) : ∃ n : ℕ, M < ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (M + 1))
  refine ⟨n, lt_of_lt_of_le ?_ (log_le_sum_inv_Icc n)⟩
  have hexp : (0 : ℝ) < Real.exp (M + 1) := Real.exp_pos _
  have hlog : Real.log (Real.exp (M + 1)) < Real.log (n : ℝ) :=
    Real.log_lt_log hexp hn
  rw [Real.log_exp] at hlog
  linarith

/-! ## The direct route's WIN CONDITION, assembled — two named inputs and nothing else

Everything above composes into one statement: the sifted log-mass is bounded below by
`(sifted count) − (total atom mass)`, both of which enter as NAMED HYPOTHESES.  That is the
direct-Möbius route's win condition in the same interface style as
`twinParitySieve_siftedSum_pos_of_margin`: **one inequality to beat, not a disjunct to eliminate.**

⭐ **What makes it worth stating is what it does NOT contain.**  No `BoundingSieve`, no door, no
`Btwin`, no `c₁`, no level `lvl` — §7's verdict 2 said the direct route needs none of them, and the
assembly shows it: the only inputs are the count and the atoms.

⛔ **BOTH INPUTS ARE HYPOTHESES AND NEITHER IS SUPPLIED HERE.**  `hcount` is the sifted harmonic
count (elementary, but it needs the residue structure of `n(n+2)` mod `d`, which is `rho`'s job and
is NOT done here).  `hatom` is the Tao two-point input — **the campaign object**.  ⇒ *This is the
shape of the prize, not the prize.*
⚠️ §7's verdict 3 stands and must not be blurred: **without roughness, "Ω(n(n+2)) odd infinitely
often" is a three-line elementary theorem.**  The roughness — the coprimality restriction that
`hcount`/`hatom` are indexed over — is the ENTIRE content, and it is why this is stated at the
SIFTED sum rather than the plain one.
-/

/-- The log-world split at an ARBITRARY index set — `sum_logTwin_split` was the `Icc 1 N` case.
Stated generally because the Möbius skeleton hands each divisor its own filtered set. -/
theorem sum_logTwin_split_on (s : Finset ℕ) :
    (∑ n ∈ s, (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ))
      = (∑ n ∈ s, (1 : ℝ) / (n : ℝ))
        - ∑ n ∈ s, ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [sub_div]

/-- ⭐ **THE DIRECT ROUTE'S WIN CONDITION.**  The sifted log-mass exceeds
`(sifted count) − (total atom mass)`:

    `Hmain − A  ≤  ∑_{n ≤ N, (n(n+2),P) = 1} (1 − λ(n(n+2)))/n`

given `hcount : Hmain ≤ ∑_{d∣P} μ(d)·∑_{n≤N, d∣n(n+2)} 1/n` and
`hatom : |∑_{d∣P} μ(d)·∑_{n≤N, d∣n(n+2)} λ(n(n+2))/n| ≤ A`.

No sieve, no door, no `Btwin`, no level — exactly as §7's verdict 2 said the direct route needs.
⛔ Both inputs are HYPOTHESES: the count is elementary but unsupplied here, and the atom mass is
the Tao campaign object. -/
theorem logSifted_lower_of_count_and_atoms {N P : ℕ} (hP : Squarefree P) {Hmain A : ℝ}
    (hcount : Hmain ≤ ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
    (hatom : |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)| ≤ A) :
    Hmain - A
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P),
          (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ) := by
  -- the skeleton, at the log weight
  rw [sum_twinCoprime_eq_moebius_divisors N P hP
      (fun n => (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ))]
  -- split each divisor's inner sum, then separate the two families
  have hsplit : (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ))
      = (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
        - ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
            * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
                ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [sum_logTwin_split_on ((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))), mul_sub]
  rw [hsplit]
  have hA := abs_le.mp hatom
  linarith [hcount, hA.1, hA.2]

/-! ## Where `W` comes from on the direct route — the divisor-sum Euler bridge

The direct route's main term is `∑_{d∣P} μ(d)·ν(d)·H_N`, so the constant in front of the
harmonic head is `∑_{d∣P} μ(d)·ν(d)`.  **That sum IS the sieve's `W`** — which is why the
sieve-free route still produces the sieve's density constant, and it is worth having as one named
equation rather than as a step inside a longer proof.

Both halves are landed in `BrunLower/Lemma3.lean` and only needed composing:
`sum_divisors_eq_sum_powerset` (`:107`, squarefree divisors ↔ prime-set powerset) and
`sum_powerset_prod_neg_nu` (`:151`, the leading Euler term `Σ_{S⊆P} ∏_{q∈S}(−ν q) = W`), with
`moebius_nu_prod_eq` (`:141`) folding `μ`'s sign into the density product at each set.

⭐ **This is the fact that makes §7's verdict 2 quantitative.** It said the direct route needs no
`BoundingSieve`; that is true of the APPARATUS and false of the CONSTANT — `W` still appears,
because it is what `∑ μν` equals. *A route can shed a machine and keep the machine's number.*
-/

/-- **`∑_{d ∣ P} μ(d)·ν(d) = W`** — the divisor-sum form of the leading Euler term, for any
`BoundingSieve` (its `prodPrimes` is squarefree by construction).

This is the constant multiplying the harmonic head in the direct-Möbius main term. -/
theorem sum_divisors_moebius_nu_eq_W (s : BoundingSieve) :
    (∑ d ∈ s.prodPrimes.divisors, (ArithmeticFunction.moebius d : ℝ) * s.nu d)
      = Salt.BrunLower.W s := by
  rw [Salt.BrunLower.sum_divisors_eq_sum_powerset s.prodPrimes_squarefree
      (fun d => (ArithmeticFunction.moebius d : ℝ) * s.nu d)]
  rw [← Salt.BrunLower.sum_powerset_prod_neg_nu s]
  refine Finset.sum_congr rfl fun S hS => ?_
  exact Salt.BrunLower.moebius_nu_prod_eq s (Finset.mem_powerset.mp hS)

/-- **The twin instance, spelled at `twinParitySieve`.**  The direct route's leading constant at
the Liouville-twisted twin sieve is `W (twinParitySieve N P hP)`, and `ν` there is the landed twin
density `Salt.TwinSieve.nu` (definitionally, `twinParitySieve_nu`). -/
theorem sum_divisors_moebius_twinNu_eq_W (N P : ℕ) (hP : Squarefree P) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d)
      = Salt.BrunLower.W (twinParitySieve N P hP) := by
  have h := sum_divisors_moebius_nu_eq_W (twinParitySieve N P hP)
  rwa [twinParitySieve_prodPrimes, twinParitySieve_nu] at h

/-! ## The per-class harmonic count — the reusable atom of `hcount`

`logSifted_lower_of_count_and_atoms` holds `hcount` as a hypothesis, and discharging it means
counting `∑_{n ≤ N, d ∣ n(n+2)} 1/n`.  By `Salt.TwinSieve.dvd_iff_mem_Rnat` that set is the union
of `ρ(d)` residue classes mod `d`, so the whole count is `ρ(d)` copies of a SINGLE class sum —
which is what this bounds.

    `∑_{n ≤ N, n ≡ r (mod d)} 1/n  ≤  1 + (1/d)·(1 + log N)`     for `r < d`

⭐ **The `1` is the class's smallest element and it is unavoidable, not slack.**  The affine
comparison needs `m ≥ 1`; the term at `m = 0` (namely `n = r` itself, when `r ≥ 1`) is outside its
range and is bounded by `1/r ≤ 1` on its own.  *A per-class count without that term is a per-class
count that is false at `N ≥ r`.*

⛔ **ONE-SIDED, AND `hcount` NEEDS MORE.**  `hcount` bounds a SIGNED sum `∑_d μ(d)·C_d` from below,
so an upper bound on each `C_d` does not discharge it: what that needs is the two-sided form
`C_d = ν(d)·H + err_d` with `err_d` controlled, and then `∑ μ(d)C_d = W·H + ∑ μ(d)err_d`.  **This
is the first half of that, not the whole of it** — stated so the gap is visible rather than
implied.
-/

/-- **The per-class harmonic count, upper.**  For `r < d`, the harmonic sum over one residue class
mod `d` is at most `1 + (1/d)·(1 + log N)`: the class's smallest element, plus `1/d` times the
harmonic bound.

The injection is `n ↦ n / d`, which is injective on a fixed residue class. -/
theorem sum_inv_class_le {d r : ℕ} (hd : 0 < d) (hr : r < d) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ))
      ≤ 1 + (1 / (d : ℝ)) * (1 + Real.log N) := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- split the class into its `n < d` part (at most one element) and its `n ≥ d` part
  set S := (Finset.Icc 1 N).filter (fun n => n % d = r) with hS
  have hsplit : (∑ n ∈ S, (1 : ℝ) / (n : ℝ))
      = (∑ n ∈ S.filter (fun n => n < d), (1 : ℝ) / (n : ℝ))
        + ∑ n ∈ S.filter (fun n => ¬ n < d), (1 : ℝ) / (n : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- the small part: the class has at most one element below `d`, and its term is `≤ 1`
  have hsmall : (∑ n ∈ S.filter (fun n => n < d), (1 : ℝ) / (n : ℝ)) ≤ 1 := by
    have hsub : S.filter (fun n => n < d) ⊆ {r} := by
      intro n hn
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn
      have : n % d = n := Nat.mod_eq_of_lt hn.2
      simp only [Finset.mem_singleton]
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro i _ _; positivity
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
        rw [Finset.sum_singleton]
        rw [div_le_one (by linarith)]
        linarith
  -- the large part: `n ↦ n / d` injects into `Icc 1 N`, and `1/n ≤ (1/d)·(1/(n/d))`
  have hlarge : (∑ n ∈ S.filter (fun n => ¬ n < d), (1 : ℝ) / (n : ℝ))
      ≤ (1 / (d : ℝ)) * (1 + Real.log N) := by
    have hstep : (∑ n ∈ S.filter (fun n => ¬ n < d), (1 : ℝ) / (n : ℝ))
        ≤ ∑ n ∈ S.filter (fun n => ¬ n < d), (1 / (d : ℝ)) * (1 / ((n / d : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      simp only [hS, Finset.mem_filter, Finset.mem_Icc, not_lt] at hn
      have hdn : d ≤ n := hn.2
      have hm1 : 1 ≤ n / d := Nat.one_le_div_iff hd |>.mpr hdn
      have hmod : d * (n / d) + n % d = n := Nat.div_add_mod n d
      have heq : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod n d).symm
      have hrle : n % d ≤ d := le_of_lt (Nat.mod_lt n hd)
      have := (logWeight_affine_le_div hd hm1 hrle).2
      rw [heq]
      exact this
    refine le_trans hstep ?_
    -- reindex by `m = n / d`, injective on a fixed residue class, into `Icc 1 N`
    have hinj : ∀ a ∈ S.filter (fun n => ¬ n < d), ∀ b ∈ S.filter (fun n => ¬ n < d),
        a / d = b / d → a = b := by
      intro a ha b hb hab
      simp only [hS, Finset.mem_filter, Finset.mem_Icc, not_lt] at ha hb
      have hA : a % d = r := ha.1.2
      have hB : b % d = r := hb.1.2
      have hda := Nat.div_add_mod a d
      have hdb := Nat.div_add_mod b d
      rw [hab] at hda
      omega
    have himg : (S.filter (fun n => ¬ n < d)).image (fun n => n / d) ⊆ Finset.Icc 1 N := by
      intro m hm
      simp only [Finset.mem_image] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      simp only [hS, Finset.mem_filter, Finset.mem_Icc, not_lt] at hn
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_div_iff hd |>.mpr hn.2,
        le_trans (Nat.div_le_self n d) hn.1.1.2⟩
    calc (∑ n ∈ S.filter (fun n => ¬ n < d), (1 / (d : ℝ)) * (1 / ((n / d : ℕ) : ℝ)))
        = ∑ m ∈ (S.filter (fun n => ¬ n < d)).image (fun n => n / d),
            (1 / (d : ℝ)) * (1 / (m : ℝ)) :=
          (Finset.sum_image (f := fun m : ℕ => (1 / (d : ℝ)) * (1 / (m : ℝ))) hinj).symm
      _ ≤ ∑ m ∈ Finset.Icc 1 N, (1 / (d : ℝ)) * (1 / (m : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg himg ?_
          intro i _ _; positivity
      _ = (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (1 / (d : ℝ)) * (1 + Real.log N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa only [one_div] using sum_inv_Icc_le N
  rw [hsplit]
  linarith [hsmall, hlarge]

/-! ## The ADDITIVE error — what a SIGNED sum actually needs

⛔⛔ **THE TRAP THIS SECTION EXISTS TO CLOSE, AND IT HAS TWO LAYERS.**  `sum_inv_class_le` is
one-sided, and `hcount` bounds the SIGNED sum `∑_{d∣P} μ(d)·C_d` from below, so an upper bound on
each `C_d` cannot discharge it.  That much was already recorded.  **The second layer is that the
two-sided pair we already have does not discharge it either:** `sum_inv_affine_le` and
`sum_inv_affine_ge` sandwich the affine sum between `(1/d)·H` and `(1/(2d))·H`, and that sandwich
is **MULTIPLICATIVE**.  A factor-2 slop on each class does not perturb the main term `W·H` — it
destroys it, because `∑_d μ(d)·(1/d)·H` is a cancelling sum whose value `W·H` is far smaller than
its individual terms.

⇒ 🔑 ***A SANDWICH IS NOT AN ERROR TERM.  A SIGNED SUM NEEDS THE ERROR TO BE ADDITIVE, AND
"two-sided" ALONE DOES NOT SAY WHICH KIND YOU HAVE.***

This lemma is the additive form: the affine sum equals `(1/d)` times the harmonic sum, up to an
error of at most `2/d` — **and the error has a SIGN**, which a cancelling consumer wants, so it is
stated as `0 ≤ … ≤ 2/d` rather than with `|·|`.  The `d`-dependence of the ERROR matches the
`d`-dependence of the MAIN TERM, which is what makes `∑_d μ(d)·err_d` summable against `W`.

The pointwise identity is `(1/d)(1/m) − 1/(dm+r) = r/(dm(dm+r))`, bounded by `1/(d·m²)` using
`r ≤ d`; the `m`-sum of `1/m²` is the landed `sum_inv_sq_Icc_le` (`TwinBar/LambdaRate.lean:363`),
whose range `Icc 1 M` and constant `2` are exactly the ones needed — **reused, not re-derived**.
-/

/-- **The affine sum against the harmonic sum, with an ADDITIVE error.**  For `r ≤ d`,

    `0  ≤  (1/d)·∑_{m≤M} 1/m  −  ∑_{m≤M} 1/(d·m+r)  ≤  2/d` .

⭐ Both the main term and the error carry `1/d` and nothing else `d`-dependent, and the error is
one-signed.  This is the form `hcount` needs; the multiplicative sandwich
(`sum_inv_affine_le`/`sum_inv_affine_ge`) is not, since `∑_d μ(d)·C_d` cancels. -/
theorem sum_inv_affine_sub_harmonic {d r : ℕ} (hd : 0 < d) (hr : r ≤ d) (M : ℕ) :
    0 ≤ (1 / (d : ℝ)) * (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ))
          - ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ))
      ∧ (1 / (d : ℝ)) * (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ))
          - ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ))
        ≤ 2 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hrd : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- the difference is a single sum of pointwise differences
  have key : (1 / (d : ℝ)) * (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ))
        - ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ))
      = ∑ m ∈ Finset.Icc 1 M,
          ((1 / (d : ℝ)) * (1 / (m : ℝ)) - 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · -- nonneg: exactly the landed upper half of the weight comparison, termwise
    rw [key]
    refine Finset.sum_nonneg fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have := (logWeight_affine_le_div (m := m) hd (by omega) hr).2
    linarith
  · rw [key]
    have hterm : ∀ m ∈ Finset.Icc 1 M,
        (1 / (d : ℝ)) * (1 / (m : ℝ)) - 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ))
          ≤ (1 / (d : ℝ)) * (((m : ℝ)) ^ 2)⁻¹ := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hdm : (0 : ℝ) < (d : ℝ) * (m : ℝ) := mul_pos hd0 hm0
      have hden : (0 : ℝ) < (d : ℝ) * (m : ℝ) + (r : ℝ) := by linarith
      have e : (1 / (d : ℝ)) * (1 / (m : ℝ)) - 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ))
          = (r : ℝ) / (((d : ℝ) * (m : ℝ)) * ((d : ℝ) * (m : ℝ) + (r : ℝ))) := by
        field_simp
        ring
      have h2 : (1 / (d : ℝ)) * (((m : ℝ)) ^ 2)⁻¹ = 1 / ((d : ℝ) * (m : ℝ) ^ 2) := by
        field_simp
      rw [e, h2, div_le_div_iff₀ (by positivity) (by positivity)]
      have hstep : (r : ℝ) * ((d : ℝ) * (m : ℝ) ^ 2) ≤ (d : ℝ) * ((d : ℝ) * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hrd (by positivity)
      nlinarith [mul_nonneg (mul_nonneg hd0.le hm0.le) hr0]
    calc ∑ m ∈ Finset.Icc 1 M,
            ((1 / (d : ℝ)) * (1 / (m : ℝ)) - 1 / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
        ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (d : ℝ)) * (((m : ℝ)) ^ 2)⁻¹ :=
          Finset.sum_le_sum hterm
      _ = (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 M, (((m : ℝ)) ^ 2)⁻¹ := by
          rw [← Finset.mul_sum]
      _ ≤ (1 / (d : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le M) (by positivity)
      _ = 2 / (d : ℝ) := by ring

/-! ## Wiring the WIN CONDITION to INFINITUDE — the composition a build cannot check

Two objects have been sitting one step apart in this file with nothing between them:

* `logSifted_lower_of_count_and_atoms` — the direct route's win condition, producing a LOWER BOUND
  on the sifted log-mass from `hcount` and `hatom`;
* `support_infinite_of_lower_unbounded` — the tail-mass argument, CONSUMING a lower bound on
  partial sums to produce an infinite support.

Its own doc says *"nothing in the corpus consumes it yet"*, and that was accurate.  **Both are
green, both are audited, and the interface between them was never stated** — which is the failure
mode a `lake build` is structurally unable to report: *the kernel checks theorems, not that they
compose.*  Stating it turns out to need three things that were not going to appear by themselves:

```
  a WEIGHT defined on all of ℕ        the win condition sums over a FILTERED Icc 1 N; the
                                      tail-mass lemma sums over range N.  The bridge is a
                                      weight extended BY ZERO off the sifted set, not a
                                      restriction of one.
  the n = 0 term                      `range (N+1)` carries it and `Icc 1 N` does not.  It
                                      vanishes for a reason worth naming: the weight divides
                                      by `n`, and Lean's `x / 0 = 0` kills it in BOTH branches
                                      of the coprimality test.
  an OFF-BY-ONE that is real          `hlow` wants `f N ≤ ∑_{range N}` while the win condition
                                      delivers `∑_{range (N+1)}`.  Going through the primitive
                                      `support_infinite_of_partialSums_unbounded` and handing it
                                      `N+1` as the witness dissolves it; going through the
                                      packaged `..._of_lower_unbounded` would have forced a
                                      shifted `f` with a false value at `N = 0`.
```
⇒ 🔑 ***AN INTERFACE NOBODY STATED IS NOT A SMALL GAP — IT IS THE PLACE WHERE TWO CORRECT OBJECTS
QUIETLY FAIL TO MEET.***  ⭐ And the third row is the one worth keeping: **the packaged lemma was
the WRONG consumer and the primitive it was built from was the right one.**  *A convenience wrapper
encodes an indexing convention, and a wrapper that does not match yours costs more than the
primitive.*

⚖️ **WHAT THIS DOES AND DOES NOT CLAIM.**  It is a COMPOSITION: `hcount`, `hatom` and the
divergence all remain hypotheses, exactly as they were.  **It supplies none of them and produces no
survivor.**  What it adds is that, once supplied, they yield INFINITELY MANY — not one survivor per
`N`, which is all a positivity statement gives.  ⛔ It is deliberately independent of how `hcount`
is discharged: the flagged per-class shape (`flags.md`, 08/26 19:1x) is a question about `hcount`'s
SUPPLIER, and nothing below reads it. -/

/-- The direct route's log-world weight, **extended by zero off the sifted set** — the shape the
tail-mass argument consumes.  On the sifted set it is the win condition's summand
`(1 − λ(n(n+2)))/n`; elsewhere it is `0`. -/
noncomputable def twinLogWeight (P : ℕ) (n : ℕ) : ℝ :=
  if Nat.Coprime (n * (n + 2)) P then
    (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ)
  else 0

/-- `twinLogWeight` is nonnegative — `λ(m) ≤ 1` pointwise (`liouville_real_le`), and the
denominator is a `ℕ`-cast.  This is the tail-mass lemma's `hw`. -/
theorem twinLogWeight_nonneg (P n : ℕ) : 0 ≤ twinLogWeight P n := by
  unfold twinLogWeight
  split
  · have h := liouville_real_le (n * (n + 2))
    exact div_nonneg (by linarith) (Nat.cast_nonneg n)
  · exact le_rfl

/-- **The bridge identity.**  The `range (N+1)` partial sum of the extended weight IS the win
condition's filtered `Icc 1 N` sum.

⭐ The `n = 0` term is where the two index conventions actually meet, and it vanishes **in both
branches**: the weight divides by `n`, and `x / 0 = 0`. -/
theorem sum_twinLogWeight_range (P N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), twinLogWeight P n)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P),
          (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ) := by
  classical
  have hzero : twinLogWeight P 0 = 0 := by
    unfold twinLogWeight; split <;> simp
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp), hzero, zero_add, Finset.sum_filter]
  rfl

/-- ⭐⭐ **THE DIRECT ROUTE'S WIN CONDITION, WIRED TO INFINITUDE.**  With the count, the atom mass
and the DIVERGENCE of `Hmain − A` all supplied, the sifted log-weight has infinite support.

⛔ **All three remain hypotheses; this supplies none of them.**  What it adds is the step a
positivity statement cannot make: `0 < siftedSum` at each `N` gives one survivor `≤ N` and is
consistent with the SAME `n` every time, whereas an unbounded mass cannot be carried by finitely
many terms.

📌 Independent of the flagged `hcount` shape by construction — `hcount` enters only through its
VALUE, never through how it is discharged. -/
theorem twinLogWeight_support_infinite_of_win {P : ℕ} (hP : Squarefree P) {A : ℝ}
    {Hmain : ℕ → ℝ}
    (hcount : ∀ N : ℕ, Hmain N ≤ ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
    (hatom : ∀ N : ℕ, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)| ≤ A)
    (hdiv : ∀ M : ℝ, ∃ N : ℕ, M < Hmain N - A) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  refine support_infinite_of_partialSums_unbounded (twinLogWeight_nonneg P) fun M => ?_
  obtain ⟨N, hN⟩ := hdiv M
  refine ⟨N + 1, ?_⟩
  rw [sum_twinLogWeight_range]
  exact lt_of_lt_of_le hN (logSifted_lower_of_count_and_atoms hP (hcount N) (hatom N))

/-- **What the infinite set actually is** — stated so the conclusion above is readable as a
statement about twin values rather than about an opaque support.

`twinLogWeight P n ≠ 0` says exactly: `n ≥ 1`, the twin value `n(n+2)` is coprime to `P`, and
`Ω(n(n+2))` is ODD.  ⭐ That is the `P`-rough parity survivor the campaign is after. -/
theorem twinLogWeight_ne_zero_iff {P n : ℕ} :
    twinLogWeight P n ≠ 0
      ↔ 1 ≤ n ∧ Nat.Coprime (n * (n + 2)) P
          ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2))) := by
  classical
  unfold twinLogWeight
  by_cases hcop : Nat.Coprime (n * (n + 2)) P
  · rw [if_pos hcop]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hne : n * (n + 2) ≠ 0 := by positivity
      have hL : ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)
          = ((-1 : ℤ) ^ ArithmeticFunction.cardFactors (n * (n + 2)) : ℤ) := by
        rw [ArithmeticFunction.liouville_apply hne]
      rw [div_ne_zero_iff]
      constructor
      · rintro ⟨h1, -⟩
        refine ⟨hn, hcop, ?_⟩
        rw [hL] at h1
        by_contra hodd
        rw [Nat.not_odd_iff_even] at hodd
        rw [hodd.neg_one_pow] at h1
        norm_num at h1
      · rintro ⟨-, -, hodd⟩
        refine ⟨?_, hn0⟩
        rw [hL, hodd.neg_one_pow]
        norm_num
  · rw [if_neg hcop]
    simp [hcop]

/-! ## The THIRD hypothesis — supplying `hdiv` from a growth RATE, and what that says about the flag

Running the same forward control over the assembled chain leaves exactly one input with no supplier
anywhere in the corpus and no campaign attached: **`hdiv`, the divergence**.  `hcount` is the
flagged per-class question and `hatom` is the Tao object, but `hdiv` is neither — it is pure
analysis, and it is discharged by ANY positive growth rate.

⭐⭐ **AND STATING IT MEASURES SOMETHING ABOUT THE FLAG THAT WAS NOT OBVIOUS: THE DOWNSTREAM CHAIN
DOES NOT CARE WHAT `c` IS, ONLY THAT IT IS POSITIVE.**  The consumer never reads the constant.  So
the flagged additive-vs-multiplicative question (`flags.md`, 08/26 19:1x) is **not** a question
about getting the RIGHT constant `W` — it is a question about whether ANY positive rate survives at
all.  A multiplicative sandwich on a CANCELLING sum can leave the lower bound NEGATIVE, in which
case there is no `c > 0` to hand this lemma; an additive error leaves `W·H + O(1)`, and `W > 0`.
⇒ 🔑 ***THE FLAG IS ABOUT THE EXISTENCE OF A RATE, NOT ITS VALUE*** — which makes it more
load-bearing than "we would lose a factor 2", and is worth knowing before it is ruled on.

⛔ **THIS DOES NOT SUPPLY `hgrow` AND DOES NOT PRESUPPOSE ITS SHAPE.**  Any producer of a positive
log-rate serves, per-class or otherwise.  *Where `hgrow` comes from is exactly where the flag
lives; this file's business is what happens once it exists.* -/

/-- **The divergence input from a growth RATE.**  If `Hmain N ≥ c·log N − C` with `c > 0`, then
`Hmain − A` is unbounded above, which is the tail-mass argument's `hdiv` for any fixed `A`.

⭐ **`c` may be arbitrarily small** — the conclusion is insensitive to it.  The witness is
`N = ⌈exp((M + A + C)/c + 1)⌉₊`, where the trailing `+1` buys the strict inequality with room `c`
to spare rather than by an epsilon argument. -/
theorem hdiv_of_log_growth {c C A : ℝ} (hc : 0 < c) {Hmain : ℕ → ℝ}
    (hgrow : ∀ N : ℕ, c * Real.log (N : ℝ) - C ≤ Hmain N) :
    ∀ M : ℝ, ∃ N : ℕ, M < Hmain N - A := by
  intro M
  set t : ℝ := (M + A + C) / c + 1 with ht
  refine ⟨⌈Real.exp t⌉₊, ?_⟩
  have hexp : Real.exp t ≤ ((⌈Real.exp t⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hlog : t ≤ Real.log ((⌈Real.exp t⌉₊ : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.exp_pos t) hexp
    rwa [Real.log_exp] at this
  have hmul : c * t ≤ c * Real.log ((⌈Real.exp t⌉₊ : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hc.le
  have hct : c * t = M + A + C + c := by
    rw [ht]; field_simp
  have hg := hgrow ⌈Real.exp t⌉₊
  linarith

/-- ⭐⭐ **THE PRIZE SHAPE, ASSEMBLED — TWO INPUTS AND NOTHING ELSE.**  Given the sifted count as a
POSITIVE LOG RATE, and the Tao atom mass as a uniform bound, the `P`-rough parity survivors are
INFINITE.

```
  hgrow :  c·log N − C ≤ Hmain N        (c > 0; the count, as a rate)
  hcount:  Hmain N ≤ ∑_{d∣P} μ(d)·C_d   (the count, at the Möbius skeleton)
  hatom :  |∑_{d∣P} μ(d)·(atom sum)| ≤ A (Tao — the campaign object)
  ⇒        {n : n ≥ 1, (n(n+2), P) = 1, Ω(n(n+2)) odd}  is INFINITE
```
⛔ **No `BoundingSieve`, no door, no `Btwin`, no level — and still no survivor**, because all three
inputs are hypotheses. **This is the shape of the prize with its last purely-analytic gap closed;
what remains is arithmetic that lives elsewhere.** -/
theorem twinLogWeight_support_infinite_of_rate {P : ℕ} (hP : Squarefree P) {A c C : ℝ}
    (hc : 0 < c) {Hmain : ℕ → ℝ}
    (hcount : ∀ N : ℕ, Hmain N ≤ ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
    (hatom : ∀ N : ℕ, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)| ≤ A)
    (hgrow : ∀ N : ℕ, c * Real.log (N : ℝ) - C ≤ Hmain N) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite :=
  twinLogWeight_support_infinite_of_win hP hcount hatom (hdiv_of_log_growth hc hgrow)

end Salt.TwinBar
