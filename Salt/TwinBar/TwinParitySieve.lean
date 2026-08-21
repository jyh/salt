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
import Salt.Maynard.GehPp2

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

end Salt.TwinBar
