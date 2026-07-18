/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.StepFull
import Salt.Vmvt.PrimeCount

/-!
# Theorem 24.5 — THE SUMMIT (VMVT-R5b)

The medium-`x` trivial branch and the induction scaffolding for the full
Vinogradov Mean Value Theorem, atop the re-graded constant `vmvtC0 k = k^{24k²}`
(`MeanValue.lean`, VMVT-R5b re-grade) and the large-`x` transversal step
`vmvt_step_transversal_large` (`StepFull.lean`).

## Contents

* `JkI_crude` — the crude count `J_k(x, b) ≤ x^{2b}` (solutions ⊆ box × box).
* `vmvtEta_ge` — the Bernoulli lower bound `η(k,r) ≥ ½k² − ½kr`
  (`one_add_mul_le_pow` at `a = −1/k`).
* `b_le_vmvtExp` — the range side lemma `k·r ≤ E(k,r)` (discrete induction,
  `f(r+1) − f(r) = k − η/k ≥ 0`).
* `vmvt_trivial_branch` — the medium-`x` branch: for `x ≤ Xmed k r = k^{24·max(k,r)}`,
  the crude `x^{2kr}` bound already gives `VmvtBound k r x` under the re-graded
  `C₀`, via the deficit split `½k(k+1) − η ≤ min(k², kr)` and
  `max(k,r)·min(k²,kr) ≤ r·k²`.

## Stone 3 (`vmvt`, THE SUMMIT INDUCTION): CLOSED in `Summit2.lean` (VMVT-SUMMIT-2)

The R5b flag (the `k`-independent, non-explicit prime-supply threshold
`y₀ = max(⌈e^{6K}⌉, 1280000)` of `primes_in_Ioc_ge`) is repaired by the effective
interval count `primes_in_Ioc_eff` (`PrimeEff.lean`, Erdős/Bertrand central-binomial
route, threshold `y₁ ≤ 2²⁴`) and the SUMMIT-2 re-grade to `C₀ = k^{24k²}` above.
The induction `vmvt` and its pigeonhole re-supply `exists_transversal_prime_set'`
live in `Summit2.lean`; the two-arm bridge `Xmed = k^{24·max(k,r)} ≥ Y'(k)^k` clears
at `k ≥ 2`. -/

namespace Salt.Vmvt

open Finset

/-! ## The re-graded constant in closed power form -/

/-- `D(k,r) = (C₀ k)^r = k^{24k²r}` with the re-graded `vmvtC0 k = k^{24k²}`. -/
lemma vmvtConst_eq (k r : ℕ) : vmvtConst k r = (k : ℝ) ^ (24 * k ^ 2 * r) := by
  unfold vmvtConst vmvtC0
  rw [← pow_mul]

/-! ## The crude count `J_k(x, b) ≤ x^{2b}` -/

/-- **The crude count.**  `J_k(x, b) ≤ x^{2b}`: the solution set is a subset of
`box^b × box^b` with `|box| = |(0,x]| = x`, so its cardinality is `≤ x^b·x^b`. -/
theorem JkI_crude (k b x : ℕ) : JkI k b x ≤ x ^ (2 * b) := by
  have hAcard : (Finset.Ioc (0 : ℤ) (x : ℤ)).card = x := card_Ioc_zero x
  have hle : JkI k b x
      ≤ (Fintype.piFinset fun _ : Fin b => Finset.Ioc (0 : ℤ) (x : ℤ)).card
        * (Fintype.piFinset fun _ : Fin b => Finset.Ioc (0 : ℤ) (x : ℤ)).card := by
    unfold JkI Jk solSet
    rw [← Finset.card_product]
    exact Finset.card_filter_le _ _
  refine hle.trans (le_of_eq ?_)
  rw [Fintype.card_piFinset_const, hAcard, ← pow_add, ← two_mul]

/-! ## The Bernoulli lower bound on `η` -/

/-- **The Bernoulli lower bound.**  `η(k,r) = ½k²(1−1/k)^r ≥ ½k² − ½kr`, from
`(1 − 1/k)^r ≥ 1 − r/k` (`one_add_mul_le_pow` at `a = −1/k`). -/
theorem vmvtEta_ge {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    (1 / 2) * (k : ℝ) ^ 2 - (1 / 2) * (k : ℝ) * (r : ℝ) ≤ vmvtEta k r := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hH : (-2 : ℝ) ≤ -1 / (k : ℝ) := by
    rw [neg_div]
    have h1 : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact hkR
    linarith
  have hber := one_add_mul_le_pow hH r
  have he1 : (1 : ℝ) + (-1 / (k : ℝ)) = 1 - 1 / (k : ℝ) := by ring
  have he2 : (1 : ℝ) + (r : ℝ) * (-1 / (k : ℝ)) = 1 - (r : ℝ) / (k : ℝ) := by
    ring
  rw [he1, he2] at hber
  unfold vmvtEta
  have hk2 : (0 : ℝ) ≤ (1 / 2) * (k : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hber hk2
  have heq : (1 / 2) * (k : ℝ) ^ 2 - (1 / 2) * (k : ℝ) * (r : ℝ)
      = (1 / 2) * (k : ℝ) ^ 2 * (1 - (r : ℝ) / (k : ℝ)) := by
    field_simp
  rw [heq]
  exact hmul

/-! ## The range side lemma `k·r ≤ E(k,r)` (the `hrange` input) -/

/-- **The range bound.**  `k·r ≤ E(k,r)` for `k ≥ 2`, `r ≥ 1` (equality at `r = 1`).
Discrete induction: `f(r) = E(k,r) − k·r` has `f(1) = 0` and step-difference
`f(r+1) − f(r) = k − η(k,r)/k ≥ 0` (since `η(k,r) ≤ ½k(k−1) < k²`). -/
theorem b_le_vmvtExp {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    ((k * r : ℕ) : ℝ) ≤ vmvtExp k r := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  induction r, hr using Nat.le_induction with
  | base =>
    rw [vmvtExp_one k hk0]
    exact le_of_eq (by push_cast; ring)
  | succ n hn ih =>
    rw [vmvtExp_step_diff k n hk0]
    have hη : vmvtEta k n ≤ (1 / 2) * (k : ℝ) * ((k : ℝ) - 1) :=
      vmvtEta_le (k := k) (r := n) (by omega) hn
    have hstep : (k : ℝ) ≤ 2 * (k : ℝ) - vmvtEta k n / (k : ℝ) := by
      have hηk : vmvtEta k n / (k : ℝ) ≤ (k : ℝ) := by
        rw [div_le_iff₀ hkpos]; nlinarith [hη, hkpos]
      linarith [hηk]
    have hcast : ((k * (n + 1) : ℕ) : ℝ) = ((k * n : ℕ) : ℝ) + (k : ℝ) := by
      push_cast; ring
    rw [hcast]
    linarith [ih, hstep]

/-! ## The medium-`x` threshold and the trivial branch -/

/-- The medium-`x` threshold `Xmed k r = k^{24·max(k,r)}`.  Below it the crude count
already gives `VmvtBound` under the re-graded `C₀ = k^{24k²}`. -/
noncomputable def Xmed (k r : ℕ) : ℕ := k ^ (24 * max k r)

/-- **The trivial (medium-`x`) branch.**  For `x ≤ Xmed k r = k^{24·max(k,r)}` the
crude count `J_k(x, kr) ≤ x^{2kr}` already lands `VmvtBound k r x`.  The deficit
`2kr − E(k,r) = ½k(k+1) − η(k,r)` is `≤ min(k², kr)` (from `η ≥ 0` and the
Bernoulli `η ≥ ½k² − ½kr`), and `max(k,r)·min(k²,kr) ≤ r·k²` (case split), so
`x^{deficit} ≤ k^{24·max(k,r)·deficit} ≤ k^{24rk²} = D(k,r)`. -/
theorem vmvt_trivial_branch {k r x : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ r) (hx : 1 ≤ x)
    (hxmed : x ≤ Xmed k r) : VmvtBound k r x := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxR0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hxmed' : x ≤ k ^ (24 * max k r) := hxmed
  -- the crude count, in ℝ, as an rpow
  have hcrudeN : JkI k (k * r) x ≤ x ^ (2 * (k * r)) := JkI_crude k (k * r) x
  have hcrude : (JkI k (k * r) x : ℝ) ≤ (x : ℝ) ^ ((2 * (k * r) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast hcrudeN
  set E : ℝ := vmvtExp k r with hEdef
  set D : ℝ := ((2 * (k * r) : ℕ) : ℝ) - E with hDdef
  have hDform : D = (1 / 2) * (k : ℝ) * ((k : ℝ) + 1) - vmvtEta k r := by
    rw [hDdef, hEdef]; unfold vmvtExp; push_cast; ring
  have hη0 : 0 ≤ vmvtEta k r := vmvtEta_nonneg (k := k) (by omega) r
  have hηle : vmvtEta k r ≤ (1 / 2) * (k : ℝ) * ((k : ℝ) - 1) :=
    vmvtEta_le (k := k) (r := r) (by omega) hr
  have hηge : (1 / 2) * (k : ℝ) ^ 2 - (1 / 2) * (k : ℝ) * (r : ℝ) ≤ vmvtEta k r :=
    vmvtEta_ge (k := k) (by omega) r
  have hD0 : 0 ≤ D := by rw [hDform]; nlinarith [hηle, hk1R]
  have hDksq : D ≤ (k : ℝ) ^ 2 := by rw [hDform]; nlinarith [hη0, hk1R, hkpos]
  have hDkr : D ≤ (k : ℝ) * (r : ℝ) := by
    rw [hDform]; nlinarith [hηge, hkpos, hrR1]
  have hxmedR : (x : ℝ) ≤ (k : ℝ) ^ ((24 * max k r : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    calc (x : ℝ) ≤ ((k ^ (24 * max k r) : ℕ) : ℝ) := by exact_mod_cast hxmed'
      _ = (k : ℝ) ^ (24 * max k r) := by push_cast; ring
  -- x^deficit ≤ D(k,r)
  have hkey : (x : ℝ) ^ D ≤ vmvtConst k r := by
    have h1 : (x : ℝ) ^ D ≤ ((k : ℝ) ^ ((24 * max k r : ℕ) : ℝ)) ^ D :=
      Real.rpow_le_rpow (by positivity) hxmedR hD0
    have h2 : ((k : ℝ) ^ ((24 * max k r : ℕ) : ℝ)) ^ D
        = (k : ℝ) ^ (((24 * max k r : ℕ) : ℝ) * D) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h2] at h1
    refine h1.trans ?_
    rw [vmvtConst_eq, ← Real.rpow_natCast (k : ℝ) (24 * k ^ 2 * r)]
    apply Real.rpow_le_rpow_of_exponent_le hk1R
    rw [show ((24 * max k r : ℕ) : ℝ) = 24 * ((max k r : ℕ) : ℝ) by push_cast; ring,
      show ((24 * k ^ 2 * r : ℕ) : ℝ) = 24 * (k : ℝ) ^ 2 * (r : ℝ) by push_cast; ring]
    rcases le_total r k with hrk | hkr
    · have hmax : (max k r : ℕ) = k := by omega
      rw [hmax]; nlinarith [hDkr, hkpos]
    · have hmax : (max k r : ℕ) = r := by omega
      rw [hmax]; nlinarith [hDksq, hrR1]
  -- assemble
  unfold VmvtBound
  rw [← hEdef]
  calc (JkI k (k * r) x : ℝ)
      ≤ (x : ℝ) ^ ((2 * (k * r) : ℕ) : ℝ) := hcrude
    _ = (x : ℝ) ^ (E + D) := by congr 1; rw [hDdef]; ring
    _ = (x : ℝ) ^ E * (x : ℝ) ^ D := Real.rpow_add hxR0 E D
    _ ≤ (x : ℝ) ^ E * vmvtConst k r :=
        mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (le_of_lt hxR0) E)
    _ = vmvtConst k r * (x : ℝ) ^ E := by ring

end Salt.Vmvt
