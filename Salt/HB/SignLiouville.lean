/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.SignChain

/-!
# The Liouville instantiation of the sign-function chain (WALL-3, wave 2, node SignLiouville)

The generic sign-function transfer chain `Salt.HB.SignChain` is built from an arbitrary
real sign function `f : ℕ → ℝ` carrying only `IsSignFunction f`.  Here we instantiate it
at the **Liouville function** `λ`, realized as `lamR n = (liouville n : ℝ)`.

`λ` is completely multiplicative with `λ(p) = -1` at every prime, so `IsSignFunction lamR`
holds (`isSignFunction_lamR`).  The arithmetic heart is `gGen_lamR_eq_moebius`: because
`μ²·λ = μ` (the squarefree split — `μ²(d)` is `1` on squarefree `d` where `λ(d) = μ(d)`,
and `0` off it), the generic multiplier `μ²λ` collapses to the Möbius function itself.  The
convolution identity `Λ̃_f = (μ²f) ∗ log` then specializes through `μ ∗ log = Λ` to give the
**λ-pole** `LamTildeGen_lamR_eq_vonMangoldt : Λ̃_λ = Λ` exactly, recovering the von Mangoldt
function on the nose rather than merely bounding it.

## The neutrality point

Two consequences of the pole certify the *neutrality point* of the exchange-rate wall.
`S2Gen_lamR_eq_S1` shows the twisted twin sum `S⁽²⁾_λ` equals the untwisted `S⁽¹⁾` term by
term, and `overshootExactGen_lamR` shows the per-term transfer difference vanishes
identically: `overshootExactGen lamR n = 0` for every `n`.  Together they say that the
Liouville twist overshoots the true twin correlation by *exactly zero* — `λ` is the
zero-overshoot sign function, the fixed point where the wall's exchange rate is neutral.
Correspondingly `PretenseSumGen_lamR_eq_zero` records that `λ`'s pretense sum is empty:
`λ(p) = -1 ≠ 1` at every prime, so no prime contributes to the `f = 1` pretense — `λ` is the
"perfect pretense" against which every other sign function's positive overshoot is measured.

Single-writer file; it touches no landed file and is not yet in the `Salt.HB.All` manifest.
It builds standalone via `Salt.HB.SignChain`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Salt.HB

/-- The Liouville function `λ` as a real sign function `ℕ → ℝ`. -/
noncomputable def lamR : ℕ → ℝ := fun n => ((ArithmeticFunction.liouville n : ℤ) : ℝ)

/-- `λ(p) = -1` at every prime: `Ω(p) = 1`, so `liouville p = (-1)¹`. -/
theorem lamR_prime {p : ℕ} (hp : p.Prime) : lamR p = -1 := by
  simp only [lamR]
  rw [liouville_apply hp.pos.ne', cardFactors_apply_prime hp, pow_one]
  norm_num

/-- `λ` carries the sign-function packet: `λ(1) = 1`, complete multiplicativity,
    `|λ| ≤ 1`, and `λ(p) = ±1` (indeed `-1`) at every prime. -/
theorem isSignFunction_lamR : IsSignFunction lamR where
  map_one := by simp [lamR, liouville_apply_one]
  map_mul := by
    intro a b
    simp only [lamR, liouville_apply_mul]
    push_cast
    ring
  abs_le_one := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [lamR]
    · have h1 : |lamR n| = 1 := by
        simp only [lamR, liouville_apply hn]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
      exact h1.le
  prime_pm := fun p hp => Or.inr (lamR_prime hp)

/-- `μ²(d)·λ(d) = μ(d)`: on squarefree `d`, `μ²(d) = 1` and `λ(d) = μ(d)`; off it, both
    sides vanish (`μ(d) = 0`).  The squarefree split that collapses `μ²λ` to `μ`. -/
lemma moebius_sq_mul_lamR (d : ℕ) : (μ d : ℝ) ^ 2 * lamR d = (μ d : ℝ) := by
  by_cases hd : Squarefree d
  · have hd0 : d ≠ 0 := hd.ne_zero
    have hsq : (μ d : ℝ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hd
    have hlv : liouville d = μ d := by
      rw [liouville_apply hd0, moebius_apply_of_squarefree hd]
    rw [hsq, one_mul]
    simp only [lamR, hlv]
  · rw [moebius_eq_zero_of_not_squarefree hd]
    simp

/-- The generic multiplier `gGen λ = μ²λ` collapses to the Möbius function. -/
lemma gGen_lamR_eq_moebius : gGen lamR = (μ : ArithmeticFunction ℝ) := by
  ext n
  simp only [gGen_apply, moebius_sq_mul_lamR, intCoe_apply]

/-- **The λ-pole.** `Λ̃_λ(n) = Λ(n)` exactly: the convolution `Λ̃_λ = (μ²λ) ∗ log`
    specializes through `gGen_lamR_eq_moebius` and `μ ∗ log = Λ`. -/
theorem LamTildeGen_lamR_eq_vonMangoldt (n : ℕ) : LamTildeGen lamR n = Λ n := by
  rw [LamTildeGen_eq_conv, gGen_lamR_eq_moebius, moebius_mul_log_eq_vonMangoldt]

/-- The twisted twin sum `S⁽²⁾_λ` equals the untwisted `S⁽¹⁾` term by term. -/
theorem S2Gen_lamR_eq_S1 (A : Finset ℕ) : S2Gen lamR A = S1 A := by
  unfold S2Gen S1
  exact Finset.sum_congr rfl fun n _ => by
    simp only [LamTildeGen_lamR_eq_vonMangoldt]

/-- The per-term transfer overshoot of `λ` vanishes identically. -/
lemma overshootExactGen_lamR (n : ℕ) : overshootExactGen lamR n = 0 := by
  unfold overshootExactGen
  simp only [LamTildeGen_lamR_eq_vonMangoldt]
  ring

/-- `λ`'s pretense sum is empty: `λ(p) = -1 ≠ 1` at every prime. -/
theorem PretenseSumGen_lamR_eq_zero (N : ℕ) : PretenseSumGen lamR N = 0 := by
  unfold PretenseSumGen
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : Nat.Prime p := hp.2.1
  have hp1 : lamR p = 1 := hp.2.2
  rw [lamR_prime hpp] at hp1
  norm_num at hp1

end Salt.HB
