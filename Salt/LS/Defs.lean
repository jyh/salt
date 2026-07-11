/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Large sieve track, node L0.1: the frozen carriers `e` and `expSum`

Blueprint: `docs/blueprints/largesieve.md` (Rung 5 opener). This file freezes
the two carriers the whole track is built on:

* `e x = exp (2πi x)`, the additive character on `ℝ`;
* `expSum N a α = ∑ n < N, a n · e (n α)`, the exponential (trig) polynomial.

Together with the elementary trivia the analytic large sieve needs: `‖e x‖ = 1`,
1-periodicity, additivity, `e 0 = 1`, the conjugate identity
`conj (e x) = e (−x)`, and continuity of both `e` and `expSum` (the derivative
identities are deferred to W2). Continuity is registered with `@[fun_prop]` so
downstream integrability side goals discharge automatically — per the blueprint
docstring note, `expSum` is a finite sum of smooth terms and needs no
measurability nodes.
-/

namespace Salt.LS

open scoped BigOperators

/-- **L0.1 carrier.** The additive character `e(x) = exp(2πi·x)` on `ℝ`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- **L0.1 carrier.** The exponential polynomial `∑_{n<N} a n · e(nα)`. -/
noncomputable def expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * e (n * α)

/-- `e` has unit modulus: `‖e x‖ = 1`. -/
@[simp] lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  have : e x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- `e 0 = 1`. -/
@[simp] lemma e_zero : e 0 = 1 := by
  unfold e; simp

/-- Additivity of `e`: `e (x + y) = e x * e y`. -/
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `e 1 = 1`. -/
@[simp] lemma e_one : e 1 = 1 := by
  have : e 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

/-- `e` is 1-periodic: `e (x + 1) = e x`. -/
lemma e_add_one (x : ℝ) : e (x + 1) = e x := by
  rw [e_add, e_one, mul_one]

/-- The conjugate identity `conj (e x) = e (−x)`. -/
lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- `e` is continuous. Registered with `@[fun_prop]`/`@[continuity]` so
integrability side goals in the track discharge by `fun_prop`. -/
@[continuity, fun_prop]
lemma continuous_e : Continuous e := by
  unfold e; fun_prop

/-- `expSum N a` is continuous (finite sum of smooth terms). -/
@[continuity, fun_prop]
lemma continuous_expSum (N : ℕ) (a : ℕ → ℂ) : Continuous (expSum N a) := by
  unfold expSum
  apply continuous_finsetSum
  intro n _
  fun_prop

end Salt.LS
