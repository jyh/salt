/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Parseval

/-!
# Large sieve track, nodes L2.1 + L2.2: the derivative of `expSum` and its Parseval bound

Blueprint: `docs/blueprints/largesieve.md`.

* **L2.1** — the derivative of the exponential polynomial is again an exponential
  polynomial, with the frequency `n` folded into the coefficient:
  `deriv (expSum N a) α = expSum N (fun n => 2πi·n · a n) α`
  (`deriv_expSum`), packaged as a global `HasDerivAt` (`hasDerivAt_expSum`) and a
  global `ContDiff ℝ 1` statement (`contDiff_expSum`) for feeding
  `gallagher_pointwise`.
* **L2.2** — the derivative Parseval + crude `n ≤ N` bound:
  `∫₀¹ ‖deriv (expSum N a)‖² ≤ (2πN)² · Σ ‖aₙ‖²` (`integral_norm_deriv_sq_le`).

The derivative identity is obtained termwise: each summand
`a n · e(nα) = a n · exp((2πi·n)·α)` has derivative `2πi·n · a n · e(nα)` by the
chain rule (`HasDerivAt.cexp`); `HasDerivAt.sum` assembles the finite sum. The
L2.2 bound then rewrites the derivative back into `expSum` form, applies the
landed `parseval`, and estimates `‖2πi·n·aₙ‖² = 4π²n²‖aₙ‖² ≤ 4π²N²‖aₙ‖²`.
-/

namespace Salt.LS

open scoped BigOperators
open Complex MeasureTheory

/-- The frequency-twisted coefficient sequence `n ↦ 2πi·n · a n`; `deriv (expSum N a)`
is `expSum N` of this sequence (L2.1). -/
noncomputable def twist (a : ℕ → ℂ) (n : ℕ) : ℂ := 2 * Real.pi * Complex.I * (n : ℂ) * a n

/-- Termwise derivative: `d/dα [a n · e(nα)] = (2πi·n · a n) · e(nα)`. -/
lemma hasDerivAt_expSum_term (a : ℕ → ℂ) (n : ℕ) (α : ℝ) :
    HasDerivAt (fun α : ℝ => a n * e ((n : ℝ) * α)) (twist a n * e ((n : ℝ) * α)) α := by
  set C : ℂ := 2 * Real.pi * Complex.I * (n : ℂ) with hCdef
  have hval : e ((n : ℝ) * α) = Complex.exp (C * (α : ℂ)) := by
    unfold e; rw [hCdef]; push_cast; ring_nf
  have hfun : (fun α : ℝ => e ((n : ℝ) * α)) = fun α : ℝ => Complex.exp (C * (α : ℂ)) := by
    funext β; unfold e; rw [hCdef]; push_cast; ring_nf
  have h1 : HasDerivAt (fun α : ℝ => ((α : ℂ))) 1 α := by
    simpa using (hasDerivAt_id α).ofReal_comp
  have h2 : HasDerivAt (fun α : ℝ => C * (α : ℂ)) (C * 1) α := h1.const_mul _
  have h3 : HasDerivAt (fun α : ℝ => Complex.exp (C * (α : ℂ)))
      (Complex.exp (C * (α : ℂ)) * (C * 1)) α := h2.cexp
  have he : HasDerivAt (fun α : ℝ => e ((n : ℝ) * α)) (C * e ((n : ℝ) * α)) α := by
    rw [hfun, hval]; convert h3 using 1; ring
  have hmul := he.const_mul (a n)
  have hval2 : a n * (C * e ((n : ℝ) * α)) = twist a n * e ((n : ℝ) * α) := by
    rw [hCdef, twist]; ring
  rw [hval2] at hmul
  exact hmul

/-- **L2.1 (HasDerivAt form).** `expSum N a` is differentiable with derivative the
frequency-twisted exponential polynomial `expSum N (twist a)`. -/
theorem hasDerivAt_expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    HasDerivAt (expSum N a) (expSum N (twist a) α) α := by
  have h := HasDerivAt.sum (u := Finset.range N)
    (A := fun n => fun α : ℝ => a n * e ((n : ℝ) * α))
    (A' := fun n => twist a n * e ((n : ℝ) * α))
    (fun n _ => hasDerivAt_expSum_term a n α)
  have hfun : expSum N a = ∑ n ∈ Finset.range N, fun α : ℝ => a n * e ((n : ℝ) * α) := by
    funext α; rw [Finset.sum_apply]; rfl
  rw [hfun]
  exact h

/-- **L2.1 (deriv form).** The pointwise derivative identity. -/
theorem deriv_expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) :
    deriv (expSum N a) α = expSum N (twist a) α :=
  (hasDerivAt_expSum N a α).deriv

/-- Each summand `a n · e(nα)` is `C¹` (indeed smooth). -/
lemma contDiff_expSum_term (a : ℕ → ℂ) (n : ℕ) :
    ContDiff ℝ 1 (fun α : ℝ => a n * e ((n : ℝ) * α)) := by
  have hfun : (fun α : ℝ => a n * e ((n : ℝ) * α))
      = fun α : ℝ => a n * Complex.exp ((2 * Real.pi * Complex.I * (n : ℂ)) * (α : ℂ)) := by
    funext β; unfold e; push_cast; ring_nf
  rw [hfun]
  have hof : ContDiff ℝ 1 (fun α : ℝ => (α : ℂ)) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((Complex.contDiff_exp).comp (contDiff_const.mul hof))

/-- **L2.1 (ContDiff form).** `expSum N a` is globally `C¹` — the hypothesis
`gallagher_pointwise` consumes. -/
theorem contDiff_expSum (N : ℕ) (a : ℕ → ℂ) : ContDiff ℝ 1 (expSum N a) := by
  unfold expSum
  exact ContDiff.sum (fun n _ => contDiff_expSum_term a n)

/-- `deriv (expSum N a)` is continuous (it is again an `expSum`). -/
lemma continuous_deriv_expSum (N : ℕ) (a : ℕ → ℂ) :
    Continuous (deriv (expSum N a)) := by
  have : deriv (expSum N a) = expSum N (twist a) := by
    funext α; exact deriv_expSum N a α
  rw [this]; exact continuous_expSum N (twist a)

/-- `‖twist a n‖² = 4π²·n²·‖a n‖²`. -/
lemma norm_twist_sq (a : ℕ → ℂ) (n : ℕ) :
    ‖twist a n‖ ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖a n‖ ^ 2 := by
  unfold twist
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, Complex.norm_real, Complex.norm_I,
    Complex.norm_natCast, Real.norm_of_nonneg Real.pi_pos.le]
  ring

/-- **L2.2 — derivative Parseval + crude `n ≤ N` bound (FROZEN shape).**
`∫₀¹ ‖deriv (expSum N a)‖² ≤ (2πN)² · Σ ‖aₙ‖²`. -/
theorem integral_norm_deriv_sq_le (N : ℕ) (a : ℕ → ℂ) :
    (∫ α in (0:ℝ)..1, ‖deriv (expSum N a) α‖ ^ 2)
      ≤ (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have hrw : (∫ α in (0:ℝ)..1, ‖deriv (expSum N a) α‖ ^ 2)
      = ∑ n ∈ Finset.range N, ‖twist a n‖ ^ 2 := by
    rw [show (fun α => ‖deriv (expSum N a) α‖ ^ 2)
          = (fun α => ‖expSum N (twist a) α‖ ^ 2) from by
        funext α; rw [deriv_expSum]]
    exact parseval N (twist a)
  rw [hrw]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_twist_sq]
  have hnN : (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Finset.mem_range.mp hn).le
  have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [hnN, Nat.cast_nonneg (α := ℝ) n]
  have hcoef : 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≤ (2 * Real.pi * N) ^ 2 := by
    have hexp : (2 * Real.pi * N) ^ 2 = 4 * Real.pi ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [hexp]
    nlinarith [hsq, Real.pi_pos, sq_nonneg Real.pi]
  calc 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖a n‖ ^ 2
      ≤ (2 * Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right hcoef (by positivity)

end Salt.LS
