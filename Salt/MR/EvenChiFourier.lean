/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Salt.MR.Sawtooth
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# E3 — the even-`χ` Fourier identity at `s = 1`

`τ(χ) · L(1, χ⁻¹) = Σ_j χ(j) · (−log(1 − ζ^{−j}))` for primitive even `χ` at modulus `N ≠ 1`.

This is the analytic hinge of the even-`χ` floor ladder.  It lives in its own module rather
than in `Salt.MR.Sawtooth` because it needs the `DirichletCharacter` / discrete-Fourier /
`LSeries` machinery, which has no business in a real-analysis file; Sawtooth carries only the
boundary values it consumes.

The three legs are all landed mathlib, which is why the refuter repriced this node down:
* `ZMod.LFunction_dft` — the L-function of a discrete Fourier transform, carrying the
  *disjunctive* hypothesis `Φ 0 = 0 ∨ s ≠ 1`.  A Dirichlet character kills the first disjunct,
  so it applies at `s = 1` directly and no continuity extension is needed.
* `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` — `𝓕 χ k = χ⁻¹(-k)·τ(χ)`.
* `expZeta_apply_one` (below) — whose cosine half is `cosZeta_apply_one` (§5b of Sawtooth) and
  whose sine half is `sinZeta_apply_one` (§5), already landed by the odd lane together with the
  polar decomposition of `1 − e^{2πix}`.
-/

namespace Salt.MR

open Complex Filter Topology Finset
open scoped Real ZMod

/-! ## E3 leg — the boundary value of `expZeta`

`expZeta a s = cosZeta a s + I * sinZeta a s` by definition (mathlib
`HurwitzZeta.lean:115`).  At `s = 1` the cosine half is `cosZeta_apply_one` above (W1/E2,
genuinely absent from mathlib) and the sine half is `sinZeta_apply_one`
(`Salt/MR/Sawtooth.lean:468`, LANDED by the odd lane).  Their combination is exactly the
principal branch of `-log (1 - e^{2πix})`, because `1 - e^{2πix}` has modulus `2 sin (πx)`
and argument `πx - π/2` — both already established here as `norm_one_sub_exp` and
`one_sub_exp_eq`.

This is the analytic input to E3 `LFunction_one_even_fourier`; it is NOT itself E3. -/
theorem expZeta_apply_one {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.expZeta (x : UnitAddCircle) 1
      = -Complex.log (1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)) := by
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx
  have hθ : (Real.pi * x - Real.pi / 2) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · nlinarith [Real.pi_pos, hx.1, hx.2]
    · nlinarith [Real.pi_pos, hx.1, hx.2]
  have harg : Complex.arg (1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I))
      = Real.pi * x - Real.pi / 2 := by
    rw [one_sub_exp_eq x]
    exact Complex.arg_mul_cos_add_sin_mul_I (by linarith) hθ
  rw [HurwitzZeta.expZeta, cosZeta_apply_one hx, sinZeta_apply_one hx, Complex.log,
    norm_one_sub_exp hx, harg]
  push_cast
  ring

/-! ## E3 proper — `LFunction_one_even_fourier`

`τ(χ) · L(1, χ⁻¹) = Σ_j χ(j) · (−log(1 − ζ^{−j}))` for primitive even `χ` at modulus `N ≠ 1`.

The `N ≠ 1` hypothesis is NOT decorative and is NOT implied by `NeZero N`: `LFunction_dft`
needs `Φ 0 = 0`, and `DirichletCharacter.map_zero'` supplies that only under `n ≠ 1`.  (At
`N = 1` the character is trivial, `χ 0 = 1`, and the `j = 0` term is a genuine pole — this is
the same pole of `ζ` that every rung of this ladder has to name its way around.)  The ladder
document leaves this rider unstated; mathlib does not. -/
theorem LFunction_one_even_fourier {N : ℕ} [NeZero N] (hN : N ≠ 1)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hev : χ.Even) :
    gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1
      = ∑ j : ZMod N, χ j *
          (-Complex.log (1 - Complex.exp (((2 * Real.pi * ((-j).val / N : ℝ) : ℝ) : ℂ) * I))) := by
  have hz : (χ : ZMod N → ℂ) 0 = 0 := χ.map_zero' hN
  -- the inverse of an even character is even
  have hinveven : ∀ k : ZMod N,
      (χ⁻¹ : DirichletCharacter ℂ N) (-k) = (χ⁻¹ : DirichletCharacter ℂ N) k := by
    intro k
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hev.to_fun k]
  -- (1) the Fourier side: `𝓕 χ k = χ⁻¹ (-k) · τ(χ)`, so the L-function scales by `τ(χ)`.
  have hfour : ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) 1
      = gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1 := by
    simp only [ZMod.LFunction, DirichletCharacter.LFunction,
      DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ, hinveven,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- (2) the arithmetic side: the boundary value at every `j ≠ 0`; the `j = 0` term vanishes.
  have hsum : ∑ j : ZMod N, (χ : ZMod N → ℂ) j * HurwitzZeta.expZeta (ZMod.toAddCircle (-j)) 1
      = ∑ j : ZMod N, χ j *
          (-Complex.log (1 - Complex.exp (((2 * Real.pi * ((-j).val / N : ℝ) : ℝ) : ℂ) * I))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp [hz]
    · have hnj : (-j) ≠ 0 := neg_ne_zero.mpr hj
      have hNpos : 0 < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      have hvpos : 0 < ((-j).val : ℝ) := by
        have := ZMod.val_pos.mpr hnj
        exact_mod_cast this
      have hvlt : ((-j).val : ℝ) < N := by
        exact_mod_cast ZMod.val_lt (-j)
      have hmem : ((-j).val / N : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨div_pos hvpos hNpos, (div_lt_one hNpos).mpr hvlt⟩
      rw [ZMod.toAddCircle_apply, expZeta_apply_one hmem]
  rw [← hfour, ZMod.LFunction_dft _ (Or.inl hz), hsum]

/-! ### Positive control: the `N ≠ 1` hypothesis is KERNEL-NECESSARY, not route-necessary

`feedback_mutation_control`: a mutation is a valid positive control only if it makes the goal
FALSE, not merely unreachable by one route.  Dropping `hN` is such a mutation — at `N = 1` the
left side is `riemannZeta 1 ≠ 0` and the right side is `0`, because the `j = 0` term the
hypothesis exists to kill contributes `-log (1 - e⁰) = -log 0 = 0` while the L-function keeps
`ζ`'s pole value.  So this is a witness against the `hN`-free statement, not a failed proof. -/
theorem LFunction_one_even_fourier_needs_modulus_ne_one (χ : DirichletCharacter ℂ 1) :
    gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1
      ≠ ∑ j : ZMod 1, χ j *
          (-Complex.log (1 - Complex.exp (((2 * Real.pi * (((-j).val : ℝ) / ((1 : ℕ) : ℝ)) : ℝ) : ℂ)
            * I))) := by
  have hchi : ∀ a : ZMod 1, χ a = 1 := fun a => by
    rw [Subsingleton.elim a 1, map_one]
  -- the right-hand side collapses to zero: every `(-j).val` is `0`, and `Complex.log 0 = 0`
  have hRHS : (∑ j : ZMod 1, χ j *
      (-Complex.log (1 - Complex.exp (((2 * Real.pi * (((-j).val : ℝ) / ((1 : ℕ) : ℝ)) : ℝ) : ℂ)
        * I)))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hv : ((-j).val : ℝ) = 0 := by
      rw [Subsingleton.elim (-j) 0]; norm_num
    rw [hv]
    norm_num
  -- the left-hand side is `riemannZeta 1`, which mathlib knows is nonzero
  have hgauss : gaussSum χ ZMod.stdAddChar = 1 := by
    simp only [gaussSum, hchi, one_mul]
    rw [Finset.sum_eq_single (0 : ZMod 1)
        (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
        (fun h => absurd (Finset.mem_univ (0 : ZMod 1)) h),
      AddChar.map_zero_eq_one]
  rw [hRHS, hgauss, one_mul, DirichletCharacter.LFunction_modOne_eq]
  exact riemannZeta_one_ne_zero

end Salt.MR
