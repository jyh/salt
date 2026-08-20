/-
# The Gauss sum at an even real character — reality, and magnitude

Module 6 of the even-χ port (2026-08-19).

## What it establishes

* `e4a_gaussSum_real` — **τ(χ) IS REAL** at an EVEN QUADRATIC χ.  Route: `conj τ(χ) = τ(χ̄)`,
  which mathlib already has as `star_gaussSum_eq`.  ⭐ **Primitivity is NOT needed for
  reality** — even + quadratic suffices, which is weaker than the ladder's design assumed.
* `e4a_gaussSum_even_inv_addChar` — a `[Field R]`-free replacement for mathlib's
  `mul_gaussSum_inv_eq_gaussSum`, which sits under `[Field R]` GRATUITOUSLY and is therefore
  unavailable at `ZMod q` for composite `q`.  Its proof uses no field structure.
* `e4a_gaussSum_re_eq_pm_sqrt` — `τ.re = ±√q`, from `‖τ‖² = q`.
  ⛔ **The MAGNITUDE, unlike the reality, IS primitive-bound** (`gaussSum_normSq_of_primitive`),
  and it is the only source of the `√q` in the ground.  The SIGN is deliberately left
  unproved: `cosh` is even, so the ladder never needs it.
* `e4a_gaussSum_re_ne_zero` / `e4a_abs_gaussSum_re` — `τ.re ≠ 0` and `|τ.re| = √q`.
-/
import Salt.MR.EvenChiRingBridge

namespace Salt.MR

open scoped ComplexOrder

/-- `[Field R]`-free replacement for `mul_gaussSum_inv_eq_gaussSum`, specialised to an
EVEN character: inverting the additive character leaves the Gauss sum alone. -/
theorem e4a_gaussSum_even_inv_addChar {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (heven : χ (-1) = 1) :
    gaussSum χ ψ⁻¹ = gaussSum χ ψ := by
  have key := gaussSum_mulShift χ ψ (-1)
  rw [Units.coe_neg_one, heven, one_mul] at key
  rw [AddChar.inv_mulShift]
  exact key

/-- **τ(χ) is real** for an even, quadratic (= real-valued) Dirichlet character mod `q`.
Conclusion in the `.im = 0` form. -/
theorem e4a_gaussSum_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, starRingEnd_apply, star_gaussSum_eq, hquad.inv,
    e4a_gaussSum_even_inv_addChar χ _ heven]

/-- Same statement in the `∃ r : ℝ` form. -/
theorem e4a_gaussSum_eq_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    ∃ r : ℝ, gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) = (r : ℂ) :=
  ⟨(gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re, by
    refine Complex.ext ?_ ?_
    · simp
    · simp [e4a_gaussSum_real χ heven hquad]⟩

/-- With τ real, `‖τ‖² = q` reads directly on the real part. -/
theorem e4a_gaussSum_re_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re ^ 2 = (q : ℝ) := by
  obtain ⟨r, hr⟩ := e4a_gaussSum_eq_real χ heven hquad
  have hn := Salt.LS.gaussSum_normSq χ hprim
  rw [hr] at hn
  rw [hr]
  simpa using hn

/-- ⭐ **τ = ±√q.**  The SIGN is not determined here and is not needed — `cosh` is even, and
`e4a_cosh_of_pm` / `e4a_cosh_integer_of_pm` absorb it.  What IS needed, and is supplied only
by primitivity, is the MAGNITUDE. -/
theorem e4a_gaussSum_re_eq_pm_sqrt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re = Real.sqrt q
      ∨ (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re = -Real.sqrt q := by
  have h := e4a_gaussSum_re_sq χ hprim heven hquad
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hs : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hq
  have hfac : ((gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re - Real.sqrt q) *
      ((gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re + Real.sqrt q) = 0 := by
    nlinarith [h, hs]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; linarith
  · right; linarith


#print axioms e4a_gaussSum_re_sq
#print axioms e4a_gaussSum_re_eq_pm_sqrt

/-! ### ⭐⭐ THE MIDDLE, CLOSED — the sine sum IS `−log` of the sine PRODUCT

⭐ NOTHING WAS GENERALISED HERE EITHER, and that is now three for three: `e4a_log_zpow_prod`
was ALREADY stated over an arbitrary index `ι`, exactly like `e4a_sum_clog_re`.  The only new
content is the SIDE CONDITION — that the sine does not vanish at a unit's coordinate — which
is `Salt.MR.sin_pi_mul_pos` plus `0 < val < q`.

⛔ STILL NOT the tier-locked statement, and still not `log η = √q·Re L`: this closes
`Re(τ·L) = −log ∏ (2 sin)^{χ}`.  Naming `∏ (2 sin)^{χ}` as η, and pulling the `√q` out of
`τ.re`, are the two remaining steps and BOTH are statement-shaped. -/

/-- τ's real part is nonzero: its square is `q`. -/
theorem e4a_gaussSum_re_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re ≠ 0 := by
  intro h
  have hsq := e4a_gaussSum_re_sq χ hprim heven hquad
  rw [h] at hsq
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← hsq] at hq
  simp at hq

/-- `|τ.re| = √q` — the magnitude, with the sign discarded exactly where it stops mattering. -/
theorem e4a_abs_gaussSum_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    |(gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re| = Real.sqrt q := by
  have hnn : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
  rcases e4a_gaussSum_re_eq_pm_sqrt χ hprim heven hquad with h | h
  · rw [h, abs_of_nonneg hnn]
  · rw [h, abs_neg, abs_of_nonneg hnn]

end Salt.MR
