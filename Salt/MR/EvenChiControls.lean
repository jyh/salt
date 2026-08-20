/-
# ⛔ NEGATIVE CONTROLS — what the even-χ hypotheses would cost if they were dropped

**NOTHING IN THIS FILE IS A THEOREM ABOUT THE EVEN-χ MATHEMATICS.** Every declaration here
exists to REFUTE something, or to be the positive arm that shows a refutation discriminates.
A reader who cites one of these as a result about `L(1,χ)` has misread the file.

## Why the corpus carries them at all

The seat's standing law is that **a check never shown to fail has not been shown to
discriminate** — and the corpus was, until this module, in exactly that position about its own
hypotheses. `Salt.MR.e4a_gaussSum_real` says τ is real at an **even** quadratic χ, and nothing
in the tree said what the evenness was doing. **A corpus that carries a hypothesis but not the
witness that the hypothesis is load-bearing is carrying an unfalsified claim.**
*(Ported at the helm's 21:0x port-rule amendment: negative controls and non-vacuity witnesses
PORT; only superseded routes and dead ends stay in custody.)*

## What each one refutes — read this, not the names

* `e4a_descent_needs_integrality` — refutes *"the descent works without integrality"*.
  **A WITNESS in ℚ**: `¬ ∃ z : ℤ, z = 1/2 + (1/2)⁻¹`. ℚ is chosen because the OTHER
  hypothesis goes vacuous there, so the one under test is ISOLATED.
* `e4a_descent_holds_when_integral` — refutes nothing; it is the **POSITIVE ARM**. Without
  it the control above shows only that *some* input fails, not that integrality is the
  variable. **Both arms differ — that is what makes it a control rather than a remark.**
* `e4a_gaussSum_mutant_is_false` — refutes *"τ is real at an ODD quadratic χ too"*. At
  `χ(−1) = −1` and primitive χ, `τ.im ≠ 0`: the exact NEGATION of the mutated conclusion,
  so the mutant is FALSE, not merely unreachable. **This is what makes `heven`
  load-bearing rather than decorative.**
* `e4a_toC_signOf_mutant_is_false` — refutes *"the ℤ sign bridge extends off the units"*.
  Off the units the complexified value is `0`, which is neither `1` nor `−1`.
* `e4a_gaussSum_real_of_primitive` — refutes *"reality needs primitivity"*. It is the
  brief's literal `hprim`-carrying signature, kept ONLY so the requested name exists;
  **its proof discards `hprim` and calls the weaker `e4a_gaussSum_real`.** The evidence
  is the proof, not the statement.
* `e4a_gaussSum_odd_re_zero` — refutes nothing; a **free companion fact**: at an ODD
  quadratic χ, τ is purely IMAGINARY. It belongs to the odd mirror and is here because it
  costs nothing and E6 will want it.
* `e4a_gaussSum_odd_inv_addChar` — the odd-parity engine the two odd results run on.
* `e4a_toC_vanishes_off_units` — the positive fact the sign-bridge control is stated against.
-/
import Salt.MR.EvenChiEta

namespace Salt.MR

open scoped ComplexOrder

section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

theorem e4a_descent_needs_integrality :
    ¬ ∃ z : ℤ, algebraMap ℤ ℚ z = (1/2 : ℚ) + (1/2 : ℚ)⁻¹ := by
  rintro ⟨z, hz⟩
  rw [show ((1:ℚ)/2) + ((1:ℚ)/2)⁻¹ = 5/2 by norm_num] at hz
  have : (z : ℚ) = 5/2 := by simpa using hz
  have h2 : (2 : ℚ) * z = 5 := by field_simp at this; linarith
  have : (2 * z : ℤ) = 5 := by exact_mod_cast h2
  omega

/-- The OTHER arm, so the control discriminates: the SAME shape at an `x` that IS integral
has its conclusion satisfied — `x = 1` gives `1 + 1 = 2 ∈ ℤ`. -/
theorem e4a_descent_holds_when_integral :
    ∃ z : ℤ, algebraMap ℤ ℚ z = (1 : ℚ) + (1 : ℚ)⁻¹ :=
  ⟨2, by norm_num⟩

#print axioms e4a_descent_needs_integrality
#print axioms e4a_descent_holds_when_integral

/-! ## PROBE 35 — ⛔ A SEVENTH GAP, CAUGHT FORWARD: the χ-WEIGHTED real↔algebraic bridge

Ran the forward control on the piece that is NOT mine — the `DirichletCharacter` statement
assembly.  Its η is the **REAL** sine product with ℤ exponents; my route's η is
**ALGEBRAIC**, in `𝓞_K`.  What connects them?

`e4a_step3_sin_bridge` is a **single-factor NORM** identity (`‖1 − ζ^a‖ = 2 sin(πa/q)`).
The assembly needs it **through a zpow-weighted PRODUCT**, and nothing here lifts it.
⇒ Seventh dangling interface, and the second caught before it could bite.

The lift is general: the norm is multiplicative, so it passes through both the product and
the ℤ-power.  Stated for an arbitrary index type over ℂ. -/

/-- The brief's literal signature, with `hprim` present.  It is UNUSED — kept only so the
name math asked for exists with the shape math asked for. -/
theorem e4a_gaussSum_real_of_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (_hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).im = 0 :=
  e4a_gaussSum_real χ heven hquad

/-! ### MUTATION CONTROL

The mutant flips ONE hypothesis: `χ (-1) = 1` ↦ `χ (-1) = -1` (even ↦ odd), conclusion
unchanged.  The two theorems below show the mutant is **FALSE**, not merely unreachable:
at an odd quadratic χ the same conjugation route yields `star τ = -τ`, i.e. `τ.re = 0`,
and `τ ≠ 0` at primitive χ (`Salt.LS.gaussSum_ne_zero`), so `τ.im ≠ 0` — the exact
NEGATION of the mutated conclusion.  (Companion file `ScratchE4aTauRealMUT-exec.lean`
runs the good proof script against the mutated hypothesis and gets a nonzero exit.) -/

/-- ODD companion: at `χ (-1) = -1`, inverting the additive character NEGATES the sum. -/
theorem e4a_gaussSum_odd_inv_addChar {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hodd : χ (-1) = -1) :
    gaussSum χ ψ⁻¹ = -gaussSum χ ψ := by
  have key := gaussSum_mulShift χ ψ (-1)
  rw [Units.coe_neg_one, hodd, neg_one_mul] at key
  rw [AddChar.inv_mulShift, ← neg_eq_iff_eq_neg]
  exact key

/-- At an ODD quadratic χ the Gauss sum is purely IMAGINARY: `τ.re = 0`. -/
theorem e4a_gaussSum_odd_re_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hodd : χ (-1) = -1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).re = 0 := by
  have h : star (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ))
      = -gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
    rw [star_gaussSum_eq, hquad.inv, e4a_gaussSum_odd_inv_addChar χ _ hodd]
  have hre := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hre
  linarith

/-- **THE FALSIFIER.**  The mutated statement (`heven` ↦ `hodd`, conclusion `τ.im = 0`)
is FALSE at every odd quadratic PRIMITIVE χ: its conclusion's negation is a theorem. -/
theorem e4a_gaussSum_mutant_is_false {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hodd : χ (-1) = -1) (hquad : χ.IsQuadratic) :
    (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).im ≠ 0 := by
  intro him
  refine Salt.LS.gaussSum_ne_zero χ hprim (Complex.ext ?_ ?_)
  · simpa using e4a_gaussSum_odd_re_zero χ hodd hquad
  · simpa using him


#print axioms e4a_gaussSum_even_inv_addChar
#print axioms e4a_gaussSum_real
#print axioms e4a_gaussSum_eq_real
#print axioms e4a_gaussSum_real_of_primitive
#print axioms e4a_gaussSum_odd_inv_addChar
#print axioms e4a_gaussSum_odd_re_zero
#print axioms e4a_gaussSum_mutant_is_false

/-! ############################################################################
## ⭐ GAP B CLOSED — THE ℝ→ℂ RING BRIDGE  (helm-ruled 08/19: ℝ-UP)

The analytic half of E5a's middle is stated at `DirichletCharacter ℂ`
(`LFunction_one_even_fourier`, `e4a_gaussSum_real`); the arithmetic half — the whole
nine-declaration `e4a_signOf` bridge and `e4a_char_vanishes_off_units` — is stated at
`DirichletCharacter ℝ`.  Nothing joined them.

DIRECTION, RULED BY THE HELM AND NOT CHOSEN HERE: push the ℝ side UP.  It is
constructive and cheap (`MulChar.ringHomComp`); pulling the ℂ side DOWN would need an
INVERSE of `ringHomComp` — a ℂ-valued quadratic χ does take values in `{0,±1} ⊆ ℝ`, but
exhibiting its real avatar is work, not a coercion.

⚠️ THIS SECTION IS PROOF-INTERNAL ARCHITECTURE ONLY.  It states nothing about E4a's
  theorem and adds no hypothesis to it.  The `hprim` question — whether the assembled
statement carries `(hprim : χ.IsPrimitive)` — is at the Captain's desk and is NOT
touched here; every lemma below is silent about primitivity.
############################################################################ -/

/-- The complexified character still vanishes off the units. -/
theorem e4a_toC_vanishes_off_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    {a : ℕ} (hncop : ¬ Nat.Coprime a q) : e4a_toC χ (a : ZMod q) = 0 := by
  rw [e4a_toC_apply, e4a_char_vanishes_off_units χ hncop, Complex.ofReal_zero]

theorem e4a_toC_signOf_mutant_is_false {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    {a : ZMod q} (hnu : ¬ IsUnit a) (z : ℤ) (hz : z = 1 ∨ z = -1) :
    e4a_toC χ a ≠ ((z : ℤ) : ℂ) := by
  rw [e4a_toC_apply, MulChar.map_nonunit χ hnu, Complex.ofReal_zero]
  rcases hz with rfl | rfl <;> norm_num


#print axioms e4a_toC_apply
#print axioms e4a_toC_isQuadratic
#print axioms e4a_toC_even
#print axioms e4a_toC_ne_one
#print axioms e4a_toC_eq_signOf
#print axioms e4a_toC_vanishes_off_units
#print axioms e4a_sum_units_of_vanishing
#print axioms e4a_toC_sum_eq_signOf_sum
#print axioms e4a_toC_signOf_mutant_is_false

/-! ### ⭐⭐ INTERFACE WITNESS — THE JOIN CLOSES, AND IT IS CHECKABLE

NOT a new mathematical fact.  It CHAINS E3's Fourier identity (stated at `DirichletCharacter
ℂ`) through the ring bridge and exhibits the ℤ-coefficient, units-indexed form of its
right-hand side — the exact shape `e4a_sum_clog_re` consumes.

WHY IT EXISTS AS A THEOREM RATHER THAN A REMARK: this file's own record is nine dangling
interfaces in one day, every one of them two green pieces whose join nobody had stated, and
NONE catchable by a build.  THE KERNEL CHECKS THEOREMS, NOT THAT THEY COMPOSE.  So the
composition is written down and handed to the kernel.

⚠️ PRIMITIVITY IS TAKEN AT THE COMPLEXIFIED CHARACTER AND IS *PASSED THROUGH*, NOT PROVED
TO TRANSPORT and NOT ADDED TO ANY STATEMENT.  It is piece (1)'s own hypothesis; whether the
assembled E4a statement carries `hprim` is at the Captain's desk and is untouched here. -/

end


end Salt.MR
