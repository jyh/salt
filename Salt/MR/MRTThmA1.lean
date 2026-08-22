/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# MRT Theorem A.1 — the statement (the reduced spine's PRIMARY)

Transcribed from `docs/sources/1503.05121v3.pdf`, Appendix A, **read from the
PDF itself** rather than from any summary (including this repo's own
`docs/sources/mrt_extract.md`).  MRT's text, verbatim:

> **Theorem A.1.** Let `f` be a 1-bounded multiplicative function and let
> `M(f; X)` be as in (1.6).  Then, for `X ≥ h ≥ 10`,
> `(1/X) ∫_X^{2X} |(1/h) Σ_{x≤n≤x+h} f(n)|² dx ≪ exp(−M(f;X))·M(f;X)
>    + (loglog h)²/(log h) + 1/(log X)^{1/50}`

## Three things the source settles, all of which the campaign had open

1. **`M(f; X)` is (1.6)'s — MRT write "as in (1.6)" in the statement itself.**
   (1.6) carries NO character.  This confirms the ratified `M`-vs-`M(Q)`
   separation from the source rather than from our re-derivation, and it is why
   `Salt.MR.lambda_nonpret`'s `χ = 1` shape is the SPECIFIED shape.
2. ⭐ **The `x`-integral runs over `[X, 2X]` and is the AVERAGE over the
   location `x`; the short interval has length `h`.**  This is the source
   confirmation of the refutation recorded in the scoping brief's erratum: the
   `[X,2X]` in A.1 is NOT the range of a typical-factorization set.
3. ⭐ **The middle error term carries `(loglog h)²` — SQUARED** — where Theorem
   1.7 carried `loglog h`.  Confirmed here so that nobody transcribes 1.7's
   shape into an A.1 proof.

⭐ **And a strengthening MRT record immediately after the statement, which is
worth having in view before anyone prices the proof:** *"The factor
`exp(−M(f;X))M(f;X)` can be replaced by `exp(−M(f;X))`, see the remark following
Proposition A.3."*  The form below is the WEAKER, as-stated one; that is
deliberate, since a door should be the weakest admissible statement.

## Multiplicativity is stated inline, on purpose

Mathlib's `IsMultiplicative` lives on `Nat.ArithmeticFunction`, so using it here
would force a `toArithmeticFunction` transport on a bare `f : ℕ → ℂ`.  Stated
over the object's own type there is nothing to transport, so the two defining
equations are written out directly.  (`IsMultiplicative` is named here so a
name-census of this corpus still finds this file.)

⚠️⚠️ **NON-VACUITY IS OWED, exactly as for `MRTProp24`.**  Lean's Bochner integral
is `0` on a non-integrable integrand, so **any eventual PROOF of `MRTThmA1` must
land integrability of `x ↦ ‖mrtShortMean f h x‖ ^ 2` on `[X, 2X]` first**, or the
bound is bought with `0 ≤ RHS`.  Nothing in this file proves `MRTThmA1` and
nothing assumes it.
-/
import Mathlib
import Salt.MR.MRTProp24

namespace Salt.MR

open scoped BigOperators

/-- **The short-interval mean `(1/h) Σ_{x ≤ n ≤ x+h} f(n)`** (MRT Theorem A.1).
The index set is the naturals in `[x, x+h]`; `mem_mrtShortWindow` proves that
reading is exact rather than assuming it. -/
noncomputable def mrtShortMean (f : ℕ → ℂ) (h x : ℝ) : ℂ :=
  (1 / (h : ℂ)) * ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n

/-- **Faithfulness of the index set, PROVED not asserted:** for `0 ≤ x` and
`0 ≤ h`, the naturals of `Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊` are exactly those with
`x ≤ n ≤ x + h`.  So the reals → naturals move in `mrtShortMean` costs nothing. -/
theorem mem_mrtShortWindow {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (n : ℕ) :
    n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊ ↔ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h := by
  rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith)]

/-- **MRT Theorem A.1 at an explicit constant `C`** (`1503.05121v3`, Appendix A).
The `≪` is discharged as a single absolute `C`, uniform in `f`, `X` and `h`. -/
def MRTThmA1 (C : ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ X h : ℝ, 10 ≤ h → h ≤ X →
      (1 / X) * (∫ x in X..(2 * X), ‖mrtShortMean f h x‖ ^ 2)
        ≤ C * (Real.exp (-(mrtM f X)) * mrtM f X
              + (Real.log (Real.log h)) ^ 2 / Real.log h
              + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-- **The door as a `Prop`**: `∃ C > 0`, A.1 holds at `C`.  A statement, not a
theorem — nothing in this development proves it and nothing assumes it. -/
def MRTThmA1Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTThmA1 C

end Salt.MR
