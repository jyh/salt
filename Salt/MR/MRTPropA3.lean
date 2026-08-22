/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# MRT Proposition A.3 — the statement (`hMsup`'s producer)

Transcribed from `docs/sources/1503.05121v3.pdf`, Appendix A, read from the PDF.

> **Proposition A.3.** Let `f` be a 1-bounded multiplicative function. Let `S` be
> as above with `η ∈ (0, 1/6)` and let `F(s) = Σ_{X≤n≤2X, n∈S} f(n)/nˢ`.
> Then, for any `T ≥ 1`,
> `∫_{−T}^{T} |F(1+it)|² dt ≪ (T/(X/Q₁) + 1)·[ (log Q₁)^{1/3}/P₁^{1/6−η}
>    + M(f;X)/exp(M(f;X)) + 1/(log X)^{1/50} ]`

This is the producer of `lemma14_shortInterval_meansq`'s surviving hypothesis
`hMsup`; the deduction is proved in `MRTPropA3Bridge.lean`
(`hMsup_of_propA3_shape`), so stating A.3 closes the naming of that chain.

⭐ **`F(1 + it)` is this corpus's `dpolyA`** (`Lemma14Taylor.lean:283`), so the
conclusion below is written with `dpolyA` rather than a fresh definition — the
producer and the consumer are then the SAME Lean object, not two objects a
comment claims are equal.

## `S` is stated against the ABSTRACT band conditions, not Definition 2.1

⛔ A correction to this seat's own earlier reading. MRT define the appendix's `S`
by the three conditions below — `Q₁ ≤ exp(√(log X₀))`, (A.1), (A.2) — and then
remark that *Definition 2.1's* sequence **"can be verified to obey the above
estimates"** given a side condition. ⇒ **Definition 2.1 is an EXAMPLE satisfying
the conditions, not the definition of the appendix's `S`.** Stating A.3 against
Definition 2.1 would couple it to one witness and silently narrow the statement.

⭐ **And membership is the corpus's landed `MemS`** (`Sec9Glue.lean:118`):
MRT's *"at least one prime factor in each `[Pⱼ, Qⱼ]` for `j ≤ J`"* is
`∀ j ∈ Icc 1 J, 1 ≤ blockOmega (Pseq j) (Qseq j) n`, verbatim.

⚠️ **NON-VACUITY IS OWED**, as for `MRTThmA1`: the Bochner integral is `0` on a
non-integrable integrand.  Here it is *cheap* — `dpolyA` is continuous on a
positive `s0`, and `MRTPropA3Bridge` already derives that integrability — but it
must be discharged by whoever proves A.3, not assumed by whoever uses it.

Nothing in this file proves A.3 and nothing assumes it.
-/
import Mathlib
import Salt.MR.MRTThmA1
import Salt.MR.Sec9Glue
import Salt.MR.Lemma14Taylor

namespace Salt.MR

open scoped BigOperators

/-- **The appendix's band conditions** (`1503.05121v3`, Appendix A, p. 21):
the `Q₁` cap, (A.1) "not too far", and (A.2) "not too close". -/
def MRTBands (X₀ η : ℝ) (Pseq Qseq : ℕ → ℕ) : Prop :=
  ((Qseq 1 : ℝ) ≤ Real.exp (Real.sqrt (Real.log X₀)))
  ∧ (∀ j : ℕ, 2 ≤ j →
      Real.log (Real.log (Qseq j)) / (Real.log (Pseq (j - 1)) - 1)
        ≤ η / (4 * (j : ℝ) ^ 2))
  ∧ (∀ j : ℕ, 2 ≤ j →
      8 * Real.log (Qseq (j - 1)) + 16 * Real.log j
        ≤ (η / (j : ℝ) ^ 2) * Real.log (Pseq j))

/-- **`J` is the largest index with `Q_J ≤ exp((log X₀)^{1/2})`.** -/
def MRTBandCount (X₀ : ℝ) (Qseq : ℕ → ℕ) (J : ℕ) : Prop :=
  ((Qseq J : ℝ) ≤ Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2)))
  ∧ ∀ j : ℕ, J < j → ¬ ((Qseq j : ℝ) ≤ Real.exp ((Real.log X₀) ^ ((1 : ℝ) / 2)))

/-- **MRT Proposition A.3 at an explicit constant `C`.**  The `≪` is discharged
as a single absolute `C`, uniform in every parameter. -/
def MRTPropA3 (C : ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ (X X₀ η : ℝ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (S : Finset ℕ),
      0 < η → η < 1 / 6 →
      Real.sqrt X ≤ X₀ → X₀ ≤ X →
      MRTBands X₀ η Pseq Qseq → MRTBandCount X₀ Qseq J →
      (∀ n : ℕ, n ∈ S ↔ (X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X ∧ MemS Pseq Qseq J n)) →
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in (-T)..T, ‖dpolyA f S t‖ ^ 2)
        ≤ C * (T / (X / (Qseq 1 : ℝ)) + 1)
            * ((Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
                + mrtM f X / Real.exp (mrtM f X)
                + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-- **The producer as a `Prop`**: `∃ C > 0`, A.3 holds at `C`.  A statement, not
a theorem — nothing proves it and nothing assumes it. -/
def MRTPropA3Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTPropA3 C

end Salt.MR
