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
import Salt.MR.CofactorSupplier
import Salt.MR.Lemma14Taylor
import Salt.MR.MVHilbertFinset
import Salt.Mertens.Third

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

/-- **THE AMBIENT HYPOTHESES OF MRT's APPENDIX A**, as one `Prop`, carried by `MRTPropA3`
below.

**ADOPTED BY CAPTAIN'S RULING, 2026-08-22 ~17:4x** (council; relayed by Sancho).  The ground
is FIDELITY TO THE SOURCE, not a weakening: MRT supply these ambiently in prose, which
transcribes into nothing —
* `Real.exp 1 ≤ X` — Theorem A.2's *"for all `X > X(η)` large enough"*;
* `T ≤ X / 2` — A.3's own opening sentence, *"we can assume `T ≤ X/2`"*;
* `2 ≤ Pseq 1` — the intervals of Definition 2.1.

*A displayed formula transcribes; a sentence of running prose does not.*  All three losses
were of the second kind, which is why the statement went vacuous in three separate ways —
`sifted_empty_at_one`, `memS_false_of_Qseq1_zero`, `mrtA3_first_term_of_Pseq1_zero` are the
witnesses, kept below, and `mrtA3_ambient_excludes_degeneracies` is the proof that these three
bounds shut all of them at once. -/
def MRTPropA3Ambient (X T : ℝ) (Pseq : ℕ → ℕ) : Prop :=
  Real.exp 1 ≤ X ∧ T ≤ X / 2 ∧ 2 ≤ Pseq 1

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
    ∀ T : ℝ, 1 ≤ T → MRTPropA3Ambient X T Pseq →
      (∫ t in (-T)..T, ‖dpolyA f S t‖ ^ 2)
        ≤ C * (T / (X / (Qseq 1 : ℝ)) + 1)
            * ((Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
                + mrtM f X / Real.exp (mrtM f X)
                + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-- **The producer as a `Prop`**: `∃ C > 0`, A.3 holds at `C`.  A statement, not
a theorem — nothing proves it and nothing assumes it.

✅ **RESOLVED 2026-08-22 10:0x — THE GUARD HOLDS, AND IT IS IN THE KERNEL:
`sifted_empty_at_one` (with `integral_dpolyA_eq_zero_of_empty`) proves that at
`X = 1` the sifted set `S` is EMPTY and A.3's left-hand side is `0`, so the
conclusion holds at every `C ≥ 0` — VACUOUSLY TRUE, NOT FALSE.  `MRTLemmaA4ii`'s
defect does NOT recur here.**  The dichotomy and the sense in which this guard is
*accidental rather than designed* are written out at the `X = 1` section below.

⭐⛔ **AND THE FLAG BELOW RECORDED THE VERY FACT THAT REFUTES IT.**  It observes
that *"`Qseq 1 = 1` kills the first term"* and counts that as HELPING a
counterexample, because it shrinks the right-hand side.  The same `Qseq 1 ≤ 1`
empties block 1, hence empties `S`, hence kills the LEFT-hand side outright — and
`0 ≤ RHS` is exactly what needed proving.  ***I had the decisive fact written down
and read it in the direction that favoured my hypothesis.***  The original
diagnosis is kept verbatim below, unedited, because the error is the lesson:

⚠️ **THE ORIGINAL FLAG, 2026-08-22 04:1x (SUPERSEDED, KEPT FOR THE RECORD):
`MRTLemmaA4ii` WAS FOUND FALSE FOR EXACTLY THIS REASON, SO THIS STATEMENT WAS
SUSPECTED OF CARRYING NO LARGENESS ON `X`.**  Its only size
hypotheses are `√X ≤ X₀ ≤ X`, which force `X ≥ 1` and nothing more, while MRT's
Appendix A runs under A.1's `X ≥ h ≥ 10` and A.2's *"for all `X > X(η)` large
enough"*.  At `X = 1` every bracket term can degenerate to `0` through Lean's junk
values — `(0:ℝ)^(1/50) = 0` so `1/(log X)^{1/50} = 0`; the primes `≤ 1` are empty so
`mrtM = 0` and `M/exp M = 0`; and `Qseq 1 = 1` kills the first term — while the LHS
integral of `‖dpolyA‖²` can be positive.

⛔ **THIS IS A CANDIDATE, NOT A WITNESS, AND THE DIFFERENCE IS THE POINT.**  A
counterexample must ALSO satisfy `MRTBands`' (A.1)/(A.2), and at `Qseq j = 2`,
`Pseq 1 = 2` the (A.1) ratio is `+1.19` against a required `≤ η/16 ≈ 0.0052`.  **I
have not constructed a consistent assignment, so I do not claim the statement is
false — only that its guard against the `A4ii` defect is unverified.**

✅ **AND THE CAPTAIN'S RULING OF 2026-08-22 ~17:4x SUPERSEDES THE WHOLE QUESTION.**
`MRTPropA3` now carries `MRTPropA3Ambient`, so `X = 1` is excluded BY HYPOTHESIS rather than
survived by accident.  This wrapper needs no structural change — it still reads
`∃ C > 0, MRTPropA3 C` — but the guard discussed above is no longer what protects the
statement; `mrtA3_ambient_excludes_degeneracies` is.  *The vacuity analysis is kept because
the reasoning, not the outcome, was the thing worth having.* -/
def MRTPropA3Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTPropA3 C

/-! ## A3-0 — `t₁` exists

MRT's A.3 proof says *"let `t₁` be **the value of `t` which attains the minimum**
in `M(f;X) = inf_{|t|≤X} 𝔻(f,n^{it};X)²`"*, and everything downstream — the whole
`T₀`/`T₁` dichotomy — is written in terms of `|t − t₁|`.

In Lean `mrtM` is an `sInf` over `ℝ`, so **attainment is not free**: it is
compactness of `[−X, X]` plus continuity of the map.  The paper's definite article
is doing that argument's work.

⭐ The idiom is the corpus's own — `IsCompact.exists_isMinOn`, as used at
`Salt/SW/ZetaInvShallow.lean:110` and `Salt/SW/ZetaZeroFree.lean:203`. -/

/-- `t ↦ 𝔻(f, n^{it}; X)²` is continuous: `pretDistSq` is a finite sum over the
primes `≤ X`, and each term depends on `t` only through `costwist`. -/
theorem continuous_pretDistSq_costwist (f : ℕ → ℂ) (X : ℝ) :
    Continuous (fun t : ℝ => pretDistSq f (costwist t) X) := by
  unfold pretDistSq costwist
  continuity

/-- **A3-0 — THE MINIMISER EXISTS.**  There is `t₁` with `|t₁| ≤ X` whose
pretentious distance to `f` realises `mrtM f X` exactly.  This is what MRT's
"the value of `t` which attains the minimum" asserts, and it is a theorem here
rather than a phrase. -/
theorem exists_min_pretDistSq (f : ℕ → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    ∃ t₁ : ℝ, |t₁| ≤ X ∧ pretDistSq f (costwist t₁) X = mrtM f X := by
  have hcont : Continuous (fun t : ℝ => pretDistSq f (costwist t) X) :=
    continuous_pretDistSq_costwist f X
  have hcompact : IsCompact (Set.Icc (-X) X) := isCompact_Icc
  have hne : (Set.Icc (-X) X).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨t₁, ht₁mem, ht₁min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have habs : |t₁| ≤ X := by
    rw [abs_le]; exact ⟨ht₁mem.1, ht₁mem.2⟩
  refine ⟨t₁, habs, ?_⟩
  have hlb : ∀ b ∈ {m : ℝ | ∃ t : ℝ, |t| ≤ X ∧ m = pretDistSq f (costwist t) X},
      pretDistSq f (costwist t₁) X ≤ b := by
    rintro b ⟨t, htX, rfl⟩
    have hmemt : t ∈ Set.Icc (-X) X := by
      rw [Set.mem_Icc]; rw [abs_le] at htX; exact ⟨htX.1, htX.2⟩
    exact ht₁min hmemt
  have hmem : pretDistSq f (costwist t₁) X
      ∈ {m : ℝ | ∃ t : ℝ, |t| ≤ X ∧ m = pretDistSq f (costwist t) X} := ⟨t₁, habs, rfl⟩
  unfold mrtM
  exact le_antisymm (le_csInf ⟨_, hmem⟩ hlb) (csInf_le ⟨_, hlb⟩ hmem)

/-! ## A3-2 — the `T₀` / `T₁` dichotomy

MRT's A.3 proof, verbatim: *"If `M(f;X) ≥ (1/8) log log X`, we write `T₁ := [−T,T]`
and `T₀ := ∅`, whereas otherwise we write
`T₀ := {|t| ≤ T : |t − t₁| ≤ (log X)^{1/16}}`,
`T₁ := {|t| ≤ T : |t − t₁| > (log X)^{1/16}}`."*

The content is that **both branches partition `{|t| ≤ T}`** — the proof handles
`T₁` first and `T₀` second, and that is only a proof of the whole range if the
two pieces cover it and do not overlap.  Both facts are proved below, uniformly
in the branch.

*This node was gated on A3-0: every set here is written in terms of `|t − t₁|`,
so it could not be stated until `t₁` was known to exist.* -/

/-- **MRT's `T₀`** — empty in the high-`M` branch, the near-`t₁` window otherwise. -/
noncomputable def mrtT0 (M t₁ X T : ℝ) : Set ℝ :=
  if (1 / 8) * Real.log (Real.log X) ≤ M then ∅
  else {t : ℝ | |t| ≤ T ∧ |t - t₁| ≤ (Real.log X) ^ ((1 : ℝ) / 16)}

/-- **MRT's `T₁`** — all of `[−T,T]` in the high-`M` branch, the far-from-`t₁`
part otherwise. -/
noncomputable def mrtT1 (M t₁ X T : ℝ) : Set ℝ :=
  if (1 / 8) * Real.log (Real.log X) ≤ M then {t : ℝ | |t| ≤ T}
  else {t : ℝ | |t| ≤ T ∧ (Real.log X) ^ ((1 : ℝ) / 16) < |t - t₁|}

/-- **A3-2 (i) — the two pieces COVER `{|t| ≤ T}`, in both branches.** -/
theorem mrtT0_union_mrtT1 (M t₁ X T : ℝ) :
    mrtT0 M t₁ X T ∪ mrtT1 M t₁ X T = {t : ℝ | |t| ≤ T} := by
  unfold mrtT0 mrtT1
  split_ifs with h
  · simp
  · ext t
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    · intro h1
      by_cases hc : |t - t₁| ≤ (Real.log X) ^ ((1 : ℝ) / 16)
      · exact Or.inl ⟨h1, hc⟩
      · exact Or.inr ⟨h1, not_le.mp hc⟩

/-- **A3-2 (ii) — the two pieces are DISJOINT, in both branches.** -/
theorem mrtT0_disjoint_mrtT1 (M t₁ X T : ℝ) :
    Disjoint (mrtT0 M t₁ X T) (mrtT1 M t₁ X T) := by
  unfold mrtT0 mrtT1
  split_ifs with h
  · simp
  · rw [Set.disjoint_left]
    rintro t ⟨_, h0⟩ ⟨_, h1⟩
    linarith

/-! ## A3-3 — MRT Lemma A.4, stated

From `1503.05121v3`, Appendix A, verbatim:

> **Lemma A.4.** Let `𝒥 ⊆ {1,…,J}` and `|t| ≤ X`.
> **(i)** One has `𝔻(f g_𝒥, p^{it}; X)² ≥ ½ 𝔻(f, p^{it}; X)²`.
> **(ii)** If `M(f;X) ≥ (1/8) log log X` or `|t − t₁| > (log X)^{1/16}/2`, then
> `𝔻(f g_𝒥, p^{it}; X)² ≥ (1/6 − 1/(3π) − ε) log log X` for any `ε > 0`.

⭐ Both are stated against the corpus's own `pretDistSq`, `costwist` and `gJ`, so
the twisted function `f·g_𝒥` is the same Lean object A.6's inclusion–exclusion
(`lemma5`) already sums over.

⚠️ Statements only — nothing proves them and nothing assumes them.  A.5, A.6 and
A.7 are **not** stated here: their conclusions are still only partially read, and
stating a display I have not seen whole is the error this seat spent the night
recovering from. -/

/-- **MRT Lemma A.4 (i)** — twisting by `g_𝒥` costs at most a factor `2`. -/
def MRTLemmaA4i : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → |t| ≤ X →
      (1 / 2) * pretDistSq f (costwist t) X
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-- **MRT Lemma A.4 (ii)** — off the `t₁` window, or at large quality, the
twisted distance is bounded below by `(1/6 − 1/(3π) − ε)·loglog X`.

⛔⛔ **`Real.exp 1 ≤ X` IS CARRIED BECAUSE WITHOUT IT THE STATEMENT IS FALSE, AND
THERE IS A WITNESS.**  My first transcription omitted it, lifting MRT's display out
of the ambient largeness their Appendix A runs under (A.1's `X ≥ h ≥ 10`, A.2's
*"for all `X > X(η)` large enough"*).  With `ε` unbounded above, the constant
`1/6 − 1/(3π) − ε` goes **negative** past `ε > 0.060563`, and `loglog X` is
**negative** for `1 < X < e`, so their product is **positive** while the RHS is a
sum over an **empty** set of primes:

    X = 1.5,  ε = 1,  ANY f, 𝒥, t
      loglog X          = −0.902720            (negative)
      1/6 − 1/(3π) − ε  = −0.939437            (negative)
      LHS               = +0.848049            (positive)
      RHS = pretDistSq … 1.5 : ⌊1.5⌋₊ = 1, primes in range 2 : NONE  ⇒ 0
      ⇒ 0.848049 > 0.  FALSE.

🔑 This is **not** a hypothesis added to make a route go through.  The proof's
need for `exp 1 ≤ X` was **the statement telling the truth about itself**: when a
proof wants a hypothesis its statement lacks, the first question is not *"how do I
close the gap"* but ***"is the statement true without it?"*** -/
def MRTLemmaA4ii : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X → 0 < ε →
    ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
      ∨ (Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁|) →
      (1 / 6 - 1 / (3 * Real.pi) - ε) * Real.log (Real.log X)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-- **THE CONSTANT IN (A.3) IS POSITIVE.**  `1/6 − 1/(3π) > 0`, i.e. `π > 2`.

*This is the small-end check on A.4 (ii): were the constant `≤ 0`, the bound
would be vacuous for every `ε` and the lemma would carry no content at all.* -/
theorem mrtA4_constant_pos : 0 < 1 / 6 - 1 / (3 * Real.pi) := by
  have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  -- `div_lt_div_iff` is gone from this mathlib; `one_div_lt_one_div_of_lt` is the
  -- sibling of `one_div_le_one_div_of_le`, which the corpus already uses.
  have h6 : (6 : ℝ) < 3 * Real.pi := by linarith
  have hinv : 1 / (3 * Real.pi) < 1 / 6 :=
    one_div_lt_one_div_of_lt (by norm_num) h6
  linarith

/-! ## A.5's `ρ`-margin — the thinnest thing in Appendix A

Lemma A.5 names `ρ := 1/6 − 1/(3π) − ε` and MRT remark that *"replacing `1/48` by
`ρ/3 > 1/50` in the definitions of `P`, `Q` and `H` … we still obtain"* their
bound.  **That inequality is asserted, not evaluated, and it is very tight:**

```
   1/6 − 1/(3π)          = 0.060563371
   (1/6 − 1/(3π))/3      = 0.020187790
   1/50                  = 0.020000000
   MARGIN                = 0.000187790          ⇐ 0.94% of 1/50
   ⇒ ρ/3 > 1/50 forces   ε < 0.000563371
```

⭐⭐ **And it needs `π > 3.125`.**  `1/6 − 1/(3π) > 3/50` unfolds to `24π > 75`.
***`Real.pi_gt_three` is INSUFFICIENT here*** — 3 < 3.125 — so this needs
`Real.pi_gt_d6` (the corpus's own sharp-π idiom, 7 uses), where
`mrtA4_constant_pos` — the same constant, one theorem above — needed only
`π > 2`.  **Two facts about one constant with completely
different `π`-requirements, and nothing on the page distinguishes them.** -/

/-- **A.5's MARGIN.**  `3/50 < 1/6 − 1/(3π)`, i.e. `24π > 75`, i.e. `π > 3.125`.
This is what makes MRT's `ρ/3 > 1/50` true at all, and it needs a `π` bound
sharper than `Real.pi_gt_three`. -/
theorem mrtA5_rho_margin : 3 / 50 < 1 / 6 - 1 / (3 * Real.pi) := by
  have hpi := Real.pi_gt_d6
  have hlt : (75 : ℝ) / 8 < 3 * Real.pi := by linarith
  have hkey : 1 / (3 * Real.pi) < 8 / 75 := by
    calc 1 / (3 * Real.pi) < 1 / ((75 : ℝ) / 8) :=
          one_div_lt_one_div_of_lt (by norm_num) hlt
      _ = 8 / 75 := by norm_num
  linarith

/-- **THE `ε`-CEILING A.5 IMPLIES.**  MRT's `ρ/3 > 1/50` holds exactly when
`ε < 1/6 − 1/(3π) − 3/50 ≈ 5.634 × 10⁻⁴`.  *The paper carries `ε > 0` as "any
`ε`"; A.5's own remark silently bounds it.*

⭐ *Note `0 < ε` is carried because MRT carry it, and is **not used** — the
consequence follows from the ceiling alone.  Recorded rather than deleted: a
hypothesis the paper states and the proof does not need is worth being able to
see.* -/
theorem mrtA5_epsilon_ceiling {ε : ℝ} (_hε0 : 0 < ε)
    (hεlt : ε < 1 / 6 - 1 / (3 * Real.pi) - 3 / 50) :
    1 / 50 < (1 / 6 - 1 / (3 * Real.pi) - ε) / 3 := by
  linarith

/-! ## A.6 and A.7, stated — read WHOLE, via `pdftotext -layout`

The earlier extraction broke MRT's displayed equations across lines and I refused
to state these on the fragments.  `pdftotext -layout` preserves the two-dimensional
layout and gives both displays entire, so they are stated here.

⚠️ **ONE AMBIGUITY IN THE SOURCE, FLAGGED RATHER THAN SILENTLY RESOLVED.**  A.7's
binder reads *"Let `t ∈ T₀` and **`I ⊆ {1,…,J}`**"* while its body sums `g_𝒥`.
Measured: **`I ⊆ {1,…,J}` occurs exactly once in the whole appendix — at that
binder — and `g_I` occurs nowhere.**  So either the binder is a typo for `𝒥`, or
the extraction rendered one symbol two ways.  *Both readings give the same
mathematical content — one subset of `{1,…,J}`, and the sums taken over it — so
it is stated with a single index and the discrepancy is recorded here rather than
hidden in a choice.* -/

/-- **MRT Lemma A.6** — for `t ∈ T₀`, the signed subset sum is small.
The inner object is exactly what `Salt.MR.lemma5` already produces. -/
def MRTLemmaA6 (C : ℝ) : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (X t t₁ : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → 0 < X → t ∈ mrtT0 (mrtM f X) t₁ X X →
      ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (-1 : ℂ) ^ 𝒥.card
            * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n‖
        ≤ C * (Real.exp (-(1 / 2) * mrtM f X) / (1 + |t - t₁|)
                + (Real.log X) ^ (-(1 : ℝ) / 16))

/-- **MRT Lemma A.7 — the renormalization.**  For `t ∈ T₀`, the `t`-twisted sum
equals `X^{i(t−t₁)}/(1 + i(t−t₁))` times the `t₁`-twisted sum, up to
`O(X/(log X)^{1/10})`.  *This is the consumer of `mrtT0`'s radius: the whole
point of `|t − t₁| ≤ (log X)^{1/16}` is that this shift is cheap.* -/
def MRTLemmaA7 (C : ℝ) : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → 0 < X → t ∈ mrtT0 (mrtM f X) t₁ X X →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n)
          - (Complex.exp ((((t - t₁ : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
              / (1 + (((t - t₁ : ℝ) : ℂ)) * Complex.I))
            * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t₁) n‖
        ≤ C * X / (Real.log X) ^ ((1 : ℝ) / 10)

/-- **A.6 as a statement** — `∃ C > 0`.  *`MRTLemmaA6` is a PREDICATE ON `C`, not a
claim; without this wrapper a reader can mistake `MRTLemmaA6 C` for the lemma and
be asserting it for a `C` nobody chose.  `MRTThmA1Statement` and
`MRTPropA3Statement` had this from the start; A.6 and A.7 did not, and the
asymmetry is the kind that invites exactly that misuse.* -/
def MRTLemmaA6Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTLemmaA6 C

/-- **A.7 as a statement** — `∃ C > 0`.  See `MRTLemmaA6Statement`. -/
def MRTLemmaA7Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTLemmaA7 C

/-! ## A3-3 (i) — PROVED

MRT prove A.4(i) by expanding `2𝔻²(f g_𝒥, ·)` into three sums and arranging that
the loss `Σ(1 − g_𝒥(p))/p` appears **twice with opposite signs**, cancelling.

⭐ In Lean the same content is cheaper **pointwise**: `g_𝒥` is a `{0,1}` indicator,
so a case split on it does at each prime what the decomposition does uniformly.

    g_𝒥(p) = 1 :  need  (1 − A)/2 ≤ 1 − A     ⟸  A ≤ 1
    g_𝒥(p) = 0 :  need  (1 − A)/2 ≤ 1         ⟸  A ≥ −1

with `A := Re(f(p)·conj(costwist t p))` and `|A| ≤ 1` from `‖f‖ ≤ 1`, `‖costwist‖ ≤ 1`.
*The cancellation MRT arrange globally is, per prime, just the two ends of `|A| ≤ 1`.* -/

/-- **MRT Lemma A.4 (i), PROVED.**  Twisting by the `{0,1}` indicator `g_𝒥` costs
at most a factor `2` in the pretentious distance. -/
theorem mrtA4i_holds (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    (1 / 2) * pretDistSq f (costwist t) X
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  unfold pretDistSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  dsimp only
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hcn : ‖(starRingEnd ℂ) (costwist t p)‖ ≤ 1 := by
    simpa using norm_costwist_le t p
  have hA : |(f p * (starRingEnd ℂ) (costwist t p)).re| ≤ 1 := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul]
    nlinarith [hf p, hcn, norm_nonneg (f p),
      norm_nonneg ((starRingEnd ℂ) (costwist t p))]
  have hAle : (f p * (starRingEnd ℂ) (costwist t p)).re ≤ 1 := le_trans (le_abs_self _) hA
  have hAge : -1 ≤ (f p * (starRingEnd ℂ) (costwist t p)).re := neg_le_of_abs_le hA
  by_cases hg : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) p = 0
  · rw [show gJ 𝒥 Pseq Qseq p = 1 from by simp only [gJ, if_pos hg]]
    have hone : (f p * 1 * (starRingEnd ℂ) (costwist t p)).re
        = (f p * (starRingEnd ℂ) (costwist t p)).re := by rw [mul_one]
    rw [hone]
    have : (1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / 2
        ≤ 1 - (f p * (starRingEnd ℂ) (costwist t p)).re := by linarith
    calc 1 / 2 * ((1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / (p : ℝ))
        = ((1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / 2) / (p : ℝ) := by ring
      _ ≤ (1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / (p : ℝ) := by gcongr
  · rw [show gJ 𝒥 Pseq Qseq p = 0 from by simp only [gJ, if_neg hg]]
    have hzero : (f p * 0 * (starRingEnd ℂ) (costwist t p)).re = 0 := by simp
    rw [hzero]
    have : (1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / 2 ≤ 1 - 0 := by linarith
    calc 1 / 2 * ((1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / (p : ℝ))
        = ((1 - (f p * (starRingEnd ℂ) (costwist t p)).re) / 2) / (p : ℝ) := by ring
      _ ≤ (1 - 0) / (p : ℝ) := by gcongr

/-- **`MRTLemmaA4i` IS DISCHARGED** — the `Prop` stated earlier is now a theorem.

⭐ Note the producer needs **one hypothesis fewer** than the `Prop` asks: `mrtA4i_holds`
never uses `|t| ≤ X`, so it is **strictly stronger** than `MRTLemmaA4i`.  Recorded
because a consumer wanting the weaker form should know the stronger one exists —
and because this is the second hypothesis tonight that a statement carries and its
proof does not need (cf. `mrtA5_epsilon_ceiling`'s `0 < ε`). -/
theorem mrtLemmaA4i_holds : MRTLemmaA4i := by
  intro f Pseq Qseq 𝒥 X t hf _htX
  exact mrtA4i_holds f Pseq Qseq 𝒥 X t hf

/-! ## A3-3 (ii), FIRST BRANCH — proved from (i)

MRT: *"Notice first that when `M(f;X) ≥ ⅛ log log X`, part (i) implies that,
whenever `|t| ≤ X`, we have `𝔻(f g_𝒥, p^{it}; X)² ≥ (1/16) log log X`, **which is
sufficient**."*

Two ingredients, both landed tonight: `mrtA4i_holds`, and the fact that `mrtM` is
an infimum so it lies below every admissible twist.

⭐ **"Which is sufficient" is a numeric claim and it is checked here:**
`1/6 − 1/(3π) = 0.060563 < 0.0625 = 1/16`, margin `0.001937`.  ⚠️ Note this needs
`π < 3.2` — an **UPPER** bound on `π` — where `mrtA4_constant_pos` needed `π > 2`
and `mrtA5_rho_margin` needed `π > 3.125`.  *Three facts about one constant,
requiring bounds on `π` from both sides.*

⛔ The **second** branch (`M < ⅛loglog X` and `|t − t₁| > (log X)^{1/16}/2`) is the
real analysis — it introduces `Y = exp((log X)^{2/3+ε})` and MRT's display (A.4) —
and is **not** attempted here. -/

/-- `mrtM` is an infimum, so it lies below the distance at every admissible twist. -/
theorem mrtM_le (f : ℕ → ℂ) {X t : ℝ} (hX : 0 ≤ X) (htX : |t| ≤ X) :
    mrtM f X ≤ pretDistSq f (costwist t) X := by
  have hcont := continuous_pretDistSq_costwist f X
  have hcompact : IsCompact (Set.Icc (-X) X) := isCompact_Icc
  have hne : (Set.Icc (-X) X).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨t₁, ht₁mem, ht₁min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have hbdd : BddBelow {m : ℝ | ∃ s : ℝ, |s| ≤ X ∧ m = pretDistSq f (costwist s) X} := by
    refine ⟨pretDistSq f (costwist t₁) X, ?_⟩
    rintro b ⟨s, hsX, rfl⟩
    exact ht₁min (by rw [Set.mem_Icc]; rw [abs_le] at hsX; exact ⟨hsX.1, hsX.2⟩)
  exact csInf_le hbdd ⟨t, htX, rfl⟩

/-- **`1/16` BEATS A.4(ii)'s TARGET CONSTANT** — this is MRT's *"which is
sufficient"*, evaluated.  Needs `π < 3.2`, an UPPER bound. -/
theorem mrtA4ii_sixteenth_suffices : 1 / 6 - 1 / (3 * Real.pi) < 1 / 16 := by
  have hpi : Real.pi < 3.2 := by linarith [Real.pi_lt_d2]
  have h3 : (0 : ℝ) < 3 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hkey : (5 : ℝ) / 48 < 1 / (3 * Real.pi) := by
    have : (3 : ℝ) * Real.pi < 48 / 5 := by linarith
    calc (5 : ℝ) / 48 = 1 / (48 / 5) := by norm_num
      _ < 1 / (3 * Real.pi) := one_div_lt_one_div_of_lt h3 this
  linarith

/-- **A.4(ii), HIGH-`M` BRANCH, PROVED.**  When `M(f;X) ≥ ⅛·loglog X`, part (i)
gives `𝔻²(f·g_𝒥, ·) ≥ (1/16)·loglog X` at every admissible twist. -/
theorem mrtA4ii_high_M (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hX : 0 ≤ X) (htX : |t| ≤ X)
    (hM : (1 / 8) * Real.log (Real.log X) ≤ mrtM f X) :
    (1 / 16) * Real.log (Real.log X)
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  have h1 := mrtA4i_holds f Pseq Qseq 𝒥 X t hf
  have h2 := mrtM_le f hX htX
  linarith

/-- **A.4(ii)'s HIGH-`M` BRANCH REACHES THE TARGET CONSTANT.**  Chaining
`mrtA4ii_high_M` with `mrtA4ii_sixteenth_suffices`: under `M(f;X) ≥ ⅛·loglog X`,
the twisted distance exceeds `(1/6 − 1/(3π) − ε)·loglog X`, which is exactly
`MRTLemmaA4ii`'s conclusion.

⚠️ `Real.exp 1 ≤ X` is needed and is **not** a technicality: it gives
`log X ≥ 1`, hence `loglog X ≥ 0`, and the constant comparison only transfers
across a **non-negative** multiplier.  *Comparing `c₁ < c₂` tells you nothing
about `c₁·L ≤ c₂·L` when `L` may be negative — and `loglog X` IS negative for
`1 < X < e`.* -/
theorem mrtA4ii_high_M_target (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ)
    (X t ε : ℝ) (hf : ∀ n, ‖f n‖ ≤ 1) (hXe : Real.exp 1 ≤ X) (htX : |t| ≤ X)
    (hε : 0 < ε) (hM : (1 / 8) * Real.log (Real.log X) ≤ mrtM f X) :
    (1 / 6 - 1 / (3 * Real.pi) - ε) * Real.log (Real.log X)
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hX0 : (0 : ℝ) ≤ X := hXpos.le
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]; exact hXe
  have hLL : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hbranch := mrtA4ii_high_M f Pseq Qseq 𝒥 X t hf hX0 htX hM
  have hconst := mrtA4ii_sixteenth_suffices
  nlinarith [hbranch, hconst, hLL, hε]

/-! ## The `X = 1` dichotomy — the helm's paper argument, run in the kernel

At `X = 1` the constraint `√X ≤ X₀ ≤ X` forces `X₀ = 1`, and **both** band bounds
collapse to `1` by different routes: `exp (√(log 1)) = exp 0 = 1` and
`exp ((log 1)^(1/2)) = exp 0 = 1` (the latter via `zero_rpow`, `1/2 ≠ 0`).
The dichotomy on `J` is then exhaustive:

* `J = 0` — `MRTBandCount`'s second clause at `j = 1` forces `Qseq 1 > 1`, while
  `MRTBands`' first clause forces `Qseq 1 ≤ 1`. **Inconsistent**: nothing to
  witness.
* `J ≥ 1` — `1 ∈ Icc 1 J`, so `MemS` demands a prime `p ∣ n` with `p ≤ Qseq 1 ≤ 1`.
  **No prime is `≤ 1`**, so `MemS` fails for every `n`, `S = ∅`, and both sides are
  `0`.

⭐⭐ **AND THE FINDING IS THAT THIS GUARD IS ACCIDENTAL, NOT DESIGNED.** It holds
only because `MemS` quantifies over `Icc 1 J` **starting at `j = 1`**, and
`MRTBands`' first clause pins **`Qseq 1` specifically** — while clauses 2 and 3 of
`MRTBands` start at `j = 2`.  ***Had `MemS` started at `j = 2`, the guard would
evaporate and `X = 1` would need explicit largeness exactly as `MRTLemmaA4ii`
did.***

🔑 **A.1 survives because it CARRIES `10 ≤ h ≤ X`.  A.3 survives because two
unrelated clauses happen to pull opposite ways on one index.  Those are not the
same kind of safe, and only the first kind survives editing.** -/

/-- No prime is `≤ 1`, so a block capped at `1` contains none. -/
theorem blockOmega_eq_zero_of_le_one {P Q n : ℕ} (hQ : Q ≤ 1) :
    blockOmega P Q n = 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

/-- **THE `J ≥ 1` BRANCH.**  With `Qseq 1 ≤ 1`, membership of `S` is impossible. -/
theorem memS_false_of_Qseq_one_le_one {Pseq Qseq : ℕ → ℕ} {J n : ℕ}
    (hJ : 1 ≤ J) (hQ : Qseq 1 ≤ 1) : ¬ MemS Pseq Qseq J n := by
  intro h
  have h1 := h 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hJ⟩)
  rw [blockOmega_eq_zero_of_le_one hQ] at h1
  omega

/-- **THE `J = 0` BRANCH.**  At `X₀ = 1` the two band conditions contradict:
`MRTBands` caps `Qseq 1` at `1`, `MRTBandCount` at `J = 0` forces it above `1`. -/
theorem mrtBands_bandCount_incompatible_at_one {η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hb : MRTBands 1 η Pseq Qseq) (hc : MRTBandCount 1 Qseq 0) : False := by
  have hcap : ((Qseq 1 : ℕ) : ℝ) ≤ 1 := by
    have := hb.1
    simpa [Real.log_one, Real.sqrt_zero, Real.exp_zero] using this
  have hgt := hc.2 1 (by norm_num)
  refine hgt ?_
  simpa [Real.log_one, Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0), Real.exp_zero] using hcap

/-- **THE DICHOTOMY, COMPOSED — AT `X = 1` THE SIFTED SET IS EMPTY.**  Both branches
were landed separately; this is the statement that consumes them, and it is the one
`MRTPropA3Statement`'s flag was actually asking for.  `J = 0` is inconsistent with the
two band conditions, and `J ≥ 1` empties `S` through `Qseq 1 ≤ 1`. -/
theorem sifted_empty_at_one {η : ℝ} {Pseq Qseq : ℕ → ℕ} {J : ℕ} {S : Finset ℕ}
    (hb : MRTBands 1 η Pseq Qseq) (hc : MRTBandCount 1 Qseq J)
    (hS : ∀ n : ℕ, n ∈ S ↔ ((1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * 1 ∧ MemS Pseq Qseq J n)) :
    S = ∅ := by
  have hQ : Qseq 1 ≤ 1 := by
    have h := hb.1
    rw [Real.log_one, Real.sqrt_zero, Real.exp_zero] at h
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos J with rfl | hJ1
  · exact (mrtBands_bandCount_incompatible_at_one hb hc).elim
  · refine Finset.eq_empty_iff_forall_notMem.mpr fun n hn => ?_
    exact memS_false_of_Qseq_one_le_one hJ1 hQ ((hS n).mp hn).2.2

/-- **AND THEREFORE A.3's LEFT-HAND SIDE VANISHES AT `X = 1`.**  With `S = ∅` the
Dirichlet polynomial is identically `0`, so the integral is `0` and the conclusion
holds at every `C ≥ 0` — *vacuously true, not false.* -/
theorem integral_dpolyA_eq_zero_of_empty (f : ℕ → ℂ) {S : Finset ℕ} (hS : S = ∅) (T : ℝ) :
    (∫ t in (-T)..T, ‖dpolyA f S t‖ ^ 2) = 0 := by
  subst hS
  simp [dpolyA]

/-! ## MRT's (A.4) — the ℂ-level half, salvaged

The full pointwise identity `costwist_conj_avg` hit its 3-attempt budget and is
flagged (queue row 15aa).  **But the wall was never the algebra — it is entirely
in the cast layer (`costwist` → `starRingEnd` → `ofReal`).**  These two lemmas are
the part that compiled, landed on their own so the remaining obstacle is exactly
the cast and nothing else.

*Salvaging the half that built is not a fourth attempt at the node; it is
shrinking what the node still needs.* -/

/-- `e^{zI} + e^{−zI} = 2·cos z`, from Euler in both directions. -/
theorem exp_add_exp_neg_eq_two_cos (z : ℂ) :
    Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)
      = 2 * Complex.cos z := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- **THE AVERAGING IDENTITY, IN `ℂ`.**  Two conjugate twists at `a` and `b`
combine into one at `(a+b)/2` scaled by `cos((a−b)/2)` — MRT's (A.4), with the
reals not yet involved. -/
theorem exp_neg_avg (a b : ℂ) :
    (Complex.exp (-a * Complex.I) + Complex.exp (-b * Complex.I)) / 2
      = Complex.exp (-((a + b) / 2) * Complex.I) * Complex.cos ((a - b) / 2) := by
  have h := exp_add_exp_neg_eq_two_cos ((a - b) / 2)
  have e1 : Complex.exp (-((a + b) / 2) * Complex.I)
        * Complex.exp (((a - b) / 2) * Complex.I) = Complex.exp (-b * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-((a + b) / 2) * Complex.I)
        * Complex.exp (-((a - b) / 2) * Complex.I) = Complex.exp (-a * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc (Complex.exp (-a * Complex.I) + Complex.exp (-b * Complex.I)) / 2
      = (Complex.exp (-((a + b) / 2) * Complex.I) * Complex.exp (-((a - b) / 2) * Complex.I)
          + Complex.exp (-((a + b) / 2) * Complex.I)
              * Complex.exp (((a - b) / 2) * Complex.I)) / 2 := by rw [e1, e2]
    _ = Complex.exp (-((a + b) / 2) * Complex.I)
          * ((Complex.exp (((a - b) / 2) * Complex.I)
              + Complex.exp (-((a - b) / 2) * Complex.I)) / 2) := by ring
    _ = Complex.exp (-((a + b) / 2) * Complex.I) * Complex.cos ((a - b) / 2) := by
        rw [h]; ring

/-- **MRT's (A.4), THE FULL POINTWISE IDENTITY — the flagged node, closed.**
`(n^{−it} + n^{−it₁})/2 = n^{−i(t+t₁)/2}·cos((t−t₁)·log n / 2)`, which is the step
turning MRT's two-point average into a single twist times a cosine (p. 23, the display
above (A.4)).

⚖️ **THIS IS A NEW ATTEMPT ON A NODE FLAGGED AT ITS 3-ATTEMPT BUDGET (queue row 15aa),
AND IT IS NOT A FOURTH GRIND.** What changed is the input: `exp_neg_avg` — the ℂ-level
half — landed at `af54accc` AFTER the flag, and the post-mortem claim that *"the wall is
the cast layer alone"* is precisely what this tests.  The whole proof below is four cast
equalities and one `exact`. -/
theorem costwist_conj_avg (t t₁ : ℝ) (n : ℕ) :
    (costwist (-t) n + costwist (-t₁) n) / 2
      = costwist (-((t + t₁) / 2)) n
        * Complex.cos (((t - t₁) * Real.log n / 2 : ℝ) : ℂ) := by
  unfold costwist
  have e1 : (((-t) * Real.log n : ℝ) : ℂ) = -((t * Real.log n : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (((-t₁) * Real.log n : ℝ) : ℂ) = -((t₁ * Real.log n : ℝ) : ℂ) := by
    push_cast; ring
  have e3 : ((-((t + t₁) / 2) * Real.log n : ℝ) : ℂ)
      = -((((t * Real.log n : ℝ) : ℂ) + ((t₁ * Real.log n : ℝ) : ℂ)) / 2) := by
    push_cast; ring
  have e4 : (((t - t₁) * Real.log n / 2 : ℝ) : ℂ)
      = (((t * Real.log n : ℝ) : ℂ) - ((t₁ * Real.log n : ℝ) : ℂ)) / 2 := by
    push_cast; ring
  rw [e1, e2, e3, e4]
  exact exp_neg_avg _ _

/-! ### ⚓ WHERE THIS FILE STANDS — 2026-08-22 19:3x (ORIENTATION, NOT LAW)

*Written under the Captain's **CLEAN HOUSE** ruling: archive stale prose as history, know where
we are now.  Measured, not recalled: **SIX section headers below mark a retraction or correction
of my own earlier claim** — a reader arriving cold should not have to reconstruct the state from
those six.  This block is orientation and is **not** a law; nothing below is superseded by it.*

⛔ *No total-line or total-section count is quoted here ON PURPOSE.  The first draft of this
block said "3124 lines and 23 sections" and was **stale the instant it landed** — the block is
inside the population it measures (3158 / 24 after writing it), and every future edit would
restale it.  **A measurement published inside the thing it measures is stale on arrival.**  The
`six` survives because it counts a property that this block does not have.*

**A.3 — the spine is complete to its boundary.**  `MRTPropA3` now CARRIES `MRTPropA3Ambient`
(Captain's ruling, 17:4x — `exp 1 ≤ X`, `T ≤ X/2`, `2 ≤ Pseq 1`), which shuts all three
degeneracies at once (`mrtA3_ambient_excludes_degeneracies`).  The one code consumer
(`mrtPropA3_in_bridge_shape`) moved with it; the aggregate builds.

**A.6 — vocabulary closed, strength OPEN.**  Its inner object **is** the sifted twisted sum
(`mrtA6_inner_eq_sifted`, `mrtA6_F_sifted`), so a supplier may feed A.3's `T₀` side without
meeting a powerset.  The exponent gap stands: landed Halász `1/(32e)` vs A.6's `1/16`.

**A.7 — residue (1) CLOSED, residue (2) OPEN and STRUCTURAL.**  The renormalisation itself is
landed in the corpus (`Renormalise.renormalise`, `:1004` — the Möbius-datum re-target was
already done, and it needs no `hyx`).  Residue (1), the summand match, is closed in
`renormalise`'s own coprime form (`gJ_f_costwist_mul_coprime`).  **Residue (2) needs an upper
bound on the UNTWISTED, NORM-form prime sum**; `mrtM` provably runs the wrong way
(`pretDistSq_one_le_sum_norm`), and at `f = λ` the route is vacuous by `(log x)^{2+1/10}`
(`sum_norm_one_sub_liouvilleC`).

**The door — walked to the corpus's own named residue.**  `M4RowMeanSq_L` (`M4RowLinear:991`),
labelled the wave's ⟦RESIDUE⟧ at its own definition site; of its two obstructions ⟦THE WALL⟧ is
REPAIRED (07-28) and ⟦THE CLASS PRICING⟧ is OPEN and design-tier.

⛔ **KNOWN DEBT, CARRIED DELIBERATELY:** six comparison-type controls hold hardcoded witnesses
and would degrade in silence; the flags on them are **document-guards, not executable ones**,
and fixing them edits A.6's/A.7's STATEMENTS (Fable/Captain tier).  `DoorRoadCompose.lean` is
**pedagogy, not contribution** — it re-derives road that `m4_hbd_of_live_L` already carries. -/

/-! ### FIVE LINKS DEEP, EVERY ONE POPULATED — AND THE REAL OPEN QUESTION IS NOT A MISSING LEMMA

Continuing the walk.  `DoorRowCarried` (the capstone producer's remaining input) is itself
populated: **8 exact producer-shaped sites**, including `M4T0Discharge.lean:738`,
`M4DoorClose.lean:{395,533,607}`, `M4Collapse.lean:216`, `M4ChiSocketWire.lean:{184,240}`.
The capstone `M4ChiDyadicRowMeanSq` has **6** (three of them `… := by` in
`M4DoorClose`/`M4DoorClosePool`).

So the door's road runs at least five links — `absWindowSum → subWindowSup → strata →
doorChiSup → dyadic → capstone → DoorRowCarried` — and **every link has producers.**

⛔ **AND HERE IS WHERE I STOP AND DO NOT INVERT MY OWN ERROR.**  I spent three beats calling
this road broken one link too early.  The opposite claim — *"the road is complete"* — is the
SAME mistake wearing the other sign, and I have not earned it.  What I measured is that each
link has producer-shaped declarations.  What I did **not** measure is whether they COMPOSE:
whether the constants, the graded floors (`doorRowFloor M`, `j₀`), the modulus cap
`arcDen 12 H ≤ Qm` and the regime fields line up across the seams.

⇒ **THAT is the genuinely open question, and it is not "a missing lemma".**  It is the class
my own banked law names: *the kernel checks theorems, not that they compose.*  A `lake build`
is green on every one of these links today and would stay green with a seam that never joins.

⭐ **INSTRUMENT, NOW CALIBRATED AND REUSABLE.**  Producer-probe v4: exact-name (reject
`Name[A-Za-z_0-9']`, which kills the 24 `DoorRowCarried*` prefix twins and `MRTUniformityXiL2`),
conclusion-shaped, binder-subtracted.  **Control: `MRTUniformityXi` → 6 real sites, 0 prefix
twins.**  v1 scored 0 on that control (missed producers); v2 scored 15 (prefix-inflated); v3
scored 0 on everything (an adjacency bug).  **The control caught all three defects; the probe
caught none of them.**  *Three versions in, the control has done more work than the probe.* -/

/-! ### THE DOOR'S CAPSTONE IDENTIFIED — AND THE ROAD RUNS ONE LINK FURTHER STILL

Continuing the walk, under the rule set in the section below: name no frontier, keep going.

**1. THE TRIVIAL SUPPLIER IS THE SMALL-LENGTH HALF, AND IT SAYS SO.**
`norm_sum_doorSievedWindow_le` (`M4CoprimeSupply.lean:105`) is the window-length bound
`‖∑_{m ∈ doorSievedWindow M K n} liouChi χ m‖ ≤ K`.  Its docstring: used at the SMALL dyadic
lengths, *"where the capstone is silent"*.  So the dyadic split is `j < j₀` trivial grade,
`j₀ ≤ j` capstone (`M4CoprimeSupply.lean:38`, `M4Maximal.lean:1024`).

**2. ⛔ TWO DIFFERENT OBJECTS ARE CALLED "THE CAPSTONE". THEY ARE NOT THE SAME.**
* `logChowla2_capstone_final_rawcap'` (`S12FuseCompose.lean:530`) — the **S12** lane.  This is
  the one carrying `S14Compose.lean:429`'s **`⚠ NOT DERIVED` … "refuted at ⟦B1'-3⟧ by §3"**.
* `M4ChiDyadicRowMeanSq` (`M4Maximal.lean:1026`) — the **M4** lane, and *this* is the one the
  door's dyadic split consumes (`M4Maximal.lean:116`, length-graded `MS j H`).

**The `⚠ NOT DERIVED` marker does NOT lie on the door's chain.**  Checked, not assumed — the
predecessor already lost a day to two different objects both called "Prop 2.4".

**3. THE DOOR'S CAPSTONE IS AN L² MEAN VALUE OBLIGATION.**  `M4ChiDyadicRowMeanSq` is a `Prop`:
`(1/X)·∫_X^{2X} ‖(1/2^j)·shortSum (doorChiCoeff χ M) … y (2^j)‖² ≤ MS j H`, graded per dyadic
length — the same family as `dpolyS_l2_mvt_final`.  69 references, 13 files, decoy 0.

**4. AND IT HAS A PRODUCER, SO THE ROAD CONTINUES.**  `m4_dyadicRow_carried`
(`M4DoorClose.lean:535`) concludes `M4ChiDyadicRowMeanSq R M k MS` from: `1 ≤ M`; the modulus
cap `arcDen 12 H ≤ Qm`; the trivial grade below `doorRowFloor M` (that is item 1); and
`DoorRowCarried …` above it.  Its constants are **constructed** (`∃ Cq cq T₀ Xcap Cs Ccc …`
via `m4_door_meansq_carried`), not assumed.

⇒ **A FOURTH LINK.  I NAME NO FRONTIER AGAIN — and this beat is the evidence the rule is
right: I was one command from calling the capstone the frontier, and the producer sits two
files away.**  The next object is `DoorRowCarried`.

⛔ **INSTRUMENT DEFECT, DISCLOSED.**  My conclusion-position probe reported 3 producer sites.
Its control — `MRTUniformityXi`, a `Prop` I know has a producer — scored **0**.  The probe
misses real producers, so **3 is a LOWER BOUND, not a count**, and is written here as one. -/

/-! ### A.6's INNER OBJECT IS THE SIFTED TWISTED SUM — the docstring's pointer, cashed

`MRTLemmaA6`'s docstring has said from the start that *"the inner object is exactly what
`Salt.MR.lemma5` already produces."*  That was a claim in prose; nothing in Lean connected the
two.  This is the connection.

`lemma5` (`Sec9Glue.lean:275`) is inclusion–exclusion:
`∑_{n ∈ N, n ∈ S} aₙ = ∑_{𝒥 ⊆ {1..J}} (−1)^{#𝒥} ∑_{n ∈ N} g_𝒥(n)·aₙ`.  At
`N := Icc 1 ⌊X⌋₊` and `aₙ := f n · costwist (−t) n` its right-hand side **is** A.6's inner
sum — up to the associativity of `gJ · f n · costwist`, which is the only real content of the
proof below.

⇒ **A.6 is a decay bound on the SIFTED TWISTED SUM**, not on a powerset alternating sum.  That
matters because the sifted twisted sum is the object Halász/pretentious theory speaks about,
and the powerset form is not.  *Restating a hypothesis in the vocabulary of the theory that
must discharge it is not cosmetic.* -/

/-- **A.6'S INNER OBJECT, REWRITTEN AS THE SIFTED SUM** — `lemma5` at `N = Icc 1 ⌊X⌋₊` and
`a = f · costwist (−t)`.  Cashes `MRTLemmaA6`'s own docstring pointer. -/
theorem mrtA6_inner_eq_sifted (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (X t : ℝ) :
    ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n
      = ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => MemS Pseq Qseq J n),
          f n * costwist (-t) n := by
  rw [lemma5 (Finset.Icc 1 ⌊X⌋₊) Pseq Qseq J (fun n => f n * costwist (-t) n)]
  refine Finset.sum_congr rfl (fun 𝒥 _ => ?_)
  refine congrArg (fun z => (-1 : ℂ) ^ 𝒥.card * z) ?_
  exact Finset.sum_congr rfl (fun n _ => (mul_assoc _ _ _))

/-- **A.6'S `F`, IN SIFTED FORM** — `mrtA6_inner_eq_sifted` under `mrtA3_T0_bound_of_A6`'s own
`(1/X)` normalisation.  The point is the CONSUMER: `hFdef` there is stated with the powerset
alternating sum, and this says it may equally be stated with the sifted twisted sum.

⇒ **A supplier who proves a decay bound on `∑_{n ≤ X, n ∈ S} f n · costwist (−t) n` can feed
A.3's `T₀` side directly**, without ever meeting an inclusion–exclusion expansion.  That is
what cashing A.6's docstring pointer buys, and it is why the rewrite was worth landing.

⛔ Note what this does NOT do: it changes the VOCABULARY of A.6's hypothesis, not its
STRENGTH.  The measured gap stands — the landed Halász exponent is `1/(32e)` against A.6's
`1/16` (`landed_halasz_exponent_weaker_than_a6`), and no rewrite closes that. -/
theorem mrtA6_F_sifted (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (X t : ℝ) :
    ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n‖
      = ‖(1 / (X : ℂ)) * ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => MemS Pseq Qseq J n),
            f n * costwist (-t) n‖ := by
  rw [mrtA6_inner_eq_sifted]

/-! ### ⛔ MY OWN HYPOTHESIS, TESTED AND REFUTED — AND THE NEEDED SHAPE, NAMED

Last section fenced a hypothesis as **UNTESTED**: that obstruction 2's *"general per-interval
input"* might be `sum_progression_le_sum_Ioc` / `progression_mem_Ioc_of_window_in_block`,
built at the dyadic step where nothing needed them.  **Tested it.  It is REFUTED.**

`M4BlockMeanSq` (`M4BridgeCover.lean:386`) reads
```
  ∀ H …, ∀ α, NearRatTight (arcDen 12 H) H α → ∀ i < k,
    ∑ n ∈ Finset.Ioc (doorLadder R.x H (i+1)) (doorLadder R.x H i),
        ‖absWindowSum (doorSievedCoeff M) H n α‖²
      ≤ Bblk H · H² · (doorLadder R.x H (i+1) : ℝ)
```
**The index set is hard-wired to `doorLadder` blocks and the RHS scale is the block's own left
endpoint.**  So *"a general per-interval input"* means **this predicate with the interval
freed** — a STATEMENT GENERALISATION, a new Prop.

⇒ **My lemmas conclude `∑_{progression} f ≤ ∑_{Ioc a b} f`: they MOVE BETWEEN INDEX SETS and
supply NO BOUND AT ALL.**  The residue needs a *bound on* an interval sum.  Different objects;
the resemblance was the word "interval" and nothing else.

⭐ **THE SHAPE THAT IS ACTUALLY NEEDED, NAMED** (naming is my tier; deciding it is not — the
source calls this a **design question**, and design is Fable/human-tier):
```
  M4IntervalMeanSq R M Bint : Prop :=
    ∀ H …, ∀ α, NearRatTight (arcDen 12 H) H α → ∀ a b : ℕ, ⟨admissibility on (a,b]⟩ →
      ∑ n ∈ Finset.Ioc a b, ‖absWindowSum (doorSievedCoeff M) H n α‖² ≤ Bint H a b
```
with `M4BlockMeanSq` recovered at `a := doorLadder R.x H (i+1)`, `b := doorLadder R.x H i`.
**The open design content is exactly what `⟨admissibility⟩` must say and what `Bint` may
depend on** — the dilated image `(X_{i+1}/d₀ − 1, X_i/d₀]` has to satisfy it.

🔑 *Process note, and it is the first of its kind today: I fenced a claim as UNTESTED, then
tested it, then refuted it — before it ever became a finding.  The four same-signed errors
earlier were all published first and corrected after.  **Fencing is cheap; retraction is not.*** -/

/-! ### THE ROAD BOTTOMS OUT — AND THE CORPUS NAMES ITS OWN FRONTIER

Walked the gates down: `M4SievedDoorSq_L → M4BlockMeanSq_L → M4RowMeanSq_L`.
`M4RowMeanSq_L` (`M4RowLinear.lean:991`) has **no producer** — established by reading **all six
of its mentions**, not by a probe: docstring · def · a cross-ref · the `hrow` binder (`:1392`) ·
an enumeration entry (`:3419`) · one arrow (`:3434`).

⭐ **AND THIS TIME IT IS NOT MY INFERENCE — THE CORPUS SAYS SO AT THE DEFINITION SITE:**
*"**THE WAVE'S REMAINING INPUT**… This predicate is the wave's ⟦RESIDUE⟧: see the module header
for the two obstructions that keep it from being discharged from `m4_meansq_per_chi_gen_L`."*

The pointer resolves — in the ORIGINAL module, not the `_L` twin: **`M4Join.lean:73`,
`## ⟦THE RESIDUE⟧ — named precisely, not deferred vaguely`.**  (The `_L` file is a verbatim
restatement of its landed original, so it inherited "the module header" pointing at `M4Join`'s.
**I nearly published "dangling reference" and checked first.**)

**THE TWO OBSTRUCTIONS, AND ONE IS ALREADY CLOSED:**
1. **⟦THE WALL⟧ — REPAIRED** (2026-07-28, the E-wave, flags `a626571`).  `M4ErrRewire`'s
   `ramP2massMR_direct` prices the `p²`-mass with the coefficient sequence UNCONSTRAINED, and
   `FrameWitness.err_at_witness_mr(_end)` supersedes the old supplier with `hwin` gone.  The
   file states it is *"no longer a blocker."*
2. **⟦THE CLASS PRICING⟧ — OPEN.**  The route from a tight-major `α` to the *unsieved dilated*
   datum changes the block's index set: dilation carries a `doorLadder` block `(X_{i+1}, X_i]`
   to `(X_{i+1}/d₀ − 1, X_i/d₀]`, **which is not a `doorLadder` block of any ladder**.  So the
   class pricing cannot be stated as `M4BlockMeanSq` at the dilated scale *"without a general
   per-interval input"*; and the non-coprime half is not discharged by the trivial threshold at
   small `d₀` (`trivThresh H d₀ W = H·d₀/W³` needs `d₀² ≳ W³`).  The file calls both **design
   questions, not proof-engineering ones.**

📌 **A HYPOTHESIS FOR THE NEXT BEAT, DELIBERATELY NOT A CLAIM.**  Obstruction 2's core is an
INDEX-SET problem, and the residue asks for *"a general per-interval input"* — which is the
shape of `sum_progression_le_sum_Ioc` / `progression_mem_Ioc_of_window_in_block`, landed in
`DoorRoadCompose.lean` and marked there as pedagogy.  **It may be that I built the right kind of
tool in the wrong place — at the dyadic step, where nothing needed it, rather than at the
DILATION, where the corpus says something does.**  That is an excited conclusion, which by my
own standing rule is a trigger to check, not a finding.  **UNTESTED.** -/

/-! ### THE DOOR'S FOUR GATES, MEASURED — TWO OF THREE REDUCE TO NAMED SMALLER THINGS

`M4RowLinear.m4_hbd_of_live_L` (`:2335`) delivers the door's `hbd` from four bundles.  Probed
each with the calibrated producer probe (control `MRTUniformityXi` → 6; decoy → 0):

**`M4GradeGate`** (`M4Close.lean:425`) — `m4_gradeGate_direct` (`M4ClassPrice.lean:709`)
produces it from **two explicit inequalities and NO other gate**:
`√(Braw H) ≤ mrtDeliveredGrade (C/2) H` and `δ/4 + 4·2^k/x ≤ mrtDeliveredGrade (C/2) H`.
*It bottoms out in arithmetic about the delivered grade, not in another Prop socket.*

**`M4SievedDoorSq_L`** (`M4LadderLinear.lean:921`) — `m4_cover_assembly_L`
(`M4RowLinear.lean:1530`) produces it from `M4DoorGates_L` + `Bblk ≥ 0` + **`M4BlockMeanSq_L`**.
Its own docstring states the gate bundle is *"the same bundle `m4_hbd_of_live_L` reads, so the
join needs no new hypothesis"* — so this reduction is free at the seam.  ⇒ **it reduces to the
BLOCK MEAN SQUARE**, which is what `M4Maximal.m4_chiBlockMeanSq_of_shiftBlock` produces.

**`M4DoorGates_L`** (`M4LadderLinear.lean:939`) is a **structure** — a bundle of regime data, so
its "producer" is an instance construction rather than a theorem.  Not measured here.

⛔ **I AM NOT CALLING THE GATES CLOSED.**  Today I made four same-signed errors reading the
corpus as having LESS than it does, and the correction for that is not to start reading it as
having MORE.  What is measured: two of three gates have producers that consume no further gate
(`M4GradeGate`) or reduce to one named object (`M4SievedDoorSq_L → M4BlockMeanSq_L`).  What is
**NOT** measured: whether `M4BlockMeanSq_L` and the `M4DoorGates_L` instance bottom out.
**That is the next question, and I have not answered it.** -/

/-! ### ⛔⛔⛔ THE DOOR'S ROAD WALKED TO ITS END — MY FRONTIER CLAIM RETRACTED, THIRD TIME

I said one beat ago that the door's missing piece is *"the TERMINAL CANCELLATION."*  **That is
wrong, and it is wrong in the same direction as the two claims before it.**  Walking the chain:

```
  norm_absWindowSum_le_drift_tight     M4BridgePhase.lean:310   (phase drift → rational b/q)
    ⟹ subWindowSup_sq_le_strata       M4Gauss.lean:577         (Gauss/strata, at doorSievedCoeff M)
        ⟹ strataTerm = ∑_χ (doorChiSup χ …)²
            ⟹ doorChiSup_sq_le_dyadic  M4Maximal.lean:396      (DYADIC MAXIMAL INEQUALITY, K-free)
                ⟹ ∑_t ‖∑_{m ∈ doorSievedWindow M 2^j (n+2^{j+1}t)} liouChi χ m‖²
```
`subWindowSup_sq_le_strata` is stated **at the door's own coefficient** `doorSievedCoeff M`, not at
a generic `a`.  `doorChiSup_sq_le_dyadic` is a Rademacher–Menshov-shaped maximal inequality with
geometric weights.  **Measured: 20+ consumption sites for that one lemma across six files**
(`M4BaseNarrow`, `M4RowLinear`, `M4ChiSummed`, `M4CoprimeSupply`, `M4RowAssemblyLinear`,
`M4Maximal`).  This is not a frontier.  It is a highway.

⛔⛔ **THREE CLAIMS, THREE BEATS, ALL ONE LINK TOO EARLY — AND ALL MINE:**
1. *"the door has NO PRODUCER"* → `mrtUniformityXi_of_absWindowBound_twelve` produces it.
2. *"the corpus lacks the ANALYTIC estimates"* → `drift_tight` / `class_sum_of_nearRatTight`.
3. *"what is missing is the TERMINAL CANCELLATION"* → strata → doorChiSup → dyadic maximal.

⇒ **THE DEFECT IS IN MY METHOD, NOT IN THE CORPUS.**  Each time I read to the edge of my own
reading, found an object whose bound I had not personally seen, and published *that* as the edge of
the CORPUS.  **"Missing" is a claim about a LEAF; I kept measuring a LINK.**

⭐ **THE ONE-COMMAND TEST I HAD NEVER RUN: `grep` THE CONSUMERS.**  A frontier has few or none
downstream; this link has twenty.  Cheap, decisive, and absent from all three of my verdicts.
*Before calling anything a frontier, count what already depends on it.*

📌 **I AM DELIBERATELY NOT NAMING A FRONTIER HERE.**  The chain bottoms out at a dyadic mean square
of `liouChi`-twisted sieved window sums; whether THAT is supplied I have not opened
(`norm_sum_doorSievedWindow_le` and three siblings exist, unread).  Naming it now would be the
fourth instance of the exact error this section diagnoses. -/

/-! ### The door's `absWindowSum` residue — OPENED, and it REFUTES my own generalisation

Last of the four sweep rows.  Measured: **57 landed `absWindowSum` theorems across 14
files.**  Opening the two that matter:

```
  integral_logMeasure_absWindowSum_le_thresh   M4Dyadic.lean:665
      (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure x ω)) ≤ thr      from (H' : ℝ) ≤ thr
```
This is the door's `hbd` shape **exactly** — and its own docstring calls it *"THE TRIVIAL
CUT… discharged with no analysis at all… the branch the consumer takes to discard tiny
windows."*  At the door's `thr := δ·H` its hypothesis is `H ≤ δ·H`, which forces `δ ≥ 1`
(`trivial_cut_needs_delta_ge_one`) — **the opposite regime from the one the door needs.**

⛔⛔ **BUT THE NEXT TWO REFUTE THE GENERALISATION I PUBLISHED ONE BEAT AGO.**  I wrote:
*"the corpus consistently holds the ALGEBRAIC identities and consistently lacks the
ANALYTIC estimates."*  That is **too strong**:
```
  norm_absWindowSum_le_drift_tight            M4BridgePhase.lean:310
      at NearRatTight (arcDen B₅ H) H α  ⟹  ‖absWindowSum a H n α‖
          ≤ (1 + 2π·(arcDen B₅ H / q))·subWindowSup a H n (b/q)
  norm_absWindowSum_le_class_sum_of_nearRatTight   M4BridgeResidue.lean:281
      at NearRatTight Q H α  ⟹  ‖absWindowSum‖ ≤ ∑_r ‖classPhaseSum …‖
```
**Both are genuine ANALYTIC reductions, at the door's OWN hypothesis** — a phase-drift
transfer from an arbitrary `α` to a rational `b/q`, and a class-sum split.  Neither is a
trivial cut.

⇒ **CORRECTED VERDICT: the corpus holds the algebra AND the analytic REDUCTIONS.  What is
missing is the TERMINAL CANCELLATION — the estimate making `subWindowSup` / the class sums
actually small (`≤ δ·H` at small `δ`).**  That is a strictly narrower and more useful
statement of where the door stands than either "no producer" or "no analysis".

🔑 *This came from deliberately opening the name most likely to refute me, immediately
after my prediction was CONFIRMED by the trivial-cut theorem.  **An agreeing result is the
one to doubt** — and here the doubt paid, in the same beat.* -/

/-- The trivial cut needs `δ ≥ 1`: `H ≤ δ·H` with `H > 0` forces `1 ≤ δ`.  *So
`integral_logMeasure_absWindowSum_le_thresh` cannot serve the door, which needs `δ` SMALL.* -/
theorem trivial_cut_needs_delta_ge_one {H : ℕ} {δ : ℝ} (hH : 0 < (H : ℝ))
    (h : (H : ℝ) ≤ δ * (H : ℝ)) : 1 ≤ δ := by
  nlinarith [h, hH]

/-! ### A.7 vs `Renormalise.lean` — OPENED, and the factor is literally the same one

Second of the two rows the sweep left *named-not-opened*.  Opening it: the match is much
closer than A.6's was.

`renormalise_aux` (`Renormalise.lean:760`), with `eIu u y := exp(I·u·log y)` — i.e.
`y^{iu}` (`Renormalise.lean:497`):
```
  ‖ ∑_{n≤x} f n · eIu u n  −  x·eIu u x/(1 + I·u) · ∑_{d≤x} mobDatum f d / d ‖
      ≤ 2C₁(5 + 2 log y)·(x/log x)·∑_{d≤x} mobNorm f d/d,     y = 3 + |u|(1+log x)
```
against **A.7**:
```
  ‖ ∑_{n≤X} gJ·f·costwist(−t) n
      − exp((t−t₁)·I·log X)/(1 + (t−t₁)·I) · ∑_{n≤X} gJ·f·costwist(−t₁) n ‖
      ≤ C·X/(log X)^{1/10}
```

✅ **THE RENORMALISATION FACTOR IS LITERALLY THE SAME OBJECT.**  At `u := t − t₁`,
`eIu u x = X^{i(t−t₁)}` and the denominator `1 + I·u` is A.7's `1 + (t−t₁)·I`.  *This is the
factor whose SIGN this seat resolved at 08:2x (`mrtA7_factor_conj`,
`mrtA7_factors_same_norm`) — it is landed machinery, not something to invent.*

⛔ **TWO REAL DIFFERENCES, and they are the residue:**
```
  (1) TARGET.  renormalise_aux renormalises against ∑ mobDatum f d/d — a Möbius/mean-value
      datum.  A.7 renormalises against the SAME sum at t₁.  Different right-hand object.
  (2) ERROR.   the landed error is (x/log x)·∑ mobNorm f d/d.  Its log POWER is stronger
      than A.7's (log X)^{−1/10} — see `renormalise_error_logpower_stronger` — but it is
      multiplied by a weight sum that is NOT bounded by a constant.
```
Also: `renormalise_aux` demands `f 1 = 1` and multiplicativity (A.7 asks only 1-boundedness),
and carries no `gJ` window.

⇒ **A.7's residue is narrower than "prove A.7": RE-TARGET the right-hand object from
`∑ mobDatum/d` to the `t₁`-twisted sum, and control `∑ mobNorm f d/d` against
`(log X)^{−1/10}`.**  *Third sweep row opened, third time the family was right and the shape
needed work — but this is the first where a NAMED PIECE of the target is landed verbatim
rather than merely nearby.* -/

/-- The landed renormalisation error carries `x/log x`, whose log power is **stronger** than
A.7's `X/(log X)^{1/10}`: for `X ≥ e`, `X/log X ≤ X/(log X)^{1/10}`.  *So the log power is
not the obstruction — the unbounded weight sum beside it is.* -/
theorem renormalise_error_logpower_stronger {X : ℝ} (hX : Real.exp 1 ≤ X) :
    X / Real.log X ≤ X / (Real.log X) ^ ((1 : ℝ) / 10) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hpow : (Real.log X) ^ ((1 : ℝ) / 10) ≤ Real.log X := by
    calc (Real.log X) ^ ((1 : ℝ) / 10)
        ≤ (Real.log X) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
  have hppos : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hLpos _
  exact div_le_div_of_nonneg_left hXpos.le hppos hpow

/-! ### A.6, measured against the landed Halász family — and the hit is the WRONG SHAPE

The set sweep reported *"A.6's estimate — OPEN → 61 landed `halasz*` theorems"*.  That
count is real and it is **not** evidence A.6 is servable.  Measuring the closest one shows
why, and it corrects my own framing one beat old.

`T1_pointwise_decay` (`PropA3Core.lean:330`) is the nearest landed relative:
```
  U ≤ (C₁+C₂)·X·( (log X)^{−1/(32e)} + (log X)^{−1/2+ε} )
      from  Uhead ≤ C₁·X·exp(−(1/e)·M_range f X T),  Utail ≤ C₂·X·(log X)^{−1/2},
      floor (1/32)·loglog X ≤ M_range f X T
```
against **A.6's** target
`‖(1/X)·Σ_𝒥 …‖ ≤ C·( exp(−M/2)/(1+|t−t₁|) + (log X)^{−1/16} )`.

⛔ **THE DECISIVE DIFFERENCE IS NOT THE CONSTANTS — IT IS THAT `T1_pointwise_decay` HAS NO
`t₁` IN IT AT ALL.**  A.6's entire content is the `1/(1+|t−t₁|)` decay away from the
minimiser; that factor is what makes `∫_{T₀} A²/(1+|t−t₁|)²` converge and is exactly what
`mrtA3_T0_setIntegral_bound_onT0` consumes.  A flat Halász bound cannot supply it.

⚠️ **And the exponents are weaker too, measured rather than eyeballed** — see
`landed_halasz_exponent_weaker_than_a6` and `landed_halasz_M_rate_weaker_than_a6` below:
`1/(32e) < 1/16` and `1/e < 1/2`, both strict.

⇒ **A.6's residue is now NAMED, and it is narrower than "prove A.6": it is the
`1/(1+|t−t₁|)` factor.**  *Correcting my own last-beat framing: "61 landed `halasz*`
theorems" was a COUNT, and a count is not a match.  The sweep found the right family and
the wrong shape — which is the same lesson as Turán–Kubilius vs Erdős–Turán, arriving from
the other direction.* -/

/-- The landed Halász grade `(log X)^{−1/(32e)}` is strictly weaker than A.6's
`(log X)^{−1/16}`: `1/(32e) < 1/16`.

⛔⛔ **THIS CONTROL HAS A HARDCODED WITNESS AND WOULD DEGRADE IN SILENCE — FLAGGED, NOT FIXED
(2026-08-22 19:1x).**  Found by applying compiler's `C4.lean` `coreShort` lesson to my own hands
the hour they posted it: *derive the witness from the quantity it is testing against, and the
control cannot outlive its own meaning.*

**BOTH sides here are literals.**  `1/(32·e)` is the landed Halász exponent and `1/16` is A.6's;
neither is read from its source.  If either moves, **this theorem keeps proving** — `1/(32e) <
1/16` is a true numeric fact forever — while its NAME and this docstring go on asserting a
relationship that no longer holds.  **Green build, silent degradation**, exactly `coreShort`.

📊 **THE RISK IS MEASURED, NOT ESTIMATED: A.6's exponent occurs as a bare literal `(1 : ℝ)/16`
THIRTY-TWO times in this file**, including inside `MRTLemmaA6`'s own statement.  A future change
is a 32-site edit with **no mechanical guard anywhere**.

⛔ **WHY IT IS FLAGGED RATHER THAN FIXED:** the real repair is to abstract A.6's exponent to a
named constant and derive both sides from it — but that edits `MRTLemmaA6`'s STATEMENT, which is
iron rule 1 and Fable/Captain tier.  The Captain's 17:4x ruling covered the ambient hypotheses
and nothing else.  *A half-fix that merely LOOKS derived — a local constant not wired into the
Prop — would be worse than this flag, because it would read as a guard while guarding nothing.* -/
theorem landed_halasz_exponent_weaker_than_a6 :
    1 / (32 * Real.exp 1) < (1 : ℝ) / 16 := by
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h32 : (0 : ℝ) < 32 * Real.exp 1 := by linarith
  rw [div_lt_div_iff₀ h32 (by norm_num : (0:ℝ) < 16)]
  linarith

/-- The landed Halász `M`-rate `exp(−M/e)` is strictly weaker than A.6's `exp(−M/2)`:
`1/e < 1/2`, i.e. `2 < e`. -/
theorem landed_halasz_M_rate_weaker_than_a6 : 1 / Real.exp 1 < (1 : ℝ) / 2 := by
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [div_lt_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
  linarith

/-! ## RECON — the trigger law, applied to ALL my remaining "open" claims at once

Row 17k found one buried massif by asking *"have I checked my own store?"* about a single
claim.  Row 17d's lesson says sweep the SET.  Doing that to every remaining open/external
claim in this campaign fires on **all three**:

```
  CLAIM                          SWEEP RESULT
  A.6's estimate — "OPEN"        61 landed `halasz*` theorems in Salt/ (A.6 IS Halász-type)
  A.7's renormalisation — "OPEN" Salt/MR/Renormalise.lean exists: renormalise_aux,
                                 renormaliseConst, renormalise_aux_zero
  the door — "NO PRODUCER"       FIVE landed theorems named mrtUniformityXi*
```

⛔⛔ **THE THIRD IS A RULED FIELD OF THE STANDING PROMPT AND IT IS WRONG AS STATED.**
`MRTUniformityXi` is *not* producerless.  Measured, not quoted:

```
  mrtUniformityXi_of_absWindowBound_twelve   M4Window.lean:268   CONCLUDES MRTUniformityXi R δ
  bigXiArcTight_twelve                       ExitClose.lean:773   NO HYPOTHESES — unconditional
  both REGISTERED in Salt/MR/All.lean (lines 1710, 2000) ⇒ inside the axiom audit
```

The adapter reduces the door to **one** remaining hypothesis — an `L¹` bound
`∫ ‖absWindowSum lamCoeff H n α‖ dμ ≤ δ·H` over the log-measure, uniformly on
`R.Hlo ≤ H ≤ R.Hhi` at arc-tightness — with the arc side **already unconditional**
(`bigXiArcTight_twelve`; the `_of_close` variant is the conditional twin, and it is a
DIFFERENT theorem).

⇒ **THE DOOR'S PRICE IS ONE NAMED ESTIMATE, NOT A FORMALISATION OF TAO PROP 2.4 FROM
SCRATCH.**  *That is the same correction as row 17k's "external" → "not yet connected", and
it is now the fourth time today: the corpus keeps already containing the thing I priced as
missing.*

⚠️ **This does NOT prove the door**, and nothing here is a claim that it holds.  The
residue is real and unproved.  What changed is the PRICE and the SHAPE of the residue.

📌 *Recorded here rather than in `MRTDoor.lean` because the door's file has 34 dependents
and this is recon, not a source change.  Re-arm request posted to the bus.* -/

/-! ## RECON — Erdős–Turán is absent, and the corpus has ROUTED AROUND IT BEFORE

A.4(ii)'s far branch was priced as needing *Erdős–Turán + VK equidistribution*, on an
absence claim that rested on ONE live search arm.  Re-run with three live arms, each
carrying a positive control:

```
  ARM 1  identifier   ^(theorem|lemma|def) …(erdos|erdős|turan|turán)   1 hit: turan_kubilius
  ARM 2  filename     find -iname *erdos*/*turan*                       1 hit: TuranKubilius.lean
  ARM 3  prose        the JOINT pattern, either order, case-insensitive  0 hits in Salt/
```

✅ **ABSENCE CONFIRMED, AND SHARPER THAN BEFORE: no Erdős–Turán declaration, file, or
prose mention anywhere in `Salt/`.**  ⚠️ **And the near-miss is named:** both non-prose
arms hit **Turán–Kubilius**, a DIFFERENT inequality (variance, not discrepancy).  A
surname-only matcher would have reported a find; the joint-pattern arm is what separates
them.

⭐⭐ **BUT THE PROSE ARM FOUND SOMETHING BETTER THAN AN ABSENCE.**  Two independent corpus
records — `docs/blueprints/flags.md` and `docs/exploration/s8-freeze-0727.md` — say the
same thing about a prior demand:

> *"D-5 is DISSOLVED (`dist_recenter` + `dist_one_floor_pow` + `dist_split_A4_frozen` —
> **no Erdős–Turán, no PNT-in-segments**; the VK region enters via `one_line_pow_growth`)"*

**All four objects are landed.**  And `dist_split_A4_frozen` (`PropA3Core.lean:172`) has a
branch-b hypothesis that is A.4(ii)'s far configuration almost verbatim — `1 ≤ |t−t₁|`,
`|t−t₁| ≤ X`, and `pretDistSq f (costwist t₁) X ≤ (1/16)·loglog X`, which is the centre
cap `mrtA4ii_far_centre_cap` supplies — with its window mass `W` **carried, not zero**.

⛔ **NAME COLLISION, AND IT MATTERS:** this is `dist_split_A4_frozen`, NOT the
`dist_split_A4` refuted in the section below.  That refutation turned on `hloss` being
unsatisfiable **at `W = 0`**; here `W` is a free carried parameter, so the obstruction
does not apply.  *Two objects one underscore-suffix apart, opposite verdicts.*

⛔ **THE `(1/32)` ROUTE CANNOT SERVE A.4(ii) AT A.4(ii)'s CONSTANT — two gaps, the second
fatal:**
```
  (1) fgJ f t₀ y Y = seamCoeff f (windowInd …) — a SEAM window with t₀,y,Y, NOT
      A.4(ii)'s (fun n => f n * gJ 𝒥 Pseq Qseq n).  Different object.
  (2) frozen gives (1/32)·loglog X;  A.4(ii) needs (1/6 − 1/(3π) − ε)·loglog X.
      1/32 = 0.03125 < 1/6 − 1/(3π) ≈ 0.0606 — SHORT BY ~2×, before the
      −5·logloglog − C − W corrections are subtracted.
```
Proved here as `landed_route_below_a4ii_target : (1:ℝ)/32 < 1/6 − 1/(3π)` — **the landed
chain is insufficient BY CONSTRUCTION, not by a gap in its proof.**

⇒ **WHAT REMAINS OPEN IS NARROWER:** whether any OTHER composition of the D-5 objects
reaches a constant above `1/6 − 1/(3π)`.  `dist_split_A4_frozen` as stated does not.

*(The correction narrative that stood here — I published "the price is OPEN" while my own
landed theorem had already closed it — is in the commit record, per the Captain's CLEAN
HOUSE ruling and compiler's law: **write the corrected FACT, not the STORY of the
correction; the story belongs in a commit message, which has no cap.**)* -/

/-! ## The salt-engine collision — `dist_split_A4` does NOT reach A.4(i)

`Salt/MR/DistSplit.lean`'s `dist_split_A4` carries A.4(i)'s conclusion SHAPE at
`W = 0`:  `(1/2)·Lf − W ≤ 𝔻²(g_J, n^{it}; x)`.  It is nevertheless **not** a route
to `mrtA4i_holds`, and the obstruction is in its hypothesis, not its conclusion:

  `hloss : pretDistSq f gJ x ≤ W`

is **unsatisfiable at `W = 0`** for A.4(i)'s own `g_J = f · g_𝒥`.  Windowing kills
primes, and each killed prime `p ≤ x` contributes exactly `1/p` to the loss, since
`g_𝒥(p) = 0` makes the summand `(1 − Re(f p · conj 0))/p = 1/p`.

`mrtA4i_loss_witness` below is a KERNEL witness, not an argument: `f ≡ 1`,
`𝒥 = {1}`, `P₁ = Q₁ = 2`, `x = 2` — one prime in range, killed by the window —
and the loss is exactly `1/2 > 0`.

⇒ **The generic triangle route (`dist_mul_half`) pays `Σ_{p killed} 1/p`; A.4(i)
asserts no such loss is needed.**  That mass is precisely what `mrtA4i_holds`'
POINTWISE case split recovers for free: at a killed prime the target term is `1/p`,
and `1/p ≥ (1/2)·(1 − Re(f p · conj (costwist t p)))/p` holds because
`1 − Re(·) ≤ 2`.  So the pointwise proof is not merely *cheaper* than the triangle
route — it reaches a statement the triangle route provably cannot.

⛔ **THIS CORRECTS THIS SEAT'S OWN PUBLISHED CLAIM** (`QUEUE.md` row 15u,
2026-08-22 02:0x): *"`dist_split_A4` at `W = 0` is A.4(i) exactly."*  It is not.
The conclusions coincide; the hypotheses do not, and the gap is not removable.
-/

/-- **Witness: A.4(i)'s window loss is strictly positive**, so `dist_split_A4`'s
`hloss` cannot be discharged at `W = 0` for `g_J = f · g_𝒥`.  Here `f ≡ 1`,
`𝒥 = {1}`, `P₁ = Q₁ = 2`, `x = 2`: the only prime in range is `2`, the block
`[2,2]` contains it, so `g_𝒥(2) = 0` and the loss is `1/2`. -/
theorem mrtA4i_loss_witness :
    pretDistSq (fun _ => (1 : ℂ))
        (fun n => (1 : ℂ) * gJ ({1} : Finset ℕ) (fun _ => 2) (fun _ => 2) n) 2
      = 1 / 2 := by
  have hb : blockOmega 2 2 2 ≠ 0 := by
    unfold blockOmega BlockPrimeDivs
    rw [Nat.Prime.primeFactors Nat.prime_two]
    simp
  have hgJ2 : gJ ({1} : Finset ℕ) (fun _ => 2) (fun _ => 2) 2 = 0 := by
    unfold gJ
    rw [if_neg]
    intro h
    exact hb (h 1 (Finset.mem_singleton_self 1))
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  unfold pretDistSq
  rw [hfloor, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two, hgJ2]

/-- The loss is positive, stated as the refutation it is: no `W = 0` instance of
`dist_split_A4` applies to A.4(i)'s windowed factor. -/
theorem mrtA4i_loss_pos :
    0 < pretDistSq (fun _ => (1 : ℂ))
        (fun n => (1 : ℂ) * gJ ({1} : Finset ℕ) (fun _ => 2) (fun _ => 2) n) 2 := by
  rw [mrtA4i_loss_witness]; norm_num

/-! ## The OTHER arm of row 15u — `dist_recenter_sq` is not A.7's algebra either

Row 15u made TWO identity claims. `mrtA4i_loss_witness` above refutes the first.
The second — *"`dist_recenter_sq` (`DistSplit.lean:140`) ⇒ A.7's RECENTERING
algebra"* — fails on TYPE, before any mathematics:

  `MRTLemmaA7`        `‖ Σ_{n ∈ Icc 1 ⌊X⌋₊} … − (X^{i(t−t₁)}/(1+i(t−t₁)))·Σ_{n} … ‖ ≤ …`
                      a ℂ-norm of a DIFFERENCE of sums over INTEGERS, with an
                      explicit MAIN TERM, bounded ABOVE.
  `dist_recenter_sq`  `(√L − √S)² ≤ pretDistSq f (costwist t) x`
                      an ℝ-valued LOWER bound on a sum over PRIMES `p ≤ x`,
                      no main term.

⇒ different index set, different codomain, opposite inequality direction.
`dist_recenter_sq` is a reverse-triangle inequality on `𝔻` — Halász /
Granville–Soundararajan apparatus, i.e. A.4's world — whereas A.7 is a partial
summation identity. **Both of row 15u's identifications are wrong.**

⚠️ Stated as what it is: a comparison of the two STATEMENTS, checked by reading
them, NOT a kernel refutation. The kernel object below is a different claim.
-/

/-- **A.7's transcription check — the identity is EXACT at the center.**  At
`t = t₁` the main-term factor `X^{i(t−t₁)}/(1 + i(t−t₁))` must collapse to `1`,
making A.7's bracketed difference identically `0`.  This tests the factor this
seat read off the PDF: a mistranscribed exponent or denominator would NOT
degenerate to `0` here.  (`X^{iu} = exp(i·u·log X)`, so `u = 0` gives `exp 0 = 1`
over `1 + 0i = 1`.) -/
theorem mrtA7_exact_at_center (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ)
    (X t₁ : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t₁) n)
        - (Complex.exp ((((t₁ - t₁ : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
            / (1 + (((t₁ - t₁ : ℝ) : ℂ)) * Complex.I))
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t₁) n
      = 0 := by
  simp

/-! ## ⛔ `MRTLemmaA4ii` IS **STILL** FALSE — the second disjunct is unguarded

An earlier pass found `MRTLemmaA4ii` false and repaired it by carrying
`Real.exp 1 ≤ X`.  That repair was necessary and insufficient: the statement is
false again, for an independent reason, on the arm that repair never touched.

**`t₁` is universally quantified and appears ONLY inside the disjunct**
`(log X)^{1/16}/2 < |t − t₁|`.  Nothing ties it to `mrtM`.  In MRT, `t₁` is *the
minimiser* of `𝔻²(f, n^{it}; X)` over `|t| ≤ X` — that is the whole content of
"`t` is far from the centre".  Dropped, the disjunct becomes satisfiable at will
(pick `t₁` far from `t`), and the lemma then asserts a positive lower bound on a
distance that can be exactly `0`.

  WITNESS   f ≡ 1,  𝒥 = ∅  (so f·g_𝒥 ≡ 1),  t = 0,  X = exp(exp 1),  ε = 1/100,
            t₁ = (log X)^{1/16}/2 + 1
    second disjunct  (log X)^{1/16}/2 < |0 − t₁|            TRUE by construction
    RHS  𝔻²(1, n^{i·0}; X) = Σ_p (1 − Re(1·conj 1))/p = 0
    LHS  (1/6 − 1/(3π) − 1/100)·loglog X = 1/6 − 1/(3π) − 1/100 > 0   (π > 3)
  ⇒ LHS > RHS.  FALSE.

⭐ Note the FIRST disjunct is immune: `mrtM f X` pins the centre by construction,
which is why `mrtA4ii_high_M_target` proves cleanly.  **The two arms were never
equally guarded, and the missing guard is exactly the object the other arm names.**

🔑 **THE REPAIR IS TO CONSTRAIN `t₁`, NOT TO WEAKEN THE CONCLUSION** —
`mrtM f X = pretDistSq f (costwist t₁) X` (t₁ attains the infimum), which
`exists_min_pretDistSq` already supplies.  Recorded, not silently patched:
`MRTLemmaA4ii` is left AS TRANSCRIBED and the defect is carried beside it, so the
statement and its refutation travel together. -/

/-- **`MRTLemmaA4ii` as transcribed is refutable.**  The second disjunct does not
constrain `t₁` to the minimiser, so it can be satisfied while the twisted distance
is exactly `0`. -/
theorem not_mrtLemmaA4ii : ¬ MRTLemmaA4ii := by
  intro h
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr he1
  have hXpos : (0 : ℝ) < Real.exp (Real.exp 1) := Real.exp_pos _
  have hlogX : Real.log (Real.exp (Real.exp 1)) = Real.exp 1 := Real.log_exp _
  have hApos : 0 < (Real.log (Real.exp (Real.exp 1))) ^ ((1 : ℝ) / 16) := by
    rw [hlogX]; exact Real.rpow_pos_of_pos (Real.exp_pos 1) _
  have habs : |(0 : ℝ) - ((Real.log (Real.exp (Real.exp 1))) ^ ((1 : ℝ) / 16) / 2 + 1)|
      = (Real.log (Real.exp (Real.exp 1))) ^ ((1 : ℝ) / 16) / 2 + 1 := by
    rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
  have key := h (fun _ => (1 : ℂ)) (fun _ => 0) (fun _ => 0) (∅ : Finset ℕ)
      (Real.exp (Real.exp 1)) 0
      ((Real.log (Real.exp (Real.exp 1))) ^ ((1 : ℝ) / 16) / 2 + 1) (1 / 100)
      (fun n => by simp) hXe (by rw [abs_zero]; linarith) (by norm_num)
      (Or.inr (by rw [habs]; linarith))
  -- the right-hand side is an empty cancellation: every summand vanishes
  have hrhs : pretDistSq
      (fun n => (1 : ℂ) * gJ (∅ : Finset ℕ) (fun _ => 0) (fun _ => 0) n)
      (costwist 0) (Real.exp (Real.exp 1)) = 0 := by
    unfold pretDistSq
    refine Finset.sum_eq_zero (fun p _ => ?_)
    have hg : gJ (∅ : Finset ℕ) (fun _ => 0) (fun _ => 0) p = 1 := by
      unfold gJ
      rw [if_pos (fun j hj => absurd hj (by simp))]
    have hcw : costwist 0 p = 1 := by unfold costwist; simp
    -- `rw` cannot see through the beta-redex `(fun n => 1 * gJ .. n) p`; `simp` beta-reduces first
    simp [hg, hcw]
  rw [hrhs, hlogX, Real.log_exp] at key
  -- and the left-hand side is positive, because `π > 3`
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h9 : 1 / (3 * Real.pi) < 1 / 9 := by
    refine one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  linarith

/-! ## Pricing A.4(ii)'s far branch: the landed engines are STRICTLY too weak

With `MRTLemmaA4ii`'s `t₁` repaired (constrained to the minimiser), the far
branch has an obvious route through objects that are already landed:

```
  dist_one_floor_pow   DistHalasz.lean:179   L ≤ 𝔻²(1, n^{i(t−t₁)}; X),  unconditional
                       the 1/4-grounding: for |b| ≤ 2X the −(3/4)loglog correction
                       eats 3/4 of the leading loglog, leaving L = (1/4)·loglog X − o(1)
  dist_recenter_sq     DistSplit.lean:140    (√L − √S)² ≤ 𝔻²(f, n^{it}; X)
                       at the centre cap S = (1/16)·loglog X
  mrtA4i_holds         (this file)           halves it onto f·g_𝒥
```

**That chain terminates at `(1/32)·loglog X`** — which is exactly `PropA3Core`'s
frozen S8 numeral, and the two lemmas below establish, by computation rather than
by citation, that it is **strictly below** A.4(ii)'s target `1/6 − 1/(3π)`:

  `(1/32) = 0.03125`   vs   `1/6 − 1/(3π) ≈ 0.06057`   — short by ~1.94×.

⇒ **The landed S8 engines cannot prove MRT's A.4(ii), and the shortfall is not a
constant one can absorb: the target is nearly twice the route's output.** MRT
reach the larger constant by a sharper argument than recentre-then-halve.

🔑 This is a PRICE, not a refutation of anything: A.4(ii)'s far branch is
genuinely open and its cost is now measured rather than guessed. *The previous
two prices in this campaign were guesses about proofs I had not opened, and they
erred in opposite directions.* -/

/-- **The landed route's terminal constant, COMPUTED.**  `dist_recenter_sq` at
`L = (1/4)ℓ`, `S = (1/16)ℓ` gives `(√L − √S)² = (1/16)ℓ`; `mrtA4i_holds` halves
it. Stated on the bare coefficients so the arithmetic is checked, not asserted. -/
theorem recenter_then_halve_constant :
    (Real.sqrt (1 / 4) - Real.sqrt (1 / 16)) ^ 2 / 2 = 1 / 32 := by
  have h4 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h16 : Real.sqrt (1 / 16) = 1 / 4 := by
    rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, h16]; norm_num

/-- **AND IT IS STRICTLY BELOW A.4(ii)'s TARGET.**  `1/32 < 1/6 − 1/(3π)`, so a
`(1/32)·loglog X` floor does NOT imply A.4(ii)'s conclusion — the landed chain is
insufficient by construction, not by a gap in its proof.  Needs only `π > 3`. -/
theorem landed_route_below_a4ii_target :
    (1 : ℝ) / 32 < 1 / 6 - 1 / (3 * Real.pi) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h3 : (0 : ℝ) < 3 * Real.pi := by linarith
  have h : 1 / (3 * Real.pi) < 1 / 9 :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  linarith

/-! ## Sibling sweep: does A.6 / A.7 have A.4(ii)'s free-`t₁` defect?

15ii found `MRTLemmaA4ii` false because `t₁` floats free. `t₁` also occurs in
`MRTLemmaA6` and `MRTLemmaA7`, so finding it fatal in one says nothing about the
others — the sweep is a step, not an inference.

**Result: A.4(ii) is the only fatal one of the three, and the discriminator is the
INEQUALITY DIRECTION of the clause `t₁` appears in.**

```
  A.4(ii)  disjunct  (log X)^{1/16}/2 < |t − t₁|    a LOWER bound — "t is FAR"
             a free t₁ satisfies it trivially (choose t₁ distant) while the
             conclusion stays at full strength           ⇒ FATAL (not_mrtLemmaA4ii)
  A.6/A.7  hypothesis  t ∈ mrtT0 (mrtM f X) t₁ X X
             unfolds to  |t − t₁| ≤ (log X)^{1/16}   an UPPER bound — "t is NEAR"
             a free t₁ satisfies it at t₁ = t, which is each conclusion's
             WEAKEST instance, not its strongest       ⇒ not exploitable that way
```

⭐ **A.7's immunity at that point is KERNEL-BACKED, not argued:**
`mrtA7_exact_at_center` shows the bracketed difference is exactly `0` at `t₁ = t`.

⭐ **AND `mrtT0` CARRIES A SECOND GUARD THAT IS EASY TO MISS: it is `∅` in the
high-`M` branch**, so `t ∈ mrtT0 (mrtM f X) t₁ X X` *silently implies*
`mrtM f X < (1/8)·loglog X`.  A.6 and A.7 therefore carry the low-`M` condition
without stating it.  The two lemmas below make that implicit carriage explicit —
they are also the extraction steps any proof of A.6/A.7 will need.

⚠️ **HONEST LIMIT: this shows A.4(ii)'s exploit does not transfer. It does NOT
show A.6 is safe.** `t₁` there may still sit at the far edge `|t − t₁| =
(log X)^{1/16}`, which minimises A.6's RHS via the `1/(1 + |t − t₁|)` factor and
is its strongest instance. I neither refuted nor cleared that; it is named here so
it is not absorbed. -/

/-- **`mrtT0` is empty in the high-`M` branch** — by definition, but worth a name:
this is the guard that makes A.6/A.7's hypotheses carry low-`M` implicitly. -/
theorem mrtT0_eq_empty_of_high_M {M t₁ X T : ℝ}
    (hM : (1 / 8) * Real.log (Real.log X) ≤ M) :
    mrtT0 M t₁ X T = ∅ := by
  unfold mrtT0; rw [if_pos hM]

/-- **Membership in `mrtT0` FORCES the low-`M` branch.**  So A.6 and A.7 carry
`M(f;X) < ⅛·loglog X` without stating it — the hypothesis is vacuous otherwise. -/
theorem lt_of_mem_mrtT0 {M t₁ X T t : ℝ} (ht : t ∈ mrtT0 M t₁ X T) :
    M < (1 / 8) * Real.log (Real.log X) := by
  by_contra h
  rw [mrtT0_eq_empty_of_high_M (not_lt.mp h)] at ht
  simp at ht

/-- **Membership in `mrtT0` yields the near-distance bound**, the form A.6/A.7's
proofs actually consume. -/
theorem abs_sub_le_of_mem_mrtT0 {M t₁ X T t : ℝ} (ht : t ∈ mrtT0 M t₁ X T) :
    |t - t₁| ≤ (Real.log X) ^ ((1 : ℝ) / 16) := by
  have h := lt_of_mem_mrtT0 ht
  unfold mrtT0 at ht
  rw [if_neg (not_le.mpr h)] at ht
  exact ht.2

/-! ## The A.4(ii) repair: pin `t₁` to the minimiser

`not_mrtLemmaA4ii` refuted `MRTLemmaA4ii` because `t₁` floats free. The repair
named there — **constrain `t₁`, do not weaken the conclusion** — is carried out
here. MRT's `t₁` is *the value attaining the minimum*, and `exists_min_pretDistSq`
already supplies it, so the fix costs one hypothesis and no new machinery.

The refuting witness is excluded by that hypothesis: it used `f ≡ 1` with
`t₁ = (log X)^{1/16}/2 + 1`, where `mrtM f X = 0` (attained at `s = 0`, since
`costwist 0 ≡ 1`) while `pretDistSq f (costwist t₁) X > 0` — so that `t₁` is not a
minimiser. *(Stated as the reason, not as a Lean proof: exhibiting `> 0` needs a
`cos` bound at a specific argument, which is not what this section is for.)*

⭐ **AND THE REPAIR BUYS SOMETHING, WHICH IS THE POINT — it is not merely
witness-proofing.** With `t₁` pinned, the far branch's *centre cap* — the `S` that
`dist_recenter_sq` consumes — becomes DERIVABLE rather than assumed:
`mrtA4ii_far_centre_cap` below. Free `t₁` could not supply it at all, because a
free `t₁` says nothing about `pretDistSq f (costwist t₁) X`. -/

/-- **A.4(ii), REPAIRED.**  Identical to `MRTLemmaA4ii` except that `t₁` is now
required to attain `mrtM f X` — MRT's own reading of `t₁`. -/
def MRTLemmaA4iiFixed : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X → 0 < ε →
    |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
    ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
      ∨ (Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁|) →
      (1 / 6 - 1 / (3 * Real.pi) - ε) * Real.log (Real.log X)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-- **The repaired statement's HIGH-`M` ARM still goes through unchanged** — that
branch never mentions `t₁`, so pinning it costs nothing there. -/
theorem mrtA4iiFixed_high_M (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ)
    (X t ε : ℝ) (hf : ∀ n, ‖f n‖ ≤ 1) (hXe : Real.exp 1 ≤ X) (htX : |t| ≤ X)
    (hε : 0 < ε) (hM : (1 / 8) * Real.log (Real.log X) ≤ mrtM f X) :
    (1 / 6 - 1 / (3 * Real.pi) - ε) * Real.log (Real.log X)
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X :=
  mrtA4ii_high_M_target f Pseq Qseq 𝒥 X t ε hf hXe htX hε hM

/-- ⭐ **WHAT THE REPAIR BUYS: the far branch's CENTRE CAP is now derivable.**
In the far branch the first disjunct fails, so `mrtM f X < ⅛·loglog X`; with `t₁`
pinned to the minimiser this transfers to the centre distance itself, which is
exactly the `S` that `dist_recenter_sq` consumes.  **A free `t₁` could not supply
this at all** — it says nothing about `pretDistSq f (costwist t₁) X`. -/
theorem mrtA4ii_far_centre_cap {f : ℕ → ℂ} {X t₁ : ℝ}
    (hmin : pretDistSq f (costwist t₁) X = mrtM f X)
    (hlow : ¬ ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X)) :
    pretDistSq f (costwist t₁) X < (1 / 8) * Real.log (Real.log X) := by
  rw [hmin]; exact not_le.mp hlow

/-! ## The A.7 sign: a check that actually DISCRIMINATES

`mrtA7_exact_at_center` evaluates A.7's main-term factor at `t = t₁`. It is a true
theorem and it is **not** a discriminator: MRT's Lemma A.7 statement (A.8) writes
the factor as `X^{i(t−t₁)}/(1 + i(t−t₁))` while its own proof, same page, writes
`X^{i(t₁−t)}/(1 + i(t₁−t))` — and **at `t = t₁` both give exactly `1`.** A control
must disagree with the test case to discriminate; that one agreed with both.

The general reason is below: **the two candidates are COMPLEX CONJUGATES of each
other.** So they coincide exactly where the factor is real — which includes the
centre `t = t₁` — and differ elsewhere. *Testing a formula at its fixed point
tests nothing about its sign.*

⛔ Which convention MRT intend is left OPEN here, not silently chosen. Partial
summation with `s = t − t₁` gives `∫₁^X u^{−is}dA(u) ≈ X^{−is}A(X)/(1−is)`, i.e.
the PROOF's form — but that is a heuristic (it assumes `A(u) ≈ (u/X)A(X)`), so it
is evidence, not a ruling. `MRTLemmaA7` still carries the STATEMENT's form. -/

/-- **The two candidate A.7 factors are complex conjugates.**  This is why any
check at a point where the factor is real cannot tell them apart. -/
theorem mrtA7_factor_conj (t t₁ X : ℝ) :
    (starRingEnd ℂ)
        (Complex.exp ((((t - t₁ : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
          / (1 + (((t - t₁ : ℝ) : ℂ)) * Complex.I))
      = Complex.exp ((((t₁ - t : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
          / (1 + (((t₁ - t : ℝ) : ℂ)) * Complex.I) := by
  rw [map_div₀, ← Complex.exp_conj]
  congr 1 <;> · push_cast; simp [Complex.conj_I]; ring_nf

/-- **And they genuinely DIFFER off the centre** — the concrete separation the
degenerate check could not provide.  At `t = 1`, `t₁ = 0`, `X = 1` the exponentials
collapse (`log 1 = 0`) and the two denominators `1 ± i` already separate. -/
theorem mrtA7_factors_differ :
    Complex.exp ((((1 - 0 : ℝ) : ℂ)) * Complex.I * ((Real.log 1 : ℝ) : ℂ))
        / (1 + (((1 - 0 : ℝ) : ℂ)) * Complex.I)
      ≠ Complex.exp ((((0 - 1 : ℝ) : ℂ)) * Complex.I * ((Real.log 1 : ℝ) : ℂ))
        / (1 + (((0 - 1 : ℝ) : ℂ)) * Complex.I) := by
  norm_num [Complex.ext_iff]

/-! ## MRT Lemma A.8 — the elementary half, with the MVT step carried as a hypothesis

`Lemma A.8` (p.27): `e^α + e^{−α} − 2cos θ ≤ exp(√(α²+θ²))` for all real `α, θ`.

MRT's proof has exactly two moving parts, and only one of them is elementary:

* **the MVT step** — `x ↦ e^{√x}` has derivative `½x^{−1/2}e^{√x}`, which
  differentiated again is minimised at `x = 1` with value `e/2`; the mean value
  theorem on `[α², α²+θ²]` then gives `e^{√(α²+θ²)} ≥ e^α + (e/2)θ²`.
  **This needs a `deriv` computation and a second-derivative minimisation — it is
  NOT class A, and it is carried below as the named hypothesis `hmvt`.**
* **the reduction** — `cos θ ≥ 1 − θ²/2` and `e^{−α} ≤ 1` collapse the claim to
  `2 − e^{−α} + θ²(e/2 − 1) ≥ 0`, immediate from `2 ≥ e^{−α}` and `e ≥ 2`.
  **That half is proved here, unconditionally.**

⚠️ I priced this lemma "class A/B, no arithmetic apparatus" from its STATEMENT
before reading its proof, and withdrew that. The split below is what the proof
actually contains; naming `hmvt` rather than hiding it keeps the remaining cost
visible instead of absorbed. -/

/-- **MRT Lemma A.8, reduced to its MVT step.**  Given the mean-value bound
`e^α + (e/2)θ² ≤ exp(√(α²+θ²))` (MRT's own first move, p.27), the rest of A.8 is
elementary: `cos θ ≥ 1 − θ²/2` and `e^{−α} ≤ 1` for `α ≥ 0`, then `e ≥ 2` makes
the `θ²` coefficient nonnegative. -/
theorem mrtA8_of_mvt (α θ : ℝ) (hα : 0 ≤ α)
    (hmvt : Real.exp α + (Real.exp 1 / 2) * θ ^ 2
              ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2))) :
    Real.exp α + Real.exp (-α) - 2 * Real.cos θ
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) := by
  have hcos : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hexp : Real.exp (-α) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  nlinarith [hmvt, hcos, hexp, he2, sq_nonneg θ]

/-- **A.8's MVT STEP — DISCHARGED, AND WITHOUT MRT's SECOND-DERIVATIVE MINIMISATION.**

MRT reach `e^{√(α²+θ²)} ≥ e^α + (e/2)θ²` by differentiating `x ↦ e^{√x}` twice and
minimising the derivative at `x = 1`.  That is avoidable.  With
`r = √(α²+θ²) ≥ α` and `r² = α² + θ²`, the claim is exactly

  `g α ≤ g r`   where `g x = e^x − (e/2)x²`,

and `g' x = e^x − e·x ≥ 0` is **one mathlib lemma**: `Real.add_one_le_exp` at
`x − 1` gives `x ≤ e^{x−1}`, i.e. `e·x ≤ e^x`.  Monotonicity then finishes it.

*The minimum of `e^x − e·x` is `0`, attained at `x = 1` — the same `x = 1` and the
same value `e/2` MRT locate by the second derivative.  The two routes meet at the
same constant; this one never has to compute a second derivative.* -/
theorem mrtA8_mvt_step (α θ : ℝ) (hα : 0 ≤ α) :
    Real.exp α + (Real.exp 1 / 2) * θ ^ 2
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) := by
  have key : ∀ x : ℝ, Real.exp 1 * x ≤ Real.exp x := by
    intro x
    have h := Real.add_one_le_exp (x - 1)
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)] at h
    linarith
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp y - (Real.exp 1 / 2) * y ^ 2)
      (Real.exp x - Real.exp 1 * x) x := by
    intro x
    have ha : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    have hb0 := (hasDerivAt_pow 2 x).const_mul (Real.exp 1 / 2)
    have hfix : (Real.exp 1 / 2) * ((2 : ℕ) * x ^ (2 - 1)) = Real.exp 1 * x := by
      push_cast
      ring
    rw [hfix] at hb0
    exact ha.sub hb0
  have hmono : Monotone (fun x : ℝ => Real.exp x - (Real.exp 1 / 2) * x ^ 2) := by
    refine monotone_of_deriv_nonneg (fun x => (hderiv x).differentiableAt) (fun x => ?_)
    rw [(hderiv x).deriv]
    linarith [key x]
  have hnn : (0 : ℝ) ≤ α ^ 2 + θ ^ 2 := by positivity
  have hr2 : Real.sqrt (α ^ 2 + θ ^ 2) ^ 2 = α ^ 2 + θ ^ 2 := Real.sq_sqrt hnn
  have hαr : α ≤ Real.sqrt (α ^ 2 + θ ^ 2) := by
    calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα).symm
      _ ≤ Real.sqrt (α ^ 2 + θ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg θ])
  have hstep : Real.exp α - (Real.exp 1 / 2) * α ^ 2
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2))
        - (Real.exp 1 / 2) * (Real.sqrt (α ^ 2 + θ ^ 2)) ^ 2 := hmono hαr
  rw [hr2] at hstep
  linarith

/-- **MRT LEMMA A.8, UNCONDITIONAL.**  `mrtA8_of_mvt` composed with the discharged
MVT step: `e^α + e^{−α} − 2cos θ ≤ exp(√(α²+θ²))` for `α ≥ 0`, no hypotheses. -/
theorem mrtA8 (α θ : ℝ) (hα : 0 ≤ α) :
    Real.exp α + Real.exp (-α) - 2 * Real.cos θ
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) :=
  mrtA8_of_mvt α θ hα (mrtA8_mvt_step α θ hα)

/-! ## MRT Lemma A.5 — the `T₁` bound, stated

Read from `1503.05121v3.pdf` **p.24** (not p.23; my earlier range read spanned both).

> **Lemma A.5.** Let `X ≥ Q ≥ P ≥ 2`. Let `t₁` be as above, `ε > 0` and let
> `𝒥 ⊆ {1,…,J}` and `G(s) = Σ_{X≤n≤2X} (g_𝒥(n)f(n)/nˢ)·1/(#{p ∈ [P,Q] : p ∣ n} + 1)`.
> Then, for any `t ∈ T₁`,
> `|G(1+it)| ≪ log Q/((log X)^{1/6−1/(3π)−ε}·log P)
>              + log X·exp(−(log X/(3 log Q))·log(log X/log Q))`

⭐ **The reciprocal block-divisor weight is the corpus's landed `blockOmega`:**
`#{p ∈ [P,Q] : p ∣ n}` is `blockOmega P Q n` by definition (`Decomp.lean:53–57`,
`n.primeFactors.filter (P ≤ p ∧ p ≤ Q)`), so no new counting object is needed.

⛔ **`t₁` IS CARRIED AS THE MINIMISER FROM THE OUTSET.** MRT's "let `t₁` be as
above" means the value attaining `mrtM f X`; `not_mrtLemmaA4ii` is what a free
`t₁` costs, and that lesson is applied here rather than repeated. Membership
`t ∈ mrtT1 …` supplies the rest of "as above".

⭐ **`ρ := 1/6 − 1/(3π) − ε` IS A.4(ii)'s CONSTANT** — MRT say so explicitly
(*"we had 1/16 in place of `ρ`"*), and their side condition `ρ/3 > 1/50` is this
file's landed `mrtA5_rho_margin`. One constant serves both lemmas.

⚠️ Nothing here proves A.5. MRT route it through **[17, Lemma 3]**, an EXTERNAL
citation, and note this was *"the only part in the proof [17, Proposition 1] that
needed `f` to be real-valued"* — a hypothesis this statement does NOT carry, and
a discharger may find it necessary. Flagged, not silently added. -/

/-- **MRT's `G(1+it)`** — the `T₁`-side Dirichlet sum with the reciprocal
block-divisor weight `1/(ω(n;P,Q) + 1)`.  `1/n^{1+it} = (1/n)·n^{−it}`, and
`n^{−it}` is the corpus's `costwist (−t)`. -/
noncomputable def mrtG (f : ℕ → ℂ) (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ)
    (P Q : ℕ) (X t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊,
    (gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n / (n : ℂ))
      / ((blockOmega P Q n : ℂ) + 1)

/-- **MRT Lemma A.5** — the `T₁` bound, as a predicate on the implied constant. -/
def MRTLemmaA5 (C : ℝ) : Prop :=
  ∀ (f : ℕ → ℂ) (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (P Q : ℕ) (X t t₁ ε : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ X → 0 < ε →
    |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
    t ∈ mrtT1 (mrtM f X) t₁ X X →
      ‖mrtG f 𝒥 Pseq Qseq P Q X t‖
        ≤ C * (Real.log Q
                  / ((Real.log X) ^ (1 / 6 - 1 / (3 * Real.pi) - ε) * Real.log P)
              + Real.log X
                  * Real.exp (-(Real.log X / (3 * Real.log Q))
                      * Real.log (Real.log X / Real.log Q)))

/-- **A.5 as a statement** — `∃ C > 0`, matching `MRTThmA1Statement` and
`MRTPropA3Statement`.  *Without the wrapper a reader can mistake `MRTLemmaA5 C`
for the lemma and assert it for a `C` nobody chose* — the defect fixed for A.6/A.7
at 04:15, applied here at birth. -/
def MRTLemmaA5Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTLemmaA5 C

/-! ## A.3's assembly — the `T₀` step MRT call "immediately implies"

MRT p.24, having stated display (A.7) `F(1+it) ≪ exp(−½M)/(1+|t−t₁|) + (log X)^{−1/16}`
for `t ∈ T₀`, write that it *"immediately implies"*

  `∫_{T₀} |F(1+it)|² dt ≪ 1/exp(M(f;X)) + (log X)^{1/16 − 2/16}`.

⭐ **THE UNSIMPLIFIED EXPONENT IS THE DERIVATION, WRITTEN DOWN.** `1/16 − 2/16` is
`−1/16`, so leaving it unsimplified is deliberate: **`+1/16` is the LENGTH of `T₀`
(its radius is `(log X)^{1/16}`) and `−2/16` is the second term SQUARED.** Reading
it as a single number `−1/16` loses exactly the information that says where each
half came from.

The step has three parts:
* `(a+b)² ≤ 2a² + 2b²` — pointwise, proved below as `mrtA3_T0_pointwise_sq`;
* `∫ dt/(1+|t−t₁|)² ≤ 2` over any interval — **NOT proved here**, and named so;
* `|T₀| ≤ 2(log X)^{1/16}` — the radius, available from `abs_sub_le_of_mem_mrtT0`.

⚠️ Only the first is landed. The integral fact is elementary (`∫₀^c (1+x)^{−2} =
1 − 1/(1+c) ≤ 1`) but needs interval-integral machinery, and I am not claiming it
by asserting it in prose. -/

/-- **The pointwise half of MRT's "immediately implies".**  From
`|F| ≤ A/(1+|u|) + B`, squaring costs only the factor `2` on each term:
`F² ≤ 2A²/(1+|u|)² + 2B²`.  *This is what makes the two halves of (A.7) integrate
separately.*

⭐ **NO NONNEGATIVITY HYPOTHESES.** I first stated this with `0 ≤ A` and `0 ≤ B`;
the unused-variable linter showed both were dead, and they are: `|F| ≥ 0` already
forces `A/(1+|u|) + B ≥ 0`. *The mirror of A.4(ii) — there the PROOF needed a
binder the statement lacked; here the STATEMENT carried binders the proof did not.
The linter found this one; a witness found that one.* -/
theorem mrtA3_T0_pointwise_sq {F A B u : ℝ}
    (hF : |F| ≤ A / (1 + |u|) + B) :
    F ^ 2 ≤ 2 * (A ^ 2 / (1 + |u|) ^ 2) + 2 * B ^ 2 := by
  have hu : (0 : ℝ) < 1 + |u| := by positivity
  have h1 : F ^ 2 ≤ (A / (1 + |u|) + B) ^ 2 := by
    rw [← sq_abs F]
    exact pow_le_pow_left₀ (abs_nonneg F) hF 2
  have h2 : (A / (1 + |u|) + B) ^ 2
      = A ^ 2 / (1 + |u|) ^ 2 + 2 * (A / (1 + |u|)) * B + B ^ 2 := by
    field_simp
    ring
  have h3 : 2 * (A / (1 + |u|)) * B
      ≤ (A / (1 + |u|)) ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (A / (1 + |u|) - B)]
  have h4 : (A / (1 + |u|)) ^ 2 = A ^ 2 / (1 + |u|) ^ 2 := by
    rw [div_pow]
  rw [h2] at h1
  rw [h4] at h3
  linarith

/-- **The exponent MRT leave unsimplified.**  `1/16 − 2/16 = −1/16`: the `+1/16`
is `T₀`'s length exponent and the `−2/16` is `(log X)^{−1/16}` squared. -/
theorem mrtA3_T0_exponent : (1 : ℝ) / 16 - 2 / 16 = -((1 : ℝ) / 16) := by norm_num

/-- **The integral fact A.3's `T₀` step needs — one-sided core.**  `∫₀^c (1+x)^{−2}
= 1 − 1/(1+c) ≤ 1` for `c ≥ 0`.  This is the half of MRT's *"immediately implies"*
that `mrtA3_T0_pointwise_sq` does not supply; naming it as a gap at 08:0x and then
closing it is the follow-through. -/
theorem integral_inv_one_add_sq_le_one {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in (0 : ℝ)..c, ((1 + x) ^ 2)⁻¹) ≤ 1 := by
  have hpos : ∀ x ∈ Set.uIcc (0 : ℝ) c, (0 : ℝ) < 1 + x := by
    intro x hx
    rw [Set.uIcc_of_le hc, Set.mem_Icc] at hx
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun y : ℝ => -(1 + y)⁻¹) (((1 + x) ^ 2)⁻¹) x := by
    intro x hx
    have hne : (1 + x) ≠ 0 := ne_of_gt (hpos x hx)
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h2 := h1.inv hne
    have hEq : -(1 : ℝ) / (1 + x) ^ 2 = -(((1 + x) ^ 2)⁻¹) := by
      rw [neg_div, one_div]
    rw [hEq] at h2
    have h3 := h2.neg
    rw [neg_neg] at h3
    exact h3
  have hcont : ContinuousOn (fun x : ℝ => ((1 + x) ^ 2)⁻¹) (Set.uIcc (0 : ℝ) c) := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + x := hpos x hx
    exact (((continuousAt_const.add continuousAt_id).pow 2).inv₀
      (pow_ne_zero 2 (ne_of_gt hx0))).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => ((1 + x) ^ 2)⁻¹) MeasureTheory.volume 0 c :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hcpos : (0 : ℝ) < 1 + c := by linarith
  have : (0 : ℝ) < (1 + c)⁻¹ := by positivity
  simp only [add_zero, inv_one]
  linarith

/-! ## Why MRT's A.7 sign discrepancy never bit them — and why it would bite us

The statement (A.8) and its own proof carry opposite signs in the renormalization
factor (`mrtA7_factor_conj` shows the two candidates are conjugates). **Nothing in
the paper resolves it, and the reason is that nothing in the paper NEEDS it
resolved.**

MRT p.25: *"Hence, thanks to Lemma A.7, Lemma A.6 follows once we have shown"* —
and the display that follows, (A.9), carries only `n^{−it₁}`: **the multiplier has
been DISCARDED**, because `|X^{iu}/(1 + iu)| = 1/√(1+u²) ≤ 1`.  That modulus is
**identical** under both conventions, since `u ↦ −u` leaves `u²` fixed.

🔑 ***THE SOURCE CAN TOLERATE THE AMBIGUITY BECAUSE IT ONLY EVER USES THE MODULUS.
A FORMALISATION CANNOT, BECAUSE IT STATES THE IDENTITY.*** `mrtA7_factors_differ`
exhibits two distinct values; `MRTLemmaA7` asserts one of them. **A formal
statement is strictly more sensitive than its source at exactly the points the
source never leans on** — and those are precisely the points where a transcription
error survives undetected, because the original had no reason to be careful there.

⇒ The flag stands as a TRANSCRIPTION question, and is now known to be
**immaterial to MRT's argument and material to ours.** -/

/-- **The two candidate A.7 factors have equal modulus** — immediate from
`mrtA7_factor_conj`, since conjugation is norm-preserving.  *This is exactly what
MRT's downstream step uses, and why their sign discrepancy never propagates.* -/
theorem mrtA7_factors_same_norm (t t₁ X : ℝ) :
    ‖Complex.exp ((((t - t₁ : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
        / (1 + (((t - t₁ : ℝ) : ℂ)) * Complex.I)‖
      = ‖Complex.exp ((((t₁ - t : ℝ) : ℂ)) * Complex.I * ((Real.log X : ℝ) : ℂ))
        / (1 + (((t₁ - t : ℝ) : ℂ)) * Complex.I)‖ := by
  rw [← mrtA7_factor_conj t t₁ X, RCLike.norm_conj]

/-- **MRT's display (A.9) is Lemma A.6 evaluated AT THE CENTRE.**  MRT p.25 reduce
A.6 to

  `U := (1/X)|∑_{𝒥} (−1)^{#𝒥} ∑_{n≤X} g_𝒥(n)f(n)n^{−it₁}| ≪ exp(−½M(f;X)) + (log X)^{−1/16}`

and that is exactly `MRTLemmaA6` at `t := t₁`: the factor `1/(1+|t−t₁|)` becomes
`1/(1+0) = 1`, and the two-term right-hand side is unchanged otherwise.

⭐ **This is what Lemma A.7 BUYS, stated as a Lean step rather than as prose: A.7
moves the problem from EVERY `t ∈ T₀` to the SINGLE POINT `t₁`.**  The membership
`t₁ ∈ T₀` is immediate — `|t₁ − t₁| = 0` clears the radius — but it needs `T₀`'s
low-`M` branch, which `mrtT0` encodes by being `∅` otherwise. -/
theorem mrtA6_at_centre {C : ℝ} (hA6 : MRTLemmaA6 C)
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (X t₁ : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hX : 0 < X) (hlogX : 0 ≤ Real.log X)
    (ht₁ : |t₁| ≤ X)
    (hlow : ¬ ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X)) :
    ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t₁) n‖
      ≤ C * (Real.exp (-(1 / 2) * mrtM f X)
              + (Real.log X) ^ (-(1 : ℝ) / 16)) := by
  have hmem : t₁ ∈ mrtT0 (mrtM f X) t₁ X X := by
    unfold mrtT0
    rw [if_neg hlow]
    refine ⟨ht₁, ?_⟩
    simp only [sub_self, abs_zero]
    exact Real.rpow_nonneg hlogX _
  have h := hA6 f Pseq Qseq J X t₁ t₁ hf hX hmem
  simpa using h

/-- **`T₀` sits inside the centred interval of radius `(log X)^{1/16}`.**  The
third part of MRT's *"immediately implies"*, in the form an integral bound
consumes: `abs_sub_le_of_mem_mrtT0` gives the DISTANCE, and an integral over `T₀`
needs a SET INCLUSION.  *Same fact, different shape — and the shape is what makes
it usable.* -/
theorem mrtT0_subset_Icc {M t₁ X T : ℝ} :
    mrtT0 M t₁ X T
      ⊆ Set.Icc (t₁ - (Real.log X) ^ ((1 : ℝ) / 16))
          (t₁ + (Real.log X) ^ ((1 : ℝ) / 16)) := by
  intro t ht
  have h := abs_sub_le_of_mem_mrtT0 ht
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **And its length.**  `|T₀| ≤ 2(log X)^{1/16}` — the factor MRT's `+1/16`
exponent came from, now available as the measure of the enclosing interval rather
than as a remark. -/
theorem mrtT0_Icc_length {t₁ X : ℝ} :
    (t₁ + (Real.log X) ^ ((1 : ℝ) / 16)) - (t₁ - (Real.log X) ^ ((1 : ℝ) / 16))
      = 2 * (Real.log X) ^ ((1 : ℝ) / 16) := by ring

/-- **Mirror of `integral_inv_one_add_sq_le_one` on the left half.**
`∫_{−r}^{0} (1−x)^{−2} = 1 − 1/(1+r) ≤ 1`.  Same antiderivative technique, with
`(1−y)⁻¹` in place of `−(1+y)⁻¹`; proving it directly is cheaper than transporting
the right-hand lemma across `x ↦ −x`. -/
theorem integral_inv_one_sub_sq_le_one {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in (-r)..(0 : ℝ), ((1 - x) ^ 2)⁻¹) ≤ 1 := by
  have hle : (-r : ℝ) ≤ 0 := by linarith
  have hpos : ∀ x ∈ Set.uIcc (-r) (0 : ℝ), (0 : ℝ) < 1 - x := by
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    linarith [hx.2]
  have hderiv : ∀ x ∈ Set.uIcc (-r) (0 : ℝ),
      HasDerivAt (fun y : ℝ => (1 - y)⁻¹) (((1 - x) ^ 2)⁻¹) x := by
    intro x hx
    have hne : (1 - x) ≠ 0 := ne_of_gt (hpos x hx)
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have h2 := h1.inv hne
    have hEq : -(-1 : ℝ) / (1 - x) ^ 2 = ((1 - x) ^ 2)⁻¹ := by
      rw [neg_neg, one_div]
    rw [hEq] at h2
    exact h2
  have hcont : ContinuousOn (fun x : ℝ => ((1 - x) ^ 2)⁻¹) (Set.uIcc (-r) (0 : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 - x := hpos x hx
    exact (((continuousAt_const.sub continuousAt_id).pow 2).inv₀
      (pow_ne_zero 2 (ne_of_gt hx0))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hrp : (0 : ℝ) < 1 + r := by linarith
  have : (0 : ℝ) < (1 + r)⁻¹ := by positivity
  simp only [sub_zero, inv_one, sub_neg_eq_add]
  linarith

/-- **The two-sided form: `∫_{−r}^{r} (1+|x|)^{−2} ≤ 2`.**  This is the quantity
A.3's `T₀` step actually consumes, after shifting by `t₁`.  Split at `0`: on
`[0,r]` the integrand is `(1+x)^{−2}`, on `[−r,0]` it is `(1−x)^{−2}`, and each
half is at most `1`. -/
theorem integral_inv_one_add_abs_sq_le_two {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in (-r)..r, ((1 + |x|) ^ 2)⁻¹) ≤ 2 := by
  have hcont : Continuous (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) := by
    have h1 : Continuous (fun x : ℝ => (1 + |x|) ^ 2) := by fun_prop
    refine h1.inv₀ (fun x => ?_)
    have hx : (0 : ℝ) < 1 + |x| := by positivity
    positivity
  have hsplit : (∫ x in (-r)..r, ((1 + |x|) ^ 2)⁻¹)
      = (∫ x in (-r)..(0 : ℝ), ((1 + |x|) ^ 2)⁻¹)
        + ∫ x in (0 : ℝ)..r, ((1 + |x|) ^ 2)⁻¹ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hright : (∫ x in (0 : ℝ)..r, ((1 + |x|) ^ 2)⁻¹) ≤ 1 := by
    have hcongr : (∫ x in (0 : ℝ)..r, ((1 + |x|) ^ 2)⁻¹)
        = ∫ x in (0 : ℝ)..r, ((1 + x) ^ 2)⁻¹ := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le hr, Set.mem_Icc] at hx
      rw [abs_of_nonneg hx.1]
    rw [hcongr]
    exact integral_inv_one_add_sq_le_one hr
  have hleft : (∫ x in (-r)..(0 : ℝ), ((1 + |x|) ^ 2)⁻¹) ≤ 1 := by
    have hcongr : (∫ x in (-r)..(0 : ℝ), ((1 + |x|) ^ 2)⁻¹)
        = ∫ x in (-r)..(0 : ℝ), ((1 - x) ^ 2)⁻¹ := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith : (-r : ℝ) ≤ 0), Set.mem_Icc] at hx
      rw [abs_of_nonpos hx.2]
      ring_nf
    rw [hcongr]
    exact integral_inv_one_sub_sq_le_one hr
  rw [hsplit]
  linarith

/-- **Centred at `t₁`: `∫_{t₁−r}^{t₁+r} (1+|t−t₁|)^{−2} dt ≤ 2`.**  The two-sided
bound moved onto `T₀`'s own centre — the last shape change between the landed
integral facts and what A.3's `T₀` assembly consumes.  Pure translation:
`intervalIntegral.integral_comp_sub_right` carries `t ↦ t − t₁` and the endpoints
`t₁ ∓ r` become `∓r`. -/
theorem integral_inv_one_add_abs_sub_sq_le_two {t₁ r : ℝ} (hr : 0 ≤ r) :
    (∫ t in (t₁ - r)..(t₁ + r), ((1 + |t - t₁|) ^ 2)⁻¹) ≤ 2 := by
  have h := intervalIntegral.integral_comp_sub_right
    (a := t₁ - r) (b := t₁ + r) (f := fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) t₁
  have e1 : t₁ - r - t₁ = -r := by ring
  have e2 : t₁ + r - t₁ = r := by ring
  rw [e1, e2] at h
  rw [h]
  exact integral_inv_one_add_abs_sq_le_two hr

/-- **A.3's `T₀` STEP, ASSEMBLED (interval form).**  MRT's *"immediately implies"*,
composed from the four landed pieces: from `|F| ≤ A/(1+|t−t₁|) + B` on the centred
interval,

  `∫_{t₁−r}^{t₁+r} F² ≤ 4A² + 4B²r`.

With `A = exp(−½M)`, `B = (log X)^{−1/16}` and `r = (log X)^{1/16}` this is
`4exp(−M) + 4(log X)^{−1/16}` — MRT's `1/exp(M) + (log X)^{1/16−2/16}` up to the
absolute constant, and **the `+1/16` in their unsimplified exponent is exactly the
`r` in the second term here.**

⚠️ Interval form, with integrability of `F²` taken as a hypothesis. `T₀` itself is
a SET; `mrtT0_subset_Icc` places it inside this interval, and a set-integral
version needs `setIntegral` monotonicity, which is NOT done here. -/
theorem mrtA3_T0_integral_bound {F : ℝ → ℝ} {A B t₁ r : ℝ} (hr : 0 ≤ r)
    (hint : IntervalIntegrable (fun t => F t ^ 2) MeasureTheory.volume (t₁ - r) (t₁ + r))
    (hF : ∀ t ∈ Set.Icc (t₁ - r) (t₁ + r), |F t| ≤ A / (1 + |t - t₁|) + B) :
    (∫ t in (t₁ - r)..(t₁ + r), F t ^ 2) ≤ 4 * A ^ 2 + 4 * B ^ 2 * r := by
  have hab : t₁ - r ≤ t₁ + r := by linarith
  have hcont : Continuous (fun t : ℝ => ((1 + |t - t₁|) ^ 2)⁻¹) := by
    have h1 : Continuous (fun t : ℝ => (1 + |t - t₁|) ^ 2) := by fun_prop
    refine h1.inv₀ (fun t => ?_)
    have : (0 : ℝ) < 1 + |t - t₁| := by positivity
    positivity
  have h1int : IntervalIntegrable (fun t : ℝ => 2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹)
      MeasureTheory.volume (t₁ - r) (t₁ + r) :=
    ((hcont.const_smul (2 * A ^ 2)).intervalIntegrable _ _)
  have h2int : IntervalIntegrable (fun _ : ℝ => 2 * B ^ 2)
      MeasureTheory.volume (t₁ - r) (t₁ + r) :=
    intervalIntegrable_const
  have hGint : IntervalIntegrable
      (fun t : ℝ => 2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹ + 2 * B ^ 2)
      MeasureTheory.volume (t₁ - r) (t₁ + r) := h1int.add h2int
  have hmono : (∫ t in (t₁ - r)..(t₁ + r), F t ^ 2)
      ≤ ∫ t in (t₁ - r)..(t₁ + r), (2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹ + 2 * B ^ 2) := by
    refine intervalIntegral.integral_mono_on hab hint hGint (fun t ht => ?_)
    have hp := mrtA3_T0_pointwise_sq (hF t ht)
    have : 2 * (A ^ 2 / (1 + |t - t₁|) ^ 2) = 2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]; ring
    linarith [hp, this.ge, this.le]
  have hsplit : (∫ t in (t₁ - r)..(t₁ + r), (2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹ + 2 * B ^ 2))
      = (∫ t in (t₁ - r)..(t₁ + r), 2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹)
        + ∫ _ in (t₁ - r)..(t₁ + r), (2 * B ^ 2) :=
    intervalIntegral.integral_add h1int h2int
  have hconst : (∫ _ in (t₁ - r)..(t₁ + r), (2 * B ^ 2)) = 2 * r * (2 * B ^ 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring_nf
  have hfirst : (∫ t in (t₁ - r)..(t₁ + r), 2 * A ^ 2 * ((1 + |t - t₁|) ^ 2)⁻¹)
      ≤ 2 * A ^ 2 * 2 := by
    rw [intervalIntegral.integral_const_mul]
    have hA : (0 : ℝ) ≤ 2 * A ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (integral_inv_one_add_abs_sub_sq_le_two hr) hA
  rw [hsplit, hconst] at hmono
  nlinarith [hmono, hfirst]

/-- **A.3's `T₀` STEP OVER `T₀` ITSELF — the set version.**  MRT integrate over the
SET `T₀`, not over an interval; `mrtT0_subset_Icc` puts `T₀` inside the centred
interval and the integrand `F²` is nonnegative, so `setIntegral_mono_set` carries
`mrtA3_T0_integral_bound` across:

  `∫_{T₀} F² ≤ ∫_{Icc} F² = ∫_{Ioc} F² = ∫_{t₁−r}^{t₁+r} F² ≤ 4A² + 4B²r`.

*The `Icc → Ioc` hop is the null-set bookkeeping `intervalIntegral.integral_of_le`
forces; `integral_Icc_eq_integral_Ioc` supplies it.* -/
theorem mrtA3_T0_setIntegral_bound {F : ℝ → ℝ} {A B t₁ r : ℝ} {M X T : ℝ}
    (hr : 0 ≤ r) (hrX : (Real.log X) ^ ((1 : ℝ) / 16) ≤ r)
    (hIcc : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (Set.Icc (t₁ - r) (t₁ + r)) MeasureTheory.volume)
    (hint : IntervalIntegrable (fun t => F t ^ 2) MeasureTheory.volume (t₁ - r) (t₁ + r))
    (hF : ∀ t ∈ Set.Icc (t₁ - r) (t₁ + r), |F t| ≤ A / (1 + |t - t₁|) + B) :
    (∫ t in mrtT0 M t₁ X T, F t ^ 2) ≤ 4 * A ^ 2 + 4 * B ^ 2 * r := by
  have hab : t₁ - r ≤ t₁ + r := by linarith
  have hsub : mrtT0 M t₁ X T ⊆ Set.Icc (t₁ - r) (t₁ + r) := by
    intro t ht
    have h := abs_sub_le_of_mem_mrtT0 ht
    rw [abs_le] at h
    exact ⟨by linarith [h.1, hrX], by linarith [h.2, hrX]⟩
  have hstep : (∫ t in mrtT0 M t₁ X T, F t ^ 2)
      ≤ ∫ t in Set.Icc (t₁ - r) (t₁ + r), F t ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hIcc ?_ hsub.eventuallyLE
    filter_upwards with t using sq_nonneg (F t)
  have hIccIoc : (∫ t in Set.Icc (t₁ - r) (t₁ + r), F t ^ 2)
      = ∫ t in Set.Ioc (t₁ - r) (t₁ + r), F t ^ 2 :=
    MeasureTheory.integral_Icc_eq_integral_Ioc
  have hIv : (∫ t in (t₁ - r)..(t₁ + r), F t ^ 2)
      = ∫ t in Set.Ioc (t₁ - r) (t₁ + r), F t ^ 2 :=
    intervalIntegral.integral_of_le hab
  have hfin := mrtA3_T0_integral_bound hr hint hF
  rw [hIv] at hfin
  rw [hIccIoc] at hstep
  linarith

/-- **`T₁` is measurable.**  Both branches of `mrtT1` are: the high-`M` branch is
the closed band `{|t| ≤ T}`, and the low-`M` branch intersects it with the open
`{(log X)^{1/16} < |t − t₁|}`.  Needed because `setIntegral_union` asks for
measurability of its SECOND set. -/
theorem measurableSet_mrtT1 (M t₁ X T : ℝ) : MeasurableSet (mrtT1 M t₁ X T) := by
  have hband : MeasurableSet {t : ℝ | |t| ≤ T} :=
    measurableSet_le (by fun_prop) measurable_const
  have hfar : MeasurableSet {t : ℝ | (Real.log X) ^ ((1 : ℝ) / 16) < |t - t₁|} :=
    measurableSet_lt measurable_const (by fun_prop)
  unfold mrtT1
  split_ifs
  · exact hband
  · exact hband.inter hfar

/-- `T₀` is measurable — the companion to `measurableSet_mrtT1`. -/
theorem measurableSet_mrtT0 (M t₁ X T : ℝ) : MeasurableSet (mrtT0 M t₁ X T) := by
  have hband : MeasurableSet {t : ℝ | |t| ≤ T} :=
    measurableSet_le (by fun_prop) measurable_const
  have hnear : MeasurableSet {t : ℝ | |t - t₁| ≤ (Real.log X) ^ ((1 : ℝ) / 16)} :=
    measurableSet_le (by fun_prop) measurable_const
  unfold mrtT0
  split_ifs
  · exact MeasurableSet.empty
  · exact hband.inter hnear

/-- The majorant `A/(1+|t−t₁|) + B` is continuous — its denominator is `≥ 1`, so
there is no side condition to discharge anywhere. -/
theorem continuous_a3_majorant (A B t₁ : ℝ) :
    Continuous (fun t : ℝ => A / (1 + |t - t₁|) + B) := by
  have hden : Continuous (fun t : ℝ => 1 + |t - t₁|) := by fun_prop
  have hne : ∀ t : ℝ, (1 : ℝ) + |t - t₁| ≠ 0 := fun t => by positivity
  exact (continuous_const.div hden hne).add continuous_const

/-- **THE `T₀` INTEGRAL BOUND THAT LEMMA A.6 CAN ACTUALLY FEED.**  Identical
conclusion to `mrtA3_T0_setIntegral_bound`, but the pointwise hypothesis is
required **only on `T₀`** rather than on the enclosing interval.

⛔ **THIS IS THE VERSION THE CHAIN NEEDS, AND THE DIFFERENCE IS NOT COSMETIC.**
`MRTLemmaA6` bounds the twisted sum for `t ∈ mrtT0` and says *nothing whatever*
off `T₀`; `mrtT0 ⊆ Icc (t₁−r) (t₁+r)` runs the WRONG WAY to transport a
hypothesis, so `mrtA3_T0_setIntegral_bound`'s `hF` could never be discharged from
A.6.  The repair is to enlarge the domain **on the majorant** — which is defined
and nonnegative everywhere — instead of on `F`, so the pointwise bound is only
ever used where A.6 actually supplies it.

`0 ≤ A` and `0 ≤ B` are genuinely needed (the majorant must dominate itself) and
are free in the application: A.6 delivers `A = C·exp(−M/2)`, `B = C·(log X)^{−1/16}`. -/
theorem mrtA3_T0_setIntegral_bound_onT0 {F : ℝ → ℝ} {A B t₁ r : ℝ} {M X T : ℝ}
    (hr : 0 ≤ r) (hrX : (Real.log X) ^ ((1 : ℝ) / 16) ≤ r)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hint : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT0 M t₁ X T) MeasureTheory.volume)
    (hF : ∀ t ∈ mrtT0 M t₁ X T, |F t| ≤ A / (1 + |t - t₁|) + B) :
    (∫ t in mrtT0 M t₁ X T, F t ^ 2) ≤ 4 * A ^ 2 + 4 * B ^ 2 * r := by
  have hab : t₁ - r ≤ t₁ + r := by linarith
  have hGcont : Continuous (fun t : ℝ => A / (1 + |t - t₁|) + B) :=
    continuous_a3_majorant A B t₁
  have hGnn : ∀ t : ℝ, 0 ≤ A / (1 + |t - t₁|) + B := by
    intro t
    have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
    have hq : 0 ≤ A / (1 + |t - t₁|) := div_nonneg hA hd.le
    linarith
  have hsub : mrtT0 M t₁ X T ⊆ Set.Icc (t₁ - r) (t₁ + r) := by
    intro t ht
    have h := abs_sub_le_of_mem_mrtT0 ht
    rw [abs_le] at h
    exact ⟨by linarith [h.1, hrX], by linarith [h.2, hrX]⟩
  have hGsqIcc : MeasureTheory.IntegrableOn (fun t => (A / (1 + |t - t₁|) + B) ^ 2)
      (Set.Icc (t₁ - r) (t₁ + r)) MeasureTheory.volume :=
    (hGcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hGsqT0 : MeasureTheory.IntegrableOn (fun t => (A / (1 + |t - t₁|) + B) ^ 2)
      (mrtT0 M t₁ X T) MeasureTheory.volume := hGsqIcc.mono_set hsub
  have h1 : (∫ t in mrtT0 M t₁ X T, F t ^ 2)
      ≤ ∫ t in mrtT0 M t₁ X T, (A / (1 + |t - t₁|) + B) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_on hint hGsqT0 (measurableSet_mrtT0 _ _ _ _) ?_
    intro t ht
    have h := hF t ht
    calc F t ^ 2 = |F t| ^ 2 := (sq_abs (F t)).symm
      _ ≤ (A / (1 + |t - t₁|) + B) ^ 2 := by nlinarith [abs_nonneg (F t)]
  have h2 : (∫ t in mrtT0 M t₁ X T, (A / (1 + |t - t₁|) + B) ^ 2)
      ≤ ∫ t in Set.Icc (t₁ - r) (t₁ + r), (A / (1 + |t - t₁|) + B) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hGsqIcc ?_ hsub.eventuallyLE
    filter_upwards with t using sq_nonneg _
  have h3 : (∫ t in Set.Icc (t₁ - r) (t₁ + r), (A / (1 + |t - t₁|) + B) ^ 2)
      ≤ 4 * A ^ 2 + 4 * B ^ 2 * r := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    refine mrtA3_T0_integral_bound hr ((hGcont.pow 2).intervalIntegrable _ _) ?_
    intro t _
    exact le_of_eq (abs_of_nonneg (hGnn t))
  linarith

/-- `T₀` grows with the band radius: `T ≤ T'` gives `mrtT0 M t₁ X T ⊆ mrtT0 M t₁ X T'`.
The `if` condition does not mention `T`, so both branches are immediate. -/
theorem mrtT0_mono_T {M t₁ X T T' : ℝ} (h : T ≤ T') :
    mrtT0 M t₁ X T ⊆ mrtT0 M t₁ X T' := by
  unfold mrtT0
  split_ifs
  · exact Set.Subset.rfl
  · exact fun t ht => ⟨le_trans ht.1 h, ht.2⟩

/-- **A.3's `T₀` SIDE, DERIVED FROM LEMMA A.6 RATHER THAN FROM AN ASSUMED BOUND.**
This is the composition the chain was missing: A.6 supplies the pointwise estimate,
`mrtA3_T0_setIntegral_bound_onT0` turns it into the integral bound, and `mrtT0_mono_T`
carries A.6's `t ∈ mrtT0 … X X` down to the split's `t ∈ mrtT0 … X T`.

⭐ **`T ≤ X` IS THE HYPOTHESIS THAT MAKES THE TRANSFER LEGAL, AND IT IS MRT's OWN.**
Their proof opens *"Since the mean value theorem gives the bound `O(T/X + 1)`, we can
assume `T ≤ X/2`"* (p. 23) — the large-`T` range is disposed of separately, which is
exactly why the `T/(X/Q₁) + 1` factor stands in front of A.3's bracket.  `MRTPropA3`
as stated quantifies `∀ T, 1 ≤ T` with **no upper bound**, so a full proof of it must
branch: this appendix argument for `T ≤ X/2`, the mean value theorem above it. -/
theorem mrtA3_T0_bound_of_A6 {C : ℝ} {F : ℝ → ℝ} (hC : 0 ≤ C) (hA6 : MRTLemmaA6 C)
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) {X T t₁ r : ℝ}
    (hFdef : ∀ t : ℝ, F t = ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n‖)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hX : 0 < X) (hlogX : 0 ≤ Real.log X) (hTX : T ≤ X)
    (hr : 0 ≤ r) (hrX : (Real.log X) ^ ((1 : ℝ) / 16) ≤ r)
    (hint : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT0 (mrtM f X) t₁ X T) MeasureTheory.volume) :
    (∫ t in mrtT0 (mrtM f X) t₁ X T, F t ^ 2)
      ≤ 4 * (C * Real.exp (-(1 / 2) * mrtM f X)) ^ 2
        + 4 * (C * (Real.log X) ^ (-(1 : ℝ) / 16)) ^ 2 * r := by
  refine mrtA3_T0_setIntegral_bound_onT0 hr hrX
    (mul_nonneg hC (Real.exp_nonneg _))
    (mul_nonneg hC (Real.rpow_nonneg hlogX _)) hint ?_
  intro t ht
  have hmem : t ∈ mrtT0 (mrtM f X) t₁ X X := mrtT0_mono_T hTX ht
  have h := hA6 f Pseq Qseq J X t t₁ hf hX hmem
  rw [hFdef t, abs_of_nonneg (norm_nonneg _)]
  have hring : C * (Real.exp (-(1 / 2) * mrtM f X) / (1 + |t - t₁|)
        + (Real.log X) ^ (-(1 : ℝ) / 16))
      = C * Real.exp (-(1 / 2) * mrtM f X) / (1 + |t - t₁|)
        + C * (Real.log X) ^ (-(1 : ℝ) / 16) := by ring
  linarith [h, hring.symm.le, hring.le]

/-! ## MRT's OTHER branch — the mean value theorem, and it is already in the corpus

MRT's A.3 proof opens *"Since the mean value theorem gives the bound `O(T/X + 1)`, we
can assume `T ≤ X/2`"*.  That disposal is not new analysis: the corpus landed the
Montgomery–Vaughan L² mean value theorem for Finset-indexed Dirichlet polynomials as
`dpolyS_l2_mvt_final` (`Salt/MR/MVHilbertFinset.lean`, unconditional).

The only thing between it and `dpolyA` is a *shape*: `dpolyS` sums `aₙ·n^{it}`, while
`dpolyA` sums `aₘ·m^{−1−it}`.  They are the same object at reciprocal-weighted
coefficients and reflected `t`. -/

/-- **`dpolyA` IS `dpolyS`**, at coefficients `aₙ/n` and reflected `t`:
`∑_{m∈s} aₘ·m^{−1−it} = ∑_{m∈s} (aₘ/m)·m^{i(−t)}`. -/
theorem dpolyA_eq_dpolyS (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (t : ℝ) :
    dpolyA a s t = dpolyS s (fun n => a n / (n : ℂ)) (-t) := by
  unfold dpolyA dpolyS
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hs m hm; omega)
  have key : Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * ((Real.log m : ℝ) : ℂ))
      = (Complex.exp (((Real.log m : ℝ) : ℂ) * ((t : ℂ) * Complex.I)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hE : Complex.exp (((Real.log m : ℝ) : ℂ) * ((t : ℂ) * Complex.I)) ≠ 0 :=
    Complex.exp_ne_zero _
  rw [Complex.cpow_add _ _ hm0, Complex.cpow_one, Complex.cpow_def_of_ne_zero hm0,
    ← Complex.natCast_log, key]
  field_simp

/-- **THE MEAN VALUE THEOREM FOR `dpolyA`** — MRT's large-`T` branch, delivered from the
corpus's landed Montgomery–Vaughan massif rather than from new analysis.  This is the
estimate that lets MRT *"assume `T ≤ X/2`"*, and it is what puts the `T/(X/Q₁) + 1`
factor in front of A.3's bracket. -/
theorem dpolyA_l2_mvt (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |Real.log i - Real.log j|) :
    (∫ t in (-T)..T, ‖dpolyA a s t‖ ^ 2)
      ≤ (2 * T + 2 * Real.pi / δ) * ∑ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 := by
  calc (∫ t in (-T)..T, ‖dpolyA a s t‖ ^ 2)
      = ∫ t in (-T)..T, ‖dpolyS s (fun n => a n / (n : ℂ)) (-t)‖ ^ 2 := by
        simp only [dpolyA_eq_dpolyS a s hs]
    _ = ∫ t in (-T)..T, ‖dpolyS s (fun n => a n / (n : ℂ)) t‖ ^ 2 :=
        dpolyS_meanSq_reflect s (fun n => a n / (n : ℂ)) T
    _ ≤ (2 * T + 2 * Real.pi / δ) * ∑ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 :=
        dpolyS_l2_mvt_final s hs (fun n => a n / (n : ℂ)) T hδ hgap

/-- **THE MEAN VALUE THEOREM ON A DYADIC BLOCK.**  For `s ⊆ [1,N]` the frequency gap is
`1/N` (`log_gap_ge`, landed in `Salt/MR/MVHilbert.lean`), so
`∫_{-T}^{T}‖A(1+it)‖² ≤ (2T + 2πN)·∑_{n∈s}‖aₙ/n‖²`.  At A.3's `S ⊆ [X,2X]` take
`N = ⌊2X⌋`. -/
theorem dpolyA_l2_mvt_Icc (a : ℕ → ℂ) (s : Finset ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hs : ∀ n ∈ s, n ∈ Finset.Icc 1 N) (T : ℝ) :
    (∫ t in (-T)..T, ‖dpolyA a s t‖ ^ 2)
      ≤ (2 * T + 2 * Real.pi * N) * ∑ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNr
  have hone : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.1 (hs n hn)).1
  have hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (1 : ℝ) / (N : ℝ) ≤ |Real.log i - Real.log j| :=
    fun i hi j hj hij => log_gap_ge (hs i hi) (hs j hj) hij
  have h := dpolyA_l2_mvt a s hone T hδ hgap
  have hrw : 2 * Real.pi / (1 / (N : ℝ)) = 2 * Real.pi * (N : ℝ) := by
    field_simp
  rwa [hrw] at h

/-- **THE COEFFICIENT SUM ON A.3's BLOCK.**  With `‖aₙ‖ ≤ 1` and `n ≥ X` throughout `s`,
`∑_{n∈s}‖aₙ/n‖² ≤ #s / X²`.  Together with `dpolyA_l2_mvt_Icc` and `#S ≤ X + 1` this is
MRT's `O(T/X + 1)`. -/
theorem sum_sq_norm_div_le (a : ℕ → ℂ) (s : Finset ℕ) {X : ℝ} (hX : 0 < X)
    (ha : ∀ n ∈ s, ‖a n‖ ≤ 1) (hlow : ∀ n ∈ s, X ≤ (n : ℝ)) :
    ∑ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 ≤ (s.card : ℝ) / X ^ 2 := by
  have hterm : ∀ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 ≤ 1 / X ^ 2 := by
    intro n hn
    have hnX : X ≤ (n : ℝ) := hlow n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hX hnX
    have hX2 : (0 : ℝ) < X ^ 2 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h1 : ‖a n‖ ^ 2 ≤ 1 := by
      have hle := ha n hn
      nlinarith [norm_nonneg (a n)]
    have h2 : X ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    rw [norm_div, Complex.norm_natCast, div_pow, div_le_div_iff₀ hn2 hX2]
    nlinarith
  calc ∑ n ∈ s, ‖a n / (n : ℂ)‖ ^ 2 ≤ ∑ _n ∈ s, 1 / X ^ 2 := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) / X ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **MRT's LARGE-`T` BRANCH, ASSEMBLED: `O(T/X + 1)` FOR A DYADIC BLOCK.**  This is the
estimate MRT invoke in their opening sentence — *"Since the mean value theorem gives the
bound `O(T/X + 1)`, we can assume `T ≤ X/2`"* — with every constant explicit.

Taking `N = ⌊2X⌋` in `dpolyA_l2_mvt_Icc` gives the frequency-gap constant `2πN ≤ 4πX`,
and `sum_sq_norm_div_le` bounds the coefficient sum by `#S/X²`.  With `#S ≤ X + 1` on a
dyadic block the right-hand side is `≍ T/X + 1`, which is MRT's quote.

*Nothing here is conditional on A.5, A.6 or A.7: this branch of A.3 rests only on
Montgomery–Vaughan.* -/
theorem mrtA3_mvt_branch (f : ℕ → ℂ) (S : Finset ℕ) {X T : ℝ} (hX : 1 ≤ X) (hT : 0 ≤ T)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hSlow : ∀ n ∈ S, X ≤ (n : ℝ)) (hShigh : ∀ n ∈ S, (n : ℝ) ≤ 2 * X) :
    (∫ t in (-T)..T, ‖dpolyA f S t‖ ^ 2)
      ≤ (2 * T + 4 * Real.pi * X) * ((S.card : ℝ) / X ^ 2) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have h2X : (0 : ℝ) ≤ 2 * X := by linarith
  set N : ℕ := ⌊2 * X⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ 2 * X := Nat.floor_le h2X
  have hN1 : 1 ≤ N := by
    have : (1 : ℕ) ≤ ⌊2 * X⌋₊ := Nat.le_floor (by push_cast; linarith)
    simpa [hNdef] using this
  have hmem : ∀ n ∈ S, n ∈ Finset.Icc 1 N := by
    intro n hn
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have h := hSlow n hn
      have : (1 : ℝ) ≤ (n : ℝ) := le_trans hX h
      exact_mod_cast this
    · exact Nat.le_floor (hShigh n hn)
  have h1 := dpolyA_l2_mvt_Icc f S hN1 hmem T
  have h2 := sum_sq_norm_div_le f S hXpos (fun n _ => hf n) hSlow
  have hcoef : (0 : ℝ) ≤ (S.card : ℝ) / X ^ 2 := by positivity
  have hconst : (0 : ℝ) ≤ 2 * T + 2 * Real.pi * (N : ℝ) := by positivity
  have hstep1 : (2 * T + 2 * Real.pi * (N : ℝ)) * ∑ n ∈ S, ‖f n / (n : ℂ)‖ ^ 2
      ≤ (2 * T + 2 * Real.pi * (N : ℝ)) * ((S.card : ℝ) / X ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hconst
  have hstep2 : (2 * T + 2 * Real.pi * (N : ℝ)) * ((S.card : ℝ) / X ^ 2)
      ≤ (2 * T + 4 * Real.pi * X) * ((S.card : ℝ) / X ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hcoef
    nlinarith [Real.pi_pos]
  linarith [h1, hstep1, hstep2]

/-! ## A transcription gap in `MRTBands`, and why it is load-bearing

MRT set up A.3's bands as *"Consider a sequence of **increasing** intervals `[Pⱼ, Qⱼ]`,
`j ≥ 1`, such that …"* (p. 21), and only then list the three bullets — `Q₁ ≤ exp(√log X₀)`,
(A.1), (A.2).  **`MRTBands` transcribes the three bullets and drops the word "increasing":
it does not carry `Pⱼ ≤ Qⱼ`.**

⚠️ **THAT OMISSION IS NOT NEUTRAL FOR THE LARGE-`T` BRANCH.**  A.3's right-hand side
carries the factor `(log Q₁)^{1/3}/P₁^{1/6−η}`, and MRT's reduction *"the mean value
theorem gives `O(T/X + 1)`, so we can assume `T ≤ X/2`"* needs that bracket to be bounded
below once `T > X/2` — the MVT delivers `≍ T/X` and the target is `≍ (T·Q₁/X)·bracket`, so
the branch closes exactly when `Q₁·bracket ≫ 1`.  With `P₁ ≤ Q₁` that holds
(`Q₁·(log Q₁)^{1/3}/P₁^{1/6−η} ≥ P₁^{5/6+η}(log Q₁)^{1/3}`).  **With `P₁` free to exceed
`Q₁` it fails: `P₁ → ∞` at fixed `Q₁ = 2` drives the bracket to `0`.**

🔑 **The statement is NOT thereby false — the same accidental guard rescues it a third
time.**  If `Qⱼ < Pⱼ` the block is empty, so `blockOmega = 0`, so `MemS` fails and `S = ∅`
and both sides are `0`.  *That is now the third distinct degeneracy (`X = 1`, `Qseq 1 ≤ 1`,
`Qseq 1 < Pseq 1`) which `MRTPropA3` survives by emptying `S` rather than by carrying a
hypothesis.*  Recorded, not repaired: adding `Pⱼ ≤ Qⱼ` to `MRTBands` is a statement change
and belongs to a design session, not to this seat. -/

/-- A block whose top is below its bottom contains no primes. -/
theorem blockOmega_eq_zero_of_lt {P Q n : ℕ} (h : Q < P) : blockOmega P Q n = 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  omega

/-- **THE THIRD DEGENERACY.**  If the first band is inverted (`Qseq 1 < Pseq 1`) then no
`n` can meet `MemS`, so A.3's sifted set is empty and the proposition holds vacuously —
exactly as it does at `X = 1`. -/
theorem memS_false_of_band_inverted {Pseq Qseq : ℕ → ℕ} {J n : ℕ}
    (hJ : 1 ≤ J) (h : Qseq 1 < Pseq 1) : ¬ MemS Pseq Qseq J n := by
  intro hm
  have h1 := hm 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hJ⟩)
  rw [blockOmega_eq_zero_of_lt h] at h1
  omega

/-! ### The degeneracies, as a SET rather than one at a time

I found three ways `MRTPropA3` goes vacuous — `X = 1`, `Qseq 1 ≤ 1`, `Qseq 1 < Pseq 1` —
by stumbling on them one at a time, three beats running.  Checked as a *set* they are all
the same fact, and the set is strictly larger than the three:

**`S = ∅` whenever ANY band `[Pⱼ, Qⱼ]`, `j ≤ J`, contains no prime.**

`Qseq 1 ≤ 1` and `Qseq 1 < Pseq 1` are two special cases of "no prime in the band", and
they are not the only ones: `[8,10]` is non-empty, non-inverted, has top well above `1`,
and still contains no prime (`band_8_10_prime_free`).  Neither
`memS_false_of_Qseq_one_le_one` nor `memS_false_of_band_inverted` sees that configuration.

⚠️ **`MRTBands` constrains none of this.**  Its three clauses bound `Q₁` above and relate
consecutive bands; nothing anywhere requires a band to *contain a prime*, and MRT do not
state it either — for them it is implicit in taking `[Pⱼ, Qⱼ]` from Definition 2.1.
Recorded for a design session, not repaired here (Iron rule 1). -/

/-- **THE SET-LEVEL FACT.**  A band containing no prime contributes nothing, whatever its
endpoints look like. -/
theorem blockOmega_eq_zero_of_no_prime {P Q n : ℕ}
    (h : ∀ p : ℕ, p.Prime → ¬ (P ≤ p ∧ p ≤ Q)) : blockOmega P Q n = 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  exact h p (Nat.prime_of_mem_primeFactors hp)

/-- **THE GENERAL DEGENERACY**, subsuming `memS_false_of_Qseq_one_le_one` and
`memS_false_of_band_inverted`: if the first band holds no prime, `MemS` fails for every
`n`, so A.3's sifted set is empty and the proposition is vacuously true. -/
theorem memS_false_of_prime_free_band {Pseq Qseq : ℕ → ℕ} {J n : ℕ} (hJ : 1 ≤ J)
    (h : ∀ p : ℕ, p.Prime → ¬ (Pseq 1 ≤ p ∧ p ≤ Qseq 1)) : ¬ MemS Pseq Qseq J n := by
  intro hm
  have h1 := hm 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hJ⟩)
  rw [blockOmega_eq_zero_of_no_prime h] at h1
  omega

/-- **THE WITNESS THAT THE CLASS IS BIGGER THAN THE THREE I FOUND.**  `[8,10]` is
non-empty (`8 ≤ 10`), non-inverted, and its top is far above `1` — so neither earlier
lemma applies — yet it contains no prime. -/
theorem band_8_10_prime_free : ∀ p : ℕ, p.Prime → ¬ (8 ≤ p ∧ p ≤ 10) := by
  rintro p hp ⟨h8, h10⟩
  interval_cases p <;> norm_num at hp

/-- `T₁` sits inside the band, whichever branch of the `M`-dichotomy it takes. -/
theorem mrtT1_subset_Icc {M t₁ X T : ℝ} : mrtT1 M t₁ X T ⊆ Set.Icc (-T) T := by
  unfold mrtT1
  split_ifs
  · intro t ht
    have h : |t| ≤ T := ht
    rw [Set.mem_Icc, ← abs_le]
    exact h
  · intro t ht
    have h : |t| ≤ T := ht.1
    rw [Set.mem_Icc, ← abs_le]
    exact h

/-- **THE `T₁` SIDE'S FIRST GAP, CLOSED: POINTWISE ⟹ INTEGRAL.**  A uniform bound `B`
on `|F|` over `T₁` gives `∫_{T₁} F² ≤ 2T·B²`, because `T₁ ⊆ [−T,T]` has measure at most
`2T`.

⛔ **THIS IS ONLY THE FIRST OF TWO GAPS BETWEEN `MRTLemmaA5` AND A.3's SPLIT, AND THE
SECOND IS NOT MINE TO CLOSE.**  A.5 bounds `‖mrtG …‖` — MRT's `G`, the Ramaré-weighted
sum — pointwise on `T₁`, while the split consumes `∫_{T₁}‖F‖²` for A.3's `F = dpolyA`.
This lemma performs the *pointwise → integral* half for whatever function is supplied;
the *`G` → `F`* half is what MRT take from `[17, Proposition 1]`.

⛔⛔ **AND "EXTERNAL" WAS THE WRONG WORD — CORRECTED 2026-08-22 14:1x.**  I published
*"external, [17, Proposition 1]"* for A.3's `T₁` side repeatedly today without once
checking the corpus for it.  `Salt/MR/Prop1Assembly.lean` is **41 KB and 22 declarations**,
and four of them are named for this exact object:

```
  prop_A3_T1_row_moment            prop_A3_T1_row_moment_T_of_floor
  prop_A3_T1_row_moment_polyT      prop_A3_T1_row_moment_le
  prop_A3'_assembly · T1_pointwise_decay_corrected · T1_decay_corrected_fgJ
```

**[17, Proposition 1]'s machinery is LANDED.**  What is *not* established is that it
composes to `MRTLemmaA5`, or to `∫_{mrtT1}‖dpolyA‖² ≤ B₁`: the vocabularies differ
(`spoly` / `annHead` / `M_range (seamCoeff (ellLin g) …)` against this file's `dpolyA` /
`mrtT1` / `pretDistSq`), and `prop_A3_T1_row_moment_le` carries the same `(1/32)·loglog X`
floor that row 17j measured as short of A.4(ii)'s constant.

⇒ **The correct standing claim is "NOT YET CONNECTED", not "external".**  The difference
matters for pricing: *external* means port a paper; *not yet connected* means write a
bridge between two landed vocabularies, which is the kind of work this file has been doing
all day.  **The `B₁` hypothesis stays carried either way — this changes what it would COST
to discharge, not whether it is discharged.**

🔑 *Third time today I said "we need X" about something already in the corpus (after
Montgomery–Vaughan, and after my own `landed_route_below_a4ii_target`).  This one I caught
by APPLYING the law banked one beat earlier rather than by accident — which is the first
time today a law of mine fired before the mistake shipped rather than after.*

*Note the enlargement is on the CONSTANT majorant, not on `F` — the same shape as
`mrtA3_T0_setIntegral_bound_onT0`, and for the same reason: `F`'s bound is only known
on `T₁`.* -/
theorem integral_sq_le_of_pointwise_on_mrtT1 {F : ℝ → ℝ} {M t₁ X T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hint : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT1 M t₁ X T) MeasureTheory.volume)
    (hF : ∀ t ∈ mrtT1 M t₁ X T, |F t| ≤ B) :
    (∫ t in mrtT1 M t₁ X T, F t ^ 2) ≤ 2 * T * B ^ 2 := by
  have hsub : mrtT1 M t₁ X T ⊆ Set.Icc (-T) T := mrtT1_subset_Icc
  have hcIcc : MeasureTheory.IntegrableOn (fun _ : ℝ => B ^ 2)
      (Set.Icc (-T) T) MeasureTheory.volume :=
    (continuous_const.continuousOn).integrableOn_compact isCompact_Icc
  have hcT1 : MeasureTheory.IntegrableOn (fun _ : ℝ => B ^ 2)
      (mrtT1 M t₁ X T) MeasureTheory.volume := hcIcc.mono_set hsub
  have h1 : (∫ t in mrtT1 M t₁ X T, F t ^ 2) ≤ ∫ _t in mrtT1 M t₁ X T, B ^ 2 := by
    refine MeasureTheory.setIntegral_mono_on hint hcT1 (measurableSet_mrtT1 _ _ _ _) ?_
    intro t ht
    have h := hF t ht
    calc F t ^ 2 = |F t| ^ 2 := (sq_abs (F t)).symm
      _ ≤ B ^ 2 := by nlinarith [abs_nonneg (F t)]
  have h2 : (∫ _t in mrtT1 M t₁ X T, B ^ 2) ≤ ∫ _t in Set.Icc (-T) T, B ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hcIcc ?_ hsub.eventuallyLE
    filter_upwards with t using (by positivity : (0 : ℝ) ≤ B ^ 2)
  have h3 : (∫ _t in Set.Icc (-T) T, (B : ℝ) ^ 2) = 2 * T * B ^ 2 := by
    rw [MeasureTheory.setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith : (-T : ℝ) ≤ T), smul_eq_mul]
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **A.3's SPLIT, as a Lean step.**  `T₀` and `T₁` partition `{|t| ≤ T}`
(`mrtT0_union_mrtT1`, `mrtT0_disjoint_mrtT1`, both landed), so a bound on each
piece adds to a bound on the band.  *This is the shape of A.3's proof: MRT bound
`∫_{T₁}` by Lemma A.5 and `∫_{T₀}` by the (A.7) display, then add.* -/
theorem mrtA3_split_bound {F : ℝ → ℝ} {M t₁ X T B₀ B₁ : ℝ}
    (h0int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT0 M t₁ X T) MeasureTheory.volume)
    (h1int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT1 M t₁ X T) MeasureTheory.volume)
    (h0 : (∫ t in mrtT0 M t₁ X T, F t ^ 2) ≤ B₀)
    (h1 : (∫ t in mrtT1 M t₁ X T, F t ^ 2) ≤ B₁) :
    (∫ t in {t : ℝ | |t| ≤ T}, F t ^ 2) ≤ B₀ + B₁ := by
  rw [← mrtT0_union_mrtT1 M t₁ X T,
    MeasureTheory.setIntegral_union (mrtT0_disjoint_mrtT1 M t₁ X T)
      (measurableSet_mrtT1 M t₁ X T) h0int h1int]
  linarith

/-- **The band set IS the centred interval.**  `{t : |t| ≤ T} = Icc (−T) T` — the
`abs_le` unfolding, isolated because `mrtT0_union_mrtT1` produces the SET form
while `MRTPropA3`'s statement uses the INTERVAL form. -/
theorem band_eq_Icc (T : ℝ) : {t : ℝ | |t| ≤ T} = Set.Icc (-T) T := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]

/-- **A.3's SPLIT, delivered in `MRTPropA3`'s own integral shape.**  The split
concludes over the SET `{|t| ≤ T}`; A.3 is stated with `∫_{−T}^{T}`.  Same bridge
as the `T₀` set version: `band_eq_Icc`, then `Icc → Ioc` (null set), then
`integral_of_le`. -/
theorem mrtA3_split_bound_interval {F : ℝ → ℝ} {M t₁ X T B₀ B₁ : ℝ} (hT : 0 ≤ T)
    (h0int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT0 M t₁ X T) MeasureTheory.volume)
    (h1int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT1 M t₁ X T) MeasureTheory.volume)
    (h0 : (∫ t in mrtT0 M t₁ X T, F t ^ 2) ≤ B₀)
    (h1 : (∫ t in mrtT1 M t₁ X T, F t ^ 2) ≤ B₁) :
    (∫ t in (-T)..T, F t ^ 2) ≤ B₀ + B₁ := by
  have hle : (-T : ℝ) ≤ T := by linarith
  have hband := mrtA3_split_bound h0int h1int h0 h1
  rw [band_eq_Icc T, MeasureTheory.integral_Icc_eq_integral_Ioc] at hband
  rw [intervalIntegral.integral_of_le hle]
  exact hband

/-! ### `0 ≤ B` — the bridge's other binder, and the last one without a producer

`MRTPropA3Bridge.hMsup_of_propA3_shape` also carries `hB : 0 ≤ B`.  At the identification
`B = C · bracket` fixed by `mrtPropA3_in_bridge_shape`, that needs `0 ≤ C` (from
`MRTLemmaA6Statement`'s `∃ C > 0`) and `0 ≤ bracket`, and the bracket's nonnegativity had
**no producer anywhere** — `mrtM_nonneg` did not exist.

⚠️ Each of the three bracket terms is nonnegative only under a side condition, and they
are not the same one: the first needs `0 ≤ log Q₁` (an `rpow` of a possibly-negative base
is not automatically nonnegative), the third needs `0 ≤ log X`, and the middle needs
`0 ≤ M(f;X)` — which is an `sInf`, so it is a real obligation rather than a syntactic one. -/

/-- **`M(f;X) ≥ 0`.**  The infimum of a set of pretentious distances, each of which is a
sum of nonnegative terms.  Nonempty via `t = 0`, bounded below by `0`. -/
theorem mrtM_nonneg (f : ℕ → ℂ) {X : ℝ} (hX : 0 ≤ X) (hf : ∀ n, ‖f n‖ ≤ 1) :
    0 ≤ mrtM f X := by
  unfold mrtM
  refine le_csInf ⟨pretDistSq f (costwist 0) X, ⟨0, by simpa using hX, rfl⟩⟩ ?_
  rintro b ⟨t, _, rfl⟩
  exact pretDistSq_nonneg f (costwist t) X hf (norm_costwist_le t)

/-- **A.3's BRACKET IS NONNEGATIVE**, which with `0 ≤ C` discharges the bridge's `hB`. -/
theorem mrtA3_bracket_nonneg (f : ℕ → ℂ) {X η : ℝ} (Pseq Qseq : ℕ → ℕ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hX : 0 ≤ X)
    (hlogQ : 0 ≤ Real.log (Qseq 1)) (hlogX : 0 ≤ Real.log X) :
    0 ≤ (Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
        + mrtM f X / Real.exp (mrtM f X)
        + 1 / (Real.log X) ^ ((1 : ℝ) / 50) := by
  have h1 : 0 ≤ (Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) :=
    div_nonneg (Real.rpow_nonneg hlogQ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h2 : 0 ≤ mrtM f X / Real.exp (mrtM f X) :=
    div_nonneg (mrtM_nonneg f hX hf) (Real.exp_nonneg _)
  have h3 : 0 ≤ 1 / (Real.log X) ^ ((1 : ℝ) / 50) :=
    div_nonneg zero_le_one (Real.rpow_nonneg hlogX _)
  linarith

/-! ### The connector to `MRTPropA3Bridge`

`Salt/MR/MRTPropA3Bridge.lean` consumes A.3 as a hand-written hypothesis

    hA3 : ∀ T, 1 ≤ T → ∫_{−T}^{T} ‖dpolyA a s₀ t‖² ≤ (T/(X/h₁) + 1) * B

and it does **not import `MRTPropA3`** — so nothing in Lean connected the two, and the
bridge's notion of "A.3's shape" was free to drift from the actual definition.  It has
not drifted: the forms agree at `h₁ := Qseq 1` and `B := C · bracket`, differing only by
the association `C * (…) * bracket = (…) * (C * bracket)`.

This is the object that says so.  *Two green pieces with no stated interface is the
defect class this file has been finding all day; here the interface holds, and stating it
is what turns that from a belief into a theorem.* -/

/-- **A.3, RESTATED IN THE BRIDGE'S SHAPE.**  Exactly `MRTPropA3Bridge`'s `hA3`
hypothesis, at `h₁ = Qseq 1` and `B = C · bracket`. -/
theorem mrtPropA3_in_bridge_shape {C : ℝ} (hA3 : MRTPropA3 C)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (X X₀ η : ℝ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (S : Finset ℕ)
    (hη0 : 0 < η) (hη6 : η < 1 / 6)
    (hX₀lo : Real.sqrt X ≤ X₀) (hX₀hi : X₀ ≤ X)
    (hbands : MRTBands X₀ η Pseq Qseq) (hcount : MRTBandCount X₀ Qseq J)
    (hS : ∀ n : ℕ, n ∈ S ↔ (X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X ∧ MemS Pseq Qseq J n)) :
    ∀ T : ℝ, 1 ≤ T → MRTPropA3Ambient X T Pseq →
      (∫ t in (-T)..T, ‖dpolyA f S t‖ ^ 2)
        ≤ (T / (X / (Qseq 1 : ℝ)) + 1)
          * (C * ((Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
                + mrtM f X / Real.exp (mrtM f X)
                + 1 / (Real.log X) ^ ((1 : ℝ) / 50))) := by
  intro T hT hamb
  refine le_trans
    (hA3 f hf hf1 hmul X X₀ η Pseq Qseq J S hη0 hη6 hX₀lo hX₀hi hbands hcount hS T hT hamb)
    (le_of_eq ?_)
  ring

/-! ### The junk-value class, swept as a SET — and one site the guard does NOT cover

Having named the blind spot, the lesson from row 17d says to sweep the CLASS rather than
collect instances.  A.3's right-hand side has four junk-value sites:

```
  X / (Qseq 1 : ℝ)            division   — Q₁ = 0  ⇒ factor collapses to 1   (17e, guard covers)
  T / (X / Qseq 1)            division   — same site, one level up            (17e, guard covers)
  (log (Qseq 1)) ^ (1/3)      rpow       — SAFE: Real.log of a ℕ-cast is ≥ 0 always,
                                           since log 0 = log 1 = 0 by convention
  (Pseq 1 : ℝ) ^ (1/6 − η)    rpow       — ⛔ P₁ = 0 ⇒ base 0, exponent > 0 ⇒ 0,
                                           and the term DIVIDES by it ⇒ term = 0
```

⛔ **THE FOURTH IS NOT COVERED BY THE EMPTY-`S` GUARD, AND THAT IS THE FINDING.**
`MRTBands` never constrains `P₁` directly — `(A.1)`/`(A.2)` mention `P_{j−1}` only for
`j ≥ 2`, and at `P₁ = 0` the `(A.1)` ratio at `j = 2` reads `log log Q₂ / (0 − 1)`, which
is NEGATIVE and so satisfies the bound.  So `P₁ = 0` is admissible.  Then A.3's first
bracket term is `(log Q₁)^{1/3} / 0 = 0` — the term MRT intend to be present simply
vanishes, making the bound strictly harder.

**And unlike every earlier degeneracy, `S` need not be empty**: the block is `[0, Q₁]`,
which contains every prime `≤ Q₁`, so at `Q₁ ≥ 2` membership is perfectly possible.
`memS_false_of_prime_free_band` does not apply.

*This does not make A.3 false — the other two bracket terms survive — but it is the first
degeneracy in this file that the one guard does NOT absorb, and it is a statement-level
gap rather than a proof difficulty.  Recorded for a design session (Iron rule 1): the
missing clause is a positive lower bound on `P₁`, which MRT supply in prose by drawing
`[Pⱼ,Qⱼ]` from Definition 2.1.* -/

/-- **A.3's FIRST BRACKET TERM VANISHES AT `Pseq 1 = 0`** — base `0`, positive exponent,
and the term divides by it. -/
theorem mrtA3_first_term_of_Pseq1_zero {η : ℝ} {Pseq Qseq : ℕ → ℕ}
    (hη : η < 1 / 6) (hP : Pseq 1 = 0) :
    (Real.log (Qseq 1)) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η) = 0 := by
  have hne : (1 : ℝ) / 6 - η ≠ 0 := by linarith
  rw [hP, Nat.cast_zero, Real.zero_rpow hne, div_zero]

/-- **AND THE EMPTY-`S` GUARD DOES NOT FIRE THERE**: the band `[0, 2]` contains a prime,
so `memS_false_of_prime_free_band`'s hypothesis fails. -/
theorem band_zero_two_has_prime : ∃ p : ℕ, p.Prime ∧ 0 ≤ p ∧ p ≤ 2 :=
  ⟨2, Nat.prime_two, by omega, by omega⟩

/-! ### What the binder audit CANNOT see — junk values inside definitions

Rows 17a/17c/17d all came from auditing HYPOTHESES.  That instrument is blind to a whole
class: a degeneracy that is not a hypothesis at all, but a *junk value* Lean assigns
inside a definition.  Asking which class my own audit cannot see turns one up in A.3's
own right-hand side.

⛔ **`X / (Qseq 1 : ℝ)` AT `Qseq 1 = 0`.**  `MRTBands` bounds `Q₁` only from ABOVE
(`Q₁ ≤ exp √(log X₀)`), so `Q₁ = 0` is admissible.  Then `X/0 = 0` and `T/0 = 0`, so A.3's
leading factor `T/(X/Q₁) + 1` **collapses from something large to exactly `1`** — the
bound gets STRICTLY HARDER, in the direction that would make the proposition false.

✅ **AND THE SAME GUARD SAVES IT, FOR THE FOURTH TIME.**  `Q₁ = 0` means the first band is
`[P₁, 0]`, which contains no prime, so `MemS` fails everywhere and `S = ∅`.  That is not a
new case: it is already inside `memS_false_of_prime_free_band`, which is evidence the
generalisation in row 16v was cut at the right level rather than at the level of the three
examples that prompted it.

*A negative result, reported as loudly as a positive one: the class my audit is blind to
does contain a real instance here, and the instance is already covered.* -/

/-- **A.3's LEADING FACTOR COLLAPSES TO `1` AT `Qseq 1 = 0`** — via `X/0 = 0` then `T/0 = 0`.
The bound becomes strictly harder, which is why this needed checking rather than assuming. -/
theorem mrtA3_leading_factor_of_Qseq1_zero {X T : ℝ} {Qseq : ℕ → ℕ} (hQ : Qseq 1 = 0) :
    T / (X / (Qseq 1 : ℝ)) + 1 = 1 := by
  rw [hQ]
  simp

/-- **AND THE SAME CONFIGURATION EMPTIES `S`** — a corollary of the general prime-free-band
lemma, not a new case. -/
theorem memS_false_of_Qseq1_zero {Pseq Qseq : ℕ → ℕ} {J n : ℕ} (hJ : 1 ≤ J)
    (hQ : Qseq 1 = 0) : ¬ MemS Pseq Qseq J n :=
  memS_false_of_Qseq_one_le_one hJ (by omega)

/-! ### The bridge's binders as a SET — and the residue is largeness

Rows 17a/17c closed two of `MRTPropA3Bridge`'s hypotheses one at a time.  Doing what the
standing law actually asks — audit the SET, not each claim as it appears — over **all five**
of the bridge's theorems gives a sharper answer.  Its hypotheses fall into exactly two
groups:

**PRODUCIBLE from A.3's own hypotheses** (this section proves them):
`hpos : ∀ m ∈ s₀, 0 < m` · `ha : ∀ m ∈ s₀, ‖a m‖ ≤ 1` ·
`hrange : ∀ m ∈ s₀, X ≤ m ≤ 4X` · `hXh : 0 < X/h₁`
— plus `hB` (row 17c) and `hA3` itself (row 17b).

⛔ **NOT PRODUCIBLE — FOUR SIZE HYPOTHESES A.3 DOES NOT CARRY:**
```
  hXe  : exp 1 ≤ X                          the bridge needs X ≥ e
  hh4  : 4 ≤ h                              and h ≥ 4
  hhX  : h ≤ X·(log X)^{−1/5}               and h not too large against X
  hR1  : 1 ≤ X/h                            hence h ≤ X
```
**This is the same finding as the `X = 1` degeneracy, arriving from the other side.**
`MRTPropA3` carries no largeness on `X` at all — that is exactly why it goes vacuous at
`X = 1` — while its consumer needs `X ≥ e` and a two-sided constraint on `h`.  Those must
come from Theorem A.2's context, which does say *"for all `X > X(η)` large enough"*.

⇒ **The A.3 → bridge chain runs only in the regime where those four hold, and they are
inputs to that regime rather than consequences of A.3.**  Named here so no future assembly
mistakes them for something A.3 supplies. -/

/-- **THE PRODUCIBLE HALF OF THE BRIDGE'S BINDERS**, derived from A.3's own hypotheses.
What remains after this is exactly the four size conditions listed above. -/
theorem bridge_side_conditions_of_mrtA3_hyps
    {X : ℝ} (hX1 : 1 ≤ X) {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {Pseq Qseq : ℕ → ℕ} {J : ℕ} {S : Finset ℕ}
    (hS : ∀ n : ℕ, n ∈ S ↔ (X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X ∧ MemS Pseq Qseq J n))
    (hQ1 : 0 < (Qseq 1 : ℝ)) :
    (∀ m ∈ S, 0 < m) ∧ (∀ m ∈ S, ‖f m‖ ≤ 1)
      ∧ (∀ m ∈ S, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
      ∧ 0 < X / (Qseq 1 : ℝ) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1
  refine ⟨?_, fun m _ => hf m, ?_, div_pos hXpos hQ1⟩
  · intro m hm
    have h := ((hS m).mp hm).1
    have : (1 : ℝ) ≤ (m : ℝ) := le_trans hX1 h
    have hm1 : 1 ≤ m := by exact_mod_cast this
    omega
  · intro m hm
    obtain ⟨hlo, hhi, _⟩ := (hS m).mp hm
    exact ⟨hlo, by linarith⟩

/-! ### Discharging the integrability side conditions

`mrtA3_band_bound_of_A6` carries two `IntegrableOn` hypotheses.  Running the standing
check — *for every hypothesis a design carries, name the node that produces it* — over
its own binders, those two were the only ones with **no producer anywhere**: `hf`, `hX`,
`hlogX`, `hT` come from A.3's own statement, `hr`/`hrX` are the caller's choice, `hC`
comes from `MRTLemmaA6Statement`'s `∃ C > 0`, and `hT1` is carried deliberately.

They are not fundamental, only unproved: the integrand is a FINITE sum of continuous
functions of `t` (`gJ` does not depend on `t` at all; `costwist` is an exponential), and
both `T₀` and `T₁` sit inside the compact band `[−T,T]`. -/

/-- `T₀` sits inside the band, on either branch — the companion to `mrtT1_subset_Icc`. -/
theorem mrtT0_subset_band {M t₁ X T : ℝ} : mrtT0 M t₁ X T ⊆ Set.Icc (-T) T := by
  unfold mrtT0
  split_ifs
  · exact Set.empty_subset _
  · intro t ht
    have h : |t| ≤ T := ht.1
    rw [Set.mem_Icc, ← abs_le]
    exact h

/-- **A.6's OBJECT IS CONTINUOUS IN `t`.**  `gJ` carries no `t`; the whole `t`-dependence
is the exponential `costwist (−t)`, and the sums are finite. -/
theorem continuous_a3_twistedSum (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (X : ℝ) :
    Continuous (fun t : ℝ => ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n‖) := by
  unfold costwist
  continuity

/-- `h0int` discharged: a continuous `F` has `F²` integrable on `T₀`. -/
theorem integrableOn_sq_mrtT0_of_continuous {F : ℝ → ℝ} (hF : Continuous F)
    (M t₁ X T : ℝ) :
    MeasureTheory.IntegrableOn (fun t => F t ^ 2) (mrtT0 M t₁ X T) MeasureTheory.volume :=
  ((hF.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set mrtT0_subset_band

/-- `h1int` discharged: a continuous `F` has `F²` integrable on `T₁`. -/
theorem integrableOn_sq_mrtT1_of_continuous {F : ℝ → ℝ} (hF : Continuous F)
    (M t₁ X T : ℝ) :
    MeasureTheory.IntegrableOn (fun t => F t ^ 2) (mrtT1 M t₁ X T) MeasureTheory.volume :=
  ((hF.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set mrtT1_subset_Icc

/-! ### THE RESIDUE, CONSOLIDATED — three missing parameter bounds, three routes

Over this session `MRTPropA3` turned out to be missing **three** parameter bounds, and
each was found by a different instrument.  Collected here because they are one fact:

```
  X : no LOWER largeness    found by hunting the X = 1 degeneracy       (rescued by empty S)
  T : no UPPER bound        found by an interface check against A.6/A.7 (MRT reduce to T ≤ X/2)
  P₁: no LOWER bound        found by the junk-value sweep               ⛔ NOT rescued
```

⭐ **They are instances of ONE thing: the transcription carries MRT's explicit displayed
inequalities and not the ambient conditions their PROSE supplies** — *"for all `X > X(η)`
large enough"* (Thm A.2), *"since the mean value theorem gives `O(T/X+1)` we can assume
`T ≤ X/2`"* (A.3's own opening), and *"the intervals `[Pⱼ,Qⱼ]` of Definition 2.1"*.  A
displayed formula transcribes; a sentence of running prose does not, and all three losses
are of the second kind.

✅ **ADOPTED BY CAPTAIN'S RULING, 2026-08-22 ~17:4x (council, relayed by Sancho).**  The
design session took this object up: `MRTPropA3` now CARRIES `MRTPropA3Ambient`, and the
definition has moved ahead of `MRTPropA3` so it can be named there.  Iron rule 1 is satisfied
by the ruling itself, not by my hand.  *The three losses recorded above are what the ruling
repairs.* -/

/-- **THE AMBIENT HYPOTHESES EXCLUDE ALL THREE DEGENERACIES AT ONCE**: `X = 1` is out,
`Pseq 1 = 0` is out, and `T ≤ X` (which is what `mrtT0_mono_T` needs to carry A.6's band
radius down to the split's). -/
theorem mrtA3_ambient_excludes_degeneracies {X T : ℝ} {Pseq : ℕ → ℕ}
    (h : MRTPropA3Ambient X T Pseq) :
    1 < X ∧ Pseq 1 ≠ 0 ∧ T ≤ X := by
  obtain ⟨hXe, hTX, hP⟩ := h
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hX2 : (2 : ℝ) ≤ X := le_trans h2e hXe
  refine ⟨by linarith, by omega, by linarith⟩

/-- **A.3's APPENDIX BRANCH, ASSEMBLED.**  The band bound over `[−T,T]`, derived from
Lemma A.6 on the `T₀` side and an assumed `T₁` bound, for `T ≤ X`.

This composes the whole `T ≤ X/2` half of MRT's proof out of pieces that are now Lean
objects: `mrtA3_T0_bound_of_A6` (A.6 ⟹ the `T₀` integral bound, via `mrtT0_mono_T` to
move A.6's band radius `X` down to the split's `T`), and `mrtA3_split_bound_interval`
(the `T₀`/`T₁` partition, delivered in `MRTPropA3`'s own `∫_{−T}^{T}` shape).

⛔ **`B₁` IS CARRIED, NOT PROVED, AND THAT IS THE HONEST STATE OF A.3.**  MRT obtain the
`T₁` bound from `[17, Proposition 1]`, and `MRTLemmaA5` as transcribed gives a *pointwise*
bound on `‖mrtG‖` rather than an integral bound on `‖dpolyA‖²` — two gaps, of which
`integral_sq_le_of_pointwise_on_mrtT1` closes only the first.  Naming `B₁` as a hypothesis
is what keeps that visible: *a theorem that quietly absorbed it would read as a proof of
A.3's branch and would not be one.*

⭐ The other branch, `T > X/2`, is `mrtA3_mvt_branch` and is UNCONDITIONAL. -/
theorem mrtA3_band_bound_of_A6 {C : ℝ} {F : ℝ → ℝ} (hC : 0 ≤ C) (hA6 : MRTLemmaA6 C)
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) {X T t₁ r B₁ : ℝ}
    (hFdef : ∀ t : ℝ, F t = ‖(1 / (X : ℂ)) * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℂ) ^ 𝒥.card
          * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, gJ 𝒥 Pseq Qseq n * f n * costwist (-t) n‖)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hX : 0 < X) (hlogX : 0 ≤ Real.log X)
    (hT : 0 ≤ T) (hTX : T ≤ X) (hr : 0 ≤ r)
    (hrX : (Real.log X) ^ ((1 : ℝ) / 16) ≤ r)
    (h0int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT0 (mrtM f X) t₁ X T) MeasureTheory.volume)
    (h1int : MeasureTheory.IntegrableOn (fun t => F t ^ 2)
      (mrtT1 (mrtM f X) t₁ X T) MeasureTheory.volume)
    (hT1 : (∫ t in mrtT1 (mrtM f X) t₁ X T, F t ^ 2) ≤ B₁) :
    (∫ t in (-T)..T, F t ^ 2)
      ≤ (4 * (C * Real.exp (-(1 / 2) * mrtM f X)) ^ 2
          + 4 * (C * (Real.log X) ^ (-(1 : ℝ) / 16)) ^ 2 * r) + B₁ :=
  mrtA3_split_bound_interval hT h0int h1int
    (mrtA3_T0_bound_of_A6 hC hA6 f Pseq Qseq J hFdef hf hX hlogX hTX hr hrX h0int) hT1

/-- **A.7's SIDE CONDITION, WITH `t` ELIMINATED** — `renormalise_aux` (`Renormalise.lean:760`)
demands `hyx : (3 + |u|·(1 + log x))² ≤ x`.  At A.7's `u := t − t₁` this is a condition on
BOTH `t` and `X`; but on `T₀` the radius `|t − t₁| ≤ (log X)^{1/16}`
(`abs_sub_le_of_mem_mrtT0`, already landed) makes it monotone in `|t − t₁|`, so it follows
from **one inequality in `X` alone**.

⇒ **The whole `t`-dependence of A.7's renormalisation side condition is discharged by `T₀`
membership.**  What is left is a largeness threshold on `X`, and nothing about `t`.

⛔ **THE THRESHOLD IS NOT SUPPLIED BY THE ADOPTED AMBIENT HYPOTHESES.**  `MRTPropA3Ambient`
gives `exp 1 ≤ X`, which is far too weak: `(3 + (log X)^{1/16}(1+log X))²` grows like
`(log X)^{17/8}`, so the hypothesis below holds for large `X` but needs an explicit constant
the Captain's ruling did not (and was not asked to) provide.  **Named, not assumed.** -/
theorem renormalise_hyx_of_mrtT0 {M t₁ X T t : ℝ} (ht : t ∈ mrtT0 M t₁ X T)
    (hlogX : 0 ≤ Real.log X)
    (hX : (3 + (Real.log X) ^ ((1 : ℝ) / 16) * (1 + Real.log X)) ^ 2 ≤ X) :
    (3 + |t - t₁| * (1 + Real.log X)) ^ 2 ≤ X := by
  have hrad : |t - t₁| ≤ (Real.log X) ^ ((1 : ℝ) / 16) := abs_sub_le_of_mem_mrtT0 ht
  have h1 : (0 : ℝ) ≤ 1 + Real.log X := by linarith
  have hbase : 3 + |t - t₁| * (1 + Real.log X)
      ≤ 3 + (Real.log X) ^ ((1 : ℝ) / 16) * (1 + Real.log X) := by
    have := mul_le_mul_of_nonneg_right hrad h1
    linarith
  have hnn : (0 : ℝ) ≤ 3 + |t - t₁| * (1 + Real.log X) := by
    have : (0 : ℝ) ≤ |t - t₁| * (1 + Real.log X) := mul_nonneg (abs_nonneg _) h1
    linarith
  exact le_trans (pow_le_pow_left₀ hnn hbase 2) hX

/-! ### ⛔ A.7's RENORMALISATION IS LANDED — AND THIS CORRECTS MY OWN LAST BEAT

I have been calling A.7's residue *"re-target the RHS from `∑ mobDatum f d/d` to the `t₁`-twisted
sum."*  **That re-target is already done.**  `Renormalise.renormalise` (`:1004`) states

```
  ‖(∑_{n≤x} f n · eIu α n) − eIu α x/(1 + Iα) · (∑_{n≤x} f n)‖
      ≤ renormaliseConst · (x/log x) · (1 + log(3+|α|(1+log x))) · exp(∑_{p≤x} ‖1−f p‖/p)
```
— **the Möbius-datum sum is GONE**, eliminated by applying `renormalise_aux` twice (once at `α`,
once at `0`), exactly as that file's own docstring says.  The main term is A.7's main term.

⛔⛔ **AND IT NEEDS NO `hyx`.**  `renormalise` assumes only `2 ≤ x`; its docstring records that
beyond `(3+|α|(1+log x))² > x` the statement is *"discharged by the trivial bound."*  ⇒ **My
`renormalise_hyx_of_mrtT0`, landed one beat ago, is correct but is NOT needed on the A.7 path** —
it serves `renormalise_aux` directly, and A.7's consumer should call `renormalise` instead.  *I
built a side-condition discharge for a hypothesis the intended consumer does not have.*

**THE ACTUAL RESIDUE OF A.7, then, is two things and neither is the re-target:**
1. **SUMMAND MATCH.**  A.7's summand is `gJ 𝒥 Pseq Qseq n · f n · costwist (−t₁) n`; `renormalise`
   quantifies over an `f` with `f 1 = 1`, multiplicativity, `‖f n‖ ≤ 1`.  Whether the *sieved*
   datum satisfies those is a hypothesis-matching question, not an estimate.
2. **THE PRETENTIOUS FACTOR.**  `renormalise`'s error carries
   `(1 + log y) · exp(∑_{p≤x} ‖1 − f p‖/p)`; A.7 wants `C·X/(log X)^{1/10}`.  Since
   `x/log x ≤ x/(log x)^{1/10}` (`renormalise_error_logpower_stronger`, landed), what remains is
   bounding `(1 + log y)·exp(∑ ‖1−f p‖/p)` by an absolute constant — and that exponential IS the
   pretentious distance, the same object `mrtM` measures.  **That is the analytic content.**

🔑 *Fifth time today the corpus held more than I said it did — but the first caught BEFORE
publishing the claim, by searching before composing.  The habit is worth more than the lemma.* -/

/-! ### A.7's SUMMAND MATCH — the two missing pieces, and a junk-value trap in one of them

`renormalise` (`Renormalise.lean:1004`) quantifies over an `f` with `f 1 = 1`, multiplicativity
and `‖f n‖ ≤ 1`.  A.7's summand is `gJ 𝒥 Pseq Qseq n · f n · costwist (−t₁) n`, so the match
needs those three properties for each factor.  Censused:

* `gJ` — **`gJ_mul` (`Sec9Glue.lean:183`) is COMPLETE multiplicativity** (`m,n ≠ 0`, no
  coprimality), and `norm_gJ_le_one` (`CofactorSupplier.lean:85`) bounds it.  Landed.
* `f` — hypotheses of A.7 itself.
* `costwist` — `costwist_norm` is landed, but **multiplicativity IN THE ARGUMENT and the value
  at `1` were both ABSENT** (measured: 0 hits, decoy control 0).  They are below.

⛔ **AND THE ABSENT ONE CARRIES A JUNK-VALUE TRAP.**  `Real.log 0 = 0`, so `costwist t 0 = 1`;
then `costwist t (0 · n) = 1` while `costwist t 0 · costwist t n = costwist t n`.
**Multiplicativity is FALSE at `m = 0`** — which is exactly why `gJ_mul` carries `m,n ≠ 0` too.
*The nonzero hypotheses are load-bearing, not decoration.* -/

/-- The twist is `1` at `n = 1` (`log 1 = 0`). -/
theorem costwist_one (t : ℝ) : costwist t 1 = 1 := by
  unfold costwist
  simp

/-- **The twist is multiplicative in its ARGUMENT** — `n ↦ n^{it}` is completely multiplicative
away from `0`.  ⛔ `m, n ≠ 0` is REQUIRED: at `m = 0` Lean's `Real.log 0 = 0` makes the left side
`1` and the right side `costwist t n`. -/
theorem costwist_mul (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    costwist t (m * n) = costwist t m * costwist t n := by
  unfold costwist
  rw [← Complex.exp_add]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : Real.log ((m * n : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (n : ℝ) := by
    push_cast
    exact Real.log_mul hm0 hn0
  rw [this]
  push_cast
  ring

/-- **A.7'S SUMMAND IS COMPLETELY MULTIPLICATIVE AWAY FROM ZERO**, given `f`'s own
multiplicativity in the same (complete) sense — the shape `renormalise` asks for. -/
theorem gJ_f_costwist_mul {f : ℕ → ℂ}
    (hfmul : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b)
    (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (t : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    gJ 𝒥 Pseq Qseq (m * n) * f (m * n) * costwist t (m * n)
      = (gJ 𝒥 Pseq Qseq m * f m * costwist t m)
        * (gJ 𝒥 Pseq Qseq n * f n * costwist t n) := by
  rw [gJ_mul 𝒥 Pseq Qseq hm hn, hfmul m n hm hn, costwist_mul t hm hn]
  ring

/-- **A.7'S SUMMAND, IN `renormalise`'S OWN HYPOTHESIS FORM** — coprime multiplicativity, which
is what `Renormalise.renormalise` (`:1004`) actually asks for (`hfmul : ∀ a b, Nat.Coprime a b →
…`), not the complete form.

The degenerate coprime pairs are the whole content: `Nat.Coprime 0 b` forces `b = 1` and
`Nat.Coprime a 0` forces `a = 1`, and there the identity holds by the three `= 1` facts —
`gJ_one`, `f 1 = 1`, `costwist_one`.  Off zero it is `gJ_mul` + `hfmul` + `costwist_mul`.

⭐ `gJ_one` is landed (`CofactorSupplier.lean:106`) — and *finding* it required the looser probe:
it is declared `@[simp] lemma`, so a `^(theorem|lemma)` anchor reports ZERO.  **That is the
`@[simp] theorem` instrument trap, live**; two probes disagreed and the gap was the finding. -/
theorem gJ_f_costwist_mul_coprime {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (t : ℝ) {a b : ℕ} (hab : Nat.Coprime a b) :
    gJ 𝒥 Pseq Qseq (a * b) * f (a * b) * costwist t (a * b)
      = (gJ 𝒥 Pseq Qseq a * f a * costwist t a)
        * (gJ 𝒥 Pseq Qseq b * f b * costwist t b) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb1 : b = 1 := by simpa [Nat.coprime_zero_left] using hab
    subst hb1
    simp [gJ_one, hf1, costwist_one]
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      have ha1 : a = 1 := by simpa [Nat.coprime_zero_right] using hab
      subst ha1
      simp [gJ_one, hf1, costwist_one]
    · rw [gJ_mul 𝒥 Pseq Qseq ha.ne' hb.ne', hfmul a b hab, costwist_mul t ha.ne' hb.ne']
      ring

/-! ### ⛔ A.7's ERROR FACTOR IS **NOT** CONTROLLED BY `mrtM` — THE INEQUALITY RUNS THE WRONG WAY

A.7's residue (2) is `renormalise`'s error factor `exp(∑_{p≤x} ‖1 − f p‖/p)`.  The obvious hope
is that `mrtM` controls it, since `mrtM` is the campaign's pretentious-distance quantity.  **It
does not, and the reason is a direction-of-inequality trap worth landing rather than recalling.**

`pretDistSq f g x = ∑_{p≤x} (1 − Re(f p · conj (g p)))/p` and
`mrtM f X = sInf {pretDistSq f (costwist t) X : |t| ≤ X}`.  Two steps, both proved below or
immediate:

* `1 − Re z ≤ ‖1 − z‖` — elementary, so **`pretDistSq f 1 x ≤ ∑_{p≤x} ‖1 − f p‖/p`**;
* `costwist 0 = 1` and `|0| ≤ X`, so **`mrtM f X ≤ pretDistSq f 1 X`** (an `sInf` is below any
  member).

⇒ **`mrtM f X ≤ pretDistSq f 1 X ≤ ∑_{p≤x} ‖1 − f p‖/p`.  BOTH steps run FROM `mrtM` TOWARD the
factor A.7 needs bounded ABOVE.**  A small `mrtM` therefore says **nothing** about
`∑ ‖1 − f p‖/p`; the chain is useless in the required direction.

⇒ **A.7's residue (2) needs a genuinely different input** — an upper bound on the UNTWISTED,
NORM-form prime sum — and cannot be discharged by the `M`-smallness the rest of A.3 runs on.
*Naming which inequality is unavailable is worth more than another attempt to use it.* -/

/-- `1 − Re z ≤ ‖1 − z‖`.  The corpus proves this inline at `SW/DHBal.lean:85` for one specific
`ρ`; this is the reusable form. -/
theorem one_sub_re_le_norm_one_sub (z : ℂ) : 1 - z.re ≤ ‖1 - z‖ := by
  have h := Complex.re_le_norm (1 - z)
  simpa using h

/-- **THE COMPARISON, IN THE UNUSABLE DIRECTION** — `𝔻(f,1;x)²` is BELOW the norm-form prime sum.
Landed so the direction is a theorem rather than a memory. -/
theorem pretDistSq_one_le_sum_norm (f : ℕ → ℂ) (x : ℝ) :
    pretDistSq f 1 x
      ≤ ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ‖1 - f p‖ / (p : ℝ) := by
  unfold pretDistSq
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hnum : (1 : ℝ) - (f p * (starRingEnd ℂ) ((1 : ℕ → ℂ) p)).re ≤ ‖1 - f p‖ := by
    simp only [Pi.one_apply, map_one, mul_one]
    exact one_sub_re_le_norm_one_sub (f p)
  gcongr

/-! ### ⛔ THE WITNESS — `renormalise`'S ROUTE CANNOT DELIVER A.7 AT `f = λ`

The section above shows `mrtM` runs the wrong way for residue (2).  This exhibits a CONCRETE
`f` at which `renormalise`'s error factor is not merely unbounded-in-principle but provably
divergent, so residue (2) is **structural, not a matter of constants.**

At Liouville, `liouvilleC p = -1` on every prime (`M4Residue.lean:109`), so
`‖1 − liouvilleC p‖ = ‖1 − (−1)‖ = 2` **exactly** — no asymptotics — and therefore
`∑_{p≤x} ‖1 − liouvilleC p‖/p = 2·∑_{p≤x} 1/p`.

That prime harmonic sum diverges, and **the corpus already has the sharp form**:
`Dist.pretDistSq_principal_eval` gives `𝔻(f,1;x)² = 2·loglog⌊x⌋ + 2M + O(1/log⌊x⌋)` off
`Salt.Mertens.mertens_second_sharp`.  With `pretDistSq_one_le_sum_norm` (landed above) the
chain closes: `2·loglog⌊x⌋ + O(1) = 𝔻(λ,1;x)² ≤ ∑ ‖1−λ p‖/p`, so
**`exp(∑_{p≤x} ‖1 − λ p‖/p) ≳ (log x)²`.**

⇒ `renormalise`'s bound at `f = λ` is `≳ (x/log x)·(log x)² = x·log x`, against A.7's target
`C·X/(log X)^{1/10}`.  **The route is vacuous there by a factor of `(log x)^{2+1/10}`.**

⛔ **AND THE CLAIM IS ABOUT THE ROUTE, NOT ABOUT A.7.**  This does **not** refute Lemma A.7 —
MRT prove it, and by other means.  It says only that **`renormalise` alone cannot be the
supplier**, which is exactly the sort of thing that is cheap to assume and expensive to assume
wrongly.  *Naming the `f` that breaks a route is worth more than another attempt to walk it.* -/

/-- `‖1 − λ(p)‖ = 2` at every prime — exact, no asymptotics. -/
theorem norm_one_sub_liouvilleC_prime {p : ℕ} (hp : p.Prime) :
    ‖1 - liouvilleC p‖ = 2 := by
  rw [liouvilleC_prime hp]
  norm_num

/-- **THE NORM-FORM PRIME SUM AT LIOUVILLE IS TWICE THE PRIME HARMONIC SUM.**  The identity
`renormalise`'s error factor sits on top of, at the `f` that breaks the route. -/
theorem sum_norm_one_sub_liouvilleC (x : ℝ) :
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, ‖1 - liouvilleC p‖ / (p : ℝ)
      = 2 * ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, 1 / (p : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [norm_one_sub_liouvilleC_prime (Finset.mem_filter.mp hp).2]
  ring

/-! ### ⛔⛔ THE HARDCODED-WITNESS SWEEP — I FLAGGED ONE AND STOPPED; HERE IS THE SET

One beat ago I applied compiler's `coreShort` lesson, found `landed_halasz_exponent_weaker_than_a6`
carrying a hardcoded witness, flagged it, and moved on.  **That is "a gate that checks each claim
never checks the set" — committed inside my own audit, on the day I quote the law.**  A defect
class is never one instance; the first one found is a sample.

Swept by READING each statement (a regex pass over-collected 20 names including structural lemmas
like `exp_neg_avg`; a loose probe is not a census):

**COMPARISON-TYPE — the true class.  A landed value against a target, BOTH literal, so the
theorem keeps proving when the relationship it names dies:**
* `landed_halasz_exponent_weaker_than_a6` — `1/(32e) < 1/16`  *(flagged last beat)*
* `landed_halasz_M_rate_weaker_than_a6` — `1/e < 1/2`
* `mrtA4ii_sixteenth_suffices` — `1/6 − 1/(3π) < 1/16`
* `landed_route_below_a4ii_target` — `1/32 < 1/6 − 1/(3π)`
* `mrtA5_rho_margin` — `3/50 < 1/6 − 1/(3π)`
* `renormalise_error_logpower_stronger` — carries A.7's `1/10` as a literal

**IDENTITY-TYPE — weaker: these go IRRELEVANT rather than MISLEADING, because they assert no
relationship that can quietly die:** `mrtA3_T0_exponent` (`1/16 − 2/16 = −(1/16)`) ·
`recenter_then_halve_constant` (`(√(1/4) − √(1/16))²/2 = 1/32`).

⇒ **SIX in the load-bearing class, not one.**  Every one of them compares a LANDED grade to a
TARGET EXPONENT, and in every one both sides are literals read from nothing.

⛔ **STILL FLAGGED, STILL NOT FIXED, AND THE REASON IS UNCHANGED:** deriving these needs A.6's and
A.7's exponents abstracted out of `MRTLemmaA6`/`MRTLemmaA7`'s STATEMENTS — iron rule 1,
Fable/Captain tier.  The 17:4x ruling covered the ambient hypotheses and nothing else.

🔑 *The lesson is not "I had a hardcoded constant."  It is that **I found one, published a flag,
and felt finished** — and the law against exactly that was already on the card I was quoting
while I did it.* -/

/-! ### ⭐ THE `1/32` IS NOT THE LANDED FLOOR'S STRENGTH — IT IS WHAT THE RECENTERING WAS FED

The narrowed question left open above was: *does any OTHER composition of the D-5 objects reach
a constant above `1/6 − 1/(3π)`?*  A constant census answers it in one place.

**`DistHalasz.dist_one_floor_pow` (`:179`) carries leading coefficient ONE:**
```
  log log x − (3/4)·log log(|b|+3) − 5·log log log(|b|+16) − C  ≤  𝔻²(1, n^{ib}; x)
```
But the recentering that produced `1/32` was fed a floor of **`1/4`**, not `1`:
`recenter_then_halve_constant : (√(1/4) − √(1/16))²/2 = 1/32`.

**Computed this session, with the landed value as a positive control:**
```
  (√(1/4) − √(1/16))²/2 = 0.03125   ← reproduces the landed 1/32 EXACTLY (control passes)
  (√1     − √(1/16))²/2 = 0.28125   = 9/32
  A.4(ii) target 1/6 − 1/(3π)       = 0.0605633…      9/32 clears it by 4.64×
```
⇒ **The `1/32` measures the recentering's INPUT, not the corpus's best floor.**  The two
arithmetic halves are landed below.

⛔⛔ **FENCED — THIS IS A CANDIDATE, NOT A RESULT, AND THE UNTESTED STEP IS NAMED.**  Whether
`dist_one_floor_pow`'s coefficient-1 floor can be fed to `dist_recenter` **at A.4(ii)'s
configuration** is **NOT** established here: its floor is stated for `𝔻²(1, n^{ib}; x)` at
`1 ≤ |b|` with its own `−(3/4)·loglog(|b|+3) − 5·logloglog(|b|+16) − C` corrections, and those
corrections must survive the recentering and the halving before any of this is a route.
**I have checked the ARITHMETIC and not the SUBSTITUTION.**

*An excited conclusion is a trigger to check, not a finding — and this one is exciting, which
is exactly why it ships fenced.*

⛔⛔ **REFUTED ONE BEAT LATER, BY THE CHECK THE FENCE EXISTED TO FORCE — AND THE FENCE NAMED THE
WRONG RISK.**  The substitution **cannot** work, and the reason is the FIRST ARGUMENT, one step
earlier and far simpler than the corrections I fenced on:
```
  dist_one_floor_pow    …  ≤ pretDistSq (fun _ => 1) (costwist b) x     ← the CONSTANT 1
  FarL2.plog_floor_real …  ≤ pretDistSq (lamChi χ)  (costwist v) X     ← λ·χ̄ — the 1/4 floor
  MRTLemmaA4ii          …  ∀ f, (∀ n, ‖f n‖ ≤ 1) → …                   ← an ARBITRARY 1-bounded f
```
**The coefficient-1 floor is a statement about `𝔻²(1, n^{ib}; x)` — how far the CONSTANT function
sits from a twist, which is a fact about the twist alone and about no datum at all.**  A.4(ii)
quantifies over arbitrary 1-bounded `f`, and `f = 1` is a single point of that domain.
⛔⛔ **AND THE SENTENCE THAT STOOD HERE WAS WRONG — CORRECTED BY THE CHECK I OWED MY OWN
CORRECTION.**  I wrote *"the `1/4` is FORCED BY THE OBJECT … which is the object A.4(ii) actually
has."*  **It is not.**  A.4(ii)'s conclusion is
```
  (1/6 − 1/(3π) − ε)·loglog X  ≤  pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X
```
— the **SIEVED datum `f·g_𝒥`, at ARBITRARY 1-bounded `f`.**  `FarL2`'s floor is stated for
`lamChi χ` = `λ·χ̄`, which is **another SPECIFIC function**, no more A.4(ii)'s object than the
constant `1` is.

⇒ **THE CORRECTED STATEMENT: NEITHER LANDED FLOOR IS STATED AT A.4(ii)'s GENERALITY.**  The
corpus has `𝔻²(1, ·)` at coefficient `1` and `𝔻²(λ·χ̄, ·)` at coefficient `1/4`; A.4(ii) needs
`𝔻²(f·g_𝒥, ·)` for arbitrary `f`.  The narrowed question is still answered **NO**, but for a
**broader** reason than I gave: not *"the `1/4` is forced"*, but *"no landed floor speaks about
A.4(ii)'s object at all."*

🔑 ***I REFUTED A CLAIM AND ASSERTED ITS REPLACEMENT IN THE SAME BREATH, AND ONLY THE REFUTED
HALF HAD BEEN CHECKED.***  The gate-checks-each-claim law applies to CORRECTIONS: **a replacement
deserves the same scrutiny as the thing it replaces**, and mine got none for one beat.

⇒ **`recenter_from_unit_floor` and `unit_floor_route_above_a4ii_target` remain TRUE and remain
LANDED — they are arithmetic — but they price a floor NOTHING SUPPLIES at A.4(ii)'s
configuration.  The narrowed question is answered: NO.**

🔑 *The fence was right to exist and wrong about where the danger was.  I fenced on "the
corrections must survive the recentering" and the killer was the first argument.  **Fencing on
the risk you can see does not protect against the risk you cannot — but the fence still did its
job, because it stopped the claim from being made.*** -/

/-- The recentering constant when the floor is `1` rather than `1/4`: `(√1 − √(1/16))²/2 = 9/32`.
*Companion to `recenter_then_halve_constant`, which is the same computation at floor `1/4`.* -/
theorem recenter_from_unit_floor :
    (Real.sqrt 1 - Real.sqrt (1/16)) ^ 2 / 2 = 9/32 := by
  have h16 : Real.sqrt (1/16) = 1/4 := by
    rw [show (1:ℝ)/16 = (1/4)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_one, h16]
  norm_num

/-- **A `9/32` floor WOULD clear A.4(ii)'s constant** — unlike the landed `1/32`
(`landed_route_below_a4ii_target`).  ⛔ The substitution that would produce `9/32` is NOT
established; see the fence above. -/
theorem unit_floor_route_above_a4ii_target :
    1/6 - 1/(3 * Real.pi) < (9:ℝ)/32 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h : 0 < 1/(3 * Real.pi) := by positivity
  have h6 : (1:ℝ)/6 < 9/32 := by norm_num
  linarith

/-! ## ⭐ A.4(ii)'S FLOOR CANNOT COME FROM `f` — IT COMES FROM THE SIEVED-OUT PRIMES

The section above established that **no landed floor is stated at A.4(ii)'s
generality**: the corpus holds `𝔻²(1, ·)` at leading coefficient `1` and
`𝔻²(λ·χ̄, ·)` at `1/4`, and each is a floor for ONE SPECIFIC function, whereas
A.4(ii) quantifies over an ARBITRARY 1-bounded `f`.

The reduction below says that generality is **not** the obstruction it looks
like.  `gJ` is `0/1`-valued, so at a prime where the sieve indicator VANISHES the
summand is `(1 − Re 0)/p = 1/p` **with `f` annihilated**; at every other prime the
summand is `≥ 0`, because `‖f p‖ ≤ 1` forces `Re(f p · gJ p · conj(costwist t p)) ≤ 1`.
So the entire floor is carried by the sieved-out primes, uniformly in `f`.

⇒ **A.4(ii) at arbitrary `f` reduces to a statement containing no `f` at all** — a
Mertens-type lower bound for `∑ 1/p` over the primes the sieve REMOVES.  That is
where `1/6 − 1/(3π)` has to come from, and it is sieve arithmetic, not a
pretentious-distance estimate.  *This is the orientation the wrong reason would
have cost: the next hand should not go hunting for a better constant inside a
landed floor.* -/
theorem sieved_primes_floor_le_pretDistSq_sifted
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
        (fun p => gJ 𝒥 Pseq Qseq p = 0), (1 : ℝ) / p
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  unfold pretDistSq
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum ?_
  intro p _hp
  by_cases h : gJ 𝒥 Pseq Qseq p = 0
  · simp [h]
  · simp only [h, if_false]
    refine div_nonneg ?_ (Nat.cast_nonneg p)
    have h1 : ‖f p‖ ≤ 1 := hf p
    have h2 : ‖gJ 𝒥 Pseq Qseq p‖ ≤ 1 := norm_gJ_le_one 𝒥 Pseq Qseq p
    have h3 : ‖(starRingEnd ℂ) (costwist t p)‖ = 1 := by
      rw [RCLike.norm_conj]; exact costwist_norm t p
    have hnorm : ‖f p * gJ 𝒥 Pseq Qseq p * (starRingEnd ℂ) (costwist t p)‖ ≤ 1 := by
      calc ‖f p * gJ 𝒥 Pseq Qseq p * (starRingEnd ℂ) (costwist t p)‖
          = ‖f p‖ * ‖gJ 𝒥 Pseq Qseq p‖ * ‖(starRingEnd ℂ) (costwist t p)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * 1 := by
            refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num))
              (le_of_eq h3) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hre := (Complex.re_le_norm
      (f p * gJ 𝒥 Pseq Qseq p * (starRingEnd ℂ) (costwist t p))).trans hnorm
    linarith

/-- ⭐ **THE SIEVED-OUT PRIMES, NAMED ARITHMETICALLY.**  Companion to
`sieved_primes_floor_le_pretDistSq_sifted`, which reduced A.4(ii)'s floor to a sum over
the primes the sieve REMOVES.  This says which primes those are: at a prime `p`, the
indicator `gJ` vanishes **exactly when `p` lies in one of the blocks `[Pseq j, Qseq j]`,
`j ∈ 𝒥`** — MRT's Definition 2.1 intervals.

Together the two turn A.4(ii)'s floor into `∑ 1/p` over the primes of `⋃ⱼ [Pⱼ, Qⱼ]`,
which is a **Mertens-type block count** with no `f` and no pretentious distance in it. -/
theorem gJ_prime_eq_zero_iff (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    gJ 𝒥 Pseq Qseq p = 0 ↔ ∃ j ∈ 𝒥, Pseq j ≤ p ∧ p ≤ Qseq j := by
  have hb : ∀ j : ℕ, blockOmega (Pseq j) (Qseq j) p = 0 ↔ ¬(Pseq j ≤ p ∧ p ≤ Qseq j) := by
    intro j
    have h1 : blockOmega (Pseq j) (Qseq j) p
        = if Pseq j ≤ p ∧ p ≤ Qseq j then 1 else 0 := by
      simpa using blockOmega_prime_pow (P := Pseq j) (Q := Qseq j) (p := p) (k := 1)
        hp one_ne_zero
    rw [h1]; split_ifs with h <;> simp [h]
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) p = 0 := by
      intro j hj
      exact (hb j).mpr (fun hc => hcon ⟨j, hj, hc⟩)
    simp only [gJ, if_pos hall] at h
    exact one_ne_zero h
  · rintro ⟨j, hj, hle⟩
    simp only [gJ]
    rw [if_neg]
    intro hall
    exact ((hb j).mp (hall j hj)) hle

/-- ⭐ **THE BLOCK COUNT ITSELF, FROM SHARP MERTENS-2 — `∑ 1/p` OVER A BLOCK IS
`loglog Q − loglog P` UP TO `12/log Q + 12/log P`.**

Third of the A.4(ii) chain.  `sieved_primes_floor_le_pretDistSq_sifted` put the floor on the
sieved-out primes uniformly in `f`; `gJ_prime_eq_zero_iff` identified those primes as the ones
lying in the blocks `[Pⱼ, Qⱼ]`; this prices **one block**, by differencing the corpus's own
sharp Mertens-2 (`Salt.Mertens.mertens_second_sharp_real`, explicit constant `12`) at the two
endpoints.  The two error terms simply add — `mertensM` cancels in the difference, which is
why no unknown constant survives.

*This is the `loglog` scale A.4(ii) needs.*  It is NOT the windowed bound
`Salt/Entropy/Chowla/WindowMertensLower.lean` proves: that one is `∑ 1/p ≥ c/log H` for a
single short window — the right KIND at the wrong SIZE for this road. -/
theorem mertens_block_difference {s t : ℝ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    |(Salt.Mertens.SPartial t - Salt.Mertens.SPartial s)
        - (Real.log (Real.log t) - Real.log (Real.log s))|
      ≤ 12 / Real.log t + 12 / Real.log s := by
  have h1 := Salt.Mertens.mertens_second_sharp_real ht
  have h2 := Salt.Mertens.mertens_second_sharp_real hs
  have key : (Salt.Mertens.SPartial t - Salt.Mertens.SPartial s)
        - (Real.log (Real.log t) - Real.log (Real.log s))
      = (Salt.Mertens.SPartial t - (Real.log (Real.log t) + Salt.Mertens.mertensM))
        - (Salt.Mertens.SPartial s - (Real.log (Real.log s) + Salt.Mertens.mertensM)) := by
    ring
  rw [key]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- ⭐⭐ **MRT'S `f`-ELIMINATION (A.4's display) — THE STEP THE WHOLE FAR ARM TURNS ON.**

Read from the source (`docs/sources/1503.05121v3.pdf`, Lemma A.4(ii)'s proof): MRT do **not**
recenter against a twist floor.  They AVERAGE the pretentious distance at `t` and at the
minimiser `t₁`.  Since `t₁` attains the infimum, `𝔻(f,t₁)² ≤ 𝔻(f,t)²`, so
`𝔻(f,t)² ≥ ½𝔻(f,t)² + ½𝔻(f,t₁)²`; the two twists then combine by `costwist_conj_avg` into a
single `cos((t−t₁)·log p/2)` factor, and `‖f p‖ ≤ 1` kills `f` entirely:

`ℜ(f(p)·p^{−i(t+t₁)/2}·cos θ) ≤ |cos θ|`.

⇒ **the bound below carries NO `f` at all.**  This is why A.4(ii) needs no floor at
arbitrary `f`: the averaging removes the datum before any floor is required.  What remains on
MRT's road is the cos-average over primes (mid range) and Erdős–Turán + Vinogradov–Korobov
(large `|t−t₁|`) — neither of which is attempted here. -/
theorem pretDistSq_ge_cos_average {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {t t₁ X : ℝ}
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X) :
    ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
        (1 - |Real.cos ((t - t₁) * Real.log p / 2)|) / (p : ℝ)
      ≤ pretDistSq f (costwist t) X := by
  have key : ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
      (1 - |Real.cos ((t - t₁) * Real.log p / 2)|) / (p : ℝ)
      ≤ (pretDistSq f (costwist t) X + pretDistSq f (costwist t₁) X) / 2 := by
    unfold pretDistSq
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    set θ : ℝ := (t - t₁) * Real.log p / 2 with hθdef
    set w : ℂ := f p * (costwist (-((t + t₁) / 2)) p * Complex.cos ((θ : ℝ) : ℂ)) with hwdef
    set A : ℝ := (f p * (starRingEnd ℂ) (costwist t p)).re with hAdef
    set B : ℝ := (f p * (starRingEnd ℂ) (costwist t₁ p)).re with hBdef
    have hid : f p * (starRingEnd ℂ) (costwist t p) + f p * (starRingEnd ℂ) (costwist t₁ p)
        = w + w := by
      rw [costwist_conj, costwist_conj, ← mul_add, hwdef]
      have h2 := costwist_conj_avg t t₁ p
      have h3 : costwist (-t) p + costwist (-t₁) p
          = 2 * (costwist (-((t + t₁) / 2)) p * Complex.cos ((θ : ℝ) : ℂ)) := by
        rw [hθdef]
        field_simp at h2
        linear_combination h2
      rw [h3]; ring
    have hnorm : ‖w‖ ≤ |Real.cos θ| := by
      rw [hwdef, norm_mul, norm_mul, costwist_norm, one_mul,
        ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      calc ‖f p‖ * |Real.cos θ| ≤ 1 * |Real.cos θ| :=
            mul_le_mul_of_nonneg_right (hf p) (abs_nonneg _)
        _ = |Real.cos θ| := one_mul _
    have hre : A + B ≤ 2 * |Real.cos θ| := by
      have h := congrArg Complex.re hid
      rw [Complex.add_re, Complex.add_re] at h
      have hw : w.re ≤ |Real.cos θ| := (Complex.re_le_norm w).trans hnorm
      rw [hAdef, hBdef]
      linarith
    have hrw : ((1 - A) / (p : ℝ) + (1 - B) / (p : ℝ)) / 2
        = (2 - (A + B)) / (2 * (p : ℝ)) := by
      field_simp; ring
    have hdiff : (2 - (A + B)) / (2 * (p : ℝ)) - (1 - |Real.cos θ|) / (p : ℝ)
        = (2 * |Real.cos θ| - (A + B)) / (2 * (p : ℝ)) := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ (2 * |Real.cos θ| - (A + B)) / (2 * (p : ℝ)) :=
      div_nonneg (by linarith) (by positivity)
    rw [hrw]
    linarith
  linarith

/-- ⭐ **`∫₀¹ |cos(πt)| dt = 2/π` — THE CONSTANT BEHIND MRT'S `(1 − 2/π)`.**

Next piece of MRT's own road for A.4(ii) (source `docs/sources/1503.05121v3.pdf`, display
(A.5)): after the averaging step eliminates `f` (`pretDistSq_ge_cos_average`), the mid range
`(log X)^{1/16}/2 ≤ |t−t₁| ≤ (log X)^{20}` is closed by a short-segment splitting whose value
is `1 − ∫₀¹|cos πt|dt`.  This lemma supplies that integral.

`cos(πt) ≥ 0` on `[0, ½]` and `≤ 0` on `[½, 1]`, so the absolute value splits into two
signed integrals, each equal to `1/π`.

⛔ The splitting argument that CONSUMES this is not attempted here — only its constant. -/
theorem integral_abs_cos_pi_unit :
    (∫ t in (0:ℝ)..1, |Real.cos (Real.pi * t)|) = 2 / Real.pi := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hcont : Continuous fun t : ℝ => |Real.cos (Real.pi * t)| :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => |Real.cos (Real.pi * t)|) MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hsplit : (∫ t in (0:ℝ)..(1/2), |Real.cos (Real.pi * t)|)
      + (∫ t in (1/2:ℝ)..1, |Real.cos (Real.pi * t)|)
      = ∫ t in (0:ℝ)..1, |Real.cos (Real.pi * t)| :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 (1/2)) (hint (1/2) 1)
  have hcos : ∀ a b : ℝ, (∫ t in a..b, Real.cos (Real.pi * t))
      = (Real.sin (Real.pi * b) - Real.sin (Real.pi * a)) / Real.pi := by
    intro a b
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (ne_of_gt hpi),
      integral_cos, smul_eq_mul]
    field_simp
  have h1 : (∫ t in (0:ℝ)..(1/2), |Real.cos (Real.pi * t)|) = 1 / Real.pi := by
    have hc : (∫ t in (0:ℝ)..(1/2), |Real.cos (Real.pi * t)|)
        = ∫ t in (0:ℝ)..(1/2), Real.cos (Real.pi * t) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩)
    rw [hc, hcos]
    have : Real.pi * (1/2) = Real.pi / 2 := by ring
    rw [this, Real.sin_pi_div_two, mul_zero, Real.sin_zero]
    ring
  have h2 : (∫ t in (1/2:ℝ)..1, |Real.cos (Real.pi * t)|) = 1 / Real.pi := by
    have hc : (∫ t in (1/2:ℝ)..1, |Real.cos (Real.pi * t)|)
        = ∫ t in (1/2:ℝ)..1, -Real.cos (Real.pi * t) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le
        (by nlinarith [hx.1]) (by nlinarith [hx.2]))
    rw [hc, intervalIntegral.integral_neg, hcos]
    have : Real.pi * (1/2) = Real.pi / 2 := by ring
    rw [this, Real.sin_pi_div_two, mul_one, Real.sin_pi]
    ring
  rw [← hsplit, h1, h2]
  ring

/-- ⭐⭐ **MRT'S A.4(i) — THE LOSS-FREE HALVING `𝔻(f·g_𝒥, p^{it})² ≥ ½·𝔻(f, p^{it})²`.**

Third piece of MRT's own road (source display (A.3)).  The corpus's `dist_split_A4`
(`DistSplit.lean:174`) is a DIFFERENT statement: it carries a window-loss term `W` and
concludes about `𝔻(g_𝒥, ·)`.  MRT's (i) has **no loss term at all** and is about the
PRODUCT — which works precisely because `g_𝒥` is `0/1`-valued.

Termwise, with `a = ℜ(f(p)·conj(p^{it})) ∈ [−1, 1]`:
* where `g_𝒥(p) = 1` the summand is `(1−a)/p`, and `(1−a)/2 ≤ (1−a)` since `a ≤ 1`;
* where `g_𝒥(p) = 0` the summand is `1/p`, and `(1−a)/2 ≤ 1` since `−1 ≤ a`.

This is the `½` of `1/6 − 1/(3π) = (½)·(1 − 2/π)·(⅓)`.  Composed with `M ≥ ⅛·loglog X` it is
MRT's high-`M` remark verbatim: `𝔻(f g_𝒥, p^{it})² ≥ (1/16)·loglog X`. -/
theorem mrtA4i_halving (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    (1 / 2) * pretDistSq f (costwist t) X
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  unfold pretDistSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro p hp
  dsimp only
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  set z : ℂ := f p * (starRingEnd ℂ) (costwist t p) with hzdef
  set a : ℝ := z.re with hadef
  have hzn : ‖z‖ ≤ 1 := by
    rw [hzdef, costwist_conj, norm_mul, costwist_norm, mul_one]
    exact hf p
  have ha1 : a ≤ 1 := by
    have := Complex.re_le_norm z
    rw [hadef]; linarith
  have ha2 : -1 ≤ a := by
    have h := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at h
    rw [hadef]; linarith
  by_cases hg : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) p = 0
  · -- the prime survives the sieve: `g_𝒥(p) = 1`, both sides share the summand
    have h1 : gJ 𝒥 Pseq Qseq p = 1 := by simp only [gJ, if_pos hg]
    rw [h1, mul_one, ← hzdef, ← hadef]
    have hnn : 0 ≤ (1 - a) / (p : ℝ) := div_nonneg (by linarith) hppos.le
    linarith
  · -- the prime is sieved out: `g_𝒥(p) = 0`, the summand is `1/p` and `f` is annihilated
    have h0 : gJ 𝒥 Pseq Qseq p = 0 := by simp only [gJ, if_neg hg]
    rw [h0, mul_zero, zero_mul, Complex.zero_re]
    have hdiff : (1 - 0) / (p : ℝ) - (1 / 2) * ((1 - a) / (p : ℝ))
        = ((1 + a) / 2) / (p : ℝ) := by
      field_simp; ring
    have hnn : 0 ≤ ((1 + a) / 2) / (p : ℝ) := div_nonneg (by linarith) hppos.le
    linarith

/-- ⭐ **MRT'S HIGH-`M` REMARK, VERBATIM: `𝔻(f g_𝒥, p^{it})² ≥ (1/16)·loglog X`.**

Source, Lemma A.4(ii)'s opening: *"when `M(f;X) ≥ ⅛ log log X`, part (i) implies that,
whenever `|t| ≤ X`, we have `D(f g_𝒥, p^{it}; X)² ≥ (1/16) log log X` which is sufficient."*
This is that sentence, composed from `mrtA4i_halving` in one step.

`hinf` is the minimality of `mrtM` at the frequency `t`, supplied by the caller — the
`|t| ≤ X` side condition of MRT's sentence lives there.

⛔ `1/16 = 0.0625` clears A.4(ii)'s target `1/6 − 1/(3π) = 0.0605634…` by only `0.0019366`;
the margin is real but thin, and it is MRT's, not a choice of ours. -/
theorem mrtA4ii_high_M_sixteenth (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hM : (1 / 8) * Real.log (Real.log X) ≤ mrtM f X)
    (hinf : mrtM f X ≤ pretDistSq f (costwist t) X) :
    (1 / 16) * Real.log (Real.log X)
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  have h := mrtA4i_halving f Pseq Qseq 𝒥 X t hf
  linarith

/-- ⭐ **THE `⅓` OF MRT'S CONSTANT — THE EXPONENT GAP AT `Y = exp((log X)^{2/3+ε})`.**

Last of the three factors in `1/6 − 1/(3π) = (½)·(1 − 2/π)·(⅓)`.  MRT's display (A.5) ends
`… ≥ (1 − 2/π)·log(log X / log Y) + O(1)`, and their `Y` is `exp((log X)^{2/3+ε})`, so the
`log(log X / log Y)` factor is exactly `(⅓ − ε)·loglog X`.

Stated first as pure algebra in `L = log X`, then at MRT's own `Y`. -/
theorem mrt_exponent_gap (L ε : ℝ) (hL : 0 < L) :
    Real.log (L / L ^ ((2 : ℝ) / 3 + ε)) = ((1 : ℝ) / 3 - ε) * Real.log L := by
  rw [Real.log_div (ne_of_gt hL) (ne_of_gt (Real.rpow_pos_of_pos hL _)), Real.log_rpow hL]
  ring

/-- **The same, at MRT's `Y = exp((log X)^{2/3+ε})`.**  `hX : 1 < log X` is `X > e`, which
`MRTPropA3Ambient` already supplies in the weak form `exp 1 ≤ X`. -/
theorem mrt_exponent_gap_at_Y (X ε : ℝ) (hX : 1 < Real.log X) :
    Real.log (Real.log X / Real.log (Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε))))
      = ((1 : ℝ) / 3 - ε) * Real.log (Real.log X) := by
  rw [Real.log_exp]
  exact mrt_exponent_gap (Real.log X) ε (by linarith)

/-- ⭐⭐⭐ **A.4(ii)'S CONSTANT, DECOMPOSED — AND EVERY FACTOR IS NOW SEPARATELY LANDED.**

`1/6 − 1/(3π) = (½)·(1 − 2/π)·(⅓)`, where each factor is a distinct step of MRT's own
proof and each is in the kernel:

* `½` — `mrtA4i_halving` (their display (A.3), the loss-free halving);
* `1 − 2/π` — `integral_abs_cos_pi_unit` (`∫₀¹|cos πt| dt = 2/π`, their display (A.5));
* `⅓` — `mrt_exponent_gap` (the gap at `Y = exp((log X)^{2/3+ε})`).

⇒ **nothing about A.4(ii)'s constant is arbitrary, and nothing in it asks for a better
floor.**  ⛔ This is an identity between real numbers, NOT a proof of A.4(ii): the analytic
steps that PRODUCE the three factors on the road — the short-segment splitting and
Erdős–Turán + Vinogradov–Korobov — are not attempted. -/
theorem mrtA4ii_constant_decomposition :
    (1 : ℝ) / 6 - 1 / (3 * Real.pi) = (1 / 2) * (1 - 2 / Real.pi) * (1 / 3) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- ⭐ **THE RESTRICTION TO `Y < p ≤ X` — THE EXACT OBJECT MRT'S (A.5) CONSUMES.**

The last link of MRT's display (A.4): having eliminated `f` by averaging
(`pretDistSq_ge_cos_average`), they DROP the primes `p ≤ Y` before applying the
short-segment splitting.  Legitimate because every summand is `≥ 0` (`|cos| ≤ 1`), so
restricting the index set only decreases the sum.

⇒ this hands the next hand the sum over `Y < p ≤ X` that (A.5) is stated about.
⛔ The splitting argument itself is still not attempted. -/
theorem pretDistSq_ge_cos_average_restricted {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {t t₁ X Y : ℝ}
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X) :
    ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
        (1 - |Real.cos ((t - t₁) * Real.log p / 2)|) / (p : ℝ)
      ≤ pretDistSq f (costwist t) X := by
  refine le_trans ?_ (pretDistSq_ge_cos_average hf hmin)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro p hp _
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hcos : |Real.cos ((t - t₁) * Real.log p / 2)| ≤ 1 := Real.abs_cos_le_one _
  exact div_nonneg (by linarith) hppos.le

/-- ⭐ **`|cos(πx)| = cos(π·‖x‖)` WHERE `‖x‖` IS THE DISTANCE TO THE NEAREST INTEGER.**

The bridge certifying that our landed bound is **literally** MRT's (A.4) final line rather
than a variant of it.  MRT write the summand as `1 − cos(π‖(t−t₁)·log p/(2π)‖)`; ours is
`1 − |cos((t−t₁)·log p/2)|`.  At `x = θ/π` this identity says they are the same number.

*Checked against mathlib first — it has `abs_cos_le_one`, `abs_cos_int_mul_pi` and
`abs_sub_round`, but no `cos`-vs-`round` identity; this is a genuine gap.* -/
theorem abs_cos_pi_mul_eq_cos_pi_mul_dist_round (x : ℝ) :
    |Real.cos (Real.pi * x)| = Real.cos (Real.pi * |x - round x|) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set n : ℤ := round x with hndef
  set r : ℝ := x - (n : ℝ) with hrdef
  have hr2 : |r| ≤ 1 / 2 := by rw [hrdef, hndef]; exact abs_sub_round x
  have hrb := abs_le.mp hr2
  have hx : Real.pi * x = (n : ℝ) * Real.pi + Real.pi * r := by rw [hrdef]; ring
  have hcos : Real.cos (Real.pi * x) = (-1 : ℝ) ^ n * Real.cos (Real.pi * r) := by
    rw [hx, Real.cos_add, Real.sin_int_mul_pi, zero_mul, sub_zero, Real.cos_int_mul_pi]
  have hnn : 0 ≤ Real.cos (Real.pi * r) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · nlinarith [hrb.1, hpi]
    · nlinarith [hrb.2, hpi]
  rw [hcos, abs_mul]
  have hsign : |(-1 : ℝ) ^ n| = 1 := by simp
  rw [hsign, one_mul, abs_of_nonneg hnn]
  rcases abs_cases r with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
  · rw [h1, mul_neg, Real.cos_neg]

/-- ⭐⭐ **OUR SUMMAND *IS* MRT'S SUMMAND — CERTIFIED, NOT ASSERTED.**

MRT's (A.4) ends with `∑_{Y<p≤X} (1 − cos(π‖(t−t₁)·log p/(2π)‖))/p`, where `‖·‖` is the
distance to the nearest integer.  Our landed bound
(`pretDistSq_ge_cos_average_restricted`) carries `1 − |cos((t−t₁)·log p/2)|`.

At `u = t − t₁` and `L = log p` these are **the same real number**.

*Tonight's recurring defect was assuming an object matched a name; this is the same
question answered in the kernel instead of by inspection.* -/
theorem mrtA4_summand_matches_source (u L : ℝ) :
    |Real.cos (u * L / 2)|
      = Real.cos (Real.pi * |u * L / (2 * Real.pi)
          - round (u * L / (2 * Real.pi))|) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h := abs_cos_pi_mul_eq_cos_pi_mul_dist_round (u * L / (2 * Real.pi))
  have hx : Real.pi * (u * L / (2 * Real.pi)) = u * L / 2 := by field_simp
  rw [hx] at h
  exact h

/-- ⭐⭐⭐ **THE FAR ARM REDUCES TO EXACTLY ONE OPEN ESTIMATE.**

Everything MRT's mid-range argument needs, *except* the short-segment splitting itself, is
now landed — so the splitting can be carried as a single explicit hypothesis and the rest
composes in the kernel:

* `mrtA4i_halving` — `𝔻(f·g_𝒥)² ≥ ½·𝔻(f)²` (their (A.3));
* `pretDistSq_ge_cos_average_restricted` — the `f`-free cos bound over `Y < p ≤ X` (their (A.4));
* `hsplit` — **THE ONE OPEN PIECE**: their (A.5), the short-segment splitting, whose value is
  `(1 − 2/π)·log(log X / log Y)`.  *Assumed here, NOT proved.*

⇒ **the remaining analytic content of A.4(ii)'s far arm is `hsplit` and nothing else.**  With
`mrt_exponent_gap_at_Y` supplying `log(log X/log Y) = (⅓ − ε)·loglog X` and
`mrtA4ii_constant_decomposition` supplying `(½)·(1 − 2/π)·(⅓) = 1/6 − 1/(3π)`, the constant
falls out of this bound by arithmetic alone.

⛔ Stating a hypothesis is not discharging it: `hsplit` is exactly the estimate nobody has
proved here, and the separate large-`|t−t₁|` branch (Erdős–Turán + VK) is not addressed by
this theorem at all. -/
theorem mrtA4ii_far_of_cos_average
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ Y : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X)
    (hsplit : (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y)
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos ((t - t₁) * Real.log p / 2)|) / (p : ℝ)) :
    (1 / 2) * ((1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y))
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  have hhalf := mrtA4i_halving f Pseq Qseq 𝒥 X t hf
  have hcos := pretDistSq_ge_cos_average_restricted (Y := Y) hf hmin
  linarith

/-! ## ⭐ THE ONE OPEN ESTIMATE, NAMED — MRT'S SHORT-SEGMENT SPLITTING (their (A.5))

`mrtA4ii_far_of_cos_average` carries the splitting as an ANONYMOUS hypothesis `hsplit`.  A
hypothesis nobody can cite is a hypothesis nobody can dispatch, so it gets a name here, in the
file's own idiom (`MRTLemmaA6`, `MRTLemmaA7`, `MRTPropA3`).

Source: `docs/sources/1503.05121v3.pdf`, display (A.5) — *"we get as in [10, Proof of Lemma 2.3]
by splitting `p` into short segments `(y, y(1 + (log X)^{-30})]`"*.  The value MRT extract is
`1 − ∫₀¹|cos πt| dt`, which `integral_abs_cos_pi_unit` has already reduced to `1 − 2/π`, and
the `O(1)` is carried in-statement as an explicit `C` (the S5 law: no hidden asymptotics).

⛔ **THIS IS A STATEMENT, NOT A THEOREM. NOTHING BELOW PROVES IT** — it is the exact remaining
analytic content of A.4(ii)'s mid range, written so it can be cited, dispatched, and tracked. -/
def MRTShortSegmentSplitting : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u ε : ℝ), 0 < ε → Real.exp 1 ≤ X →
    Y = Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε)) →
    (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |u| →
    |u| ≤ (Real.log X) ^ (20 : ℕ) →
      (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
              (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ)

/-- ⭐⭐ **THE NAMED ESTIMATE DISCHARGES THE FAR ARM — the composition, in the kernel.**

Given `MRTShortSegmentSplitting` and the minimality of `t₁`, the far arm's bound follows from
already-landed pieces: the splitting supplies the `f`-free sum's lower bound, and
`mrtA4ii_far_of_cos_average` turns it into a bound on `𝔻(f·g_𝒥, costwist t)²`.

⇒ **the remaining analytic debt of A.4(ii)'s mid range is EXACTLY `MRTShortSegmentSplitting`**
(the large-`|t−t₁|` branch, Erdős–Turán + VK, is a separate case and untouched here). -/
theorem mrtA4ii_far_of_named_splitting (hsplit : MRTShortSegmentSplitting)
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hε : 0 < ε) (hXe : Real.exp 1 ≤ X)
    (hlo : (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |t - t₁|)
    (hhi : |t - t₁| ≤ (Real.log X) ^ (20 : ℕ))
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X) :
    ∃ C : ℝ, 0 ≤ C ∧
      (1 / 2) * ((1 - 2 / Real.pi)
          * Real.log (Real.log X
              / Real.log (Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε)))) - C)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  obtain ⟨C, hC0, hC⟩ := hsplit
  refine ⟨C, hC0, ?_⟩
  have hs := hC X (Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε))) (t - t₁) ε hε hXe rfl hlo hhi
  have hhalf := mrtA4i_halving f Pseq Qseq 𝒥 X t hf
  have hcos := pretDistSq_ge_cos_average_restricted
    (Y := Real.exp ((Real.log X) ^ ((2 : ℝ) / 3 + ε))) hf hmin
  linarith

/-! ## ⭐ THE OTHER OPEN ESTIMATE, NAMED — MRT'S LARGE-`|t−t₁|` EQUIDISTRIBUTION

The mid range now has a citable target (`MRTShortSegmentSplitting`).  Its sibling did not, and
an unnamed obligation is one no brief can dispatch — so the large branch gets the same
treatment, and A.4(ii)'s three arms become three named objects.

Source, Lemma A.4(ii)'s proof: *"when `|t − t₁| > (log X)^{20}` and `|t| ≤ X`,
`(t−t₁)·log p / 2π` is equidistributed (mod 1) by the Erdős–Turán inequality and the
Vinogradov–Korobov"* zero-free region.

⚖️ **THE PRICING IS ASYMMETRIC AND THAT IS THE USEFUL PART** (rows 19d/19j): **VK is LANDED
UNCONDITIONALLY** in this corpus — `Salt.Vk.zeta_zero_free_region_pow`, producer
`zeta_growth_pow : ZetaGrowthPow` taking NO hypotheses — while **Erdős–Turán is ABSENT**
(asserted to the sibling standard: seven named `# <Name> inequality` headers answer the same
arm, including Kusmin–Landau in the very directory the target would live in).

⛔ **A STATEMENT, NOT A THEOREM.  NOTHING HERE PROVES IT** — and note the conclusion is written
in the SAME shape as the mid-range Prop, so a discharger of either feeds the same consumer. -/
def MRTLargeRangeEquidistribution : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u : ℝ), Real.exp 1 ≤ X → |u| ≤ 2 * X →
    (Real.log X) ^ (20 : ℕ) < |u| →
      (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
              (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ)

/-- ⭐⭐ **A.4(ii)'s THREE ARMS, ALL NAMED — THE CAMPAIGN'S REMAINING DEBT IN ONE STATEMENT.**

* **HIGH `M`** — `mrtA4ii_high_M_sixteenth`, **LANDED** (`1/16 = 0.0625` clears the
  `0.0605634…` target; MRT's own remark).
* **MID RANGE** — `MRTShortSegmentSplitting`, **OPEN**, discharges via
  `mrtA4ii_far_of_named_splitting`.
* **LARGE RANGE** — `MRTLargeRangeEquidistribution`, **OPEN**; its heavy half (VK) is landed
  and hypothesis-free, its light half (Erdős–Turán) is absent.

This theorem is the trivial disjunction-elimination shape: **either open Prop, plus `t₁`'s
minimality, yields the far-arm bound** — recorded so the two obligations are visibly
interchangeable at the consumer. -/
theorem mrtA4ii_far_of_either_estimate
    (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X Y t t₁ : ℝ) (C : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmin : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X)
    (hbound : (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter
              (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos ((t - t₁) * Real.log p / 2)|) / (p : ℝ)) :
    (1 / 2) * ((1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C)
      ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  have hhalf := mrtA4i_halving f Pseq Qseq 𝒥 X t hf
  have hcos := pretDistSq_ge_cos_average_restricted (Y := Y) hf hmin
  linarith

/-! ## ⭐⭐ THE MISSING MIDDLE OF THE RATIFIED SPINE — MRT THEOREM A.2

The reduced spine's PRIMARY is **A.1**, its engine is **A.3**, and MRT's own chain runs
**A.3 ⇒ A.2 ⇒ A.1** (source line 1728: *"implies Proposition A.3 and thus also Theorem A.2"*).
Measured with a sibling control: the corpus states **A.1** (`MRTThmA1`) and **A.3**
(`MRTPropA3`) and has **no A.2 and no bridge** — the same description arm that finds
`# MRT Theorem A.1`, `# MRT Proposition A.3` and `# Block C — the λ-quality supply` returns
**nothing** for A.2. It is not in the ratified deletions (Lemma 2.2 · Thm 2.3 · the minor arc ·
E-5's split), so it is a genuine hole in the middle of the spine.

Source, extract line 1231 — A.2 is A.1's shape with the datum **SIFTED**: the mean is taken
over `n ∈ S`, which in this development is `f · gJ 𝒥 Pseq Qseq` — **the very object A.4(ii)
bounds.** That is why tonight's A.4(ii) work sits upstream of the primary rather than beside it.

⛔ **A STATEMENT, NOT A THEOREM, AND THE BRIDGES ARE NOT ATTEMPTED.** MRT get A.3 ⇒ A.2 by a
**Parseval bound** (*"the proof proceeds as [17, Theorem 3]; the first step is a Parseval
bound"*, line 1243) — named here so it can be dispatched, not discharged here. -/
def MRTThmA2 (C : ℝ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ X h : ℝ, 10 ≤ h → h ≤ X →
      (1 / X) * (∫ x in X..(2 * X),
          ‖mrtShortMean (fun n => f n * gJ 𝒥 Pseq Qseq n) h x‖ ^ 2)
        ≤ C * (Real.exp (-(mrtM f X)) * mrtM f X
              + (Real.log (Real.log h)) ^ 2 / Real.log h
              + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-- **The spine's shape, recorded: A.2 is A.1 with the datum sifted.**

Both sides quantify identically; the ONLY difference is that `MRTThmA2`'s integrand takes the
short mean of `f · g_𝒥` where `MRTThmA1`'s takes it of `f`. ⇒ **an A.2 discharged at `𝒥 = ∅`
IS A.1**, because `gJ ∅ Pseq Qseq n = 1` (the `∀ j ∈ ∅` is vacuous).

*This is the observation that makes the sifted work load-bearing for the primary rather than a
detour — and it is exactly the `𝒥 = ∅` degeneracy that killed my \"reduction\" three hours ago,
used here in the direction where it is TRUE.* -/
theorem mrtThmA1_of_mrtThmA2_empty (C : ℝ) (Pseq Qseq : ℕ → ℕ)
    (h2 : MRTThmA2 C Pseq Qseq ∅) : MRTThmA1 C := by
  intro f hf h1 hmul X h hh hhX
  have := h2 f hf h1 hmul X h hh hhX
  simpa [gJ] using this

/-! ## ⭐ THE ENDPOINT RECONCILIATION — CLOSED WINDOW vs HALF-OPEN, AT MOST ONE TERM

The Parseval assembly is landed (`parseval_bound_of_propA3_shape`, `MRTPropA3Bridge.lean:204`)
and its left-hand side is A.2's — **except for the window convention.**  `shortSum`
(`Lemma14.lean:479`) sums the HALF-OPEN `(x, x+h]`; `mrtShortMean` (`MRTThmA1.lean:60`) averages
the CLOSED `[x, x+h]` (that identification is `mem_mrtShortWindow`, already proved).

The gap is exactly `x ≤ n` versus `x < n`, so the two index sets differ **only at `n = x`** — a
natural equal to `x` on the nose, which exists for at most one `n`.  Hence for 1-bounded data
the two sums differ by **at most one term**, and the two MEANS by at most `1/h`.

⇒ this is the whole convention gap between the landed Parseval bound and `MRTThmA2`'s LHS,
priced.  ⛔ It does not close the bridge — the constant-matching to A.2's RHS is separate and
untouched. -/
theorem closed_open_window_card_le_one (x h : ℝ) :
    ((Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter (fun n : ℕ => ¬ (x < (n : ℝ)))).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
  have hxa : x ≤ (a : ℝ) := by
    have := ha.1.1
    exact_mod_cast (Nat.ceil_le.mp this)
  have hxb : x ≤ (b : ℝ) := by
    have := hb.1.1
    exact_mod_cast (Nat.ceil_le.mp this)
  have hax : (a : ℝ) ≤ x := not_lt.mp ha.2
  have hbx : (b : ℝ) ≤ x := not_lt.mp hb.2
  have : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast this

/-- **The two window conventions differ by at most ONE term**, hence — for 1-bounded data —
by at most `1` in the sum and `1/h` in the mean. -/
theorem shortWindow_closed_sub_open_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (x h : ℝ) :
    ‖(∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n)
        - ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter (fun n : ℕ => x < (n : ℝ)), f n‖ ≤ 1 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊) (fun n : ℕ => x < (n : ℝ)) f
  have hEq : (∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n)
      - ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter (fun n : ℕ => x < (n : ℝ)), f n
      = ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter (fun n : ℕ => ¬ (x < (n : ℝ))), f n := by
    rw [← hsplit]; ring
  rw [hEq]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun i _ => hf i)) ?_
  simpa using (Nat.cast_le (α := ℝ)).mpr (closed_open_window_card_le_one x h)

/-! ## ⭐⭐ THE LAST UNNAMED OBLIGATION — THE CONSTANT MATCH ON `A.3 ⇒ A.2`

Three of the spine's four gaps now have citable names.  The fourth was still prose: the landed
`parseval_bound_of_propA3_shape` delivers an explicit `B`-shaped bound, and `MRTThmA2` wants
MRT's `exp(−M)M + (log h)^{1/3}/P₁^{1/6−η} + (log X)^{−1/50}`.  **Matching those two is the
remaining analytic content of the bridge** (the assembly is landed, the endpoint is priced at
one term by `shortWindow_closed_sub_open_norm_le`).

⛔ **A STATEMENT.  NOT PROVED HERE, AND DELIBERATELY WEAK: it asks only that SOME admissible
constant exists**, because the discharger picks it — the same shape the door's `δ` has. -/
def MRTParsevalConstantMatch (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ MRTThmA2 C Pseq Qseq 𝒥

/-- ⭐⭐⭐ **THE WHOLE RATIFIED SPINE, CONDITIONALLY, IN ONE THEOREM.**

`MRTThmA1Statement` — the campaign's PRIMARY — follows from the single named obligation
`MRTParsevalConstantMatch` at `𝒥 = ∅`, via `mrtThmA1_of_mrtThmA2_empty`.

⇒ **this is the campaign's remaining debt expressed as a Lean implication rather than a
paragraph**: whoever discharges the constant match at the empty sieve has the primary.  The
mid- and large-range obligations (`MRTShortSegmentSplitting`, `MRTLargeRangeEquidistribution`)
sit beneath A.3 and feed A.4(ii), which is what supplies A.3's own hypothesis.

⛔ **NOTHING HERE PROVES ANY OF IT.**  The implication is real and the antecedent is open;
naming it is what lets a design session price the road instead of re-deriving it. -/
theorem mrtThmA1Statement_of_constantMatch (Pseq Qseq : ℕ → ℕ)
    (h : MRTParsevalConstantMatch Pseq Qseq ∅) : MRTThmA1Statement := by
  obtain ⟨C, hCpos, hA2⟩ := h
  exact ⟨C, hCpos, mrtThmA1_of_mrtThmA2_empty C Pseq Qseq hA2⟩

end Salt.MR

