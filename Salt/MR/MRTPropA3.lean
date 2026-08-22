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
a theorem — nothing proves it and nothing assumes it.

⚠️⚠️ **UNRESOLVED, FLAGGED 2026-08-22 04:1x, AFTER `MRTLemmaA4ii` WAS FOUND FALSE FOR
EXACTLY THIS REASON: THIS STATEMENT MAY CARRY NO LARGENESS ON `X`.**  Its only size
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
false — only that its guard against the `A4ii` defect is unverified.** -/
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

end Salt.MR
