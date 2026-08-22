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
twisted distance is bounded below by `(1/6 − 1/(3π) − ε)·loglog X`. -/
def MRTLemmaA4ii : Prop :=
  ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → |t| ≤ X → 0 < ε →
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

end Salt.MR
