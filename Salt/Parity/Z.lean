/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Basic
import Salt.Brun.M5BigO

/-!
# Parity — Z, the demand specification of the parity-breaking bilinear estimate

This module is the first formal existence of `Z`, the program's gap statement:
the precise demand specification of the parity-breaking bilinear estimate that
separates the entire landed corpus from the Twin Prime Conjecture.

## Module invariant (oracle-cleanliness, ratified amendment J4)

The import list of this file is EXACTLY `Mathlib`, `Salt.Basic`, and
`Salt.Brun.M5BigO`. In particular this module NEVER imports `Salt.HB` or
`Salt.TwinBar`. This is checkable by the import list alone and is the
definition's formal claim to carrying no exceptional-character oracle: no
`DirichletCharacter`, `LamTilde`, L-function, or `¬F` appears anywhere in the
inputs to `Z`. The `Salt.HB`/`Salt.TwinBar` insensitivity instantiations of the
`L0` closure schema live in the sibling file `Salt/Parity/Instances.lean`,
keeping this demand-spec module oracle-clean by construction.
-/

namespace Salt.Parity

/-- ρ(d): #{r < d : d ∣ r(r+2)} — the local twin density numerator.
    PINNED, not quantified: completions must share the TRUE twin Type-I
    main term (fixes the pass2 sketch's ∀g bug, which admitted a ≡ 0
    with g ≡ 0 as a completion). -/
def twinRho (d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun r => d ∣ r * (r + 2))).card

/-- The (n,n+2) Type-I congruence sum of weight `a` at level `d`, window `x`.
    NOTE: this is the ONLY functional through which the class reads `a` —
    pure Type-I is pinned by the TYPE, so Type-II bilinear data (M5 knob,
    fulcrum-pass2.md:82) is structurally inexpressible, not merely excluded. -/
noncomputable def typeISum (a : ℕ → ℝ) (d x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if d ∣ n * (n + 2) then a n else 0

/-- Pure Type-I error norm at divisor level x^θ. -/
noncomputable def typeIError (a : ℕ → ℝ) (θ : ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊,
    |typeISum a d x - (twinRho d : ℝ) / d * x|

/-- 𝒞(θ,A₀): nonnegative completions carrying the true twin Type-I data at
    level x^θ, quality (log x)^(−A₀), with a per-completion constant. -/
def Completion (θ A₀ : ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
    typeIError a θ x ≤ C * x / Real.log x ^ A₀

/-- ParityInv at grade (θ,A₀): E holds in EVERY completion.  Semantic
    (model-class) invariance — quantifies over the mechanism, not the method. -/
def ParityInv (θ A₀ : ℝ) (E : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, Completion θ A₀ a → E a

/-- Twin mass of a completion (consumers use the W5 shape ∀C ∃x). -/
noncomputable def twinMass (a : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if n.Prime ∧ (n + 2).Prime then a n else 0

/-- Twin-sufficiency: E semantically FORCES unbounded twin mass in every
    completion satisfying it.  The load-bearing lower-bound clause. -/
def TwinSufficient (θ A₀ : ℝ) (E : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a : ℕ → ℝ, Completion θ A₀ a → E a →
    ∀ C : ℝ, ∃ x : ℕ, C < twinMass a x

def oneWeight : ℕ → ℝ := fun _ => 1

/-- The Brun-grade twin-free completion 𝒜⁻ (the landable witness). -/
noncomputable def twinFree : ℕ → ℝ :=
  fun n => if n.Prime ∧ (n + 2).Prime then 0 else 1

/-- **Z — the demand specification, frozen.**  A twin proof must supply a
    predicate on completions that forces unbounded twin mass across the whole
    pure-Type-I model class AND holds for the true sequence.  No
    DirichletCharacter, no L-function, no exceptional-character oracle
    appears anywhere in the inputs.

    GRADE GUARD (ratified amendment J5).  The demand-force of `Z` is
    CONDITIONAL on true-sequence membership `oneWeight ∈ Completion θ A₀`.  On
    the certified window `θ ∈ (0, 1/2)` with `A₀ ≥ 0` this membership holds
    (`L1`), so `Z θ A₀` genuinely forces the Twin Prime Conjecture (`L5`).
    OUTSIDE that window — at any `(θ, A₀)` with `oneWeight ∉ Completion θ A₀` —
    `Z` TRIVIALIZES: the witness `E := (· = oneWeight)` satisfies it with
    `TwinSufficient` vacuous, carrying zero twin content
    (`Z_trivial_of_not_completion`).  Every downstream `Z`-claim therefore
    carries the `θ ∈ (0, 1/2)` window. -/
def Z (θ A₀ : ℝ) : Prop :=
  ∃ E : (ℕ → ℝ) → Prop, TwinSufficient θ A₀ E ∧ E oneWeight

/-- The OPEN full-quality parity barrier (stated, never assumed): a bounded-
    twin completion at EVERY quality.  M1/M2-grade target, D-class. -/
def ParityBarrier (θ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ a : ℕ → ℝ, Completion θ A₀ a ∧
    ∃ M : ℝ, ∀ x : ℕ, twinMass a x ≤ M

/-- **L0 — insensitivity closure schema [A].**  A closed proposition `P` — one
    that never reads the completion — is parity-invariant at every grade: it is
    the constant predicate `fun _ => P`, which holds in every completion iff `P`
    holds.  This is the formal content of "𝒟(¬F) ⊆ ParityInv" under semantic
    invariance; the landed-theorem instantiations live in
    `Salt/Parity/Instances.lean`. -/
theorem parityInv_of_closed (θ A₀ : ℝ) {P : Prop} (hP : P) :
    ParityInv θ A₀ (fun _ => P) := fun _ _ => hP

/-- **Grade guard [A] (ratified amendment J5).**  At any grade where the true
    sequence `oneWeight` is not a completion, `Z` is trivially satisfied by the
    single-point predicate `E := (· = oneWeight)`: `TwinSufficient` is vacuous
    (no completion equals `oneWeight`) and `E oneWeight` is `rfl`.  Makes the
    grade-degeneracy of `Z` kernel-visible. -/
theorem Z_trivial_of_not_completion {θ A₀ : ℝ}
    (h : ¬ Completion θ A₀ oneWeight) : Z θ A₀ := by
  refine ⟨fun a => a = oneWeight, ?_, rfl⟩
  intro a hc he _
  have he' : a = oneWeight := he
  rw [he'] at hc
  exact absurd hc h

end Salt.Parity
