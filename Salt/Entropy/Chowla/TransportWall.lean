/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The orthogonality wall: the transport-door impossibility triple (node TD-R2b)

A boundary-map exhibit.  The TD-R1 recon (`docs/exploration/boundary-map.md`,
"THE ORTHOGONALITY FINDING") adjudicated all three Siegel-oracle transport
candidates as WALLS.  The sharpest, candidate 3 (`AbstractSiegelOracle` in the
frozen probe `scratchpad/ProbeTD.lean`), is an **impossibility triple**: a single
weight `w : ℕ → ℝ` cannot simultaneously carry

* **slot 1 — boundedness.**  In its sharpest form the `±1`-normalization on the
  support: `w n ∈ {1, -1}` for `n ≥ 1` with `w 1 = 1` (`PmNormalized`).  The
  probe's literal slot 1 was the weaker windowed-first-moment budget
  `|∑ w n·(x-n)| ≤ D·x²`; that budget alone does not grade `w` to `±1`, and it is
  exactly the `±1` grade that lets slot 2 bite, so we freeze the sharp form.
* **slot 2 — the pair-collapse.**  `w(pN)·w(pN+p) = w(N)·w(N+1)` for every prime
  `p` and `N ≥ 1` (`PairCollapse`, the *shift-1* form).  This is precisely the
  hypothesis the landed rigidity engine `collapse_forces_completelyMult`
  consumes.  The probe's candidate 3 stated the *shift-2* variant
  `w(pN)·w(pN+2p) = w(N)·w(N+2)`; the constant witness satisfies that too
  (`const_satisfies_shift2`), but the *shift-2 ⟹ CM* direction is not the landed
  engine, so shift-1 is the form frozen here (shift-2 is a documented remark).
* **linkage — twin-detection.**  `w`'s pair-correlation actually separates a twin
  pair from a non-twin pair (`TwinDetecting`).  This is the minimal necessary
  condition for "the weight sees twins"; the probe's candidate-3 linkage
  (`0 ≤ p1PrimeSum` gated by `w x ≠ 0`) is orthogonal-by-construction — for the
  constant witness the gate is vacuous and the clause reduces to a statement about
  the twin carrier with no dependence on `w` at all — so we replace it with this
  honest, self-contained detection notion.

## The finding, frozen

`slots_force_completelyMult` restates the rigidity theorem: slot 1 ∧ slot 2 force
`w` into the completely-multiplicative `±1` class (`slots_iff_completelyMult` gives
the biconditional).  But that class contains **twin-blind** members: the constant
weight `w ≡ 1` passes both slots (`const_satisfies_slots`) yet has constant
pair-correlation `w(n)·w(n+2) = 1`, so it cannot separate any two pairs, twin or
not (`const_twin_blind`).  Hence:

* `orthogonality_wall` — `¬ ∀ w, PmNormalized w → PairCollapse w → TwinDetecting w`.
  Passing both slots does **not** force even the minimal twin-detection clause.
* `no_slot_derived_twin_linkage` — the abstract form: no linkage `L` can be both
  *slot-derivable* (`slots ⟹ L`) and *detection-sufficient* (`L ⟹ TwinDetecting`).
  The two proven parity mechanisms are structurally orthogonal: the entropy
  spine's slot 2 consumes a PAIR-COLLAPSE object, and a slot-passing weight can be
  twin-blind, so no first-moment / slot content composes into twin detection along
  this route.

## Honest scope

This exhibit rules out slot-satisfaction ALONE ever forcing twin detection — it
exhibits a slot-passing, twin-blind witness.  It does **not** rule out a cleverer
door whose *linkage clause pins `w` beyond the slots* (a stronger hypothesis that
excludes the constant witness).  The strong wall — "no completely-multiplicative
`±1` weight controls the twin carrier through the spine's chain" — is the Chowla /
twin-correlation open problem and is NOT claimed here; it is recorded as the prose
wall in the boundary map.  What is kernel-checked: the slots are jointly
satisfiable, and their satisfier class is twin-blind at a witness.
-/
import Salt.Entropy.Chowla.BoundaryMap

namespace Salt.Entropy.Chowla

/-! ### The three slots, as named Props -/

/-- **Slot 1 (boundedness), sharp form.**  The `±1`-normalization on the support:
`w n ∈ {1, -1}` for `n ≥ 1`, normalized by `w 1 = 1`.  This is the grade that lets
the rigidity engine fire; the probe's windowed-budget slot 1 is strictly weaker. -/
def PmNormalized (w : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → w n = 1 ∨ w n = -1) ∧ w 1 = 1

/-- **Slot 2 (pair-collapse), shift-1 form.**  Dilation-invariant pair correlation
`w(pN)·w(pN+p) = w(N)·w(N+1)` for every prime `p` and `N ≥ 1` — the exact
hypothesis of `collapse_forces_completelyMult`. -/
def PairCollapse (w : ℕ → ℝ) : Prop :=
  ∀ p N, p.Prime → 1 ≤ N → w (p * N) * w (p * N + p) = w N * w (N + 1)

/-- The probe's candidate-3 pair-collapse (shift-2 form), kept as a remark carrier.
The landed rigidity engine consumes the shift-1 form, so this is documented, not
used to force multiplicativity. -/
def PairCollapseShift2 (w : ℕ → ℝ) : Prop :=
  ∀ p N, p.Prime → w (p * N) * w (p * N + 2 * p) = w N * w (N + 2)

/-- **The linkage (twin-detection), honest minimal form.**  `w`'s pair-correlation
`n ↦ w(n)·w(n+2)` separates at least one genuine twin pair from at least one
non-twin pair.  A weight whose correlation cannot even do this cannot "see" twins,
so this is a necessary condition for any real twin detector — the weakest honest
clause, which makes the wall (that the slots cannot force it) the strongest. -/
def TwinDetecting (w : ℕ → ℝ) : Prop :=
  ∃ m n, (m.Prime ∧ (m + 2).Prime) ∧ ¬ (n.Prime ∧ (n + 2).Prime) ∧
    w m * w (m + 2) ≠ w n * w (n + 2)

/-! ### slot 1 ∧ slot 2 ⟹ CM±1 (the rigidity engine, restated for the wall) -/

/-- **Slots force complete multiplicativity.**  The boundedness slot (`±1`-grade)
and the pair-collapse slot together drop `w` into the real completely-multiplicative
`±1` class — a direct restatement of the landed `collapse_forces_completelyMult`. -/
theorem slots_force_completelyMult (w : ℕ → ℝ)
    (hb : PmNormalized w) (hc : PairCollapse w) :
    ∀ a b, 1 ≤ a → 1 ≤ b → w (a * b) = w a * w b :=
  collapse_forces_completelyMult w hb.1 hb.2 hc

/-- **The slot ⟺ CM±1 characterization.**  On a `±1`-normalized weight, the
pair-collapse slot is *equivalent* to complete multiplicativity — the satisfier
class of the two slots is exactly the completely-multiplicative `±1` class
(the landed `collapse_iff_completelyMult`). -/
theorem slots_iff_completelyMult (w : ℕ → ℝ) (hb : PmNormalized w) :
    PairCollapse w ↔ (∀ a b, 1 ≤ a → 1 ≤ b → w (a * b) = w a * w b) :=
  collapse_iff_completelyMult w hb.1 hb.2

/-! ### The twin-blind witness: the constant weight passes both slots -/

/-- The constant weight `w ≡ 1` satisfies slot 1 and slot 2 (shift-1). -/
theorem const_satisfies_slots :
    PmNormalized (fun _ => (1 : ℝ)) ∧ PairCollapse (fun _ => (1 : ℝ)) := by
  refine ⟨⟨fun n _ => Or.inl rfl, rfl⟩, ?_⟩
  intro p N _ _
  norm_num

/-- The constant weight also satisfies the probe's shift-2 pair-collapse — so the
wall below refutes candidate 3's *literal* slot pairing as well. -/
theorem const_satisfies_shift2 : PairCollapseShift2 (fun _ => (1 : ℝ)) := by
  intro p N _
  norm_num

/-- **Twin-blind.**  The constant weight's pair-correlation is identically `1`, so it
separates no two pairs — in particular no twin pair from a non-twin pair.  It is a
slot-passing member of the class that carries zero twin information. -/
theorem const_twin_blind : ¬ TwinDetecting (fun _ => (1 : ℝ)) := by
  rintro ⟨m, n, -, -, hne⟩
  simp at hne

/-! ### The orthogonality wall -/

/-- **THE ORTHOGONALITY WALL.**  There is no derivation of twin-detection from the
two slots alone: boundedness (`±1`-grade) and the pair-collapse are jointly
satisfiable by a weight (`const_satisfies_slots`) that is twin-blind
(`const_twin_blind`).  So `{bounded ∧ pair-collapse ∧ twin-detecting}` is mutually
exclusive as a *slot-forced* triple — the transport door's slots and its twin
linkage are structurally orthogonal. -/
theorem orthogonality_wall :
    ¬ ∀ w : ℕ → ℝ, PmNormalized w → PairCollapse w → TwinDetecting w := by
  intro h
  exact const_twin_blind
    (h (fun _ => (1 : ℝ)) const_satisfies_slots.1 const_satisfies_slots.2)

/-- **The abstract door schema is vacuous.**  No linkage predicate `L` can be both
*slot-derivable* (implied by the two slots) and *detection-sufficient* (implying
`TwinDetecting`).  Any proposed transport door of the shape
`slots ⟹ L ⟹ twin-detection` collapses, witnessed by the constant weight.  This is
the orthogonality of the two only-ever-proven parity mechanisms, frozen: the
entropy spine's PAIR-COLLAPSE slot cannot be composed into twin detection. -/
theorem no_slot_derived_twin_linkage (L : (ℕ → ℝ) → Prop)
    (hderive : ∀ w, PmNormalized w → PairCollapse w → L w)
    (hdetect : ∀ w, L w → TwinDetecting w) : False :=
  const_twin_blind
    (hdetect _ (hderive _ const_satisfies_slots.1 const_satisfies_slots.2))

end Salt.Entropy.Chowla
