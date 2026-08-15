/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.TransportWall

/-!
# The pin dichotomy inside the slot class (wall-L1)

## The anti-door reading

`TransportWall.lean`'s `TwinDetecting` leaves the non-twin index `n` unguarded, and
the weight `slackWitness n = if n = 0 then 5 else 1` lives in exactly that slack.  It
passes both slots — `PmNormalized` constrains only `n ≥ 1`, and `PairCollapse` reads
only indices `≥ 1`, so the value at `0` is never seen — yet it satisfies
`TwinDetecting` through the pair `(m, n) = (3, 0)`, where the entire separation comes
from the unconstrained value `5`.  That weight sees no twins at all.
`slack_witness_twinDetecting` puts it in the kernel, and
`blind_iff_const_fails_unguarded` reads the same fact from the other side: at the
landed unguarded definition the dichotomy proved below is FALSE.  The `1 ≤ n` guard in
`TwinDetecting'` is therefore NECESSARY rather than stylistic — it is what restores
content to the clause "the weight separates a twin pair from a non-twin pair".

## The strength law

`TwinDetecting'` adds a conjunct, so `twinDetecting'_imp : TwinDetecting' w →
TwinDetecting w`, and it is the landed UNGUARDED definition that yields the stronger
wall.  Substituting `TwinDetecting'` into `orthogonality_wall` or into
`no_slot_derived_twin_linkage` would be a silent strength regression the kernel cannot
catch: both statements would stay true and stay green.  `TwinDetecting'` is therefore
ADDITIVE — used only in the door and dichotomy statements of this file — and
`TransportWall.lean` is byte-untouched by this module.  The fence is kernel-borne, not
prose-borne: `slack_witness_twinDetecting` is proved at `(m, n) = (3, 0)`, so
re-guarding the landed definition in place would make that statement unprovable and
break the build.

## What is landed

* `blind_iff_const` — inside the slot class, `¬ TwinDetecting' w` is EQUIVALENT to
  `w n = 1` for every `n ≥ 1`.  The pair correlation `k ↦ w k · w (k+2)` is globally
  constant (the guarded hypothesis relates twin starts and non-twin starts, and both
  classes are inhabited at `3` and at `1`); the seeds `n ∈ {1, 2, 4}` pin that constant
  to `+1` through complete multiplicativity; and the step `k ↦ k + 2` then carries `+1`
  up from `w 1` and `w 2` over every index.
* `pin_iff_detecting`, together with its two directions `pinned_door` and
  `pin_minimal` — the contrapositive: one pinned sign `w n = -1` at some `n ≥ 1` is
  already equivalent to detection.  So the weakest pin is the bottom element of the
  detection-sufficient hypotheses above the slots, dual to
  `no_slot_derived_twin_linkage`.
* `liouville_pinned` — the class is inhabited away from the constant weight: `λ`
  detects, at the separator `(m, n) = (3, 7)`, where `λ3·λ5 = +1` and `λ7·λ9 = -1`.

The route the descent actually uses — the seeds `{1, 2, 3, 4}` together with `p - 2`
at every prime `p ≥ 7` — carries its own positive control at
`scripts/l1_gf2_control.py`: recast over `GF(2)` the route pins every sign below the
cutoff, and dropping the `n = 4` seed exhibits a genuine second solution.

## Scope

Boundary-map completion, and nothing else.  No statement here is a claim about twin
primes, and the transport route these slots describe is the one Tao's own note declines
to connect to twin-prime sums (`docs/sources/chowla.txt:196-200`).  This module
advances the flagship zero inches; it records where the wall's satisfier class sits.
-/

namespace Salt.Entropy.Chowla

/-! ### The guarded detection notion, beside the frozen one -/

/-- **Twin detection, guarded.**  `TransportWall.lean`'s `TwinDetecting` with the
non-twin index held away from `0`.  Adding the conjunct `1 ≤ n` makes this the
STRONGER predicate (`twinDetecting'_imp`), so it never replaces the landed definition;
it is used only in the door statements below. -/
def TwinDetecting' (w : ℕ → ℝ) : Prop :=
  ∃ m n, (m.Prime ∧ (m + 2).Prime) ∧ ¬ (n.Prime ∧ (n + 2).Prime) ∧ 1 ≤ n ∧
    w m * w (m + 2) ≠ w n * w (n + 2)

/-- **The strength law, in the kernel.**  The guarded notion implies the landed one,
so the landed `orthogonality_wall` and `no_slot_derived_twin_linkage` are the stronger
theorems and must keep the unguarded definition. -/
theorem twinDetecting'_imp : ∀ w : ℕ → ℝ, TwinDetecting' w → TwinDetecting w := by
  rintro w ⟨m, n, hm, hn, -, hne⟩
  exact ⟨m, n, hm, hn, hne⟩

/-! ### The slack witness: what the unguarded notion admits -/

/-- The `n = 0` slack witness: `5` at `0`, `1` everywhere else. -/
private def slackWitness : ℕ → ℝ := fun n => if n = 0 then 5 else 1

private lemma slackWitness_pos {n : ℕ} (hn : 1 ≤ n) : slackWitness n = 1 := by
  have hne : n ≠ 0 := by omega
  simp [slackWitness, hne]

/-- **The unguarded notion admits a weight that detects nothing.**  `slackWitness`
passes both slots and satisfies the landed `TwinDetecting`, entirely through the
unconstrained value at `0`, at the pair `(m, n) = (3, 0)`. -/
theorem slack_witness_twinDetecting :
    PmNormalized slackWitness ∧ PairCollapse slackWitness ∧ TwinDetecting slackWitness := by
  refine ⟨⟨fun n hn => Or.inl (slackWitness_pos hn), slackWitness_pos le_rfl⟩, ?_, ?_⟩
  · intro p N hp hN
    have hpN : 0 < p * N := Nat.mul_pos hp.pos hN
    have e1 : p * N ≠ 0 := by omega
    have e3 : N ≠ 0 := by omega
    simp [slackWitness, e1, e3]
  · exact ⟨3, 0, by norm_num, by norm_num, by norm_num [slackWitness]⟩

/-- **The guard rejects the slack witness.**  Every index the guarded notion may read
is `≥ 1`, where `slackWitness` is constantly `1`. -/
theorem slack_witness_not_twinDetecting' : ¬ TwinDetecting' slackWitness := by
  rintro ⟨m, n, ⟨hmp, -⟩, -, hn1, hne⟩
  have hm1 : 1 ≤ m := hmp.one_lt.le
  exact hne (by rw [slackWitness_pos hm1, slackWitness_pos (by omega : 1 ≤ m + 2),
    slackWitness_pos hn1, slackWitness_pos (by omega : 1 ≤ n + 2)])

/-- **The guard is necessary, not stylistic.**  At the landed unguarded definition the
dichotomy below is FALSE: `slackWitness` is constantly `1` on `n ≥ 1` and still
satisfies `TwinDetecting`.  This is the anti-repair fence read from the far side. -/
theorem blind_iff_const_fails_unguarded :
    ¬ ∀ w : ℕ → ℝ, PmNormalized w → PairCollapse w →
      (¬ TwinDetecting w ↔ ∀ n, 1 ≤ n → w n = 1) := by
  intro h
  obtain ⟨hpm, hpc, hdet⟩ := slack_witness_twinDetecting
  exact (h slackWitness hpm hpc).mpr (fun _ hn => slackWitness_pos hn) hdet

/-! ### The dichotomy -/

/-- **THE PIN DICHOTOMY.**  Inside the slot class, twin-blindness is a single point:
a slot-satisfying weight fails the guarded detection clause exactly when it is
constantly `1` on `n ≥ 1`.

The proof derives global constancy of the pair correlation before anything else — the
hypothesis relates twin starts to non-twin starts only, and both classes are inhabited
(`3` is a twin start, `1` is a non-twin start), so the two instantiations chain — then
pins the constant at the seeds `n ∈ {1, 2, 4}` using complete multiplicativity, and
finally runs the step `k ↦ k + 2` up from `w 1` and `w 2`. -/
theorem blind_iff_const (w : ℕ → ℝ) (hb : PmNormalized w) (hc : PairCollapse w) :
    ¬ TwinDetecting' w ↔ ∀ n, 1 ≤ n → w n = 1 := by
  constructor
  · intro h
    -- The hypothesis, in usable form.
    have key : ∀ m n : ℕ, (m.Prime ∧ (m + 2).Prime) → ¬ (n.Prime ∧ (n + 2).Prime) →
        1 ≤ n → w m * w (m + 2) = w n * w (n + 2) := by
      intro m n hm hn hn1
      by_contra hne
      exact h ⟨m, n, hm, hn, hn1, hne⟩
    have h35 : ((3 : ℕ).Prime ∧ ((3 : ℕ) + 2).Prime) := by norm_num
    have h1nt : ¬ ((1 : ℕ).Prime ∧ ((1 : ℕ) + 2).Prime) := by norm_num
    have hw1 : w 1 = 1 := hb.2
    -- STEP 1: the pair correlation is globally constant on `k ≥ 1`.
    have hall : ∀ k : ℕ, 1 ≤ k → w k * w (k + 2) = w 3 * w 5 := by
      intro k hk
      by_cases hkt : k.Prime ∧ (k + 2).Prime
      · have e1 : w k * w (k + 2) = w 1 * w 3 := key k 1 hkt h1nt le_rfl
        have e2 : w 3 * w 5 = w 1 * w 3 := key 3 1 h35 h1nt le_rfl
        rw [e1, e2]
      · exact (key 3 k h35 hkt hk).symm
    -- STEP 2: the seeds `n ∈ {1, 2, 4}` pin the constant to `+1`.
    have hcm := slots_force_completelyMult w hb hc
    have hw4 : w 4 = w 2 * w 2 := hcm 2 2 (by norm_num) (by norm_num)
    have hw6 : w 6 = w 2 * w 3 := hcm 2 3 (by norm_num) (by norm_num)
    have hb2 : w 2 = 1 ∨ w 2 = -1 := hb.1 2 (by norm_num)
    have hb3 : w 3 = 1 ∨ w 3 = -1 := hb.1 3 (by norm_num)
    have hA1 : w 1 * w 3 = w 3 * w 5 := hall 1 le_rfl
    have hA2 : w 2 * w 4 = w 3 * w 5 := hall 2 (by norm_num)
    have hA4 : w 4 * w 6 = w 3 * w 5 := hall 4 (by norm_num)
    have hw4one : w 4 = 1 := by
      rcases hb2 with h2 | h2 <;> rw [hw4, h2] <;> norm_num
    have hw3c : w 3 = w 3 * w 5 := by rw [hw1, one_mul] at hA1; exact hA1
    have hw2c : w 2 = w 3 * w 5 := by rw [hw4one, mul_one] at hA2; exact hA2
    have hw6c : w 6 = w 3 * w 5 := by rw [hw4one, one_mul] at hA4; exact hA4
    have hw2eq : w 2 = w 3 := by rw [hw2c, ← hw3c]
    have h23 : w 2 * w 3 = w 3 := by rw [hw6] at hw6c; rw [← hw3c] at hw6c; exact hw6c
    have hw3one : w 3 = 1 := by
      rcases hb3 with h3 | h3
      · exact h3
      · rw [hw2eq, h3] at h23; norm_num at h23
    have hw5one : w 5 = 1 := by
      rw [hw3one, one_mul] at hw3c; exact hw3c.symm
    have hw2one : w 2 = 1 := by rw [hw2eq, hw3one]
    have hall1 : ∀ k : ℕ, 1 ≤ k → w k * w (k + 2) = 1 := by
      intro k hk
      rw [hall k hk, hw3one, hw5one, one_mul]
    -- STEP 3: the descent, one strong induction.
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 3 with hlt | hge
      · have hcase : n = 1 ∨ n = 2 := by omega
        rcases hcase with rfl | rfl
        · exact hw1
        · exact hw2one
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have hk1 : 1 ≤ k := by omega
        have hwk : w k = 1 := ih k (by omega) hk1
        have hstep := hall1 k hk1
        rw [hwk, one_mul] at hstep
        exact hstep
  · intro hconst
    rintro ⟨m, n, ⟨hmp, -⟩, -, hn1, hne⟩
    have hm1 : 1 ≤ m := hmp.one_lt.le
    exact hne (by rw [hconst m hm1, hconst (m + 2) (by omega), hconst n hn1,
      hconst (n + 2) (by omega)])

/-! ### The pin, and the two directions of the door -/

/-- **The pin IS detection.**  Inside the slot class, carrying a single `-1` at some
`n ≥ 1` is equivalent to the guarded detection clause — so the weakest pin is already
detection-sufficient, and every detection-sufficient hypothesis factors through it. -/
theorem pin_iff_detecting (w : ℕ → ℝ) (hb : PmNormalized w) (hc : PairCollapse w) :
    (∃ n, 1 ≤ n ∧ w n = -1) ↔ TwinDetecting' w := by
  constructor
  · rintro ⟨n, hn, hneg⟩
    by_contra hnd
    have h1 := (blind_iff_const w hb hc).mp hnd n hn
    rw [h1] at hneg
    norm_num at hneg
  · intro hd
    by_contra hno
    have hconst : ∀ n, 1 ≤ n → w n = 1 := by
      intro n hn
      rcases hb.1 n hn with h | h
      · exact h
      · exact (hno ⟨n, hn, h⟩).elim
    exact (blind_iff_const w hb hc).mpr hconst hd

/-- **The pinned door.**  A slot-satisfying weight with one pinned sign detects. -/
theorem pinned_door (w : ℕ → ℝ) (hb : PmNormalized w) (hc : PairCollapse w)
    (hpin : ∃ n, 1 ≤ n ∧ w n = -1) : TwinDetecting' w :=
  (pin_iff_detecting w hb hc).mp hpin

/-- **The pin is minimal.**  A slot-satisfying weight that detects must carry a pinned
sign — there is no detection below the pin. -/
theorem pin_minimal (w : ℕ → ℝ) (hb : PmNormalized w) (hc : PairCollapse w)
    (hd : TwinDetecting' w) : ∃ n, 1 ≤ n ∧ w n = -1 :=
  (pin_iff_detecting w hb hc).mpr hd

/-! ### The class is inhabited away from the constant weight -/

private lemma liouville_prime_neg {p : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.liouville p : ℝ) = -1 := by
  have h : ArithmeticFunction.liouville p = -1 := by
    rw [ArithmeticFunction.liouville_apply hp.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  rw [h]
  norm_num

private lemma liouville_nine : (ArithmeticFunction.liouville 9 : ℝ) = 1 := by
  have h9 : (9 : ℕ) = 3 * 3 := by norm_num
  rw [h9, ArithmeticFunction.liouville_apply_mul]
  push_cast
  rw [liouville_prime_neg (by norm_num : Nat.Prime 3)]
  norm_num

/-- **The Liouville weight is pinned, hence detecting.**  `λ` separates the twin pair
`(3, 5)` from the non-twin pair `(7, 9)`: `λ3·λ5 = +1` while `λ7·λ9 = -1`, since `9` is
composite.  So the slot class's detecting members are not empty, and the dichotomy is
not vacuous on either side. -/
theorem liouville_pinned :
    TwinDetecting' (fun n => (ArithmeticFunction.liouville n : ℝ)) := by
  refine ⟨3, 7, by norm_num, by norm_num, by norm_num, ?_⟩
  change (ArithmeticFunction.liouville 3 : ℝ) * (ArithmeticFunction.liouville 5 : ℝ)
      ≠ (ArithmeticFunction.liouville 7 : ℝ) * (ArithmeticFunction.liouville 9 : ℝ)
  have h3 : (ArithmeticFunction.liouville 3 : ℝ) = -1 :=
    liouville_prime_neg (by norm_num)
  have h5 : (ArithmeticFunction.liouville 5 : ℝ) = -1 :=
    liouville_prime_neg (by norm_num)
  have h7 : (ArithmeticFunction.liouville 7 : ℝ) = -1 :=
    liouville_prime_neg (by norm_num)
  rw [h3, h5, h7, liouville_nine]
  norm_num

end Salt.Entropy.Chowla
