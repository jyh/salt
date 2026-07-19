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

/-! ## D4-b — membership keystones (L1, L2) and the orphaned bridges (L4, L6) -/

/-- **L2 companion [A].**  The twin-free completion has identically zero twin
    mass: every twin index is zeroed by construction. -/
theorem twinFree_twinMass : ∀ x, twinMass twinFree x = 0 := by
  intro x
  unfold twinMass
  apply Finset.sum_eq_zero
  intro n _
  simp only [twinFree]
  by_cases h : n.Prime ∧ (n + 2).Prime
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]

/-- **L4 bridge [A/B].**  Unboundedness of the true-sequence twin mass is
    exactly the Twin Prime Conjecture (repo form, `Salt/Basic.lean`). -/
theorem twinMass_oneWeight_unbounded_iff :
    (∀ C : ℝ, ∃ x : ℕ, C < twinMass oneWeight x) ↔ TwinPrimeConjecture := by
  have hcard : ∀ x : ℕ, twinMass oneWeight x
      = (((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ) := by
    intro x
    unfold twinMass
    simp only [oneWeight]
    rw [Finset.sum_boole]
  constructor
  · intro hub n
    obtain ⟨x, hx⟩ := hub (n : ℝ)
    rw [hcard] at hx
    have hn : n < ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card := by
      exact_mod_cast hx
    have hne : ∃ p ∈ (Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime), n ≤ p := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hsub : (Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)
          ⊆ Finset.range n := by
        intro p hp
        exact Finset.mem_range.mpr (hcon p hp)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_range] at hle
      omega
    obtain ⟨p, hpS, hnp⟩ := hne
    rw [Finset.mem_filter] at hpS
    exact ⟨p, hnp, hpS.2.1, hpS.2.2⟩
  · intro htpc C
    have key : ∀ m : ℕ, ∃ x : ℕ,
        m ≤ ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card := by
      intro m
      induction m with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨x, hx⟩ := ih
        obtain ⟨p, hpx, hp, hp2⟩ := htpc (x + 1)
        refine ⟨p, ?_⟩
        have hpmem : p ∈ (Finset.Icc 1 p).filter (fun n => n.Prime ∧ (n + 2).Prime) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, le_refl p⟩, hp, hp2⟩
        have hpnotSx : p ∉ (Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          rintro ⟨⟨_, hple⟩, _⟩
          omega
        have hsub : insert p ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime))
            ⊆ (Finset.Icc 1 p).filter (fun n => n.Prime ∧ (n + 2).Prime) := by
          rw [Finset.insert_subset_iff]
          refine ⟨hpmem, ?_⟩
          exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (by omega))
        calc k + 1 ≤ ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card + 1 := by
              omega
          _ = (insert p ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime))).card := by
              rw [Finset.card_insert_of_notMem hpnotSx]
          _ ≤ ((Finset.Icc 1 p).filter (fun n => n.Prime ∧ (n + 2).Prime)).card :=
              Finset.card_le_card hsub
    obtain ⟨x, hx⟩ := key (⌊C⌋₊ + 1)
    refine ⟨x, ?_⟩
    rw [hcard]
    have h1 : C < (⌊C⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one C
    have h2 : ((⌊C⌋₊ + 1 : ℕ) : ℝ)
        ≤ (((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card : ℝ) := by
      exact_mod_cast hx
    push_cast at h2
    linarith

/-- **L6 non-degeneracy converse [A].**  The Twin Prime Conjecture makes `Z`
    hold via the tautological twin-sufficient witness. -/
theorem TPC_implies_Z {θ A₀ : ℝ} : TwinPrimeConjecture → Z θ A₀ := by
  intro htpc
  refine ⟨fun a => ∀ C : ℝ, ∃ x : ℕ, C < twinMass a x, ?_, ?_⟩
  · intro a _ he
    exact he
  · exact twinMass_oneWeight_unbounded_iff.mpr htpc

/-- The `{0,1}` divisor indicator `[d ∣ n(n+2)]`, `ℕ`-valued, used to count
    twin-type congruence solutions by periodicity. -/
def twinIndic (d n : ℕ) : ℕ := if d ∣ n * (n + 2) then 1 else 0

/-- **L1 per-divisor bound.**  For the true sequence, the level-`d` Type-I error
    is `O(d)`: by `d`-periodicity of `[d ∣ n(n+2)]`, the count over `[1,x]` is
    `(ρ(d)/d)·x` up to a boundary error `≤ 3d`. -/
lemma oneWeight_perd (x d : ℕ) (hd : 1 ≤ d) :
    |typeISum oneWeight d x - (twinRho d : ℝ) / d * x| ≤ 3 * (d : ℝ) := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- `d`-periodicity of the indicator
  have hshift : ∀ q n, twinIndic d (d * q + n) = twinIndic d n := by
    intro q n
    have hdvd_iff : (d ∣ (d * q + n) * (d * q + n + 2)) ↔ (d ∣ n * (n + 2)) := by
      have hc1 : d * q + n ≡ n [MOD d] := by
        have h0 : d * q ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right d q)
        have h1 := h0.add_right n
        rwa [zero_add] at h1
      have hc2 : d * q + n + 2 ≡ n + 2 [MOD d] := hc1.add_right 2
      have hcong : (d * q + n) * (d * q + n + 2) ≡ n * (n + 2) [MOD d] := hc1.mul hc2
      constructor
      · intro h
        exact (Nat.modEq_zero_iff_dvd).mp (hcong.symm.trans ((Nat.modEq_zero_iff_dvd).mpr h))
      · intro h
        exact (Nat.modEq_zero_iff_dvd).mp (hcong.trans ((Nat.modEq_zero_iff_dvd).mpr h))
    unfold twinIndic
    by_cases h : d ∣ n * (n + 2)
    · rw [if_pos h, if_pos (hdvd_iff.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hdvd_iff.mp hc))]
  -- one period sums to `ρ(d)`
  have hbase : (∑ n ∈ Finset.range d, twinIndic d n) = twinRho d := by
    simp only [twinIndic, twinRho, Finset.sum_boole, Nat.cast_id]
  -- `q` periods sum to `q·ρ(d)`
  have hblock : ∀ q, (∑ n ∈ Finset.range (d * q), twinIndic d n) = q * twinRho d := by
    intro q
    induction q with
    | zero => simp
    | succ k ih =>
      rw [show d * (k + 1) = d * k + d by ring, Finset.sum_range_add, ih]
      have hp : (∑ n ∈ Finset.range d, twinIndic d (d * k + n)) = twinRho d := by
        rw [← hbase]; exact Finset.sum_congr rfl (fun n _ => hshift k n)
      rw [hp]; ring
  -- Euclidean split of `range (x+1)`
  have hdecomp : (∑ n ∈ Finset.range (x + 1), twinIndic d n)
      = ((x + 1) / d) * twinRho d + (∑ n ∈ Finset.range ((x + 1) % d), twinIndic d n) := by
    conv_lhs => rw [← Nat.div_add_mod (x + 1) d]
    rw [Finset.sum_range_add, hblock ((x + 1) / d)]
    congr 1
    exact Finset.sum_congr rfl (fun n _ => hshift ((x + 1) / d) n)
  -- peel the `n = 0` boundary term
  have herase : (Finset.range (x + 1)).erase 0 = Finset.Icc 1 x := by
    ext n; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
  have hind0 : twinIndic d 0 = 1 := by simp [twinIndic]
  have hbdry : (∑ n ∈ Finset.range (x + 1), twinIndic d n)
      = 1 + ∑ n ∈ Finset.Icc 1 x, twinIndic d n := by
    rw [← Finset.add_sum_erase (Finset.range (x + 1)) (twinIndic d)
        (Finset.mem_range.mpr (Nat.succ_pos x)), herase, hind0]
  -- cast the true-sequence sum to `ℕ`
  have hcast :
      typeISum oneWeight d x = ((∑ n ∈ Finset.Icc 1 x, twinIndic d n : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    unfold typeISum
    apply Finset.sum_congr rfl
    intro n _
    simp only [oneWeight, twinIndic]
    by_cases h : d ∣ n * (n + 2) <;> simp [h]
  set S := (∑ n ∈ Finset.Icc 1 x, twinIndic d n) with hSdef
  set q := (x + 1) / d with hq
  set r := (x + 1) % d with hr
  set p := (∑ n ∈ Finset.range r, twinIndic d n) with hpdef
  have hrlt : r < d := by rw [hr]; exact Nat.mod_lt _ hd0
  have hpart_le : p ≤ twinRho d := by
    rw [hpdef, ← hbase]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (le_of_lt hrlt)) (fun i _ _ => Nat.zero_le _)
  have hIccSum : 1 + S = q * twinRho d + p := by
    rw [← hbdry]; exact hdecomp
  rw [hcast]
  have hIccR : (S : ℝ) = (q : ℝ) * (twinRho d : ℝ) + (p : ℝ) - 1 := by
    have h := congrArg (Nat.cast (R := ℝ)) hIccSum
    push_cast at h
    linarith
  have hxR : (x : ℝ) = (d : ℝ) * q + r - 1 := by
    have h := congrArg (Nat.cast (R := ℝ)) (Nat.div_add_mod (x + 1) d)
    rw [← hq, ← hr] at h
    push_cast at h
    linarith
  rw [hIccR, hxR]
  have hsimp : ((q : ℝ) * (twinRho d : ℝ) + (p : ℝ) - 1)
        - (twinRho d : ℝ) / d * ((d : ℝ) * q + r - 1)
      = (p : ℝ) - 1 - (twinRho d : ℝ) / d * ((r : ℝ) - 1) := by
    field_simp
    ring
  rw [hsimp]
  have hρle : (twinRho d : ℝ) ≤ d := by
    have hnat : twinRho d ≤ d := by
      unfold twinRho
      calc ((Finset.range d).filter (fun r => d ∣ r * (r + 2))).card
            ≤ (Finset.range d).card := Finset.card_filter_le _ _
        _ = d := Finset.card_range d
    exact_mod_cast hnat
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hpleR : (p : ℝ) ≤ (twinRho d : ℝ) := by exact_mod_cast hpart_le
  have hrR : (r : ℝ) < d := by exact_mod_cast hrlt
  have hY : |(twinRho d : ℝ) / d * ((r : ℝ) - 1)| ≤ d := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (twinRho d : ℝ) / d)]
    have hr1 : |(r : ℝ) - 1| ≤ d := by
      rw [abs_le]; constructor <;> [linarith; linarith]
    have hqd1 : (twinRho d : ℝ) / d ≤ 1 := by rw [div_le_one hdR]; exact hρle
    calc (twinRho d : ℝ) / d * |(r : ℝ) - 1| ≤ 1 * d :=
          mul_le_mul hqd1 hr1 (abs_nonneg _) (by norm_num)
      _ = d := one_mul _
  rw [abs_le] at hY
  rw [abs_le]
  constructor <;> linarith [hY.1, hY.2, hpleR, hp0, hρle, hd1R]

/-- **Log-power absorber.**  For `θ < 1/2` and any `A₀ ≥ 0`, the crude Type-I
    total `x^{2θ}` is dominated by `x·(log x)^{−A₀}` with an *explicit* constant
    (via `log x ≤ s⁻¹·x^s` at `s = (1−2θ)/A₀`), so no `o(·)`/compactness step is
    needed. -/
lemma logpow_absorb (θ A₀ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ θ * (x : ℝ) ^ θ ≤ C * x / (Real.log x) ^ A₀ := by
  have hβ : 0 < 1 - 2 * θ := by linarith
  obtain ⟨K, hK0, hKbound⟩ :
      ∃ K : ℝ, 0 < K ∧ ∀ x : ℕ, 2 ≤ x →
        (Real.log x) ^ A₀ ≤ K * (x : ℝ) ^ (1 - 2 * θ) := by
    rcases le_or_gt 0 A₀ with hA0 | hA0
    · rcases eq_or_lt_of_le hA0 with hA00 | hA00
      · -- `A₀ = 0`
        refine ⟨1, one_pos, ?_⟩
        intro x hx
        have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
        rw [← hA00, Real.rpow_zero, one_mul]
        calc (1 : ℝ) = (x : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
          _ ≤ (x : ℝ) ^ (1 - 2 * θ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hβ)
      · -- `0 < A₀`: the `s = (1−2θ)/A₀` slice
        set s := (1 - 2 * θ) / A₀ with hs
        have hA0' : A₀ ≠ 0 := ne_of_gt hA00
        have hs0 : 0 < s := div_pos hβ hA00
        have hsne : s ≠ 0 := ne_of_gt hs0
        have hsA : s * A₀ = 1 - 2 * θ := by rw [hs]; field_simp
        refine ⟨(1 / s) ^ A₀, Real.rpow_pos_of_pos (one_div_pos.mpr hs0) _, ?_⟩
        intro x hx
        have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
        have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
        have hlogpos : 0 ≤ Real.log x := Real.log_nonneg hx1
        have h1 : Real.log ((x : ℝ) ^ s) = s * Real.log x := Real.log_rpow hxpos s
        have h2 : Real.log ((x : ℝ) ^ s) ≤ (x : ℝ) ^ s - 1 :=
          Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos s)
        have h3 : Real.log x = (1 / s) * Real.log ((x : ℝ) ^ s) := by
          rw [h1, one_div, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
        have hlogle : Real.log x ≤ (1 / s) * (x : ℝ) ^ s := by
          rw [h3]
          have hinv : (0 : ℝ) ≤ 1 / s := by positivity
          calc (1 / s) * Real.log ((x : ℝ) ^ s) ≤ (1 / s) * ((x : ℝ) ^ s - 1) :=
                mul_le_mul_of_nonneg_left h2 hinv
            _ ≤ (1 / s) * (x : ℝ) ^ s := by
                apply mul_le_mul_of_nonneg_left _ hinv; linarith
        have hpow : (Real.log x) ^ A₀ ≤ ((1 / s) * (x : ℝ) ^ s) ^ A₀ :=
          Real.rpow_le_rpow hlogpos hlogle (le_of_lt hA00)
        have heq :
            ((1 / s) * (x : ℝ) ^ s) ^ A₀ = (1 / s) ^ A₀ * (x : ℝ) ^ (1 - 2 * θ) := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (le_of_lt hxpos) s),
              ← Real.rpow_mul (le_of_lt hxpos) s A₀, hsA]
        rw [heq] at hpow
        exact hpow
    · -- `A₀ < 0`: `(log x)^{A₀}` is antitone in the base, capped at `x = 2`
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2β : 0 < (2 : ℝ) ^ (1 - 2 * θ) := Real.rpow_pos_of_pos (by norm_num) _
      have h2βne : (2 : ℝ) ^ (1 - 2 * θ) ≠ 0 := ne_of_gt h2β
      refine ⟨(Real.log 2) ^ A₀ / (2 : ℝ) ^ (1 - 2 * θ),
        div_pos (Real.rpow_pos_of_pos hlog2 A₀) h2β, ?_⟩
      intro x hx
      have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
      have hlogx : Real.log 2 ≤ Real.log x := (Real.log_le_log_iff (by norm_num) hxpos).mpr hx2
      have hmono : (Real.log x) ^ A₀ ≤ (Real.log 2) ^ A₀ :=
        Real.rpow_le_rpow_of_nonpos hlog2 hlogx (le_of_lt hA0)
      have hbase : (2 : ℝ) ^ (1 - 2 * θ) ≤ (x : ℝ) ^ (1 - 2 * θ) :=
        Real.rpow_le_rpow (by norm_num) hx2 (le_of_lt hβ)
      calc (Real.log x) ^ A₀ ≤ (Real.log 2) ^ A₀ := hmono
        _ = (Real.log 2) ^ A₀ / (2 : ℝ) ^ (1 - 2 * θ) * (2 : ℝ) ^ (1 - 2 * θ) := by
            field_simp
        _ ≤ (Real.log 2) ^ A₀ / (2 : ℝ) ^ (1 - 2 * θ) * (x : ℝ) ^ (1 - 2 * θ) :=
            mul_le_mul_of_nonneg_left hbase
              (le_of_lt (div_pos (Real.rpow_pos_of_pos hlog2 A₀) h2β))
  refine ⟨K, hK0, ?_⟩
  intro x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1lt : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hlogpos : 0 < Real.log x := Real.log_pos hx1lt
  have hLA : (0 : ℝ) < (Real.log x) ^ A₀ := Real.rpow_pos_of_pos hlogpos A₀
  have hxθ : (x : ℝ) ^ θ * (x : ℝ) ^ θ = (x : ℝ) ^ (2 * θ) := by
    rw [show (2 : ℝ) * θ = θ + θ by ring, Real.rpow_add hxpos]
  have hxprod : (x : ℝ) ^ (2 * θ) * (x : ℝ) ^ (1 - 2 * θ) = x := by
    rw [← Real.rpow_add hxpos, show (2 * θ) + (1 - 2 * θ) = 1 by ring, Real.rpow_one]
  rw [le_div_iff₀ hLA]
  calc (x : ℝ) ^ θ * (x : ℝ) ^ θ * (Real.log x) ^ A₀
      ≤ (x : ℝ) ^ θ * (x : ℝ) ^ θ * (K * (x : ℝ) ^ (1 - 2 * θ)) :=
        mul_le_mul_of_nonneg_left (hKbound x hx) (by positivity)
    _ = K * ((x : ℝ) ^ (2 * θ) * (x : ℝ) ^ (1 - 2 * θ)) := by rw [hxθ]; ring
    _ = K * x := by rw [hxprod]

/-- The `oneWeight` Type-I error, summed over `d ≤ x^θ`, is `≤ 3·(x^θ)²`:
    each level contributes `O(d)` (`oneWeight_perd`), `#Icc = D`, `d ≤ D ≤ x^θ`. -/
lemma typeIError_oneWeight_le (x : ℕ) (θ : ℝ) :
    typeIError oneWeight θ x ≤ 3 * ((x : ℝ) ^ θ * (x : ℝ) ^ θ) := by
  set D := ⌊(x : ℝ) ^ θ⌋₊ with hD
  have hDle : (D : ℝ) ≤ (x : ℝ) ^ θ := by rw [hD]; exact Nat.floor_le (by positivity)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hsum : typeIError oneWeight θ x ≤ (D : ℝ) * (3 * (D : ℝ)) := by
    unfold typeIError
    rw [← hD]
    calc ∑ d ∈ Finset.Icc 1 D, |typeISum oneWeight d x - (twinRho d : ℝ) / d * x|
        ≤ ∑ d ∈ Finset.Icc 1 D, (3 * (D : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hb := oneWeight_perd x d hd.1
          have hdD : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd.2
          linarith
      _ = (D : ℝ) * (3 * (D : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  calc typeIError oneWeight θ x
      ≤ (D : ℝ) * (3 * (D : ℝ)) := hsum
    _ = 3 * ((D : ℝ) * (D : ℝ)) := by ring
    _ ≤ 3 * ((x : ℝ) ^ θ * (x : ℝ) ^ θ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hDle hDle hD0 (by positivity)

/-- **L1 — true-sequence membership [B].**  `oneWeight ∈ 𝒞(θ,A₀)` for
    `θ ∈ (0,1/2)`, `A₀ ≥ 0`: per-divisor error `O(d)` summed over `d ≤ x^θ`
    gives `O(x^{2θ}) = o(x·log^{−A₀}x)`. -/
theorem oneWeight_mem {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1 / 2) (hA : 0 ≤ A₀) :
    Completion θ A₀ oneWeight := by
  have _ := hA  -- `0 ≤ A₀` is part of the frozen interface; the bound holds for all `A₀`
  refine ⟨fun _ => by norm_num [oneWeight], ?_⟩
  obtain ⟨C, hC0, hCbound⟩ := logpow_absorb θ A₀ h0 h
  refine ⟨3 * C, by linarith, ?_⟩
  intro x hx
  calc typeIError oneWeight θ x
      ≤ 3 * ((x : ℝ) ^ θ * (x : ℝ) ^ θ) := typeIError_oneWeight_le x θ
    _ ≤ 3 * (C * x / (Real.log x) ^ A₀) := by
        apply mul_le_mul_of_nonneg_left (hCbound x hx) (by norm_num)
    _ = 3 * C * x / (Real.log x) ^ A₀ := by ring

/-- Number of twin indices `n ∈ [1,x]` with `d ∣ n(n+2)` — the level-`d`
    discrepancy between `oneWeight` and `twinFree`. -/
def twinLocCount (d x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime)).card

/-- The level-`d` Type-I sums of `oneWeight` and `twinFree` differ by exactly
    `twinLocCount d x` (the twin indices zeroed by `twinFree`). -/
lemma typeISum_diff (d x : ℕ) :
    typeISum oneWeight d x - typeISum twinFree d x = (twinLocCount d x : ℝ) := by
  unfold typeISum oneWeight twinFree twinLocCount
  rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hd : d ∣ n * (n + 2)
  · by_cases ht : n.Prime ∧ (n + 2).Prime
    · simp [hd, ht]
    · simp [hd, ht]
  · simp [hd]

/-- **The 4-divisor bound.**  Summed over levels `d ≤ D`, the twin discrepancy
    counts each twin `n ≤ x` at most `τ(n(n+2)) = 4` times (the divisors
    `{1, n, n+2, n(n+2)}`), hence is `≤ 4·twinPrimeCounting x`. -/
lemma twinCount_sum_le (x D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, twinLocCount d x) ≤ 4 * twinPrimeCounting x := by
  calc (∑ d ∈ Finset.Icc 1 D, twinLocCount d x)
      = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.Icc 1 x,
          (if d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.card_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 D,
          (if d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.Icc 1 x, (if n.Prime ∧ (n + 2).Prime then 4 else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases ht : n.Prime ∧ (n + 2).Prime
        · rw [if_pos ht]
          have h1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hne0 : n * (n + 2) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
          have hcop : Nat.Coprime n (n + 2) := (Nat.coprime_primes ht.1 ht.2).mpr (by omega)
          have hdvcard : (n * (n + 2)).divisors.card = 4 := by
            rw [Nat.Coprime.card_divisors_mul hcop, Nat.Prime.divisors ht.1,
                Nat.Prime.divisors ht.2, Finset.card_pair (by have := ht.1.two_le; omega),
                Finset.card_pair (by omega)]
          have hsub : (Finset.Icc 1 D).filter
              (fun d => d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime)
                ⊆ (n * (n + 2)).divisors := by
            intro d hd
            rw [Finset.mem_filter] at hd
            exact Nat.mem_divisors.mpr ⟨hd.2.1, hne0⟩
          calc ∑ d ∈ Finset.Icc 1 D,
                  (if d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime then 1 else 0)
              = ((Finset.Icc 1 D).filter
                  (fun d => d ∣ n * (n + 2) ∧ n.Prime ∧ (n + 2).Prime)).card :=
                (Finset.card_filter _ _).symm
            _ ≤ (n * (n + 2)).divisors.card := Finset.card_le_card hsub
            _ = 4 := hdvcard
        · rw [if_neg ht]
          exact (Finset.sum_eq_zero (fun d _ => if_neg (fun hc => ht hc.2))).le
    _ = 4 * ((Finset.Icc 1 x).filter (fun n => n.Prime ∧ (n + 2).Prime)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        by_cases ht : n.Prime ∧ (n + 2).Prime <;> simp [ht]
    _ ≤ 4 * twinPrimeCounting x := by
        gcongr
        rw [twinPrimeCounting, Nat.count_eq_card_filter_range]
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_range]
        omega

/-- **N5.3 absorption.**  For `A₀ ≤ 2`, the Brun twin-count bound
    (`Salt.M5BigO.nat_absorb`: `twinPrimeCounting N ≤ 25700·N/log²N` for `N ≥ N₁`)
    folds into the `∃C ∀x≥2` slot of `Completion` — an `x₀`-split with the finitely
    many small `x` summed off, `log^{A₀} ≤ log²` supplying `A₀ ≤ 2`. -/
lemma twinCount_absorb (A₀ : ℝ) (hA : A₀ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      4 * (twinPrimeCounting x : ℝ) ≤ C * x / (Real.log x) ^ A₀ := by
  obtain ⟨N1, hN1⟩ := Salt.M5BigO.nat_absorb
  set M := max N1 3 with hM
  set g := fun y : ℕ => 4 * (twinPrimeCounting y : ℝ) * (Real.log y) ^ A₀ / y with hg
  have hgnn : ∀ y : ℕ, 2 ≤ y → 0 ≤ g y := by
    intro y hy
    have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hLy : 0 < (Real.log y) ^ A₀ := Real.rpow_pos_of_pos hlogy A₀
    have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    simp only [hg]
    apply div_nonneg (mul_nonneg (by positivity) (le_of_lt hLy)) (le_of_lt hypos)
  refine ⟨102800 + ∑ y ∈ Finset.Ico 2 M, g y, ?_, ?_⟩
  · have : 0 ≤ ∑ y ∈ Finset.Ico 2 M, g y :=
      Finset.sum_nonneg (fun y hy => hgnn y (Finset.mem_Ico.mp hy).1)
    linarith
  · intro x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hLA : (0 : ℝ) < (Real.log x) ^ A₀ := Real.rpow_pos_of_pos hlogx A₀
    have hsumnn : 0 ≤ ∑ y ∈ Finset.Ico 2 M, g y :=
      Finset.sum_nonneg (fun y hy => hgnn y (Finset.mem_Ico.mp hy).1)
    have hgxC : g x ≤ 102800 + ∑ y ∈ Finset.Ico 2 M, g y := by
      by_cases hxM : x < M
      · have hmem : x ∈ Finset.Ico 2 M := Finset.mem_Ico.mpr ⟨hx, hxM⟩
        have hle := Finset.single_le_sum (fun y hy => hgnn y (Finset.mem_Ico.mp hy).1) hmem
        linarith
      · have hMx : M ≤ x := not_lt.mp hxM
        have hN1x : N1 ≤ x := le_trans (le_max_left N1 3) hMx
        have h3x : 3 ≤ x := le_trans (le_max_right N1 3) hMx
        have hlog1 : 1 ≤ Real.log x := by
          rw [Real.le_log_iff_exp_le hxpos]
          have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast h3x
          calc Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
            _ ≤ 3 := by norm_num
            _ ≤ (x : ℝ) := hx3
        have hL2pos : (0 : ℝ) < (Real.log x) ^ (2 : ℕ) := by positivity
        have hlogpow : (Real.log x) ^ A₀ ≤ (Real.log x) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast (Real.log x) 2]
          exact Real.rpow_le_rpow_of_exponent_le hlog1 (by exact_mod_cast hA)
        have haP : (twinPrimeCounting x : ℝ) * (Real.log x) ^ (2 : ℕ) ≤ 25700 * x :=
          (le_div_iff₀ hL2pos).mp (hN1 x hN1x)
        have hstep : 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ A₀
            ≤ 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hlogpow (by positivity)
        have h4aL : 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ A₀ ≤ 102800 * x := by
          nlinarith [haP, hstep]
        have hgx : g x ≤ 102800 := by
          have hgxx : g x * (x : ℝ) = 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ A₀ := by
            simp only [hg]; field_simp
          have hmul : g x * x ≤ 102800 * x := by rw [hgxx]; exact h4aL
          exact le_of_mul_le_mul_right hmul hxpos
        linarith
    rw [le_div_iff₀ hLA]
    have hgxx : g x * (x : ℝ) = 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ A₀ := by
      simp only [hg]; field_simp
    calc 4 * (twinPrimeCounting x : ℝ) * (Real.log x) ^ A₀
        = g x * x := hgxx.symm
      _ ≤ (102800 + ∑ y ∈ Finset.Ico 2 M, g y) * x :=
          mul_le_mul_of_nonneg_right hgxC (le_of_lt hxpos)

/-- **L2 — the Brun-witness keystone [B/C].**  `twinFree ∈ 𝒞(θ,A₀)` for
    `θ ∈ (0,1/2)`, `A₀ ≤ 2`.  The level-`d` discrepancy from `oneWeight` is
    `≤ twinLocCount d x`; summed by the 4-divisor argument it is
    `≤ 4·twinPrimeCounting x = O(x/log²x)` (`N5.3`), which the `A₀ ≤ 2` log
    comparison folds into the completion budget alongside `L1`'s `x^{2θ}`. -/
theorem twinFree_mem {θ A₀ : ℝ} (h0 : 0 < θ) (h : θ < 1 / 2) (hA : A₀ ≤ 2) :
    Completion θ A₀ twinFree := by
  refine ⟨fun n => ?_, ?_⟩
  · simp only [twinFree]; split <;> norm_num
  obtain ⟨C, hC0, hCbound⟩ := logpow_absorb θ A₀ h0 h
  obtain ⟨C2, hC20, hC2bound⟩ := twinCount_absorb A₀ hA
  refine ⟨3 * C + C2, by linarith, ?_⟩
  intro x hx
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le a, le_abs_self b], by linarith [le_abs_self a, neg_abs_le b]⟩
  have hperd : typeIError twinFree θ x ≤ typeIError oneWeight θ x
      + ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, (twinLocCount d x : ℝ) := by
    unfold typeIError
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d _
    have hdc := typeISum_diff d x
    have hrw : typeISum twinFree d x - (twinRho d : ℝ) / d * x
        = (typeISum oneWeight d x - (twinRho d : ℝ) / d * x) - (twinLocCount d x : ℝ) := by
      rw [← hdc]; ring
    rw [hrw]
    calc |(typeISum oneWeight d x - (twinRho d : ℝ) / d * x) - (twinLocCount d x : ℝ)|
        ≤ |typeISum oneWeight d x - (twinRho d : ℝ) / d * x| + |(twinLocCount d x : ℝ)| :=
          htri _ _
      _ = |typeISum oneWeight d x - (twinRho d : ℝ) / d * x| + (twinLocCount d x : ℝ) := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (twinLocCount d x : ℝ))]
  calc typeIError twinFree θ x
      ≤ typeIError oneWeight θ x
        + ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, (twinLocCount d x : ℝ) := hperd
    _ ≤ 3 * ((x : ℝ) ^ θ * (x : ℝ) ^ θ) + 4 * (twinPrimeCounting x : ℝ) := by
        apply add_le_add (typeIError_oneWeight_le x θ)
        calc (∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, (twinLocCount d x : ℝ))
            = ((∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, twinLocCount d x : ℕ) : ℝ) := by
              rw [Nat.cast_sum]
          _ ≤ 4 * (twinPrimeCounting x : ℝ) := by
              exact_mod_cast twinCount_sum_le x ⌊(x : ℝ) ^ θ⌋₊
    _ ≤ 3 * (C * x / (Real.log x) ^ A₀) + C2 * x / (Real.log x) ^ A₀ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hCbound x hx) (by norm_num)
        · exact hC2bound x hx
    _ = (3 * C + C2) * x / (Real.log x) ^ A₀ := by ring

end Salt.Parity
