/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.CollisionQuant
import Salt.Maynard.S1Bound

/-!
# explicit12 W5-1 — the `y`-generic S1 collision assembly (Node A)

The S1 collision bound (`CollisionQuant.lean`, `S1Bound.lean`) has exactly ONE
tensor-dependent atom: the per-assignment inner bound `inner_abs_le`, whose
proof is the only place the crude tensor weight `(f₀, hf01, hfmono, hy)` enters
the assembly. Everything downstream — `collision_lower_orderW`,
`crossCollisionControlled_holdsW`, `compat_le_two_ysideW`, `S1_leW`,
`S1_upperW` — is otherwise `y`-generic, using only off-support vanishing `hy0`
(and, for `S1_upper`, the `|y| ≤ 1` bound `hy1`).

This module isolates that atom behind the abstract hypothesis `S1InnerBound`
and republishes the entire chain as PARALLEL `*_of` lemmas that take
`S1InnerBound` (plus `hy0`/`hy1`) instead of the tensor structure. Each `*_of`
lemma is its landed twin with the tensor hypotheses swapped for `S1InnerBound`
and the single `inner_abs_le` call replaced by `hInner`; the conclusions are
identical. The landed tensor lemmas are left BYTE-IDENTICAL (the merged spine
depends on them); the tensor `y` is one instance of `S1InnerBound` via
`inner_abs_le`, so the pinned chain stays recoverable.

The chain mirrors the landed one exactly:
`S1InnerBound → collision_lower_orderW_of → crossCollisionControlled_holds_of →
 compat_le_two_yside_of → S1_le_of → S1_upper_of`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- **W5-1 (Node A).** The one tensor-dependent atom of the S1 collision
bound, isolated behind an abstract hypothesis. This is the exact conclusion of
`inner_abs_le` (`CollisionQuant.lean`), universally quantified over the
squarefree modulus `s` and the prime-to-slot assignment `α`. Supplying
`S1InnerBound k R W' y` makes the whole S1 collision assembly `y`-generic: the
landed tensor weight is one instance (`inner_abs_le ... ⟹ S1InnerBound`), but
any `y` satisfying this bound (plus off-support vanishing `hy0`) drives the same
conclusions. -/
def S1InnerBound (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) : Prop :=
  ∀ {s : ℕ}, Squarefree s →
    ∀ (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k),
      α ∈ assignments k s →
    |∑ u ∈ kSieveIndex k R W', (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)


/-- `y`-generic form of `collision_lower_orderW`: the tensor weight is
replaced by the abstract atom `hInner : S1InnerBound k R W' y` (plus off-support
vanishing `hy0`). Body is the landed proof with the single `inner_abs_le` call
swapped for `hInner`. -/
theorem collision_lower_orderW_of (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBound k R W' y)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    |s1CollisionForm k R W' y|
      ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ)
          * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  classical
  have hyside : 0 ≤ ∑ r ∈ kSieveIndex k R W',
      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := s1_yside_nonneg k R W' y
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
  have hκ : (0 : ℝ) ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hempty : kSieveIndex k 0 W' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      exact absurd ((mem_kSieveIndex_iff r).mp hr).2.2.2 (Nat.not_lt_zero _)
    unfold s1CollisionForm
    rw [hempty]
    simp
  have h1mem : (1 : ℕ) ∈ collisionModuli k R := by
    rw [collisionModuli, Finset.mem_range]
    have := Nat.one_le_pow k R hRpos
    omega
  have hcompat := compat_moebius_expansion k R W' y
  have herase := Finset.add_sum_erase (collisionModuli k R)
    (fun t => ((μ t : ℤ) : ℝ)
      * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          (if t ∣ cRad d e then s1Summand k R W' y d e else 0)) h1mem
  have hG1 : (∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
      (if (1 : ℕ) ∣ cRad d e then s1Summand k R W' y d e else 0))
      = s1FullForm k R W' y := by
    unfold s1FullForm
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    rw [if_pos (one_dvd _)]
  have hμ1 : ((μ 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]
    norm_num
  have hkey : s1CollisionForm k R W' y
      = - ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0) := by
    have hsplit0 := s1_full_split k R W' y
    have hfull := s1_full_eq_yside k R W' y hy0
    simp only [hμ1, one_mul, hG1] at herase
    have e1 : s1CompatForm k R W' y
        = s1FullForm k R W' y
          + ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
              * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                  (if t ∣ cRad d e then s1Summand k R W' y d e else 0) := by
      rw [hcompat, ← herase]
    linarith
  have hbound : ∀ t ∈ (collisionModuli k R).erase 1,
      |((μ t : ℤ) : ℝ)
        * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
            (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
      ≤ (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ kSieveIndex k R W',
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R W',
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
        rw [inner_collision_expand k R W' y hsq]
        calc |∑ α ∈ assignments k t,
              ∑ d ∈ (kSieveIndex k R W').filter
                  (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                ∑ e ∈ (kSieveIndex k R W').filter
                    (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                  s1Summand k R W' y d e|
            ≤ ∑ α ∈ assignments k t,
                |∑ d ∈ (kSieveIndex k R W').filter
                    (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                  ∑ e ∈ (kSieveIndex k R W').filter
                      (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                    s1Summand k R W' y d e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ assignments k t,
                ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ kSieveIndex k R W',
                      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
              apply Finset.sum_le_sum
              intro α hα
              have hinner := inner_exact k R W' y hy0
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              unfold s1Summand
              rw [hinner]
              exact hInner hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ kSieveIndex k R W',
                      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcast : ((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card
          ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card := by
        rw [hcard]
        push_cast
        rw [← mul_pow]
        apply pow_le_pow_left₀
        · positivity
        · have hle : ((k * k - k : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
            have h1 : (k * k - k : ℕ) ≤ k * k := Nat.sub_le _ _
            calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h1
              _ = (k : ℝ) * (k : ℝ) := by push_cast; ring
          nlinarith
      calc |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0)|
          ≤ |∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| := by
            rw [abs_mul]
            have h1 := abs_moebius_real_le_one t
            have h2 := abs_nonneg (∑ d ∈ kSieveIndex k R W',
              ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0))
            nlinarith
        _ ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R W',
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ kSieveIndex k R W',
                  (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R W',
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
              mul_nonneg hinvsq_nonneg hyside
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ kSieveIndex k R W',
                        (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ kSieveIndex k R W',
                          (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ kSieveIndex k R W',
                          (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ kSieveIndex k R W',
                        (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by ring
    · rw [if_neg hgood]
      by_cases hsq : Squarefree t
      · have hsmall : ∃ p ∈ t.primeFactors, ¬ D < p := by
          by_contra hall
          push Not at hall
          exact hgood ⟨hsq, hall⟩
        obtain ⟨p, hp, hple⟩ := hsmall
        have hzero := inner_collision_zeroW k R W' D y hDlt
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) (not_lt.mp hple)
        rw [hzero, mul_zero, abs_zero]
      · have hμ0 : ((μ t : ℤ) : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          norm_num
        rw [hμ0, zero_mul, abs_zero]
  have htail := euler_tailW k (R ^ k + 1) D hk hDk
  calc |s1CollisionForm k R W' y|
      = |∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
              (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| := by
        rw [hkey, abs_neg]
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
                (if t ∣ cRad d e then s1Summand k R W' y d e else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p then
            (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ kSieveIndex k R W',
                  (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ kSieveIndex k R W',
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R W',
              (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ)
          * ∑ r ∈ kSieveIndex k R W',
              (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
        mul_le_mul_of_nonneg_right htail hyside

/-- `y`-generic form of `crossCollisionControlled_holdsW`. -/
theorem crossCollisionControlled_holds_of (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBound k R W' y)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    CrossCollisionControlled k R W' y := by
  refine ⟨12 * (k : ℝ) ^ 2 / (D : ℝ), ?_, ?_⟩
  · have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
    have hDposN : 0 < D := by omega
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
    positivity
  · exact collision_lower_orderW_of k R W' D y hy0 hInner hDlt hk hDk

/-- `y`-generic form of `compat_le_two_ysideW`. -/
theorem compat_le_two_yside_of (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBound k R W' y)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) :
    s1CompatForm k R W' y
      ≤ 2 * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  have hcoll := collision_lower_orderW_of k R W' D y hy0 hInner hDlt hk hDk
  have hyside := s1_yside_nonneg k R W' y
  have heq := s1_compat_eq k R W' y hy0
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D := by omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposN
  have hratio : 12 * (k : ℝ) ^ 2 / (D : ℝ) ≤ 1 := by
    rw [div_le_one hDpos]
    exact_mod_cast hDk
  have habs := neg_le_abs (s1CollisionForm k R W' y)
  have hcoll2 : |s1CollisionForm k R W' y|
      ≤ ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
    calc |s1CollisionForm k R W' y|
        ≤ 12 * (k : ℝ) ^ 2 / (D : ℝ)
            * ∑ r ∈ kSieveIndex k R W',
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := hcoll
      _ ≤ 1 * ∑ r ∈ kSieveIndex k R W',
            (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
          mul_le_mul_of_nonneg_right hratio hyside
      _ = ∑ r ∈ kSieveIndex k R W',
            (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := one_mul _
  linarith

/-- `y`-generic form of `S1_leW` (assembly over the public
`S1_le_main_add_errorW` + `compat_le_two_yside_of`). -/
theorem S1_le_of (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hInner : S1InnerBound k R W' y)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) (hK₀ : 1 ≤ K₀)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  have hL2 := S1_le_main_add_errorW k K₀ N R W' ν₀ D y hW' hK₀ hDlt hlt hsol
  have hcompat := compat_le_two_yside_of k R W' D y hy0 hInner hDlt hk hDk
  have hcoeff_nonneg : (0 : ℝ) ≤ ((K₀ - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  calc S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL2
    _ ≤ ((K₀ - 1) * N / W' : ℝ)
          * (2 * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat hcoeff_nonneg) (le_refl _)
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by ring

/-- `y`-generic form of `S1_upperW` (assembly over the public
`S1_trivial_error_le'` + `S1_le_of`; the tensor-derived `|y| ≤ 1` becomes the
hypothesis `hy1`). -/
theorem S1_upper_of (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hy1 : ∀ r, |y r| ≤ 1)
    (hInner : S1InnerBound k R W' y)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) (hK₀ : 1 ≤ K₀)
    (hR : 2 ≤ R)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    ∃ C : ℝ, 0 ≤ C ∧ S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  have hW0 : W' ≠ 0 := hW'.ne_zero
  obtain ⟨C0, hC0, hC0le⟩ := S1_trivial_error_le' k R W' y hy1 hR hW0
  have hL3 := S1_le_of k K₀ N R W' ν₀ D y hy0 hInner hW' hDlt hlt hk hDk hK₀ hsol
  refine ⟨2 ^ (k + 1) * C0, by positivity, ?_⟩
  calc S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL3
    _ ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hC0le (by positivity))
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + (2 ^ (k + 1) * C0) * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

end Salt.Maynard
