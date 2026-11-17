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
identical. `S1InnerBound` and `collision_lower_orderW_of` live in `CollisionQuant`
since O13-e row 218, where `collision_lower_orderW` is the tensor instance (via
`inner_abs_le`); the other landed tensor lemmas are left byte-identical.

The chain mirrors the landed one exactly:
`S1InnerBound → collision_lower_orderW_of → crossCollisionControlled_holds_of →
 compat_le_two_yside_of → S1_le_of → S1_upper_of`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

omit [Salt.Maynard.TupleChoice] in
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

omit [Salt.Maynard.TupleChoice] in
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
