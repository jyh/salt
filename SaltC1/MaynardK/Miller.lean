/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.SeriesM

/-!
# C1 · A2d (a) — the Miller power recurrence in `MvPowerSeries`, and uniqueness

For a series `G` in `M` variables with constant term `1`, and every `k` and every exponent `C`,

  `weight C · [x^C] G^k = Σ_{0 ≠ A ≤ C} (k·weight A − weight (C − A)) · [x^A] G · [x^{C−A}] G^k`

(`miller_coeff`). The proof: the weight-Euler operator `eulerD P = Σ_C weight C · [x^C] P · x^C`
is a derivation (`eulerD_mul`, because `weight` is additive), so
`G · eulerD (G^k) = k · eulerD G · G^k` (`mul_eulerD_pow`); its coefficient at `C`, with the
`A = 0` term moved left, is the recurrence.
Since every term on the right has `weight (C − A) < weight C`, a table that has constant term `1`
and satisfies the recurrence on the keys of weight `≤ wmax`, with `G`'s coefficients there, IS
`[x^·] G^k` on those keys (`eq_coeff_pow_of_rec`, strong induction on the weight).

The certificate's `checkRecGen` is this recurrence at one key; `Series54` instantiates the
uniqueness at `GM 13`, `k = 54, 53`. Pure series algebra: nothing here bears on twin primes.
-/

open Finset

namespace SaltC1.MaynardK

open Salt.MaynardK

variable {M : ℕ}

/-- `Finsupp.equivFunOnFinite.symm`, the exponent of a tuple. -/
local notation "eF" => Finsupp.equivFunOnFinite.symm

/-! ## `weight` is additive -/

lemma weight_add (A B : Fin M → ℕ) : weight (A + B) = weight A + weight B := by
  unfold weight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.add_apply]
  ring

lemma weight_zero : weight (0 : Fin M → ℕ) = 0 := by
  simp [weight]

lemma weight_pos {A : Fin M → ℕ} (hA : A ≠ 0) : 0 < weight A := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hA
  have := two_mul_le_weight A m
  simp only [Pi.zero_apply] at hm
  omega

lemma weight_sub_add {A C : Fin M → ℕ} (h : ∀ m, A m ≤ C m) :
    weight (C - A) + weight A = weight C := by
  rw [← weight_add]
  congr 1
  funext m
  simp only [Pi.add_apply, Pi.sub_apply]
  have := h m
  omega

/-! ## The weight-Euler operator -/

/-- `eulerD P = Σ_C weight C · [x^C] P · x^C`. -/
noncomputable def eulerD (P : MvPowerSeries (Fin M) ℚ) : MvPowerSeries (Fin M) ℚ :=
  fun C => (weight ⇑C : ℚ) * P C

lemma coeff_eulerD (P : MvPowerSeries (Fin M) ℚ) (C : Fin M →₀ ℕ) :
    MvPowerSeries.coeff C (eulerD P) = (weight ⇑C : ℚ) * MvPowerSeries.coeff C P := rfl

/-- `eulerD` is a derivation. -/
lemma eulerD_mul (P Q : MvPowerSeries (Fin M) ℚ) :
    eulerD (P * Q) = eulerD P * Q + P * eulerD Q := by
  refine MvPowerSeries.ext fun C => ?_
  rw [map_add, coeff_eulerD, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [coeff_eulerD, coeff_eulerD, ← hp, Finsupp.coe_add, weight_add]
  push_cast
  ring

lemma eulerD_one : eulerD (1 : MvPowerSeries (Fin M) ℚ) = 0 := by
  refine MvPowerSeries.ext fun C => ?_
  rw [coeff_eulerD, MvPowerSeries.coeff_one, map_zero]
  by_cases h : C = 0
  · subst h
    simp [weight_zero]
  · simp [h]

/-- `G · eulerD (G^k) = k · (eulerD G · G^k)`. -/
lemma mul_eulerD_pow (G : MvPowerSeries (Fin M) ℚ) (k : ℕ) :
    G * eulerD (G ^ k) = (k : MvPowerSeries (Fin M) ℚ) * (eulerD G * G ^ k) := by
  induction k with
  | zero => simp [eulerD_one]
  | succ k ih =>
    rw [pow_succ, eulerD_mul, mul_add, ← mul_assoc, ih]
    push_cast
    ring

/-! ## Sums over the antidiagonal as sums over the box -/

lemma sum_antidiagonal_eq_boxM (C : Fin M → ℕ) (f : (Fin M →₀ ℕ) → (Fin M →₀ ℕ) → ℚ) :
    ∑ p ∈ antidiagonal (eF C), f p.1 p.2 = ∑ A ∈ boxM C, f (eF A) (eF (C - A)) := by
  refine (Finset.sum_nbij' (fun A => (eF A, eF (C - A))) (fun p => ⇑p.1) ?_ ?_ ?_ ?_ ?_).symm
  · intro A hA
    rw [boxM, Fintype.mem_piFinset] at hA
    rw [Finset.mem_antidiagonal]
    ext m
    have := Finset.mem_range.mp (hA m)
    simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply]
    omega
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [boxM, Fintype.mem_piFinset]
    intro m
    have := DFunLike.congr_fun hp m
    simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm] at this
    rw [Finset.mem_range]
    omega
  · intro A _
    rfl
  · intro p hp
    rw [Finset.mem_antidiagonal] at hp
    refine Prod.ext (Finsupp.equivFunOnFinite_symm_coe _) ?_
    ext m
    have := DFunLike.congr_fun hp m
    simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm] at this
    simp only [Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply]
    omega
  · intro A _
    rfl

lemma zero_mem_boxM (C : Fin M → ℕ) : (0 : Fin M → ℕ) ∈ boxM C := by
  rw [boxM, Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_range]
  simp

lemma le_of_mem_boxM {A C : Fin M → ℕ} (h : A ∈ boxM C) : ∀ m, A m ≤ C m := by
  rw [boxM, Fintype.mem_piFinset] at h
  intro m
  have := Finset.mem_range.mp (h m)
  omega

lemma eF_zero : eF (0 : Fin M → ℕ) = 0 := by
  ext m
  rfl

lemma coeff_zero_pow (G : MvPowerSeries (Fin M) ℚ) (hG : MvPowerSeries.constantCoeff G = 1)
    (k : ℕ) : MvPowerSeries.coeff (eF (0 : Fin M → ℕ)) (G ^ k) = 1 := by
  rw [eF_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hG, one_pow]

/-! ## The Miller recurrence -/

/-- **The Miller power recurrence**, for EVERY `k` and EVERY exponent `C` (no weight bound):
`weight C · [x^C] G^k = Σ_{0 ≠ A ≤ C} (k·weight A − weight (C − A)) · [x^A] G · [x^{C−A}] G^k`. -/
theorem miller_coeff (G : MvPowerSeries (Fin M) ℚ) (hG : MvPowerSeries.constantCoeff G = 1)
    (k : ℕ) (C : Fin M → ℕ) :
    (weight C : ℚ) * MvPowerSeries.coeff (eF C) (G ^ k)
      = ∑ A ∈ boxM C, if A = 0 then 0 else
          ((k : ℚ) * (weight A : ℚ) - (weight (C - A) : ℚ)) * MvPowerSeries.coeff (eF A) G *
            MvPowerSeries.coeff (eF (C - A)) (G ^ k) := by
  set t : (Fin M → ℕ) → ℚ := fun A =>
    ((k : ℚ) * (weight A : ℚ) - (weight (C - A) : ℚ)) * MvPowerSeries.coeff (eF A) G *
      MvPowerSeries.coeff (eF (C - A)) (G ^ k) with ht
  -- the coefficient identity, as `Σ_A t A = 0`
  have hid := congrArg (MvPowerSeries.coeff (eF C)) (mul_eulerD_pow G k)
  rw [← map_natCast (MvPowerSeries.C (σ := Fin M) (R := ℚ)) k, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
    sum_antidiagonal_eq_boxM C (fun a b => MvPowerSeries.coeff a G *
      MvPowerSeries.coeff b (eulerD (G ^ k))),
    sum_antidiagonal_eq_boxM C (fun a b => MvPowerSeries.coeff a (eulerD G) *
      MvPowerSeries.coeff b (G ^ k)), Finset.mul_sum] at hid
  simp only [coeff_eulerD, Finsupp.coe_equivFunOnFinite_symm] at hid
  have hsum : ∑ A ∈ boxM C, t A = 0 := by
    rw [ht]
    simp only
    rw [← sub_eq_zero.mpr hid.symm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    ring
  have h0 := zero_mem_boxM C
  have hite : ∀ A ∈ boxM C, (if A = 0 then (0 : ℚ) else t A) = t A - if A = 0 then t A else 0 := by
    intro A _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hite, Finset.sum_sub_distrib, hsum, Finset.sum_ite_eq' (boxM C) 0 t,
    if_pos h0, ht]
  simp only [weight_zero, Nat.cast_zero, mul_zero, zero_sub, tsub_zero]
  rw [eF_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
  ring

/-! ## Uniqueness: a table satisfying the recurrence is the power's coefficients -/

/-- **Uniqueness by strong induction on the weight.** A table `P` with `P 0 = 1`, satisfying the
Miller recurrence at every key of weight `≤ wmax` with `G`'s coefficients there, is `[x^·] G^k`
on those keys. -/
theorem eq_coeff_pow_of_rec (G : MvPowerSeries (Fin M) ℚ)
    (hG : MvPowerSeries.constantCoeff G = 1) (k wmax : ℕ) (P g : (Fin M → ℕ) → ℚ)
    (hP0 : P 0 = 1) (hg : ∀ A, weight A ≤ wmax → g A = MvPowerSeries.coeff (eF A) G)
    (hrec : ∀ C, weight C ≤ wmax → (weight C : ℚ) * P C
      = ∑ A ∈ boxM C, if A = 0 then 0 else
          ((k : ℚ) * (weight A : ℚ) - (weight (C - A) : ℚ)) * g A * P (C - A)) :
    ∀ C, weight C ≤ wmax → P C = MvPowerSeries.coeff (eF C) (G ^ k) := by
  intro C
  induction h : weight C using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    intro hC
    by_cases hC0 : C = 0
    · subst hC0
      rw [hP0, coeff_zero_pow G hG]
    · have hw : (weight C : ℚ) ≠ 0 := by
        have := weight_pos hC0
        exact_mod_cast this.ne'
      refine mul_left_cancel₀ hw ?_
      rw [hrec C (h ▸ hC), miller_coeff G hG k C]
      refine Finset.sum_congr rfl fun A hA => ?_
      by_cases hA0 : A = 0
      · simp [hA0]
      · have hle := le_of_mem_boxM hA
        have hsa := weight_sub_add hle
        have hApos := weight_pos hA0
        rw [if_neg hA0, if_neg hA0, hg A (by omega),
          ih (weight (C - A)) (by omega) (C - A) rfl (by omega)]

end SaltC1.MaynardK
