/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.TensorA1
import Salt.Maynard.Overshoot

/-!
# C3b — the S₂ tensor lower bound

This file assembles the S₂ diagonal main-term lower bound for the concrete
tensor weight `yTensor`.  Starting from the abstract main term
`∑_{u:uₘ=1} (contraction u)² / ∏ᵢ φ(uᵢ)` (the load-bearing term of
`s2main_lower`), we lower-bound it by `c₀·B₁²·A₁^{k-1}` with an **explicit**
`c₀ = 1/16 > 0`.

## Structure (design C3b, four steps)

For `u` with `uₘ = 1`, the contraction of the concrete tensor factorises as
`S(u) = P(u)·Q(u)`, where `P(u) = ∏_{i≠m} fTilde(uᵢ)` is the "off-`m`" tensor
mass and `Q(u) = ∑_{aₘ<R} [update u m aₘ ∈ 𝒟]·fTilde(aₘ)/φ(aₘ)` is the
coprime/threshold-restricted 1-dimensional `m`-contraction
(`contraction_factor`, **landed exactly**).

1. **Restrict** the outer `u`-sum to the clean sub-region `Good` (squarefree
   coprime off-`m` coords, threshold `Σ_{i≠m} uVal < k − T`), dropping the
   nonnegative complement (`Finset.sum_le_sum_of_subset_of_nonneg`).
2. **Lower-bound** the contraction on `Good`: `Q(u) ≥ (1/2)·B₁`
   (the coprimality omitted-mass bound, PORT-BLOCKED as `H_contract`), hence
   `S(u) = P(u)·Q(u) ≥ (1/2)·B₁·P(u) ≥ 0`.
3. **Square & sum**: `S(u)² ≥ (1/4)·B₁²·P(u)²`; dividing by `∏ᵢ φ(uᵢ)` and using
   `φ(uₘ) = φ(1) = 1` collapses `P(u)²/∏ᵢφ = ∏_{i≠m}(fTilde(uᵢ)²/φ(uᵢ))`
   (**landed exactly**).
4. **Overshoot**: the `(k-1)`-dim threshold-`(k-T)` truncated tensor mass is
   `≥ (1/4)·A₁^{k-1}` (PORT-BLOCKED as `H_overshoot`).

Combining, `main ≥ (1/4)·B₁²·(1/4)·A₁^{k-1} = (1/16)·B₁²·A₁^{k-1}`.

## Port-blocked atoms (each strictly narrower than the conclusion)

* `H_contract` — the per-`u`, 1-dimensional coprime/threshold-restricted
  `m`-contraction is `≥ (1/2)·B₁`.  (No squaring, no outer sum, no `A₁^{k-1}`.)
* `H_overshoot` — the `(k-1)`-dim truncated tensor mass over `Good` is
  `≥ (1/4)·A₁^{k-1}`.  (No `B₁`, no contraction, no squaring.)
-/

open Finset

namespace Salt.Maynard

/-- Nonnegativity of the truncated coordinate weight `fTilde`. -/
lemma fTilde_nonneg (k R : ℕ) (T : ℝ) (r : ℕ) (hR : 2 ≤ R) : 0 ≤ fTilde k R T r := by
  unfold fTilde
  split_ifs with h
  · have hr : 1 ≤ r := by
      rw [sqfCop, Finset.mem_filter] at h
      exact Nat.one_le_iff_ne_zero.mpr h.2.1.ne_zero
    exact fWt_nonneg hr hR
  · exact le_refl 0

/-- The clean sub-region `Good`: sieve tuples with `uₘ = 1`, squarefree coprime
off-`m` coordinates, below the threshold `Σ_{i≠m} uVal(uᵢ) < k − T`. -/
noncomputable def Good (k R : ℕ) (m : Fin k) (T : ℝ) : Finset (Fin k → ℕ) :=
  (kSieveIndex k R (W k)).filter (fun u => u m = 1
    ∧ (∀ i, i ≠ m → u i ∈ sqfCop (R0 k R T) (W k))
    ∧ (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)

/-- **The contraction factorisation (landed exactly).** For `uₘ = 1`, the concrete
tensor `m`-contraction factors as the off-`m` tensor mass `P(u) = ∏_{i≠m} fTilde(uᵢ)`
times the coprime/threshold-restricted 1-dimensional sum
`Q(u) = ∑_{aₘ<R} [update u m aₘ ∈ 𝒟]·fTilde(aₘ)/φ(aₘ)`. -/
theorem contraction_factor (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) (_hum : u m = 1) :
    (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      = (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
        * ∑ am ∈ Finset.range R,
            (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
              / (Nat.totient am : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro am _
  rw [yTensor]
  have hprod : (∏ i, fTilde k R T (Function.update u m am i))
      = fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => fTilde k R T (Function.update u m am i)) (Finset.mem_univ m),
        Function.update_self]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  by_cases hguard : Function.update u m am ∈ kSieveIndex k R (W k)
  · rw [if_pos hguard, if_pos hguard, hprod]; ring
  · rw [if_neg hguard, if_neg hguard]; simp

/-- **C3b — the S₂ tensor lower bound.**  The abstract S₂ main term for the
concrete tensor `yTensor` is bounded below by `(1/16)·B₁²·A₁^{k-1}`, an explicit
positive multiple of the frozen target `B₁²·A₁^{k-1}`.

Two genuinely-analytic sub-atoms are supplied as hypotheses, each strictly
narrower than the conclusion:

* `H_contract` — the coprime/threshold-restricted `m`-contraction is `≥ (1/2)·B₁`
  on `Good` (the coprimality omitted-mass bound `ε_c ≤ 1/2`);
* `H_overshoot` — the `(k-1)`-dim threshold-`(k-T)` truncated tensor mass is
  `≥ (1/4)·A₁^{k-1}`.

Everything else — the factorisation `S = P·Q`, the clean-region restriction, the
squaring/monotonicity, and the `φ(1)=1` product collapse — is proved here. -/
theorem s2_tensor_lower (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R)
    (H_contract : ∀ u ∈ Good k R m T,
        (1 / 2 : ℝ) * B1 k R (W k) T
          ≤ ∑ am ∈ Finset.range R,
              (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
                / (Nat.totient am : ℝ))
    (H_overshoot : (1 / 4 : ℝ) * (A1 k R (W k) T) ^ (k - 1)
          ≤ ∑ u ∈ Good k R m T,
              ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 16 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  rw [ge_iff_le]
  have hB1nn : 0 ≤ B1 k R (W k) T := B1_nonneg k R (W k) T hR
  -- `Good ⊆ {u : uₘ = 1}`
  have hsubset : Good k R m T ⊆ (kSieveIndex k R (W k)).filter (fun u => u m = 1) := by
    intro u hu
    rw [Good, Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    exact ⟨hu.1, hu.2.1⟩
  -- every outer summand is `≥ 0`
  have hterm_nonneg : ∀ u : Fin k → ℕ,
      0 ≤ (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ) :=
    fun u => div_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  -- Step 1: drop the complement of `Good` (all terms `≥ 0`)
  have step1 :
      (∑ u ∈ Good k R m T,
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun u _ _ => hterm_nonneg u)
  -- Step 3 (algebra): the squared, `φ`-collapsed identity on `Good`
  have key_eq : ∀ u ∈ Good k R m T,
      ((1 / 2 : ℝ) * B1 k R (W k) T * (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ)
        = (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
    intro u hu
    rw [Good, Finset.mem_filter] at hu
    have hum : u m = 1 := hu.2.1
    have hφsplit : (∏ i, (Nat.totient (u i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (u i) : ℝ))
          (Finset.mem_univ m)]
      simp [hum]
    have hPD : (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i)) ^ 2
          / (∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
      rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    rw [hφsplit, ← hPD]; ring
  -- Step 2 + 4 assembly on `Good`
  have step2 :
      (1 / 16 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
        ≤ ∑ u ∈ Good k R m T,
            (∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ) := by
    calc (1 / 16 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
        = (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * ((1 / 4 : ℝ) * (A1 k R (W k) T) ^ (k - 1)) := by
          ring
      _ ≤ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2
            * ∑ u ∈ Good k R m T,
                ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) :=
          mul_le_mul_of_nonneg_left H_overshoot
            (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = ∑ u ∈ Good k R m T,
            (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2
              * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
          rw [Finset.mul_sum]
      _ = ∑ u ∈ Good k R m T,
            ((1 / 2 : ℝ) * B1 k R (W k) T * (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (key_eq u hu).symm
      _ ≤ ∑ u ∈ Good k R m T,
            (∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          have humem := hu
          rw [Good, Finset.mem_filter] at hu
          have hum : u m = 1 := hu.2.1
          have huks : u ∈ kSieveIndex k R (W k) := hu.1
          set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
          set S := ∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hSdef
          have hφpos : 0 < ∏ i, (Nat.totient (u i) : ℝ) :=
            Finset.prod_pos (fun i _ => by
              exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos huks i))
          have hPnn : 0 ≤ P :=
            Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T (u i) hR)
          have hcnn : 0 ≤ (1 / 2 : ℝ) * B1 k R (W k) T * P :=
            mul_nonneg (mul_nonneg (by norm_num) hB1nn) hPnn
          -- `S = P·Q` and `Q ≥ (1/2)·B₁`
          have hS : S = P * ∑ am ∈ Finset.range R,
              (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
                / (Nat.totient am : ℝ) := contraction_factor k R m T u hum
          have hQ := H_contract u humem
          have hSge : (1 / 2 : ℝ) * B1 k R (W k) T * P ≤ S := by
            rw [hS, mul_comm ((1 / 2 : ℝ) * B1 k R (W k) T) P]
            exact mul_le_mul_of_nonneg_left hQ hPnn
          have hsq : ((1 / 2 : ℝ) * B1 k R (W k) T * P) ^ 2 ≤ S ^ 2 :=
            pow_le_pow_left₀ hcnn hSge 2
          exact (div_le_div_iff_of_pos_right hφpos).mpr hsq
  exact le_trans step2 step1

end Salt.Maynard
