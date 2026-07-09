/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.HMainClose
import Salt.Maynard.OvershootCheb
import Salt.Maynard.S2Tensor
import Salt.Maynard.HOmit
import Salt.Maynard.HMain

/-!
# C3b — the S₂ tensor lower bound re-threaded through the Chebyshev overshoot

The committed `s2_tensor_lower_closed` (via `H_main_bound_closed`) was conditional on
the **unprovable** transfer atom `hA11 : A₁⁽¹⁾ ≤ (1/4)·A₁`.  Here we replace that
route entirely, using the now-proven second-moment overshoot
`overshoot_cheb_composed` (`overshoot ≤ (100·T²/k)·A₁^{k-1}`, `o(1)`):

* `overshoot_le_eighth` — in the regime (`T = k^{1/8}/log k`, `log k ≥ 300`) the
  Chebyshev overshoot is `≤ (1/8)·A₁^{k-1}` (since `100·T²/k ≤ 1/8`).
* `H_main_cheb` — mirrors `H_main_bound_closed`'s `sum_sdiff` box assembly with the
  `(1/8, 1/8)` split (overshoot `1/8` from `overshoot_le_eighth`, coprimality `1/8`
  from `hCop_bound`), giving `Σ_Good ≥ (1/2)·A₁^{k-1}` with **no** `hA11`.
* `s2_tensor_lower_cheb` — plugs `H_main_cheb` + `H_omit_bound_closed` into
  `s2_tensor_lower`, giving `≥ (1/4)·B₁²·A₁^{k-1}` with **no** `hA11 ≤ 1/4`.
-/

open Finset

namespace Salt.Maynard

/-- **Overshoot ≤ (1/8)·A₁^{k-1} in the regime.**  From `overshoot_cheb_composed`
(`≤ (100·T²/k)·A₁^{k-1}`) plus `100·T²/k ≤ 1/8`, which holds because `T = k^{1/8}/log k`
gives `k = (T·log k)^8 = T^8·(log k)^8`, so `800·T² ≤ T^8·(log k)^8 = k` (using
`T ≥ 1`, `log k ≥ 300`, hence `T^6·(log k)^8 ≥ 300^8 ≥ 800`). -/
theorem overshoot_le_eighth (k R : ℕ) (m : Fin k) (T : ℝ) (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT0 : 0 ≤ T) (hTk : 5 * T ≤ (k : ℝ)) (hA1pos : 0 < A1 k R (W k) T)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k R T)
    (hlogk : 300 ≤ Real.log k) (hb4 : 4 ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k (W k)
        ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹) * Real.log k)
    (hEB : errB1 k (W k) ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹)) :
    (∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
        hmW k R m T u)
      ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) := by
  have hcomp := overshoot_cheb_composed k R m T hk hR hT0 hTk hA1pos hT hT1 hX hlogk hb4 hEA hEB
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hLpos : (0 : ℝ) < Real.log k := by linarith
  have hLne : Real.log k ≠ 0 := ne_of_gt hLpos
  -- `k = (T · log k)^8`.
  have hkeq : (T * Real.log k) ^ 8 = (k : ℝ) := by
    have h : T * Real.log k = (k : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [hT]; field_simp
    rw [h, ← Real.rpow_natCast ((k : ℝ) ^ ((1 : ℝ) / 8)) 8,
        ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hkeq2 : (k : ℝ) = T ^ 8 * (Real.log k) ^ 8 := by
    rw [mul_pow] at hkeq; exact hkeq.symm
  -- `800·T² ≤ k`.
  have hT2nn : (0 : ℝ) ≤ T ^ 2 := sq_nonneg T
  have hT6 : (1 : ℝ) ≤ T ^ 6 := one_le_pow₀ hT1
  have hL8 : (800 : ℝ) ≤ (Real.log k) ^ 8 := by
    have hmono : (300 : ℝ) ^ 8 ≤ (Real.log k) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) hlogk 8
    have h3 : (800 : ℝ) ≤ (300 : ℝ) ^ 8 := by norm_num
    linarith
  have hLT : (800 : ℝ) ≤ (Real.log k) ^ 8 * T ^ 6 := by
    have h := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ (Real.log k) ^ 8) hT6
    linarith
  have h800 : 800 * T ^ 2 ≤ (k : ℝ) := by
    rw [hkeq2]
    calc 800 * T ^ 2 ≤ ((Real.log k) ^ 8 * T ^ 6) * T ^ 2 :=
          mul_le_mul_of_nonneg_right hLT hT2nn
      _ = T ^ 8 * (Real.log k) ^ 8 := by ring
  -- `100·T²/k ≤ 1/8`.
  have h8 : 100 * T ^ 2 / (k : ℝ) ≤ (1 / 8 : ℝ) := by
    rw [div_le_iff₀ hkpos]; linarith
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 1) := pow_nonneg hA1pos.le _
  calc (∑ u ∈ (hmBox k R m T).filter
            (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
            hmW k R m T u)
      ≤ (100 * T ^ 2 / (k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := hcomp
    _ ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right h8 hApow

/-- **`H_main` via Chebyshev.**  Mirrors the `sum_sdiff`/subadditivity box assembly of
`HMainClose.H_main_bound_closed`, but sources the overshoot loss from
`overshoot_le_eighth` (`1/8`) instead of the `hA11`-conditional `hOver_bound` (`3/8`).
With the coprimality loss `hCop_bound` (`1/8`), the total box loss is `1/4`, so
`Σ_Good ≥ A₁^{k-1} − (1/4)·A₁^{k-1} = (3/4)·A₁^{k-1} ≥ (1/2)·A₁^{k-1}`.  **No** `hA11`. -/
theorem H_main_cheb (k R : ℕ) (m : Fin k) (T : ℝ) (hk : 16 ≤ k) (hR : 2 ≤ R)
    (hTk : 5 * T ≤ (k : ℝ)) (hA1pos : 0 < A1 k R (W k) T)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k R T)
    (hlogk : 300 ≤ Real.log k) (hb4 : 4 ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k (W k)
        ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹) * Real.log k)
    (hEB : errB1 k (W k) ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹)) :
    (1 / 2 : ℝ) * (A1 k R (W k) T) ^ (k - 1)
      ≤ ∑ u ∈ Good k R m T,
          ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hT0 : 0 ≤ T := by linarith
  -- Convert the `fTilde`-summand to `hmW` (on `Good`, off-`m` coords are in `S`).
  have hconv : ∑ u ∈ Good k R m T,
        ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
      = ∑ u ∈ Good k R m T, hmW k R m T u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Good, Finset.mem_filter] at hu
    obtain ⟨_, _, hmemS, _⟩ := hu
    rw [hmW]
    apply Finset.prod_congr rfl
    intro i hi
    rw [fTilde, if_pos (hmemS i (Finset.ne_of_mem_erase hi))]
  rw [hconv]
  have hsub := Good_subset_hmBox k R m T
  have hsd := Finset.sum_sdiff (f := hmW k R m T) hsub
  rw [hmBox_sum] at hsd
  set A := (hmBox k R m T).filter
      (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)) with hA
  set Bset := (hmBox k R m T).filter
      (fun u => ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))) with hB
  have hsubAB : (hmBox k R m T) \ (Good k R m T) ⊆ A ∪ Bset := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    obtain ⟨huBox, huG⟩ := hu
    rw [Finset.mem_union, hA, hB, Finset.mem_filter, Finset.mem_filter]
    by_cases hthr : (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T
    · by_cases hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
      · exact absurd (mem_Good_of_hmBox k R m T hR hk1 hT0 huBox hthr hcop) huG
      · exact Or.inr ⟨huBox, hcop⟩
    · exact Or.inl ⟨huBox, hthr⟩
  have hsdle : ∑ u ∈ (hmBox k R m T) \ (Good k R m T), hmW k R m T u
      ≤ ∑ u ∈ A ∪ Bset, hmW k R m T u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubAB (fun u _ _ => hmW_nonneg k R m T u)
  have hunion : ∑ u ∈ A ∪ Bset, hmW k R m T u
      ≤ ∑ u ∈ A, hmW k R m T u + ∑ u ∈ Bset, hmW k R m T u := by
    have hui := Finset.sum_union_inter (s₁ := A) (s₂ := Bset) (f := hmW k R m T)
    have hinn : 0 ≤ ∑ u ∈ A ∩ Bset, hmW k R m T u :=
      Finset.sum_nonneg (fun u _ => hmW_nonneg k R m T u)
    linarith [hui]
  have hOver : ∑ u ∈ A, hmW k R m T u ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
    overshoot_le_eighth k R m T (by omega) hR hT0 hTk hA1pos hT hT1 hX hlogk hb4 hEA hEB
  have hCop : ∑ u ∈ Bset, hmW k R m T u ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
    hCop_bound k R m T hR hk
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 1) := pow_nonneg (A1_nonneg _ _ _ _) _
  linarith [hsd, hsdle, hunion, hOver, hCop, hApow]

/-- **C3b, fully re-threaded through the Chebyshev overshoot.**  The S₂ diagonal
quadratic form (restricted to `uₘ = 1`) is bounded below by `(1/4)·B₁²·A₁^{k-1}`,
now conditional only on the regime hypotheses (`hk`, `hR`, `hTk`, `hT`, `hT1`, `hX`,
`hlogk`, `hb4`) and the `R`-large error atoms (`hEA`, `hEB`) plus `hB1` — with **no**
unprovable `hA11 : A₁⁽¹⁾ ≤ (1/4)·A₁`.  Positivity `0 < A₁` is derived internally from
`hX : 4 ≤ R0` (so `1 ∈ sqfCop`); the `H_main` slot is supplied by `H_main_cheb`. -/
theorem s2_tensor_lower_cheb (k R : ℕ) (m : Fin k) (T : ℝ) (hk : 16 ≤ k) (hR : 2 ≤ R)
    (hTk : 5 * T ≤ (k : ℝ))
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k R T)
    (hlogk : 300 ≤ Real.log k) (hb4 : 4 ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k (W k)
        ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹) * Real.log k)
    (hEB : errB1 k (W k) ≤ (1 / 100) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹))
    (hB1 : 0 ≤ B1 k R (W k) T) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  -- `0 < A₁`: the element `1 ∈ sqfCop (R0 …) (W k)` (since `R0 ≥ 4 > 1`) contributes
  -- a strictly positive term `fWt(1)²/φ(1) > 0`.
  have h1mem : (1 : ℕ) ∈ sqfCop (R0 k R T) (W k) := by
    rw [sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, squarefree_one, Nat.coprime_one_left _⟩
  have hA1pos : 0 < A1 k R (W k) T := by
    rw [A1]
    apply Finset.sum_pos' (fun r _ => by positivity)
    refine ⟨1, h1mem, ?_⟩
    have hfw : 0 < fWt k R 1 := fWt_pos (by norm_num) hR
    rw [Nat.totient_one]
    positivity
  -- `16·k ≤ D₀ k` (as in `s2_tensor_lower_closed`).
  have hDcube : (k : ℕ) ^ 3 ≤ D₀ k := le_max_left _ _
  have hD : 16 * k ≤ D₀ k := by
    have hk3 : 16 * k ≤ k ^ 3 := by
      have h16 : 16 ≤ k * k := le_trans hk (Nat.le_mul_of_pos_left k (by omega))
      calc 16 * k ≤ (k * k) * k := Nat.mul_le_mul_right k h16
        _ = k ^ 3 := by ring
    exact le_trans hk3 hDcube
  exact s2_tensor_lower k R m T hR hB1
    (H_main_cheb k R m T hk hR hTk hA1pos hT hT1 hX hlogk hb4 hEA hEB)
    (H_omit_bound_closed k R m T hR (by omega) hD)

end Salt.Maynard
