/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Tensor

/-!
# C3b — the `H_main` sum-level atom (overshoot + `u`-coprimality)

This file discharges the `H_main` hypothesis of `s2_tensor_lower`
(`Salt/Maynard/S2Tensor.lean`): the `(k-1)`-dimensional off-`m` truncated tensor
mass over the clean region `Good` is `≥ (1/2)·A₁^{k-1}`.

## Route (Maynard, overshoot + pairwise-coprimality loss)

Let `S := sqfCop (R₀ k R T) (W k)` and `Box := piFinset (fun i => if i = m then {1} else S)`
be the full `(k-1)`-box (the `m`-coordinate frozen at `1`).  The box mass
`Σ_{Box} ∏_{i≠m} fWt(uᵢ)²/φ(uᵢ) = A₁^{k-1}` (`hmBox_sum`, a genuine tensor identity
via `Finset.prod_univ_sum`).  `Good` embeds into `Box`, and on `Box` a tuple lands
in `Good` exactly when it clears the `uVal`-threshold (`Σ_{i≠m} uVal < k − T`) and is
pairwise coprime (`mem_Good_of_hmBox`; the `∏ < R` sieve clause is automatic from the
threshold via `prod_lt_of_sum_uVal_lt`).  Hence

`Σ_{Good} ≥ A₁^{k-1} − (overshoot region) − (coprimality region)`,

and with each loss region bounded by `(1/4)·A₁^{k-1}` the target `(1/2)·A₁^{k-1}`
follows by `linarith`.

## Port-blockers (the two analytic loss bounds)

The two loss-region fractions are the genuinely analytic content and are taken as
explicit hypotheses `hOver`, `hCop` of `H_main_bound`.  Each is a single concrete
inequality on a `Σ` over a `Box`-filter:

* `hOver` — first-moment Markov overshoot: `Σ_{Box, Σ_{i≠m}uVal ≥ k−T} ≤ (1/4)·A₁^{k-1}`.
  (Mirror of `Overshoot.overshoot_le` at dimension `k−1`, threshold `k−T`, together
  with the `A₁⁽¹⁾/A₁` and `B₁/A₁` ratio arithmetic.)
* `hCop` — pairwise-coprimality mass: `Σ_{Box, ¬pairwise-coprime} ≤ (1/4)·A₁^{k-1}`.
  (`binom(k−1,2)·Σ_{p>D₀} 1/(p−1)² ≤ 1/4` via `CollisionQuant.inv_sq_tele`.)

Everything else — the box identity, the `Good ⊆ Box` embedding, the sieve
reconstruction on `Box`, the `Box \ Good ⊆ overshoot ∪ coprime` split, and the
`fTilde = fWt` conversion on `Good` — is proved here, sorry-free.
-/

open Finset

namespace Salt.Maynard

/-- `fWt(1) = 1`: `u(1) = k·log 1/log R = 0`, so `fWt(1) = 1/(1+0) = 1`. -/
lemma fWt_one (k R : ℕ) : fWt k R 1 = 1 := by
  simp [fWt, uVal, Nat.cast_one, Real.log_one]

/-- The `(k-1)`-box: `k`-tuples with the `m`-coordinate frozen at `1` and every
other coordinate ranging over `S = sqfCop (R₀ k R T) (W k)`. -/
noncomputable def hmBox (k R : ℕ) (m : Fin k) (T : ℝ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun i => if i = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))

/-- The off-`m` box weight `W(u) = ∏_{i≠m} fWt(uᵢ)²/φ(uᵢ)`. -/
noncomputable def hmW (k R : ℕ) (m : Fin k) (_T : ℝ) (u : Fin k → ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.erase m, (fWt k R (u i)) ^ 2 / (Nat.totient (u i) : ℝ)

/-- The box weight is nonnegative. -/
lemma hmW_nonneg (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) : 0 ≤ hmW k R m T u :=
  Finset.prod_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- **Box identity.** The full `(k-1)`-box mass equals `A₁^{k-1}`. -/
lemma hmBox_sum (k R : ℕ) (m : Fin k) (T : ℝ) :
    ∑ u ∈ hmBox k R m T, hmW k R m T u = (A1 k R (W k) T) ^ (k - 1) := by
  classical
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by
    rw [fWt_one]; simp
  -- Step 1: rewrite each `hmW u` as the full `univ`-product (the `m`-factor is `1`).
  have hrw : ∀ u ∈ hmBox k R m T,
      hmW k R m T u = ∏ i, (fWt k R (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
    intro u hu
    simp only [hmBox, Fintype.mem_piFinset] at hu
    have hum : u m = 1 := by
      have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
    rw [hmW]
    have hexp : (∏ i, (fWt k R (u i)) ^ 2 / (Nat.totient (u i) : ℝ))
        = (fWt k R (u m)) ^ 2 / (Nat.totient (u m) : ℝ)
          * ∏ i ∈ Finset.univ.erase m, (fWt k R (u i)) ^ 2 / (Nat.totient (u i) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ
        (fun i => (fWt k R (u i)) ^ 2 / (Nat.totient (u i) : ℝ)) (Finset.mem_univ m)).symm
    rw [hexp, hum, hg1, one_mul]
  rw [Finset.sum_congr rfl hrw]
  -- Step 2: the box is a `piFinset`; run the tensor factorisation backwards.
  simp only [hmBox]
  rw [← Finset.prod_univ_sum
      (fun i : Fin k => if i = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
      (fun _ x => (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
  -- Step 3: evaluate each coordinate factor (`1` at `m`, `A₁` elsewhere).
  have hfac : ∀ i : Fin k,
      (∑ x ∈ (if i = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
          (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
        = if i = m then (1 : ℝ) else A1 k R (W k) T := by
    intro i
    by_cases hi : i = m
    · rw [if_pos hi, if_pos hi, Finset.sum_singleton]; exact hg1
    · rw [if_neg hi, if_neg hi]; rfl
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  rw [← Finset.prod_erase (f := fun i => if i = m then (1 : ℝ) else A1 k R (W k) T)
      Finset.univ (if_pos rfl)]
  rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ m),
      Finset.card_univ, Fintype.card_fin]

/-- `Good` embeds into the `(k-1)`-box. -/
lemma Good_subset_hmBox (k R : ℕ) (m : Fin k) (T : ℝ) :
    Good k R m T ⊆ hmBox k R m T := by
  intro u hu
  rw [Good, Finset.mem_filter] at hu
  obtain ⟨_, hum, hmemS, _⟩ := hu
  simp only [hmBox, Fintype.mem_piFinset]
  intro i
  rcases eq_or_ne i m with rfl | hi
  · rw [if_pos rfl, Finset.mem_singleton]; exact hum
  · rw [if_neg hi]; exact hmemS i hi

/-- **Sieve reconstruction.** A box tuple that clears the `uVal`-threshold and is
pairwise coprime lands in `Good` (the `∏ < R` sieve clause is automatic from the
threshold, via `prod_lt_of_sum_uVal_lt`). -/
lemma mem_Good_of_hmBox (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 1 ≤ k) (hT : 0 ≤ T)
    {u : Fin k → ℕ} (hu : u ∈ hmBox k R m T)
    (hthr : (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) :
    u ∈ Good k R m T := by
  classical
  simp only [hmBox, Fintype.mem_piFinset] at hu
  have hum : u m = 1 := by
    have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
  have hmemS : ∀ i, i ≠ m → u i ∈ sqfCop (R0 k R T) (W k) := by
    intro i hi; have h := hu i; rwa [if_neg hi] at h
  have hsq : ∀ i, Squarefree (u i) := by
    intro i
    rcases eq_or_ne i m with rfl | hi
    · rw [hum]; exact squarefree_one
    · have h := hmemS i hi
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at h; exact h.2.1
  have hcw : ∀ i, Nat.Coprime (u i) (W k) := by
    intro i
    rcases eq_or_ne i m with rfl | hi
    · rw [hum]; exact Nat.coprime_one_left _
    · have h := hmemS i hi
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at h; exact h.2.2
  have hpos : ∀ i, 1 ≤ u i := fun i => Squarefree.pos (hsq i)
  have hprodR : (∏ i, u i) < R := by
    apply prod_lt_of_sum_uVal_lt hk hR u hpos
    have huval_m : uVal k R (u m) = 0 := by rw [hum]; simp [uVal, Nat.cast_one, Real.log_one]
    have hsplit : (∑ i, uVal k R (u i))
        = uVal k R (u m) + ∑ i ∈ Finset.univ.erase m, uVal k R (u i) :=
      (Finset.add_sum_erase Finset.univ (fun i => uVal k R (u i)) (Finset.mem_univ m)).symm
    rw [hsplit, huval_m, zero_add]
    linarith [hthr]
  rw [Good, Finset.mem_filter]
  refine ⟨?_, hum, hmemS, hthr⟩
  rw [mem_kSieveIndex_iff]
  exact ⟨hsq, hcop, hcw, hprodR⟩

/-- **C3b `H_main`.**  The `(k-1)`-dimensional off-`m` truncated tensor mass over the
clean region `Good` is `≥ (1/2)·A₁^{k-1}`.  Conclusion matches the `H_main`
hypothesis of `s2_tensor_lower` verbatim.

The two analytic loss-region fractions are hypotheses (`hOver`, `hCop`, PORT-BLOCKERs);
everything structural is proved. -/
theorem H_main_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 1 ≤ k) (hT : 0 ≤ T)
    (hOver : ∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
        hmW k R m T u ≤ (1 / 4 : ℝ) * (A1 k R (W k) T) ^ (k - 1))
    (hCop : ∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))),
        hmW k R m T u ≤ (1 / 4 : ℝ) * (A1 k R (W k) T) ^ (k - 1)) :
    (1 / 2 : ℝ) * (A1 k R (W k) T) ^ (k - 1)
      ≤ ∑ u ∈ Good k R m T,
          ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
  classical
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
  -- `Σ_{Box\Good} + Σ_Good = Σ_Box = A₁^{k-1}`.
  have hsub := Good_subset_hmBox k R m T
  have hsd := Finset.sum_sdiff (f := hmW k R m T) hsub
  rw [hmBox_sum] at hsd
  -- Name the two loss regions.
  set A := (hmBox k R m T).filter
      (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)) with hA
  set Bset := (hmBox k R m T).filter
      (fun u => ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))) with hB
  -- `Box \ Good ⊆ A ∪ Bset`.
  have hsubAB : (hmBox k R m T) \ (Good k R m T) ⊆ A ∪ Bset := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    obtain ⟨huBox, huG⟩ := hu
    rw [Finset.mem_union, hA, hB, Finset.mem_filter, Finset.mem_filter]
    by_cases hthr : (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T
    · by_cases hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
      · exact absurd (mem_Good_of_hmBox k R m T hR hk hT huBox hthr hcop) huG
      · exact Or.inr ⟨huBox, hcop⟩
    · exact Or.inl ⟨huBox, hthr⟩
  have hsdle : ∑ u ∈ (hmBox k R m T) \ (Good k R m T), hmW k R m T u
      ≤ ∑ u ∈ A ∪ Bset, hmW k R m T u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubAB (fun u _ _ => hmW_nonneg k R m T u)
  -- `Σ_{A∪B} ≤ Σ_A + Σ_B`.
  have hunion : ∑ u ∈ A ∪ Bset, hmW k R m T u
      ≤ ∑ u ∈ A, hmW k R m T u + ∑ u ∈ Bset, hmW k R m T u := by
    have hui := Finset.sum_union_inter (s₁ := A) (s₂ := Bset) (f := hmW k R m T)
    have hinn : 0 ≤ ∑ u ∈ A ∩ Bset, hmW k R m T u :=
      Finset.sum_nonneg (fun u _ => hmW_nonneg k R m T u)
    linarith [hui]
  linarith [hsd, hsdle, hunion, hOver, hCop]

end Salt.Maynard
