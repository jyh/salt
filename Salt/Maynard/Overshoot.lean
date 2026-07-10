/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Transfer
import Salt.Maynard.TensorA1

/-!
# C3a — the overshoot mass bound (first-moment Markov)

The `𝒟`-constraint `∏ᵢ rᵢ < R ⟺ Σᵢ uVal(rᵢ) < k` (since `uVal(r) = k·log r/log R`)
truncates the tensor box-sum, discarding the overshoot region `{Σ uVal ≥ k}`.
This file bounds that overshoot mass by `A₁⁽¹⁾·A₁^{k-1}` via a genuine first-moment
Markov argument — a bounded fraction of `A₁^k`.

* `moment1_box_eq` — the first-moment tensor identity: the box-sum weighted by
  `Σᵢ uVal(rᵢ)` equals `k·A₁⁽¹⁾·A₁^{k-1}` (single special coordinate factorization).
* `overshoot_le` — Markov: the `{Σ uVal ≥ k}`-filtered box mass is `≤ A₁⁽¹⁾·A₁^{k-1}`.
* `trunc_tensor_ge` — the truncated (`{Σ uVal < k}`) box mass is
  `≥ A₁^k − A₁⁽¹⁾·A₁^{k-1}` (box = truncated ⊎ overshoot, `tensor_box_eq_A1pow`).
-/

namespace Salt.Maynard

/-- On the natural-number support `r ≥ 1`, `u(r) = k·log r/log R ≥ 0` — no `2 ≤ R`
needed, since `Real.log` of a natural number is always `≥ 0` (`log 0 = log 1 = 0`). -/
lemma uVal_nonneg_nat (k R r : ℕ) (hr : 1 ≤ r) : 0 ≤ uVal k R r := by
  unfold uVal
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by exact_mod_cast hr))
  · exact Real.log_natCast_nonneg R

/-- **Deliverable 1** — the first-moment tensor identity.  Weighting the tensor
box-sum by `Σᵢ uVal(rᵢ)` and factoring the single special coordinate (which
carries `A₁⁽¹⁾ = Σ fWt²·u/φ`, the remaining `k-1` carrying `A₁ = Σ fWt²/φ`) gives
`Σ_{i} A₁⁽¹⁾·A₁^{k-1} = k·A₁⁽¹⁾·A₁^{k-1}`. -/
theorem moment1_box_eq (k R : ℕ) (T : ℝ) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
        (∑ i, uVal k R (r i)) * ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      = (k : ℝ) * (A1_1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1) := by
  -- Step 1: distribute the coordinate sum over the product weight.
  simp_rw [Finset.sum_mul]
  -- Step 2: swap the box-sum and the coordinate-sum.
  rw [Finset.sum_comm]
  -- For each special coordinate `i`, the box-sum factors as `A₁⁽¹⁾·A₁^{k-1}`.
  have hF : ∀ i : Fin k,
      (∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
          uVal k R (r i) * ∏ j, (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
        = A1_1 k R (W k) T * A1 k R (W k) T ^ (k - 1) := by
    intro i
    -- Rewrite the summand as a single product with the `i`-th coordinate special.
    have factor : ∀ r : Fin k → ℕ,
        uVal k R (r i) * ∏ j, (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ)
          = ∏ j, (if j = i then
                    uVal k R (r j) * ((fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
                  else (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ)) := by
      intro r
      have e1 : (∏ j, (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
              = (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)
                  * ∏ j ∈ Finset.univ.erase i,
                      (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      have e2 : (∏ j, (if j = i then
                    uVal k R (r j) * ((fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
                  else (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ)))
              = (uVal k R (r i) * ((fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)))
                  * ∏ j ∈ Finset.univ.erase i,
                      (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
        congr 1
        exact Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))
      rw [e1, e2]; ring
    have hsum : (∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
            uVal k R (r i) * ∏ j, (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
          = ∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
              ∏ j, (if j = i then
                      uVal k R (r j) * ((fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ))
                    else (fWt k R (r j)) ^ 2 / (Nat.totient (r j) : ℝ)) :=
      Finset.sum_congr rfl (fun r _ => factor r)
    rw [hsum, Finset.sum_prod_piFinset (sqfCop (R0 k R T) (W k))
          (fun j x => if j = i then
                        uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                      else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
    -- The `i`-th coordinate factor sums to `A₁⁽¹⁾`, the others to `A₁`.
    have inner : ∀ j : Fin k,
        (∑ x ∈ sqfCop (R0 k R T) (W k), if j = i then
              uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
            else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
          = if j = i then A1_1 k R (W k) T else A1 k R (W k) T := by
      intro j
      by_cases hji : j = i
      · simp only [if_pos hji]
        rw [A1_1]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      · simp only [if_neg hji]
        rw [A1]
    have hprod : (∏ j, (∑ x ∈ sqfCop (R0 k R T) (W k), if j = i then
              uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
            else (fWt k R x) ^ 2 / (Nat.totient x : ℝ)))
        = ∏ j, (if j = i then A1_1 k R (W k) T else A1 k R (W k) T) :=
      Finset.prod_congr rfl (fun j _ => inner j)
    rw [hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    have hrest : (∏ j ∈ Finset.univ.erase i,
            if j = i then A1_1 k R (W k) T else A1 k R (W k) T)
        = ∏ _j ∈ Finset.univ.erase i, A1 k R (W k) T :=
      Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))
    rw [hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hF i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Deliverable 2** — the overshoot bound (first-moment Markov).  On the
overshoot region `{k ≤ Σ uVal}` we have `1 ≤ (Σ uVal)/k`, so each box weight
`∏ᵢ fWt²/φ` is dominated by `((Σ uVal)/k)·∏ᵢ fWt²/φ`.  Extending to the whole box
(dropped terms are `≥ 0` since `uVal ≥ 0`) and applying `moment1_box_eq` gives
`overshoot ≤ (1/k)·(k·A₁⁽¹⁾·A₁^{k-1}) = A₁⁽¹⁾·A₁^{k-1}`. -/
theorem overshoot_le (k R : ℕ) (T : ℝ) (hk : 1 ≤ k) :
    (∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
        (fun r => (k : ℝ) ≤ ∑ i, uVal k R (r i)),
        ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      ≤ (A1_1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  -- Nonnegativity of the box weight.
  have hPr : ∀ r : Fin k → ℕ,
      0 ≤ ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ) :=
    fun r => Finset.prod_nonneg (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  -- Every box coordinate is `≥ 1` (squarefree), so `uVal ≥ 0` on the box.
  have hri1 : ∀ r : Fin k → ℕ,
      r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)) → ∀ i, 1 ≤ r i := by
    intro r hr i
    rw [Fintype.mem_piFinset] at hr
    have hmem := hr i
    rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hmem
    exact Nat.one_le_iff_ne_zero.mpr hmem.2.1.ne_zero
  calc (∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
            (fun r => (k : ℝ) ≤ ∑ i, uVal k R (r i)),
            ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      ≤ ∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
            (fun r => (k : ℝ) ≤ ∑ i, uVal k R (r i)),
            ((∑ i, uVal k R (r i)) / (k : ℝ))
              * ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_filter] at hr
        have h1 : 1 ≤ (∑ i, uVal k R (r i)) / (k : ℝ) := (one_le_div hkpos).mpr hr.2
        exact le_mul_of_one_le_left (hPr r) h1
    _ ≤ ∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
            ((∑ i, uVal k R (r i)) / (k : ℝ))
              * ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro r hr _
        apply mul_nonneg _ (hPr r)
        apply div_nonneg _ hkpos.le
        exact Finset.sum_nonneg (fun i _ => uVal_nonneg_nat k R (r i) (hri1 r hr i))
    _ = (∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
            (∑ i, uVal k R (r i))
              * ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)) / (k : ℝ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun r _ => by ring)
    _ = ((k : ℝ) * A1_1 k R (W k) T * A1 k R (W k) T ^ (k - 1)) / (k : ℝ) := by
        rw [moment1_box_eq]
    _ = A1_1 k R (W k) T * A1 k R (W k) T ^ (k - 1) := by
        rw [show ((k : ℝ) * A1_1 k R (W k) T * A1 k R (W k) T ^ (k - 1)) / (k : ℝ)
              = (k : ℝ) / (k : ℝ) * (A1_1 k R (W k) T * A1 k R (W k) T ^ (k - 1)) from by ring,
           div_self hkpos.ne', one_mul]

/-- **Deliverable 3** — the truncated tensor lower bound.  The box splits into the
truncated region `{Σ uVal < k}` and its complement, the overshoot `{k ≤ Σ uVal}`.
Since the whole box sums to `A₁^k` (`tensor_box_eq_A1pow`) and the overshoot is
`≤ A₁⁽¹⁾·A₁^{k-1}` (`overshoot_le`), the truncated mass is
`≥ A₁^k − A₁⁽¹⁾·A₁^{k-1}`. -/
theorem trunc_tensor_ge (k R : ℕ) (T : ℝ) (hk : 1 ≤ k) :
    (∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
        (fun r => (∑ i, uVal k R (r i)) < (k : ℝ)),
        ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      ≥ (A1 k R (W k) T) ^ k - (A1_1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)))
    (fun r => (∑ i, uVal k R (r i)) < (k : ℝ))
    (fun r => ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
  rw [tensor_box_eq_A1pow] at hsplit
  -- The complement filter `{¬ (Σ < k)}` equals the overshoot filter `{k ≤ Σ}`.
  have hover : (∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
        (fun r => ¬ ((∑ i, uVal k R (r i)) < (k : ℝ))),
        ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      = (∑ r ∈ (Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k))).filter
        (fun r => (k : ℝ) ≤ ∑ i, uVal k R (r i)),
        ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ)) :=
    Finset.sum_congr (Finset.filter_congr (fun r _ => not_lt)) (fun _ _ => rfl)
  rw [hover] at hsplit
  have hle := overshoot_le k R T hk
  linarith [hle]

end Salt.Maynard
