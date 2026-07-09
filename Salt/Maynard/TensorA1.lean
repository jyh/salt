/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Transfer
import Salt.Maynard.KSieve
import Salt.Maynard.Diagonal

/-!
# The C1 tensor identity and the S₁-upper bound `yside ≤ A₁^k`

This file connects the abstract S₁ diagonal side
`yside = ∑_{r∈𝒟} (y r)² / ∏ᵢ φ(rᵢ)` (for the concrete tensor weight
`yTensor`) to the closed form `A₁^k`.

* `tensor_box_eq_A1pow` — the *unconstrained* tensor sum over the box
  `piFinset (sqfCop R₀ W)` equals `A₁^k` exactly, via `Finset.sum_prod_piFinset`.
* `yside_le_A1pow` — the concrete tensor yside (a sum over the sieve index `𝒟`)
  is `≤ A₁^k`, obtained by observing that the `R₀`-cutoff support of
  `yTensor` lands in the box and dropping the `𝒟` constraints.
-/

namespace Salt.Maynard

/-- The truncated coordinate weight: `fWt` inside the `R₀` box (squarefree,
coprime to `W k`, below `R₀`), and `0` outside. The `R₀` cutoff is what forces
the support into the box used by `A₁`. -/
noncomputable def fTilde (k R : ℕ) (T : ℝ) (r : ℕ) : ℝ :=
  if r ∈ sqfCop (R0 k R T) (W k) then fWt k R r else 0

/-- The concrete tensor weight on the sieve index `𝒟`: the product of the
truncated coordinate weights, `0` off `𝒟`. -/
noncomputable def yTensor (k R : ℕ) (T : ℝ) (r : Fin k → ℕ) : ℝ :=
  if r ∈ kSieveIndex k R (W k) then ∏ i, fTilde k R T (r i) else 0

/-- **Deliverable 1** — the unconstrained tensor sum over the box equals `A₁^k`.
The sum over `piFinset (sqfCop R₀ W)` of the coordinate product `∏ᵢ fWt(rᵢ)²/φ(rᵢ)`
factors as `∏ᵢ (∑ fWt²/φ) = A₁^k`. -/
theorem tensor_box_eq_A1pow (k R : ℕ) (T : ℝ) :
    (∑ r ∈ Fintype.piFinset (fun _ : Fin k => sqfCop (R0 k R T) (W k)),
        ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ))
      = (A1 k R (W k) T) ^ k := by
  rw [Finset.sum_prod_piFinset (sqfCop (R0 k R T) (W k))
        (fun _ r => (fWt k R r) ^ 2 / (Nat.totient r : ℝ))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- **Deliverable 2** — the concrete tensor yside is `≤ A₁^k`.

For `r ∈ 𝒟`, `yTensor r = ∏ᵢ fTilde(rᵢ)`, so the yside term equals
`∏ᵢ (fTilde(rᵢ)²/φ(rᵢ))`, which is `∏ᵢ fWt(rᵢ)²/φ(rᵢ)` when every `rᵢ` clears
the `R₀` cutoff (i.e. `rᵢ ∈ sqfCop R₀ W`) and `0` otherwise. The set of such
tuples is a subset of the box `piFinset (sqfCop R₀ W)`, and every box summand is
nonnegative, so the yside is bounded by the full box sum `= A₁^k`. -/
theorem yside_le_A1pow (k R : ℕ) (T : ℝ) :
    (∑ r ∈ kSieveIndex k R (W k),
        (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
      ≤ (A1 k R (W k) T) ^ k := by
  -- Rewrite each `𝒟`-term as the cutoff-guarded coordinate product.
  have hterm : ∀ r ∈ kSieveIndex k R (W k),
      (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
        = if (∀ i, r i ∈ sqfCop (R0 k R T) (W k)) then
            ∏ i, (fWt k R (r i)) ^ 2 / (Nat.totient (r i) : ℝ) else 0 := by
    intro r hr
    simp only [yTensor, if_pos hr]
    -- `(∏ fTilde)² / ∏ φ = ∏ (fTilde²/φ)`.
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    by_cases hall : ∀ i, r i ∈ sqfCop (R0 k R T) (W k)
    · rw [if_pos hall]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [fTilde, if_pos (hall i)]
    · rw [if_neg hall]
      obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      simp only [fTilde, if_neg hi₀]
      norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← tensor_box_eq_A1pow]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    rw [Finset.mem_filter] at hr
    rw [Fintype.mem_piFinset]
    exact hr.2
  · intro r _ _
    exact Finset.prod_nonneg (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

end Salt.Maynard
