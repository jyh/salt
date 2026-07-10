/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom
import Salt.Maynard.Mertens

/-!
# N3.4 — Rankin's multiplicative-sum bound

For a fixed exponent `L ∈ ℕ` we bound the multiplicative sum
`Σ_{q < Q, squarefree} L^{ω(q)}/φ(q)` (with `ω q = q.primeFactors.card`) by
`(C log Q)^L`.

The route is the classical Rankin / Euler-product argument:

1. On squarefree `q`, `L^{ω q}/φ(q) = ∏_{p ∣ q} (L/(p−1))`
   (`rankin_term_eq`), using `φ(q) = ∏_{p ∣ q}(p−1)` for squarefree `q`.
2. `q ↦ q.primeFactors` injects squarefree `q < Q` into the powerset of the
   primes `< Q`, so the sum is a sub-sum of the nonnegative expansion
   `∏_{p < Q}(1 + L/(p−1)) = Σ_{S} ∏_{p ∈ S} L/(p−1)` (`Finset.prod_add`).
3. Take logs: `log ∏ = Σ log(1 + L/(p−1)) ≤ Σ L/(p−1) = L·Σ 1/(p−1) ≤
   L(log log Q + C₀)` (via `log(1+x) ≤ x` and Mertens
   `sum_inv_prime_sub_one_le`), then exponentiate to `(e^{C₀} log Q)^L`.

Class B (guide): Finset powerset step plus log/exp bookkeeping. The constant
is `C = exp (max C₀ 0) ≥ 1`; no small-`Q` case split is needed because the
`p ≤ Q` Mertens sum dominates the `p < Q` product uniformly for `Q ≥ 2`.
-/

open Finset

namespace Salt.Maynard

/-- The local Euler factor `L/(p−1)`. -/
noncomputable def rFac (L p : ℕ) : ℝ := (L : ℝ) / ((p : ℝ) - 1)

/-- For a prime `p`, the Euler factor `L/(p−1)` is nonnegative. -/
lemma rFac_nonneg (L : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ rFac L p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  refine div_nonneg (by positivity) (by linarith)

/-- **Per-term factorization.** For squarefree `q`,
`L^{ω q}/φ(q) = ∏_{p ∣ q} (L/(p−1))`. -/
lemma rankin_term_eq (L : ℕ) {q : ℕ} (hq : Squarefree q) :
    (L : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
      = ∏ p ∈ q.primeFactors, rFac L p := by
  simp only [rFac]
  rw [totient_squarefree_cast hq, Finset.prod_div_distrib, Finset.prod_const]

/-- **Rankin's bound.** `Σ_{q < Q, squarefree} L^{ω(q)}/φ(q) ≤ (C log Q)^L`
for a fixed `L ∈ ℕ`, with `C = exp (max C₀ 0) ≥ 1` where `C₀` is the Mertens
constant. `ω q = q.primeFactors.card`. -/
theorem rankin_bound (L : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∑ q ∈ (Finset.range Q).filter Squarefree,
          ((L : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        ≤ (C * Real.log Q) ^ L := by
  obtain ⟨C₀, hC₀⟩ := sum_inv_prime_sub_one_le
  set C₀' : ℝ := max C₀ 0 with hC₀'def
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  have hC₀'ge : C₀ ≤ C₀' := le_max_left _ _
  refine ⟨Real.exp C₀', ?_, ?_⟩
  · calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp C₀' := Real.exp_le_exp.mpr hC₀'0
  intro Q hQ
  -- Real bookkeeping for `Q`.
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ1
  set SF := (Finset.range Q).filter Squarefree with hSF
  set P := (Finset.range Q).filter Nat.Prime with hP
  -- Step 1: rewrite each summand as a product of Euler factors.
  have hstep1 : ∑ q ∈ SF, ((L : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
      = ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac L p := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hSF, Finset.mem_filter] at hq
    exact rankin_term_eq L hq.2
  rw [hstep1]
  -- Injectivity of `primeFactors` on squarefree numbers.
  have hinj : Set.InjOn Nat.primeFactors ↑SF := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hSF, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2]
  -- The image of `primeFactors` lands in the powerset of the primes `< Q`.
  have hsub : SF.image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    rw [hSF, Finset.mem_filter] at hq
    rw [Finset.mem_powerset]
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range]
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hqr : q < Q := by have := hq.1; rwa [Finset.mem_range] at this
    have hq0 : 0 < q := Nat.pos_of_ne_zero hq.2.ne_zero
    have hpq : p ≤ q := Nat.le_of_dvd hq0 hpd
    exact ⟨by omega, hpp⟩
  -- Step 2: `Finset.prod_add` expands the Euler product as a powerset sum.
  have hprodadd : ∏ p ∈ P, (1 + rFac L p)
      = ∑ t ∈ P.powerset, ∏ p ∈ t, rFac L p := by
    have h := Finset.prod_add (fun p => rFac L p) (fun _ => (1 : ℝ)) P
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  -- Nonnegativity of powerset terms (each factor is over primes `< Q`).
  have hnonneg : ∀ t ∈ P.powerset, t ∉ SF.image Nat.primeFactors →
      0 ≤ ∏ p ∈ t, rFac L p := by
    intro t ht _
    rw [Finset.mem_powerset] at ht
    refine Finset.prod_nonneg (fun p hp => rFac_nonneg L ?_)
    have := ht hp
    rw [hP, Finset.mem_filter] at this
    exact this.2
  -- Combine steps 1–2: the sum is a sub-sum of the Euler product.
  have himg : ∑ t ∈ SF.image Nat.primeFactors, (∏ p ∈ t, rFac L p)
      = ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac L p := Finset.sum_image hinj
  have hstep2 : ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac L p
      ≤ ∏ p ∈ P, (1 + rFac L p) := by
    rw [hprodadd, ← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  -- Step 3: bound the log of the Euler product.
  have hfacpos : ∀ p ∈ P, 0 < 1 + rFac L p := by
    intro p hp
    have hpp : p.Prime := by rw [hP, Finset.mem_filter] at hp; exact hp.2
    have := rFac_nonneg L hpp
    linarith
  have hprodpos : 0 < ∏ p ∈ P, (1 + rFac L p) := Finset.prod_pos hfacpos
  have hlogprod : Real.log (∏ p ∈ P, (1 + rFac L p))
      ≤ (L : ℝ) * (Real.log (Real.log Q) + C₀') := by
    rw [Real.log_prod (fun p hp => (hfacpos p hp).ne')]
    -- `log(1+x) ≤ x`.
    have h1 : ∑ p ∈ P, Real.log (1 + rFac L p) ≤ ∑ p ∈ P, rFac L p := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      linarith [Real.log_le_sub_one_of_pos (hfacpos p hp)]
    -- `Σ L/(p−1) = L · Σ 1/(p−1)`.
    have h2 : ∑ p ∈ P, rFac L p = (L : ℝ) * ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by simp only [rFac]; ring)
    -- Mertens: `Σ_{p ≤ Q} 1/(p−1) ≤ log log Q + C₀`, dominating `p < Q`.
    have h3 : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ≤ Real.log (Real.log Q) + C₀' := by
      have hrange : Finset.range Q ⊆ Finset.range (Q + 1) := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      have hsubP : P ⊆ (Finset.range (Q + 1)).filter Nat.Prime := by
        rw [hP]; exact Finset.filter_subset_filter _ hrange
      have hnn : ∀ p ∈ (Finset.range (Q + 1)).filter Nat.Prime, p ∉ P →
          0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
        intro p hp _
        rw [Finset.mem_filter] at hp
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        exact div_nonneg (by norm_num) (by linarith)
      calc ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1)
          ≤ ∑ p ∈ (Finset.range (Q + 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubP hnn
        _ ≤ Real.log (Real.log Q) + C₀ := hC₀ Q hQ
        _ ≤ Real.log (Real.log Q) + C₀' := by linarith
    calc ∑ p ∈ P, Real.log (1 + rFac L p)
        ≤ ∑ p ∈ P, rFac L p := h1
      _ = (L : ℝ) * ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := h2
      _ ≤ (L : ℝ) * (Real.log (Real.log Q) + C₀') :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  -- Step 4: exponentiate the log bound.
  have hRHSeq : Real.exp ((L : ℝ) * (Real.log (Real.log Q) + C₀'))
      = (Real.exp C₀' * Real.log Q) ^ L := by
    rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hlogQ]
    ring
  calc ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac L p
      ≤ ∏ p ∈ P, (1 + rFac L p) := hstep2
    _ = Real.exp (Real.log (∏ p ∈ P, (1 + rFac L p))) := (Real.exp_log hprodpos).symm
    _ ≤ Real.exp ((L : ℝ) * (Real.log (Real.log Q) + C₀')) := Real.exp_le_exp.mpr hlogprod
    _ = (Real.exp C₀' * Real.log Q) ^ L := hRHSeq

end Salt.Maynard
