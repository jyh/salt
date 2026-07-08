/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Diagonal
import Salt.Maynard.DiagonalS2

/-!
# The CORRECTED S₂ diagonalisation for the sieve weight `lam` (Maynard Lemma 5.2)

The file `DiagonalS2.lean` diagonalises `∑ lamG·lamG/∏φ(lcm)` where
`lamG = ∏μ(dᵢ)φ(dᵢ)·wSumG`.  But the *actual* Maynard sieve weight is
`lam = ∏μ(dᵢ)dᵢ·wSum` (the same weight `S₁` uses).  This file proves the
correct diagonalisation of the `lam`-weighted `φ(lcm)`-density sum.

The new arithmetic ingredient is the per-coordinate Möbius/`d/φ` sum
`sigmaMu : ∑_{d∣r, u∣d} μ(d)·(d/φ(d)) = μ(r)·u/φ(r)` (real division), which
replaces the clean Möbius collapse `moebius_inv_dvd_lower_bound` used in the
`S₁` file.  Unlike `S₁`, the inner sum does *not* collapse to a diagonal: the
`d/φ(d)` weight prevents it, giving the contraction `lamPhiContract u = V(u)`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- Move the innermost of three nested sums to the front (local copy; `private`
in the S₁ file). -/
private theorem sum_move3'' {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-! ## The multiplicative atom `n ↦ n/φ(n)` -/

/-- The arithmetic function `n ↦ n/φ(n)` over `ℝ` (with `0 ↦ 0`). -/
noncomputable def nOverPhi : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) / (Nat.totient n), by simp⟩

@[simp] lemma nOverPhi_apply (n : ℕ) : nOverPhi n = (n : ℝ) / (Nat.totient n) := rfl

lemma nOverPhi_isMult : nOverPhi.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n h
  simp only [nOverPhi_apply]
  rw [Nat.totient_mul h]
  push_cast
  rw [mul_div_mul_comm]

/-! ## Deliverable 1 — the crux: `sigmaMu` -/

/-- **The `u = 1` core.** For squarefree `s`,
`∑_{d ∣ s} μ(d)·(d/φ(d)) = μ(s)/φ(s)` (real division).  Proof: this is the
`prodPrimeFactors_one_sub_of_squarefree` identity for the multiplicative
function `n ↦ n/φ(n)`, whose per-prime factor `1 − p/(p−1) = −1/(p−1)`
multiplies to `μ(s)/φ(s)`. -/
theorem sigmaMuCore {s : ℕ} (hs : Squarefree s) :
    (∑ d ∈ s.divisors, ((μ d : ℤ) : ℝ) * ((d : ℝ) / (Nat.totient d)))
      = ((μ s : ℤ) : ℝ) / (Nat.totient s) := by
  -- rewrite the divisor sum as the prime-factor product `∏ (1 − p/φ(p))`
  have key : (∑ d ∈ s.divisors, ((μ d : ℤ) : ℝ) * ((d : ℝ) / (Nat.totient d)))
      = ∏ p ∈ s.primeFactors, (1 - nOverPhi p) := by
    rw [ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      nOverPhi nOverPhi_isMult hs]
    apply Finset.sum_congr rfl; intro d _
    rw [nOverPhi_apply]
  rw [key]
  -- evaluate the product: `μ(s) = ∏ (-1)`, `φ(s) = ∏ (p-1)`
  have hmu : ((μ s : ℤ) : ℝ) = ∏ p ∈ s.primeFactors, (-1 : ℝ) := by
    rw [← ArithmeticFunction.intCoe_apply,
      ← (ArithmeticFunction.isMultiplicative_moebius.intCast (R := ℝ)).prod_primeFactors hs]
    apply Finset.prod_congr rfl; intro p hp
    rw [ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    norm_num
  rw [div_eq_mul_inv, hmu, totient_squarefree_cast hs, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hpp]; push_cast [Nat.cast_sub hpp.one_le]; ring
  rw [nOverPhi_apply, hφp]
  field_simp
  ring

/-- **Deliverable 1 (the crux).** For squarefree `r` and `u ∣ r`, the
Möbius/`d/φ`-weighted divisor sum, restricted to multiples of `u`, evaluates to
`μ(r)·u/φ(r)` (real division).  Proof: reindex `d = u·t` with `t ∣ r/u`
(coprime), factor `μ(u)·(u/φ(u))` out, and apply `sigmaMuCore` to the `t`-sum. -/
theorem sigmaMu {r : ℕ} (hr : Squarefree r) {u : ℕ} (hur : u ∣ r) :
    (∑ d ∈ r.divisors, (if u ∣ d then ((μ d : ℤ) : ℝ) * ((d : ℝ) / (Nat.totient d)) else 0))
      = ((μ r : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient r)) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hu0 : u ≠ 0 := (Nat.pos_of_dvd_of_pos hur (Nat.pos_of_ne_zero hr0)).ne'
  have hupos : 0 < u := Nat.pos_of_ne_zero hu0
  set s := r / u with hs_def
  have hus : u * s = r := Nat.mul_div_cancel' hur
  have hs0 : s ≠ 0 := fun h => hr0 (by rw [← hus, h, mul_zero])
  have hsdvd : s ∣ r := ⟨u, by rw [mul_comm]; exact hus.symm⟩
  have hssq : Squarefree s := hr.squarefree_of_dvd hsdvd
  have hcop : Nat.Coprime u s := by
    apply Nat.coprime_of_squarefree_mul; rw [hus]; exact hr
  -- the reindexing bijection: `{d ∣ r : u ∣ d} = (u * ·) '' s.divisors`
  have hbij : (r.divisors.filter (fun d => u ∣ d)) = s.divisors.image (fun t => u * t) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hdr, _⟩, hud⟩
      refine ⟨d / u, ⟨?_, hs0⟩, Nat.mul_div_cancel' hud⟩
      have heq : u * (d / u) = d := Nat.mul_div_cancel' hud
      have hdvd : u * (d / u) ∣ u * s := by rw [heq, hus]; exact hdr
      exact (Nat.mul_dvd_mul_iff_left hupos).mp hdvd
    · rintro ⟨t, ⟨hts, _⟩, rfl⟩
      exact ⟨⟨by rw [← hus]; exact Nat.mul_dvd_mul_left u hts, hr0⟩, dvd_mul_right u t⟩
  -- per-`t` factorisation of the summand
  have hFut : ∀ t ∈ s.divisors,
      ((μ (u * t) : ℤ) : ℝ) * (((u * t : ℕ) : ℝ) / (Nat.totient (u * t)))
        = (((μ u : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient u)))
          * (((μ t : ℤ) : ℝ) * ((t : ℝ) / (Nat.totient t))) := by
    intro t ht
    have htdvd : t ∣ s := Nat.dvd_of_mem_divisors ht
    have hcut : Nat.Coprime u t := Nat.Coprime.coprime_dvd_right htdvd hcop
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcut,
      Nat.totient_mul hcut]
    push_cast
    rw [mul_div_mul_comm]
    ring
  -- assemble
  calc (∑ d ∈ r.divisors,
        (if u ∣ d then ((μ d : ℤ) : ℝ) * ((d : ℝ) / (Nat.totient d)) else 0))
      = ∑ d ∈ r.divisors.filter (fun d => u ∣ d),
          ((μ d : ℤ) : ℝ) * ((d : ℝ) / (Nat.totient d)) := by
        rw [Finset.sum_filter]
    _ = ∑ t ∈ s.divisors, ((μ (u * t) : ℤ) : ℝ) * (((u * t : ℕ) : ℝ) / (Nat.totient (u * t))) := by
        rw [hbij, Finset.sum_image]
        intro t₁ _ t₂ _ heq
        exact Nat.eq_of_mul_eq_mul_left hupos heq
    _ = ∑ t ∈ s.divisors, (((μ u : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient u)))
          * (((μ t : ℤ) : ℝ) * ((t : ℝ) / (Nat.totient t))) := Finset.sum_congr rfl hFut
    _ = (((μ u : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient u)))
          * ∑ t ∈ s.divisors, (((μ t : ℤ) : ℝ) * ((t : ℝ) / (Nat.totient t))) := by
        rw [Finset.mul_sum]
    _ = (((μ u : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient u))) * (((μ s : ℤ) : ℝ) / (Nat.totient s)) := by
        rw [sigmaMuCore hssq]
    _ = ((μ r : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient r)) := by
        have hmur : ((μ u : ℤ) : ℝ) * ((μ s : ℤ) : ℝ) = ((μ r : ℤ) : ℝ) := by
          rw [← Int.cast_mul,
            ← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, hus]
        have hphir : (Nat.totient u : ℝ) * (Nat.totient s : ℝ) = (Nat.totient r : ℝ) := by
          rw [← Nat.cast_mul, ← Nat.totient_mul hcop, hus]
        rw [show (((μ u : ℤ) : ℝ) * ((u : ℝ) / (Nat.totient u)))
              * (((μ s : ℤ) : ℝ) / (Nat.totient s))
            = (((μ u : ℤ) : ℝ) * ((μ s : ℤ) : ℝ))
              * ((u : ℝ) / ((Nat.totient u : ℝ) * (Nat.totient s : ℝ))) from by ring]
        rw [hmur, hphir]

/-! ## Deliverable 2 — the contraction `V(u) = lamPhiContract u` -/

/-- **The `k`-fold tensor of `sigmaMu`.** For squarefree `r` and `u ∣ r`
coordinatewise, the guarded product-sum over the divisor tuples of `r` factors
as `∏ᵢ μ(rᵢ)·uᵢ/φ(rᵢ)`.  This is the exact analog of `kernelKG`'s
`Finset.prod_univ_sum` tensoring, with `sigmaMu` per coordinate. -/
theorem sigmaMuK {k : ℕ} {r u : Fin k → ℕ} (hr : ∀ i, Squarefree (r i))
    (hu : ∀ i, u i ∣ r i) :
    (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        if (∀ i, u i ∣ d i) then
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
      = ∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))) := by
  have hpi : ∀ (d : Fin k → ℕ),
      (∏ i, (if u i ∣ d i then ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0))
        = if (∀ i, u i ∣ d i) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0 := by
    intro d
    split_ifs with h
    · apply Finset.prod_congr rfl; intro i _; rw [if_pos (h i)]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  calc (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
        if (∀ i, u i ∣ d i) then
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
      = ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
          ∏ i, (if u i ∣ d i then
            ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0) := by
        apply Finset.sum_congr rfl; intro d _; rw [hpi d]
    _ = ∏ i, ∑ dᵢ ∈ (r i).divisors,
          (if u i ∣ dᵢ then ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0) :=
        (Finset.prod_univ_sum (fun i => (r i).divisors)
          (fun i dᵢ => if u i ∣ dᵢ then
            ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0)).symm
    _ = ∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))) := by
        apply Finset.prod_congr rfl; intro i _
        exact sigmaMu (hr i) (hu i)

/-- **Ingredient B — the contraction `V(u)`.** The `m`-agnostic full contraction
`V(u) = (∏ uᵢ)·∑_{r∈𝒟, uᵢ∣rᵢ} y_r·∏μ(rᵢ)/∏φ(rᵢ)²`.  Unlike `S₁`, this does
*not* collapse to a single diagonal term (the `d/φ` weight prevents it). -/
noncomputable def lamPhiContract (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (u : Fin k → ℕ) : ℝ :=
  (∏ i, (u i : ℝ)) * ∑ r ∈ kSieveIndex k R W,
    (if ∀ i, u i ∣ r i then
       y r * (∏ i, ((μ (r i) : ℤ) : ℝ)) / (∏ i, (Nat.totient (r i) : ℝ)) ^ 2
     else 0)

/-- **Deliverable 2 — the intermediate `W`-sum.** The `lam`-weighted
`φ`-density sum, restricted to multiples of `u`, equals the full contraction
`V(u) = lamPhiContract u`.  Proof: expand `wSum`, swap the `d`/`r` sums, and
apply `sigmaMuK` per fixed `r` (the inner `d`-sum contracts by `sigmaMu`). -/
theorem wsum_lam_phi (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (u : Fin k → ℕ) :
    (∑ d ∈ kSieveIndex k R W,
      (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
      = lamPhiContract k R W y u := by
  -- per-`d` factorisation of `lam d / ∏ φ(dᵢ)`
  have hlam : ∀ d, lam k R W y d / (∏ i, (Nat.totient (d i) : ℝ))
      = (∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i)))) * wSum k R W y d := by
    intro d
    rw [lam, show (∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))))
          = (∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ)) / (∏ i, (Nat.totient (d i) : ℝ)) from ?_]
    · ring
    · rw [← Finset.prod_div_distrib]; apply Finset.prod_congr rfl; intro i _; rw [mul_div_assoc]
  -- LHS to canonical `∑_r` form
  have hLHS : (∑ d ∈ kSieveIndex k R W,
        (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
      = ∑ r ∈ kSieveIndex k R W, (if (∀ i, u i ∣ r i) then
          (y r / ∏ i, (Nat.totient (r i) : ℝ))
            * ∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))) else 0) := by
    have hstep : (∑ d ∈ kSieveIndex k R W,
          (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
        = ∑ d ∈ kSieveIndex k R W, ∑ r ∈ kSieveIndex k R W,
            (if (∀ i, u i ∣ d i) then
              ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
            * (if (∀ i, d i ∣ r i) then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro d _
      by_cases h : ∀ i, u i ∣ d i
      · rw [if_pos h, hlam d, wSum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _; rw [if_pos h]
      · rw [if_neg h]; symm; apply Finset.sum_eq_zero; intro r _; rw [if_neg h, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    have hsq : ∀ i, Squarefree (r i) := fun i => ((mem_kSieveIndex_iff r).mp hr).1 i
    by_cases hguard : ∀ i, u i ∣ r i
    · rw [if_pos hguard]
      have hconv : (∑ d ∈ kSieveIndex k R W,
            (if (∀ i, u i ∣ d i) then
              ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
            * (if (∀ i, d i ∣ r i) then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0))
          = (∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
              (if (∀ i, u i ∣ d i) then
                ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0))
            * (y r / ∏ i, (Nat.totient (r i) : ℝ)) := by
        rw [Finset.sum_congr rfl (fun d _ => mul_ite_zero (P := ∀ i, d i ∣ r i)
          (a := (if (∀ i, u i ∣ d i) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0))
          (b := y r / ∏ i, (Nat.totient (r i) : ℝ)))]
        rw [sum_ksieve_guarded_eq hr (fun d =>
          (if (∀ i, u i ∣ d i) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
          * (y r / ∏ i, (Nat.totient (r i) : ℝ))), ← Finset.sum_mul]
      rw [hconv, sigmaMuK hsq hguard]; ring
    · rw [if_neg hguard]
      apply Finset.sum_eq_zero; intro d _
      by_cases hud : ∀ i, u i ∣ d i
      · have hb : ¬ (∀ i, d i ∣ r i) := fun hdr => hguard (fun i => (hud i).trans (hdr i))
        rw [if_neg hb, mul_zero]
      · rw [if_neg hud, zero_mul]
  -- `lamPhiContract u` to the same canonical `∑_r` form
  have hRHS : lamPhiContract k R W y u
      = ∑ r ∈ kSieveIndex k R W, (if (∀ i, u i ∣ r i) then
          (y r / ∏ i, (Nat.totient (r i) : ℝ))
            * ∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))) else 0) := by
    rw [lamPhiContract, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [mul_ite_zero]
    by_cases hguard : ∀ i, u i ∣ r i
    · rw [if_pos hguard, if_pos hguard]
      have hprodeq : (∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))))
          = (∏ i, ((μ (r i) : ℤ) : ℝ)) * (∏ i, (u i : ℝ)) / (∏ i, (Nat.totient (r i) : ℝ)) := by
        calc (∏ i, (((μ (r i) : ℤ) : ℝ) * ((u i : ℝ) / (Nat.totient (r i)))))
            = ∏ i, (((μ (r i) : ℤ) : ℝ) * (u i : ℝ)) / (Nat.totient (r i) : ℝ) := by
              apply Finset.prod_congr rfl; intro i _; rw [mul_div_assoc]
          _ = (∏ i, ((μ (r i) : ℤ) : ℝ) * (u i : ℝ)) / (∏ i, (Nat.totient (r i) : ℝ)) := by
              rw [Finset.prod_div_distrib]
          _ = (∏ i, ((μ (r i) : ℤ) : ℝ)) * (∏ i, (u i : ℝ)) / (∏ i, (Nat.totient (r i) : ℝ)) := by
              rw [Finset.prod_mul_distrib]
      rw [hprodeq]; ring
    · rw [if_neg hguard, if_neg hguard]
  rw [hLHS, hRHS]

/-! ## Deliverable 3 — the corrected S₂ diagonalisation (Lemma 5.2) -/

/-- **Per-coordinate `φ(gcd)` expansion, tensored over `Fin k`.** For sieve
tuples `d, e`, `∏ᵢ φ(gcd(dᵢ,eᵢ)) = ∑_{u∈𝒟, uᵢ∣dᵢ ∧ uᵢ∣eᵢ} ∏ᵢ g(uᵢ)`.  This is
the `g`-analog of the `φ = 1 ∗ g` divisor identity (`sum_gMult_eq_totient`),
tensored and moved onto `𝒟` by divisor-closedness. -/
theorem prod_totient_gcd_expand {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) :
    (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
      = ∑ u ∈ kSieveIndex k R W,
          (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) := by
  have hdsq : ∀ i, Squarefree (d i) := fun i => ((mem_kSieveIndex_iff d).mp hd).1 i
  have hgcd : ∀ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ)
      = ∑ uᵢ ∈ (d i).divisors, if uᵢ ∣ d i ∧ uᵢ ∣ e i then (gMult uᵢ : ℝ) else 0 := by
    intro i
    have hd0 : d i ≠ 0 := (hdsq i).ne_zero
    have hgd : Nat.gcd (d i) (e i) ∣ d i := Nat.gcd_dvd_left _ _
    have hgsf : Squarefree (Nat.gcd (d i) (e i)) := (hdsq i).squarefree_of_dvd hgd
    have hsum : (∑ uᵢ ∈ (Nat.gcd (d i) (e i)).divisors, (gMult uᵢ : ℝ))
        = (Nat.totient (Nat.gcd (d i) (e i)) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast sum_gMult_eq_totient hgsf
    rw [← hsum, Salt.SelbergPort.sum_over_dvd_ite hd0 hgd]
    apply Finset.sum_congr rfl; intro uᵢ _
    simp only [Nat.dvd_gcd_iff]
  calc (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
      = ∏ i, ∑ uᵢ ∈ (d i).divisors, (if uᵢ ∣ d i ∧ uᵢ ∣ e i then (gMult uᵢ : ℝ) else 0) := by
        apply Finset.prod_congr rfl; intro i _; exact hgcd i
    _ = ∑ u ∈ Fintype.piFinset (fun i => (d i).divisors),
          ∏ i, (if u i ∣ d i ∧ u i ∣ e i then (gMult (u i) : ℝ) else 0) :=
        Finset.prod_univ_sum (fun i => (d i).divisors)
          (fun i uᵢ => if uᵢ ∣ d i ∧ uᵢ ∣ e i then (gMult uᵢ : ℝ) else 0)
    _ = ∑ u ∈ Fintype.piFinset (fun i => (d i).divisors),
          (if (∀ i, u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro u hu
        rw [Fintype.mem_piFinset] at hu
        have hud : ∀ i, u i ∣ d i := fun i => Nat.dvd_of_mem_divisors (hu i)
        split_ifs with he'
        · apply Finset.prod_congr rfl; intro i _; rw [if_pos ⟨hud i, he' i⟩]
        · obtain ⟨i, hi⟩ := not_forall.mp he'
          exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (fun h => hi h.2))
    _ = ∑ u ∈ kSieveIndex k R W,
          (if (∀ i, u i ∣ d i) then
            (if (∀ i, u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) else 0) := by
        rw [sum_ksieve_guarded_eq hd
          (fun u => if (∀ i, u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0)]
    _ = ∑ u ∈ kSieveIndex k R W,
          (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro u _
        by_cases hP : ∀ i, u i ∣ d i <;> by_cases hQ : ∀ i, u i ∣ e i
        · rw [if_pos hP, if_pos hQ, if_pos (forall_and.mpr ⟨hP, hQ⟩)]
        · rw [if_pos hP, if_neg hQ, if_neg (fun h => hQ (forall_and.mp h).2)]
        · rw [if_neg hP, if_neg (fun h => hP (forall_and.mp h).1)]
        · rw [if_neg hP, if_neg (fun h => hP (forall_and.mp h).1)]

/-- **Deliverable 3 — Maynard's Lemma 5.2 (the CORRECT S₂ diagonalisation).**
With the *actual* sieve weight `lam` (same as `S₁`), the S₂ quadratic form over
`𝒟 × 𝒟` with denominator `∏ᵢ φ(lcm(dᵢ,eᵢ))` diagonalises to
`∑_u (∏ᵢ g(uᵢ))·V(u)²`, where `V(u) = lamPhiContract u`.  Unlike `S₁`, `V(u)`
does not collapse to a single diagonal term — this is the S₂-vs-S₁ asymmetry. -/
theorem s2_diag_lam (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (_hy0 : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
      = ∑ u ∈ kSieveIndex k R W, (∏ i, (gMult (u i) : ℝ)) * (lamPhiContract k R W y u) ^ 2 := by
  -- (stepA) per-`(d,e)`: split off `∏ φ(gcd)` from `1/∏ φ(lcm)`.
  have stepA : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
        = (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
          * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
          * ∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ) := by
    intro d hd e he
    have hdsq : ∀ i, Squarefree (d i) := fun i => ((mem_kSieveIndex_iff d).mp hd).1 i
    have hesq : ∀ i, Squarefree (e i) := fun i => ((mem_kSieveIndex_iff e).mp he).1 i
    have hφd : (∏ i, (Nat.totient (d i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos hd i)).ne'
    have hφe : (∏ i, (Nat.totient (e i) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos he i)).ne'
    have hφlcm : (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr; intro i _
      have : 0 < Nat.totient (Nat.lcm (d i) (e i)) := Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
          (kSieveIndex_coord_pos he i).ne'))
      exact_mod_cast this.ne'
    have hkey : (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
          * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
        = (∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      exact totient_gcd_mul_totient_lcm (hdsq i) (hesq i)
    rw [div_eq_iff hφlcm]
    rw [show (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * (∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
            * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
          = (lam k R W y d * lam k R W y e)
            / ((∏ i, (Nat.totient (d i) : ℝ)) * (∏ i, (Nat.totient (e i) : ℝ)))
            * ((∏ i, (Nat.totient (Nat.gcd (d i) (e i)) : ℝ))
              * (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))) from by ring]
    rw [hkey, div_mul_cancel₀ _ (mul_ne_zero hφd hφe)]
  -- (hMain) rewrite each summand as a `∑_u` via `stepA` + `prod_totient_gcd_expand`.
  have hMain : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)
        = ∑ u ∈ kSieveIndex k R W,
            (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
              * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
              * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0) := by
    intro d hd e he
    rw [stepA d hd e he, prod_totient_gcd_expand hd, Finset.mul_sum]
  -- (hInner) per-`u` collapse to `∏ g(uᵢ)·V(u)²`.
  have hInner : ∀ u ∈ kSieveIndex k R W,
      (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
          * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
          * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0))
        = (∏ i, (gMult (u i) : ℝ)) * (lamPhiContract k R W y u) ^ 2 := by
    intro u _
    have he2 : (∑ e ∈ kSieveIndex k R W,
          (if (∀ i, u i ∣ e i) then
            (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ)) * ∏ i, (gMult (u i) : ℝ) else 0))
        = (∏ i, (gMult (u i) : ℝ)) * lamPhiContract k R W y u := by
      rw [← wsum_lam_phi k R W y u, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [mul_ite_zero]; split_ifs with h
      · ring
      · rfl
    calc (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          (lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ))
            * (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
            * (if (∀ i, u i ∣ d i ∧ u i ∣ e i) then ∏ i, (gMult (u i) : ℝ) else 0))
        = (∑ d ∈ kSieveIndex k R W,
              (if (∀ i, u i ∣ d i) then lam k R W y d / ∏ i, (Nat.totient (d i) : ℝ) else 0))
          * (∑ e ∈ kSieveIndex k R W,
              (if (∀ i, u i ∣ e i) then
                (lam k R W y e / ∏ i, (Nat.totient (e i) : ℝ))
                  * ∏ i, (gMult (u i) : ℝ)
                else 0)) := by
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          by_cases hP : ∀ i, u i ∣ d i <;> by_cases hQ : ∀ i, u i ∣ e i
          · rw [if_pos (forall_and.mpr ⟨hP, hQ⟩), if_pos hP, if_pos hQ]; ring
          · rw [if_neg (fun h => hQ (forall_and.mp h).2), if_pos hP, if_neg hQ]; ring
          · rw [if_neg (fun h => hP (forall_and.mp h).1), if_neg hP, if_pos hQ]; ring
          · rw [if_neg (fun h => hP (forall_and.mp h).1), if_neg hP, if_neg hQ]; ring
      _ = lamPhiContract k R W y u * ((∏ i, (gMult (u i) : ℝ)) * lamPhiContract k R W y u) := by
          rw [wsum_lam_phi k R W y u, he2]
      _ = (∏ i, (gMult (u i) : ℝ)) * (lamPhiContract k R W y u) ^ 2 := by ring
  -- assemble
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hMain d hd e he))]
  rw [sum_move3'']
  apply Finset.sum_congr rfl; intro u hu
  exact hInner u hu

end Salt.Maynard
