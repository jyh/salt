/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Tuple
import Salt.Maynard.PhiAtom

/-!
# Primorial ratio bound (`explicit12` blueprint, wave 5, card W5-4)

`primorial D / φ(primorial D) ≤ 5·√D` for `D ≥ 2` — an ELEMENTARY bound
(no Mertens' theorem, no `∃`-opaque constants), needed so the endgame's
Archimedean `D★` choice can be made with an absolute constant.

## Route

`primorial D` is squarefree, so `primorial D / φ(primorial D) =
∏_{p ≤ D, prime} p/(p−1)`. Each factor `p/(p−1) = 1 + 1/(p−1) ≤ exp(1/(p−1))`,
so the product is `≤ exp(Σ_{p ≤ D} 1/(p−1))`. The sum is bounded elementarily
(no Mertens): the odd primes `≤ D` (i.e. all but `p = 2`) inject into
`{1, …, ⌊(D−1)/2⌋}` via `p ↦ (p−1)/2` (exact since `p` odd), so
`Σ_{p ≤ D, p ≠ 2} 1/(p−1) ≤ (1/2)·Σ_{i=1}^{⌊(D−1)/2⌋} 1/i ≤ (1/2)(1 + log D)`
via the harmonic-number bound `harmonic n ≤ 1 + log n`
(`Mathlib.NumberTheory.Harmonic.Bounds`). Adding back the `p = 2` term (`= 1`)
gives `Σ_{p ≤ D} 1/(p−1) ≤ 3/2 + (log D)/2`, hence the ratio is
`≤ exp(3/2)·√D ≤ 5·√D` (`exp(3/2) < 4.49`).
-/

namespace Salt.Twelve

open Finset

/-! ## Squarefreeness and prime factors of `primorial` -/

/-- A finite product of (distinct) primes is squarefree. Local copy of the
`private` `Salt.Maynard.prod_primes_squarefree` (`Tuple.lean`) — reproved
here since the source lemma is not importable. -/
private lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

/-- `primorial D` is squarefree. -/
private lemma primorial_squarefree (D : ℕ) : Squarefree (primorial D) := by
  unfold primorial
  exact prod_primes_squarefree (fun p hp => (Finset.mem_filter.mp hp).2)

/-- The prime-factor set of `primorial D` is exactly the primes `≤ D`. -/
private lemma primorial_primeFactors (D : ℕ) :
    (primorial D).primeFactors = (Finset.range (D + 1)).filter Nat.Prime := by
  unfold primorial
  exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)

/-! ## The elementary key estimate -/

/-- For an odd prime `p`, `(p:ℝ) - 1 = 2 * ((p-1)/2 : ℕ)` (the division is
exact). -/
private lemma odd_prime_sub_one_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℝ) - 1 = 2 * (((p - 1) / 2 : ℕ) : ℝ) := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hdiv : (p - 1) / 2 = m := by omega
  rw [hdiv]
  have hcast : (p : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  linarith

/-- **Elementary key estimate.** `Σ_{p ≤ D prime} 1/(p−1) ≤ 3/2 + (log D)/2`.
No Mertens: split off `p = 2` (contributing exactly `1`); the remaining odd
primes inject into `{1,…,⌊(D−1)/2⌋}` via `p ↦ (p−1)/2`, and the harmonic-sum
bound `harmonic n ≤ 1 + log n` finishes it. -/
theorem sum_inv_prime_sub_one_le (D : ℕ) (hD : 2 ≤ D) :
    ∑ p ∈ (Finset.range (D + 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ 3 / 2 + Real.log D / 2 := by
  set S := (Finset.range (D + 1)).filter Nat.Prime with hSdef
  have h2S : 2 ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  have hsplit : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1)
      = 1 + ∑ p ∈ S.erase 2, (1 : ℝ) / ((p : ℝ) - 1) := by
    rw [← Finset.insert_erase h2S, Finset.sum_insert (Finset.notMem_erase 2 _)]
    norm_num
  rw [hsplit]
  set M : ℕ := (D - 1) / 2 with hMdef
  set i : ℕ → ℕ := fun p => (p - 1) / 2 with hidef
  -- injectivity of `i` on the odd primes `≤ D`
  have hinj : Set.InjOn i (S.erase 2 : Finset ℕ) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_erase] at hp hq
    obtain ⟨hp2, hpS⟩ := hp
    obtain ⟨hq2, hqS⟩ := hq
    rw [hSdef, Finset.mem_filter] at hpS hqS
    obtain ⟨m, hm⟩ := hpS.2.odd_of_ne_two hp2
    obtain ⟨n, hn⟩ := hqS.2.odd_of_ne_two hq2
    simp only [hidef] at hpq
    omega
  -- the image lands in `Icc 1 M`
  have himg : (S.erase 2).image i ⊆ Finset.Icc 1 M := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨p, hp, rfl⟩ := hj
    simp only [Finset.mem_erase] at hp
    obtain ⟨hp2, hpS⟩ := hp
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hpS
    have hp2le : 2 ≤ p := hpS.2.two_le
    simp only [Finset.mem_Icc, hidef, hMdef]
    omega
  -- rewrite each summand via `odd_prime_sub_one_eq`
  have hstep1 : ∑ p ∈ S.erase 2, (1 : ℝ) / ((p : ℝ) - 1)
      = ∑ p ∈ S.erase 2, (1 : ℝ) / (2 * (i p : ℝ)) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [Finset.mem_erase] at hp
    obtain ⟨hp2, hpS⟩ := hp
    rw [hSdef, Finset.mem_filter] at hpS
    rw [odd_prime_sub_one_eq hpS.2 hp2]
  rw [hstep1]
  -- reindex the sum over the image
  have hstep2 : ∑ p ∈ S.erase 2, (1 : ℝ) / (2 * (i p : ℝ))
      = ∑ j ∈ (S.erase 2).image i, (1 : ℝ) / (2 * (j : ℝ)) :=
    (Finset.sum_image (f := fun j : ℕ => (1 : ℝ) / (2 * (j : ℝ))) hinj).symm
  rw [hstep2]
  -- extend the sum to all of `Icc 1 M` (all terms nonneg)
  have hstep3 : ∑ j ∈ (S.erase 2).image i, (1 : ℝ) / (2 * (j : ℝ))
      ≤ ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (j : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg himg
    intro j _ _
    positivity
  -- factor out the `1/2`
  have hstep4 : ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (2 * (j : ℝ))
      = (1 / 2) * ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (j : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- apply the harmonic bound
  have hharm : ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log M := by
    have h := harmonic_le_one_add_log M
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have hMD : (M : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : M ≤ D)
  have hlogMD : Real.log M ≤ Real.log D := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · rw [hM0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ D))
    · exact Real.log_le_log (by exact_mod_cast hMpos) hMD
  linarith [hstep3, hstep4, hharm, hlogMD]

/-! ## The main ratio bound -/

/-- `exp(3/2) ≤ 5` (numeric; `exp(3/2)^2 = exp(3) = exp(1)^3 < 2.7182818286^3 < 25`). -/
private lemma exp_three_half_le_five : Real.exp (3 / 2 : ℝ) ≤ 5 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hb1 : Real.exp 1 * Real.exp 1 < 2.7182818286 * Real.exp 1 :=
    mul_lt_mul_of_pos_right h1 he1pos
  have hb2 : (2.7182818286 : ℝ) * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_lt_mul_of_pos_left h1 (by norm_num)
  have hb3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := hb1.trans hb2
  have hb4 : Real.exp 1 * Real.exp 1 * Real.exp 1
      < (2.7182818286 * 2.7182818286) * Real.exp 1 :=
    mul_lt_mul_of_pos_right hb3 he1pos
  have hb5 : (2.7182818286 : ℝ) * 2.7182818286 * Real.exp 1
      < 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_lt_mul_of_pos_left h1 (by norm_num)
  have hcube : Real.exp 1 * Real.exp 1 * Real.exp 1 < 25 := by
    have hchain := hb4.trans hb5
    nlinarith [hchain]
  have hexp3eq : Real.exp 1 * Real.exp 1 * Real.exp 1 = Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
  have hexp3lt25 : Real.exp 3 < 25 := hexp3eq ▸ hcube
  have hsqeq : Real.exp (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ) = Real.exp 3 := by
    rw [← Real.exp_add]; norm_num
  have hexp32pos : (0 : ℝ) < Real.exp (3 / 2 : ℝ) := Real.exp_pos _
  nlinarith [hsqeq, hexp3lt25, hexp32pos, sq_nonneg (Real.exp (3 / 2 : ℝ) - 5)]

/-- **The frozen deliverable (W5-4).** `primorial D / φ(primorial D) ≤ 5·√D`
for `D ≥ 2`, elementary (no Mertens). -/
theorem primorial_ratio_le (D : ℕ) (hD : 2 ≤ D) :
    (primorial D : ℝ) / (primorial D).totient ≤ 5 * Real.sqrt D := by
  have hsq : Squarefree (primorial D) := primorial_squarefree D
  have hfac : (primorial D).primeFactors = (Finset.range (D + 1)).filter Nat.Prime :=
    primorial_primeFactors D
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have ratio_eq : (primorial D : ℝ) / (Nat.totient (primorial D) : ℝ)
      = ∏ p ∈ (primorial D).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hnum : (primorial D : ℝ) = ∏ p ∈ (primorial D).primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    rw [hnum, Salt.Maynard.totient_squarefree_cast hsq, ← Finset.prod_div_distrib]
  have hStepB : ∏ p ∈ (primorial D).primeFactors, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ (primorial D).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      apply div_nonneg <;> linarith
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hsplit : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
        field_simp; ring
      rw [hsplit]; linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
  have hStepC : ∏ p ∈ (primorial D).primeFactors, Real.exp (1 / ((p : ℝ) - 1))
      = Real.exp (∑ p ∈ (primorial D).primeFactors, 1 / ((p : ℝ) - 1)) :=
    (Real.exp_sum _ _).symm
  have hSum : ∑ p ∈ (primorial D).primeFactors, 1 / ((p : ℝ) - 1)
      ≤ 3 / 2 + Real.log D / 2 := by
    rw [hfac]; exact sum_inv_prime_sub_one_le D hD
  have hFinal : (primorial D : ℝ) / (Nat.totient (primorial D) : ℝ)
      ≤ Real.exp (3 / 2 + Real.log D / 2) := by
    calc (primorial D : ℝ) / (Nat.totient (primorial D) : ℝ)
        = ∏ p ∈ (primorial D).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := ratio_eq
      _ ≤ ∏ p ∈ (primorial D).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := hStepB
      _ = Real.exp (∑ p ∈ (primorial D).primeFactors, 1 / ((p : ℝ) - 1)) := hStepC
      _ ≤ Real.exp (3 / 2 + Real.log D / 2) := Real.exp_le_exp.mpr hSum
  have hsqrt_eq : Real.sqrt (D : ℝ) = Real.exp (Real.log (D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hDpos]
    congr 1; ring
  have hExpEq : Real.exp (3 / 2 + Real.log D / 2) = Real.exp (3 / 2) * Real.sqrt D := by
    rw [Real.exp_add, ← hsqrt_eq]
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  calc (primorial D : ℝ) / (Nat.totient (primorial D) : ℝ)
      ≤ Real.exp (3 / 2 + Real.log D / 2) := hFinal
    _ = Real.exp (3 / 2) * Real.sqrt D := hExpEq
    _ ≤ 5 * Real.sqrt D := by
        apply mul_le_mul_of_nonneg_right exp_three_half_le_five hsqrt_nonneg

end Salt.Twelve
