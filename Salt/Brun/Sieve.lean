/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.M2
import Salt.Brun.M3Expansion

/-!
# The twin-prime Selberg sieve setup (blueprint N2.6)

Assembles the M2 facts about `rho` into a mathlib `BoundingSieve` for sifting
the values `n(n+2)`, `n ∈ [1,N]`, by the primes dividing a squarefree `P`:

* `nu d = rho d / d` as an `ArithmeticFunction ℝ`, multiplicative (from N2.2),
  with `0 < ν(p) < 1` on every prime (from N2.3);
* `support = (Icc 1 N).image (n ↦ n(n+2))`, of cardinality `N` (from N2.5),
  each element weight `1`, so `totalMass = N`;
* the sieve's remainder `rem d` equals the M2 `rem d N` (from N2.4), so it is
  bounded by `progression_count_bound`.
-/

open ArithmeticFunction Finset

namespace Salt.TwinSieve

/-- `n ↦ n(n+2)` is injective on ℕ (from strict monotonicity, N2.5). -/
lemma twinProd_injective : Function.Injective (fun n : ℕ => n * (n + 2)) := by
  intro a b h
  simp only at h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (by have := twinProd_strictMono a b hab; omega)
  · exact hab
  · exact absurd h (by have := twinProd_strictMono b a hab; omega)

/-- N2.6: the density `ν d = ρ(d)/d` as an arithmetic function (`ν 0 = 0`). -/
noncomputable def nu : ArithmeticFunction ℝ :=
  ⟨fun d => (rho d : ℝ) / d, by simp [rho]⟩

@[simp] lemma nu_apply (d : ℕ) : nu d = (rho d : ℝ) / d := rfl

/-- `ν` is multiplicative on coprime moduli (from N2.2). -/
lemma nu_mult : nu.IsMultiplicative := by
  constructor
  · simp only [nu_apply]; norm_num [show rho 1 = 1 by decide]
  · intro m n hmn
    simp only [nu_apply]
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [Nat.coprime_zero_left] at hmn; subst hmn; simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.coprime_zero_right] at hmn; subst hmn; simp
    rw [rho_mul_of_coprime hm hn hmn]; push_cast; field_simp

/-- `0 < ν(p)` for prime `p` (from N2.3: `ρ(p) ≥ 1`). -/
lemma nu_pos_of_prime (p : ℕ) (hp : p.Prime) : 0 < nu p := by
  rw [nu_apply]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hrho : 0 < (rho p : ℝ) := by
    rcases eq_or_ne p 2 with rfl | hodd
    · rw [rho_two]; norm_num
    · rw [rho_odd_prime hp hodd]; norm_num
  positivity

/-- `ν(p) < 1` for prime `p` (from N2.3: `ρ(2)/2 = 1/2`, `ρ(p)/p = 2/p ≤ 2/3`
for odd `p`). -/
lemma nu_lt_one_of_prime (p : ℕ) (hp : p.Prime) : nu p < 1 := by
  rw [nu_apply]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [div_lt_one hp0]
  rcases eq_or_ne p 2 with rfl | hodd
  · rw [rho_two]; norm_num
  · rw [rho_odd_prime hp hodd]
    have h3 : 3 ≤ p := by
      have h2 := hp.two_le
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hodd
      · rcases h with ⟨k, hk⟩; omega
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    push_cast; linarith

/-- **N2.6**: the `BoundingSieve` for twin primes up to `N`, sifting by the
primes dividing the squarefree modulus `P`. -/
noncomputable def sieve (N : ℕ) (P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Icc 1 N).image (fun n => n * (n + 2))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := nu
  nu_mult := nu_mult
  nu_pos_of_prime := fun p hp _ => nu_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => nu_lt_one_of_prime p hp

variable {N P : ℕ} {hP : Squarefree P}

@[simp] lemma sieve_totalMass : (sieve N P hP).totalMass = N := rfl
@[simp] lemma sieve_nu : (sieve N P hP).nu = nu := rfl
@[simp] lemma sieve_prodPrimes : (sieve N P hP).prodPrimes = P := rfl

/-- N2.5 (second half): `support` has cardinality exactly `N`. -/
lemma sieve_support_card : (sieve N P hP).support.card = N := by
  change ((Finset.Icc 1 N).image (fun n => n * (n + 2))).card = N
  rw [Finset.card_image_of_injective _ twinProd_injective, Nat.card_Icc]; omega

/-- The sieve's weighted count of `support` elements divisible by `d` equals
the honest progression count `#{n ∈ [1,N] : d ∣ n(n+2)}`. -/
lemma sieve_multSum (d : ℕ) :
    (sieve N P hP).multSum d
      = (((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) := by
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      if d ∣ m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => twinProd_injective h),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The sieve's remainder equals the M2 remainder `rem d N` (so
`progression_count_bound`/N2.4 bounds it). -/
lemma sieve_rem (d : ℕ) : (sieve N P hP).rem d = rem d N := by
  rw [BoundingSieve.rem, sieve_multSum, sieve_totalMass, sieve_nu, rem, nu_apply]
  ring

/-- N3.1: at a prime, `selbergTerms p = ν(p)/(1−ν(p))`
(since `p.primeFactors = {p}`). -/
lemma selbergTerms_prime (p : ℕ) (hp : p.Prime) :
    (sieve N P hP).selbergTerms p = nu p * (1 - nu p)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply, sieve_nu, hp.primeFactors, Finset.prod_singleton]

/-- N3.1 (`p = 2`): `selbergTerms 2 = 1` (`ν(2) = 1/2`). -/
lemma selbergTerms_two : (sieve N P hP).selbergTerms 2 = 1 := by
  rw [selbergTerms_prime 2 (by norm_num), nu_apply, rho_two]
  norm_num

/-- N3.1 (odd prime): `selbergTerms p ≥ 2/p` (`ν(p) = 2/p`, so
`selbergTerms p = 2/(p−2) ≥ 2/p`). -/
lemma selbergTerms_odd_prime_ge (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (2 : ℝ) / p ≤ (sieve N P hP).selbergTerms p := by
  rw [selbergTerms_prime p hp, nu_apply, rho_odd_prime hp hodd]
  push_cast
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hodd
    · rcases h with ⟨k, hk⟩; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast h3
  have hp0 : (0 : ℝ) < p := by linarith
  have hnum : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [show (1 : ℝ) - 2 / p = (p - 2) / p by field_simp, inv_div,
    show (2 : ℝ) / p * (p / (p - 2)) = 2 / (p - 2) by field_simp]
  gcongr
  linarith

/-- The sifted sum counts `n ∈ [1,N]` whose `n(n+2)` is coprime to `P`. -/
lemma sieve_siftedSum :
    (sieve N P hP).siftedSum
      = (((Finset.Icc 1 N).filter (fun n => Nat.Coprime P (n * (n + 2)))).card : ℝ) := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      if Nat.Coprime P m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => twinProd_injective h),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A twin prime `p` (both `p`, `p+2` prime) with neither dividing `P` yields
`p(p+2)` coprime to `P` — the only primes dividing `p(p+2)` are `p` and `p+2`. -/
lemma coprime_twinProd {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hd1 : ¬ p ∣ P) (hd2 : ¬ (p + 2) ∣ P) : Nat.Coprime P (p * (p + 2)) :=
  Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hd1).symm
    (hp2.coprime_iff_not_dvd.mpr hd2).symm

/-- N5.1: if every prime factor of `P` is `≤ z`, every twin-prime leader
`p ∈ (z, N]` lands in the coprime-to-`P` set (so is counted by `siftedSum`). -/
lemma twin_subset_coprime {z : ℕ} (hPz : ∀ q, q.Prime → q ∣ P → q ≤ z) :
    (Finset.Icc 1 N).filter (fun n => z < n ∧ n.Prime ∧ (n + 2).Prime) ⊆
      (Finset.Icc 1 N).filter (fun n => Nat.Coprime P (n * (n + 2))) := by
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  obtain ⟨hmem, hz, hp, hp2⟩ := hn
  refine ⟨hmem, coprime_twinProd hp hp2 ?_ ?_⟩
  · intro hdvd; exact absurd (hPz n hp hdvd) (by omega)
  · intro hdvd; exact absurd (hPz (n + 2) hp2 hdvd) (by omega)

/-- N5.1 (counting form): the number of twin-prime leaders in `(z, N]` is at
most `siftedSum`, when all prime factors of `P` are `≤ z`. -/
lemma twin_count_le_siftedSum {z : ℕ} (hPz : ∀ q, q.Prime → q ∣ P → q ≤ z) :
    (((Finset.Icc 1 N).filter (fun n => z < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ)
      ≤ (sieve N P hP).siftedSum := by
  rw [sieve_siftedSum]
  exact_mod_cast Finset.card_le_card (twin_subset_coprime hPz)

/-- Exact value (not just the `selbergTerms_odd_prime_ge` lower bound):
`selbergTerms p = 2/(p-2)` for odd prime `p`. -/
lemma selbergTerms_odd_prime_eq (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (sieve N P hP).selbergTerms p = 2 / ((p:ℝ) - 2) := by
  rw [selbergTerms_prime p hp, nu_apply, rho_odd_prime hp hodd]
  push_cast
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hodd
    · rcases h with ⟨k, hk⟩; omega
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast h3
  rw [show (1:ℝ) - 2/p = (p-2)/p by field_simp, inv_div]
  field_simp

/-- `selbergTerms` decomposes as a product over prime factors, for any
squarefree `d ∣ P` (immediate from `ArithmeticFunction.IsMultiplicative.prod_primeFactors`,
applied to `selbergTerms` instead of `nu`). -/
lemma prod_primeFactors_selbergTerms {d : ℕ} (hd : d ∣ P) :
    ∏ p ∈ d.primeFactors, (sieve N P hP).selbergTerms p = (sieve N P hP).selbergTerms d :=
  (sieve N P hP).selbergTerms_isMultiplicative.prod_primeFactors
    (Squarefree.squarefree_of_dvd hd hP)

/-- For `ℓ` ODD and SQUAREFREE with `ℓ ∣ P`: `selbergTerms ℓ` equals the bare
twin formula `Salt.M3Expansion.gTwin ℓ` EXACTLY. -/
lemma selbergTerms_eq_gTwin {ℓ : ℕ} (hℓP : ℓ ∣ P) (hℓodd : Odd ℓ) (_hℓsq : Squarefree ℓ) :
    (sieve N P hP).selbergTerms ℓ = Salt.M3Expansion.gTwin ℓ := by
  rw [← prod_primeFactors_selbergTerms hℓP, Salt.M3Expansion.gTwin]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpodd : p ≠ 2 := by
    rintro rfl
    have hpdvd : (2:ℕ) ∣ ℓ := Nat.dvd_of_mem_primeFactors hp
    exact (Nat.not_even_iff_odd.mpr hℓodd) (even_iff_two_dvd.mpr hpdvd)
  exact selbergTerms_odd_prime_eq p hpp hpodd

end Salt.TwinSieve
