/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.SelbergPort
import Salt.BrunLower.MertensWindow
import Salt.Chen.MertensPNT
import Salt.Maynard.Mertens
import Salt.TwinBar.LambdaRate

/-!
# TypicalDensity — the sieve density of the set `S` (S8 / MR-CORE, node A4a)

Matomäki–Radziwiłł's Lemma 2.2 / the "standard sieve bound" of MR §2, p.6
(source `docs/sources/1501.04585v4.pdf`, and the density line consumed on p.31,
`Σ_{X≤n≤2X, n∉S} 1 ≤ (1+1/100) X Σ_j ∏_{P_j≤p≤Q_j}(1-1/p) ≤ (1+1/100) X Σ_j log P_j/log Q_j`):

  `#{n ∈ (X, 2X] : n has no prime factor in [P, Q]} ≪ (log P / log Q) · X`.

This is the density of the complement of one sieve band `[P, Q]`; the full set
`S` (a prime factor in *every* band `[P_j, Q_j]`) then follows by a union bound
over `j`, which A4 (`ThmA1.lean`) performs.

**Route: Brun-adapt (the freeze's primary directive).**  We instantiate the
*general* Selberg Λ²-sieve fundamental theorem `Salt.SelbergPort.selberg_bound_simple`
(mathlib's `SelbergSieve` layer, not the twin-specific corpus pipeline):

* `support = (X, 2X]`, `weights ≡ 1`, `totalMass = X`;
* `prodPrimes = ∏_{P≤p≤Q} p` (the radical of the band, squarefree);
* `nu d = 1/d` (the density of multiples of `d`), so `selbergTerms ℓ = 1/φ(ℓ)`;
* `level = ⌊√X⌋`.

The sieve gives `U ≤ X/G + Σ_{d∣P, d≤√X} 3^{ω d}|R_d|` with `G` the Selberg
bounding sum and `|R_d| ≤ 1` (a per-divisor interval count is off from `X/d` by
`< 1`).  The **error** is `≪ √X (log X)²`, negligible; the **main term** `X/G`
needs a lower bound `G ≫ log Q/log P` — the freeze's *Rankin fallback* ("any
positive power serves"): a Rankin tail bound shows the truncated bounding sum
captures a positive proportion of the full Euler product `∏(1-1/p)^{-1} ≍ log Q/log P`.

Source pins (D5): MR arXiv v4 (`1501.04585v4`), §2 p.6 / §9 p.31.
-/

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

namespace Salt.MR

/-! ## §1  The density function `nu` and the prime band -/

/-- The multiplicative density `nu d = 1/d`: the proportion of `(X, 2X]` that are
multiples of `d`.  Fed as the `nu` of the Selberg sieve. -/
noncomputable def nuDens : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else (d : ℝ)⁻¹
  map_zero' := by simp

theorem nuDens_apply {d : ℕ} (hd : d ≠ 0) : nuDens d = (d : ℝ)⁻¹ := by
  simp only [nuDens, ArithmeticFunction.coe_mk, if_neg hd]

theorem nuDens_mult : nuDens.IsMultiplicative := by
  constructor
  · simp [nuDens]
  · intro m n _
    simp only [nuDens, ArithmeticFunction.coe_mk]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]; push_cast; rw [mul_inv]

/-- The primes in the band `[P, Q]`. -/
noncomputable def primeBand (P Q : ℕ) : Finset ℕ := (Finset.Icc P Q).filter Nat.Prime

/-- The radical of the band: the product of all primes in `[P, Q]`. Squarefree. -/
noncomputable def bandProd (P Q : ℕ) : ℕ := ∏ p ∈ primeBand P Q, p

theorem bandProd_squarefree (P Q : ℕ) : Squarefree (bandProd P Q) := by
  unfold bandProd
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [primeBand, Finset.mem_coe, Finset.mem_filter] at hp hq
    have hcop : Nat.gcd p q = 1 := (Nat.coprime_primes hp.2 hq.2).mpr hpq
    intro c hcp hcq
    exact isUnit_of_dvd_one (hcop ▸ Nat.dvd_gcd hcp hcq)
  · intro p hp
    rw [primeBand, Finset.mem_filter] at hp
    exact hp.2.squarefree

theorem bandProd_ne_zero (P Q : ℕ) : bandProd P Q ≠ 0 := (bandProd_squarefree P Q).ne_zero

/-- Membership in the band's radical: for a prime `p`, `p ∣ bandProd P Q` iff
`p` lies in the band. -/
theorem prime_dvd_bandProd_iff {P Q p : ℕ} (hp : p.Prime) :
    p ∣ bandProd P Q ↔ (P ≤ p ∧ p ≤ Q) := by
  unfold bandProd
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hq
    rw [(Nat.prime_dvd_prime_iff_eq hp hq.2).mp hpq]
    exact hq.1
  · intro h
    exact ⟨p, by rw [primeBand, Finset.mem_filter, Finset.mem_Icc]; exact ⟨h, hp⟩, dvd_refl p⟩

theorem nuDens_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < nuDens p := by
  rw [nuDens_apply hp.pos.ne']
  exact inv_pos.mpr (by exact_mod_cast hp.pos)

theorem nuDens_lt_one_of_prime {p : ℕ} (hp : p.Prime) : nuDens p < 1 := by
  rw [nuDens_apply hp.pos.ne']
  rw [inv_lt_one_iff₀]
  right
  exact_mod_cast hp.one_lt

/-! ## §2  The Selberg sieve instance -/

/-- The Selberg sieve for the band-`[P,Q]` density problem on `(X, 2X]`. -/
noncomputable def densSieve (P Q X : ℕ) : SelbergSieve where
  support := Finset.Ioc X (2 * X)
  prodPrimes := bandProd P Q
  prodPrimes_squarefree := bandProd_squarefree P Q
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (X : ℝ)
  nu := nuDens
  nu_mult := nuDens_mult
  nu_pos_of_prime := fun p hp _ => nuDens_pos_of_prime hp
  nu_lt_one_of_prime := fun p hp _ => nuDens_lt_one_of_prime hp
  level := (Nat.sqrt X : ℝ) + 1
  one_le_level := by
    have : (0 : ℝ) ≤ (Nat.sqrt X : ℝ) := by positivity
    linarith

@[simp] theorem densSieve_prodPrimes (P Q X : ℕ) :
    (densSieve P Q X).prodPrimes = bandProd P Q := rfl

@[simp] theorem densSieve_level (P Q X : ℕ) :
    (densSieve P Q X).level = (Nat.sqrt X : ℝ) + 1 := rfl

@[simp] theorem densSieve_totalMass (P Q X : ℕ) :
    (densSieve P Q X).totalMass = (X : ℝ) := rfl

/-- The sifted sum is the density count: the number of `n ∈ (X, 2X]` with no
prime factor in the band. -/
theorem densSieve_siftedSum (P Q X : ℕ) :
    (densSieve P Q X).siftedSum
      = ((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card := by
  rw [BoundingSieve.siftedSum]
  simp only [densSieve]
  rw [Finset.sum_boole]

/-- The remainder of the Selberg sieve is bounded by `1` in absolute value:
a per-divisor interval count `#{n ∈ (X,2X] : d ∣ n}` is within `1` of `X/d`. -/
theorem densSieve_rem_abs_le_one (P Q X d : ℕ) : |(densSieve P Q X).rem d| ≤ 1 := by
  have hmult : (densSieve P Q X).multSum d
      = (((Finset.Ioc X (2 * X)).filter (fun n => d ∣ n)).card : ℝ) := by
    rw [BoundingSieve.multSum]
    simp only [densSieve]
    rw [Finset.sum_boole]
  rw [BoundingSieve.rem, hmult]
  simp only [densSieve_totalMass]
  rcases eq_or_ne d 0 with rfl | hd
  · -- d = 0: no multiples of 0 in (X,2X], and nu 0 · X = 0
    have hemp : ((Finset.Ioc X (2 * X)).filter (fun n => (0:ℕ) ∣ n)) = ∅ :=
      Finset.filter_false_of_mem (by
        intro n hn; simp only [Finset.mem_Ioc] at hn
        simp only [zero_dvd_iff]; omega)
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [show (densSieve P Q X).nu 0 = 0 by simp [densSieve, nuDens]]
    simp
  · -- d ≥ 1: the count is (2X)/d - X/d (nat div), off from X/d by (m₁-m₂)/d, |·|<1
    rw [show (densSieve P Q X).nu d = (d : ℝ)⁻¹ by simp only [densSieve]; exact nuDens_apply hd]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hle : X / d ≤ (2 * X) / d := Nat.div_le_div_right (by omega)
    have hcard : ((Finset.Ioc X (2 * X)).filter (fun n => d ∣ n)).card = (2 * X) / d - X / d := by
      rw [show (Finset.Ioc X (2 * X)).filter (fun n => d ∣ n)
          = (Finset.Ioc 0 (2 * X)).filter (fun n => d ∣ n)
              \ (Finset.Ioc 0 X).filter (fun n => d ∣ n) by
        ext n
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc]
        by_cases hdn : d ∣ n
        · simp only [hdn, and_true]; omega
        · simp [hdn]]
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ (by
        intro n hn; simp only [Finset.mem_Ioc] at hn ⊢; omega))]
      rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
    rw [hcard, Nat.cast_sub hle]
    -- the mod identities: d·(2X/d) + (2X)%d = 2X,  d·(X/d) + X%d = X
    have eb : (d : ℝ) * ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) = X := by
      exact_mod_cast Nat.div_add_mod X d
    have ea : (d : ℝ) * (((2 * X) / d : ℕ) : ℝ) + (((2 * X) % d : ℕ) : ℝ) = 2 * X := by
      exact_mod_cast Nat.div_add_mod (2 * X) d
    have hm1R : ((X % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt X hdpos
    have hm2R : (((2 * X) % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt (2 * X) hdpos
    have hm1R0 : (0 : ℝ) ≤ ((X % d : ℕ) : ℝ) := by positivity
    have hm2R0 : (0 : ℝ) ≤ (((2 * X) % d : ℕ) : ℝ) := by positivity
    -- the count minus X/d equals (m₁ - m₂)/d, of absolute value < 1
    have heq : (((2 * X) / d : ℕ) : ℝ) - ((X / d : ℕ) : ℝ) - (d : ℝ)⁻¹ * X
        = (((X % d : ℕ) : ℝ) - ((2 * X) % d : ℕ)) * (d : ℝ)⁻¹ := by
      field_simp
      nlinarith [ea, eb]
    rw [heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (d:ℝ)⁻¹)]
    rw [show (1 : ℝ) = d * (d:ℝ)⁻¹ from (mul_inv_cancel₀ hdR.ne').symm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [abs_le]; constructor <;> linarith [hm1R, hm2R, hm1R0, hm2R0]

/-! ## §3  The Selberg error term is negligible

The Selberg error `Σ_{d∣P, d≤√X} 3^{ω d}|R_d|` is `≤ (√X+1)·∏_{P≤p≤Q}(1+3/p)`
(Rankin exponent 1: `3^{ω d} ≤ (√X/d)·3^{ω d}` for `d ≤ √X`, then the Euler
product over the squarefree band radical). -/

/-- `ω n = #n.primeFactors`. -/
theorem omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- The band radical's prime factors are exactly the band. -/
theorem primeFactors_bandProd (P Q : ℕ) : (bandProd P Q).primeFactors = primeBand P Q := by
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpd, _⟩
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨(prime_dvd_bandProd_iff hp).mp hpd, hp⟩
  · intro hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨hp.2, (prime_dvd_bandProd_iff hp.2).mpr hp.1, bandProd_ne_zero P Q⟩

/-- The multiplicative Rankin weight `w₃ d = 3^{ω d}/d`. -/
noncomputable def w3 : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else (3 : ℝ) ^ (ω d) / d
  map_zero' := by simp

theorem w3_apply {d : ℕ} (hd : d ≠ 0) : w3 d = (3 : ℝ) ^ (ω d) / d := by
  simp only [w3, ArithmeticFunction.coe_mk, if_neg hd]

theorem w3_prime {p : ℕ} (hp : p.Prime) : w3 p = 3 / p := by
  rw [w3_apply hp.pos.ne', omega_eq_card, hp.primeFactors, Finset.card_singleton, pow_one]

theorem w3_mult : w3.IsMultiplicative := by
  refine ⟨by simp [w3], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [w3]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [w3]
  rw [w3_apply (Nat.mul_ne_zero hm hn), w3_apply hm, w3_apply hn]
  have ho : ω (m * n) = ω m + ω n := by
    rw [omega_eq_card, omega_eq_card, omega_eq_card, Nat.primeFactors_mul hm hn,
      Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn)]
  rw [ho, pow_add]
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast; field_simp

/-- **§3 (Stone 1).**  The Selberg error term is `≤ (√X+1)·∏_{P≤p≤Q}(1+3/p)`. -/
theorem densSieve_error_le (P Q X : ℕ) :
    ∑ d ∈ (bandProd P Q).divisors,
        (if (d : ℝ) ≤ (Nat.sqrt X : ℝ) + 1 then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d|
          else 0)
      ≤ ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ)) := by
  set L : ℝ := (Nat.sqrt X : ℝ) + 1 with hL
  have hLpos : (0 : ℝ) < L := by positivity
  -- Step 1: bound each term by `L · w₃ d`
  have hstep : ∀ d ∈ (bandProd P Q).divisors,
      (if (d : ℝ) ≤ L then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d| else 0)
        ≤ L * w3 d := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [w3_apply hd0]
    split_ifs with hcond
    · calc (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d|
          ≤ (3 : ℝ) ^ (ω d) * 1 :=
            mul_le_mul_of_nonneg_left (densSieve_rem_abs_le_one P Q X d) (by positivity)
        _ = (3 : ℝ) ^ (ω d) := by ring
        _ ≤ L * ((3 : ℝ) ^ (ω d) / d) := by
            rw [mul_div_assoc', le_div_iff₀ hdR]
            have : (d : ℝ) ≤ L := hcond
            nlinarith [pow_pos (show (0:ℝ) < 3 by norm_num) (ω d)]
    · positivity
  calc ∑ d ∈ (bandProd P Q).divisors,
          (if (d : ℝ) ≤ L then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d| else 0)
      ≤ ∑ d ∈ (bandProd P Q).divisors, L * w3 d := Finset.sum_le_sum hstep
    _ = L * ∑ d ∈ (bandProd P Q).divisors, w3 d := by rw [Finset.mul_sum]
    _ = L * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ)) := by
        rw [← w3_mult.prodPrimeFactors_one_add_of_squarefree (bandProd_squarefree P Q),
          primeFactors_bandProd]
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        rw [primeBand, Finset.mem_filter] at hp
        rw [w3_prime hp.2]

/-- The band Euler product `∏_{P≤p≤Q}(1+3/p)` is `≤ exp(3(log(log(Q+1)/log P)+19/log P))`,
via `1+x ≤ exp x` and the windowed Mertens bound on `Σ 1/p`. -/
theorem prod_one_add_three_div_le {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ Real.exp (3 * (Real.log (Real.log (Q + 1) / Real.log P) + 19 / Real.log P)) := by
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hwz : (P : ℝ) ≤ (Q : ℝ) + 1 := by linarith
  have hsum : ∑ p ∈ primeBand P Q, (1 : ℝ) / p
      ≤ Real.log (Real.log (Q + 1) / Real.log P) + 19 / Real.log P := by
    apply Salt.BrunLower.sum_inv_le_of_prime_window hPR hwz
    intro p hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
    refine ⟨hp.2, by exact_mod_cast hp.1.1, ?_⟩
    have : (p : ℝ) ≤ Q := by exact_mod_cast hp.1.2
    linarith
  calc ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ ∏ p ∈ primeBand P Q, Real.exp (3 / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p _; linarith [Real.add_one_le_exp (3 / (p : ℝ))]
    _ = Real.exp (∑ p ∈ primeBand P Q, 3 / (p : ℝ)) := (Real.exp_sum _ _).symm
    _ = Real.exp (3 * ∑ p ∈ primeBand P Q, 1 / (p : ℝ)) := by
        rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ Real.exp (3 * (Real.log (Real.log (Q + 1) / Real.log P) + 19 / Real.log P)) := by
        apply Real.exp_le_exp.mpr
        linarith [mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 3)]

/-! ## §4  The Selberg bounding sum lower bound

`selbergTerms ℓ = ∏_{p∣ℓ} 1/(p-1)` for `ℓ ∣ bandProd`; the full sum
`Σ_{ℓ∣bandProd} selbergTerms ℓ = ∏_{P≤p≤Q}(1+1/(p-1)) = ∏(1-1/p)⁻¹ ≍ log Q/log P`.
The bounding sum `G` is this full sum truncated to `ℓ² ≤ √X`; a Rankin tail bound
(RESIDUAL, see NOTES) shows the truncation costs at most half. -/

/-- The Selberg term at a prime is `1/(p-1)`. -/
theorem densSieve_selbergTerms_prime (P Q X : ℕ) {p : ℕ} (hp : p.Prime) :
    (densSieve P Q X).selbergTerms p = 1 / ((p : ℝ) - 1) := by
  rw [BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton,
    show (densSieve P Q X).nu p = (p : ℝ)⁻¹ from nuDens_apply hp.pos.ne']
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpm : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  rw [show (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) by field_simp, inv_div]
  field_simp

/-- The full (untruncated) Selberg sum equals the band Euler product `∏(1+1/(p-1))`. -/
theorem densSieve_full_eq (P Q X : ℕ) :
    ∑ ℓ ∈ (bandProd P Q).divisors, (densSieve P Q X).selbergTerms ℓ
      = ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
  rw [← (densSieve P Q X).selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (bandProd_squarefree P Q), primeFactors_bandProd]
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeBand, Finset.mem_filter] at hp
  rw [densSieve_selbergTerms_prime P Q X hp.2]

/-- The band as a Mertens window `[P, Q+1)`. -/
theorem primeBand_eq_window (P Q : ℕ) :
    primeBand P Q = Salt.BrunLower.primesInWindow (P : ℝ) ((Q : ℝ) + 1) := by
  ext p
  rw [primeBand, Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨hP, hQ⟩, hpr⟩
    have hpQ : (p : ℝ) ≤ Q := by exact_mod_cast hQ
    refine ⟨?_, hpr, by exact_mod_cast hP⟩
    rw [Nat.lt_ceil]; linarith
  · rintro ⟨hlt, hpr, hP⟩
    rw [Nat.lt_ceil] at hlt
    have hpQn : p < Q + 1 := by exact_mod_cast hlt
    exact ⟨⟨by exact_mod_cast hP, by omega⟩, hpr⟩

/-- **§4 (Stone E).**  `Full = ∏_{P≤p≤Q}(1+1/(p-1)) ≥ exp(-19/log 2)·(log Q/log P)`,
via `log(1+1/(p-1)) ≥ 1/p` and the windowed Mertens lower bound. -/
theorem densSieve_full_ge {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    Real.exp (-19 / Real.log 2) * (Real.log Q / Real.log P)
      ≤ ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
  have hP2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hP2)
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hQ1 : (P : ℝ) ≤ (Q : ℝ) + 1 := by linarith
  have hprodpos : (0 : ℝ) < ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
    apply Finset.prod_pos; intro p hp
    rw [primeBand, Finset.mem_filter] at hp
    have : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  -- per-prime bound `log(1+1/(p-1)) ≥ 1/p`
  have hlog_ge : ∀ p ∈ primeBand P Q, (1 : ℝ) / p ≤ Real.log (1 + 1 / ((p : ℝ) - 1)) := by
    intro p hp
    rw [primeBand, Finset.mem_filter] at hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have ha : (0 : ℝ) < ((p : ℝ) - 1) / p := by positivity
    have hla : Real.log (((p : ℝ) - 1) / p) ≤ ((p : ℝ) - 1) / p - 1 :=
      Real.log_le_sub_one_of_pos ha
    have heq : (1 : ℝ) + 1 / ((p : ℝ) - 1) = (((p : ℝ) - 1) / p)⁻¹ := by field_simp; ring
    rw [heq, Real.log_inv]
    have hnp : ((p : ℝ) - 1) / p - 1 = -(1 / p) := by field_simp; ring
    linarith [hla, hnp]
  -- windowed Mertens lower bound on Σ 1/p
  have hmert : Real.log (Real.log Q / Real.log P) - 19 / Real.log P
      ≤ ∑ p ∈ primeBand P Q, (1 : ℝ) / p := by
    rw [primeBand_eq_window]
    have hge := Salt.Chen.sum_inv_prime_window_ge hPR hQ1
    have hlogQle : Real.log Q ≤ Real.log ((Q : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hmono : Real.log (Real.log Q / Real.log P)
        ≤ Real.log (Real.log ((Q : ℝ) + 1) / Real.log P) :=
      Real.log_le_log (by positivity) (by gcongr)
    linarith [hge, hmono]
  -- `log Full = Σ log(1+1/(p-1)) ≥ Σ 1/p ≥ log(logQ/logP) - 19/logP`
  have hB : Real.log (Real.log Q / Real.log P) - 19 / Real.log P
      ≤ Real.log (∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1))) := by
    rw [Real.log_prod (fun p hp => by
      rw [primeBand, Finset.mem_filter] at hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
      have hpm2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 1) := by positivity
      exact this.ne')]
    exact le_trans hmert (Finset.sum_le_sum hlog_ge)
  -- assemble
  rw [← Real.exp_log hprodpos]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2P : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hPR
  have hexp : Real.exp (-19 / Real.log 2) ≤ Real.exp (-19 / Real.log P) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  calc Real.exp (-19 / Real.log 2) * (Real.log Q / Real.log P)
      ≤ Real.exp (-19 / Real.log P) * (Real.log Q / Real.log P) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = Real.exp (Real.log (Real.log Q / Real.log P) - 19 / Real.log P) := by
        have hne : (-19 : ℝ) / Real.log P = -(19 / Real.log P) := by ring
        rw [Real.exp_sub, Real.exp_log (by positivity : (0:ℝ) < Real.log Q / Real.log P),
          hne, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log (∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)))) :=
        Real.exp_le_exp.mpr hB

/-! ## §5  Assembly: the typical-density bound (conditional on the bounding-sum lower bound)

`count = siftedSum ≤ X/G + error`.  Given `G ≥ c₄·(log Q/log P)` and the (large-`X`)
hypothesis that the error is below the main scale, `count ≤ C·(log P/log Q)·X`. -/

/-- **§5 (conditional exit stone).**  The MR Lemma-2.2 density bound, modulo the Selberg
bounding-sum lower bound `hG` (discharged unconditionally by `bandProd_selbergBoundingSum_ge`
below when available) and a large-`X` guard `herr` folding the negligible sieve error into the
main term. -/
theorem typical_density_le_of_boundingSum
    {c₄ : ℝ} (hc₄ : 0 < c₄)
    (hG : ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q → Real.log Q ≤ Real.sqrt (Real.log X) →
        c₄ * (Real.log Q / Real.log P) ≤ Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q → Real.log Q ≤ Real.sqrt (Real.log X) →
        ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log P / Real.log Q) →
        (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
          ≤ C * (Real.log P / Real.log Q) * X := by
  refine ⟨1 / c₄ + 1, by positivity, ?_⟩
  intro P Q X hP hPQ hreg herr
  have hP2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hP2)
  have hXnn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hGpos : 0 < Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) :=
    Salt.SelbergPort.selbergBoundingSum_pos _
  -- the Selberg fundamental bound, with siftedSum rewritten to the count
  have hsel := Salt.SelbergPort.selberg_bound_simple (densSieve P Q X)
  rw [densSieve_siftedSum] at hsel
  simp only [densSieve_totalMass, densSieve_level, densSieve_prodPrimes] at hsel
  -- main term: X/G ≤ (1/c₄)(logP/logQ)X
  have hmain : (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
      ≤ (1 / c₄) * (Real.log P / Real.log Q) * X := by
    rw [div_le_iff₀ hGpos]
    have hcoef : (0 : ℝ) ≤ 1 / c₄ * (Real.log P / Real.log Q) * X := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hG P Q X hP hPQ hreg) hcoef
    have hid : 1 / c₄ * (Real.log P / Real.log Q) * X * (c₄ * (Real.log Q / Real.log P)) = X := by
      field_simp
    linarith [hstep, hid]
  -- error term: ≤ (√X+1)∏(1+3/p) ≤ X(logP/logQ)  [by herr]
  calc (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
      ≤ (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
          + ∑ d ∈ (bandProd P Q).divisors,
              (if (d : ℝ) ≤ (Nat.sqrt X : ℝ) + 1 then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d|
                else 0) := hsel
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X
          + ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ)) := by
        gcongr
        exact densSieve_error_le P Q X
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X + (X : ℝ) * (Real.log P / Real.log Q) := by
        linarith [herr]
    _ = (1 / c₄ + 1) * (Real.log P / Real.log Q) * X := by ring

/-! ## §6  The Rankin tail bound: the truncation costs at most half

`G = Full − Tail`.  On the tail `ℓ² > √X+1` we insert the Rankin weight
`(√X+1)^{-a/2}·ℓ^a ≥ 1` at exponent `a = 1/log Q`, evaluate the Rankin-weighted
Euler product `∏(1 + p^a/(p-1)) ≤ e^{24}·Full` (via `e^x - 1 ≤ x e^x` and the
Mertens bound on `Σ log p/p`), and the regime `log Q ≤ √log X` gives
`(√X+1)^{-a/2} ≤ exp(-√log X/4)`; with `√log X ≥ 100` the tail is `≤ Full/2`. -/

/-- The Rankin-weighted Selberg term `ℓ^a · g(ℓ)` as an arithmetic function. -/
noncomputable def rankinWt (P Q X : ℕ) (a : ℝ) : ArithmeticFunction ℝ where
  toFun ℓ := (ℓ : ℝ) ^ a * (densSieve P Q X).selbergTerms ℓ
  map_zero' := by simp

theorem rankinWt_apply (P Q X : ℕ) (a : ℝ) (ℓ : ℕ) :
    rankinWt P Q X a ℓ = (ℓ : ℝ) ^ a * (densSieve P Q X).selbergTerms ℓ := by
  simp only [rankinWt, ArithmeticFunction.coe_mk]

theorem rankinWt_mult (P Q X : ℕ) (a : ℝ) : (rankinWt P Q X a).IsMultiplicative := by
  constructor
  · rw [rankinWt_apply, Nat.cast_one, Real.one_rpow,
      (densSieve P Q X).selbergTerms_isMultiplicative.map_one, mul_one]
  · intro m n hmn
    rw [rankinWt_apply, rankinWt_apply, rankinWt_apply, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      (densSieve P Q X).selbergTerms_isMultiplicative.map_mul_of_coprime hmn]
    ring

theorem rankinWt_prime (P Q X : ℕ) (a : ℝ) {p : ℕ} (hp : p.Prime) :
    rankinWt P Q X a p = (p : ℝ) ^ a / ((p : ℝ) - 1) := by
  rw [rankinWt_apply, densSieve_selbergTerms_prime P Q X hp, mul_one_div]

/-- The Rankin-weighted Euler product over the band radical. -/
theorem densSieve_rankin_sum_eq (P Q X : ℕ) (a : ℝ) :
    ∑ ℓ ∈ (bandProd P Q).divisors, rankinWt P Q X a ℓ
      = ∏ p ∈ primeBand P Q, (1 + (p : ℝ) ^ a / ((p : ℝ) - 1)) := by
  rw [← (rankinWt_mult P Q X a).prodPrimeFactors_one_add_of_squarefree
      (bandProd_squarefree P Q), primeFactors_bandProd]
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeBand, Finset.mem_filter] at hp
  rw [rankinWt_prime P Q X a hp.2]

/-- The split `Full = G + Tail` of the untruncated Selberg sum. -/
theorem densSieve_boundingSum_split (P Q X : ℕ) :
    ∑ ℓ ∈ (bandProd P Q).divisors, (densSieve P Q X).selbergTerms ℓ
      = Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
        + ∑ ℓ ∈ (bandProd P Q).divisors,
            (if ((ℓ : ℝ) ^ 2 ≤ (Nat.sqrt X : ℝ) + 1) then 0
              else (densSieve P Q X).selbergTerms ℓ) := by
  classical
  rw [Salt.SelbergPort.selbergBoundingSum]
  simp only [densSieve_prodPrimes, densSieve_level]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _
  split_ifs <;> ring

/-- The per-prime Rankin-vs-Mertens sum bound: `Σ_{p∈band} (p^a - 1)/p ≤ 24`
at `a = 1/log Q`, via `e^x - 1 ≤ x e^x ≤ e x` for `x = a log p ∈ [0,1]` and the
Mertens bound `Σ_{p≤Q} log p/p ≤ log Q + log 4 + 4`. -/
theorem densSieve_rankin_exponent_sum_le {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ primeBand P Q, ((p : ℝ) ^ (1 / Real.log Q) - 1) / p ≤ 24 := by
  have hQ2 : 2 ≤ Q := hP.trans hPQ
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  set a : ℝ := 1 / Real.log Q with ha
  have ha0 : 0 < a := by positivity
  -- pointwise: (p^a - 1)/p ≤ e·a·(log p/p)
  have hpt : ∀ p ∈ primeBand P Q,
      ((p : ℝ) ^ a - 1) / p ≤ Real.exp 1 * a * (Real.log p / p) := by
    intro p hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpQ : (p : ℝ) ≤ Q := by exact_mod_cast hp.1.2
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    set x : ℝ := a * Real.log p with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx, ha, div_mul_eq_mul_div, one_mul, div_le_one hlogQ]
      exact Real.log_le_log hp0 hpQ
    have hpa : (p : ℝ) ^ a = Real.exp x := by
      rw [Real.rpow_def_of_pos hp0, hx, mul_comm]
    have hxe : (1 - x) * Real.exp x ≤ 1 := by
      have h1 := Real.add_one_le_exp (-x)
      have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x]
    have hex : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
    have hnum : (p : ℝ) ^ a - 1 ≤ Real.exp 1 * a * Real.log p := by
      rw [hpa]
      have hstep1 : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith [hxe]
      have hstep2 : x * Real.exp x ≤ x * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hex hx0
      calc Real.exp x - 1 ≤ x * Real.exp x := hstep1
        _ ≤ x * Real.exp 1 := hstep2
        _ = Real.exp 1 * a * Real.log p := by rw [hx]; ring
    rw [show Real.exp 1 * a * (Real.log p / p) = (Real.exp 1 * a * Real.log p) / p by ring]
    exact div_le_div_of_nonneg_right hnum hp0.le
  -- the Mertens majorant
  have hsum1 : ∑ p ∈ primeBand P Q, Real.log p / p
      ≤ Real.log Q + (Real.log 4 + 4) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (Salt.Maynard.sum_log_div_prime_le (by omega : 1 ≤ Q))
    · intro p hp
      rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      rw [Finset.mem_filter, Finset.mem_range] at hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
      have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
      positivity
  -- the numeric cap: e·a·(log Q + log 4 + 4) ≤ 24
  have hS : Real.exp 1 * a * (Real.log Q + (Real.log 4 + 4)) ≤ 24 := by
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2pos : (0 : ℝ) < Real.log 2 := by linarith
    have hlog2Q : Real.log 2 ≤ Real.log Q :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hQ2)
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have hexpand : Real.exp 1 * a * (Real.log Q + (Real.log 4 + 4))
        = Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log Q) := by
      rw [ha]; field_simp
    rw [hexpand, hlog4]
    have hdivle : (2 * Real.log 2 + 4) / Real.log Q ≤ (2 * Real.log 2 + 4) / Real.log 2 := by
      apply div_le_div_of_nonneg_left (by linarith) hl2pos hlog2Q
    have hstep : (2 * Real.log 2 + 4) / Real.log 2 ≤ 7.8 := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have hD : 1 + (2 * Real.log 2 + 4) / Real.log Q ≤ 8.8 := by linarith
    calc Real.exp 1 * (1 + (2 * Real.log 2 + 4) / Real.log Q)
        ≤ Real.exp 1 * 8.8 := by nlinarith [Real.exp_pos 1]
      _ ≤ 2.7182818286 * 8.8 := by nlinarith
      _ ≤ 24 := by norm_num
  calc ∑ p ∈ primeBand P Q, ((p : ℝ) ^ a - 1) / p
      ≤ ∑ p ∈ primeBand P Q, Real.exp 1 * a * (Real.log p / p) :=
        Finset.sum_le_sum hpt
    _ = Real.exp 1 * a * ∑ p ∈ primeBand P Q, Real.log p / p := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * a * (Real.log Q + (Real.log 4 + 4)) := by
        apply mul_le_mul_of_nonneg_left hsum1 (by positivity)
    _ ≤ 24 := hS

/-- **The Rankin tail bound.**  ⟦R3b — THE RELAXED REGULARITY GATE⟧ under
`100·log Q ≤ log X` the tail of the Selberg bounding sum beyond the truncation
`ℓ² ≤ √X+1` is at most `exp(24 − (1/4)·log X/log Q)` times the full band Euler product.

Against the landed form (`log Q ≤ √log X`, `√log X ≥ 100`, tail `exp(24 − √log X/4)`) this
is a STRICT WEAKENING of the hypothesis — the old pair gives `100 log Q ≤ √logX·√logX =
log X` — and the exponent is the one the proof always produced: the `√log X` step was a
LOSSY specialization of `log X/(4 log Q)`, discarded here. -/
theorem densSieve_tail_le {P Q X : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hgate : 100 * Real.log Q ≤ Real.log X) :
    ∑ ℓ ∈ (bandProd P Q).divisors,
        (if ((ℓ : ℝ) ^ 2 ≤ (Nat.sqrt X : ℝ) + 1) then 0
          else (densSieve P Q X).selbergTerms ℓ)
      ≤ Real.exp (24 - Real.log X / (4 * Real.log Q))
          * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hQ2 : 2 ≤ Q := hP.trans hPQ
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  set a : ℝ := 1 / Real.log Q with ha
  have ha0 : 0 < a := by positivity
  set lev : ℝ := (Nat.sqrt X : ℝ) + 1 with hlev
  have hcast0 : (0 : ℝ) ≤ (Nat.sqrt X : ℝ) := Nat.cast_nonneg _
  have hlev0 : (0 : ℝ) < lev := by rw [hlev]; linarith
  -- `100 log Q ≤ log X` with `log Q > 0` forces `log X > 0`, hence `X ≥ 2`
  have hlogX0 : 0 < Real.log X := by linarith
  have hX1 : (1 : ℝ) < (X : ℕ) := by
    by_contra hcon
    push Not at hcon
    have : Real.log X ≤ 0 := Real.log_nonpos (by positivity) hcon
    linarith
  -- pointwise Rankin: on the tail, `g ℓ ≤ lev^{-a/2}·ℓ^a·g ℓ`
  have hpoint : ∀ ℓ ∈ (bandProd P Q).divisors,
      (if ((ℓ : ℝ) ^ 2 ≤ lev) then 0 else (densSieve P Q X).selbergTerms ℓ)
        ≤ lev ^ (-(a / 2)) * ((ℓ : ℝ) ^ a * (densSieve P Q X).selbergTerms ℓ) := by
    intro ℓ hℓ
    have hgpos : 0 < (densSieve P Q X).selbergTerms ℓ :=
      BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hℓ)
    have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast Nat.pos_of_mem_divisors hℓ
    have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
    split_ifs with hc
    · have h1 : (0 : ℝ) ≤ lev ^ (-(a / 2)) := Real.rpow_nonneg hlev0.le _
      have h2 : (0 : ℝ) ≤ (ℓ : ℝ) ^ a := Real.rpow_nonneg hℓ0.le _
      positivity
    · push Not at hc
      have hlevpow : 0 < lev ^ (a / 2) := Real.rpow_pos_of_pos hlev0 _
      have h1 : lev ^ (a / 2) ≤ ((ℓ : ℝ) ^ 2) ^ (a / 2) :=
        Real.rpow_le_rpow hlev0.le hc.le (by positivity)
      have h2 : ((ℓ : ℝ) ^ 2) ^ (a / 2) = (ℓ : ℝ) ^ a := by
        rw [← Real.rpow_natCast (ℓ : ℝ) 2, ← Real.rpow_mul hℓ0.le]
        congr 1
        push_cast
        ring
      have h3 : 1 ≤ lev ^ (-(a / 2)) * (ℓ : ℝ) ^ a := by
        rw [Real.rpow_neg hlev0.le, inv_mul_eq_div, le_div_iff₀ hlevpow, one_mul]
        exact h1.trans_eq h2
      calc (densSieve P Q X).selbergTerms ℓ
          = 1 * (densSieve P Q X).selbergTerms ℓ := (one_mul _).symm
        _ ≤ (lev ^ (-(a / 2)) * (ℓ : ℝ) ^ a) * (densSieve P Q X).selbergTerms ℓ :=
            mul_le_mul_of_nonneg_right h3 hgpos.le
        _ = lev ^ (-(a / 2)) * ((ℓ : ℝ) ^ a * (densSieve P Q X).selbergTerms ℓ) := by
            ring
  -- the weighted Euler product is ≤ e^24·Full
  have hEuler : ∑ ℓ ∈ (bandProd P Q).divisors, rankinWt P Q X a ℓ
      ≤ Real.exp 24 * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
    rw [densSieve_rankin_sum_eq]
    have hfac : ∀ p ∈ primeBand P Q,
        1 + (p : ℝ) ^ a / ((p : ℝ) - 1)
          = (1 + 1 / ((p : ℝ) - 1)) * (1 + ((p : ℝ) ^ a - 1) / p) := by
      intro p hp
      rw [primeBand, Finset.mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hp0 : (0 : ℝ) < p := by linarith
      field_simp
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, mul_comm]
    apply mul_le_mul_of_nonneg_right
    · calc ∏ p ∈ primeBand P Q, (1 + ((p : ℝ) ^ a - 1) / p)
          ≤ ∏ p ∈ primeBand P Q, Real.exp (((p : ℝ) ^ a - 1) / p) := by
            apply Finset.prod_le_prod
            · intro p hp
              rw [primeBand, Finset.mem_filter] at hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
              have hp0 : (0 : ℝ) < p := by linarith
              have hpa1 : (1 : ℝ) ≤ (p : ℝ) ^ a := Real.one_le_rpow (by linarith) ha0.le
              positivity
            · intro p _
              linarith [Real.add_one_le_exp (((p : ℝ) ^ a - 1) / p)]
        _ = Real.exp (∑ p ∈ primeBand P Q, ((p : ℝ) ^ a - 1) / p) :=
            (Real.exp_sum _ _).symm
        _ ≤ Real.exp 24 :=
            Real.exp_le_exp.mpr (densSieve_rankin_exponent_sum_le hP hPQ)
    · apply Finset.prod_nonneg
      intro p hp
      rw [primeBand, Finset.mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
  -- the level decay: `lev^{-a/2} ≤ exp(-(log X)/(4 log Q))`
  have hlevX : Real.log X / (4 * Real.log Q) ≤ (a / 2) * Real.log lev := by
    have hlev_gt : Real.sqrt (X : ℝ) < lev := by
      rw [Real.sqrt_lt' hlev0]
      have h := Nat.lt_succ_sqrt' X
      calc (X : ℝ) < ((Nat.sqrt X + 1) ^ 2 : ℕ) := by exact_mod_cast h
        _ = lev ^ 2 := by rw [hlev]; push_cast; ring
    have hsqrt0 : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hloglev : Real.log X / 2 ≤ Real.log lev := by
      rw [← Real.log_sqrt (by linarith : (0:ℝ) ≤ (X:ℝ))]
      exact Real.log_le_log hsqrt0 hlev_gt.le
    rw [ha, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.log Q)]
    have hgoal : (1 / Real.log Q / 2) * Real.log lev * (4 * Real.log Q)
        = 2 * Real.log lev := by field_simp; ring
    rw [hgoal]
    linarith [hloglev]
  have hlevle : lev ^ (-(a / 2)) ≤ Real.exp (-(Real.log X / (4 * Real.log Q))) := by
    rw [Real.rpow_def_of_pos hlev0]
    apply Real.exp_le_exp.mpr
    nlinarith [hlevX]
  -- assemble
  have hsumnn : 0 ≤ ∑ ℓ ∈ (bandProd P Q).divisors, rankinWt P Q X a ℓ := by
    apply Finset.sum_nonneg
    intro ℓ hℓ
    rw [rankinWt_apply]
    have hg : 0 < (densSieve P Q X).selbergTerms ℓ :=
      BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hℓ)
    have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
    have := Real.rpow_nonneg hℓ0 a
    positivity
  calc ∑ ℓ ∈ (bandProd P Q).divisors,
        (if ((ℓ : ℝ) ^ 2 ≤ lev) then 0 else (densSieve P Q X).selbergTerms ℓ)
      ≤ ∑ ℓ ∈ (bandProd P Q).divisors,
          lev ^ (-(a / 2)) * ((ℓ : ℝ) ^ a * (densSieve P Q X).selbergTerms ℓ) :=
        Finset.sum_le_sum hpoint
    _ = lev ^ (-(a / 2)) * ∑ ℓ ∈ (bandProd P Q).divisors, rankinWt P Q X a ℓ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ _
        rw [rankinWt_apply]
    _ ≤ Real.exp (-(Real.log X / (4 * Real.log Q)))
          * (Real.exp 24 * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1))) := by
        apply mul_le_mul hlevle hEuler hsumnn (Real.exp_nonneg _)
    _ = Real.exp (24 - Real.log X / (4 * Real.log Q))
          * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf

/-- The full band Euler product is positive. -/
theorem densSieve_full_pos (P Q : ℕ) :
    0 < ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
  apply Finset.prod_pos
  intro p hp
  rw [primeBand, Finset.mem_filter] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

/-- **The truncation costs at most half.**  `G ≥ (1/2)·Full` in the regime. -/
theorem densSieve_boundingSum_ge_half {P Q X : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hgate : 100 * Real.log Q ≤ Real.log X) :
    (1 / 2) * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1))
      ≤ Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) := by
  have hQ2 : 2 ≤ Q := hP.trans hPQ
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  have hsplit := densSieve_boundingSum_split P Q X
  rw [densSieve_full_eq P Q X] at hsplit
  have htail := densSieve_tail_le hP hPQ hgate
  have hFullpos := densSieve_full_pos P Q
  -- `exp(24 - logX/(4 logQ)) ≤ exp(-1) ≤ 1/2` — the gate is `logX/(4 logQ) ≥ 25`
  have hexphalf : Real.exp (24 - Real.log X / (4 * Real.log Q)) ≤ 1 / 2 := by
    have h25 : (25 : ℝ) ≤ Real.log X / (4 * Real.log Q) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.log Q)]
      linarith
    have h1 : (24 : ℝ) - Real.log X / (4 * Real.log Q) ≤ -1 := by linarith
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    calc Real.exp (24 - Real.log X / (4 * Real.log Q))
        ≤ Real.exp (-1) := Real.exp_le_exp.mpr h1
      _ = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) h2
  have htail2 : ∑ ℓ ∈ (bandProd P Q).divisors,
      (if ((ℓ : ℝ) ^ 2 ≤ (Nat.sqrt X : ℝ) + 1) then 0
        else (densSieve P Q X).selbergTerms ℓ)
      ≤ (1 / 2) * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) :=
    htail.trans (mul_le_mul_of_nonneg_right hexphalf hFullpos.le)
  linarith [hsplit, htail2]

/-- **§4 exit: the Selberg bounding-sum lower bound** — discharges the `hG`
hypothesis of `typical_density_le_of_boundingSum` with
`c₄ = exp(-19/log 2)/2`. -/
theorem densSieve_boundingSum_ge {P Q X : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hgate : 100 * Real.log Q ≤ Real.log X) :
    (Real.exp (-19 / Real.log 2) / 2) * (Real.log Q / Real.log P)
      ≤ Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) := by
  have h1 := densSieve_full_ge hP hPQ
  have h2 := densSieve_boundingSum_ge_half hP hPQ hgate
  calc (Real.exp (-19 / Real.log 2) / 2) * (Real.log Q / Real.log P)
      = (1 / 2) * (Real.exp (-19 / Real.log 2) * (Real.log Q / Real.log P)) := by
        ring
    _ ≤ (1 / 2) * ∏ p ∈ primeBand P Q, (1 + 1 / ((p : ℝ) - 1)) := by
        linarith [h1]
    _ ≤ Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) := h2

/-! ## §7  The unconditional exit stone -/

/-- ⟦R3b — THE GATE BRIDGE⟧ MR's landed regularity PAIR (`log Q ≤ √log X` together with
`100 ≤ √log X`) implies the relaxed gate `100·log Q ≤ log X`, so every consumer that still
carries the pair reaches the relaxed stones in one step.  The converse fails (take
`log Q = 1`, `log X = 100`), which is exactly the room R3b buys: at the door band
`[P₈₃, Q₈₃]` the pair is UNAVAILABLE and the relaxed gate is free. -/
theorem densGate_of_sqrt {Q X : ℕ} (hQ : 2 ≤ Q)
    (hreg : Real.log Q ≤ Real.sqrt (Real.log X))
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log X)) :
    100 * Real.log Q ≤ Real.log X := by
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ)
  have hlogX0 : 0 ≤ Real.log X := by
    by_contra hcon
    push Not at hcon
    rw [Real.sqrt_eq_zero'.mpr hcon.le] at hbig
    norm_num at hbig
  have hsq : Real.sqrt (Real.log X) * Real.sqrt (Real.log X) = Real.log X :=
    Real.mul_self_sqrt hlogX0
  nlinarith


/-- **`typical_density_le` — the exit stone (S8/MR-CORE node A4a; MR Lemma 2.2).**
`#{n ∈ (X, 2X] : n has no prime factor in [P, Q]} ≤ C·(log P/log Q)·X`, with an
absolute constant `C`, in MR's regime (`2 ≤ P ≤ Q`, `log Q ≤ √log X` — MR's
`Q₁ ≤ exp(√log X)` — plus the large-`X` guards `√log X ≥ 100` and the explicit
error-domination inequality, both satisfied for all large `X` at fixed band).
Delivers the sharp power `log P/log Q` of the freeze line
`[A4a] Lemma-2.2 ≪ (log P1/log Q1)·X`.  Fully unconditional: the bounding-sum
hypothesis of `typical_density_le_of_boundingSum` is discharged by
`densSieve_boundingSum_ge`. -/
theorem typical_density_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q →
        100 * Real.log Q ≤ Real.log X →
        ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log P / Real.log Q) →
        (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
          ≤ C * (Real.log P / Real.log Q) * X := by
  have hc₄ : (0 : ℝ) < Real.exp (-19 / Real.log 2) / 2 := by positivity
  refine ⟨1 / (Real.exp (-19 / Real.log 2) / 2) + 1, by positivity, ?_⟩
  intro P Q X hP hPQ hgate herr
  set c₄ : ℝ := Real.exp (-19 / Real.log 2) / 2 with hc₄def
  have hP2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hP2)
  have hXnn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hGpos : 0 < Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) :=
    Salt.SelbergPort.selbergBoundingSum_pos _
  have hG := densSieve_boundingSum_ge hP hPQ hgate
  rw [← hc₄def] at hG
  -- the Selberg fundamental bound, with siftedSum rewritten to the count
  have hsel := Salt.SelbergPort.selberg_bound_simple (densSieve P Q X)
  rw [densSieve_siftedSum] at hsel
  simp only [densSieve_totalMass, densSieve_level, densSieve_prodPrimes] at hsel
  -- main term: X/G ≤ (1/c₄)(logP/logQ)X
  have hmain : (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
      ≤ (1 / c₄) * (Real.log P / Real.log Q) * X := by
    rw [div_le_iff₀ hGpos]
    have hcoef : (0 : ℝ) ≤ 1 / c₄ * (Real.log P / Real.log Q) * X := by positivity
    have hstep := mul_le_mul_of_nonneg_left hG hcoef
    have hid : 1 / c₄ * (Real.log P / Real.log Q) * X * (c₄ * (Real.log Q / Real.log P))
        = X := by
      field_simp
    linarith [hstep, hid]
  calc (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
      ≤ (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
          + ∑ d ∈ (bandProd P Q).divisors,
              (if (d : ℝ) ≤ (Nat.sqrt X : ℝ) + 1
                then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d| else 0) := hsel
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X
          + ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ)) := by
        gcongr
        exact densSieve_error_le P Q X
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X + (X : ℝ) * (Real.log P / Real.log Q) := by
        linarith [herr]
    _ = (1 / c₄ + 1) * (Real.log P / Real.log Q) * X := by ring

/-! ## The union over bands — the step this file's own header said lived elsewhere

`typical_density_le` is **one band**.  MR's Lemma 2.2 needs the complement of the FULL typical set
`S` (a prime factor in *every* band `[P_j, Q_j]`, `j ≤ J`), which is a union bound over `j` against
`Σ_j log P_j/log Q_j`, and MR's own schedule makes that sum converge by
`log P_j/log Q_j = (1/j²)·(log P₁/log Q₁)`.

⛔⛔ **THIS FILE'S HEADER SAID THE UNION BOUND WAS PERFORMED BY "A4 (`ThmA1.lean`)". THERE IS NO
`Salt/MR/ThmA1.lean`.** The file does not exist (checked); the only `ThmA1`-shaped module is
`MRTThmA1.lean`, which is a different object and in fact imports THIS file — so it could not have
performed this step without a cycle.  `QUEUE.md`'s wave-1a row was right that this is *"unlanded
regardless of range"*, and the header was the stale document.
⇒ 🔑 ***A POINTER TO A FILE THAT DOES NOT EXIST READS EXACTLY LIKE A DISCHARGED OBLIGATION*** — it
names a location, so the eye stops there.  *Two documents disagreed; the one that turned out stale
was the one physically closest to the code.*

📌 **Reused, not re-derived:** `Σ_{j≤J} 1/j² ≤ 2` is `Salt.TwinBar.sum_inv_sq_Icc_le` — the corpus
carries at least five copies of that inequality across `MR`/`Chen`/`TwinBar`, and this file's
closure had none, so the cheapest reachable one is imported (+1 module, measured).  ⚠️ `MRTThmA1`'s
copy would have been a **cycle**. -/

open Classical in
/-- **The band-union density bound.**  With MR's `1/j²` schedule on the band ratios, the count of
`n ∈ (X, 2X]` missing a prime factor in SOME band is at most `2·C·r·X`, where `r` is the common
scale `log P_j/log Q_j = r/j²` and `C` is `typical_density_le`'s absolute constant.

⭐ **The `2` is `Σ 1/j²`'s bound and is where the schedule pays for itself** — the union over
arbitrarily many bands costs a bounded factor, not a factor `J`.

⛔ Each band's four side conditions are carried per-`j` exactly as the one-band stone states them;
nothing here weakens them, and no `j`-uniformity is assumed beyond the ratio schedule.

⚖️⚖️ **SCOPE — MEASURED AFTER LANDING, AND IT IS A SOCKET.**  **Nothing in the corpus
consumes this yet, and the live route may never need it.**  Every consumer of
`typical_density_le` reaches it at **ONE BLOCK SCALE** — `M4Door.SieveBlockGate` bundles
its gates *"as they reach `m4_sieve_block_mass`, at one block scale `X`"*, presented once
per block.  The union over `j` is what MR's **Lemma 2.2** needs, and Lemma 2.2 is **DELETED
FROM THE RATIFIED PORT WAVES** (`QUEUE.md:582`): with `c_p = 1` in the Liouville case,
`[23, Lemma 2.2, Thm 2.3]` is replaced by `[23, Theorem A.1]`.

⇒ **What is and is not true:** the one-band stone is LIVE (consumed per-block by `M4Door`,
`M4Sieve`, `CgPin`, `ConstantsExposed`); the *union* direction serves the deleted port
target.  So this theorem **closes the gap the wave-1a row named** and **unblocks nothing
measured**.
⇒ 🔑 ***"THE ROW SAYS IT IS UNLANDED" AND "THE ROUTE STILL NEEDS IT" ARE DIFFERENT
CLAIMS, AND A QUEUE ROW OUTLIVES THE DELETION THAT EMPTIED IT.***
*Disclosed at landing rather than left for a census: on tonight's own dead-branch
instrument this name would read as a corpse, and it is a socket — the two are
indistinguishable to a grep, which is exactly why the author must say which.* -/
theorem typical_density_union_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (J X : ℕ) (P Q : ℕ → ℕ) (r : ℝ), 0 ≤ r →
      (∀ j ∈ Finset.Icc 1 J, 2 ≤ P j) →
      (∀ j ∈ Finset.Icc 1 J, P j ≤ Q j) →
      (∀ j ∈ Finset.Icc 1 J, 100 * Real.log (Q j) ≤ Real.log X) →
      (∀ j ∈ Finset.Icc 1 J, ((Nat.sqrt X : ℝ) + 1)
          * ∏ p ∈ primeBand (P j) (Q j), (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log (P j) / Real.log (Q j))) →
      (∀ j ∈ Finset.Icc 1 J, Real.log (P j) / Real.log (Q j) = r / (j : ℝ) ^ 2) →
      (((Finset.Ioc X (2 * X)).filter
          (fun n => ∃ j ∈ Finset.Icc 1 J, (bandProd (P j) (Q j)).Coprime n)).card : ℝ)
        ≤ 2 * C * r * X := by
  classical
  obtain ⟨C, hC, hband⟩ := typical_density_le
  refine ⟨C, hC, ?_⟩
  intro J X P Q r hr hP hPQ hgate herr hratio
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  -- the failing set sits inside the union of the per-band failing sets
  have hsub : (Finset.Ioc X (2 * X)).filter
        (fun n => ∃ j ∈ Finset.Icc 1 J, (bandProd (P j) (Q j)).Coprime n)
      ⊆ (Finset.Icc 1 J).biUnion (fun j =>
          (Finset.Ioc X (2 * X)).filter (fun n => (bandProd (P j) (Q j)).Coprime n)) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hn1, j, hj, hcop⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hn1, hcop⟩⟩
  have hcard : (((Finset.Ioc X (2 * X)).filter
        (fun n => ∃ j ∈ Finset.Icc 1 J, (bandProd (P j) (Q j)).Coprime n)).card : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 J,
          (((Finset.Ioc X (2 * X)).filter
            (fun n => (bandProd (P j) (Q j)).Coprime n)).card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := Finset.Icc 1 J)
      (t := fun j => (Finset.Ioc X (2 * X)).filter (fun n => (bandProd (P j) (Q j)).Coprime n))
    have : ((Finset.Ioc X (2 * X)).filter
        (fun n => ∃ j ∈ Finset.Icc 1 J, (bandProd (P j) (Q j)).Coprime n)).card
        ≤ ∑ j ∈ Finset.Icc 1 J,
            ((Finset.Ioc X (2 * X)).filter (fun n => (bandProd (P j) (Q j)).Coprime n)).card :=
      le_trans h1 h2
    exact_mod_cast this
  refine le_trans hcard ?_
  -- each band by the one-band stone, then the schedule
  have hterm : ∀ j ∈ Finset.Icc 1 J,
      (((Finset.Ioc X (2 * X)).filter
        (fun n => (bandProd (P j) (Q j)).Coprime n)).card : ℝ)
        ≤ C * (r / (j : ℝ) ^ 2) * X := by
    intro j hj
    have := hband (P j) (Q j) X (hP j hj) (hPQ j hj) (hgate j hj) (herr j hj)
    rwa [hratio j hj] at this
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hrw : ∑ j ∈ Finset.Icc 1 J, C * (r / (j : ℝ) ^ 2) * X
      = C * r * (X : ℝ) * ∑ j ∈ Finset.Icc 1 J, (((j : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hrw]
  have hsum : ∑ j ∈ Finset.Icc 1 J, (((j : ℝ)) ^ 2)⁻¹ ≤ 2 :=
    Salt.TwinBar.sum_inv_sq_Icc_le J
  have hcoef : (0 : ℝ) ≤ C * r * (X : ℝ) := by positivity
  calc C * r * (X : ℝ) * ∑ j ∈ Finset.Icc 1 J, (((j : ℝ)) ^ 2)⁻¹
      ≤ C * r * (X : ℝ) * 2 := mul_le_mul_of_nonneg_left hsum hcoef
    _ = 2 * C * r * X := by ring

end Salt.MR
