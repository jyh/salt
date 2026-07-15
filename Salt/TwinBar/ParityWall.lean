/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.LinearSieve
import Salt.TwinBar.LambdaRate

/-!
# The parity wall — the Selberg witness pair (Q6a-1)

Design: `docs/exploration/q6a-design.md` (REVISED post-gate; nodes D1/D2/D3/D5).
This file lands the **Selberg witness pair** `sPlus x` / `sMinus x`: two mathlib
`BoundingSieve` values that agree on every field the sieve's main term consumes
(`prodPrimes`, `nu`, `totalMass`) yet whose sifted outputs differ by the entire
prime mass in `(√x, x]`. It is the concrete carrier of the parity obstruction:
no sieve certificate reading only the shared fields can distinguish them.

The two sieves sift `[1, x]` by the primes `≤ ⌊√x⌋` (GATE CORRECTION 1: the
primorial cutoff is `≤ z`, not `< z`), with the shared integer-sifting density
`ν(d) = 1/d`, shared `totalMass = x`, and Liouville-twisted weights
`1 ± λ(n)`.

## Main results

* `nuDiv` — the density `ν(d) = 1/d`, multiplicative, `0 < ν(p) < 1` on primes.
* `sPlus`, `sMinus` — the witness pair as `BoundingSieve` values.
* `siftedSum_sPlus : (sPlus x).siftedSum = 2` — survivors `{1} ∪ primes(√x, x]`,
  each prime killed by `1 + λ(p) = 0`.
* `siftedSum_sMinus : (sMinus x).siftedSum = 2·(π(x) − π(√x))` — the prime mass.
* `sPlus_multSum` / `sMinus_multSum` — the pointwise remainder identity
  `A_d = ⌊x/d⌋ ± λ(d)·M_λ(⌊x/d⌋)` from total multiplicativity (no coprimality).
* `sPlus_rem_bound` / `sMinus_rem_bound` — `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|`.
* `SieveAgree` (D2) and `sieveAgree_pair` — the pair agrees on the main fields
  and shares any remainder budget both meet.

The analytic discharge `|M_λ(y)| ≤ C·y/(log y)^A` (feeding the `SieveAgree`
budget) is the sibling node's job (`Salt/TwinBar/LambdaRate.lean`, Q6a-3); the
wall assembly is Q6a-2.
-/

open ArithmeticFunction Finset

namespace Salt.TwinBar

/-! ## The sifting density `ν(d) = 1/d` -/

/-- The integer-sifting density `ν(d) = 1/d` (with `ν 0 = 0` via `1/0 = 0`). -/
noncomputable def nuDiv : ArithmeticFunction ℝ :=
  ⟨fun d => 1 / (d : ℝ), by simp⟩

@[simp] lemma nuDiv_apply (d : ℕ) : nuDiv d = 1 / (d : ℝ) := rfl

lemma nuDiv_mult : nuDiv.IsMultiplicative := by
  constructor
  · simp [nuDiv_apply]
  · intro m n _
    simp only [nuDiv_apply]
    push_cast
    rw [one_div_mul_one_div]

lemma nuDiv_pos_of_prime (p : ℕ) (hp : p.Prime) : 0 < nuDiv p := by
  rw [nuDiv_apply]
  have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  positivity

lemma nuDiv_lt_one_of_prime (p : ℕ) (hp : p.Prime) : nuDiv p < 1 := by
  rw [nuDiv_apply, div_lt_one (by exact_mod_cast hp.pos)]
  exact_mod_cast hp.one_lt

/-! ## Liouville-function facts (cast to `ℝ`) -/

/-- `|λ(d)| ≤ 1` as integers. -/
lemma liouville_int_abs_le (d : ℕ) : |(liouville d : ℤ)| ≤ 1 := by
  rcases eq_or_ne d 0 with h | h
  · simp [h]
  · rw [liouville_apply h, abs_pow, abs_neg, abs_one, one_pow]

/-- `λ(p) = -1` for a prime `p`. -/
lemma liouville_int_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.pos.ne', cardFactors_apply_prime hp, pow_one]

/-- `(λ(1) : ℝ) = 1`. -/
lemma liouville_real_one : (liouville 1 : ℝ) = 1 := by
  rw [liouville_apply_one]; norm_num

/-- `(λ(p) : ℝ) = -1` for a prime `p`. -/
lemma liouville_real_prime {p : ℕ} (hp : p.Prime) : (liouville p : ℝ) = -1 := by
  rw [liouville_int_prime hp]; norm_num

/-- `-1 ≤ (λ(n) : ℝ)`. -/
lemma liouville_real_ge (n : ℕ) : (-1 : ℝ) ≤ (liouville n : ℝ) := by
  have h := (abs_le.mp (liouville_int_abs_le n)).1
  exact_mod_cast h

/-- `(λ(n) : ℝ) ≤ 1`. -/
lemma liouville_real_le (n : ℕ) : (liouville n : ℝ) ≤ 1 := by
  have h := (abs_le.mp (liouville_int_abs_le n)).2
  exact_mod_cast h

/-- `|(λ(d) : ℝ)| ≤ 1`. -/
lemma liouville_real_abs_le (d : ℕ) : |(liouville d : ℝ)| ≤ 1 := by
  have h : |(liouville d : ℤ)| ≤ 1 := liouville_int_abs_le d
  calc |(liouville d : ℝ)| = ((|liouville d| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
    _ = 1 := by norm_num

/-! ## The primorial is squarefree -/

/-- A finite product of distinct primes is squarefree. -/
lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
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

/-- The primorial `∏_{p ≤ n} p` is squarefree. -/
lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) :=
  prod_primes_squarefree (fun _p hp => (Finset.mem_filter.mp hp).2)

/-! ## The witness pair -/

-- `Mlambda` is owned by `Salt.TwinBar.LambdaRate` (the Q6a-3 bridge file); the
-- byte-identical local definition that briefly lived here was dropped at the
-- Q6a-3 merge.

/-- The upper witness `s₊`: sifts `[1, x]` by the primes `≤ ⌊√x⌋`, density `1/d`,
weights `1 + λ(n)`, total mass `x`. -/
noncomputable def sPlus (x : ℕ) : BoundingSieve where
  support := Finset.Icc 1 x
  prodPrimes := primorial (Nat.sqrt x)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun n => 1 + (liouville n : ℝ)
  weights_nonneg := fun n => by have := liouville_real_ge n; linarith
  totalMass := (x : ℝ)
  nu := nuDiv
  nu_mult := nuDiv_mult
  nu_pos_of_prime := fun p hp _ => nuDiv_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => nuDiv_lt_one_of_prime p hp

/-- The lower witness `s₋`: identical to `s₊` except weights `1 − λ(n)`. -/
noncomputable def sMinus (x : ℕ) : BoundingSieve where
  support := Finset.Icc 1 x
  prodPrimes := primorial (Nat.sqrt x)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun n => 1 - (liouville n : ℝ)
  weights_nonneg := fun n => by have := liouville_real_le n; linarith
  totalMass := (x : ℝ)
  nu := nuDiv
  nu_mult := nuDiv_mult
  nu_pos_of_prime := fun p hp _ => nuDiv_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => nuDiv_lt_one_of_prime p hp

@[simp] lemma sPlus_support (x : ℕ) : (sPlus x).support = Finset.Icc 1 x := rfl
@[simp] lemma sPlus_prodPrimes (x : ℕ) : (sPlus x).prodPrimes = primorial (Nat.sqrt x) := rfl
@[simp] lemma sPlus_weights (x n : ℕ) : (sPlus x).weights n = 1 + (liouville n : ℝ) := rfl
@[simp] lemma sPlus_totalMass (x : ℕ) : (sPlus x).totalMass = (x : ℝ) := rfl
@[simp] lemma sPlus_nu (x : ℕ) : (sPlus x).nu = nuDiv := rfl

@[simp] lemma sMinus_support (x : ℕ) : (sMinus x).support = Finset.Icc 1 x := rfl
@[simp] lemma sMinus_prodPrimes (x : ℕ) : (sMinus x).prodPrimes = primorial (Nat.sqrt x) := rfl
@[simp] lemma sMinus_weights (x n : ℕ) : (sMinus x).weights n = 1 - (liouville n : ℝ) := rfl
@[simp] lemma sMinus_totalMass (x : ℕ) : (sMinus x).totalMass = (x : ℝ) := rfl
@[simp] lemma sMinus_nu (x : ℕ) : (sMinus x).nu = nuDiv := rfl

/-! ## The survivor analysis -/

/-- The prime survivors: primes in `(⌊√x⌋, x]`. -/
def survPrimes (x : ℕ) : Finset ℕ := Nat.primesLE x \ Nat.primesLE (Nat.sqrt x)

lemma prime_of_mem_survPrimes {x n : ℕ} (hn : n ∈ survPrimes x) : n.Prime := by
  rw [survPrimes, Finset.mem_sdiff, Nat.mem_primesLE] at hn
  exact hn.1.2

lemma one_notMem_survPrimes (x : ℕ) : 1 ∉ survPrimes x := by
  rw [survPrimes, Finset.mem_sdiff, Nat.mem_primesLE]
  rintro ⟨⟨_, h⟩, _⟩
  exact Nat.not_prime_one h

lemma primesLE_sqrt_subset (x : ℕ) : Nat.primesLE (Nat.sqrt x) ⊆ Nat.primesLE x := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨le_trans hp.1 (Nat.sqrt_le_self x), hp.2⟩

/-- The number of prime survivors is `π(x) − π(√x)`. -/
lemma survPrimes_card (x : ℕ) :
    (survPrimes x).card = Nat.primeCounting x - Nat.primeCounting (Nat.sqrt x) := by
  rw [survPrimes, Finset.card_sdiff_of_subset (primesLE_sqrt_subset x),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

/-- The real form: `|survPrimes x| = π(x) − π(√x)` with real subtraction. -/
lemma survPrimes_card_real (x : ℕ) :
    ((survPrimes x).card : ℝ)
      = (Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ) := by
  rw [survPrimes_card, Nat.cast_sub (Nat.monotone_primeCounting (Nat.sqrt_le_self x))]

/-- **Forward survivor characterization**: a survivor coprime to `P(⌊√x⌋)` in
`[1, x]` is either `1` or prime (a composite `n ≤ x` has a prime factor
`≤ √n ≤ √x`, hence dividing the primorial). -/
lemma coprime_survivor_one_or_prime (x n : ℕ) (hn : 1 ≤ n ∧ n ≤ x)
    (hcop : Nat.Coprime (primorial (Nat.sqrt x)) n) : n = 1 ∨ n.Prime := by
  obtain ⟨hn1, hnx⟩ := hn
  by_cases h1 : n = 1
  · exact Or.inl h1
  · right
    by_contra hnp
    have hpos : 0 < n := by omega
    set p := n.minFac with hp
    have hp_prime : p.Prime := Nat.minFac_prime h1
    have hp_dvd : p ∣ n := Nat.minFac_dvd n
    have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hpos hnp
    have hpx : p * p ≤ x := by nlinarith [hsq, hnx]
    have hple : p ≤ Nat.sqrt x := Nat.le_sqrt.mpr hpx
    have hp_dvd_prim : p ∣ primorial (Nat.sqrt x) := hp_prime.dvd_primorial_iff.mpr hple
    have hdvd : p ∣ Nat.gcd (primorial (Nat.sqrt x)) n := Nat.dvd_gcd hp_dvd_prim hp_dvd
    rw [hcop] at hdvd
    exact hp_prime.one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- **The survivor set** coprime to `P(⌊√x⌋)` in `[1, x]` is exactly
`{1} ∪ primes(⌊√x⌋, x]`. -/
lemma coprime_filter_eq (x : ℕ) (hx : 1 ≤ x) :
    (Finset.Icc 1 x).filter (fun n => Nat.Coprime (primorial (Nat.sqrt x)) n)
      = insert 1 (survPrimes x) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, survPrimes,
    Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hn1, hnx⟩, hcop⟩
    rcases coprime_survivor_one_or_prime x n ⟨hn1, hnx⟩ hcop with h1 | hnp
    · exact Or.inl h1
    · refine Or.inr ⟨⟨hnx, hnp⟩, ?_⟩
      rintro ⟨hle, -⟩
      have hdvd : n ∣ primorial (Nat.sqrt x) := hnp.dvd_primorial_iff.mpr hle
      have : n ∣ Nat.gcd (primorial (Nat.sqrt x)) n := Nat.dvd_gcd hdvd dvd_rfl
      rw [hcop] at this
      exact hnp.one_lt.ne' (Nat.dvd_one.mp this)
  · rintro (rfl | ⟨⟨hnx, hnp⟩, hnotle⟩)
    · exact ⟨⟨le_refl 1, hx⟩, by simp⟩
    · have hlt : Nat.sqrt x < n := by
        by_contra h
        exact hnotle ⟨Nat.not_lt.mp h, hnp⟩
      refine ⟨⟨hnp.one_lt.le, hnx⟩, ?_⟩
      have hnd : ¬ n ∣ primorial (Nat.sqrt x) := by rw [hnp.dvd_primorial_iff]; omega
      exact (hnp.coprime_iff_not_dvd.mpr hnd).symm

/-- **Survivor evaluation, upper witness**: `siftedSum s₊ = 2`. The only
non-prime survivor is `1` (weight `1 + λ(1) = 2`); every prime `p` has weight
`1 + λ(p) = 0`. -/
lemma siftedSum_sPlus (x : ℕ) (hx : 2 ≤ x) : (sPlus x).siftedSum = 2 := by
  simp only [BoundingSieve.siftedSum, sPlus_support, sPlus_prodPrimes, sPlus_weights]
  rw [← Finset.sum_filter, coprime_filter_eq x (by omega),
    Finset.sum_insert (one_notMem_survPrimes x), liouville_real_one]
  have hz : ∑ n ∈ survPrimes x, (1 + (liouville n : ℝ)) = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [liouville_real_prime (prime_of_mem_survPrimes hn)]; norm_num
  rw [hz]; norm_num

/-- **Survivor evaluation, lower witness**: `siftedSum s₋ = 2·(π(x) − π(√x))`.
Here `1` has weight `1 − λ(1) = 0` and every prime `p` has weight
`1 − λ(p) = 2`, so the total is twice the prime count in `(√x, x]`. -/
lemma siftedSum_sMinus (x : ℕ) (hx : 2 ≤ x) :
    (sMinus x).siftedSum
      = 2 * ((Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ)) := by
  simp only [BoundingSieve.siftedSum, sMinus_support, sMinus_prodPrimes, sMinus_weights]
  rw [← Finset.sum_filter, coprime_filter_eq x (by omega),
    Finset.sum_insert (one_notMem_survPrimes x), liouville_real_one]
  have hval : ∀ n ∈ survPrimes x, (1 - (liouville n : ℝ)) = 2 := fun n hn => by
    rw [liouville_real_prime (prime_of_mem_survPrimes hn)]; norm_num
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, survPrimes_card_real]
  ring

/-! ## The pointwise remainder identity (D3) -/

/-- The multiples of `d ≥ 1` in `[1, x]` are `d·[1, ⌊x/d⌋]`. -/
lemma filter_dvd_eq_image (x d : ℕ) (hd : 1 ≤ d) :
    (Finset.Icc 1 x).filter (fun n => d ∣ n)
      = (Finset.Icc 1 (x / d)).image (fun m => d * m) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hn1, hnx⟩, hdn⟩
    exact ⟨n / d, ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdn),
      Nat.div_le_div_right hnx⟩, Nat.mul_div_cancel' hdn⟩
  · rintro ⟨m, ⟨hm1, hmx⟩, rfl⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity),
      le_trans (Nat.mul_le_mul_left d hmx) (Nat.mul_div_le x d)⟩, Dvd.intro m rfl⟩

/-- The count of multiples of `d` in `[1, x]` is `⌊x/d⌋`. -/
lemma count_mult_sum (x d : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1 : ℝ) else 0)) = ((x / d : ℕ) : ℝ) := by
  rw [Finset.sum_boole]
  norm_cast
  rw [show Finset.Icc 1 x = Finset.Ioc 0 x from by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
  exact Nat.Ioc_filter_dvd_card_eq_div x d

/-- The Liouville sum over multiples of `d`: `Σ_{n≤x, d∣n} λ(n) = λ(d)·M_λ(⌊x/d⌋)`
via total multiplicativity (`λ(dm) = λ(d)λ(m)`, no coprimality needed). -/
lemma lambda_mult_sum (x d : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (liouville n : ℝ) else 0))
      = (liouville d : ℝ) * Mlambda (x / d) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hL : ∑ n ∈ Finset.Icc 1 x, (if (0 : ℕ) ∣ n then (liouville n : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [if_neg (by rw [Nat.zero_dvd]; omega)]
    rw [hL]; simp
  · rw [← Finset.sum_filter, filter_dvd_eq_image x d hd,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h),
      Mlambda, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [liouville_apply_mul]; push_cast; ring

/-- **The pointwise remainder identity, upper witness** (D3):
`A_d(s₊) = ⌊x/d⌋ + λ(d)·M_λ(⌊x/d⌋)`. -/
lemma sPlus_multSum (x d : ℕ) :
    (sPlus x).multSum d = ((x / d : ℕ) : ℝ) + (liouville d : ℝ) * Mlambda (x / d) := by
  simp only [BoundingSieve.multSum, sPlus_support, sPlus_weights]
  have hsplit : ∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1 + (liouville n : ℝ)) else 0)
      = (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1 : ℝ) else 0))
        + (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (liouville n : ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [hsplit, count_mult_sum, lambda_mult_sum]

/-- **The pointwise remainder identity, lower witness**:
`A_d(s₋) = ⌊x/d⌋ − λ(d)·M_λ(⌊x/d⌋)`. -/
lemma sMinus_multSum (x d : ℕ) :
    (sMinus x).multSum d = ((x / d : ℕ) : ℝ) - (liouville d : ℝ) * Mlambda (x / d) := by
  simp only [BoundingSieve.multSum, sMinus_support, sMinus_weights]
  have hsplit : ∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1 - (liouville n : ℝ)) else 0)
      = (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1 : ℝ) else 0))
        - (∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (liouville n : ℝ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [hsplit, count_mult_sum, lambda_mult_sum]

/-! ## The remainder bound (D3): `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|` -/

/-- The floor crumb `|⌊x/d⌋ − x/d| ≤ 1` (the integer count vs. `ν(d)·X`). -/
lemma floor_frac_bound (x d : ℕ) : |((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h1 : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
    have h2 : (x : ℝ) / (d : ℝ) < ((x / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd']
      have hR : (x : ℝ) = (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod x d).symm
      have hltR : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt x hd
      nlinarith [hR, hltR]
    rw [abs_le]
    constructor <;> linarith

/-- `|a ± b·M| ≤ 1 + |M|` when `|a| ≤ 1` and `|b| ≤ 1`. -/
lemma abs_add_mul_le {a b M : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a + b * M| ≤ 1 + |M| := by
  have hbM : |b * M| ≤ |M| := by
    rw [abs_mul]
    calc |b| * |M| ≤ 1 * |M| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = |M| := one_mul _
  calc |a + b * M| ≤ |a| + |b * M| := abs_add_le _ _
    _ ≤ 1 + |M| := by linarith

lemma abs_sub_mul_le {a b M : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a - b * M| ≤ 1 + |M| := by
  rw [show a - b * M = a + (-b) * M from by ring]
  exact abs_add_mul_le ha (by rwa [abs_neg])

/-- The remainder of the upper witness, exact form. -/
lemma sPlus_rem (x d : ℕ) :
    (sPlus x).rem d
      = (((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)) + (liouville d : ℝ) * Mlambda (x / d) := by
  simp only [BoundingSieve.rem, sPlus_nu, sPlus_totalMass, nuDiv_apply]
  rw [sPlus_multSum]; ring

/-- The remainder of the lower witness, exact form. -/
lemma sMinus_rem (x d : ℕ) :
    (sMinus x).rem d
      = (((x / d : ℕ) : ℝ) - (x : ℝ) / (d : ℝ)) - (liouville d : ℝ) * Mlambda (x / d) := by
  simp only [BoundingSieve.rem, sMinus_nu, sMinus_totalMass, nuDiv_apply]
  rw [sMinus_multSum]; ring

/-- **The remainder bound, upper witness**: `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|`. -/
lemma sPlus_rem_bound (x d : ℕ) : |(sPlus x).rem d| ≤ 1 + |Mlambda (x / d)| := by
  rw [sPlus_rem]
  exact abs_add_mul_le (floor_frac_bound x d) (liouville_real_abs_le d)

/-- **The remainder bound, lower witness**: `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|`. -/
lemma sMinus_rem_bound (x d : ℕ) : |(sMinus x).rem d| ≤ 1 + |Mlambda (x / d)| := by
  rw [sMinus_rem]
  exact abs_sub_mul_le (floor_frac_bound x d) (liouville_real_abs_le d)

/-! ## The `SieveAgree` relation (D2) and the pair's agreement -/

/-- **`SieveAgree s t D B`** (D2): `s` and `t` agree on every field the sieve's
main term consumes (`prodPrimes`, `nu`, `totalMass`) and both meet the Rosser
remainder budget `B` at level `D`. This is the exact granularity at which the
landed sieve interface operates: exact equality on the main fields, a shared
budget on the error term. -/
def SieveAgree (s t : BoundingSieve) (D : ℕ) (B : ℝ) : Prop :=
  s.prodPrimes = t.prodPrimes ∧ s.nu = t.nu ∧ s.totalMass = t.totalMass
    ∧ Salt.Chen.rosserRemainder s (D : ℝ) ≤ B ∧ Salt.Chen.rosserRemainder t (D : ℝ) ≤ B

/-- **The witness pair agrees**: `s₊` and `s₋` share `prodPrimes`, `nu`,
`totalMass` (all `rfl`), so any common remainder budget `B` both meet gives
`SieveAgree (sPlus x) (sMinus x) D B`. The budget discharge is Q6a-2's job (via
the `M_λ` rate bridge, Q6a-3). -/
lemma sieveAgree_pair (x D : ℕ) (B : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B) :
    SieveAgree (sPlus x) (sMinus x) D B :=
  ⟨rfl, rfl, rfl, hplus, hminus⟩

/-! ## Numeric sanity (D5.3): at `x = 100`, `π(100) = 25`, `π(√100) = π(10) = 4`,
so `siftedSum s₊ = 2` and `siftedSum s₋ = 2·(25 − 4) = 42`. -/

example : (sPlus 100).siftedSum = 2 := siftedSum_sPlus 100 (by norm_num)

set_option maxRecDepth 4000 in
example : (sMinus 100).siftedSum = 42 := by
  have h1 : Nat.sqrt 100 = 10 := by norm_num
  have h2 : Nat.primeCounting 100 = 25 := by decide
  have h3 : Nat.primeCounting 10 = 4 := by decide
  rw [siftedSum_sMinus 100 (by norm_num), h1, h2, h3]
  norm_num

end Salt.TwinBar
