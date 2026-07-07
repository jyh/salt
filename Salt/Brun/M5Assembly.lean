/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.Sieve
import Salt.Brun.SelbergPort
import Salt.Brun.M3Expansion
import Salt.Brun.M3Assembly
import Salt.Brun.M2
import Salt.Brun

/-!
# N5.2 — the counting bound: assembling a `SelbergSieve` instance for twin
primes and chaining N1.4, N2.6, N3.6, N4.2 through it.

This is the biggest assembly node in the Brun track: it builds an actual
`SelbergSieve` instance (`twinSelbergSieve`) out of the twin-prime
`BoundingSieve` (N2.6, `Salt.TwinSieve.sieve`) with sieve parameters
`y N = N^(1/5)`, `z N = ⌊N^(1/10)⌋₊`, `P N = primorial (z N)`, and derives the
counting bound `twinPrimeCounting N ≤ N / S + (error) + (z N)` where
`S = Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)`.

This node is existential/asymptotic: constants and thresholds are loosened
freely throughout (a later node, N5.3, absorbs everything into a clean
`O(N / (log N)^2)`).
-/

open Finset ArithmeticFunction

namespace Salt.M5Assembly

/-! ## Step 0 — the primorial is squarefree -/

/-- A finite product of (distinct) primes is squarefree. -/
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

/-- The primorial (product of all primes `≤ n`) is squarefree. -/
lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) :=
  prod_primes_squarefree (fun _p hp => (Finset.mem_filter.mp hp).2)

/-! ## Step 1 — the sieve parameters, for a given `N` -/

/-- The Selberg sieve level: `N^(1/5)`. -/
noncomputable def y (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)

/-- The sieve truncation parameter: `⌊N^(1/10)⌋₊`. -/
noncomputable def z (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊

/-- The modulus to sift by: the primorial of `z N`. -/
noncomputable def P (N : ℕ) : ℕ := primorial (z N)

lemma P_squarefree (N : ℕ) : Squarefree (P N) := primorial_squarefree (z N)

/-! ## Rpow bookkeeping helpers -/

private lemma rpow_tenth_sq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 10 : ℝ)) ^ 2 = x ^ (1 / 5 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (1 / 10 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

private lemma rpow_tenth_pow8 (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 10 : ℝ)) ^ 8 = x ^ (4 / 5 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (1 / 10 : ℝ)) 8, ← Real.rpow_mul hx]
  norm_num

/-- The bridge between our own `omega` (`M4.lean`) and mathlib's
`ArithmeticFunction.cardDistinctFactors` (the `ω` used by `SelbergPort`). -/
lemma omega_eq_cardDistinctFactors (n : ℕ) :
    (omega n : ℕ) = ArithmeticFunction.cardDistinctFactors n := by
  unfold omega
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-! ## Step 2 — the `SelbergSieve` instance -/

/-- The twin-prime `SelbergSieve`, for `N ≥ 1`. -/
noncomputable def twinSelbergSieve (N : ℕ) (hN : 1 ≤ N) : SelbergSieve where
  toBoundingSieve := Salt.TwinSieve.sieve N (P N) (P_squarefree N)
  level := y N
  one_le_level := by
    unfold y
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

@[simp] lemma twinSelbergSieve_prodPrimes (N : ℕ) (hN : 1 ≤ N) :
    (twinSelbergSieve N hN).prodPrimes = P N := rfl

@[simp] lemma twinSelbergSieve_totalMass (N : ℕ) (hN : 1 ≤ N) :
    (twinSelbergSieve N hN).totalMass = (N : ℝ) := rfl

@[simp] lemma twinSelbergSieve_level (N : ℕ) (hN : 1 ≤ N) :
    (twinSelbergSieve N hN).level = y N := rfl

lemma twinSelbergSieve_selbergTerms (N : ℕ) (hN : 1 ≤ N) :
    (twinSelbergSieve N hN).selbergTerms
      = (Salt.TwinSieve.sieve N (P N) (P_squarefree N)).selbergTerms := rfl

lemma twinSelbergSieve_rem (N : ℕ) (hN : 1 ≤ N) (d : ℕ) :
    (twinSelbergSieve N hN).rem d = rem d N := by
  change (Salt.TwinSieve.sieve N (P N) (P_squarefree N)).rem d = rem d N
  exact Salt.TwinSieve.sieve_rem d

lemma twinSelbergSieve_siftedSum (N : ℕ) (hN : 1 ≤ N) :
    (twinSelbergSieve N hN).siftedSum
      = (Salt.TwinSieve.sieve N (P N) (P_squarefree N)).siftedSum := rfl

/-! ## Step 3 — `S ≥ mainTermSum (z N)`, hence `S ≥ c₀(log z)²` -/

lemma selbergBoundingSum_ge_mainTermSum (N : ℕ) (hN : 1 ≤ N) :
    Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
      ≥ Salt.M3Assembly.mainTermSum (z N) := by
  classical
  rw [ge_iff_le, Salt.SelbergPort.selbergBoundingSum, twinSelbergSieve_prodPrimes,
    twinSelbergSieve_level, ← Finset.sum_filter]
  rw [twinSelbergSieve_selbergTerms]
  rw [Salt.M3Assembly.mainTermSum]
  set small : Finset ℕ := (Finset.range (z N)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hsmall
  set big : Finset ℕ := (P N).divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ y N) with hbig
  have hsub : small ⊆ big := by
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, (P_squarefree N).ne_zero⟩, ?_⟩
    · -- ℓ ∣ P N
      have h1 : ℓ ∣ primorial ℓ := Squarefree.dvd_primorial hℓsq
      have h2 : primorial ℓ ∣ primorial (z N) := primorial_dvd_primorial (le_of_lt hℓz)
      exact h1.trans h2
    · -- (ℓ:ℝ)^2 ≤ y N
      have hℓR : (ℓ : ℝ) ≤ (z N : ℝ) := by exact_mod_cast (le_of_lt hℓz)
      have hzR : (z N : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
      have hℓnonneg : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
      have hstep : (ℓ : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hℓnonneg (le_trans hℓR hzR) 2
      rw [rpow_tenth_sq (N : ℝ) (Nat.cast_nonneg N)] at hstep
      change (ℓ : ℝ) ^ 2 ≤ y N
      rw [y]
      exact hstep
  have heq : ∑ ℓ ∈ small, Salt.M3Expansion.gTwin ℓ
      = ∑ ℓ ∈ small, (Salt.TwinSieve.sieve N (P N) (P_squarefree N)).selbergTerms ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    have hℓP : ℓ ∣ P N := by
      have h1 : ℓ ∣ primorial ℓ := Squarefree.dvd_primorial hℓsq
      have h2 : primorial ℓ ∣ primorial (z N) := primorial_dvd_primorial (le_of_lt hℓz)
      exact h1.trans h2
    exact (Salt.TwinSieve.selbergTerms_eq_gTwin hℓP hℓodd hℓsq).symm
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [hbig, Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt ((Salt.TwinSieve.sieve N (P N) (P_squarefree N)).selbergTerms_pos hl.1.1)

lemma selbergBoundingSum_ge_log_sq (N : ℕ) (hN : 1 ≤ N) (hzbig : Salt.M3Assembly.z0 ≤ z N) :
    Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
      ≥ (1 / 64 : ℝ) * (Real.log (z N)) ^ 2 := by
  have h1 := selbergBoundingSum_ge_mainTermSum N hN
  have hz16 : (16 : ℕ) ≤ z N := by unfold Salt.M3Assembly.z0 at hzbig; omega
  have hsqrt_ge1 : (1 : ℕ) ≤ (z N).sqrt := by
    have h4 : (4 : ℕ) ≤ (z N).sqrt := Nat.le_sqrt.mpr (by omega)
    omega
  have hlog4 : (4 : ℝ) ≤ Real.log (z N) := Salt.M3Assembly.log_ge_four hzbig
  have hD := Salt.M3Assembly.stepD hzbig
  have hpos : (0 : ℝ) ≤ (1 / 8 : ℝ) * Real.log (z N) := by linarith
  have hsq : ((1 / 8 : ℝ) * Real.log (z N)) ^ 2 ≤ (oddHarmonicSum ((z N).sqrt - 1)) ^ 2 :=
    pow_le_pow_left₀ hpos hD 2
  have hchain := Salt.M3Assembly.mainTermSum_ge_oddHarmonicSum_sq (z := z N) hsqrt_ge1
  have heq : ((1 / 8 : ℝ) * Real.log (z N)) ^ 2 = (1 / 64 : ℝ) * (Real.log (z N)) ^ 2 := by ring
  rw [heq] at hsq
  linarith [h1, hchain, hsq]

/-! ## Step 4 — the (guarded) error sum bound, reindexed -/

open Classical in
/-- The error sum appearing in `selberg_bound_simple`'s upper bound, for our
instance, is at most a generous `256 * N^(4/5)` (loose on purpose — no need
to fight for a tight constant/exponent here). -/
lemma guardedErrorSum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ (P N).divisors,
        if (d : ℝ) ≤ y N then (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N|
        else 0)
      ≤ 256 * (N : ℝ) ^ (4 / 5 : ℝ) := by
  classical
  set y' : ℕ := (z N + 1) ^ 2 with hy'def
  have hN10 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hzN : (z N : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
  have hlt : (N : ℝ) ^ (1 / 10 : ℝ) < (z N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hyN_lt : y N < ((z N : ℝ) + 1) ^ 2 := by
    have hsq : (N : ℝ) ^ (1 / 5 : ℝ) = ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 :=
      (rpow_tenth_sq (N : ℝ) (Nat.cast_nonneg N)).symm
    rw [y, hsq]
    exact pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  have hsub : (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N)
      ⊆ (Finset.range y').filter Squarefree := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hdle⟩ := hd
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Squarefree.squarefree_of_dvd hdvd (P_squarefree N)⟩
    have hdlt : (d : ℝ) < ((z N : ℝ) + 1) ^ 2 := lt_of_le_of_lt hdle hyN_lt
    have hy'cast : ((y' : ℕ) : ℝ) = ((z N : ℝ) + 1) ^ 2 := by rw [hy'def]; push_cast; ring
    rw [← hy'cast] at hdlt
    exact_mod_cast hdlt
  have hstep1 : (∑ d ∈ (P N).divisors,
      if (d : ℝ) ≤ y N then (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N|
      else 0)
      = ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N| := by
    rw [Finset.sum_filter]
  have hstep2 : ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N),
      (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N|
      = ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N),
          (3 : ℝ) ^ (omega d) * |rem d N| := by
    apply Finset.sum_congr rfl
    intro d _
    rw [omega_eq_cardDistinctFactors]
  have hstep3 : ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N),
      (3 : ℝ) ^ (omega d) * |rem d N|
      ≤ ∑ d ∈ (Finset.range y').filter Squarefree, (3 : ℝ) ^ (omega d) * |rem d N| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro d _ _
    positivity
  have hstep4 : ∑ d ∈ (Finset.range y').filter Squarefree, (3 : ℝ) ^ (omega d) * |rem d N|
      ≤ (y' : ℝ) ^ 4 := N4_2 y' N
  have hy'R : (y' : ℝ) ^ 4 = ((z N : ℝ) + 1) ^ 8 := by
    have : ((y' : ℕ) : ℝ) = ((z N : ℝ) + 1) ^ 2 := by rw [hy'def]; push_cast; ring
    rw [this]; ring
  have hzn1 : (z N : ℝ) + 1 ≤ 2 * (N : ℝ) ^ (1 / 10 : ℝ) := by linarith
  have hfinal : ((z N : ℝ) + 1) ^ 8 ≤ 256 * (N : ℝ) ^ (4 / 5 : ℝ) := by
    have h1 : ((z N : ℝ) + 1) ^ 8 ≤ (2 * (N : ℝ) ^ (1 / 10 : ℝ)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hzn1 8
    have h2 : (2 * (N : ℝ) ^ (1 / 10 : ℝ)) ^ 8
        = 256 * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 8 := by rw [mul_pow]; norm_num
    rw [h2, rpow_tenth_pow8 (N : ℝ) (Nat.cast_nonneg N)] at h1
    exact h1
  calc (∑ d ∈ (P N).divisors,
      if (d : ℝ) ≤ y N then (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N|
      else 0)
      = ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N| := hstep1
    _ = ∑ d ∈ (P N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y N), (3 : ℝ) ^ (omega d) * |rem d N| :=
        hstep2
    _ ≤ ∑ d ∈ (Finset.range y').filter Squarefree, (3 : ℝ) ^ (omega d) * |rem d N| := hstep3
    _ ≤ (y' : ℝ) ^ 4 := hstep4
    _ = ((z N : ℝ) + 1) ^ 8 := hy'R
    _ ≤ 256 * (N : ℝ) ^ (4 / 5 : ℝ) := hfinal

/-! ## Step 5 — assemble -/

/-- Every prime factor of `P N` is `≤ z N` — immediate from `P N` being the
primorial of `z N`. -/
lemma P_prime_factors_le (N : ℕ) : ∀ q, q.Prime → q ∣ P N → q ≤ z N := by
  intro q hq hqP
  exact hq.dvd_primorial_iff.mp hqP

/-- **N5.2.** The Selberg-sieve counting bound: `twinPrimeCounting N` is at
most `N / S + (error) + (z N + 1)`, where `S` is the twin sieve's Selberg
bounding sum. (The additive constants/exponents here are loosened generously;
a later node, N5.3, absorbs everything into a clean `O(N/(log N)^2)`.) -/
theorem N5_2 :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ hN : 1 ≤ N,
      (twinPrimeCounting N : ℝ) ≤
        (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
          + 256 * (N : ℝ) ^ (4 / 5 : ℝ)
          + ((z N : ℝ) + 1) := by
  refine ⟨1, fun N _ hN => ?_⟩
  -- Step (a): `twinPrimeCounting N` as a `Finset.filter` cardinality.
  have hcount : twinPrimeCounting N
      = ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card := by
    unfold twinPrimeCounting
    rw [Nat.count_eq_card_filter_range]
  set A := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) with hAdef
  set A1 := A.filter (fun p => p ≤ z N) with hA1def
  set A2 := A.filter (fun p => z N < p) with hA2def
  -- Step (b): `A = A1 ∪ A2`, disjointly.
  have hAeq : A = A1 ∪ A2 := by
    rw [hA1def, hA2def]
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p ≤ z N
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, by omega⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hAdisj : Disjoint A1 A2 := by
    rw [hA1def, hA2def, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega
  have hcard : A.card = A1.card + A2.card := by
    rw [hAeq, Finset.card_union_of_disjoint hAdisj]
  -- Step (c): bound `A1.card` trivially by `z N + 1`.
  have hA1sub : A1 ⊆ Finset.range (z N + 1) := by
    intro p hp
    rw [hA1def, Finset.mem_filter] at hp
    rw [Finset.mem_range]
    omega
  have hA1card : A1.card ≤ z N + 1 := by
    calc A1.card ≤ (Finset.range (z N + 1)).card := Finset.card_le_card hA1sub
      _ = z N + 1 := Finset.card_range _
  -- Step (d): bound `A2.card` by `siftedSum` via N5.1.
  have hA2sub : A2 ⊆ (Finset.Icc 1 N).filter
      (fun n => z N < n ∧ n.Prime ∧ (n + 2).Prime) := by
    intro p hp
    rw [hA2def, hAdef] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hpN, hpp, hp2⟩, hpz⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, by omega⟩, hpz, hpp, hp2⟩
    have := hpp.pos
    omega
  have hA2card_real : (A2.card : ℝ) ≤ (twinSelbergSieve N hN).siftedSum := by
    rw [twinSelbergSieve_siftedSum]
    have hstep1 : (A2.card : ℝ) ≤ (((Finset.Icc 1 N).filter
        (fun n => z N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hA2sub
    have hstep2 : (((Finset.Icc 1 N).filter
        (fun n => z N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ)
        ≤ (Salt.TwinSieve.sieve N (P N) (P_squarefree N)).siftedSum :=
      Salt.TwinSieve.twin_count_le_siftedSum (P_prime_factors_le N)
    exact le_trans hstep1 hstep2
  -- Step (e): `selberg_bound_simple` (N1.4) bounds `siftedSum`.
  have hselberg := Salt.SelbergPort.selberg_bound_simple (twinSelbergSieve N hN)
  rw [twinSelbergSieve_totalMass, twinSelbergSieve_prodPrimes, twinSelbergSieve_level] at hselberg
  have herr := guardedErrorSum_le N hN
  have hSpos := Salt.SelbergPort.selbergBoundingSum_pos (twinSelbergSieve N hN)
  -- Step (f): assemble everything.
  have hrem_eq : (∑ d ∈ (P N).divisors,
      if (d : ℝ) ≤ y N then
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |(twinSelbergSieve N hN).rem d|
      else 0)
      = ∑ d ∈ (P N).divisors,
          if (d : ℝ) ≤ y N then (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |rem d N|
          else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [twinSelbergSieve_rem]
  rw [hrem_eq] at hselberg
  have hchain : (twinSelbergSieve N hN).siftedSum
      ≤ (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
          + 256 * (N : ℝ) ^ (4 / 5 : ℝ) :=
    le_trans hselberg (by linarith [herr])
  have hcard_real : (A.card : ℝ) = (A1.card : ℝ) + (A2.card : ℝ) := by
    exact_mod_cast hcard
  rw [hcount, hcard_real]
  have hA1card_real : (A1.card : ℝ) ≤ (z N : ℝ) + 1 := by exact_mod_cast hA1card
  linarith [hA1card_real, hA2card_real, hchain]

end Salt.M5Assembly
