/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.ShiuSieve
import Salt.MR.RampSliver

/-!
# Short-interval Chebyshev / Brun–Titchmarsh bound (`ShortIntervalPsi`)

The named residual **THE GRAIN** of `Salt/MR/RampSliver.lean`: the short-interval
von Mangoldt bound

  `Σ_{k ∈ (a, a+H]} Λ(k) ≤ C_cheb · H`   in the regime `H ~ a·(log X)^{-1/2}`.

This is a Brun–Titchmarsh-grade estimate.  We obtain it by **adapting the Brun-track
Selberg-sieve apparatus** (`Salt/Brun/SelbergPort.lean`'s `selberg_bound_simple`,
already packaged for arithmetic progressions in `Salt/Maynard/ShiuSieve.lean` as
`apSieve`/`roughSieve`) from the full interval `[1,y]` to a **short interval
`(M, K]`** — the object `apSieve`/`roughSieve` never handled, and the reason the
`rough_count_in_ap_le` pole cannot be reused directly (it upper-bounds a full count;
a short-interval count is not a difference of two upper bounds).

The Part-1 law is preserved: this uses **no ζ-theory and no PNT** — the Selberg
`Λ²` sieve is elementary.

## The pieces

* `intSieve M K t` — the Selberg sieve on the interval `Ioc M K`, weight `≡ 1`,
  density `ν(d) = 1/d`, sifting by the primes `≤ t` (`roughP 1 t`), level `t²`.
  Same `ν`/`prodPrimes`/`level` as `roughSieve _ 1 _ t`, so it **shares the Selberg
  bounding sum** and reuses `Salt.Maynard.boundingSum_ge` (giving `log t ≤ S`).
* `intSieve_rem_abs_le` — `|R_d| ≤ 2`.  The one genuinely new analytic input: the
  count of multiples of `d` in a short interval is within `1` of `(K−M)/d`, applied
  at both endpoints (`congCount_bound` of `Salt/Brun/CongruenceCounting.lean`).
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

open Salt.Maynard

namespace Salt.MR

noncomputable section

/-! ## The interval Selberg sieve -/

/-- **The short-interval Selberg sieve.**  The integers of `(M, K]`, weight `≡ 1`,
density `ν(d) = 1/d`, sifted by the primes `≤ t` (`roughP 1 t = ∏_{p ≤ t} p`), at
level `t²`.  Identical `ν`/`prodPrimes`/`level` to `roughSieve _ 1 _ t`. -/
def intSieve (M K t : ℕ) (ht : 2 ≤ t) : SelbergSieve where
  support := Finset.Ioc M K
  prodPrimes := roughP 1 t
  prodPrimes_squarefree := roughP_squarefree 1 t
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (K : ℝ) - (M : ℝ)
  nu := apNu
  nu_mult := apNu_mult
  nu_pos_of_prime := fun p hp _ => apNu_pos p hp
  nu_lt_one_of_prime := fun p hp _ => apNu_lt_one p hp
  level := (t : ℝ) ^ 2
  one_le_level := by
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith

@[simp] lemma intSieve_prodPrimes (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).prodPrimes = roughP 1 t := rfl
@[simp] lemma intSieve_level (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).level = (t : ℝ) ^ 2 := rfl
@[simp] lemma intSieve_totalMass (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).totalMass = (K : ℝ) - (M : ℝ) := rfl
@[simp] lemma intSieve_nu (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).nu = apNu := rfl
@[simp] lemma intSieve_support (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).support = Finset.Ioc M K := rfl
@[simp] lemma intSieve_weights (M K t : ℕ) (ht : 2 ≤ t) (n : ℕ) :
    (intSieve M K t ht).weights n = 1 := rfl

/-- The multiplicity count of the interval sieve at `d` is the count of `n ∈ (M,K]`
divisible by `d`. -/
lemma intSieve_multSum (M K t d : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).multSum d
      = (((Finset.Ioc M K).filter (fun n => d ∣ n)).card : ℝ) := by
  rw [BoundingSieve.multSum, intSieve_support, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n _
  rw [intSieve_weights]

/-- The sifted sum counts `n ∈ (M,K]` coprime to `P = roughP 1 t`. -/
lemma intSieve_siftedSum (M K t : ℕ) (ht : 2 ≤ t) :
    (intSieve M K t ht).siftedSum
      = (((Finset.Ioc M K).filter (fun n => Nat.Coprime (roughP 1 t) n)).card : ℝ) := by
  rw [BoundingSieve.siftedSum, intSieve_support, intSieve_prodPrimes, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n _
  rw [intSieve_weights]

/-! ## The interval remainder bound `|R_d| ≤ 2` -/

/-- `congCount d {0} N = #{n ∈ [1,N] : d ∣ n}` for the residue set `{0}`. -/
lemma congCount_zero_eq_dvd (d N : ℕ) :
    congCount d {0} N = ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card := by
  unfold congCount
  congr 1
  apply Finset.filter_congr
  intro n _
  rw [Finset.mem_singleton, Nat.dvd_iff_mod_eq_zero]

/-- Multiples of `d` in `(M,K]` split off multiples in `[1,M]` from `[1,K]`. -/
lemma Ioc_filter_dvd_card (d M K : ℕ) (hMK : M ≤ K) :
    (((Finset.Icc 1 M).filter (fun n => d ∣ n)).card
        + ((Finset.Ioc M K).filter (fun n => d ∣ n)).card)
      = ((Finset.Icc 1 K).filter (fun n => d ∣ n)).card := by
  have hset : Finset.Icc 1 M ∪ Finset.Ioc M K = Finset.Icc 1 K := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Ioc M K) := by
    rw [Finset.disjoint_left]; intro n hn hn'
    simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_Ioc] at hn'; omega
  rw [← hset, Finset.filter_union,
    Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- The interval multiplicity as a difference of two `congCount`s. -/
lemma intSieve_multSum_eq_diff (M K t d : ℕ) (ht : 2 ≤ t) (hMK : M ≤ K) :
    (intSieve M K t ht).multSum d
      = (congCount d {0} K : ℝ) - (congCount d {0} M : ℝ) := by
  rw [intSieve_multSum, congCount_zero_eq_dvd, congCount_zero_eq_dvd]
  have := Ioc_filter_dvd_card d M K hMK
  have hcast : (((Finset.Icc 1 M).filter (fun n => d ∣ n)).card : ℝ)
      + (((Finset.Ioc M K).filter (fun n => d ∣ n)).card : ℝ)
      = (((Finset.Icc 1 K).filter (fun n => d ∣ n)).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- **The interval remainder bound.**  For `d ∣ roughP 1 t`, the interval Selberg
sieve's remainder is `≤ 2` — the short-interval multiple count is within `1` of the
expected value at each of the two endpoints (`congCount_bound`). -/
lemma intSieve_rem_abs_le (M K t : ℕ) (hMK : M ≤ K) (ht : 2 ≤ t)
    {d : ℕ} (hd : d ∣ roughP 1 t) : |(intSieve M K t ht).rem d| ≤ 2 := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (roughP_squarefree 1 t).ne_zero hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hcard : ({0} ∩ Finset.range d).card = 1 := by
    rw [Finset.singleton_inter_of_mem (Finset.mem_range.mpr hdpos), Finset.card_singleton]
  have e1 : ((({0} : Finset ℕ) ∩ Finset.range d).card : ℝ) = 1 := by rw [hcard, Nat.cast_one]
  -- endpoint bounds `|cc_N - N/d| ≤ 1`
  have hKb : |(congCount d {0} K : ℝ) - (K : ℝ) / d| ≤ 1 := by
    have h := congCount_bound (d := d) (S := {0}) hdpos K
    rw [e1, mul_one] at h; exact h
  have hMb : |(congCount d {0} M : ℝ) - (M : ℝ) / d| ≤ 1 := by
    have h := congCount_bound (d := d) (S := {0}) hdpos M
    rw [e1, mul_one] at h; exact h
  -- `rem = (cc_K - K/d) - (cc_M - M/d)`
  rw [BoundingSieve.rem, intSieve_multSum_eq_diff M K t d ht hMK, intSieve_nu,
    intSieve_totalMass, apNu_apply]
  have hexpand : ((congCount d {0} K : ℝ) - (congCount d {0} M : ℝ))
        - (d : ℝ)⁻¹ * ((K : ℝ) - (M : ℝ))
      = ((congCount d {0} K : ℝ) - (K : ℝ) / d)
        - ((congCount d {0} M : ℝ) - (M : ℝ) / d) := by
    ring
  rw [hexpand, abs_le]
  rw [abs_le] at hKb hMb
  exact ⟨by linarith [hKb.1, hKb.2, hMb.1, hMb.2],
         by linarith [hKb.1, hKb.2, hMb.1, hMb.2]⟩

/-! ## Reuse of the Selberg bounding-sum lower bound

`intSieve M K t` and `roughSieve 0 1 0 t` share `ν`, `prodPrimes`, `level`, hence
the same Selberg terms and the same bounding sum. -/

lemma intSieve_boundingSum_eq (M K t : ℕ) (ht : 2 ≤ t) :
    Salt.SelbergPort.selbergBoundingSum (intSieve M K t ht)
      = Salt.SelbergPort.selbergBoundingSum (roughSieve 0 1 0 t ht) := rfl

/-- **`log t ≤ S`.**  The Selberg bounding-sum lower bound for the interval sieve,
inherited from `Salt.Maynard.boundingSum_ge` at `q = 1`. -/
lemma intSieve_boundingSum_ge (M K t : ℕ) (ht : 2 ≤ t) :
    Real.log t ≤ Salt.SelbergPort.selbergBoundingSum (intSieve M K t ht) := by
  have h := boundingSum_ge 0 1 0 t (le_refl 1) ht
  rw [intSieve_boundingSum_eq M K t ht]
  simpa using h

/-! ## The interval error sum -/

/-- **The interval error sum bound.**  The Selberg error sum for the interval sieve,
truncated at `level = t²`, is `≤ 2·D·(1+log D)²` once every `d ∣ P` with `d ≤ t²`
is `≤ D`.  (Factor `2` vs. the AP case: `|R_d| ≤ 2` here.) -/
lemma intSieve_errSum_le (M K t : ℕ) (hMK : M ≤ K) (ht : 2 ≤ t)
    (D : ℕ) (hDbound : ∀ d, d ∣ roughP 1 t → (d : ℝ) ≤ (t : ℝ) ^ 2 → d ≤ D) :
    ∑ d ∈ (roughP 1 t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(intSieve M K t ht).rem d| else 0)
      ≤ 2 * ((D : ℝ) * (1 + Real.log D) ^ 2) := by
  have step1 : ∑ d ∈ (roughP 1 t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(intSieve M K t ht).rem d| else 0)
      ≤ ∑ d ∈ (roughP 1 t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then 2 * (3 : ℝ) ^ d.primeFactors.card else 0) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Nat.mem_divisors] at hd
    split_ifs with hL'
    · rw [omega_eq_card]
      have hb := intSieve_rem_abs_le M K t hMK ht hd.1
      have : (3 : ℝ) ^ d.primeFactors.card * |(intSieve M K t ht).rem d|
          ≤ (3 : ℝ) ^ d.primeFactors.card * 2 :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      linarith
    · exact le_refl _
  have step2 : ∑ d ∈ (roughP 1 t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then 2 * (3 : ℝ) ^ d.primeFactors.card else 0)
      ≤ 2 * ∑ d ∈ Finset.Icc 1 D, (3 : ℝ) ^ d.primeFactors.card := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdmem, hdL⟩ := hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
      rw [Nat.mem_divisors] at hdmem
      rw [Finset.mem_Icc]
      exact ⟨hd1, hDbound d hdmem.1 hdL⟩
    · intro d _ _; positivity
  have step3 := sum_k_pow_omega_le D 3 (by norm_num)
  have h32 : (3 : ℕ) - 1 = 2 := rfl
  rw [h32] at step3
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ 2 * ((D : ℝ) * (1 + Real.log D) ^ 2) := by
        have : ∑ d ∈ Finset.Icc 1 D, (3 : ℝ) ^ d.primeFactors.card
            ≤ (D : ℝ) * (1 + Real.log D) ^ 2 := step3
        linarith

/-! ## The short-interval Brun–Titchmarsh rough count -/

/-- **Short-interval rough count** (the Selberg-sieve Brun–Titchmarsh bound, adapted to
`(M, K]`).  The number of integers in `(M, K]` with no prime factor `≤ t` is at most
`(K−M)/log t + 50·t³`.  No ζ-theory, no PNT. -/
theorem shortInterval_rough_count_le (M K t : ℕ) (hMK : M ≤ K) (ht : 2 ≤ t) :
    (((Finset.Ioc M K).filter (fun n => Nat.Coprime (roughP 1 t) n)).card : ℝ)
      ≤ ((K : ℝ) - (M : ℝ)) / Real.log t + 50 * (t : ℝ) ^ 3 := by
  have htR : (0 : ℝ) < t := by
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hKM : (0 : ℝ) ≤ (K : ℝ) - (M : ℝ) := by
    have : (M : ℝ) ≤ (K : ℝ) := by exact_mod_cast hMK
    linarith
  -- Selberg fundamental theorem for the interval sieve
  have hsel := Salt.SelbergPort.selberg_bound_simple (intSieve M K t ht)
  rw [intSieve_prodPrimes, intSieve_level, intSieve_totalMass, intSieve_siftedSum] at hsel
  -- main term: totalMass / S ≤ (K-M)/log t
  have hSge := intSieve_boundingSum_ge M K t ht
  have hmain : ((K : ℝ) - (M : ℝ)) / Salt.SelbergPort.selbergBoundingSum (intSieve M K t ht)
      ≤ ((K : ℝ) - (M : ℝ)) / Real.log t :=
    div_le_div_of_nonneg_left hKM hlogt hSge
  -- error term: ≤ 50 t³
  have hDbound : ∀ d, d ∣ roughP 1 t → (d : ℝ) ≤ (t : ℝ) ^ 2 → d ≤ t ^ 2 := by
    intro d _ hdL
    have h : (d : ℝ) ≤ ((t ^ 2 : ℕ) : ℝ) := by
      rw [show ((t ^ 2 : ℕ) : ℝ) = (t : ℝ) ^ 2 by push_cast; ring]; exact hdL
    exact_mod_cast h
  have herr := intSieve_errSum_le M K t hMK ht (t ^ 2) hDbound
  have herrcube := err_le_cube t ht
  have herr2 : ∑ d ∈ (roughP 1 t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(intSieve M K t ht).rem d| else 0)
      ≤ 50 * (t : ℝ) ^ 3 := by
    have hcast : ((t ^ 2 : ℕ) : ℝ) = (t : ℝ) ^ 2 := by push_cast; ring
    calc _ ≤ 2 * (((t ^ 2 : ℕ) : ℝ) * (1 + Real.log ((t ^ 2 : ℕ) : ℝ)) ^ 2) := herr
      _ ≤ 2 * (25 * (t : ℝ) ^ 3) := by linarith [herrcube]
      _ = 50 * (t : ℝ) ^ 3 := by ring
  calc (((Finset.Ioc M K).filter (fun n => Nat.Coprime (roughP 1 t) n)).card : ℝ)
      ≤ ((K : ℝ) - (M : ℝ)) / Salt.SelbergPort.selbergBoundingSum (intSieve M K t ht)
          + ∑ d ∈ (roughP 1 t).divisors,
              (if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(intSieve M K t ht).rem d|
                else 0) := hsel
    _ ≤ ((K : ℝ) - (M : ℝ)) / Real.log t + 50 * (t : ℝ) ^ 3 := add_le_add hmain herr2

/-! ## From the rough count to the von Mangoldt mass -/

/-- **Not-coprime prime powers are few.**  In `(M, K]` with `K ≤ 2M+1`, at most `t`
integers are prime powers whose base is `≤ t`: the map `k ↦ minFac k` is injective
into the primes `≤ t` — a base `p` has at most one power in the interval, since
`p^{e+1} ≥ 2(M+1) > K`. -/
lemma intSieve_notCoprime_pp_card_le (M K t : ℕ) (hM : 1 ≤ M) (hK2M : K ≤ 2 * M + 1)
    (ht : 2 ≤ t) :
    ((Finset.Ioc M K).filter
        (fun k => IsPrimePow k ∧ ¬ Nat.Coprime (roughP 1 t) k)).card ≤ t := by
  calc ((Finset.Ioc M K).filter
          (fun k => IsPrimePow k ∧ ¬ Nat.Coprime (roughP 1 t) k)).card
      ≤ (Finset.Icc 1 t).card := by
        apply Finset.card_le_card_of_injOn (fun k => k.minFac)
        · -- maps into `Icc 1 t`
          intro k hk
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hk
          obtain ⟨⟨_, _⟩, _, hncop⟩ := hk
          simp only [Finset.mem_coe, Finset.mem_Icc]
          refine ⟨Nat.minFac_pos k, ?_⟩
          have hne1 : Nat.gcd (roughP 1 t) k ≠ 1 := hncop
          obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne1
          have hpP : p ∣ roughP 1 t := hpg.trans (Nat.gcd_dvd_left _ _)
          have hpk : p ∣ k := hpg.trans (Nat.gcd_dvd_right _ _)
          have hpt : p ≤ t := (prime_dvd_roughP hp hpP).1
          exact le_trans (Nat.minFac_le_of_dvd hp.two_le hpk) hpt
        · -- injective on the set
          intro k1 hk1 k2 hk2 heq
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hk1 hk2
          obtain ⟨⟨hMk1, hk1K⟩, hpp1, -⟩ := hk1
          obtain ⟨⟨hMk2, hk2K⟩, hpp2, -⟩ := hk2
          have heq' : k1.minFac = k2.minFac := heq
          have hk1ne1 : k1 ≠ 1 := by omega
          set p := k1.minFac with hpdef
          have hp2 : 2 ≤ p := (Nat.minFac_prime hk1ne1).two_le
          have hk1pow : p ^ (k1.factorization p) = k1 :=
            IsPrimePow.minFac_pow_factorization_eq hpp1
          have hk2pow : p ^ (k2.factorization p) = k2 := by
            have h := IsPrimePow.minFac_pow_factorization_eq hpp2
            rw [← heq'] at h; exact h
          set e1 := k1.factorization p with he1
          set e2 := k2.factorization p with he2
          rcases lt_trichotomy e1 e2 with h | h | h
          · exfalso
            have h1 : p ^ (e1 + 1) ≤ p ^ e2 := Nat.pow_le_pow_right (by omega) (by omega)
            rw [pow_succ, hk1pow, hk2pow] at h1
            have hmul : k1 * 2 ≤ k1 * p := by gcongr
            omega
          · rw [← hk1pow, ← hk2pow, h]
          · exfalso
            have h1 : p ^ (e2 + 1) ≤ p ^ e1 := Nat.pow_le_pow_right (by omega) (by omega)
            rw [pow_succ, hk1pow, hk2pow] at h1
            have hmul : k2 * 2 ≤ k2 * p := by gcongr
            omega
    _ = t := by rw [Nat.card_Icc]; omega

/-- **The short-interval von Mangoldt bound (parametrised by the sifting `t`).**
`Σ_{k ∈ (M,K]} Λ(k) ≤ log K · ((K−M)/log t + 50·t³ + t)`, for `1 ≤ M ≤ K ≤ 2M+1`
and `2 ≤ t`.  Each `Λ(k) ≤ log K` on the `#{prime powers}` support; that count splits
into rough numbers (the sieve count) plus the `≤ t` small-base prime powers. -/
theorem shortInterval_vonMangoldt_le_aux (M K t : ℕ) (hM : 1 ≤ M) (hMK : M ≤ K)
    (hK2M : K ≤ 2 * M + 1) (ht : 2 ≤ t) :
    ∑ k ∈ Finset.Ioc M K, ArithmeticFunction.vonMangoldt k
      ≤ Real.log K * (((K : ℝ) - (M : ℝ)) / Real.log t + 50 * (t : ℝ) ^ 3 + (t : ℝ)) := by
  have hK1 : 1 ≤ K := le_trans hM hMK
  have hlogK_nn : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
  -- Step A: `Σ Λ(k) ≤ log K · #{prime powers in (M,K]}`
  have hstepA : ∑ k ∈ Finset.Ioc M K, ArithmeticFunction.vonMangoldt k
      ≤ Real.log K * (((Finset.Ioc M K).filter (fun k => IsPrimePow k)).card : ℝ) := by
    have hbound : ∀ k ∈ Finset.Ioc M K, ArithmeticFunction.vonMangoldt k
        ≤ Real.log K * (if IsPrimePow k then (1 : ℝ) else 0) := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [ArithmeticFunction.vonMangoldt_apply]
      split_ifs with hpp
      · rw [mul_one]
        apply Real.log_le_log (by exact_mod_cast Nat.minFac_pos k)
        have h1 : k.minFac ≤ k := Nat.minFac_le (by omega)
        exact_mod_cast le_trans h1 hk.2
      · rw [mul_zero]
    calc ∑ k ∈ Finset.Ioc M K, ArithmeticFunction.vonMangoldt k
        ≤ ∑ k ∈ Finset.Ioc M K, Real.log K * (if IsPrimePow k then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hbound
      _ = Real.log K * (((Finset.Ioc M K).filter (fun k => IsPrimePow k)).card : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
  -- Step B: `#{pp} ≤ #{coprime} + #{pp ∧ ¬coprime}`
  have hstepB : (((Finset.Ioc M K).filter (fun k => IsPrimePow k)).card : ℝ)
      ≤ (((Finset.Ioc M K).filter (fun k => Nat.Coprime (roughP 1 t) k)).card : ℝ)
        + (((Finset.Ioc M K).filter
            (fun k => IsPrimePow k ∧ ¬ Nat.Coprime (roughP 1 t) k)).card : ℝ) := by
    have hsub : (Finset.Ioc M K).filter (fun k => IsPrimePow k)
        ⊆ (Finset.Ioc M K).filter (fun k => Nat.Coprime (roughP 1 t) k)
          ∪ (Finset.Ioc M K).filter
              (fun k => IsPrimePow k ∧ ¬ Nat.Coprime (roughP 1 t) k) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hc : Nat.Coprime (roughP 1 t) k
      · exact Or.inl ⟨hk.1, hc⟩
      · exact Or.inr ⟨hk.1, hk.2, hc⟩
    have := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    exact_mod_cast this
  -- Step C: `#{pp ∧ ¬coprime} ≤ t`
  have hstepC : (((Finset.Ioc M K).filter
      (fun k => IsPrimePow k ∧ ¬ Nat.Coprime (roughP 1 t) k)).card : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast intSieve_notCoprime_pp_card_le M K t hM hK2M ht
  -- Step D: rough count for `#{coprime}`
  have hrough := shortInterval_rough_count_le M K t hMK ht
  -- combine
  refine le_trans hstepA ?_
  refine mul_le_mul_of_nonneg_left ?_ hlogK_nn
  linarith [hstepB, hstepC, hrough]

/-! ## The short-interval von Mangoldt bound at relative length `a^{-1/8}` -/

set_option maxHeartbeats 1600000 in
-- Heartbeats raised: the final assembly runs linear arithmetic over the (opaque)
-- nested-`sqrt`/`log`/floor atoms of a long real-analytic optimisation.
/-- **THE GRAIN, discharged.**  The short-interval von Mangoldt / Chebyshev bound in
the Brun–Titchmarsh regime: there is an absolute `C` with
`Σ_{k ∈ (a, a+H]} Λ(k) ≤ C · H` whenever the interval is "not too short" —
`a^{7/8} ≤ H ≤ a` (equivalently relative length `H/a ≥ a^{-1/8}`) and `a ≥ 2^16`.

The sifting level is `t = ⌊(a+H)^{1/8}⌋`: the main term's `log K` cancels against
`log t ≥ (1/16) log K`, and the Selberg error `50 t³` plus the small-base prime powers
`t`, each weighted by `log K ≤ 2√(a+H)`, land at `(a+H)^{7/8} ≤ 2 a^{7/8} ≤ 2H`.
No ζ-theory, no PNT.  Regime hypothesis stated rpow-free via `√(√(√ ·)) = ·^{1/8}`. -/
theorem shortInterval_vonMangoldt_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a H : ℝ, (65536 : ℝ) ≤ a →
        a ≤ H * Real.sqrt (Real.sqrt (Real.sqrt a)) → H ≤ a →
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊a + H⌋₊, ArithmeticFunction.vonMangoldt k ≤ C * H := by
  refine ⟨250, by norm_num, fun a H ha hHr hHa => ?_⟩
  -- basic positivity
  have ha0 : (0 : ℝ) < a := by linarith
  have hrpos : 0 < Real.sqrt (Real.sqrt (Real.sqrt a)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha0))
  have hH0 : (0 : ℝ) < H := by
    by_contra h
    rw [not_lt] at h
    nlinarith [hrpos, hHr, ha0, h]
  set P : ℝ := a + H with hPdef
  have hP0 : (0 : ℝ) < P := by rw [hPdef]; linarith
  have hP2a : P ≤ 2 * a := by rw [hPdef]; linarith
  have hPge : (65536 : ℝ) ≤ P := by rw [hPdef]; linarith
  -- the eighth-root `q = √√√P` and its powers
  have hsqP : (0 : ℝ) ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hssP : (0 : ℝ) ≤ Real.sqrt (Real.sqrt P) := Real.sqrt_nonneg _
  set q : ℝ := Real.sqrt (Real.sqrt (Real.sqrt P)) with hqdef
  have hq0 : (0 : ℝ) ≤ q := Real.sqrt_nonneg _
  have hqpos : (0 : ℝ) < q :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hP0))
  have hq2 : q ^ 2 = Real.sqrt (Real.sqrt P) := Real.sq_sqrt hssP
  have hq4 : q ^ 4 = Real.sqrt P := by
    have h : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [h, hq2, Real.sq_sqrt hsqP]
  have hq8 : q ^ 8 = P := by
    have h : q ^ 8 = (q ^ 4) ^ 2 := by ring
    rw [h, hq4, Real.sq_sqrt hP0.le]
  -- `q ≥ 4`
  have hq4ge : (4 : ℝ) ≤ q := by
    have h48 : (4 : ℝ) ^ 8 ≤ q ^ 8 := by rw [hq8]; nlinarith [hPge]
    exact le_of_pow_le_pow_left₀ (by norm_num) hq0 h48
  -- the root `r = √√√a` and its powers
  have hsqa : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hssa : (0 : ℝ) ≤ Real.sqrt (Real.sqrt a) := Real.sqrt_nonneg _
  set r : ℝ := Real.sqrt (Real.sqrt (Real.sqrt a)) with hrdef
  have hr8 : r ^ 8 = a := by
    have h2 : r ^ 2 = Real.sqrt (Real.sqrt a) := Real.sq_sqrt hssa
    have h4 : r ^ 4 = Real.sqrt a := by
      have h : r ^ 4 = (r ^ 2) ^ 2 := by ring
      rw [h, h2, Real.sq_sqrt hsqa]
    have h : r ^ 8 = (r ^ 4) ^ 2 := by ring
    rw [h, h4, Real.sq_sqrt ha0.le]
  have hqr : r ≤ q := by
    rw [hqdef, hrdef]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by rw [hPdef]; linarith)))
  have hr4ge : (4 : ℝ) ≤ r := by
    have h48 : (4 : ℝ) ^ 8 ≤ r ^ 8 := by rw [hr8]; nlinarith [ha]
    exact le_of_pow_le_pow_left₀ (by norm_num) hrpos.le h48
  -- `r^7 ≤ H` and `q^7 ≤ 2H`
  have hr7 : r ^ 7 ≤ H := by
    have hstep : r ^ 7 * r ≤ H * r := by
      rw [← pow_succ, hr8]; exact hHr
    exact le_of_mul_le_mul_right hstep hrpos
  have hH1 : (1 : ℝ) ≤ H := by
    have hr7ge1 : (1 : ℝ) ≤ r ^ 7 := by
      calc (1 : ℝ) = 1 ^ 7 := by norm_num
        _ ≤ r ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith [hr4ge]) 7
    linarith [hr7, hr7ge1]
  have hq7 : q ^ 7 ≤ 2 * H := by
    have hstep : q ^ 7 * q ≤ (2 * H) * q := by
      rw [← pow_succ, hq8]
      have h1 : (2 : ℝ) * H * r ≤ 2 * H * q :=
        mul_le_mul_of_nonneg_left hqr (by linarith [hH0.le])
      nlinarith [hP2a, hHr, h1]
    exact le_of_mul_le_mul_right hstep hqpos
  -- the sifting level `t = ⌊q⌋`
  set t : ℕ := ⌊q⌋₊ with htdef
  have ht_le : (t : ℝ) ≤ q := Nat.floor_le hq0
  have ht_lt : q < (t : ℝ) + 1 := Nat.lt_floor_add_one q
  have ht4 : 4 ≤ t := Nat.le_floor (by exact_mod_cast hq4ge)
  have ht2 : 2 ≤ t := by omega
  -- floors `M = ⌊a⌋`, `K = ⌊a+H⌋`
  set M : ℕ := ⌊a⌋₊ with hMdef
  set K : ℕ := ⌊a + H⌋₊ with hKdef
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ a))
  have hMK : M ≤ K := Nat.floor_mono (by linarith)
  have hKleP : (K : ℝ) ≤ P := by rw [hKdef, hPdef]; exact Nat.floor_le (by linarith)
  have hMgt : a - 1 < (M : ℝ) := by have := Nat.lt_floor_add_one a; rw [hMdef]; linarith
  have hK2M : K ≤ 2 * M + 1 := by
    have hreal : (K : ℝ) < 2 * (M : ℝ) + 2 := by
      have h2a : a < (M : ℝ) + 1 := by have := Nat.lt_floor_add_one a; rw [hMdef]; linarith
      have : (K : ℝ) ≤ 2 * a := le_trans hKleP hP2a
      linarith
    have : K < 2 * M + 2 := by exact_mod_cast hreal
    omega
  -- basic log facts
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : 1 ≤ K := le_trans hM1 hMK
    exact_mod_cast this
  have hlogK_nn : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (le_trans hM1 hMK))
  have hlogP_pos : (0 : ℝ) < Real.log P := Real.log_pos (by linarith)
  have hlogK_le : Real.log K ≤ Real.log P := Real.log_le_log hKpos hKleP
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have h4t : (4 : ℝ) ≤ t := by exact_mod_cast ht4
    linarith
  have hlogt_pos : (0 : ℝ) < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  -- `log q = (1/8) log P`
  have hlogq : Real.log q = (1 / 8) * Real.log P := by
    rw [hqdef, Real.log_sqrt hssP, Real.log_sqrt hsqP, Real.log_sqrt hP0.le]; ring
  -- `log t ≥ (1/16) log P`
  have hqhalf : q / 2 ≤ (t : ℝ) := by linarith [hq4ge, ht_lt]
  have hlogt_ge : (1 / 16) * Real.log P ≤ Real.log t := by
    have hlogqhalf : Real.log (q / 2) ≤ Real.log t :=
      Real.log_le_log (by positivity) hqhalf
    have heq : Real.log (q / 2) = (1 / 8) * Real.log P - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hqpos) (by norm_num), hlogq]
    have hlog2 : (16 : ℝ) * Real.log 2 ≤ Real.log P := by
      have h1 : Real.log ((2 : ℝ) ^ (16 : ℕ)) ≤ Real.log P := by
        apply Real.log_le_log (by norm_num)
        rw [show ((2 : ℝ) ^ (16 : ℕ)) = 65536 by norm_num]; exact hPge
      rwa [Real.log_pow] at h1
    linarith [hlogqhalf, heq, hlog2]
  -- `log P ≤ 2 √P`
  have hlogP_2sqrt : Real.log P ≤ 2 * Real.sqrt P := by
    have h1 : Real.log (Real.sqrt P) ≤ Real.sqrt P - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hP0)
    have h2 : Real.log P = 2 * Real.log (Real.sqrt P) := by
      rw [Real.log_sqrt hP0.le]; ring
    linarith
  have hlogK_2q4 : Real.log K ≤ 2 * q ^ 4 := by rw [hq4]; linarith [hlogK_le, hlogP_2sqrt]
  -- the counting inputs
  have hKM_le : (K : ℝ) - (M : ℝ) ≤ H + 1 := by linarith [hKleP, hMgt, hP2a]
  have hKM_nn : (0 : ℝ) ≤ (K : ℝ) - (M : ℝ) := by
    have : (M : ℝ) ≤ (K : ℝ) := by exact_mod_cast hMK
    linarith
  -- make the sqrt/floor definitions opaque so linarith/nlinarith stay cheap
  clear_value P q r t M K
  -- the parametrised bound
  have haux := shortInterval_vonMangoldt_le_aux M K t hM1 hMK hK2M ht2
  refine le_trans haux ?_
  -- distribute and bound the three terms
  rw [mul_add, mul_add]
  -- term (i): `log K * ((K-M)/log t) ≤ 32 H`
  have hti : Real.log K * (((K : ℝ) - (M : ℝ)) / Real.log t) ≤ 32 * H := by
    rw [← mul_div_assoc]
    have hnum : Real.log K * ((K : ℝ) - (M : ℝ)) ≤ Real.log P * (H + 1) :=
      mul_le_mul hlogK_le hKM_le hKM_nn hlogP_pos.le
    have hstep1 : Real.log K * ((K : ℝ) - (M : ℝ)) / Real.log t
        ≤ Real.log P * (H + 1) / Real.log t :=
      div_le_div_of_nonneg_right hnum hlogt_pos.le
    have hnum_nn : (0 : ℝ) ≤ Real.log P * (H + 1) := mul_nonneg hlogP_pos.le (by linarith [hH1])
    have hstep2 : Real.log P * (H + 1) / Real.log t
        ≤ Real.log P * (H + 1) / ((1 / 16) * Real.log P) :=
      div_le_div_of_nonneg_left hnum_nn (mul_pos (by norm_num) hlogP_pos) hlogt_ge
    have hstep3 : Real.log P * (H + 1) / ((1 / 16) * Real.log P) = 16 * (H + 1) := by
      field_simp [hlogP_pos.ne']
    have hfin : (16 : ℝ) * (H + 1) ≤ 32 * H := by linarith [hH1]
    linarith [hstep1, hstep2, hstep3.le, hfin]
  -- term (ii): `50 * log K * t³ ≤ 200 H`
  have htii : Real.log K * (50 * (t : ℝ) ^ 3) ≤ 200 * H := by
    have h2 : Real.log K * (t : ℝ) ^ 3 ≤ (2 * q ^ 4) * q ^ 3 :=
      mul_le_mul hlogK_2q4 (pow_le_pow_left₀ ht_pos.le ht_le 3) (by positivity) (by positivity)
    have h3 : (2 * q ^ 4) * q ^ 3 = 2 * q ^ 7 := by ring
    have h5 : Real.log K * (t : ℝ) ^ 3 ≤ 2 * q ^ 7 := by rw [← h3]; exact h2
    nlinarith [h5, hq7]
  -- term (iii): `log K * t ≤ 4 H`
  have htiii : Real.log K * (t : ℝ) ≤ 4 * H := by
    have h2 : Real.log K * (t : ℝ) ≤ (2 * q ^ 4) * q :=
      mul_le_mul hlogK_2q4 ht_le (by positivity) (by positivity)
    have h3 : (2 * q ^ 4) * q = 2 * q ^ 5 := by ring
    have h4 : q ^ 5 ≤ q ^ 7 := pow_le_pow_right₀ (by linarith [hq4ge]) (by norm_num)
    have h5 : Real.log K * (t : ℝ) ≤ 2 * q ^ 5 := by rw [← h3]; exact h2
    nlinarith [h5, h4, hq7, hH0.le]
  refine le_trans (add_le_add (add_le_add hti htii) htiii) ?_
  linarith only [hH1]

/-! ## Discharging RampSliver's `hgrain` -/

/-- **The `hgrain` discharge.**  `RampSliver.ramp_sliver_bound`'s sole named residual
`hgrain` follows by direct application of `shortInterval_vonMangoldt_le` at
`a = X/l`, `H = h/l` (note `(X+h)/l = X/l + h/l`), given the per-window regime facts
`hreg` (each provided by the branch-(a) caller: `X/l ≥ 2^16`, relative length
`(X/l)^{7/8} ≤ h/l`, and `h/l ≤ X/l`).  This turns `ramp_sliver_bound` from
conditional into a closed bound. -/
theorem rampSliverMass_bound_unconditional (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y : ℝ} (hX : Real.exp 1 ≤ X) (hh : h = X / Real.sqrt (Real.log X))
    (hy10 : (10 : ℝ) ≤ y) (hygate : Real.sqrt (Real.log X) ≤ y)
    (hreg : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
        (65536 : ℝ) ≤ X / (l : ℝ) ∧
        X / (l : ℝ) ≤ (h / (l : ℝ)) *
          Real.sqrt (Real.sqrt (Real.sqrt (X / (l : ℝ)))) ∧
        h / (l : ℝ) ≤ X / (l : ℝ)) :
    ∃ C : ℝ, rampSliverMass g X h y ≤ C * (X / Real.log X) * Real.log y := by
  obtain ⟨Cc, hCc0, hCbound⟩ := shortInterval_vonMangoldt_le
  refine ramp_sliver_bound g hg hX hh hy10 hygate hCc0 ?_
  intro l hl
  obtain ⟨h1, h2, h3⟩ := hreg l hl
  have hkey := hCbound (X / (l : ℝ)) (h / (l : ℝ)) h1 h2 h3
  rwa [show (X + h) / (l : ℝ) = X / (l : ℝ) + h / (l : ℝ) from add_div X h (l : ℝ)]

end

end Salt.MR
