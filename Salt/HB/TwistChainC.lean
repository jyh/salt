/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TwistChain

/-!
# Heath-Brown's Lemma 1(c): the `Λ̃ − Λ` bound (HB-ENGINE, node HB-1c)

The residual of `HB-1`. For a real character `χ` (`χ² = 1`) and `n` coprime to `q`,
Lemma 1(c) bounds the "overshoot" of the twisted von Mangoldt function `Λ̃` over the
genuine `Λ`:

`Λ̃(n) − Λ(n) ≤ 2·( f(n)·log n + (f(n₊) − 1)·Λ(n₋) )`.

## The engine (from `Salt.HB.TwistChain`)

`Λ̃ = f ∗ Λ` (`LamTilde_eq_fChi_conv`), so reindexing the convolution over divisors,
`Λ̃(n) = ∑_{a ∣ n} f(a)·Λ(n/a)`. Since `Λ` is supported on prime powers, the surviving
terms are `a = n/p^k`. Two local facts about `f = fChiArith` drive the case analysis:

* `f(a) = 0` as soon as some prime `p ∣ a` has `χ(p) = −1` (local factor `1 + χ(p) = 0`);
* on `χ = +1` numbers `f` is `2^ω` (each local factor is `1 + 1 = 2`).

The proof then splits on `ω(n₋)`, the number of distinct primes `p ∣ n` with `χ(p) = −1`:
`≥ 2` (then `Λ̃(n) = 0`), `= 1` (a single surviving term `f(n₊)·Λ(n₋)`), `= 0`
(then `n₊ = n` and the crude `Λ̃(n) ≤ f(n)·log n`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — local factors of `f = fChiArith` -/

/-- `f(p^e) = 1 + χ(p)` for `e ≥ 1` (`e = 0` gives `1`; here the exponent is positive so
    the truncated geometric sum is `χ(p)^0 + χ(p)^1`). -/
lemma fChiArith_primePow_pos {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) {e : ℕ} (he : e ≠ 0) :
    fChiArith χ (p ^ e) = 1 + chiRe χ p := by
  rw [fChiArith_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [gChi_primePow hp χ hsq]
  rw [← Finset.sum_filter]
  have hfilter : (range (e + 1)).filter (· < 2) = range 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilter, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]

/-- If a prime `p` with `χ(p) = −1` divides `a ≠ 0`, then `f(a) = 0`: the local factor
    `f(p^{v_p(a)}) = 1 + χ(p) = 0` kills the multiplicative factorization. -/
lemma fChiArith_eq_zero_of_dvd_neg {p a : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) (hneg : chiRe χ p = -1) (hpa : p ∣ a) (ha : a ≠ 0) :
    fChiArith χ a = 0 := by
  rw [(fChiArith_mult χ hsq).multiplicative_factorization (fChiArith χ) ha, Finsupp.prod]
  apply Finset.prod_eq_zero (i := p)
  · rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩
  · have hvp : a.factorization p ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hp ha hpa).ne'
    rw [fChiArith_primePow_pos hp χ hsq hvp, hneg]; norm_num

/-- On a number all of whose prime factors have `χ(p) = 1`, `f = 2^ω` (each local factor is
    `1 + 1 = 2`). -/
lemma fChiArith_eq_two_pow {m : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (hm : m ≠ 0) (hpos : ∀ p ∈ m.primeFactors, chiRe χ p = 1) :
    fChiArith χ m = (2 : ℝ) ^ m.primeFactors.card := by
  rw [(fChiArith_mult χ hsq).multiplicative_factorization (fChiArith χ) hm, Finsupp.prod]
  have hval : ∀ p ∈ m.factorization.support,
      fChiArith χ (p ^ m.factorization p) = (2 : ℝ) := by
    intro p hps
    have hpf : p ∈ m.primeFactors := by rwa [Nat.support_factorization] at hps
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hvp : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hps
    rw [fChiArith_primePow_pos hpp χ hsq hvp, hpos p hpf]; norm_num
  rw [Finset.prod_congr rfl hval, Finset.prod_const, Nat.support_factorization]

/-- The convolution reindexed over divisors: `Λ̃(n) = ∑_{a ∣ n} f(a)·Λ(n/a)`. -/
lemma LamTilde_eq_sum_div (χ : DirichletCharacter ℂ q) (n : ℕ) :
    LamTilde χ n = ∑ a ∈ n.divisors, fChiArith χ a * Λ (n / a) := by
  rw [LamTilde_eq_fChi_conv, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => fChiArith χ a * Λ b)]

/-! ## §1 — the prime signs of `n₊`, `n₋` -/

/-- Every prime dividing `n₊` has `χ(p) = 1`. -/
lemma nPlus_dvd_sign {χ : DirichletCharacter ℂ q} {n r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ nPlus χ n) : chiRe χ r = 1 := by
  classical
  rw [nPlus] at hdvd
  obtain ⟨p, hpf, hrp⟩ := (hr.prime.dvd_finsetProd_iff _).mp hdvd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hpf)
  have hrpp : r = p := (Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow hrp)
  subst hrpp
  exact (Finset.mem_filter.mp hpf).2

/-- Every prime dividing `n₋` has `χ(p) = −1`. -/
lemma nMinus_dvd_sign {χ : DirichletCharacter ℂ q} {n r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ nMinus χ n) : chiRe χ r = -1 := by
  classical
  rw [nMinus] at hdvd
  obtain ⟨p, hpf, hrp⟩ := (hr.prime.dvd_finsetProd_iff _).mp hdvd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hpf)
  have hrpp : r = p := (Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow hrp)
  subst hrpp
  exact (Finset.mem_filter.mp hpf).2

/-- The prime factors of `n₊` all have `χ = 1`. -/
lemma nPlus_sign {χ : DirichletCharacter ℂ q} {n p : ℕ} (hp : p ∈ (nPlus χ n).primeFactors) :
    chiRe χ p = 1 :=
  nPlus_dvd_sign (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-! ## §2 — the reduction to divisors of `n₊`

Since `f(a) = 0` whenever `a` carries a `χ = −1` prime, the convolution collapses onto
divisors of `n₊`: `Λ̃(n) = ∑_{a ∣ n₊} f(a)·Λ(n/a)`. -/

/-- **Reduction.** `Λ̃(n) = ∑_{a ∣ n₊} f(a)·Λ(n/a)` for `n` coprime to `q`. -/
lemma LamTilde_eq_sum_nPlus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) :
    LamTilde χ n = ∑ a ∈ (nPlus χ n).divisors, fChiArith χ a * Λ (n / a) := by
  classical
  have hfact := eq_nPlus_mul_nMinus χ hsq hn hcop
  have hnp : nPlus χ n ≠ 0 := by rintro h; rw [h, zero_mul] at hfact; exact hn hfact
  have hsub : (nPlus χ n).divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn ⟨nMinus χ n, hfact⟩
  rw [LamTilde_eq_sum_div]
  refine (Finset.sum_subset hsub ?_).symm
  intro a ha hanp
  suffices h0 : fChiArith χ a = 0 by rw [h0, zero_mul]
  have han : a ∣ n := Nat.dvd_of_mem_divisors ha
  by_contra hne
  apply hanp
  have hsign : ∀ p, p.Prime → p ∣ a → chiRe χ p = 1 := by
    intro p hp hpa
    have hpq : Nat.Coprime p q := Nat.Coprime.coprime_dvd_left (hpa.trans han) hcop
    rcases chiRe_eq_one_or_neg_one χ hsq hpq with h1 | h1
    · exact h1
    · exact absurd (fChiArith_eq_zero_of_dvd_neg hp χ hsq h1 hpa
        (Nat.pos_of_mem_divisors ha).ne') hne
  have hcopa : Nat.Coprime a (nMinus χ n) := by
    by_contra hnc
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnc
    have h1 := hsign p hp (hpg.trans (Nat.gcd_dvd_left _ _))
    have h2 := nMinus_dvd_sign hp (hpg.trans (Nat.gcd_dvd_right _ _))
    rw [h1] at h2; norm_num at h2
  have hdvd : a ∣ nPlus χ n := hcopa.dvd_of_dvd_mul_right (hfact ▸ han)
  exact Nat.mem_divisors.mpr ⟨hdvd, hnp⟩

/-! ## §3 — structural and arithmetic helpers -/

/-- `n₊` is a product of prime powers, hence positive. -/
lemma nPlus_pos (χ : DirichletCharacter ℂ q) (n : ℕ) : 0 < nPlus χ n := by
  classical
  rw [nPlus]; refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos _

/-- `n₋` is a product of prime powers, hence positive. -/
lemma nMinus_pos (χ : DirichletCharacter ℂ q) (n : ℕ) : 0 < nMinus χ n := by
  classical
  rw [nMinus]; refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos _

/-- For `a ∣ n₊`, `n / a = (n₊ / a)·n₋`. -/
lemma nDiv_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime n q) {a : ℕ} (ha : a ∣ nPlus χ n) :
    n / a = nPlus χ n / a * nMinus χ n := by
  have hfact := eq_nPlus_mul_nMinus χ hsq hn hcop
  have ha0 : a ≠ 0 := fun h => (nPlus_pos χ n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  have hmul : n = nPlus χ n / a * nMinus χ n * a := by
    rw [mul_right_comm, Nat.div_mul_cancel ha]; exact hfact
  exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero ha0) hmul

/-- `n₋ ≠ 1` forces `f(n₋) = 0` (`n₋` carries a `χ = −1` prime). -/
lemma fChiSum_nMinus_eq_zero (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hM : nMinus χ n ≠ 1) : fChiSum χ (nMinus χ n) = 0 := by
  obtain ⟨p, hp, hpM⟩ := Nat.exists_prime_and_dvd hM
  rw [← fChiArith_eq_fChiSum]
  exact fChiArith_eq_zero_of_dvd_neg hp χ hsq (nMinus_dvd_sign hp hpM) hpM (nMinus_pos χ n).ne'

/-- `n₋ ≠ 1` forces `f(n) = 0` too (that `χ = −1` prime divides `n`). -/
lemma fChiSum_n_eq_zero (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hM : nMinus χ n ≠ 1) : fChiSum χ n = 0 := by
  obtain ⟨p, hp, hpM⟩ := Nat.exists_prime_and_dvd hM
  have hMn : nMinus χ n ∣ n :=
    ⟨nPlus χ n, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hn hcop⟩
  rw [← fChiArith_eq_fChiSum]
  exact fChiArith_eq_zero_of_dvd_neg hp χ hsq (nMinus_dvd_sign hp hpM) (hpM.trans hMn) hn

/-- `1 ≤ f(n₊)` (a power of `2`). -/
lemma one_le_fChiSum_nPlus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    1 ≤ fChiSum χ (nPlus χ n) := by
  rw [← fChiArith_eq_fChiSum,
      fChiArith_eq_two_pow χ hsq (nPlus_pos χ n).ne' (fun p hp => nPlus_sign hp)]
  exact one_le_pow₀ (by norm_num)

/-- `n₊ ≠ 1` forces `2 ≤ f(n₊)` (`f(n₊) = 2^{ω(n₊)}` with `ω(n₊) ≥ 1`). -/
lemma two_le_fChiSum_nPlus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hP : nPlus χ n ≠ 1) : 2 ≤ fChiSum χ (nPlus χ n) := by
  rw [← fChiArith_eq_fChiSum,
      fChiArith_eq_two_pow χ hsq (nPlus_pos χ n).ne' (fun p hp => nPlus_sign hp)]
  have hcard : 1 ≤ (nPlus χ n).primeFactors.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro h; rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
    · exact (nPlus_pos χ n).ne' h0
    · exact hP h1
  calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (nPlus χ n).primeFactors.card := pow_le_pow_right₀ (by norm_num) hcard

/-- Monotonicity of `f` under divisibility on `χ = +1` numbers: `a ∣ n₊ → f(a) ≤ f(n₊)`. -/
lemma fChiArith_le_of_dvd_nPlus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n a : ℕ}
    (ha : a ∣ nPlus χ n) : fChiArith χ a ≤ fChiArith χ (nPlus χ n) := by
  have ha0 : a ≠ 0 := fun h => (nPlus_pos χ n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  rw [fChiArith_eq_two_pow χ hsq ha0 (fun p hp =>
        nPlus_dvd_sign (Nat.prime_of_mem_primeFactors hp)
          ((Nat.dvd_of_mem_primeFactors hp).trans ha)),
      fChiArith_eq_two_pow χ hsq (nPlus_pos χ n).ne' (fun p hp => nPlus_sign hp)]
  exact pow_le_pow_right₀ (by norm_num)
    (Finset.card_le_card (Nat.primeFactors_mono ha (nPlus_pos χ n).ne'))

/-- Two distinct primes ⇒ not a prime power (via a divisor with `≥ 2` prime factors). -/
lemma not_isPrimePow_of_two_le_card {u m : ℕ} (hm0 : m ≠ 0) (hdvd : u ∣ m)
    (hu : 2 ≤ u.primeFactors.card) : ¬ IsPrimePow m := by
  rw [isPrimePow_iff_card_primeFactors_eq_one]
  have : u.primeFactors.card ≤ m.primeFactors.card :=
    Finset.card_le_card (Nat.primeFactors_mono hdvd hm0)
  omega

/-- A product of two coprime numbers `> 1` is never a prime power. -/
lemma not_isPrimePow_mul_coprime {u v : ℕ} (hcop : Nat.Coprime u v) (hu : u ≠ 1) (hv : v ≠ 1)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : ¬ IsPrimePow (u * v) := by
  have hu1 : 1 ≤ u.primeFactors.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro h; rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
    · exact hu0 h0
    · exact hu h1
  have hv1 : 1 ≤ v.primeFactors.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro h; rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
    · exact hv0 h0
    · exact hv h1
  rw [isPrimePow_iff_card_primeFactors_eq_one, hcop.primeFactors_mul,
      Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  omega

/-! ## §4 — the three cases on `ω(n₋)` -/

/-- **Case `ω(n₋) ≥ 2`.** Every term of the reduced sum vanishes (each `n/a` inherits `n₋`'s
    two distinct primes, so is not a prime power), hence `Λ̃(n) = 0`. -/
lemma LamTilde_eq_zero_of_two_le_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hM : 2 ≤ (nMinus χ n).primeFactors.card) :
    LamTilde χ n = 0 := by
  rw [LamTilde_eq_sum_nPlus χ hsq hn hcop]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hadvd : a ∣ nPlus χ n := Nat.dvd_of_mem_divisors ha
  have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (nPlus_pos χ n)
  have hna : n / a = nPlus χ n / a * nMinus χ n := nDiv_eq χ hsq hn hcop hadvd
  have hPa_pos : 0 < nPlus χ n / a := Nat.div_pos (Nat.le_of_dvd (nPlus_pos χ n) hadvd) ha_pos
  have hna0 : n / a ≠ 0 := by rw [hna]; exact Nat.mul_ne_zero hPa_pos.ne' (nMinus_pos χ n).ne'
  have hMdvd : nMinus χ n ∣ n / a := by rw [hna]; exact dvd_mul_left _ _
  have hnp : ¬ IsPrimePow (n / a) := not_isPrimePow_of_two_le_card hna0 hMdvd hM
  rw [vonMangoldt_eq_zero_iff.mpr hnp, mul_zero]

/-- **Case `ω(n₋) = 1`.** `n₋` is a prime power; the only surviving term is `a = n₊`,
    giving `Λ̃(n) = f(n₊)·Λ(n₋)`. -/
lemma LamTilde_eq_single_of_card_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hM1 : IsPrimePow (nMinus χ n)) :
    LamTilde χ n = fChiSum χ (nPlus χ n) * Λ (nMinus χ n) := by
  rw [LamTilde_eq_sum_nPlus χ hsq hn hcop,
      Finset.sum_eq_single_of_mem (nPlus χ n)
        (Nat.mem_divisors_self _ (nPlus_pos χ n).ne') ?_]
  · rw [fChiArith_eq_fChiSum, nDiv_eq χ hsq hn hcop dvd_rfl, Nat.div_self (nPlus_pos χ n), one_mul]
  · intro a ha hane
    have hadvd : a ∣ nPlus χ n := Nat.dvd_of_mem_divisors ha
    have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (nPlus_pos χ n)
    have hPa_pos : 0 < nPlus χ n / a := Nat.div_pos (Nat.le_of_dvd (nPlus_pos χ n) hadvd) ha_pos
    have hPa1 : nPlus χ n / a ≠ 1 := by
      intro h; apply hane
      have hh := Nat.mul_div_cancel' hadvd
      rw [h, mul_one] at hh; exact hh
    have hcopPaM : Nat.Coprime (nPlus χ n / a) (nMinus χ n) :=
      Nat.Coprime.coprime_dvd_left ⟨a, (Nat.div_mul_cancel hadvd).symm⟩ (coprime_nPlus_nMinus χ n)
    have hnp : ¬ IsPrimePow (n / a) := by
      rw [nDiv_eq χ hsq hn hcop hadvd]
      exact not_isPrimePow_mul_coprime hcopPaM hPa1
        (fun h => not_isPrimePow_one (h ▸ hM1)) hPa_pos.ne' (nMinus_pos χ n).ne'
    rw [vonMangoldt_eq_zero_iff.mpr hnp, mul_zero]

/-- **Case `ω(n₋) = 0`** (i.e. `n₋ = 1`, `n₊ = n`). The crude divisor-monotone bound:
    `f(a) ≤ f(n)` for `a ∣ n`, and `∑_{a ∣ n} Λ(n/a) = log n`. -/
lemma LamTilde_le_of_nMinus_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hM1 : nMinus χ n = 1) :
    LamTilde χ n ≤ fChiSum χ n * Real.log n := by
  have hPn : nPlus χ n = n := by
    have h := eq_nPlus_mul_nMinus χ hsq hn hcop; rw [hM1, mul_one] at h; exact h.symm
  rw [LamTilde_eq_sum_nPlus χ hsq hn hcop]
  calc ∑ a ∈ (nPlus χ n).divisors, fChiArith χ a * Λ (n / a)
      ≤ ∑ a ∈ (nPlus χ n).divisors, fChiArith χ (nPlus χ n) * Λ (n / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact mul_le_mul_of_nonneg_right
          (fChiArith_le_of_dvd_nPlus χ hsq (Nat.dvd_of_mem_divisors ha)) vonMangoldt_nonneg
    _ = fChiSum χ n * Real.log n := by
        rw [← Finset.mul_sum, fChiArith_eq_fChiSum, hPn,
            Nat.sum_div_divisors n (fun d => Λ d), vonMangoldt_sum]

/-! ## §5 — Heath-Brown Lemma 1(c) -/

/-- **Lemma 1(c).** For a real character `χ` (`χ² = 1`) and `n` coprime to `q`,
    `Λ̃(n) − Λ(n) ≤ 2·( f(n)·log n + (f(n₊) − 1)·Λ(n₋) )`.

    The proof splits on `ω(n₋)`, the number of distinct primes `p ∣ n` with `χ(p) = −1`:
    `≥ 2` gives `Λ̃(n) = 0`; `= 1` gives the single surviving term `f(n₊)·Λ(n₋)` (with the
    `f(n₊) ≥ 2` slack absorbing it, or `n = n₋` making both sides zero); `= 0` gives the
    crude `Λ̃(n) ≤ f(n)·log n`. -/
theorem LamTilde_sub_vonMangoldt_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) :
    LamTilde χ n - Λ n ≤
      2 * (fChiSum χ n * Real.log n + (fChiSum χ (nPlus χ n) - 1) * Λ (nMinus χ n)) := by
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hFn_nonneg : 0 ≤ fChiSum χ n := by
    rw [← fChiArith_eq_fChiSum]; exact fChiArith_nonneg χ hsq n
  have hLM_nonneg : 0 ≤ Λ (nMinus χ n) := vonMangoldt_nonneg
  have hLn_nonneg : 0 ≤ Λ n := vonMangoldt_nonneg
  have hFP1 : 0 ≤ fChiSum χ (nPlus χ n) - 1 := by linarith [one_le_fChiSum_nPlus χ hsq n]
  have hR_nonneg : 0 ≤ 2 * (fChiSum χ n * Real.log n
      + (fChiSum χ (nPlus χ n) - 1) * Λ (nMinus χ n)) :=
    mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg hFn_nonneg hlogn) (mul_nonneg hFP1 hLM_nonneg))
  rcases lt_trichotomy (nMinus χ n).primeFactors.card 1 with hc | hc | hc
  · -- `ω(n₋) = 0`: `n₋ = 1`
    have hcard0 : (nMinus χ n).primeFactors.card = 0 := by omega
    have hM1 : nMinus χ n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard0) with h | h
      · exact absurd h (nMinus_pos χ n).ne'
      · exact h
    rw [hM1, vonMangoldt_apply_one, mul_zero, add_zero]
    linarith [LamTilde_le_of_nMinus_one χ hsq hn hcop hM1, mul_nonneg hFn_nonneg hlogn]
  · -- `ω(n₋) = 1`: `n₋` is a prime power
    have hM1 : IsPrimePow (nMinus χ n) := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    have hMne1 : nMinus χ n ≠ 1 := by intro h; rw [h] at hc; simp at hc
    have hLT := LamTilde_eq_single_of_card_one χ hsq hn hcop hM1
    by_cases hP1 : nPlus χ n = 1
    · have hFP1' : fChiSum χ (nPlus χ n) = 1 := by
        rw [hP1, ← fChiArith_eq_fChiSum]; exact (fChiArith_mult χ hsq).map_one
      have hnM : n = nMinus χ n := by
        have h := eq_nPlus_mul_nMinus χ hsq hn hcop; rw [hP1, one_mul] at h; exact h
      have hLn : Λ n = Λ (nMinus χ n) := by rw [← hnM]
      have hFn0 : fChiSum χ n = 0 := fChiSum_n_eq_zero χ hsq hn hcop hMne1
      rw [hLT, hFP1', hLn, hFn0]
      exact le_of_eq (by ring)
    · have hFn0 : fChiSum χ n = 0 := fChiSum_n_eq_zero χ hsq hn hcop hMne1
      have hLn0 : Λ n = 0 := by
        rw [vonMangoldt_eq_zero_iff, eq_nPlus_mul_nMinus χ hsq hn hcop]
        exact not_isPrimePow_mul_coprime (coprime_nPlus_nMinus χ n) hP1 hMne1
          (nPlus_pos χ n).ne' (nMinus_pos χ n).ne'
      rw [hLT, hLn0, sub_zero, hFn0, zero_mul, zero_add]
      nlinarith [mul_nonneg (sub_nonneg.mpr (two_le_fChiSum_nPlus χ hsq hP1)) hLM_nonneg,
        hLM_nonneg]
  · -- `ω(n₋) ≥ 2`: `Λ̃(n) = 0`
    rw [LamTilde_eq_zero_of_two_le_card χ hsq hn hcop hc]
    linarith [hR_nonneg, hLn_nonneg]

end Salt.HB
