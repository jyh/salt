/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.CongruenceCounting
import Salt.Brun.SelbergPort
import Salt.Maynard.PhiAtom
import Salt.Maynard.PpSums

/-!
# ShiuSieve — the rough-count-in-AP pole (S1)

Shiu's Lemma-2 analog: an upper bound for the number of integers `m ∈ [1,y]` in a
fixed residue class `m ≡ a (mod q)` with `(a,q)=1` that have no prime factor `≤ t`.
Via the landed general Selberg `Λ²` bound `Salt.SelbergPort.selberg_bound_simple`,
instantiated for the arithmetic-progression weight.

Main result:

`rough_count_in_ap_le : ∃ C₀ > 0, ∀ y q a t, 1 ≤ q → 2 ≤ t → Nat.Coprime a q →`
`  card {m ∈ [1,y] : m%q=a ∧ ∀ p prime ≤ t, ¬p∣m} ≤ C₀·(y/φ(q)/log t + t³)`.

Sub-deliverables:
* **S1a** — the AP `SelbergSieve` instance (`apSieve`): density `ν(d) = 1/d`,
  `totalMass = y/q`, remainder `|R_d| ≤ 1` via the CRT single-class count
  `_root_.congCount_bound`.
* **S1b** — the `φ`-saving lower bound on the Selberg bounding sum, via
  `Salt.Maynard.phiAtom_lower` plus a uniform coprime-part factorization.
* **S1c** — the remainder sum `Σ_{d ≤ D} 3^ω(d) ≤ D(1+log D)²` from
  `Salt.Maynard.sum_k_pow_omega_le`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

namespace Salt.Maynard

/-! ## S1a — the arithmetic-progression density and Selberg sieve instance -/

/-- The AP sieve density `ν(d) = 1/d` as an arithmetic function (`ν 0 = 0`).
Each prime `p ∤ q` sifts out `1/p` of the residue class `m ≡ a (q)` by CRT. -/
noncomputable def apNu : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ)⁻¹, by simp⟩

@[simp] lemma apNu_apply (d : ℕ) : apNu d = (d : ℝ)⁻¹ := rfl

/-- `ν(d) = 1/d` is (completely) multiplicative. -/
lemma apNu_mult : apNu.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [apNu_apply, Nat.cast_mul, mul_inv]

lemma apNu_pos (p : ℕ) (hp : p.Prime) : 0 < apNu p := by
  rw [apNu_apply]
  have : (0 : ℝ) < p := by exact_mod_cast hp.pos
  positivity

lemma apNu_lt_one (p : ℕ) (hp : p.Prime) : apNu p < 1 := by
  rw [apNu_apply]
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact inv_lt_one_of_one_lt₀ this

/-- **S1a.** The Selberg sieve for the residue class `m ≡ a (mod q)` in `[1,y]`,
sifting by the primes dividing the squarefree modulus `P`.  The weight is the
indicator of the class; the density is `ν(d) = 1/d`; `totalMass = y/q`. -/
noncomputable def apSieve (y q a P : ℕ) (L : ℝ) (hP : Squarefree P) (hL : 1 ≤ L) :
    SelbergSieve where
  support := Finset.Icc 1 y
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun n => if n % q = a then 1 else 0
  weights_nonneg := fun n => by split_ifs <;> norm_num
  totalMass := (y : ℝ) / q
  nu := apNu
  nu_mult := apNu_mult
  nu_pos_of_prime := fun p hp _ => apNu_pos p hp
  nu_lt_one_of_prime := fun p hp _ => apNu_lt_one p hp
  level := L
  one_le_level := hL

variable {y q a P : ℕ} {L : ℝ} {hP : Squarefree P} {hL : 1 ≤ L}

@[simp] lemma apSieve_prodPrimes : (apSieve y q a P L hP hL).prodPrimes = P := rfl
@[simp] lemma apSieve_level : (apSieve y q a P L hP hL).level = L := rfl
@[simp] lemma apSieve_totalMass : (apSieve y q a P L hP hL).totalMass = (y : ℝ) / q := rfl
@[simp] lemma apSieve_nu : (apSieve y q a P L hP hL).nu = apNu := rfl

lemma apSieve_weights (n : ℕ) :
    (apSieve y q a P L hP hL).weights n = if n % q = a then 1 else 0 := rfl

/-- The multiplicity count of the AP sieve at `d` is the count of `n ∈ [1,y]` with
`d ∣ n` and `n ≡ a (mod q)`. -/
lemma apSieve_multSum (d : ℕ) :
    (apSieve y q a P L hP hL).multSum d
      = (((Finset.Icc 1 y).filter (fun n => d ∣ n ∧ n % q = a)).card : ℝ) := by
  have hsupp : (apSieve y q a P L hP hL).support = Finset.Icc 1 y := rfl
  rw [BoundingSieve.multSum, hsupp, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n _
  rw [apSieve_weights]
  by_cases hd : d ∣ n <;> by_cases hm : n % q = a <;> simp [hd, hm]

/-- **S1a (remainder).** For `d ∣ P` with `(P,q)=1` and `a < q`, the AP sieve
remainder is bounded by `1` — the CRT single-class count in an interval. -/
lemma apSieve_rem_abs_le (hq : 1 ≤ q) (ha : a < q) (hPq : Nat.Coprime P q)
    {d : ℕ} (hd : d ∣ P) : |(apSieve y q a P L hP hL).rem d| ≤ 1 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hP.ne_zero (Nat.eq_zero_of_zero_dvd hd)
  have hq0 : 0 < q := hq
  have hdq0 : 0 < d * q := Nat.mul_pos (Nat.pos_of_ne_zero hd0) hq0
  have hdq : Nat.Coprime d q := Nat.Coprime.coprime_dvd_left hd hPq
  -- CRT residue `r` with `r ≡ 0 (d)`, `r ≡ a (q)`.
  set cr := Nat.chineseRemainder hdq 0 a with hcr
  set k := cr.1 with hk
  obtain ⟨hk_d, hk_q⟩ := cr.2
  set r := k % (d * q) with hrdef
  have hr_lt : r < d * q := Nat.mod_lt _ hdq0
  have hrr : r % (d * q) = r := Nat.mod_eq_of_lt hr_lt
  have hr_d : r ≡ 0 [MOD d] :=
    ((Nat.mod_modEq k (d * q)).of_dvd (dvd_mul_right d q)).trans hk_d
  have hr_q : r ≡ a [MOD q] :=
    ((Nat.mod_modEq k (d * q)).of_dvd (dvd_mul_left q d)).trans hk_q
  -- the pointwise predicate equivalence
  have hpred : ∀ n, (d ∣ n ∧ n % q = a) ↔ n % (d * q) = r := by
    intro n
    have hmod : n % (d * q) = r ↔ n ≡ r [MOD d * q] := by
      constructor
      · intro h; exact h.trans hrr.symm
      · intro h; have h2 : n % (d * q) = r % (d * q) := h; rwa [hrr] at h2
    rw [hmod, ← Nat.modEq_and_modEq_iff_modEq_mul hdq]
    constructor
    · rintro ⟨hdn, hnq⟩
      refine ⟨(Nat.modEq_zero_iff_dvd.mpr hdn).trans hr_d.symm, ?_⟩
      have hna : n ≡ a [MOD q] := hnq.trans (Nat.mod_eq_of_lt ha).symm
      exact hna.trans hr_q.symm
    · rintro ⟨hnd, hnq⟩
      refine ⟨Nat.modEq_zero_iff_dvd.mp (hnd.trans hr_d), ?_⟩
      have h3 : n % q = a % q := hnq.trans hr_q
      rwa [Nat.mod_eq_of_lt ha] at h3
  -- identify multSum with a congCount, apply the bound
  have hms : (apSieve y q a P L hP hL).multSum d
      = (_root_.congCount (d * q) {r} y : ℝ) := by
    rw [apSieve_multSum]
    congr 1
    change ((Finset.Icc 1 y).filter (fun n => d ∣ n ∧ n % q = a)).card
      = ((Finset.Icc 1 y).filter (fun n => n % (d * q) ∈ ({r} : Finset ℕ))).card
    congr 1
    apply Finset.filter_congr
    intro n _
    rw [Finset.mem_singleton]
    exact hpred n
  have hsr : ({r} : Finset ℕ) ∩ Finset.range (d * q) = {r} :=
    Finset.singleton_inter_of_mem (Finset.mem_range.mpr hr_lt)
  have hbound := _root_.congCount_bound (d := d * q) (S := {r}) hdq0 y
  rw [hsr, Finset.card_singleton] at hbound
  -- convert the congCount bound into the rem bound
  rw [BoundingSieve.rem, hms, apSieve_nu, apSieve_totalMass, apNu_apply]
  have hcast : (d : ℝ)⁻¹ * ((y : ℝ) / q)
      = (y : ℝ) * ((1 : ℕ) : ℝ) / ((d * q : ℕ) : ℝ) := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    field_simp
  rw [hcast]
  simpa using hbound

/-! ## S1c — the remainder (error) sum -/

/-- `ω n = |primeFactors n|` (bridge between the Selberg `ω` and `PpSums`). -/
lemma omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- **S1c.** The Selberg error sum for the AP sieve (truncated at `level = L`),
bounded by the polylogarithmic `Σ_{d ≤ D} 3^ω(d) ≤ D(1+log D)²` once every
`d ∣ P` with `d ≤ L` is `≤ D`. -/
lemma apSieve_errSum_le (hq : 1 ≤ q) (ha : a < q) (hPq : Nat.Coprime P q)
    (D : ℕ) (hDbound : ∀ d, d ∣ P → (d : ℝ) ≤ L → d ≤ D) :
    ∑ d ∈ P.divisors,
        (if (d : ℝ) ≤ L then (3 : ℝ) ^ ω d * |(apSieve y q a P L hP hL).rem d| else 0)
      ≤ (D : ℝ) * (1 + Real.log D) ^ 2 := by
  have step1 : ∑ d ∈ P.divisors,
        (if (d : ℝ) ≤ L then (3 : ℝ) ^ ω d * |(apSieve y q a P L hP hL).rem d| else 0)
      ≤ ∑ d ∈ P.divisors,
        (if (d : ℝ) ≤ L then (3 : ℝ) ^ d.primeFactors.card else 0) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Nat.mem_divisors] at hd
    split_ifs with hL'
    · rw [omega_eq_card]
      exact mul_le_of_le_one_right (by positivity) (apSieve_rem_abs_le hq ha hPq hd.1)
    · exact le_refl _
  have step2 : ∑ d ∈ P.divisors,
        (if (d : ℝ) ≤ L then (3 : ℝ) ^ d.primeFactors.card else 0)
      ≤ ∑ d ∈ Finset.Icc 1 D, (3 : ℝ) ^ d.primeFactors.card := by
    rw [← Finset.sum_filter]
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
    _ ≤ (D : ℝ) * (1 + Real.log D) ^ 2 := step3

/-! ## The concrete sifting modulus `roughP q t = ∏_{p ≤ t, p ∤ q} p` -/

/-- A finite product of distinct primes is squarefree (copied utility). -/
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

/-- The set of primes `≤ t` not dividing `q`. -/
def roughPrimes (q t : ℕ) : Finset ℕ :=
  (Finset.range (t + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q)

/-- The sifting modulus: the product of all primes `≤ t` not dividing `q`. -/
def roughP (q t : ℕ) : ℕ := ∏ p ∈ roughPrimes q t, p

lemma mem_roughPrimes {q t p : ℕ} :
    p ∈ roughPrimes q t ↔ p ≤ t ∧ p.Prime ∧ ¬ p ∣ q := by
  rw [roughPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

lemma roughP_squarefree (q t : ℕ) : Squarefree (roughP q t) :=
  prod_primes_squarefree (fun _p hp => (mem_roughPrimes.mp hp).2.1)

lemma roughP_coprime (q t : ℕ) : Nat.Coprime (roughP q t) q := by
  apply Nat.Coprime.prod_left
  intro p hp
  obtain ⟨_, hpp, hpq⟩ := mem_roughPrimes.mp hp
  exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpq

/-- Any prime dividing `roughP q t` is `≤ t` and does not divide `q`. -/
lemma prime_dvd_roughP {q t p : ℕ} (hp : p.Prime) (hdvd : p ∣ roughP q t) :
    p ≤ t ∧ ¬ p ∣ q := by
  rw [roughP] at hdvd
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  obtain ⟨hrt, hrp, hrq⟩ := mem_roughPrimes.mp hr
  have : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr
  subst this
  exact ⟨hrt, hrq⟩

/-- Squarefree `l ≤ t` coprime to `q` divides `roughP q t`. -/
lemma dvd_roughP_of_squarefree {q t l : ℕ} (hl : Squarefree l) (hlq : Nat.Coprime l q)
    (hlt : l ≤ t) : l ∣ roughP q t := by
  have hsub : l.primeFactors ⊆ roughPrimes q t := by
    intro p hp
    obtain ⟨hpp, hpl, _⟩ := Nat.mem_primeFactors.mp hp
    rw [mem_roughPrimes]
    refine ⟨le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hl.ne_zero) hpl) hlt, hpp, ?_⟩
    exact fun hpq => (Nat.Prime.coprime_iff_not_dvd hpp).mp
      (Nat.Coprime.coprime_dvd_left hpl hlq) hpq
  calc l = ∏ p ∈ l.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hl).symm
    _ ∣ ∏ p ∈ roughPrimes q t, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
    _ = roughP q t := rfl

/-! ## The sifted sum counts the rough numbers in the class -/

variable {t : ℕ}

/-- The sifted sum counts `n ∈ [1,y]` with `n ≡ a (q)` coprime to `P`. -/
lemma apSieve_siftedSum :
    (apSieve y q a P L hP hL).siftedSum
      = (((Finset.Icc 1 y).filter (fun n => Nat.Coprime P n ∧ n % q = a)).card : ℝ) := by
  have hsupp : (apSieve y q a P L hP hL).support = Finset.Icc 1 y := rfl
  rw [BoundingSieve.siftedSum]
  change (∑ n ∈ Finset.Icc 1 y,
      if Nat.Coprime P n then (if n % q = a then (1 : ℝ) else 0) else 0) = _
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hc : Nat.Coprime P n <;> by_cases hm : n % q = a <;> simp [hc, hm]

/-! ## S1b — the uniform coprime-part factorization and the `φ`-saving bound

The classical lower bound `Σ_{l ∣ P, l ≤ t} 1/φ(l) ≥ c·(φ(q)/q)·log t` needs a
version of the coprime-harmonic bound that is uniform in `q` (valid even when
`q > t`, where `copHarmonic_lower`'s `− log q` loss is fatal).  We prove it via
the unique factorization `n = (coprime-to-q part) · (q-smooth part)`. -/

/-- The largest divisor of `n` coprime to `q` (product of `n`'s prime powers at
primes not dividing `q`). -/
def coPart (q n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p ^ (n.factorization p)

/-- The `q`-smooth part of `n` (product of `n`'s prime powers at primes dividing `q`). -/
def qPart (q n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∣ q), p ^ (n.factorization p)

lemma coPart_mul_qPart {q n : ℕ} (hn : n ≠ 0) : coPart q n * qPart q n = n := by
  have hself : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hn
  rw [coPart, qPart, mul_comm,
    Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ∣ q)]
  exact hself

lemma coPart_coprime (q n : ℕ) : Nat.Coprime (coPart q n) q := by
  rw [coPart]
  apply Nat.Coprime.prod_left
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hp.2)

lemma qPart_prime_dvd {q n p : ℕ} (hp : p.Prime) (hdvd : p ∣ qPart q n) : p ∣ q := by
  rw [qPart] at hdvd
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  rw [Finset.mem_filter] at hr
  have := hp.dvd_of_dvd_pow hpr
  exact (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hr.1)).mp this ▸ hr.2

lemma coPart_pos {q n : ℕ} (hn : n ≠ 0) : 0 < coPart q n := by
  have := coPart_mul_qPart (q := q) hn
  rcases Nat.eq_zero_or_pos (coPart q n) with h | h
  · rw [h, zero_mul] at this; exact absurd this.symm hn
  · exact h

lemma qPart_pos {q n : ℕ} (hn : n ≠ 0) : 0 < qPart q n := by
  have := coPart_mul_qPart (q := q) hn
  rcases Nat.eq_zero_or_pos (qPart q n) with h | h
  · rw [h, mul_zero] at this; exact absurd this.symm hn
  · exact h

lemma coPart_le {q n : ℕ} (hn : n ≠ 0) : coPart q n ≤ n := by
  have h := coPart_mul_qPart (q := q) hn
  calc coPart q n ≤ coPart q n * qPart q n := Nat.le_mul_of_pos_right _ (qPart_pos hn)
    _ = n := h

lemma qPart_le {q n : ℕ} (hn : n ≠ 0) : qPart q n ≤ n := by
  have h := coPart_mul_qPart (q := q) hn
  calc qPart q n ≤ coPart q n * qPart q n := Nat.le_mul_of_pos_left _ (coPart_pos hn)
    _ = n := h

/-- `q/φ(q) = ∏_{p ∣ q} (1 - 1/p)⁻¹` (the Euler ratio). -/
lemma qPhi_prod {q : ℕ} (hq : 1 ≤ q) :
    ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ = (q : ℝ) / (Nat.totient q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : (Nat.totient q : ℚ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors q
  set S := ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) with hSdef
  have hphi : (Nat.totient q : ℝ) = (q : ℝ) * S := by
    have := congrArg (Rat.cast : ℚ → ℝ) hQ
    push_cast at this
    exact this
  have hne : ∀ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    intro h; linarith [h]
  have hSpos : (0 : ℝ) < S := by
    rw [hSdef]; apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have hTS : (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) * S = 1 := by
    rw [hSdef, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    exact inv_mul_cancel₀ (hne p hp)
  rw [hphi, eq_div_iff (by positivity : (q : ℝ) * S ≠ 0),
    mul_comm (q : ℝ) S, ← mul_assoc, hTS, one_mul]

/-- **S1c-helper.** The `q`-smooth harmonic sum (over `b < x` all of whose prime
factors divide `q`) is at most `q/φ(q)` — the truncated Euler product. -/
lemma qsmoothSum_le {q : ℕ} (hq : 1 ≤ q) (x : ℕ) :
    ∑ b ∈ (Finset.range x).filter (fun b => 1 ≤ b ∧ ∀ p ∈ b.primeFactors, p ∣ q),
        (1 : ℝ) / b ≤ (q : ℝ) / (Nat.totient q) := by
  classical
  set F := (Finset.range x).filter (fun b => 1 ≤ b ∧ ∀ p ∈ b.primeFactors, p ∣ q)
    with hFdef
  have hqz : q ≠ 0 := by omega
  have hF0 : ∀ b ∈ F, b ≠ 0 := by
    intro b hb
    rw [hFdef, Finset.mem_filter] at hb
    omega
  have hpf_sub : ∀ b ∈ F, b.primeFactors ⊆ q.primeFactors := by
    intro b hb p hp
    rw [hFdef, Finset.mem_filter] at hb
    obtain ⟨hpp, hpb, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpp, hb.2.2 p hp, hqz⟩
  let e : ℕ → (∀ p ∈ q.primeFactors, ℕ) := fun b p _ => b.factorization p
  have hval : ∀ b ∈ F, (1 : ℝ) / b
      = ∏ p ∈ q.primeFactors.attach,
        (((p : ℕ) : ℝ))⁻¹ ^ (b.factorization (p : ℕ)) := by
    intro b hb
    have hb0 := hF0 b hb
    rw [one_div, inv_eq_prod_primeFactors hb0,
      Finset.prod_subset (hpf_sub b hb) (fun p hpq hpnb => by
        rw [Nat.factorization_eq_zero_of_not_dvd (fun hpb => hpnb
          (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpq, hpb, hb0⟩)), pow_zero]),
      ← Finset.prod_attach]
  have hinj : Set.InjOn e ↑F := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    apply Nat.eq_of_factorization_eq (hF0 a ha) (hF0 b hb)
    intro p
    by_cases hp : p ∈ q.primeFactors
    · exact congrFun (congrFun hab p) hp
    · have hqa : a.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact fun h => hp (hpf_sub a ha h)
      have hqb : b.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact fun h => hp (hpf_sub b hb h)
      rw [hqa, hqb]
  have hsub : F.image e ⊆ q.primeFactors.pi (fun _ => Finset.Icc 0 x) := by
    intro g hg
    rw [Finset.mem_image] at hg
    obtain ⟨b, hbF, rfl⟩ := hg
    have hb0 := hF0 b hbF
    have hbx : b < x := by rw [hFdef, Finset.mem_filter, Finset.mem_range] at hbF; exact hbF.1
    rw [Finset.mem_pi]
    intro p hp
    change b.factorization p ∈ Finset.Icc 0 x
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, le_of_lt (lt_of_lt_of_le (Nat.factorization_lt p hb0) (le_of_lt hbx))⟩
  calc ∑ b ∈ F, (1 : ℝ) / b
      = ∑ g ∈ F.image e,
          ∏ p ∈ q.primeFactors.attach, (((p : ℕ) : ℝ))⁻¹ ^ (g (p : ℕ) p.2) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun b hb => hval b hb)
    _ ≤ ∑ g ∈ q.primeFactors.pi (fun _ => Finset.Icc 0 x),
          ∏ p ∈ q.primeFactors.attach, (((p : ℕ) : ℝ))⁻¹ ^ (g (p : ℕ) p.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro g _ _
        exact Finset.prod_nonneg (fun p _ => by positivity)
    _ = ∏ p ∈ q.primeFactors, ∑ j ∈ Finset.Icc 0 x, ((p : ℝ))⁻¹ ^ j :=
        (Finset.prod_sum q.primeFactors (fun _ => Finset.Icc 0 x)
          (fun p j => ((p : ℝ))⁻¹ ^ j)).symm
    _ ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
        apply Finset.prod_le_prod
        · intro p _
          exact Finset.sum_nonneg (fun j _ => by positivity)
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have hsplit : Finset.Icc 0 x = insert 0 (Finset.Icc 1 x) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit, Finset.sum_insert (by simp), pow_zero]
          have hgeo := geom_inv_bound hpp x
          have hstep : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
          have heq : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + ((p : ℝ) - 1)⁻¹ := by
            rw [hstep, inv_div]; field_simp; ring
          rw [heq]; linarith [hgeo]
    _ = (q : ℝ) / (Nat.totient q) := qPhi_prod hq

/-- **S1b (F1).** The coprime-part factorization: the full harmonic sum is at most
the product of the coprime-to-`q` harmonic sum and the `q`-smooth harmonic sum. -/
lemma coprime_factor_le (q x : ℕ) :
    (∑ n ∈ Finset.range x, (1 : ℝ) / n)
      ≤ (∑ a ∈ (Finset.range x).filter (fun a => Nat.Coprime a q), (1 : ℝ) / a)
        * (∑ b ∈ (Finset.range x).filter
            (fun b => 1 ≤ b ∧ ∀ p ∈ b.primeFactors, p ∣ q), (1 : ℝ) / b) := by
  classical
  set A := (Finset.range x).filter (fun a => Nat.Coprime a q) with hA
  set B := (Finset.range x).filter (fun b => 1 ≤ b ∧ ∀ p ∈ b.primeFactors, p ∣ q) with hB
  set dom := (Finset.range x).filter (fun n => 1 ≤ n) with hdom
  let φmap : ℕ → ℕ × ℕ := fun n => (coPart q n, qPart q n)
  have hdrop : ∑ n ∈ Finset.range x, (1 : ℝ) / n = ∑ n ∈ dom, (1 : ℝ) / n := by
    rw [hdom, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs with h
    · rfl
    · have : n = 0 := by omega
      subst this; simp
  have hval : ∀ n ∈ dom,
      (1 : ℝ) / n = (1 / (coPart q n : ℝ)) * (1 / (qPart q n : ℝ)) := by
    intro n hn
    rw [hdom, Finset.mem_filter] at hn
    have hn0 : n ≠ 0 := by omega
    have : (n : ℝ) = (coPart q n : ℝ) * (qPart q n : ℝ) := by
      exact_mod_cast (coPart_mul_qPart hn0).symm
    rw [this, one_div_mul_one_div]
  have hinj : Set.InjOn φmap ↑dom := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, hdom, Finset.mem_filter] at ha hb
    simp only [φmap, Prod.mk.injEq] at hab
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [← coPart_mul_qPart ha0, ← coPart_mul_qPart hb0, hab.1, hab.2]
  have hmaps : dom.image φmap ⊆ A ×ˢ B := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    rw [hdom, Finset.mem_filter, Finset.mem_range] at hn
    have hn0 : n ≠ 0 := by omega
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (coPart_le hn0) hn.1, coPart_coprime q n⟩
    · rw [hB, Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_le_of_lt (qPart_le hn0) hn.1, qPart_pos hn0, ?_⟩
      intro r hr
      exact qPart_prime_dvd (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  rw [hdrop]
  calc ∑ n ∈ dom, (1 : ℝ) / n
      = ∑ n ∈ dom, (1 / (coPart q n : ℝ)) * (1 / (qPart q n : ℝ)) :=
        Finset.sum_congr rfl hval
    _ = ∑ p ∈ dom.image φmap, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ A ×ˢ B, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hmaps
        intro p _ _; positivity
    _ = (∑ a ∈ A, (1 : ℝ) / a) * (∑ b ∈ B, (1 : ℝ) / b) := by
        rw [Finset.sum_mul_sum A B (fun a => (1 : ℝ) / a) (fun b => (1 : ℝ) / b),
          ← Finset.sum_product']

/-- **S1b (uniform coprime-harmonic lower bound).** `(φ(q)/q)·log x ≤ Σ_{a<x,(a,q)=1} 1/a`
for all `q ≥ 1` and `x ≥ 2` — the `q`-uniform strengthening of `copHarmonic_lower`. -/
lemma copHarmonic_uniform_lower (q x : ℕ) (hq : 1 ≤ q) (hx : 2 ≤ x) :
    (Nat.totient q / q : ℝ) * Real.log x ≤ copHarmonic x q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphipos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr (show 0 < q by omega); exact_mod_cast this
  set A := (Finset.range x).filter (fun a => Nat.Coprime a q) with hA
  have hAnn : (0 : ℝ) ≤ ∑ a ∈ A, (1 : ℝ) / a :=
    Finset.sum_nonneg (fun a _ => by positivity)
  -- copHarmonic x q = Σ_A 1/a
  have hcop : copHarmonic x q = ∑ a ∈ A, (1 : ℝ) / a := rfl
  -- log x ≤ Σ_{range x} 1/n via `copHarmonic_lower` at B = 1
  have hc1 : copHarmonic x 1 = ∑ n ∈ Finset.range x, (1 : ℝ) / n := by
    rw [copHarmonic, Finset.filter_true_of_mem (fun n _ => Nat.coprime_one_right n)]
  have hlog : Real.log x ≤ ∑ n ∈ Finset.range x, (1 : ℝ) / n := by
    have hcl := copHarmonic_lower 1 one_ne_zero x hx
    rw [hc1, Nat.totient_one] at hcl
    simpa using hcl
  -- factorization + q-smooth bound
  have hf1 := coprime_factor_le q x
  have hf2 := qsmoothSum_le hq x
  have hchain : (∑ n ∈ Finset.range x, (1 : ℝ) / n)
      ≤ (∑ a ∈ A, (1 : ℝ) / a) * ((q : ℝ) / (Nat.totient q)) :=
    le_trans hf1 (mul_le_mul_of_nonneg_left hf2 hAnn)
  rw [hcop]
  calc (Nat.totient q / q : ℝ) * Real.log x
      ≤ (Nat.totient q / q : ℝ) * (∑ n ∈ Finset.range x, (1 : ℝ) / n) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (Nat.totient q / q : ℝ)
          * ((∑ a ∈ A, (1 : ℝ) / a) * ((q : ℝ) / (Nat.totient q))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = ∑ a ∈ A, (1 : ℝ) / a := by field_simp

/-! ## S1b — the Selberg term identity and the bounding-sum lower bound -/

/-- With density `ν(d) = 1/d`, the Selberg term at a squarefree `l` is `1/φ(l)`. -/
lemma apSelbergTerms_eq {l : ℕ} (hl : Squarefree l) :
    (apSieve y q a P L hP hL).selbergTerms l = 1 / (Nat.totient l : ℝ) := by
  rw [BoundingSieve.selbergTerms_apply, apSieve_nu]
  simp only [apNu_apply]
  have hlprod : (∏ p ∈ l.primeFactors, (p : ℝ)) = (l : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hl]
  have hphi : (∏ p ∈ l.primeFactors, ((p : ℝ) - 1)) = (Nat.totient l : ℝ) :=
    (totient_squarefree_cast hl).symm
  have hterm : ∀ p ∈ l.primeFactors,
      (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hstep : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
    rw [hstep, inv_div]
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, hlprod, hphi,
    ← mul_div_assoc, inv_mul_cancel₀ hl0]

/-- The concrete Shiu sieve: the residue class `m ≡ a (q)` in `[1,y]`, sifted by the
primes `≤ t` (not dividing `q`), at level `t²`. -/
noncomputable def roughSieve (y q a t : ℕ) (ht : 2 ≤ t) : SelbergSieve :=
  apSieve y q a (roughP q t) ((t : ℝ) ^ 2) (roughP_squarefree q t)
    (by have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
        nlinarith)

@[simp] lemma roughSieve_prodPrimes (y q a t : ℕ) (ht : 2 ≤ t) :
    (roughSieve y q a t ht).prodPrimes = roughP q t := rfl
@[simp] lemma roughSieve_level (y q a t : ℕ) (ht : 2 ≤ t) :
    (roughSieve y q a t ht).level = (t : ℝ) ^ 2 := rfl
@[simp] lemma roughSieve_totalMass (y q a t : ℕ) (ht : 2 ≤ t) :
    (roughSieve y q a t ht).totalMass = (y : ℝ) / q := rfl

lemma roughSieve_siftedSum (y q a t : ℕ) (ht : 2 ≤ t) :
    (roughSieve y q a t ht).siftedSum
      = (((Finset.Icc 1 y).filter
          (fun n => Nat.Coprime (roughP q t) n ∧ n % q = a)).card : ℝ) :=
  apSieve_siftedSum

lemma roughSieve_rem_abs_le (y q a t : ℕ) (hq : 1 ≤ q) (ha : a < q) (ht : 2 ≤ t)
    {d : ℕ} (hd : d ∣ roughP q t) : |(roughSieve y q a t ht).rem d| ≤ 1 :=
  apSieve_rem_abs_le hq ha (roughP_coprime q t) hd

lemma roughSieve_errSum_le (y q a t : ℕ) (hq : 1 ≤ q) (ha : a < q) (ht : 2 ≤ t) (D : ℕ)
    (hDbound : ∀ d, d ∣ roughP q t → (d : ℝ) ≤ (t : ℝ) ^ 2 → d ≤ D) :
    ∑ d ∈ (roughP q t).divisors,
        (if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(roughSieve y q a t ht).rem d|
          else 0)
      ≤ (D : ℝ) * (1 + Real.log D) ^ 2 :=
  apSieve_errSum_le hq ha (roughP_coprime q t) D hDbound

/-- **S1b (subset).** The Selberg bounding sum of `roughSieve` dominates `phiAtomSum (t+1) q`. -/
lemma phiAtomSum_le_boundingSum (y q a t : ℕ) (ht : 2 ≤ t) :
    phiAtomSum (t + 1) q ≤ Salt.SelbergPort.selbergBoundingSum (roughSieve y q a t ht) := by
  classical
  have hsub : sqfCop (t + 1) q ⊆
      (roughP q t).divisors.filter (fun l => (l : ℝ) ^ 2 ≤ (t : ℝ) ^ 2) := by
    intro r hr
    simp only [sqfCop, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrt, hrsq, hrcop⟩ := hr
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨dvd_roughP_of_squarefree hrsq hrcop (by omega),
      (roughP_squarefree q t).ne_zero⟩, ?_⟩
    have hrR : (r : ℝ) ≤ t := by exact_mod_cast (by omega : r ≤ t)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have heq : phiAtomSum (t + 1) q
      = ∑ r ∈ sqfCop (t + 1) q, (roughSieve y q a t ht).selbergTerms r := by
    rw [phiAtomSum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [sqfCop, Finset.mem_filter] at hr
    exact (apSelbergTerms_eq hr.2.1).symm
  rw [Salt.SelbergPort.selbergBoundingSum, ← Finset.sum_filter, roughSieve_prodPrimes,
    roughSieve_level, heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt (BoundingSieve.selbergTerms_pos hl.1.1)

/-- **S1b (main).** The `φ`-saving lower bound on the Selberg bounding sum:
`(φ(q)/q)·log t ≤ S`, uniformly in `q`. -/
lemma boundingSum_ge (y q a t : ℕ) (hq : 1 ≤ q) (ht : 2 ≤ t) :
    (Nat.totient q / q : ℝ) * Real.log t
      ≤ Salt.SelbergPort.selbergBoundingSum (roughSieve y q a t ht) := by
  have h1 := phiAtomSum_le_boundingSum y q a t ht
  have h2 := copHarmonic_le_phiAtomSum (t + 1) q
  have h3 := copHarmonic_uniform_lower q (t + 1) hq (by omega)
  have htR : (0 : ℝ) < t := by
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have h4 : Real.log (t : ℝ) ≤ Real.log ((t + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log htR
    push_cast; linarith
  have hnn : (0 : ℝ) ≤ (Nat.totient q / q : ℝ) := by positivity
  calc (Nat.totient q / q : ℝ) * Real.log t
      ≤ (Nat.totient q / q : ℝ) * Real.log ((t + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h4 hnn
    _ ≤ copHarmonic (t + 1) q := h3
    _ ≤ phiAtomSum (t + 1) q := h2
    _ ≤ Salt.SelbergPort.selbergBoundingSum (roughSieve y q a t ht) := h1

/-! ## S1c — the polylogarithmic error absorbed into the `t³` slack -/

/-- `t²·(1 + log(t²))² ≤ 25·t³` for `t ≥ 2` (via `log t ≤ 2√t`). -/
lemma err_le_cube (t : ℕ) (ht : 2 ≤ t) :
    ((t ^ 2 : ℕ) : ℝ) * (1 + Real.log ((t ^ 2 : ℕ) : ℝ)) ^ 2 ≤ 25 * (t : ℝ) ^ 3 := by
  have htR : (0 : ℝ) < t := by
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hcast : ((t ^ 2 : ℕ) : ℝ) = (t : ℝ) ^ 2 := by push_cast; ring
  have hlogeq : Real.log ((t ^ 2 : ℕ) : ℝ) = 2 * Real.log t := by
    rw [hcast, Real.log_pow]; push_cast; ring
  rw [hlogeq, hcast]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htR
  have hsqt : Real.sqrt t ^ 2 = t := Real.sq_sqrt htR.le
  have hsge1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ t))
  have hlogst : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hst
    have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by rw [Real.log_sqrt htR.le]; ring
    rw [h2]; linarith
  have hlin : 1 + 2 * Real.log t ≤ 5 * Real.sqrt t := by linarith [hlogst, hsge1]
  have hlogpos : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  have hsq : (1 + 2 * Real.log t) ^ 2 ≤ 25 * t := by
    nlinarith [hsqt, mul_nonneg (by linarith : (0 : ℝ) ≤ 5 * Real.sqrt t - (1 + 2 * Real.log t))
      (by linarith : (0 : ℝ) ≤ 5 * Real.sqrt t + (1 + 2 * Real.log t))]
  calc (t : ℝ) ^ 2 * (1 + 2 * Real.log t) ^ 2
      ≤ (t : ℝ) ^ 2 * (25 * t) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 25 * (t : ℝ) ^ 3 := by ring

/-! ## The assembled pole -/

open Classical in
/-- **S1 (the POLE).** Shiu's Lemma-2 analog: the rough count in an arithmetic
progression via the Selberg sieve. -/
theorem rough_count_in_ap_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ y q a t : ℕ, 1 ≤ q → 2 ≤ t → Nat.Coprime a q →
      (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
          ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
        ≤ C₀ * ((y : ℝ) / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) := by
  classical
  refine ⟨25, by norm_num, fun y q a t hq ht _ => ?_⟩
  have htR : (0 : ℝ) < t := by
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphipos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hmainnn : (0 : ℝ) ≤ (y : ℝ) / (q.totient) / Real.log t := by positivity
  have ht3 : (0 : ℝ) ≤ (t : ℝ) ^ 3 := by positivity
  by_cases haq : a < q
  · have hsub : (Finset.Icc 1 y).filter
          (fun m => m % q = a ∧ ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)
        ⊆ (Finset.Icc 1 y).filter (fun n => Nat.Coprime (roughP q t) n ∧ n % q = a) := by
      intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      obtain ⟨hmem, hmq, hmp⟩ := hm
      exact ⟨hmem, Nat.coprime_of_dvd
        (fun k hk hkR => hmp k hk (prime_dvd_roughP hk hkR).1), hmq⟩
    have hsift :
        (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
            ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
          ≤ (roughSieve y q a t ht).siftedSum := by
      rw [roughSieve_siftedSum]
      exact_mod_cast Finset.card_le_card hsub
    have hselberg := Salt.SelbergPort.selberg_bound_simple (roughSieve y q a t ht)
    rw [roughSieve_prodPrimes, roughSieve_level] at hselberg
    have hSge := boundingSum_ge y q a t hq ht
    have hbpos : (0 : ℝ) < (q.totient / q : ℝ) * Real.log t := by positivity
    have hmain : (roughSieve y q a t ht).totalMass
          / Salt.SelbergPort.selbergBoundingSum (roughSieve y q a t ht)
        ≤ (y : ℝ) / (q.totient) / Real.log t := by
      rw [roughSieve_totalMass]
      have hEq : (y : ℝ) / (q.totient) / Real.log t
          = (y : ℝ) / q / ((q.totient / q : ℝ) * Real.log t) := by field_simp
      rw [hEq]
      gcongr
    have hDbound : ∀ d, d ∣ roughP q t → (d : ℝ) ≤ (t : ℝ) ^ 2 → d ≤ t ^ 2 := by
      intro d _ hdL
      have h : (d : ℝ) ≤ ((t ^ 2 : ℕ) : ℝ) := by
        rw [show ((t ^ 2 : ℕ) : ℝ) = (t : ℝ) ^ 2 by push_cast; ring]; exact hdL
      exact_mod_cast h
    have herr := roughSieve_errSum_le y q a t hq haq ht (t ^ 2) hDbound
    have herrcube := err_le_cube t ht
    calc (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
              ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
        ≤ (roughSieve y q a t ht).siftedSum := hsift
      _ ≤ (roughSieve y q a t ht).totalMass
            / Salt.SelbergPort.selbergBoundingSum (roughSieve y q a t ht)
          + ∑ d ∈ (roughP q t).divisors,
              if (d : ℝ) ≤ (t : ℝ) ^ 2 then (3 : ℝ) ^ ω d * |(roughSieve y q a t ht).rem d|
              else 0 := hselberg
      _ ≤ (y : ℝ) / (q.totient) / Real.log t
            + ((t ^ 2 : ℕ) : ℝ) * (1 + Real.log ((t ^ 2 : ℕ) : ℝ)) ^ 2 :=
          add_le_add hmain herr
      _ ≤ (y : ℝ) / (q.totient) / Real.log t + 25 * (t : ℝ) ^ 3 := by linarith [herrcube]
      _ ≤ 25 * ((y : ℝ) / (q.totient) / Real.log t + (t : ℝ) ^ 3) := by linarith [hmainnn]
  · have hqa : q ≤ a := by omega
    have hempty : (Finset.Icc 1 y).filter
        (fun m => m % q = a ∧ ∀ p, p.Prime → p ≤ t → ¬ p ∣ m) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro m _ hcon
      obtain ⟨hmq, _⟩ := hcon
      have hlt : m % q < q := Nat.mod_lt m hq
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith [hmainnn, ht3]

end Salt.Maynard
