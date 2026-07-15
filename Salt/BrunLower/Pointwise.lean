/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.LowerMoebius

/-!
# The pointwise block-Brun inequalities (blueprint `p0`, node B2)

The combinatorial keystone of the both-sided Brun sieve of Halberstam–Richert,
*A new look at Brun's sieve*, Mém. SMF **25** (1971) 97–106
(numdam `10.24033/msmf.39`).  This is the machine-checked form of the paper's
**Lemma 2** / equation (2.5): for a squarefree `n` and the block predicate
`χ_ν` (`Salt.BrunLower.chi`, node B0),
```
        [n = 1] ≤ ∑_{d ∣ n} μ(d) χ₁(d)        (upper, ν = 1)
        ∑_{d ∣ n} μ(d) χ₂(d) ≤ [n = 1]        (lower, ν = 2)
```

## The mechanism (H-R's own, re-derived)

The proof is **not** an induction on `ω(n)`; it is a *single peel of the smallest
prime*.  Write `n = p·m` with `p = q(n)` the least prime factor, so every prime of
`m` exceeds `p`.  Splitting the divisor sum over the two cosets `t ∣ m` and `p·t`,
and using `μ(pt) = −μ(t)`,
```
    ∑_{d ∣ n} μ(d) χ_ν(d) = ∑_{t ∣ m} μ(t) (χ_ν(t) − χ_ν(pt)).
```
H-R's **fundamental identity (Lemma 1)** evaluates each bracket: `χ_ν(t) − χ_ν(pt)`
vanishes unless `χ_ν(t)=1, χ_ν(pt)=0`, and in that case the closure rule (2.3)
(`chi_add_smaller_prime`) forces — by contraposition — the parity
`Ω(t) ≢ ν (mod 2)`, i.e. `μ(t) = (−1)^{ν−1}`.  Hence every term of the peeled sum
has the **single sign** `(−1)^{ν−1}`:
```
    (−1)^{ν−1} · ∑_{d ∣ n} μ(d) χ_ν(d) = ∑_{t ∣ m} χ_ν(t)(1 − χ_ν(pt)) ≥ 0,
```
which is exactly (2.5) `(−1)^ν T_ν(n) ≤ 0`.  The parity/sign control therefore
lives entirely in `chi_add_smaller_prime` (B0); B2 is the algebra that turns it
into a definite sign on the alternating Möbius sum.

The `z`-hypothesis `hprime` (all primes of `n` below `z`) is part of the frozen
H-R interface (`n ∣ P(z)`) but is *not* used: the structural rules
(2.2)/(2.3) are purely combinatorial, so the pointwise inequalities hold for every
squarefree `n`.

## B2.4 bridge

`sum_moebius_chi_upper`/`sum_moebius_chi_lower` package as `IsUpperMoebius (μ·χ₁)`
and `IsLowerMoebius (μ·χ₂)` (`isUpperMoebius_moebius_chiOne` /
`isLowerMoebius_moebius_chiTwo`) after extending from squarefree `n` to all `n`
via the radical (`μ` kills non-squarefree divisors).  These feed the sifted-sum
plumbing of mathlib's `SelbergSieve` (upper) and node B1 (lower).
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.BrunLower

open BoundingSieve

/-- For squarefree `t`, the (real-cast) Möbius value is `(−1)` to the number of
distinct prime factors. -/
lemma moebius_real_of_squarefree {t : ℕ} (ht : Squarefree t) :
    (μ t : ℝ) = (-1 : ℝ) ^ t.primeFactors.card := by
  have hnodup : t.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList ht.ne_zero).mp ht
  have hcard : cardFactors t = t.primeFactors.card := by
    rw [cardFactors_apply, ← Nat.toFinset_factors, List.toFinset_card_of_nodup hnodup]
  rw [moebius_apply_of_squarefree ht, hcard]
  push_cast
  ring

/-- The divisor sum over `p·m` (`p` prime, `p ∤ m`) splits over the two cosets
`{t ∣ m}` and `{p·t : t ∣ m}`. -/
lemma sum_over_divisors_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (F : ℕ → ℝ) :
    ∑ d ∈ (p * m).divisors, F d
      = ∑ t ∈ m.divisors, F t + ∑ t ∈ m.divisors, F (p * t) := by
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm
  have himg_inj : ∀ a ∈ m.divisors, ∀ b ∈ m.divisors, p * a = p * b → a = b :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h
  have hdisj : Disjoint m.divisors (m.divisors.image (p * ·)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    rw [Finset.mem_image] at hx'
    obtain ⟨t, ht, rfl⟩ := hx'
    exact hpm ((dvd_mul_right p t).trans (Nat.dvd_of_mem_divisors hx))
  have hunion : (p * m).divisors = m.divisors ∪ m.divisors.image (p * ·) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      by_cases hpd : p ∣ d
      · obtain ⟨t, rfl⟩ := hpd
        exact Or.inr ⟨t, ⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp hd, hm⟩, rfl⟩
      · exact Or.inl ⟨((hp.coprime_iff_not_dvd).mpr hpd).symm.dvd_of_dvd_mul_left hd, hm⟩
    · rintro (⟨hd, -⟩ | ⟨t, ⟨ht, -⟩, rfl⟩)
      · exact ⟨hd.mul_left p, hpm0⟩
      · exact ⟨mul_dvd_mul_left p ht, hpm0⟩
  rw [hunion, Finset.sum_union hdisj, Finset.sum_image himg_inj]

/-- H-R's fundamental identity (Lemma 1) in sign form: for a prime `p` smaller than
every prime factor of a squarefree `t`, the Möbius-weighted boundary bracket
`μ(t)(χ_ν(t) − χ_ν(pt))` carries the single sign `(−1)^{ν−1}`.  Stated as the
nonnegativity of `(−1)^{ν−1}` times the bracket (`side = ν ∈ {1,2}`). -/
lemma peel_term_nonneg {Lam z : ℝ} {b side : ℕ}
    (hside : side = 1 ∨ side = 2) {p t : ℕ} (hp : p.Prime) (ht : Squarefree t)
    (hlt : ∀ q ∈ t.primeFactors, p < q) :
    0 ≤ (-1 : ℝ) ^ (side - 1) *
        ((μ t : ℝ) * ((if chi Lam z side b t then (1 : ℝ) else 0)
                      - (if chi Lam z side b (p * t) then (1 : ℝ) else 0))) := by
  by_cases hC : chi Lam z side b (p * t)
  · -- `χ_ν(pt) = 1` forces `χ_ν(t) = 1` (divisor closure); the bracket vanishes.
    have hpt0 : p * t ≠ 0 := Nat.mul_ne_zero hp.ne_zero ht.ne_zero
    have hA : chi Lam z side b t := chi_dvd_closed Lam z hpt0 (dvd_mul_left t p) hC
    rw [if_pos hA, if_pos hC, sub_self, mul_zero, mul_zero]
  · rw [if_neg hC]
    by_cases hA : chi Lam z side b t
    · rw [if_pos hA, sub_zero]
      -- `χ_ν(t)=1, χ_ν(pt)=0`: (2.3) contrapositive fixes the parity of `Ω(t)`.
      have hpar_ne : ¬ (t.primeFactors.card % 2 = side % 2) := fun hpar =>
        hC (chi_add_smaller_prime Lam z hp ht.ne_zero hlt hpar hA)
      have hmu : (μ t : ℝ) = (-1 : ℝ) ^ t.primeFactors.card := moebius_real_of_squarefree ht
      have hsign : (μ t : ℝ) = (-1 : ℝ) ^ (side - 1) := by
        rcases hside with rfl | rfl
        · rw [hmu, (Nat.even_iff.mpr (by omega : t.primeFactors.card % 2 = 0)).neg_one_pow]
          norm_num
        · rw [hmu, (Nat.odd_iff.mpr (by omega : t.primeFactors.card % 2 = 1)).neg_one_pow]
          norm_num
      rw [hsign, mul_one]
      exact mul_self_nonneg _
    · rw [if_neg hA, sub_self, mul_zero, mul_zero]

/-- The core of Lemma 2 / equation (2.5): for squarefree `n ≠ 1`, the alternating
Möbius sum against `χ_ν`, multiplied by `(−1)^{ν−1}`, is nonnegative. -/
lemma neg_one_pow_mul_sum_moebius_chi_nonneg {Lam z : ℝ} {b side : ℕ}
    (hside : side = 1 ∨ side = 2) {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1) :
    0 ≤ (-1 : ℝ) ^ (side - 1) *
        ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∣ n := Nat.minFac_dvd n
  set m := n / p with hm_def
  have hn_eq : p * m = n := Nat.mul_div_cancel' hpn
  have hm0 : m ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hn_eq; exact hn0 hn_eq.symm
  have hpm : ¬ p ∣ m := by
    intro hd
    have hpp : p * p ∣ n := by rw [← hn_eq]; exact mul_dvd_mul_left p hd
    exact hp.ne_one (Nat.isUnit_iff.mp (hn p hpp))
  have hmdvd : m ∣ n := ⟨p, by rw [← hn_eq]; ring⟩
  have hmsf : Squarefree m := Squarefree.squarefree_of_dvd hmdvd hn
  have hlt : ∀ q ∈ m.primeFactors, p < q := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    have hle : p ≤ q := Nat.minFac_le_of_dvd hqp.two_le (hqm.trans hmdvd)
    have hne : q ≠ p := by rintro rfl; exact hpm hqm
    omega
  -- Peel the smallest prime and combine the two cosets via `μ(pt) = −μ(t)`.
  have hsplit : ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0)
      = ∑ t ∈ m.divisors, (μ t : ℝ) *
          ((if chi Lam z side b t then (1 : ℝ) else 0)
            - (if chi Lam z side b (p * t) then (1 : ℝ) else 0)) := by
    rw [← hn_eq,
      sum_over_divisors_prime_mul hp hpm hm0
        (fun d => (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have htm : t ∣ m := Nat.dvd_of_mem_divisors ht
    have hpt : ¬ p ∣ t := fun h => hpm (h.trans htm)
    have hcop : Nat.Coprime p t := (hp.coprime_iff_not_dvd).mpr hpt
    have hmuZ : μ (p * t) = - μ t := by
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]; ring
    have hmu : (μ (p * t) : ℝ) = -(μ t : ℝ) := by rw [hmuZ]; push_cast; ring
    rw [hmu]; ring
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_nonneg
  intro t ht
  have htm : t ∣ m := Nat.dvd_of_mem_divisors ht
  have htsf : Squarefree t := Squarefree.squarefree_of_dvd htm hmsf
  have hltt : ∀ q ∈ t.primeFactors, p < q :=
    fun q hq => hlt q (Nat.primeFactors_mono htm hm0 hq)
  exact peel_term_nonneg hside hp htsf hltt

/-! ## The frozen pair (H-R Lemma 2 / (2.5)) -/

set_option linter.unusedVariables false in
/-- **Upper block-Brun pointwise inequality** (H-R (2.5), `ν = 1`): for squarefree
`n`, the truncated Möbius sum against `χ₁` overestimates the indicator `[n = 1]`.
The `hprime` (all primes `< z`) hypothesis is part of the H-R `n ∣ P(z)` interface
and is not needed for the pointwise inequality (the structural rules are purely
combinatorial). -/
theorem sum_moebius_chi_upper {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) {n : ℕ}
    (hn : Squarefree n) (hprime : ∀ p ∈ n.primeFactors, (p : ℝ) < z) :
    (if n = 1 then (1 : ℝ) else 0)
      ≤ ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z 1 b d then 1 else 0) := by
  by_cases hn1 : n = 1
  · subst hn1
    rw [if_pos rfl, Nat.divisors_one, Finset.sum_singleton,
      if_pos (chi_one Lam z hb (by norm_num)), moebius_apply_one]
    norm_num
  · rw [if_neg hn1]
    have h := neg_one_pow_mul_sum_moebius_chi_nonneg (Lam := Lam) (z := z) (b := b)
      (Or.inl rfl) hn hn1
    simpa using h

set_option linter.unusedVariables false in
/-- **Lower block-Brun pointwise inequality** (H-R (2.5), `ν = 2`): for squarefree
`n`, the truncated Möbius sum against `χ₂` underestimates the indicator `[n = 1]`.
The `hprime` hypothesis is unused (see `sum_moebius_chi_upper`). -/
theorem sum_moebius_chi_lower {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) {n : ℕ}
    (hn : Squarefree n) (hprime : ∀ p ∈ n.primeFactors, (p : ℝ) < z) :
    ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z 2 b d then 1 else 0)
      ≤ (if n = 1 then (1 : ℝ) else 0) := by
  by_cases hn1 : n = 1
  · subst hn1
    rw [if_pos rfl, Nat.divisors_one, Finset.sum_singleton,
      if_pos (chi_one Lam z hb (by norm_num)), moebius_apply_one]
    norm_num
  · rw [if_neg hn1]
    have h := neg_one_pow_mul_sum_moebius_chi_nonneg (Lam := Lam) (z := z) (b := b)
      (Or.inr rfl) hn hn1
    have hpow : (-1 : ℝ) ^ (2 - 1) = -1 := by norm_num
    rw [hpow] at h
    linarith

/-! ## B2.4 bridge: `IsUpperMoebius`/`IsLowerMoebius` for all `n`

The pointwise pair is proved for squarefree `n`; the sieve plumbing needs it for
every `n`.  Since `μ` vanishes off the squarefree divisors, the Möbius sum against
`χ_ν` over `n.divisors` equals the one over the radical `∏_{p ∣ n} p` (a squarefree
number with the same prime factors), reducing the general case to the frozen pair. -/

/-- The radical `∏_{p ∣ n} p` (product of distinct primes) is squarefree. -/
lemma squarefree_prod_primeFactors (n : ℕ) : Squarefree (∏ p ∈ n.primeFactors, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)
    change IsRelPrime p q
    exact hpp.prime.irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h))
  · exact fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree

/-- For `n ∉ {0, 1}` the radical is not `1` (it has the same, nonempty, prime set). -/
lemma prod_primeFactors_ne_one {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    (∏ p ∈ n.primeFactors, p) ≠ 1 := by
  intro hone
  have hpf : n.primeFactors = ∅ := by
    have hp := Nat.primeFactors_prod (s := n.primeFactors)
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [← hp, hone, Nat.primeFactors_one]
  rcases Nat.primeFactors_eq_empty.mp hpf with h | h
  · exact hn0 h
  · exact hn1 h

/-- The Möbius-`χ_ν` sum over `n.divisors` collapses to the sum over the radical's
divisors (`μ` kills non-squarefree divisors, whose only squarefree divisors are the
divisors of the radical). -/
lemma sum_moebius_chi_eq_over_radical {Lam z : ℝ} {side b n : ℕ} (hn0 : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0)
      = ∑ d ∈ (∏ p ∈ n.primeFactors, p).divisors,
          (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) := by
  have hrad_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hrad_ne0 : (∏ p ∈ n.primeFactors, p) ≠ 0 :=
    (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)).ne'
  refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hn0 hrad_dvd) ?_).symm
  intro d hd hdr
  rcases eq_or_ne (μ d) 0 with hmu | hmu
  · simp [hmu]
  · exfalso
    have hsqf : Squarefree d := moebius_ne_zero_iff_squarefree.mp hmu
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hddvd : d ∣ ∏ p ∈ n.primeFactors, p := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsqf]
      exact Finset.prod_dvd_prod_of_subset _ _ (fun p => p) (Nat.primeFactors_mono hdn hn0)
    exact hdr (Nat.mem_divisors.mpr ⟨hddvd, hrad_ne0⟩)

/-- **B2.4 (upper bridge)**: `μ·χ₁` is an upper-Möbius coefficient system, hence
feeds mathlib's `siftedSum_le_…_of_upperMoebius` plumbing. -/
theorem isUpperMoebius_moebius_chiOne {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    IsUpperMoebius (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then 1 else 0)) := by
  intro n
  change (if n = 1 then (1 : ℝ) else 0)
      ≤ ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z 1 b d then 1 else 0)
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.divisors_one, Finset.sum_singleton]
    rw [if_pos (chi_one Lam z hb (by norm_num)), moebius_apply_one]; norm_num
  · rw [if_neg hn1, sum_moebius_chi_eq_over_radical hn0]
    have h := neg_one_pow_mul_sum_moebius_chi_nonneg (Lam := Lam) (z := z) (b := b)
      (Or.inl rfl) (squarefree_prod_primeFactors n) (prod_primeFactors_ne_one hn0 hn1)
    simpa using h

/-- **B2.4 (lower bridge)**: `μ·χ₂` is a lower-Möbius coefficient system (node B1),
hence feeds `siftedSum_ge_…_of_lowerMoebius`. -/
theorem isLowerMoebius_moebius_chiTwo {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    IsLowerMoebius (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then 1 else 0)) := by
  intro n
  change ∑ d ∈ n.divisors, (μ d : ℝ) * (if chi Lam z 2 b d then 1 else 0)
      ≤ (if n = 1 then (1 : ℝ) else 0)
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.divisors_one, Finset.sum_singleton]
    rw [if_pos (chi_one Lam z hb (by norm_num)), moebius_apply_one]; norm_num
  · rw [if_neg hn1, sum_moebius_chi_eq_over_radical hn0]
    have h := neg_one_pow_mul_sum_moebius_chi_nonneg (Lam := Lam) (z := z) (b := b)
      (Or.inr rfl) (squarefree_prod_primeFactors n) (prod_primeFactors_ne_one hn0 hn1)
    have hpow : (-1 : ℝ) ^ (2 - 1) = -1 := by norm_num
    rw [hpow] at h
    linarith

end Salt.BrunLower
