/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.PseudoChar

/-!
# B2 W5 — Jutila's Lemmas 2 and 3 (L2, L3): the coefficients `h(d; r, r')`

Jutila 1977, p.48 (Lemma 2) and p.49 (Lemma 3). For a multiplicative `f` and square-free
levels `r, r'`, the product of two pseudocharacters is a divisor sum,

    f_r(n) · f_{r'}(n) = Σ_{d ∣ n} h(d; r, r'),                     (`pseudoChar_mul_eq_sum_hCoef`)

where `h(·; r, r')` (`hCoef f r r'`) is the multiplicative function supported on the square-free
divisors of `r r'` with `h(p) = f(p) − 1` when `p` divides exactly one of `r, r'` and
`h(p) = f(p)² − 1` when `p ∣ (r, r')`. Here it is DEFINED by its prime values
`h(p) = f_r(p)·f_{r'}(p) − 1` (the same numbers, by `pseudoChar_prime_right`), extended
multiplicatively to square-free `d` and by `0` elsewhere. For Selberg's `ψ = μ·φ`
(`selbergPsi`, `ψ(p) = 1 − p`) Lemma 3 gives the two facts the density argument consumes at its
diagonal (design v2 §4: W9b's residue block `B(s, χ₀)` and W9c's diagonal),

    Σ_d h(d; r, r')/d = δ_{r,r'} · φ(r),                             (`hCoef_sum_div_eq`)
    Σ_d |h(d; r, r')| ≤ ∏_{p ∣ r} (p + 1) · ∏_{p ∣ r'} (p + 1).      (`hCoef_abs_sum_le`)

Both are finite Euler products of explicit local factors: at `p ∣ r`, `p ∤ r'` the local factor
of the first sum is `1 + (1 − p − 1)/p = 0`, at `p ∣ (r, r')` it is `1 + ((1 − p)² − 1)/p = p − 1`,
so the sum is `0` unless `r = r'`, when it is `∏_{p ∣ r} (p − 1) = φ(r)`. The engine is ONE row
(`sum_divisors_eq_prod_primeFactors_of_squarefree_support`): for `g` multiplicative on coprime
pairs and vanishing off square-free arguments, and any `N ≠ 0`,
`Σ_{d ∣ N} g(d) = ∏_{p ∣ N} (1 + g(p))` — the square-free divisors of `N` are the subsets of its
prime factors. `h`, `h/d` and `|h|` are its three instances.

## The honest label

Every row here is an INPUT to Jutila's §3 (W9): nothing below bears on twin primes or on the
crown's conditions. Lemma 2's Dirichlet-series form on p.48 (the product
`∏_{p ∣ r r', p ∤ (r, r')} (1 + (f(p) − 1) p^{−s}) · ∏_{p ∣ (r, r')} (1 + (f(p)² − 1) p^{−s})`) is
NOT stated: it is the route of Lemma 3 at `s = 1`, folded into the engine row, and W9 consumes
the coefficient identity and the two sums, never the series. The identity is stated twice: over
`n.divisors` (Lemma 2 as written; `n ≠ 0` is load-bearing since `Nat.divisors 0 = ∅`) and as a
sum over the FINITE range `(r r').divisors` filtered by `d ∣ n` (valid at every `n`, including
`n = 0`), the form under which W9 swaps the `d`-sum with the `n`-series. All values are ℝ-valued
as in `PseudoChar.lean`; `hCoef f r r'` is an `ArithmeticFunction` so mathlib's multiplicativity
API applies to it verbatim.

## The measured receipts behind these statements

(`h2c-desk/w1w5_receipts.py`, exact rationals.) Lemma 2 checked on every square-free pair `r, r' ≤
30` and `n ≤ 200`: 0 failures / 72,200 checks; on NON-square-free levels the identity FAILS, first
at `(r, r', n) = (1, 4, 4)` (`ψ_4(4) = 0` against `Σ_{d ∣ 4} h(d; 1, 4) = −1`; at `(4, 4, 4)`: `0`
against `1`), so the two `Squarefree` binders are load-bearing in Lean as in the paper; the filter
form holds at `n = 0` (`ψ_2(0)·ψ_1(0) = −1 = Σ_{d ∣ 2} h(d; 2, 1)`), where the `n.divisors` form
reads `−1 = 0`; for the NON-multiplicative `f ≡ 2` (`f(1) = 2`) the identity fails already at `(1,
1, 1)`. Lemma 3's orthogonality on every square-free pair `r, r' ≤ 60`: 0 failures / 1,369 pairs,
exact; the mutant `f = μ` in place of `μφ` gives `Σ h/d = 1, 0, 1, 1/5` at `(2,2), (2,3), (6,6),
(6,10)` — agreeing at the first two by the accident `1 + (μ(2) − 1)/2 = 0` and failing at `(6,6)`
(`1 ≠ 2`) and `(6,10)` (`1/5 ≠ 0`): Selberg's `ψ` is load-bearing, since the local factor `1 +
(ψ(p) − 1)/p` vanishes only for `ψ(p) = 1 − p`. The size bound: max ratio `1.0000` over the same
pairs, EQUALITY exactly on coprime pairs (`(2, 3)`: `12 ≤ 12`); at `(6, 6)`: `4 ≤ 144`. The exit
rows: `Σ h/d = 1 = φ(2)` at `(2, 2)`, `= 0` at `(2, 3)`; `ψ_6(30)·ψ_10(30) = 8 = Σ_{d ∣ 30} h(d;
6, 10)` with `h(1, 2, 3, 5, 6, 10, 15, 30) = (1, 0, −3, −5, 0, 0, 15, 0)`.
-/

open ArithmeticFunction Finset

noncomputable section
namespace Salt.SW

/-- Jutila's `h(d; r, r')` (Lemma 2, p.48): the multiplicative function with prime values
`h(p) = f_r(p)·f_{r'}(p) − 1` (that is `f(p) − 1` on `p ∣ r r'`, `p ∤ (r, r')`; `f(p)² − 1` on
`p ∣ (r, r')`; `0` on `p ∤ r r'`), supported on square-free `d`. -/
def hCoef (f : ArithmeticFunction ℝ) (r r' : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if Squarefree d then
      ∏ p ∈ d.primeFactors, (pseudoChar f r p * pseudoChar f r' p - 1) else 0,
    by simp [not_squarefree_zero]⟩

variable {f : ArithmeticFunction ℝ} {r r' : ℕ}

theorem hCoef_apply (d : ℕ) :
    hCoef f r r' d = if Squarefree d then
      ∏ p ∈ d.primeFactors, (pseudoChar f r p * pseudoChar f r' p - 1) else 0 := by
  rfl

theorem hCoef_of_squarefree {d : ℕ} (hd : Squarefree d) :
    hCoef f r r' d = ∏ p ∈ d.primeFactors, (pseudoChar f r p * pseudoChar f r' p - 1) := by
  rw [hCoef_apply, if_pos hd]

theorem hCoef_of_not_squarefree {d : ℕ} (hd : ¬ Squarefree d) : hCoef f r r' d = 0 := by
  rw [hCoef_apply, if_neg hd]

theorem hCoef_one : hCoef f r r' 1 = 1 := by
  rw [hCoef_of_squarefree squarefree_one, Nat.primeFactors_one, Finset.prod_empty]

theorem hCoef_prime {p : ℕ} (hp : p.Prime) :
    hCoef f r r' p = pseudoChar f r p * pseudoChar f r' p - 1 := by
  rw [hCoef_of_squarefree hp.squarefree, hp.primeFactors, Finset.prod_singleton]

/-- A pseudocharacter at a PRIME argument: `f_r(p) = f(gcd(r, p))` is `f(p)` on `p ∣ r` and `1`
otherwise (the landed `pseudoChar_prime_left` is the mirror statement, a prime LEVEL). -/
theorem pseudoChar_prime_right (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    pseudoChar f r p = if p ∣ r then f p else 1 := by
  by_cases h : p ∣ r
  · rw [if_pos h]
    simp only [pseudoChar, Nat.gcd_eq_right h]
  · rw [if_neg h]
    exact pseudoChar_of_coprime hf ((hp.coprime_iff_not_dvd.mpr h).symm)

/-- Off `r r'` the prime values vanish: `f_r(p) = f_{r'}(p) = 1` there. -/
theorem hCoef_prime_of_not_dvd (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ r * r') : hCoef f r r' p = 0 := by
  have h1 : ¬ p ∣ r := fun hd => h (hd.mul_right r')
  have h2 : ¬ p ∣ r' := fun hd => h (hd.mul_left r)
  rw [hCoef_prime hp, pseudoChar_prime_right hf hp r, pseudoChar_prime_right hf hp r',
    if_neg h1, if_neg h2]
  norm_num

/-- `h(·; r, r')` is multiplicative in `d` for EVERY `f` (the prime values are arbitrary
numbers; multiplicativity is the product over `primeFactors` of a coprime product). -/
theorem hCoef_isMultiplicative (f : ArithmeticFunction ℝ) (r r' : ℕ) :
    (hCoef f r r').IsMultiplicative := by
  refine ⟨hCoef_one, fun {a b} hab => ?_⟩
  by_cases hsq : Squarefree (a * b)
  · obtain ⟨-, ha, hb⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [hCoef_of_squarefree hsq, hCoef_of_squarefree ha, hCoef_of_squarefree hb,
      hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]
  · rw [hCoef_of_not_squarefree hsq]
    by_cases ha : Squarefree a
    · have hb : ¬ Squarefree b := fun hb => hsq (Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩)
      rw [hCoef_of_not_squarefree hb, mul_zero]
    · rw [hCoef_of_not_squarefree ha, zero_mul]

/-- The support: `h(d; r, r') = 0` unless `d ∣ r r'` (a square-free `d ∤ r r'` has a prime
factor `p ∤ r r'`, where the local value is `0`). -/
theorem hCoef_eq_zero_of_not_dvd (hf : f.IsMultiplicative) {d : ℕ} (h : ¬ d ∣ r * r') :
    hCoef f r r' d = 0 := by
  by_cases hd : Squarefree d
  · rw [hCoef_of_squarefree hd]
    have hall : ¬ ∀ p ∈ d.primeFactors, p ∣ r * r' := by
      intro hall
      refine h ?_
      rw [← Nat.prod_primeFactors_of_squarefree hd]
      exact Finset.prod_primes_dvd _
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hall
    obtain ⟨p, hpmem, hpnd⟩ : ∃ p ∈ d.primeFactors, ¬ p ∣ r * r' := by
      by_contra hcon
      exact hall fun p hp => not_not.mp fun hnp => hcon ⟨p, hp, hnp⟩
    have hp := Nat.prime_of_mem_primeFactors hpmem
    refine Finset.prod_eq_zero hpmem ?_
    rw [pseudoChar_prime_right hf hp r, pseudoChar_prime_right hf hp r',
      if_neg (fun hh => hpnd (hh.mul_right r')), if_neg (fun hh => hpnd (hh.mul_left r))]
    norm_num
  · exact hCoef_of_not_squarefree hd

/-- **The engine.** For `g` multiplicative on coprime pairs (`g 1 = 1`) and vanishing off
square-free arguments, the divisor sum over ANY `N ≠ 0` is the product of the local factors
`1 + g(p)` over the primes of `N`: the square-free divisors of `N` are the products of the
subsets of `N.primeFactors`. -/
theorem sum_divisors_eq_prod_primeFactors_of_squarefree_support {g : ℕ → ℝ} (hg1 : g 1 = 1)
    (hg : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (hg0 : ∀ d : ℕ, ¬ Squarefree d → g d = 0) {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, g d = ∏ p ∈ N.primeFactors, (1 + g p) := by
  classical
  obtain ⟨G, hGc⟩ : ∃ G : ArithmeticFunction ℝ, ⇑G = g :=
    ⟨⟨g, hg0 0 not_squarefree_zero⟩, rfl⟩
  have hG : G.IsMultiplicative := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [hGc]; exact hg1
    · rw [hGc]; exact hg a b hab
  have hmsq : Squarefree (∏ p ∈ N.primeFactors, p) := by
    rw [← Nat.radical_eq_prod_primeFactors]
    exact UniqueFactorizationMonoid.squarefree_radical
  have hmpf : (∏ p ∈ N.primeFactors, p).primeFactors = N.primeFactors :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hmdvd : (∏ p ∈ N.primeFactors, p) ∣ N :=
    Finset.prod_primes_dvd N (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors hp)
  have hsum : ∑ d ∈ (∏ p ∈ N.primeFactors, p).divisors, g d = ∑ d ∈ N.divisors, g d := by
    refine Finset.sum_subset (Nat.divisors_subset_of_dvd hN hmdvd) (fun d hdN hdm => ?_)
    by_cases hdsq : Squarefree d
    · refine absurd (Nat.mem_divisors.mpr ⟨?_, hmsq.ne_zero⟩) hdm
      rw [← Nat.prod_primeFactors_of_squarefree hdsq]
      exact Finset.prod_dvd_prod_of_subset _ _ _
        (Nat.primeFactors_mono (Nat.mem_divisors.mp hdN).1 hN)
    · exact hg0 d hdsq
  have key : ∑ d ∈ (∏ p ∈ N.primeFactors, p).divisors, G d
      = ∏ p ∈ (∏ p ∈ N.primeFactors, p).primeFactors, (1 + G p) :=
    (hG.prodPrimeFactors_one_add_of_squarefree hmsq).symm
  rw [hmpf, hGc] at key
  exact hsum.symm.trans key

/-- The engine at `g = h·u` for `u` multiplicative on coprime pairs. -/
theorem sum_divisors_hCoef_mul_eq_prod {u : ℕ → ℝ} (hu1 : u 1 = 1)
    (hu : ∀ a b : ℕ, Nat.Coprime a b → u (a * b) = u a * u b) {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, hCoef f r r' d * u d
      = ∏ p ∈ N.primeFactors, (1 + hCoef f r r' p * u p) := by
  refine sum_divisors_eq_prod_primeFactors_of_squarefree_support
    (g := fun d => hCoef f r r' d * u d) ?_ ?_ ?_ hN
  · rw [hCoef_one, hu1, mul_one]
  · intro a b hab
    rw [(hCoef_isMultiplicative f r r').map_mul_of_coprime hab, hu a b hab, mul_mul_mul_comm]
  · intro d hd
    rw [hCoef_of_not_squarefree hd, zero_mul]

/-- The engine at `g = h(d)/d`. -/
theorem sum_divisors_hCoef_div_eq_prod {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, hCoef f r r' d / (d : ℝ)
      = ∏ p ∈ N.primeFactors, (1 + hCoef f r r' p / (p : ℝ)) := by
  have h := sum_divisors_hCoef_mul_eq_prod (f := f) (r := r) (r' := r')
    (u := fun d : ℕ => 1 / (d : ℝ)) (by norm_num)
    (fun a b _ => by simp only [Nat.cast_mul, one_div_mul_one_div]) hN
  simpa only [mul_one_div] using h

/-- The engine at `g = |h|`. -/
theorem sum_divisors_abs_hCoef_eq_prod {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, |hCoef f r r' d| = ∏ p ∈ N.primeFactors, (1 + |hCoef f r r' p|) := by
  refine sum_divisors_eq_prod_primeFactors_of_squarefree_support
    (g := fun d => |hCoef f r r' d|) ?_ ?_ ?_ hN
  · rw [hCoef_one, abs_one]
  · intro a b hab
    rw [(hCoef_isMultiplicative f r r').map_mul_of_coprime hab, abs_mul]
  · intro d hd
    rw [hCoef_of_not_squarefree hd, abs_zero]

/-- A pseudocharacter at a square-free level is the product of its prime values over the primes
of `n`: `f_r(n) = f(gcd(r, n))`, `gcd(r, n)` is square-free with `primeFactors = r.pF ∩ n.pF`,
and `f_r(p) = f(p)` or `1` according as `p ∣ r`. -/
theorem pseudoChar_eq_prod_primeFactors (hf : f.IsMultiplicative) (hr : Squarefree r) {n : ℕ}
    (hn : n ≠ 0) : pseudoChar f r n = ∏ p ∈ n.primeFactors, pseudoChar f r p := by
  classical
  have hgcdsq : Squarefree (Nat.gcd r n) := hr.squarefree_of_dvd (Nat.gcd_dvd_left r n)
  have hlhs : pseudoChar f r n = ∏ p ∈ (Nat.gcd r n).primeFactors, f p := by
    rw [hf.prod_primeFactors hgcdsq]
    rfl
  have hcongr : ∀ p ∈ n.primeFactors,
      pseudoChar f r p = if p ∈ r.primeFactors then f p else 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [pseudoChar_prime_right hf hpp r]
    by_cases hd : p ∣ r
    · rw [if_pos hd, if_pos (Nat.mem_primeFactors.mpr ⟨hpp, hd, hr.ne_zero⟩)]
    · rw [if_neg hd, if_neg (fun hm => hd (Nat.dvd_of_mem_primeFactors hm))]
  rw [hlhs, Nat.primeFactors_gcd hr.ne_zero hn, Finset.prod_congr rfl hcongr,
    Finset.prod_ite_mem, Finset.inter_comm]

/-- **Lemma 2 (p.48).** `f_r(n)·f_{r'}(n) = Σ_{d ∣ n} h(d; r, r')` for square-free `r, r'` and
`n ≠ 0` (`Nat.divisors 0 = ∅` while `f_r(0) = f(r)`): both sides are the product over `p ∣ n`
of `f_r(p)·f_{r'}(p) = 1 + h(p)`. -/
theorem pseudoChar_mul_eq_sum_hCoef (hf : f.IsMultiplicative) (hr : Squarefree r)
    (hr' : Squarefree r') {n : ℕ} (hn : n ≠ 0) :
    pseudoChar f r n * pseudoChar f r' n = ∑ d ∈ n.divisors, hCoef f r r' d := by
  have hE : ∑ d ∈ n.divisors, hCoef f r r' d
      = ∏ p ∈ n.primeFactors, (1 + hCoef f r r' p) :=
    sum_divisors_eq_prod_primeFactors_of_squarefree_support hCoef_one
      (fun a b hab => (hCoef_isMultiplicative f r r').map_mul_of_coprime hab)
      (fun d hd => hCoef_of_not_squarefree hd) hn
  rw [hE, pseudoChar_eq_prod_primeFactors hf hr hn, pseudoChar_eq_prod_primeFactors hf hr' hn,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [hCoef_prime (Nat.prime_of_mem_primeFactors hp)]
  ring

/-- A pseudocharacter at `0` is `f r`, and for a square-free level that is the product of its
prime values over any set of primes containing `r.primeFactors` (the extra factors are `1`). -/
private theorem pseudoChar_zero_eq_prod (hf : f.IsMultiplicative) {s : ℕ} (hs : Squarefree s)
    {t : Finset ℕ} (hst : s.primeFactors ⊆ t) (ht : ∀ p ∈ t, Nat.Prime p) :
    pseudoChar f s 0 = ∏ p ∈ t, pseudoChar f s p := by
  have h1 : ∏ p ∈ s.primeFactors, pseudoChar f s p = ∏ p ∈ t, pseudoChar f s p := by
    refine Finset.prod_subset hst (fun x hxt hxs => ?_)
    have hxp := ht x hxt
    rw [pseudoChar_prime_right hf hxp s,
      if_neg (fun hd => hxs (Nat.mem_primeFactors.mpr ⟨hxp, hd, hs.ne_zero⟩))]
  have h2 : ∀ p ∈ s.primeFactors, pseudoChar f s p = f p := by
    intro p hp
    rw [pseudoChar_prime_right hf (Nat.prime_of_mem_primeFactors hp) s,
      if_pos (Nat.dvd_of_mem_primeFactors hp)]
  rw [← h1, Finset.prod_congr rfl h2, hf.prod_primeFactors hs]
  simp only [pseudoChar, Nat.gcd_zero_right]

/-- **Lemma 2 in the finite-range form** W9 swaps with the `n`-series: the `d`-sum over the
divisors of `r r'` that divide `n`. Valid at EVERY `n` (at `n = 0` every `d` divides `n` and
both sides are `f(r)·f(r')`). -/
theorem pseudoChar_mul_eq_sum_hCoef_filter (hf : f.IsMultiplicative) (hr : Squarefree r)
    (hr' : Squarefree r') (n : ℕ) :
    pseudoChar f r n * pseudoChar f r' n
      = ∑ d ∈ (r * r').divisors with d ∣ n, hCoef f r r' d := by
  classical
  have hrr0 : r * r' ≠ 0 := mul_ne_zero hr.ne_zero hr'.ne_zero
  by_cases hn : n = 0
  · subst hn
    rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d)]
    have hE : ∑ d ∈ (r * r').divisors, hCoef f r r' d
        = ∏ p ∈ (r * r').primeFactors, (1 + hCoef f r r' p) :=
      sum_divisors_eq_prod_primeFactors_of_squarefree_support hCoef_one
        (fun a b hab => (hCoef_isMultiplicative f r r').map_mul_of_coprime hab)
        (fun d hd => hCoef_of_not_squarefree hd) hrr0
    have hup : ∀ p ∈ r.primeFactors ∪ r'.primeFactors, Nat.Prime p := by
      intro p hp
      rcases Finset.mem_union.mp hp with hq | hq
      · exact Nat.prime_of_mem_primeFactors hq
      · exact Nat.prime_of_mem_primeFactors hq
    have hterm : ∀ p ∈ r.primeFactors ∪ r'.primeFactors,
        1 + hCoef f r r' p = pseudoChar f r p * pseudoChar f r' p := by
      intro p hp
      rw [hCoef_prime (hup p hp)]
      ring
    rw [hE, Nat.primeFactors_mul hr.ne_zero hr'.ne_zero, Finset.prod_congr rfl hterm,
      Finset.prod_mul_distrib, pseudoChar_zero_eq_prod hf hr Finset.subset_union_left hup,
      pseudoChar_zero_eq_prod hf hr' Finset.subset_union_right hup]
  · have hsub : Finset.filter (fun d => d ∣ n) (r * r').divisors ⊆ n.divisors := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mem_divisors.mpr ⟨hd.2, hn⟩
    have hzero : ∀ d ∈ n.divisors, d ∉ Finset.filter (fun d => d ∣ n) (r * r').divisors →
        hCoef f r r' d = 0 := by
      intro d hd hnd
      refine hCoef_eq_zero_of_not_dvd hf (fun hdvd => hnd ?_)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hrr0⟩, (Nat.mem_divisors.mp hd).1⟩
    rw [pseudoChar_mul_eq_sum_hCoef hf hr hr' hn]
    exact (Finset.sum_subset hsub hzero).symm

/-- The prime values for Selberg's `ψ = μφ` (`ψ(p) = 1 − p`): `p(p − 2)` on `p ∣ (r, r')`,
`−p` on `p` dividing exactly one of `r, r'`, `0` off `r r'`. -/
theorem hCoef_selbergPsi_prime {p : ℕ} (hp : p.Prime) :
    hCoef selbergPsi r r' p
      = if p ∣ r then (if p ∣ r' then (p : ℝ) * ((p : ℝ) - 2) else -(p : ℝ))
        else (if p ∣ r' then -(p : ℝ) else 0) := by
  rw [hCoef_prime hp, pseudoChar_prime_right selbergPsi_isMultiplicative hp r,
    pseudoChar_prime_right selbergPsi_isMultiplicative hp r', selbergPsi_apply_prime hp]
  split_ifs <;> ring

/-- **Lemma 3, the orthogonality (p.49).** `Σ_d h(d; r, r')/d = δ_{r,r'}·φ(r)` for square-free
`r, r'`: the local factor is `0` at a prime dividing exactly one level and `p − 1` at a common
prime; two square-free numbers with the same primes are equal. -/
theorem hCoef_sum_div_eq (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ d ∈ (r * r').divisors, hCoef selbergPsi r r' d / (d : ℝ)
      = if r = r' then (Nat.totient r : ℝ) else 0 := by
  rw [sum_divisors_hCoef_div_eq_prod (mul_ne_zero hr.ne_zero hr'.ne_zero)]
  split_ifs with hrr
  · subst hrr
    have hterm : ∀ p ∈ r.primeFactors,
        1 + hCoef selbergPsi r r p / (p : ℝ) = (p : ℝ) - 1 := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
      have hcancel : (p : ℝ) * ((p : ℝ) - 2) / (p : ℝ) = (p : ℝ) - 2 := by
        rw [mul_comm, mul_div_assoc, div_self hp0, mul_one]
      rw [hCoef_selbergPsi_prime hpp, if_pos hpd, if_pos hpd, hcancel]
      ring
    rw [Nat.primeFactors_mul hr.ne_zero hr.ne_zero, Finset.union_self,
      Finset.prod_congr rfl hterm]
    have hprodp : ∏ p ∈ r.primeFactors, p = r := Nat.prod_primeFactors_of_squarefree hr
    have h1 := Nat.totient_mul_prod_primeFactors r
    rw [hprodp, Nat.mul_comm (Nat.totient r) r] at h1
    have h2 : Nat.totient r = ∏ p ∈ r.primeFactors, (p - 1) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr.ne_zero) h1
    rw [h2, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  · have hne : ¬ ∀ p, Nat.Prime p → (p ∣ r ↔ p ∣ r') :=
      (Nat.Squarefree.ext_iff hr hr').not.mp hrr
    obtain ⟨p, hp, hpiff⟩ : ∃ p, Nat.Prime p ∧ ¬ (p ∣ r ↔ p ∣ r') := by
      by_contra hcon
      exact hne (fun p hp => not_not.mp (fun hnp => hcon ⟨p, hp, hnp⟩))
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hdvd : p ∣ r * r' := by
      by_cases hd : p ∣ r
      · exact hd.mul_right r'
      · have hd' : p ∣ r' := by
          by_contra hd2
          exact hpiff ⟨fun hq => absurd hq hd, fun hq => absurd hq hd2⟩
        exact hd'.mul_left r
    refine Finset.prod_eq_zero
      (Nat.mem_primeFactors.mpr ⟨hp, hdvd, mul_ne_zero hr.ne_zero hr'.ne_zero⟩) ?_
    rw [hCoef_selbergPsi_prime hp]
    by_cases hd : p ∣ r
    · have hd' : ¬ p ∣ r' := fun hq => hpiff ⟨fun _ => hq, fun _ => hd⟩
      rw [if_pos hd, if_neg hd', neg_div, div_self hp0]
      ring
    · have hd' : p ∣ r' := by
        by_contra hd2
        exact hpiff ⟨fun hq => absurd hq hd, fun hq => absurd hq hd2⟩
      rw [if_neg hd, if_pos hd', neg_div, div_self hp0]
      ring

/-- **Lemma 3, the size (p.49).** `Σ_d |h(d; r, r')| ≤ ∏_{p ∣ r} (p + 1) · ∏_{p ∣ r'} (p + 1)`:
the local factor `1 + |h(p)|` is `1 + p` at a prime of exactly one level and
`1 + p(p − 2) = (p − 1)² ≤ (p + 1)²` at a common prime. Equality on coprime pairs. -/
theorem hCoef_abs_sum_le (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ d ∈ (r * r').divisors, |hCoef selbergPsi r r' d|
      ≤ (∏ p ∈ r.primeFactors, ((p : ℝ) + 1)) * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1) := by
  classical
  rw [sum_divisors_abs_hCoef_eq_prod (mul_ne_zero hr.ne_zero hr'.ne_zero),
    Nat.primeFactors_mul hr.ne_zero hr'.ne_zero,
    ← Finset.prod_union_inter (s₁ := r.primeFactors) (s₂ := r'.primeFactors)
      (f := fun p => ((p : ℝ) + 1))]
  have hinter : ∏ p ∈ r.primeFactors ∩ r'.primeFactors, ((p : ℝ) + 1)
      = ∏ p ∈ r.primeFactors ∪ r'.primeFactors,
          (if p ∈ r.primeFactors ∩ r'.primeFactors then ((p : ℝ) + 1) else 1) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.inter_subset_union]
  rw [hinter, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  have hpp : Nat.Prime p := by
    rcases Finset.mem_union.mp hp with hq | hq
    · exact Nat.prime_of_mem_primeFactors hq
    · exact Nat.prime_of_mem_primeFactors hq
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  rw [hCoef_selbergPsi_prime hpp]
  by_cases hd : p ∣ r
  · by_cases hd' : p ∣ r'
    · have hmem : p ∈ r.primeFactors ∩ r'.primeFactors :=
        Finset.mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hd, hr.ne_zero⟩,
          Nat.mem_primeFactors.mpr ⟨hpp, hd', hr'.ne_zero⟩⟩
      rw [if_pos hd, if_pos hd', if_pos hmem,
        abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 2))]
      nlinarith
    · have hnm : p ∉ r.primeFactors ∩ r'.primeFactors := fun hq =>
        hd' (Nat.dvd_of_mem_primeFactors (Finset.mem_inter.mp hq).2)
      rw [if_pos hd, if_neg hd', if_neg hnm, abs_neg,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ)), mul_one]
      linarith
  · have hnm : p ∉ r.primeFactors ∩ r'.primeFactors := fun hq =>
      hd (Nat.dvd_of_mem_primeFactors (Finset.mem_inter.mp hq).1)
    by_cases hd' : p ∣ r'
    · rw [if_neg hd, if_pos hd', if_neg hnm, abs_neg,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ)), mul_one]
      linarith
    · rw [if_neg hd, if_neg hd', if_neg hnm, abs_zero, mul_one]
      linarith

/-- **The W5 exit rows** (measured: `Σ h/d = 1 = φ(2)` at `(2, 2)`, `= 0` at `(2, 3)`;
`ψ_6(30)·ψ_10(30) = 8 = Σ_{d ∣ 30} h(d; 6, 10)`). Each INVOKES a frozen row. -/
example : ∑ d ∈ (2 * 2).divisors, hCoef selbergPsi 2 2 d / (d : ℝ) = 1 := by
  rw [hCoef_sum_div_eq Nat.prime_two.squarefree Nat.prime_two.squarefree]
  simp [Nat.totient_two]

example : ∑ d ∈ (2 * 3).divisors, hCoef selbergPsi 2 3 d / (d : ℝ) = 0 := by
  rw [hCoef_sum_div_eq Nat.prime_two.squarefree Nat.prime_three.squarefree]
  simp

example : pseudoChar selbergPsi 6 30 * pseudoChar selbergPsi 10 30
    = ∑ d ∈ (30 : ℕ).divisors, hCoef selbergPsi 6 10 d :=
  pseudoChar_mul_eq_sum_hCoef selbergPsi_isMultiplicative
    (by rw [show (6 : ℕ) = 2 * 3 from rfl]
        exact Nat.squarefree_mul_iff.mpr
          ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)
    (by rw [show (10 : ℕ) = 2 * 5 from rfl]
        exact Nat.squarefree_mul_iff.mpr
          ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_five.squarefree⟩)
    (by norm_num)

end Salt.SW
