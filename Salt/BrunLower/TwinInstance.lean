/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Pair
import Salt.BrunLower.MertensDischarge

/-!
# P1 — the twin almost-prime headline (blueprint `p0`, node P1)

The capstone of the `p0` rung: an unconditional, kernel-checked proof of

```
theorem twin_almost_prime : {n : ℕ | Ω (n * (n + 2)) ≤ 20}.Infinite
```

(`Ω = ArithmeticFunction.cardFactors`, prime factors with multiplicity).  Assembled by
instantiating the both-sided Brun sieve `brun_lower` (node B5) at the TwinSieve
(`Salt/Brun/Sieve.lean`) at the PRIMARY operating point `b = 2`, `λ = 1/4`, `A = 2`, with
the `hMert` discharge `hMert_twinSieve` (node PM2) and the windowed Mertens estimates
(node PM1) supplying the density inputs.

## The chain

For a real `z ≥ zOne := exp (exp 50000)` (astronomical, per H-R's "z large"; `zOne`
dominates every threshold), set `P := ∏_{p < z} p` (squarefree), `N := ⌈z^(103/10)⌉₊`,
`s := TwinSieve.sieve N P`.  Then

* `brun_lower` gives `s.siftedSum ≥ N·W(z)·margin − Rem`;
* `W_twin_ge`: `W(z) ≥ e^{-70}/(log z)²` (from the pointwise `−log(1−ν) ≤ 2/p + 12/p²` and
  PM1's full-range windowed Mertens at `w = 2`);
* `margin_ge`: `margin ≥ 9/10` (the +0.946 main-term margin, crude exp bounds);
* the remainder `Rem ≤ 125·25^{r-1}·exp((3 + 2/(e^Λ-1))·log z)` with the level exponent
  `3 + 2/(e^Λ-1) ≤ 10.2 < 10.3`, so `N·W·margin > Rem` and `s.siftedSum > 0`;
* a survivor `n` has `n(n+2)` coprime to `P`, hence all its prime factors `≥ z`, so
  `z^{Ω(n(n+2))} ≤ n(n+2) ≤ N(N+2) < z^{21}` gives `Ω(n(n+2)) ≤ 20`, and `z ≤ n + 2`;
* letting `z → ∞` gives infinitely many such `n` (`Set.infinite_of_forall_exists_gt`).

`Halberstam–Richert, "A new look at Brun's sieve", Mém. SMF 25 (1971) 97–106`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace Salt.BrunLower

/-! ## Numeric exp bounds (all via `Real.exp_one_lt_d9`) -/

/-- `exp 5 < 148.5` (the workhorse for every exp upper bound below). -/
lemma exp_five_lt : Real.exp 5 < 148.5 := by
  have h1 : Real.exp 1 < 2.7183 := by have := Real.exp_one_lt_d9; linarith
  have h0 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hpow : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [hpow]
  calc (Real.exp 1) ^ 5 < 2.7183 ^ 5 := pow_lt_pow_left₀ h1 h0 (by norm_num)
    _ < 148.5 := by norm_num

/-- `exp (1/2) ≤ 1.65`. -/
lemma exp_half_le : Real.exp (1/2 : ℝ) ≤ 1.65 := by
  have h5 : Real.exp 1 < 2.7225 := by have := Real.exp_one_lt_d9; linarith
  have hsq : (Real.exp (1/2:ℝ)) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1/2:ℝ), hsq, h5]

/-- `exp (5/2) ≤ 12.2`. -/
lemma exp_five_halves_le : Real.exp (5/2 : ℝ) ≤ 12.2 := by
  have hsq : (Real.exp (5/2:ℝ)) ^ 2 = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (5/2:ℝ), hsq, exp_five_lt]

/-- `exp (5/4) < 4` (equivalently `exp 5 < 256`), the `h12` input. -/
lemma exp_five_quarters_lt : Real.exp (5/4 : ℝ) < 4 := by
  have hpow : (Real.exp (5/4:ℝ)) ^ 4 = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h : (Real.exp (5/4:ℝ)) ^ 4 < (4:ℝ) ^ 4 := by rw [hpow]; nlinarith [exp_five_lt]
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).mp h

/-- The second-order lower bound `1 + x + x²/2 ≤ exp x` for `x ≥ 0` (the load-bearing
convexity fact: it beats `1 + x` by enough to keep `2/(e^Λ - 1)` below `7.2`). -/
lemma exp_quad_lower {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  have hmono : MonotoneOn (fun t => Real.exp t - (1 + t + t ^ 2 / 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (Real.continuous_exp.sub (by fun_prop)).continuousOn
    · intro t _
      exact ((Real.differentiable_exp t).sub (by fun_prop)).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t => Real.exp t - (1 + t + t ^ 2 / 2))
          (Real.exp t - (1 + t)) t := by
        have e1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
          have h := (hasDerivAt_pow 2 t).div_const 2
          have he : ((2:ℕ):ℝ) * t ^ (2 - 1) / 2 = t := by norm_num
          rwa [he] at h
        have e2 : HasDerivAt (fun t : ℝ => (1:ℝ) + t) 1 t := by
          simpa using (hasDerivAt_id t).const_add (1:ℝ)
        exact (Real.hasDerivAt_exp t).sub (e2.add e1)
      rw [hd.deriv]
      have := Real.add_one_le_exp t
      linarith
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hx) hx
  simp only [Real.exp_zero] at this
  nlinarith [this]

/-! ## `π(m) ≤ m + 1` and `z^{Ω m} ≤ m` -/

/-- Crude prime-counting bound `π(m) ≤ m + 1` (all we need for the remainder numerics —
the level arithmetic has enough slack that the `log`-refinement is unnecessary). -/
lemma primeCounting_le (m : ℕ) : (Nat.primeCounting m : ℝ) ≤ (m:ℝ) + 1 := by
  have : Nat.primeCounting m ≤ m + 1 := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
    calc (Finset.filter Nat.Prime (Finset.range (m+1))).card
        ≤ (Finset.range (m+1)).card := Finset.card_filter_le _ _
      _ = m + 1 := by rw [Finset.card_range]
  exact_mod_cast this

/-- If every prime factor of `m ≠ 0` is `≥ z` (a real `≥ 1`), then `z^{Ω m} ≤ m`.  Product
of `Ω m` primes each `≥ z`, with multiplicity.  Strong induction peeling `minFac`. -/
lemma pow_cardFactors_le (z : ℝ) (hz1 : 1 ≤ z) : ∀ m : ℕ, m ≠ 0 →
    (∀ p ∈ m.primeFactors, z ≤ (p:ℝ)) → z ^ (Ω m) ≤ (m:ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hp
    rcases eq_or_ne m 1 with rfl | hm1
    · simp
    · set p := m.minFac with hpdef
      have hpprime : p.Prime := Nat.minFac_prime hm1
      obtain ⟨k, hk⟩ : p ∣ m := Nat.minFac_dvd m
      have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hm
      have hklt : k < m := by
        rw [hk]; nlinarith [hpprime.two_le, Nat.pos_of_ne_zero hk0, Nat.pos_of_ne_zero hm]
      have hpmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hpprime, ⟨k, hk⟩, hm⟩
      have hzp : z ≤ (p:ℝ) := hp p hpmem
      have hksub : ∀ q ∈ k.primeFactors, z ≤ (q:ℝ) := by
        intro q hq
        apply hp
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1, hq.2.1.trans ⟨p, by rw [hk]; ring⟩, hm⟩
      have hind : z ^ (Ω k) ≤ (k:ℝ) := ih k hklt hk0 hksub
      have hΩ : Ω m = 1 + Ω k := by
        rw [hk, ArithmeticFunction.cardFactors_mul hpprime.ne_zero hk0,
          ArithmeticFunction.cardFactors_apply_prime hpprime]
      rw [hΩ, pow_add, pow_one, hk]
      push_cast
      have hzpow : (0:ℝ) ≤ z ^ (Ω k) := by positivity
      calc z * z ^ (Ω k) ≤ (p:ℝ) * (k:ℝ) := mul_le_mul hzp hind hzpow (by positivity)

/-! ## The threshold `zOne` and its facts -/

/-- The astronomical positivity threshold `zOne = exp(exp 50000)`.  Dominates
`zThresh (1/4) = exp(exp 400)` (so PM2's `hMert` fires) and forces `loglog z ≥ 50000`
(so the ladder scale `Λ ≥ 0.2494`, keeping the level exponent below `10.2`). -/
noncomputable def zOne : ℝ := Real.exp (Real.exp 50000)

/-- Facts extracted from `z ≥ zOne`. -/
lemma zOne_facts {z : ℝ} (hz : zOne ≤ z) :
    (1:ℝ) < z ∧ 0 < Real.log z ∧ (50000:ℝ) ≤ Real.log (Real.log z) ∧
      (Real.log (Real.log z))^2 / 4 ≤ Real.log z ∧
      zThresh (1/4) ≤ z := by
  have he50 : (0:ℝ) < Real.exp 50000 := Real.exp_pos _
  have hz0 : (0:ℝ) < zOne := Real.exp_pos _
  -- log z ≥ exp 50000
  have hlogz_ge : Real.exp 50000 ≤ Real.log z := by
    have := Real.log_le_log hz0 hz
    simpa only [zOne, Real.log_exp] using this
  have hlz_pos : 0 < Real.log z := lt_of_lt_of_le he50 hlogz_ge
  have hz1 : (1:ℝ) < z := by
    have h1 : (1:ℝ) < Real.exp (Real.exp 50000) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr he50
    exact lt_of_lt_of_le h1 hz
  -- loglog z ≥ 50000
  have hllz : (50000:ℝ) ≤ Real.log (Real.log z) := by
    have := Real.log_le_log he50 hlogz_ge
    rwa [Real.log_exp] at this
  have hllz_pos : 0 < Real.log (Real.log z) := by linarith
  -- log z = exp(loglog z) ≥ (loglog z)²/4
  have hlz_eq : Real.log z = Real.exp (Real.log (Real.log z)) := (Real.exp_log hlz_pos).symm
  have hquad : (Real.log (Real.log z))^2 / 4 ≤ Real.log z := by
    have h := Real.add_one_le_exp (Real.log (Real.log z) / 2)
    have hexppos : 0 < Real.exp (Real.log (Real.log z) / 2) := Real.exp_pos _
    have h2 : (1 + Real.log (Real.log z) / 2)^2 ≤ (Real.exp (Real.log (Real.log z) / 2))^2 := by
      apply sq_le_sq' <;> nlinarith [hexppos, hllz_pos]
    have h3 : (Real.exp (Real.log (Real.log z) / 2))^2 = Real.exp (Real.log (Real.log z)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    nlinarith [h2, h3, hllz_pos, hlz_eq]
  -- zThresh (1/4) ≤ z
  have hzth : zThresh (1/4) ≤ z := by
    refine le_trans ?_ hz
    simp only [zThresh, zOne]
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    norm_num
  exact ⟨hz1, hlz_pos, hllz, hquad, hzth⟩

/-! ## The sifting modulus `P = ∏_{p < z} p` -/

/-- The sifting modulus: the product of all primes `< z`. -/
noncomputable def Pz (z : ℝ) : ℕ := ∏ p ∈ (Finset.range ⌈z⌉₊).filter Nat.Prime, p

/-- A product of distinct primes is squarefree. -/
lemma prod_primes_squarefree {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha IH =>
    have haP : a.Prime := hS a (Finset.mem_insert_self a S)
    have hSP : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    refine ⟨?_, haP.prime.squarefree, IH hSP⟩
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes haP (hSP p hp)).mpr (by rintro rfl; exact ha hp)

lemma Pz_squarefree (z : ℝ) : Squarefree (Pz z) :=
  prod_primes_squarefree (fun _ hp => (Finset.mem_filter.mp hp).2)

lemma Pz_primeFactors (z : ℝ) :
    (Pz z).primeFactors = (Finset.range ⌈z⌉₊).filter Nat.Prime :=
  Nat.primeFactors_prod (fun _ hp => (Finset.mem_filter.mp hp).2)

/-- `p ∈ P.primeFactors ↔ p` prime and `p < z`. -/
lemma mem_Pz_primeFactors {z : ℝ} {p : ℕ} :
    p ∈ (Pz z).primeFactors ↔ p.Prime ∧ (p : ℝ) < z := by
  rw [Pz_primeFactors, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil, and_comm]

/-- Every prime `< z` divides `P` (the coprimality bridge). -/
lemma prime_lt_dvd_Pz {z : ℝ} {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) < z) : p ∣ Pz z := by
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  exact ⟨hpz, hp⟩

/-! ## The remainder weight `ω = ρ` is multiplicative on squarefrees -/

/-- `ρ` is a product over prime factors, for squarefree `d` (the `hωprod` input, cast to ℝ). -/
lemma rho_prod_primeFactors : ∀ d : ℕ, Squarefree d →
    (rho d : ℝ) = ∏ p ∈ d.primeFactors, (rho p : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with rfl | hd1
    · simp [show rho 1 = 1 by decide, Nat.primeFactors_one]
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨d', rfl⟩ := hpd
      have hcop : p.Coprime d' := (Nat.squarefree_mul_iff.mp hd).1
      have hd'sq : Squarefree d' := (Nat.squarefree_mul_iff.mp hd).2.2
      have hd'ne0 : d' ≠ 0 := hd'sq.ne_zero
      have hd'lt : d' < p * d' := by
        nlinarith [hp.two_le, Nat.pos_of_ne_zero hd'ne0]
      have hind := ih d' hd'lt hd'sq
      rw [rho_mul_of_coprime hp.ne_zero hd'ne0 hcop]
      push_cast
      rw [Nat.primeFactors_mul hp.ne_zero hd'ne0, Finset.prod_union hcop.disjoint_primeFactors,
        hp.primeFactors, Finset.prod_singleton, ← hind]

/-! ## The `W`-lower bound `W(z) ≥ e^{-70}/(log z)²` -/

/-- **W-lower** (`W_twin_ge`).  For the twin sieve with all sifting primes `< z`,
`W(z) ≥ e^{-70}/(log z)²`.  From the pointwise `−log(1−ν(p)) ≤ 2/p + 12/p²` (PM2) summed
over `[2, z)` via PM1's full-range windowed Mertens (`w = 2`) and the `Σ 1/p²` telescope. -/
lemma W_twin_ge {N P : ℕ} (hP : Squarefree P) {z : ℝ} (hz2 : 2 ≤ z)
    (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    Real.exp (-70) / (Real.log z)^2 ≤ W (Salt.TwinSieve.sieve N P hP) := by
  set s := Salt.TwinSieve.sieve N P hP with hs
  have hz1 : (1:ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpf : s.prodPrimes.primeFactors = P.primeFactors := by
    rw [hs, Salt.TwinSieve.sieve_prodPrimes]
  have hnu2 : (2:ℕ) ∈ s.prodPrimes.primeFactors → s.nu 2 ≤ 1/2 := by
    intro _
    rw [hs, Salt.TwinSieve.sieve_nu, Salt.TwinSieve.nu_apply, rho_two]; norm_num
  have hnuodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 → s.nu q ≤ 2/q := by
    intro q hq hq2
    rw [hpf] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    rw [hs, Salt.TwinSieve.sieve_nu, Salt.TwinSieve.nu_apply, rho_odd_prime hqp hq2]
    norm_num
  have hlogW : Real.log (W s) = ∑ p ∈ s.prodPrimes.primeFactors, Real.log (1 - s.nu p) := by
    unfold W
    rw [Real.log_prod]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
    have := s.nu_lt_one_of_prime p hpp hpd
    exact ne_of_gt (by linarith)
  have hbound : -Real.log (W s)
      ≤ ∑ p ∈ s.prodPrimes.primeFactors, (2/(p:ℝ) + 12/(p:ℝ)^2) := by
    rw [hlogW, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    exact neg_log_one_sub_nu_le s hp hnu2 hnuodd
  have hsumle : ∑ p ∈ s.prodPrimes.primeFactors, (2/(p:ℝ) + 12/(p:ℝ)^2)
      ≤ 2 * Real.log (Real.log z) + 70 := by
    rw [hpf]
    have hsplit : ∑ p ∈ P.primeFactors, (2/(p:ℝ) + 12/(p:ℝ)^2)
        = 2 * (∑ p ∈ P.primeFactors, (1:ℝ)/p)
          + 12 * (∑ p ∈ P.primeFactors, (1:ℝ)/(p:ℝ)^2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [hsplit]
    have hinv : ∑ p ∈ P.primeFactors, (1:ℝ)/p
        ≤ Real.log (Real.log z / Real.log 2) + 19 / Real.log 2 := by
      apply sum_inv_le_of_prime_window (by norm_num) hz2
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact ⟨hpp, by exact_mod_cast hpp.two_le, hpz p hp⟩
    have hsq : ∑ p ∈ P.primeFactors, (1:ℝ)/(p:ℝ)^2 ≤ 1 := by
      have hsub : P.primeFactors ⊆ Finset.Icc 2 ⌊z⌋₊ := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        rw [Finset.mem_Icc]
        exact ⟨hpp.two_le, Nat.le_floor (le_of_lt (hpz p hp))⟩
      have hstep : ∑ p ∈ P.primeFactors, (1:ℝ)/(p:ℝ)^2
          ≤ ∑ p ∈ Finset.Icc 2 ⌊z⌋₊, (1:ℝ)/(p:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have hkey := sum_one_div_sq_le (M := 2) (K := ⌊z⌋₊) (by norm_num)
      have hval : (1:ℝ)/(((2:ℕ):ℝ) - 1) = 1 := by norm_num
      linarith [hstep, hkey, hval]
    have hlogdiv : Real.log (Real.log z / Real.log 2)
        = Real.log (Real.log z) - Real.log (Real.log 2) := Real.log_div hlogz.ne' hlog2.ne'
    have hlog2gt : (0.6931:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hnll2 : -Real.log (Real.log 2) ≤ 1 := by
      have hexp1 : Real.exp (-1 : ℝ) ≤ Real.log 2 := by
        have he1 : (2.7:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        rw [show Real.exp (-1:ℝ) = 1 / Real.exp 1 by rw [Real.exp_neg]; ring,
          div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [he1, hlog2gt]
      have := Real.log_le_log (Real.exp_pos _) hexp1
      rw [Real.log_exp] at this
      linarith
    have h19 : 19 / Real.log 2 ≤ 28 := by
      rw [div_le_iff₀ hlog2]; nlinarith [hlog2gt]
    linarith [hinv, hsq, hnll2, h19, hlogdiv]
  have hlogW_ge : -(2 * Real.log (Real.log z) + 70) ≤ Real.log (W s) := by
    linarith [hbound, hsumle]
  have hWpos : 0 < W s := W_pos s
  have hexp2 : Real.exp (2 * Real.log (Real.log z)) = (Real.log z)^2 := by
    rw [show (2:ℝ) * Real.log (Real.log z)
        = Real.log (Real.log z) + Real.log (Real.log z) by ring,
      Real.exp_add, Real.exp_log hlogz]
    ring
  have hWge : Real.exp (-(2 * Real.log (Real.log z) + 70)) ≤ W s := by
    calc Real.exp (-(2 * Real.log (Real.log z) + 70))
        ≤ Real.exp (Real.log (W s)) := Real.exp_le_exp.mpr hlogW_ge
      _ = W s := Real.exp_log hWpos
  have hid : Real.exp (-(2 * Real.log (Real.log z) + 70))
      = Real.exp (-70) / (Real.log z)^2 := by
    rw [show -(2 * Real.log (Real.log z) + 70)
        = (-70) + (-(2 * Real.log (Real.log z))) by ring, Real.exp_add,
      Real.exp_neg (2 * Real.log (Real.log z)), hexp2, div_eq_mul_inv]
  rw [hid] at hWge
  exact hWge

/-! ## The main-term margin `margin ≥ 9/10` -/

/-- **Main-term margin** (`margin_ge`).  At `b = 2`, `λ = 1/4` the H-R main-term factor
`1 − 2λ^{2b}e^{2λ}/(1 − λ²e^{2+2λ})` is `≥ 9/10` (the true value is `+0.946`; crude exp
bounds `e^{1/2} ≤ 1.65`, `e^{5/2} ≤ 12.2`). -/
lemma margin_ge :
    (9:ℝ)/10 ≤ 1 - 2 * (1/4 : ℝ) ^ (2 * 2) * Real.exp (2 * (1/4))
      / (1 - (1/4) ^ 2 * Real.exp (2 + 2 * (1/4))) := by
  have he12 : Real.exp (2 * (1/4:ℝ)) ≤ 1.65 := by
    rw [show (2 * (1/4:ℝ)) = 1/2 by norm_num]; exact exp_half_le
  have he52 : Real.exp (2 + 2 * (1/4:ℝ)) ≤ 12.2 := by
    rw [show (2 + 2 * (1/4:ℝ)) = 5/2 by norm_num]; exact exp_five_halves_le
  have he12pos : 0 < Real.exp (2 * (1/4:ℝ)) := Real.exp_pos _
  have he52pos : 0 < Real.exp (2 + 2 * (1/4:ℝ)) := Real.exp_pos _
  set E1 := Real.exp (2 * (1/4:ℝ)) with hE1
  set E2 := Real.exp (2 + 2 * (1/4:ℝ)) with hE2
  have hden : 0 < 1 - (1/4:ℝ) ^ 2 * E2 := by nlinarith [he52]
  have hnum : 2 * (1/4:ℝ) ^ (2 * 2) * E1 / (1 - (1/4) ^ 2 * E2) ≤ 1/10 := by
    rw [div_le_iff₀ hden]
    have h4 : (1/4:ℝ) ^ (2 * 2) = 1/256 := by norm_num
    have h2 : (1/4:ℝ) ^ 2 = 1/16 := by norm_num
    rw [h4, h2]
    nlinarith [he12, he52, he12pos, he52pos]
  linarith [hnum]

/-! ## The remainder product upper bound -/

/-- The remainder product `(1 + 2π(⌊z⌋))³ · ∏_{n=1}^{r-1} (1 + 2π(⌊z_n⌋))²` is bounded by
`125·25^{r-1}·exp((3 + 2/(e^Λ-1))·log z)`.  Route: `1 + 2π(⌊w⌋) ≤ 5w` (crude `π ≤ ·+1`),
`∏ z_n² = exp(2·log z·Σ e^{-nΛ})`, and the geometric `Σ_{n≥1} e^{-nΛ} ≤ 1/(e^Λ-1)`. -/
lemma remainder_upper {Lam z : ℝ} (hz1 : 1 < z) (hLam : 0 < Lam) :
    (1 + 2 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ 3
      * ∏ n ∈ Finset.Ico 1 (minLevel Lam z),
          (1 + 2 * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2
    ≤ 125 * 25 ^ (minLevel Lam z - 1)
        * Real.exp ((3 + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z) := by
  have hL : 0 < Real.log z := Real.log_pos hz1
  set r := minLevel Lam z with hr
  -- `1 + 2π(⌊w⌋) ≤ 5w` for `w ≥ 1`.
  have hpi5 : ∀ w : ℝ, 1 ≤ w → 1 + 2 * (Nat.primeCounting ⌊w⌋₊ : ℝ) ≤ 5 * w := by
    intro w hw
    have h1 := primeCounting_le ⌊w⌋₊
    have h2 : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le (by linarith)
    linarith
  -- each ladder value `z_n ≥ 1`.
  have hzn1 : ∀ n, (1:ℝ) ≤ zLev Lam z n := by
    intro n
    rw [zLev, show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (mul_nonneg (Real.exp_pos _).le hL.le)
  -- top factor.
  have htop : (1 + 2 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ 3 ≤ (5 * z) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (hpi5 z hz1.le) 3
  -- interior product.
  have hprod_le : ∏ n ∈ Finset.Ico 1 r, (1 + 2 * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2
      ≤ ∏ n ∈ Finset.Ico 1 r, (5 * zLev Lam z n) ^ 2 := by
    apply Finset.prod_le_prod
    · intro n _; positivity
    · intro n _; exact pow_le_pow_left₀ (by positivity) (hpi5 _ (hzn1 n)) 2
  -- `∏ (5 z_n)² = 25^{r-1} · ∏ z_n²`.
  have hsplit : ∏ n ∈ Finset.Ico 1 r, (5 * zLev Lam z n) ^ 2
      = 25 ^ (r - 1) * ∏ n ∈ Finset.Ico 1 r, (zLev Lam z n) ^ 2 := by
    rw [Finset.prod_congr rfl
        (fun n _ => show (5 * zLev Lam z n) ^ 2 = 25 * (zLev Lam z n) ^ 2 by ring),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  -- `∏ z_n² = exp(2·log z·Σ e^{-nΛ})`.
  have hprodz : ∏ n ∈ Finset.Ico 1 r, (zLev Lam z n) ^ 2
      = Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro n _
    rw [zLev, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  -- geometric bound `Σ e^{-nΛ} ≤ 1/(e^Λ-1)`.
  have hgeom : ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam)) ≤ (Real.exp Lam - 1)⁻¹ := by
    have hx0 : (0:ℝ) ≤ Real.exp (-Lam) := (Real.exp_pos _).le
    have hx1 : Real.exp (-Lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have hcast : ∀ n : ℕ, Real.exp (-(↑n * Lam)) = (Real.exp (-Lam)) ^ n := by
      intro n; rw [← Real.exp_nat_mul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun n _ => hcast n)]
    have hgs := geom_sum_Ico_le_of_lt_one hx0 hx1 (m := 1) (n := r)
    have hEpos : (0:ℝ) < Real.exp Lam := Real.exp_pos _
    have hE1 : (1:ℝ) < Real.exp Lam := by have := Real.add_one_le_exp Lam; linarith
    have hident : Real.exp (-Lam) ^ 1 / (1 - Real.exp (-Lam)) = (Real.exp Lam - 1)⁻¹ := by
      rw [pow_one, Real.exp_neg]
      have hEne : Real.exp Lam ≠ 0 := hEpos.ne'
      have hlt1 : (Real.exp Lam)⁻¹ < 1 := (inv_lt_one₀ hEpos).mpr hE1
      have h1 : (1:ℝ) - (Real.exp Lam)⁻¹ ≠ 0 := ne_of_gt (by linarith)
      have h2 : Real.exp Lam - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    rw [hident] at hgs
    exact hgs
  -- assemble.
  have hexpcomb : Real.exp (3 * Real.log z)
        * Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam)))
      = Real.exp ((3 + 2 * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))) * Real.log z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmain : (5 * z) ^ 3 * (25 ^ (r - 1)
        * Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))))
      = 125 * 25 ^ (r - 1)
        * Real.exp ((3 + 2 * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))) * Real.log z) := by
    have hz3 : (5 * z) ^ 3 = 125 * Real.exp (3 * Real.log z) := by
      rw [show (5 * z) ^ 3 = 125 * z ^ 3 by ring]
      congr 1
      rw [← Real.exp_log (show (0:ℝ) < z ^ 3 by positivity), Real.log_pow]; norm_num
    rw [hz3, show (125 * Real.exp (3 * Real.log z)) * (25 ^ (r - 1)
          * Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))))
        = 125 * 25 ^ (r - 1) * (Real.exp (3 * Real.log z)
          * Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam)))) by ring,
      hexpcomb]
  calc (1 + 2 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ 3
          * ∏ n ∈ Finset.Ico 1 r, (1 + 2 * (Nat.primeCounting ⌊zLev Lam z n⌋₊ : ℝ)) ^ 2
      ≤ (5 * z) ^ 3 * ∏ n ∈ Finset.Ico 1 r, (5 * zLev Lam z n) ^ 2 := by
        apply mul_le_mul htop hprod_le (Finset.prod_nonneg (fun n _ => by positivity))
        positivity
    _ = (5 * z) ^ 3 * (25 ^ (r - 1)
          * Real.exp (2 * Real.log z * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam)))) := by
        rw [hsplit, hprodz]
    _ = 125 * 25 ^ (r - 1)
          * Real.exp ((3 + 2 * ∑ n ∈ Finset.Ico 1 r, Real.exp (-(↑n * Lam))) * Real.log z) := hmain
    _ ≤ 125 * 25 ^ (r - 1) * Real.exp ((3 + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hL.le
        linarith [hgeom]

/-! ## The survivor lemma and the headline -/

/-- The numeric heart of the positivity: `125·25^{r-1}·exp(10.2L) < (9/10)·exp(-70)·exp(10.3L)/L²`.
Given `log L ≥ 50000` and `L ≥ (log L)²/4`, the astronomical `L` swallows the `r-1` factor
(bounded via `(r-1)·Λ ≤ log L + 1`, `Λ ≥ 0.2494`). -/
lemma crux_numeric {L Lam : ℝ} {r : ℕ} (hLpos : 0 < L)
    (hLL : (50000 : ℝ) ≤ Real.log L) (hquad : (Real.log L) ^ 2 / 4 ≤ L)
    (hLam_lb : (0.2494 : ℝ) ≤ Lam) (hr_ub : (↑(r - 1) : ℝ) * Lam ≤ Real.log L + 1) :
    125 * (25:ℝ) ^ (r - 1) * Real.exp (10.2 * L)
      < (9/10) * Real.exp (-70) * Real.exp (10.3 * L) / L ^ 2 := by
  have hExp2 : L ^ 2 = Real.exp (2 * Real.log L) := by
    rw [show (2:ℝ) * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
      Real.exp_log hLpos]; ring
  have hlog125 : Real.log 125 ≤ 5 := by
    have hexp5gt : (143:ℝ) < Real.exp 5 := by
      have h : (2.7:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have he : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      calc (143:ℝ) < 2.7 ^ 5 := by norm_num
        _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
    rw [show (5:ℝ) = Real.log (Real.exp 5) from (Real.log_exp _).symm]
    exact Real.log_le_log (by norm_num) (by linarith [hexp5gt])
  have hlog25 : Real.log 25 ≤ 3.3 := by
    have hexp165 : (5:ℝ) < Real.exp 1.65 := by
      rw [show (1.65:ℝ) = 1 + 0.65 by norm_num, Real.exp_add]
      have h1 : (2.7:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h2 : (1.86:ℝ) ≤ Real.exp 0.65 := by
        have h := exp_quad_lower (show (0:ℝ) ≤ 0.65 by norm_num); nlinarith [h]
      have hp : (2.7:ℝ) * 1.86 ≤ Real.exp 1 * Real.exp 0.65 :=
        mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
      linarith [hp]
    have hlog5 : Real.log 5 ≤ 1.65 := by
      rw [show (1.65:ℝ) = Real.log (Real.exp 1.65) from (Real.log_exp _).symm]
      exact Real.log_le_log (by norm_num) (by linarith [hexp165])
    rw [show (25:ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith [hlog5]
  have hlog910 : (-1:ℝ) ≤ Real.log (9/10) := by
    rw [show (-1:ℝ) = Real.log (Real.exp (-1)) from (Real.log_exp _).symm]
    apply Real.log_le_log (Real.exp_pos _)
    rw [show Real.exp (-1:ℝ) = 1 / Real.exp 1 by rw [Real.exp_neg]; ring,
      div_le_iff₀ (Real.exp_pos 1)]
    have := Real.exp_one_gt_d9; nlinarith [this]
  have h25 : (25:ℝ) ^ (r - 1) = Real.exp (↑(r - 1) * Real.log 25) := by
    rw [← Real.exp_log (show (0:ℝ) < (25:ℝ) ^ (r - 1) by positivity), Real.log_pow]
  have hLHS' : 125 * (25:ℝ) ^ (r - 1) * Real.exp (10.2 * L) * Real.exp (2 * Real.log L)
      = Real.exp (Real.log 125 + ↑(r - 1) * Real.log 25 + 10.2 * L + 2 * Real.log L) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log (show (0:ℝ) < 125 by norm_num), ← h25]
  have hRHS' : (9/10:ℝ) * Real.exp (-70) * Real.exp (10.3 * L)
      = Real.exp (Real.log (9/10) + (-70) + 10.3 * L) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (show (0:ℝ) < 9/10 by norm_num)]
  rw [lt_div_iff₀ (show (0:ℝ) < L ^ 2 by positivity), hExp2, hLHS', hRHS', Real.exp_lt_exp]
  have hr_ub2 : (↑(r - 1) : ℝ) ≤ (Real.log L + 1) / 0.2494 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 0.2494)]
    calc (↑(r - 1) : ℝ) * 0.2494 ≤ (↑(r - 1)) * Lam :=
          mul_le_mul_of_nonneg_left hLam_lb (by positivity)
      _ ≤ Real.log L + 1 := hr_ub
  have h_r25 : (↑(r - 1) : ℝ) * Real.log 25 ≤ ((Real.log L + 1) / 0.2494) * 3.3 :=
    mul_le_mul hr_ub2 hlog25 (Real.log_nonneg (by norm_num)) (by positivity)
  have h_r25' : (↑(r - 1) : ℝ) * Real.log 25 ≤ 13.24 * (Real.log L + 1) := by
    have hh : ((Real.log L + 1) / 0.2494) * 3.3 ≤ 13.24 * (Real.log L + 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 0.2494)]
      nlinarith [hLL]
    linarith [h_r25, hh]
  have hprod : (50000:ℝ) * Real.log L ≤ (Real.log L) ^ 2 := by
    nlinarith [hLL, mul_nonneg (show (0:ℝ) ≤ Real.log L by linarith [hLL])
      (show (0:ℝ) ≤ Real.log L - 50000 by linarith [hLL])]
  nlinarith [hlog125, hlog910, h_r25', hquad, hprod, hLL]

/-- `N(N+2) ≤ exp(20.95·L)` when `N < exp(10.3L) + 1` and `L` is large — the per-pair
size bound giving `Ω(n(n+2)) ≤ 20`. -/
lemma expNat_prod_le {L : ℝ} {N : ℕ} (hLbig : (1000 : ℝ) ≤ L)
    (hNce : (N : ℝ) < Real.exp (10.3 * L) + 1) :
    ((N * (N + 2) : ℕ) : ℝ) ≤ Real.exp (20.95 * L) := by
  have hNr2 : (N : ℝ) ≤ Real.exp (10.45 * L) := by
    have h1 : Real.exp (10.3 * L) + 1 ≤ Real.exp (10.45 * L) := by
      have he : Real.exp (10.45 * L) = Real.exp (10.3 * L) * Real.exp (0.15 * L) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : (2:ℝ) ≤ Real.exp (0.15 * L) := by
        have := Real.add_one_le_exp (0.15 * L); nlinarith [this, hLbig]
      have h3 : (1:ℝ) ≤ Real.exp (10.3 * L) := Real.one_le_exp (by positivity)
      nlinarith [he, h2, h3, mul_nonneg (Real.exp_pos (10.3 * L)).le
        (show (0:ℝ) ≤ Real.exp (0.15 * L) - 2 by linarith [h2])]
    linarith
  have hN2r : (↑(N + 2) : ℝ) ≤ Real.exp (10.5 * L) := by
    have h1 : (↑(N + 2) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [h1]
    have he : Real.exp (10.5 * L) = Real.exp (10.45 * L) * Real.exp (0.05 * L) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : (2:ℝ) ≤ Real.exp (0.05 * L) := by
      have := Real.add_one_le_exp (0.05 * L); nlinarith [this, hLbig]
    have h5 : (2:ℝ) ≤ Real.exp (10.45 * L) := by
      have := Real.add_one_le_exp (10.45 * L); nlinarith [this, hLbig]
    nlinarith [hNr2, he, h3, h5, mul_nonneg (Real.exp_pos (10.45 * L)).le
      (show (0:ℝ) ≤ Real.exp (0.05 * L) - 2 by linarith [h3])]
  calc ((N * (N + 2) : ℕ) : ℝ) = (N : ℝ) * (↑(N + 2)) := by push_cast; ring
    _ ≤ Real.exp (10.45 * L) * Real.exp (10.5 * L) :=
        mul_le_mul hNr2 hN2r (by positivity) (by positivity)
    _ = Real.exp (20.95 * L) := by rw [← Real.exp_add]; congr 1; ring

set_option maxHeartbeats 1600000 in
-- Raised limit: this lemma assembles the whole P1 positivity + survivor chain
-- (`brun_lower`, the W/margin bounds, the remainder product, the crux, and the Ω
-- extraction) in a single proof, which exceeds the default heartbeat budget.
/-- For each real `z ≥ zOne` the twin sieve has a survivor: `∃ n` with `z ≤ n + 2` and
`Ω(n(n+2)) ≤ 20`.  This is the full P1 chain — `brun_lower` at `(b, λ, A) = (2, 1/4, 2)`,
the W-lower `W_twin_ge`, the margin `margin_ge`, and the remainder `remainder_upper`, whose
level exponent `3 + 2/(e^Λ-1) ≤ 10.2 < 10.3` forces `siftedSum > 0`; a survivor's `n(n+2)`
is coprime to `P = ∏_{p<z} p`, hence has all prime factors `≥ z`, so
`z^{Ω(n(n+2))} ≤ n(n+2) ≤ z^{20.95} < z^{21}` gives `Ω ≤ 20`. -/
lemma twin_survivor {z : ℝ} (hz : zOne ≤ z) :
    ∃ n : ℕ, (z : ℝ) ≤ (n : ℝ) + 2 ∧ Ω (n * (n + 2)) ≤ 20 := by
  obtain ⟨hz1, hlogz, hLL, hquad, hzth⟩ := zOne_facts hz
  have hzOne2 : (2:ℝ) ≤ zOne := by
    calc (2:ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      _ ≤ Real.exp (Real.exp 50000) := Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num))
      _ = zOne := rfl
  have hz2 : (2:ℝ) ≤ z := le_trans hzOne2 hz
  set L : ℝ := Real.log z with hLdef
  have hLpos : 0 < L := hlogz
  -- `L` is astronomically large.
  have hLbig : (1000:ℝ) ≤ L := by
    have hsq : (50000:ℝ) * 50000 ≤ Real.log L * Real.log L :=
      mul_le_mul hLL hLL (by norm_num) (by linarith [hLL])
    nlinarith [hquad, hsq]
  -- ladder scale and its bounds.
  have hLam0 : 0 < LamTwin (1/4) z := LamTwin_pos (by norm_num) (by norm_num) hzth
  have hLam_lb : (0.2494:ℝ) ≤ LamTwin (1/4) z := by
    have hllpos : (0:ℝ) < Real.log (Real.log z) := by linarith
    have hdiv : 120 / Real.log (Real.log z) ≤ 0.0024 := by
      rw [div_le_iff₀ hllpos]; nlinarith [hLL]
    rw [LamTwin]; nlinarith [hdiv]
  -- the modulus and sieve.
  set P : ℕ := Pz z with hPdef
  have hP : Squarefree P := Pz_squarefree z
  have hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z := by
    intro p hp; rw [hPdef] at hp; exact (mem_Pz_primeFactors.mp hp).2
  set N : ℕ := ⌈Real.exp (10.3 * L)⌉₊ with hNdef
  set s := Salt.TwinSieve.sieve N P hP with hsdef
  -- `brun_lower` at `(b, λ, A) = (2, 1/4, 2)`.
  have h12 : (1/4:ℝ) * Real.exp (1 + 1/4) < 1 := by
    rw [show (1 + 1/4 : ℝ) = 5/4 by norm_num]; nlinarith [exp_five_quarters_lt]
  have htotalMass : 0 ≤ s.totalMass := by
    rw [hsdef, Salt.TwinSieve.sieve_totalMass]; exact Nat.cast_nonneg N
  have hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z := by
    intro p hp
    rw [hsdef, Salt.TwinSieve.sieve_prodPrimes] at hp
    exact hpz p hp
  have hMert := hMert_twinSieve (N := N) hP (show (0:ℝ) < 1/4 by norm_num)
    (show (1/4:ℝ) ≤ 1/4 by norm_num) hzth hpz
  have hωnn : ∀ p, p.Prime → 0 ≤ ((rho p : ℝ)) := fun p _ => by positivity
  have hωA : ∀ p, p.Prime → ((rho p : ℝ)) ≤ 2 := by
    intro p hp
    rcases eq_or_ne p 2 with rfl | h2
    · rw [rho_two]; norm_num
    · rw [rho_odd_prime hp h2]; norm_num
  have hωprod : ∀ d, Squarefree d → ((rho d : ℝ)) = ∏ p ∈ d.primeFactors, ((rho p : ℝ)) :=
    rho_prod_primeFactors
  have hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ ((rho d : ℝ)) := by
    intro d hd
    have hdne : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [hsdef, Salt.TwinSieve.sieve_rem]
    exact rem_abs_le d N hdne
  have hbl := brun_lower s (b := 2) (lam := 1/4) (Lam := LamTwin (1/4) z) (z := z)
    (kappa := 2 * (1/4)) (A := 2) (fun d => (rho d : ℝ))
    (by norm_num) (by norm_num) h12 hLam0 hz1 htotalMass hzprimes (le_refl _) hMert
    (by norm_num) hωnn hωA hωprod hR
  -- Normalise the exponent `2*2-1 = 3` and abbreviate the margin/remainder.
  rw [show (2 * 2 - 1 : ℕ) = 3 from rfl] at hbl
  set r := minLevel (LamTwin (1/4) z) z with hrdef
  have hr1 : 1 ≤ r := (minLevel_mem hLam0 hz1).1
  set M : ℝ := 1 - 2 * (1/4 : ℝ) ^ (2 * 2) * Real.exp (2 * (1/4))
      / (1 - (1/4) ^ 2 * Real.exp (2 + 2 * (1/4))) with hMdef
  set Rem : ℝ := (1 + 2 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ 3
      * ∏ n ∈ Finset.Ico 1 r,
          (1 + 2 * (Nat.primeCounting ⌊zLev (LamTwin (1/4) z) z n⌋₊ : ℝ)) ^ 2 with hRemdef
  -- The level exponent `3 + 2/(e^Λ-1) ≤ 10.2`.
  have hquadE := exp_quad_lower hLam0.le
  have hEm1 : (0.2805:ℝ) ≤ Real.exp (LamTwin (1/4) z) - 1 := by nlinarith [hquadE, hLam_lb]
  have hInvBd : (Real.exp (LamTwin (1/4) z) - 1)⁻¹ ≤ 1/0.2805 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hEm1
  have hExpBd : 3 + 2 * (Real.exp (LamTwin (1/4) z) - 1)⁻¹ ≤ 10.2 := by
    have h : (1:ℝ)/0.2805 ≤ 3.566 := by norm_num
    linarith [hInvBd, h]
  -- Remainder ≤ 125·25^{r-1}·exp(10.2·L).
  have hRemub := remainder_upper (Lam := LamTwin (1/4) z) (z := z) hz1 hLam0
  rw [← hrdef] at hRemub
  have hRem102 : Rem ≤ 125 * 25 ^ (r - 1) * Real.exp (10.2 * L) := by
    rw [hRemdef]
    refine le_trans hRemub ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hExpBd hLpos.le)
  -- The numeric crux `125·25^{r-1}·exp(10.2L) < (9/10)·exp(-70)·exp(10.3L)/L²`.
  have hr_ub : (↑(r - 1) : ℝ) * LamTwin (1/4) z ≤ Real.log L + 1 := by
    rcases Nat.lt_or_ge 1 r with hr2 | hr2
    · have hrm1 : 1 ≤ r - 1 := by omega
      have hgt : ¬ zLev (LamTwin (1/4) z) z (r - 1) ≤ 2 := by
        intro h
        have hle := minLevel_le hrm1 h
        rw [← hrdef] at hle; omega
      have hexp : Real.exp ((↑(r - 1) : ℝ) * LamTwin (1/4) z) < L / Real.log 2 := by
        by_contra h; rw [not_lt] at h
        exact hgt ((zLev_le_two_iff (LamTwin (1/4) z) z (r - 1) hz1).2 h)
      have hlog := Real.log_le_log (Real.exp_pos _) hexp.le
      rw [Real.log_exp, Real.log_div hlogz.ne' (Real.log_pos (by norm_num)).ne'] at hlog
      have hnll2 : -Real.log (Real.log 2) ≤ 1 := by
        have hexp1 : Real.exp (-1 : ℝ) ≤ Real.log 2 := by
          have he1 : (2.7:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          rw [show Real.exp (-1:ℝ) = 1 / Real.exp 1 by rw [Real.exp_neg]; ring,
            div_le_iff₀ (Real.exp_pos 1)]
          nlinarith [he1, (show (0.6931:ℝ) < Real.log 2 by have := Real.log_two_gt_d9; linarith)]
        have := Real.log_le_log (Real.exp_pos _) hexp1
        rw [Real.log_exp] at this; linarith
      linarith [hlog, hnll2]
    · have hre : r - 1 = 0 := by omega
      rw [hre]; simp only [Nat.cast_zero, zero_mul]; linarith [hLL]
  have hcrux := crux_numeric (L := L) (Lam := LamTwin (1/4) z) (r := r)
    hLpos hLL hquad hLam_lb hr_ub
  -- Positivity of the main term.
  have htm : s.totalMass = (N : ℝ) := by rw [hsdef, Salt.TwinSieve.sieve_totalMass]
  have hWpos : 0 < W s := W_pos s
  have hN : Real.exp (10.3 * L) ≤ s.totalMass := by rw [htm, hNdef]; exact Nat.le_ceil _
  have hW : Real.exp (-70) / L ^ 2 ≤ W s := by
    have h := W_twin_ge (N := N) hP hz2 hpz
    rw [← hLdef, ← hsdef] at h; exact h
  have hmargin : (9/10 : ℝ) ≤ M := by rw [hMdef]; exact margin_ge
  have hmainlb : (9/10 : ℝ) * Real.exp (-70) * Real.exp (10.3 * L) / L ^ 2
      ≤ s.totalMass * W s * M := by
    rw [show (9/10:ℝ) * Real.exp (-70) * Real.exp (10.3 * L) / L ^ 2
        = Real.exp (10.3 * L) * (Real.exp (-70) / L ^ 2) * (9/10) by ring]
    apply mul_le_mul (mul_le_mul hN hW (by positivity) htotalMass) hmargin (by norm_num)
      (mul_nonneg htotalMass hWpos.le)
  -- Hence `siftedSum > 0`.
  have hsift : 0 < s.siftedSum := by
    have hRemlt : Rem < s.totalMass * W s * M :=
      lt_of_le_of_lt hRem102 (lt_of_lt_of_le hcrux hmainlb)
    linarith [hbl, hRemlt]
  -- Extract a survivor.
  rw [hsdef, Salt.TwinSieve.sieve_siftedSum] at hsift
  have hcardpos : 0 < ((Finset.Icc 1 N).filter (fun n => Nat.Coprime P (n * (n + 2)))).card := by
    exact_mod_cast hsift
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcardpos
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnN⟩, hcop⟩ := hn
  have hm0 : n * (n + 2) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- Every prime factor of `n(n+2)` is `≥ z`.
  have hprimes : ∀ q ∈ (n * (n + 2)).primeFactors, (z : ℝ) ≤ (q : ℝ) := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ n * (n + 2) := Nat.dvd_of_mem_primeFactors hq
    by_contra hlt; rw [not_le] at hlt
    have hqP : q ∣ P := by rw [hPdef]; exact prime_lt_dvd_Pz hqp hlt
    have hqc : Nat.Coprime q (n * (n + 2)) := Nat.Coprime.coprime_dvd_left hqP hcop
    exact hqp.ne_one (Nat.dvd_one.mp (hqc ▸ Nat.dvd_gcd dvd_rfl hqd))
  refine ⟨n, ?_, ?_⟩
  · -- `z ≤ n + 2`.
    have hge3 : 3 ≤ n * (n + 2) := by
      calc 3 = 1 * (1 + 2) := by norm_num
        _ ≤ n * (n + 2) := Nat.mul_le_mul hn1 (by omega)
    have hm1 : n * (n + 2) ≠ 1 := by omega
    obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hm1
    have hqmem : q ∈ (n * (n + 2)).primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, hm0⟩
    have hqle : q ≤ n + 2 := by
      rcases (hqp.dvd_mul.mp hqd) with h | h
      · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
      · exact Nat.le_of_dvd (by omega) h
    have h1 := hprimes q hqmem
    have h2 : (q : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast hqle
    linarith
  · -- `Ω(n(n+2)) ≤ 20`.
    have hzL : (z : ℝ) = Real.exp L := by rw [hLdef, Real.exp_log (by linarith [hz2])]
    have hpow' : Real.exp (↑(Ω (n * (n + 2))) * L) ≤ (↑(n * (n + 2)) : ℝ) := by
      have hpc := pow_cardFactors_le z (by linarith [hz2]) (n * (n + 2)) hm0 hprimes
      rwa [hzL, ← Real.exp_nat_mul] at hpc
    have hNub : (↑(n * (n + 2)) : ℝ) ≤ Real.exp (20.95 * L) := by
      have hnN2 : n * (n + 2) ≤ N * (N + 2) := Nat.mul_le_mul hnN (by omega)
      have hNce : (N : ℝ) < Real.exp (10.3 * L) + 1 := by
        rw [hNdef]; exact Nat.ceil_lt_add_one (by positivity)
      calc (↑(n * (n + 2)) : ℝ) ≤ (↑(N * (N + 2)) : ℝ) := by exact_mod_cast hnN2
        _ ≤ Real.exp (20.95 * L) := expNat_prod_le hLbig hNce
    by_contra hΩgt; rw [not_le] at hΩgt
    have h21 : Real.exp (21 * L) ≤ Real.exp (↑(Ω (n * (n + 2))) * L) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hLpos.le
      have h21n : 21 ≤ Ω (n * (n + 2)) := hΩgt
      exact_mod_cast h21n
    have h2095 : Real.exp (20.95 * L) < Real.exp (21 * L) :=
      Real.exp_lt_exp.mpr (by nlinarith [hLpos])
    linarith [hpow', hNub, h21, h2095]

/-- **The headline** (blueprint `p0`, node P1): infinitely many `n` with
`Ω(n(n+2)) ≤ 20`. -/
theorem twin_almost_prime :
    {n : ℕ | ArithmeticFunction.cardFactors (n * (n + 2)) ≤ 20}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn2, hΩ⟩ := twin_survivor (z := max zOne ((a : ℝ) + 3)) (le_max_left _ _)
  refine ⟨n, hΩ, ?_⟩
  have : (a : ℝ) + 3 ≤ max zOne ((a : ℝ) + 3) := le_max_right _ _
  have hlt : (a : ℝ) < (n : ℝ) := by linarith [hn2, this]
  exact_mod_cast hlt

end Salt.BrunLower
