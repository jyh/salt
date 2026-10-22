/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Gate
import Salt.ThreePrimes.Ramanujan
import Salt.ThreePrimes.SingularIntegral

/-!
# Three primes: the major-arc approximation

This is lemma L8 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Step 3), together with
the pieces of L7 it uses.

Near a fraction `a/q` with small `q`, the prime exponential sum
`S(α) = Σ_{1 ≤ n ≤ N} Λ(n) e(nα)` looks like a simple explicit function:

  `S(a/q + β) = (μ(q)/φ(q)) · v(β) + O(N/(log N)^A)`,  where `v(β) = Σ_{1 ≤ n ≤ N} e(nβ)`,

uniformly for `q ≤ (log N)^B`, `gcd(a, q) = 1` and `|β| ≤ (log N)^B/N`, for any fixed `A` and `B`.
This is the only place the proof uses primes in arithmetic progressions, and the only source of the
ineffective constant `N₀`: it rests on Siegel–Walfisz (`Salt.SW.siegelWalfisz_holds`). Its constant
comes from Siegel's theorem, which bounds how close a real zero of a Dirichlet `L`-function can be
to `1`. Its proof splits on whether some other `L`-function has such a zero, so it yields no
constant that can be computed.

**The argument, in four moves.**

1. *Split by residue.* `e(n(a/q + β)) = e(an/q) e(nβ)`, and `e(an/q)` depends only on `n mod q`. So
   `S(a/q + β) = Σ_{r < q} e(ar/q) T_r(β)`, where `T_r(β)` sums `Λ(n) e(nβ)` over `n ≡ r (mod q)`
   (`primeExpSum_split`).
2. *Discard the residues that share a factor with `q`.* If `gcd(r, q) > 1`, every `n ≡ r`
   shares that factor, so `Λ(n) ≠ 0` only for prime powers `p^k` with `p ∣ q`. There are few of
   those: their total weight is at most `q log N` (`norm_nonCoprime_part_le`).
3. *Each coprime residue carries `v(β)/φ(q)`.* Siegel–Walfisz says `ψ(n; q, r) = n/φ(q) + E(n)` with
   `E` small. The weights `Λ(n)·[n ≡ r]` and the constant weight `1/φ(q)` then have partial sums
   that differ by `E(n)`. Discrete Abel summation turns the twist `e(nβ)` into differences
   `e((n+1)β) − e(nβ)`, each of size at most `2π|β|`. So `T_r(β)` differs from `v(β)/φ(q)` by at
   most `max |E| · (1 + 2π|β|N)` (`norm_residueSum_sub_le`). The main term is exact: summing the
   constant weight gives `v(β)/φ(q)` on the nose.
4. *Collect the phases.* Summing `e(ar/q)` over the `φ(q)` residues coprime to `q` gives the
   Ramanujan sum `c_q(a) = μ(q)` (`ramanujanSum_of_coprime`). That is where `μ(q)/φ(q)` comes from.

**Why the error may grow with `|β|N` and with `q`.** Siegel–Walfisz saves every power of `log N`
(`psiAP_error_uniform`), while `|β|N ≤ (log N)^B` and `q ≤ (log N)^B` cost only fixed powers. So
asking Siegel–Walfisz for a saving `A + 2B` pays for both.
**Why the uniformity needs care.** Siegel–Walfisz at height `n` covers moduli up to `(log n)^C`, not
`(log N)^C`. For `n ≤ √N` the trivial bound is already small enough. For `n > √N`,
`log n ≥ ½ log N`, so `q ≤ (log N)^B ≤ (log n)^{2B}` once `n` is large, and Siegel–Walfisz with
`C = 2B` applies.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction
open Salt.ExpSum (eR norm_eR)
open Salt.LS (psiAP)

/-- **The prime exponential sum** `S(α) = Σ_{1 ≤ n ≤ N} Λ(n) e(nα)`. -/
noncomputable def primeExpSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℂ) * eR ((n : ℝ) * α)

/-- **The part of `S` in one residue class:** `T_r(β) = Σ_{n ≤ N, n ≡ r (mod q)} Λ(n) e(nβ)`. -/
noncomputable def residueSum (N q r : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = r), (vonMangoldt n : ℂ) * eR ((n : ℝ) * β)

/-- **Move 1, split by residue:** `S(a/q + β) = Σ_{r < q} e(ar/q) T_r(β)`, because `e(an/q)` depends
only on `n mod q`. -/
theorem primeExpSum_split (N q a : ℕ) (hq : 1 ≤ q) (β : ℝ) :
    primeExpSum N ((a : ℝ) / q + β)
      = ∑ r ∈ Finset.range q, eR ((a : ℝ) * r / q) * residueSum N q r β := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hphase : ∀ n : ℕ, eR ((n : ℝ) * ((a : ℝ) / q + β))
      = eR ((a : ℝ) * ((n % q : ℕ) : ℝ) / q) * eR ((n : ℝ) * β) := by
    intro n
    obtain ⟨m, hn⟩ : ∃ m : ℕ, (n : ℝ) = (q : ℝ) * m + ((n % q : ℕ) : ℝ) :=
      ⟨n / q, by exact_mod_cast (Nat.div_add_mod n q).symm⟩
    have hcancel : (a : ℝ) / q * q = a := div_mul_cancel₀ _ hq0
    have key : (n : ℝ) * ((a : ℝ) / q + β)
        = ((a : ℝ) * ((n % q : ℕ) : ℝ) / q + (n : ℝ) * β) + (((a : ℤ) * (m : ℤ) : ℤ) : ℝ) := by
      push_cast
      linear_combination ((a : ℝ) / q) * hn + (m : ℝ) * hcancel
    rw [key, Salt.MR.eR_add_intCast, Salt.ExpSum.eR_add]
  unfold primeExpSum residueSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 N) (t := Finset.range q)
    (g := fun n => n % q) (fun n _ => Finset.mem_range.2 (Nat.mod_lt n (by omega)))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  obtain ⟨-, hnr⟩ := Finset.mem_filter.1 hn
  rw [hphase n, hnr]
  ring

/-- **Move 2, the residues sharing a factor with `q` are negligible:** there only prime powers of
primes dividing `q` contribute, with total weight at most `q log N`. -/
theorem norm_nonCoprime_part_le (N q a : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (β : ℝ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
        eR ((a : ℝ) * r / q) * residueSum N q r β‖ ≤ q * Real.log N := by
  classical
  have hN0 : N ≠ 0 := by omega
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  -- each residue sum is at most its total weight; regroup the weights by `n`
  have h1 : ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
        eR ((a : ℝ) * r / q) * residueSum N q r β‖
      ≤ ∑ n ∈ Finset.Icc 1 N, if ¬ Nat.Coprime q (n % q) then vonMangoldt n else 0 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
          ‖eR ((a : ℝ) * r / q) * residueSum N q r β‖
        ≤ ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            ∑ n ∈ Finset.Icc 1 N, if n % q = r then vonMangoldt n else 0 := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [norm_mul, norm_eR, one_mul, ← Finset.sum_filter]
          unfold residueSum
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
          rw [norm_mul, norm_eR, mul_one, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            if n % q = r then vonMangoldt n else 0 := Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [Finset.sum_ite_eq]
          have hlt : n % q < q := Nat.mod_lt n (by omega)
          split_ifs with h h' h' <;> simp_all
  -- a weight `Λ(n)` with `gcd(n, q) > 1` sits on a power of a prime dividing `q`
  have h2 : ∀ n ∈ Finset.Icc 1 N, (if ¬ Nat.Coprime q (n % q) then vonMangoldt n else 0)
      ≤ ∑ p ∈ q.primeFactors,
          if n ∈ (p ^ Nat.log p N).divisors then vonMangoldt n else 0 := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
    have hnn : ∀ m : ℕ, 0 ≤ ∑ p ∈ q.primeFactors,
        (if m ∈ (p ^ Nat.log p N).divisors then vonMangoldt m else 0) :=
      fun m => Finset.sum_nonneg fun p _ => by split_ifs <;> simp [vonMangoldt_nonneg]
    by_cases hc : Nat.Coprime q (n % q)
    · rw [if_neg (not_not_intro hc)]; exact hnn n
    · rw [if_pos hc]
      by_cases hΛ : vonMangoldt n = 0
      · exact (le_of_eq hΛ).trans (hnn n)
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
      have hpq : p ∣ q := by
        by_contra hpq
        apply hc
        have hcop : Nat.Coprime q (p ^ k) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm.pow_right k
        unfold Nat.Coprime
        rw [Nat.gcd_comm, ← Nat.gcd_rec]
        exact hcop
      have hpF : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, by omega⟩
      have hmem : p ^ k ∈ (p ^ Nat.log p N).divisors :=
        Nat.mem_divisors.2 ⟨pow_dvd_pow p (Nat.le_log_of_pow_le hp.one_lt hnN),
          pow_ne_zero _ hp.ne_zero⟩
      calc vonMangoldt (p ^ k)
          = if p ^ k ∈ (p ^ Nat.log p N).divisors then vonMangoldt (p ^ k) else 0 :=
            (if_pos hmem).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun p' => if p ^ k ∈ (p' ^ Nat.log p' N).divisors then vonMangoldt (p ^ k) else 0)
            (fun p' _ => by split_ifs <;> simp [vonMangoldt_nonneg]) hpF
  refine h1.trans ?_
  calc ∑ n ∈ Finset.Icc 1 N, (if ¬ Nat.Coprime q (n % q) then vonMangoldt n else 0)
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ q.primeFactors,
          if n ∈ (p ^ Nat.log p N).divisors then vonMangoldt n else 0 := Finset.sum_le_sum h2
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ (p ^ Nat.log p N).divisors),
          vonMangoldt n := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ p ∈ q.primeFactors, ∑ d ∈ (p ^ Nat.log p N).divisors, vonMangoldt d :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_filter.1 hx).2) (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log N := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [vonMangoldt_sum]
        have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
        exact Real.log_le_log (by exact_mod_cast pow_pos hp0 _)
          (by exact_mod_cast Nat.pow_log_le_self p hN0)
    _ = (q.primeFactors.card : ℝ) * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q * Real.log N := by
        gcongr
        have hsub : q.primeFactors ⊆ q.divisors := fun p hp =>
          Nat.mem_divisors.2 ⟨Nat.dvd_of_mem_primeFactors hp, by omega⟩
        exact_mod_cast (Finset.card_le_card hsub).trans (Nat.card_divisors_le_self q)

/-- **Discrete Abel summation on `[1, N]`:** with `F(n) = Σ_{1 ≤ m ≤ n} f(m)`,
`Σ_{1 ≤ n ≤ N} f(n) g(n) = F(N) g(N) − Σ_{n < N} F(n) (g(n+1) − g(n))`. -/
theorem sum_Icc_mul_abel (f g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n * g n
      = (∑ m ∈ Finset.Icc 1 N, f m) * g N
        - ∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 n, f m) * (g (n + 1) - g n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]
    ring

/-- One step of the twist costs at most `2π|β|`: `|e((n+1)β) − e(nβ)| = |e(β) − 1| ≤ 2π|β|`. -/
theorem norm_eR_succ_sub_le (n : ℕ) (β : ℝ) :
    ‖eR (((n + 1 : ℕ) : ℝ) * β) - eR ((n : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have hsplit : eR (((n + 1 : ℕ) : ℝ) * β) - eR ((n : ℝ) * β)
      = eR ((n : ℝ) * β) * (eR β - 1) := by
    rw [show ((n + 1 : ℕ) : ℝ) * β = (n : ℝ) * β + β by push_cast; ring, Salt.ExpSum.eR_add]
    ring
  have hexp : eR β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold eR; congr 1; push_cast; ring
  rw [hsplit, norm_mul, norm_eR, one_mul, hexp]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- **Move 3, one coprime residue carries `v(β)/φ(q)`:** if the progression discrepancy
`|ψ(n; q, r) − n/φ(q)|` is at most `E` for every `n ≤ N`, then `T_r(β)` differs from `v(β)/φ(q)` by
at most `E (1 + 2π|β|N)`. Discrete Abel summation, against the constant weight `1/φ(q)`. -/
theorem norm_residueSum_sub_le (N q r : ℕ) (hq : 1 ≤ q) (hr : r < q) (β E : ℝ)
    (hE : ∀ n ≤ N, |psiAP n q r - (n : ℝ) / q.totient| ≤ E) :
    ‖residueSum N q r β - expSumOne N β / (q.totient : ℂ)‖
      ≤ E * (1 + 2 * Real.pi * |β| * N) := by
  -- (`1 ≤ q` is not needed: `r < q` already makes `q` positive)
  have _hq : 0 < q := hq
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 0 (Nat.zero_le _))
  set f : ℕ → ℂ := fun n =>
    ((if n % q = r then vonMangoldt n else 0 : ℝ) : ℂ) - 1 / (q.totient : ℂ) with hf
  set g : ℕ → ℂ := fun n => eR ((n : ℝ) * β) with hg
  have hsplit : residueSum N q r β - expSumOne N β / (q.totient : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, f n * g n := by
    unfold residueSum expSumOne
    rw [Finset.sum_filter, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf, hg]
    split_ifs <;> push_cast <;> ring
  have hpart : ∀ n ≤ N, ‖∑ m ∈ Finset.Icc 1 n, f m‖ ≤ E := by
    intro n hn
    have hsum : ∑ m ∈ Finset.Icc 1 n, f m = ((psiAP n q r - (n : ℝ) / q.totient : ℝ) : ℂ) := by
      unfold psiAP
      rw [Nat.mod_eq_of_lt hr, Finset.sum_filter]
      simp only [hf]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      ring
    rw [hsum, Complex.norm_real, Real.norm_eq_abs]
    exact hE n hn
  rw [hsplit, sum_Icc_mul_abel]
  calc ‖(∑ m ∈ Finset.Icc 1 N, f m) * g N
        - ∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 n, f m) * (g (n + 1) - g n)‖
      ≤ ‖(∑ m ∈ Finset.Icc 1 N, f m) * g N‖
        + ‖∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 n, f m) * (g (n + 1) - g n)‖ :=
        norm_sub_le _ _
    _ ≤ E + ∑ _n ∈ Finset.range N, E * (2 * Real.pi * |β|) := by
        gcongr
        · rw [norm_mul, hg, norm_eR, mul_one]; exact hpart N le_rfl
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
          rw [norm_mul]
          exact mul_le_mul (hpart n (Finset.mem_range.1 hn).le) (norm_eR_succ_sub_le n β)
            (norm_nonneg _) hE0
    _ = E * (1 + 2 * Real.pi * |β| * N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Powers of `log` lose to `√x`:** for `m > 0` there is a `C` with `(log x)^m ≤ C √x` for all
`x ≥ 1`. It turns the trivial bound on small `n`, and the `q log N` term, into `O(N/(log N)^A)`. -/
theorem log_rpow_le_mul_sqrt {m : ℝ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ m ≤ C * Real.sqrt x := by
  set ε := 1 / (2 * m) with hε_def
  have hε : 0 < ε := by positivity
  refine ⟨(1 / ε) ^ m, by positivity, fun x hx => ?_⟩
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have hεm : ε * m = 1 / 2 := by rw [hε_def]; field_simp
  calc Real.log x ^ m ≤ (x ^ ε / ε) ^ m := Real.rpow_le_rpow hl0 h1 hm.le
    _ = (1 / ε) ^ m * Real.sqrt x := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_one_div (x ^ ε),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith), hεm,
        mul_comm]

/-- **The trivial progression bound:** for `n ≤ N`, `|ψ(n; q, r) − n/φ(q)| ≤ n (log N + 1)`, since
`ψ(n; q, r)` has at most `n` terms `Λ(m) ≤ log N` and `0 ≤ n/φ(q) ≤ n`. -/
theorem abs_psiAP_sub_le_trivial {N q r n : ℕ} (hq : 1 ≤ q) (hn : n ≤ N) :
    |psiAP n q r - (n : ℝ) / q.totient| ≤ n * (Real.log N + 1) := by
  have hψ0 : 0 ≤ psiAP n q r := Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hψ : psiAP n q r ≤ n * Real.log N := by
    unfold psiAP
    calc _ ≤ ∑ m ∈ Finset.Icc 1 n, vonMangoldt m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => vonMangoldt_nonneg)
      _ ≤ ∑ _m ∈ Finset.Icc 1 n, Real.log N := Finset.sum_le_sum fun m hm => by
          have hm1 := (Finset.mem_Icc.1 hm).1
          refine vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
          · exact_mod_cast (by omega : 0 < m)
          · exact_mod_cast (Finset.mem_Icc.1 hm).2.trans hn
      _ = n * Real.log N := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hd0 : 0 ≤ (n : ℝ) / q.totient := by positivity
  have hd : (n : ℝ) / q.totient ≤ n := div_le_self (by positivity) hφ
  have hnL : 0 ≤ (n : ℝ) * Real.log N := mul_nonneg (by positivity) (Real.log_natCast_nonneg N)
  rw [abs_le]
  constructor <;> nlinarith

/-- `log 8 ≥ 2`, because `e² < 8`: the height from which Siegel–Walfisz at `C = 2B` covers every
`q ≤ (log N)^B` once `n ≥ √N`. -/
theorem two_le_log_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

/-- `psiAP_error_uniform` with the Siegel–Walfisz statement as the hypothesis `hSWall`, in place of
the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem psiAP_error_uniform_of_SW (hSWall : Salt.BV.SiegelWalfisz) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q r : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime r q → ∀ n ≤ N,
        |psiAP n q r - (n : ℝ) / q.totient| ≤ K * N / Real.log N ^ A := by
  obtain ⟨K₀, hK₀, hSW⟩ := hSWall A (2 * B) hA (by linarith)
  obtain ⟨C₁, hC₁, hC₁b⟩ := log_rpow_le_mul_sqrt (m := A + 1) (by linarith)
  obtain ⟨C₂, hC₂, hC₂b⟩ := log_rpow_le_mul_sqrt (m := A) hA
  refine ⟨K₀ * 2 ^ A + 8 * (C₁ + C₂), by positivity, fun N q r hN hq hqB hcop n hn => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLA : 0 < Real.log N ^ A := Real.rpow_pos_of_pos hL A
  have hK₀2 : 0 ≤ K₀ * 2 ^ A := by positivity
  by_cases hlarge : 8 ≤ n ∧ N ≤ n * n
  · -- large `n`: Siegel–Walfisz at height `n`, modulus range `(log n)^{2B}`
    obtain ⟨h8, hsq⟩ := hlarge
    have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
    have hn2 : 2 ≤ Real.log n := two_le_log_of_eight_le hn8
    have hLn : Real.log N ≤ 2 * Real.log n := by
      have := Real.log_le_log (by positivity) (show (N : ℝ) ≤ n * n by exact_mod_cast hsq)
      rw [Real.log_mul (by positivity) (by positivity)] at this
      linarith
    have hqn : (q : ℝ) ≤ Real.log n ^ (2 * B) := by
      calc (q : ℝ) ≤ Real.log N ^ B := hqB
        _ ≤ (2 * Real.log n) ^ B := Real.rpow_le_rpow hL.le hLn hB.le
        _ = 2 ^ B * Real.log n ^ B := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ Real.log n ^ B * Real.log n ^ B :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) hn2 hB.le)
              (by positivity)
        _ = Real.log n ^ (2 * B) := by rw [two_mul, Real.rpow_add (by linarith)]
    have hsw := hSW n q r (by omega) (by omega) hqn hcop
    have hLnA : Real.log N ^ A ≤ 2 ^ A * Real.log n ^ A := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow hL.le hLn hA.le
    have hlnA : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (by linarith) A
    calc |psiAP n q r - (n : ℝ) / q.totient| ≤ K₀ * n / Real.log n ^ A := hsw
      _ ≤ K₀ * 2 ^ A * N / Real.log N ^ A := by
          rw [div_le_div_iff₀ hlnA hLA]
          calc K₀ * n * Real.log N ^ A ≤ K₀ * N * (2 ^ A * Real.log n ^ A) := by
                gcongr
              _ = K₀ * 2 ^ A * N * Real.log n ^ A := by ring
      _ ≤ (K₀ * 2 ^ A + 8 * (C₁ + C₂)) * N / Real.log N ^ A := by
          gcongr; linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (add_nonneg hC₁ hC₂)]
  · -- small `n` (`n < 8` or `n < √N`): the trivial bound
    have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
    have hsmall : (n : ℝ) ≤ 8 * Real.sqrt N := by
      rcases not_and_or.1 hlarge with h | h
      · have : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
        linarith
      · have hlt : (n : ℝ) < Real.sqrt N := by
          rw [Real.lt_sqrt (by positivity), sq]
          exact_mod_cast (by omega : n * n < N)
        linarith
    have b1 := hC₁b N hN1
    have b2 := hC₂b N hN1
    rw [Real.rpow_add_one hL.ne' A] at b1
    have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by positivity)
    calc |psiAP n q r - (n : ℝ) / q.totient| ≤ n * (Real.log N + 1) :=
          abs_psiAP_sub_le_trivial hq hn
      _ ≤ 8 * (C₁ + C₂) * N / Real.log N ^ A := by
          rw [le_div_iff₀ hLA]
          calc (n : ℝ) * (Real.log N + 1) * Real.log N ^ A
              = n * (Real.log N ^ A * Real.log N + Real.log N ^ A) := by ring
            _ ≤ (8 * Real.sqrt N) * (C₁ * Real.sqrt N + C₂ * Real.sqrt N) :=
                mul_le_mul hsmall (add_le_add b1 b2) (by positivity) (by positivity)
            _ = 8 * (C₁ + C₂) * N := by linear_combination 8 * (C₁ + C₂) * hs
      _ ≤ (K₀ * 2 ^ A + 8 * (C₁ + C₂)) * N / Real.log N ^ A := by
          gcongr; linarith

/-- **Siegel–Walfisz, uniform up to height `N`:** for any `A, B > 0` there is a `K` with
`|ψ(n; q, r) − n/φ(q)| ≤ K N/(log N)^A` for every `n ≤ N`, every `q ≤ (log N)^B` and every `r`
coprime to `q`. Small `n` use the trivial bound; large `n` use Siegel–Walfisz with `C = 2B`. -/
theorem psiAP_error_uniform {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q r : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime r q → ∀ n ≤ N,
        |psiAP n q r - (n : ℝ) / q.totient| ≤ K * N / Real.log N ^ A :=
  psiAP_error_uniform_of_SW Salt.SW.siegelWalfisz_holds hA hB

/-- `majorArc_approx` with the Siegel–Walfisz statement as the hypothesis `hSWall`, in place of
the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem majorArc_approx_of_SW (hSWall : Salt.BV.SiegelWalfisz) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q a : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime q a → ∀ β : ℝ, |β| ≤ Real.log N ^ B / N →
        ‖primeExpSum N ((a : ℝ) / q + β)
            - ((moebius q : ℂ) / (q.totient : ℂ)) * expSumOne N β‖
          ≤ K * N / Real.log N ^ A := by
  obtain ⟨K₁, hK₁, hU⟩ :=
    psiAP_error_uniform_of_SW hSWall (A := A + 2 * B) (B := B) (by positivity) hB
  obtain ⟨C₃, hC₃, hC₃b⟩ := log_rpow_le_mul_sqrt (m := A + B + 1) (by positivity)
  refine ⟨K₁ * (1 / Real.log 2 ^ B + 2 * Real.pi) + C₃, by positivity,
    fun N q a hN hq hqB hcop β hβ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  set L := Real.log N with hL_def
  set P := L ^ B with hP_def
  set Q := L ^ A with hQ_def
  have hP : 0 < P := Real.rpow_pos_of_pos hL B
  have hQ : 0 < Q := Real.rpow_pos_of_pos hL A
  have hPl : Real.log 2 ^ B ≤ P := Real.rpow_le_rpow hl.le hlL hB.le
  have hpow : L ^ (A + 2 * B) = Q * P * P := by
    rw [two_mul, ← add_assoc, Real.rpow_add hL, Real.rpow_add hL]
  set E := K₁ * N / (Q * P * P) with hE_def
  have hE0 : 0 ≤ E := by positivity
  have hE : ∀ r, Nat.Coprime r q → ∀ n ≤ N, |psiAP n q r - (n : ℝ) / q.totient| ≤ E := by
    intro r hr n hn
    have := hU N q r hN hq hqB hr n hn
    rwa [hpow] at this
  -- split into the coprime residues (main term + Abel errors) and the rest
  rw [primeExpSum_split N q a hq, ← Finset.sum_filter_add_sum_filter_not (Finset.range q)
    (fun r => Nat.Coprime q r)]
  set cop := (Finset.range q).filter (fun r => Nat.Coprime q r) with hcop_def
  set v := expSumOne N β
  set φq : ℂ := (q.totient : ℂ)
  have hmain : ∑ r ∈ cop, eR ((a : ℝ) * r / q) * (v / φq) = ((moebius q : ℂ) / φq) * v := by
    rw [← Finset.sum_mul,
      show (∑ r ∈ cop, eR ((a : ℝ) * r / q)) = ramanujanSum q a from rfl,
      ramanujanSum_of_coprime hq hcop]
    ring
  have hrw : ∑ r ∈ cop, eR ((a : ℝ) * r / q) * residueSum N q r β
      = ((moebius q : ℂ) / φq) * v
        + ∑ r ∈ cop, eR ((a : ℝ) * r / q) * (residueSum N q r β - v / φq) := by
    rw [← hmain, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hrw, show ∀ x y z : ℂ, x + y + z - x = y + z from fun x y z => by ring]
  -- the coprime residues: `φ(q)` Abel errors
  have hT1 : ‖∑ r ∈ cop, eR ((a : ℝ) * r / q) * (residueSum N q r β - v / φq)‖
      ≤ q.totient * (E * (1 + 2 * Real.pi * |β| * N)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r ∈ cop, ‖eR ((a : ℝ) * r / q) * (residueSum N q r β - v / φq)‖
        ≤ ∑ _r ∈ cop, E * (1 + 2 * Real.pi * |β| * N) := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [norm_mul, norm_eR, one_mul]
          obtain ⟨hrq, hcr⟩ := Finset.mem_filter.1 hr
          exact norm_residueSum_sub_le N q r hq (Finset.mem_range.1 hrq) β E (hE r hcr.symm)
      _ = q.totient * (E * (1 + 2 * Real.pi * |β| * N)) := by
          rw [Finset.sum_const, hcop_def, card_coprime_filter, nsmul_eq_mul]
  have hT2 := norm_nonCoprime_part_le N q a (by omega) hq β
  -- the arithmetic
  have hφ : (q.totient : ℝ) ≤ P :=
    (by exact_mod_cast Nat.totient_le q : (q.totient : ℝ) ≤ q).trans hqB
  have hβN : |β| * N ≤ P := by rwa [le_div_iff₀ hN0] at hβ
  have hB1 : (q.totient : ℝ) * (E * (1 + 2 * Real.pi * |β| * N))
      ≤ K₁ * (1 / Real.log 2 ^ B + 2 * Real.pi) * N / Q := by
    have h1 : 1 + 2 * Real.pi * |β| * N ≤ 1 + 2 * Real.pi * P := by
      have := mul_le_mul_of_nonneg_left hβN (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
    calc (q.totient : ℝ) * (E * (1 + 2 * Real.pi * |β| * N))
        ≤ P * (E * (1 + 2 * Real.pi * P)) :=
          mul_le_mul hφ (mul_le_mul_of_nonneg_left h1 hE0) (by positivity) hP.le
      _ = K₁ * N / Q * (1 / P + 2 * Real.pi) := by
          rw [hE_def]; field_simp
      _ ≤ K₁ * N / Q * (1 / Real.log 2 ^ B + 2 * Real.pi) := by
          gcongr
      _ = K₁ * (1 / Real.log 2 ^ B + 2 * Real.pi) * N / Q := by ring
  have hB2 : (q : ℝ) * L ≤ C₃ * N / Q := by
    rw [le_div_iff₀ hQ]
    have hpow' : L ^ (A + B + 1) = Q * P * L := by
      rw [Real.rpow_add_one hL.ne', Real.rpow_add hL]
    have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
    have hsN : Real.sqrt N ≤ N := by
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ N by positivity)]
    calc (q : ℝ) * L * Q ≤ P * L * Q := by gcongr
      _ = L ^ (A + B + 1) := by rw [hpow']; ring
      _ ≤ C₃ * Real.sqrt N := hC₃b N hN1
      _ ≤ C₃ * N := mul_le_mul_of_nonneg_left hsN hC₃
  calc ‖∑ r ∈ cop, eR ((a : ℝ) * r / q) * (residueSum N q r β - v / φq)
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            eR ((a : ℝ) * r / q) * residueSum N q r β‖
      ≤ ‖∑ r ∈ cop, eR ((a : ℝ) * r / q) * (residueSum N q r β - v / φq)‖
        + ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            eR ((a : ℝ) * r / q) * residueSum N q r β‖ := norm_add_le _ _
    _ ≤ K₁ * (1 / Real.log 2 ^ B + 2 * Real.pi) * N / Q + C₃ * N / Q :=
        add_le_add (hT1.trans hB1) (hT2.trans hB2)
    _ = (K₁ * (1 / Real.log 2 ^ B + 2 * Real.pi) + C₃) * N / Q := by ring

/-- **The major-arc approximation:** for any `A, B > 0` there is a `K` such that, for every `N ≥ 2`,
every `q ≤ (log N)^B`, every `a` coprime to `q` and every `|β| ≤ (log N)^B/N`,
`|S(a/q + β) − (μ(q)/φ(q)) v(β)| ≤ K N/(log N)^A`. -/
theorem majorArc_approx {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q a : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime q a → ∀ β : ℝ, |β| ≤ Real.log N ^ B / N →
        ‖primeExpSum N ((a : ℝ) / q + β)
            - ((moebius q : ℂ) / (q.totient : ℂ)) * expSumOne N β‖
          ≤ K * N / Real.log N ^ A :=
  majorArc_approx_of_SW Salt.SW.siegelWalfisz_holds hA hB

end Salt.ThreePrimes
