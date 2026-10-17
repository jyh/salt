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
ineffective constant `N₀`: it rests on Siegel–Walfisz (`Salt.SW.siegelWalfisz_holds`).

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
asking Siegel–Walfisz for a saving `A + 2B + 1` pays for both.
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
  sorry

/-- **Move 2, the residues sharing a factor with `q` are negligible:** there only prime powers of
primes dividing `q` contribute, with total weight at most `q log N`. -/
theorem norm_nonCoprime_part_le (N q a : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (β : ℝ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
        eR ((a : ℝ) * r / q) * residueSum N q r β‖ ≤ q * Real.log N := by
  sorry

/-- **Move 3, one coprime residue carries `v(β)/φ(q)`:** if the progression discrepancy
`|ψ(n; q, r) − n/φ(q)|` is at most `E` for every `n ≤ N`, then `T_r(β)` differs from `v(β)/φ(q)` by
at most `E (1 + 2π|β|N)`. Discrete Abel summation, against the constant weight `1/φ(q)`. -/
theorem norm_residueSum_sub_le (N q r : ℕ) (hq : 1 ≤ q) (hr : r < q) (β E : ℝ)
    (hE : ∀ n ≤ N, |psiAP n q r - (n : ℝ) / q.totient| ≤ E) :
    ‖residueSum N q r β - expSumOne N β / (q.totient : ℂ)‖
      ≤ E * (1 + 2 * Real.pi * |β| * N) := by
  sorry

/-- **Siegel–Walfisz, uniform up to height `N`:** for any `A, B > 0` there is a `K` with
`|ψ(n; q, r) − n/φ(q)| ≤ K N/(log N)^A` for every `n ≤ N`, every `q ≤ (log N)^B` and every `r`
coprime to `q`. Small `n` use the trivial bound; large `n` use Siegel–Walfisz with `C = 2B`. -/
theorem psiAP_error_uniform {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q r : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime r q → ∀ n ≤ N,
        |psiAP n q r - (n : ℝ) / q.totient| ≤ K * N / Real.log N ^ A := by
  sorry

/-- **The major-arc approximation:** for any `A, B > 0` there is a `K` such that, for every `N ≥ 2`,
every `q ≤ (log N)^B`, every `a` coprime to `q` and every `|β| ≤ (log N)^B/N`,
`|S(a/q + β) − (μ(q)/φ(q)) v(β)| ≤ K N/(log N)^A`. -/
theorem majorArc_approx {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N q a : ℕ, 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      Nat.Coprime q a → ∀ β : ℝ, |β| ≤ Real.log N ^ B / N →
        ‖primeExpSum N ((a : ℝ) / q + β)
            - ((moebius q : ℂ) / (q.totient : ℂ)) * expSumOne N β‖
          ≤ K * N / Real.log N ^ A := by
  sorry

end Salt.ThreePrimes
