/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinA1
import Salt.Chen.WRatioSharp

/-!
# WLOW — the crude `W`-lower for the Chen `twinA1Sieve`

Design: `docs/blueprints/flags.md`, the `2026-07-14 GLU-1` entry (the FLAGGED PREREQ paragraph)
— the crude positive lower bound on `Salt.BrunLower.W (twinA1Sieve …)` that GLU-2's `R/X_W`
and strip error-shares consume, so that `X_W = totalMass · W ≥ x · (crude positive)/(polylog)`
and the `x/(log x)^{10}`-type remainders vanish relatively.

## The bound

Mirror of the Brun-track `Salt.BrunLower.W_twin_ge` (`Salt/BrunLower/TwinInstance.lean`), but at
the Chen instance (`twinA1Sieve`, density `ν = nuChen`, `ν(p) = 1/(p−1)`) and using the **sharp**
pointwise bracket `neg_log_one_sub_nuChen_le` (`−log(1 − ν(p)) ≤ 1/p + 6/p²`, `Salt/Chen/
WRatioSharp.lean`) rather than the crude Brun `2/p + 12/p²`.  Since every sifting prime is
`p ≥ w₀ ≥ 3` and `p < z`,

```
−log W(z) = −Σ_{p ∣ P} log(1 − ν(p)) ≤ Σ_{p ∣ P} (1/p + 6/p²)
          ≤ [log(log z/log 2) + 19/log 2]      -- Salt.BrunLower.sum_inv_le_of_prime_window, w = 2
            + 6 · 1                              -- Salt.BrunLower.sum_one_div_sq_le, M = 2
          ≤ log(log z) + 35,                     -- −log(log 2) ≤ 1, 19/log 2 ≤ 28, 6·Σ1/p² ≤ 6
```

so `W(z) ≥ exp(−(log(log z) + 35)) = exp(−35)/log z`.  The sharp bracket keeps the coefficient of
`log(log z)` at **1** (the crude Brun route would double it to `2`, giving only
`exp(−C)/(log z)²`), so the Chen window buys the stronger single-power form
`W(z) ≥ exp(−35)/log z` — comfortably beating any polylog, which is all GLU-2 needs.

No `sorry`, no `native_decide`, no new axioms; `maxHeartbeats` default.
-/

open Finset

namespace Salt.Chen

/-- **The crude Chen `W`-lower** (`W_twinA1_ge`).  For the Chen `twinA1Sieve` with all sifting
primes `< z` (and `≥ w₀ ≥ 3`, supplied by `hPodd`), `W(z) ≥ exp(−35)/log z`.

Route: the sharp pointwise bracket `neg_log_one_sub_nuChen_le` (`−log(1 − ν(p)) ≤ 1/p + 6/p²`)
summed over `p ∣ P` via the window Mertens `Salt.BrunLower.sum_inv_le_of_prime_window` (at `w = 2`)
and the square tail `Salt.BrunLower.sum_one_div_sq_le`, then exponentiated.  The single power of
`log z` (vs. the Brun-track `W_twin_ge`'s `(log z)²`) is the payoff of the sharp bracket. -/
theorem W_twinA1_ge {x P : ℕ} (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    {z : ℝ} (hz2 : 2 ≤ z) (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    Real.exp (-35) / Real.log z ≤ Salt.BrunLower.W (twinA1Sieve x P hP hPodd) := by
  set s := twinA1Sieve x P hP hPodd with hs
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpf : s.prodPrimes.primeFactors = P.primeFactors := by rw [hs, twinA1Sieve_prodPrimes]
  have hnu_eq : ∀ p, s.nu p = nuChen p := fun p => by rw [hs, twinA1Sieve_nu]
  -- `log W = Σ log(1 − ν(p))`.
  have hlogW : Real.log (Salt.BrunLower.W s)
      = ∑ p ∈ s.prodPrimes.primeFactors, Real.log (1 - s.nu p) := by
    unfold Salt.BrunLower.W
    rw [Real.log_prod]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
    have := s.nu_lt_one_of_prime p hpp hpd
    exact ne_of_gt (by linarith)
  -- `−log W ≤ Σ (1/p + 6/p²)` via the sharp pointwise bracket.
  have hbound : -Real.log (Salt.BrunLower.W s)
      ≤ ∑ p ∈ s.prodPrimes.primeFactors, (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2)) := by
    rw [hlogW, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [hnu_eq]
    rw [hpf] at hp
    exact neg_log_one_sub_nuChen_le (Nat.prime_of_mem_primeFactors hp) (hPodd p hp)
  -- `Σ (1/p + 6/p²) ≤ log(log z) + 35`.
  have hsumle : ∑ p ∈ s.prodPrimes.primeFactors, (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2))
      ≤ Real.log (Real.log z) + 35 := by
    rw [hpf]
    have hsplit : ∑ p ∈ P.primeFactors, (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2))
        = (∑ p ∈ P.primeFactors, (1 : ℝ) / p)
          + 6 * (∑ p ∈ P.primeFactors, (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsplit]
    have hinv : ∑ p ∈ P.primeFactors, (1 : ℝ) / p
        ≤ Real.log (Real.log z / Real.log 2) + 19 / Real.log 2 := by
      apply Salt.BrunLower.sum_inv_le_of_prime_window (by norm_num) hz2
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact ⟨hpp, by exact_mod_cast hpp.two_le, hpz p hp⟩
    have hsq : ∑ p ∈ P.primeFactors, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
      have hsub : P.primeFactors ⊆ Finset.Icc 2 ⌊z⌋₊ := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        rw [Finset.mem_Icc]
        exact ⟨hpp.two_le, Nat.le_floor (le_of_lt (hpz p hp))⟩
      have hstep : ∑ p ∈ P.primeFactors, (1 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ p ∈ Finset.Icc 2 ⌊z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have hkey := Salt.BrunLower.sum_one_div_sq_le (M := 2) (K := ⌊z⌋₊) (by norm_num)
      have hval : (1 : ℝ) / (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
      linarith [hstep, hkey, hval]
    have hlogdiv : Real.log (Real.log z / Real.log 2)
        = Real.log (Real.log z) - Real.log (Real.log 2) := Real.log_div hlogz.ne' hlog2.ne'
    have hlog2gt : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hnll2 : -Real.log (Real.log 2) ≤ 1 := by
      have hexp1 : Real.exp (-1 : ℝ) ≤ Real.log 2 := by
        have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        rw [show Real.exp (-1 : ℝ) = 1 / Real.exp 1 by rw [Real.exp_neg]; ring,
          div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [he1, hlog2gt]
      have := Real.log_le_log (Real.exp_pos _) hexp1
      rw [Real.log_exp] at this
      linarith
    have h19 : 19 / Real.log 2 ≤ 28 := by
      rw [div_le_iff₀ hlog2]; nlinarith [hlog2gt]
    linarith [hinv, hsq, hnll2, h19, hlogdiv]
  -- `log W ≥ −(log(log z) + 35)`, so `W ≥ exp(−(log(log z) + 35)) = exp(−35)/log z`.
  have hlogW_ge : -(Real.log (Real.log z) + 35) ≤ Real.log (Salt.BrunLower.W s) := by
    linarith [hbound, hsumle]
  have hWpos : 0 < Salt.BrunLower.W s := Salt.BrunLower.W_pos s
  have hexpid : Real.exp (Real.log (Real.log z)) = Real.log z := Real.exp_log hlogz
  have hWge : Real.exp (-(Real.log (Real.log z) + 35)) ≤ Salt.BrunLower.W s := by
    calc Real.exp (-(Real.log (Real.log z) + 35))
        ≤ Real.exp (Real.log (Salt.BrunLower.W s)) := Real.exp_le_exp.mpr hlogW_ge
      _ = Salt.BrunLower.W s := Real.exp_log hWpos
  have hid : Real.exp (-(Real.log (Real.log z) + 35)) = Real.exp (-35) / Real.log z := by
    rw [show -(Real.log (Real.log z) + 35) = (-35) + (-(Real.log (Real.log z))) by ring,
      Real.exp_add, Real.exp_neg (Real.log (Real.log z)), hexpid, div_eq_mul_inv]
  rw [hid] at hWge
  exact hWge

end Salt.Chen
