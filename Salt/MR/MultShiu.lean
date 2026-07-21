/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# MULT-SHIU — the `hfactor` secondary bound (GHS Lemma 2.4 at `κ = 1`)

The `z = x`, `q = 1` case of Shiu's theorem is *not* Shiu: it is the elementary
**Hall–Tenenbaum bound** (Tenenbaum, *Introduction to Analytic and Probabilistic
Number Theory*, Thm III.3.5 shape), proven by the swap-order argument with no
sieve and no bootstrap.  This file lands the stone ladder of the MULT-SHIU freeze
(`docs/exploration/mult-shiu-freeze.md`).

## Route committed (freeze HT-1 ⟦R⟧, single-route declaration)

The `ν ≥ 2` prime-power mass in the Hall–Tenenbaum core is handled by
`S(x/p^ν) ≤ x/p^ν` (which needs `F ≤ 1`), giving the absolutely-convergent
prime-power constant `B`, then reattached to `∑_{m≤x} F(m)/m` via `F 1 = 1 ⟹
∑ F(m)/m ≥ 1`.  We never bound `F(p^ν) ≤ 1` while dropping the `p^{-ν}` weight
(that path hits `ψ(y) − θ(y) ~ √y` and diverges).

## The partial-summation engine

Both the Chebyshev-`Λ` stone (CHEB-Λ) and the rough-prime tail (ROUGH-TAIL) ride
one reusable Abel lemma, `abel_master`: for a nonnegative sequence `a` whose
partial sums obey `∑_{i<m} a i ≤ c·m` and a nonnegative decreasing weight `w`,

  `∑_{i<N} w i · a i ≤ c · ∑_{i<N} w i`.

Instantiated at `a = Λ(·+1)` (so `∑_{i<m} = ψ(m) ≤ (log 4 + 4)·m` by mathlib's
`Chebyshev.psi_le_const_mul_self`) and `w = (·+1)^{-α}`, it turns the `Λ`-weighted
sum into a bare `∑ k^{-α}`, closed by the sum/integral comparison.

## Stones (freeze ladder)

* `abel_master`, `sum_range_vonMangoldt_succ` — the partial-summation engine.
* `lambda_partial_alpha` (CHEB-Λ) — `∑_{k≤K} Λ(k)/k^α ≤ 2(log4+4)·K^{1-α}/(1-α)`.
* `rough_prime_tail` (ROUGH-TAIL) — `∑_{y<p≤x} p^{-1-η} ≤ 2(log 4 + 4)` (absolute).

Constants are HONEST-EXPLICIT (house law #253); nothing absorbed silently.
-/

namespace Salt.MR

open scoped BigOperators
open Finset ArithmeticFunction

/-! ## The Abel partial-summation master lemma -/

/-- **Abel partial-summation master bound.**  Let `a : ℕ → ℝ` have partial sums
controlled by `∑_{i<m} a i ≤ c·m`, and let `w : ℕ → ℝ` be nonnegative and
decreasing (`w (i+1) ≤ w i`).  Then

  `∑_{i<N} w i · a i ≤ c · ∑_{i<N} w i`.

Proof: two applications of `Finset.sum_range_by_parts` (one with `g = a`, one with
`g = 1`) express both sides through the boundary term `w (N-1)` and the increment
sums `∑ (w i − w (i+1))·(partial sum)`; the partial-sum bound `≤ c·m` and the sign
of the (nonpositive) increments combine termwise.  No hypothesis on the sign of
`a` or `c` is needed. -/
theorem abel_master {a w : ℕ → ℝ} {c : ℝ} (N : ℕ)
    (hA : ∀ m, (∑ i ∈ Finset.range m, a i) ≤ c * m)
    (hw_dec : ∀ i, w (i + 1) ≤ w i)
    (hw_nn : ∀ i, 0 ≤ w i) :
    (∑ i ∈ Finset.range N, w i * a i) ≤ c * ∑ i ∈ Finset.range N, w i := by
  have key1 := Finset.sum_range_by_parts w a N
  have key2 := Finset.sum_range_by_parts w (fun _ => (1 : ℝ)) N
  simp only [smul_eq_mul] at key1
  simp only [smul_eq_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at key2
  -- key1 : ∑ w i * a i = w(N-1)·A N − ∑_{i<N-1} (w(i+1)−w i)·A(i+1)
  -- key2 : ∑ w i = w(N-1)·↑N − ∑_{i<N-1} (w(i+1)−w i)·↑(i+1)
  set S1 : ℝ := ∑ i ∈ Finset.range (N - 1),
      (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), a j with hS1
  set S1' : ℝ := ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) * ((i + 1 : ℕ) : ℝ) with hS1'
  -- The boundary term: w(N-1) ≥ 0, A N ≤ c·N.
  have hb : w (N - 1) * (∑ i ∈ Finset.range N, a i) ≤ c * w (N - 1) * (N : ℝ) := by
    calc w (N - 1) * (∑ i ∈ Finset.range N, a i)
        ≤ w (N - 1) * (c * (N : ℝ)) := mul_le_mul_of_nonneg_left (hA N) (hw_nn _)
      _ = c * w (N - 1) * (N : ℝ) := by ring
  -- The increment term: c·S1' ≤ S1, comparing termwise with a sign flip.
  have hs : c * S1' ≤ S1 := by
    rw [hS1, hS1', Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hdec : w (i + 1) - w i ≤ 0 := by linarith [hw_dec i]
    have hAi : (∑ j ∈ Finset.range (i + 1), a j) ≤ c * ((i + 1 : ℕ) : ℝ) := hA (i + 1)
    nlinarith [hAi, hdec]
  -- Assemble.
  have expand : c * (∑ i ∈ Finset.range N, w i) = c * w (N - 1) * (N : ℝ) - c * S1' := by
    rw [key2]; ring
  rw [key1, expand]
  linarith [hb, hs]

/-- `∑_{i<m} Λ(i+1) = ψ(m)` — the range-shifted von Mangoldt partial sum is
Chebyshev's `ψ` evaluated at the natural number `m`. -/
theorem sum_range_vonMangoldt_succ (m : ℕ) :
    (∑ i ∈ Finset.range m, (Λ (i + 1) : ℝ)) = Chebyshev.psi m := by
  have hpsi : ∀ j : ℕ, Chebyshev.psi (j : ℝ) = ∑ n ∈ Finset.Ioc 0 j, Λ n := by
    intro j; rw [Chebyshev.psi, Nat.floor_natCast]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, hpsi, hpsi, Finset.sum_Ioc_succ_top (by omega)]

/-- Reindex `∑_{1≤k≤K} f k = ∑_{i<K} f (i+1)` (shift the `Icc 1 K` sum onto `range K`). -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, f k = ∑ i ∈ Finset.range K, f (i + 1) := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1), ih, Finset.sum_range_succ]

/-! ## Sum/integral comparison for the weight `k^{-β}` -/

/-- **Sum/integral comparison.**  For `0 ≤ β` and `1 ≤ K`, the discrete sum
`∑_{i<K} (i+1)^{-β}` exceeds its first term (`= 1`) by at most `∫₁ᴷ t^{-β}`:

  `∑_{i<K} (i+1)^{-β} ≤ 1 + ∫₁ᴷ t^{-β}`.

Antitone comparison (`AntitoneOn.sum_le_integral`) applied to the reindexed tail. -/
theorem sum_range_rpow_neg_le_integral {β : ℝ} (hβ : 0 ≤ β) {K : ℕ} (hK : 1 ≤ K) :
    (∑ i ∈ Finset.range K, ((i + 1 : ℕ) : ℝ) ^ (-β))
      ≤ 1 + ∫ t in (1 : ℝ)..(K : ℝ), t ^ (-β) := by
  obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : ((0 + 1 : ℕ) : ℝ) ^ (-β) = 1 := by norm_num
  rw [h0]
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-β)) (Set.Icc (1 : ℝ) (1 + (M : ℝ))) := by
    intro s hs t _ hst
    simp only
    rw [Real.rpow_neg (by linarith [hs.1]), Real.rpow_neg (by linarith [hs.1])]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith [hs.1]) β)
      (Real.rpow_le_rpow (by linarith [hs.1]) hst hβ)
  have hcmp := hanti.sum_le_integral
  have hcast : (1 : ℝ) + (M : ℝ) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hcmp
  have hL : (∑ i ∈ Finset.range M, ((i + 1 + 1 : ℕ) : ℝ) ^ (-β))
      = ∑ i ∈ Finset.range M, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-β) := by
    apply Finset.sum_congr rfl; intro i _; congr 1; push_cast; ring
  rw [hL]
  linarith [hcmp]

/-! ## CHEB-Λ — the Chebyshev-`Λ` partial sum at a fractional exponent -/

/-- **CHEB-Λ (`lambda_partial_alpha`).**  For `0 ≤ α < 1` and any `K`,

  `∑_{k≤K} Λ(k)/k^α ≤ (log 4 + 4)·(1 + K^{1-α}/(1-α))`.

The `Λ`-weighted sum is turned into a bare `∑ (i+1)^{-α}` by `abel_master`
(partial sums `= ψ ≤ (log 4 + 4)·m`, `Chebyshev.psi_le_const_mul_self`); the bare
sum is closed by `sum_range_rpow_neg_le_integral` and `∫₁ᴷ t^{-α} = (K^{1-α}-1)/
(1-α)` (`integral_rpow`).  Constant `log 4 + 4 = c_ψ` is honest-explicit. -/
theorem lambda_partial_alpha {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (K : ℕ) :
    (∑ i ∈ Finset.range K, (Λ (i + 1) : ℝ) / ((i + 1 : ℕ) : ℝ) ^ α)
      ≤ (Real.log 4 + 4) * (1 + (K : ℝ) ^ (1 - α) / (1 - α)) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcpos : (0 : ℝ) ≤ Real.log 4 + 4 := by linarith
  -- rewrite `Λ(i+1)/(i+1)^α` as `(i+1)^{-α}·Λ(i+1)`
  have hconv : (∑ i ∈ Finset.range K, (Λ (i + 1) : ℝ) / ((i + 1 : ℕ) : ℝ) ^ α)
      = ∑ i ∈ Finset.range K, ((i + 1 : ℕ) : ℝ) ^ (-α) * (Λ (i + 1) : ℝ) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Real.rpow_neg (by positivity), div_eq_mul_inv, mul_comm]
  rw [hconv]
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      Real.zero_rpow (show (1 : ℝ) - α ≠ 0 by linarith)]
    positivity
  -- Abel: `∑ (i+1)^{-α}·Λ(i+1) ≤ c·∑ (i+1)^{-α}`
  have habel := abel_master (a := fun i => (Λ (i + 1) : ℝ))
    (w := fun i => ((i + 1 : ℕ) : ℝ) ^ (-α)) (c := Real.log 4 + 4) K
    (fun m => by
      rw [sum_range_vonMangoldt_succ]; exact Chebyshev.psi_le_const_mul_self (by positivity))
    (fun i => by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) α)
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ (i + 1)) hα0))
    (fun i => by positivity)
  refine habel.trans ?_
  apply mul_le_mul_of_nonneg_left _ hcpos
  refine (sum_range_rpow_neg_le_integral hα0 hK1).trans ?_
  have hint : (∫ t in (1 : ℝ)..(K : ℝ), t ^ (-α)) = ((K : ℝ) ^ (1 - α) - 1) / (1 - α) := by
    rw [integral_rpow (Or.inl (show (-1 : ℝ) < -α by linarith)),
      show (-α + 1 : ℝ) = 1 - α from by ring, Real.one_rpow]
  rw [hint]
  have h1α : 0 < 1 - α := by linarith
  gcongr
  linarith

/-! ## The shifted-exponent tail (analytic core of ROUGH-TAIL) -/

/-- **Shifted von Mangoldt tail (integer core).**  For `η > 0` and any `K`,

  `∑_{k≤K} Λ(k)·k^{-(1+η)} ≤ (log 4 + 4)·(1 + 1/η)`.

Same `abel_master` engine as CHEB-Λ but at the summable exponent `1+η > 1`; the
bare sum `∑ (i+1)^{-(1+η)} ≤ 1 + ∫₁ᴷ t^{-(1+η)} ≤ 1 + 1/η` since
`∫₁ᴷ t^{-(1+η)} = (K^{-η}-1)/(-η) ≤ 1/η`.  This is the analytic heart of
ROUGH-TAIL, before the prime restriction and the `log p ≥ log y` step. -/
theorem lambda_tail_shift {η : ℝ} (hη : 0 < η) (K : ℕ) :
    (∑ i ∈ Finset.range K, ((i + 1 : ℕ) : ℝ) ^ (-(1 + η)) * (Λ (i + 1) : ℝ))
      ≤ (Real.log 4 + 4) * (1 + 1 / η) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcpos : (0 : ℝ) ≤ Real.log 4 + 4 := by linarith
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    rw [Finset.range_zero, Finset.sum_empty]
    have : (0 : ℝ) ≤ 1 / η := le_of_lt (by positivity)
    nlinarith [hcpos]
  have habel := abel_master (a := fun i => (Λ (i + 1) : ℝ))
    (w := fun i => ((i + 1 : ℕ) : ℝ) ^ (-(1 + η))) (c := Real.log 4 + 4) K
    (fun m => by
      rw [sum_range_vonMangoldt_succ]; exact Chebyshev.psi_le_const_mul_self (by positivity))
    (fun i => by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) (1 + η))
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ (i + 1)) (by linarith)))
    (fun i => by positivity)
  refine habel.trans ?_
  apply mul_le_mul_of_nonneg_left _ hcpos
  refine (sum_range_rpow_neg_le_integral (show (0 : ℝ) ≤ 1 + η by linarith) hK1).trans ?_
  have hint : (∫ t in (1 : ℝ)..(K : ℝ), t ^ (-(1 + η))) = ((K : ℝ) ^ (-η) - 1) / (-η) := by
    have hK1' : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, by
        rw [Set.uIcc_of_le hK1']; intro h; rw [Set.mem_Icc] at h; linarith [h.1]⟩),
      show (-(1 + η) + 1 : ℝ) = -η from by ring, Real.one_rpow]
  rw [hint]
  have hKη0 : (0 : ℝ) ≤ (K : ℝ) ^ (-η) := Real.rpow_nonneg (by positivity) _
  have hrw : ((K : ℝ) ^ (-η) - 1) / (-η) = (1 - (K : ℝ) ^ (-η)) / η := by
    rw [div_neg, ← neg_div, neg_sub]
  rw [hrw]
  gcongr
  linarith

/-! ## ROUGH-TAIL — the rough-prime tail is absolutely bounded -/

/-- **ROUGH-TAIL (`rough_prime_tail`).**  With the GHS smooth/rough cut `y ≥ 8` and
`η = 1/log y`, the rough-prime tail is bounded by an ABSOLUTE constant:

  `∑_{y<p≤x} p^{-1-η} ≤ 2·(log 4 + 4)`.

Route (freeze): on the range `p > y` we have `log p ≥ log y`, so
`p^{-1-η} ≤ (1/log y)·Λ(p)·p^{-1-η}`; extend the prime sum to all `n ≤ x`
(`Λ ≥ 0`) and apply `lambda_tail_shift`, giving `(1/log y)·(log4+4)·(1+1/η) =
(log4+4)·(1/log y + 1) ≤ 2·(log4+4)` since `log y ≥ log 8 > 1`.  The `y ≥ 8`
floor (freeze ⟦R⟧) is exactly what makes `1/log y ≤ 1`. -/
theorem rough_prime_tail {y x η : ℝ} (hy : 8 ≤ y) (hη : η = 1 / Real.log y) :
    (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (p : ℝ) ^ (-1 - η))
      ≤ 2 * (Real.log 4 + 4) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcpos : (0 : ℝ) ≤ Real.log 4 + 4 := by linarith
  have hexp8 : Real.exp 1 < 8 := by have := Real.exp_one_lt_d9; linarith
  have hlogy1 : 1 < Real.log y := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log y := Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have hLpos : 0 < Real.log y := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  -- per-prime bound: `p^{-1-η} ≤ (1/log y)·(p^{-(1+η)}·Λ p)`
  have hper : ∀ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime,
      (p : ℝ) ^ (-1 - η) ≤ (1 / Real.log y) * ((p : ℝ) ^ (-(1 + η)) * (Λ p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hyp, _⟩, hpp⟩ := hp
    have h1 : ⌊y⌋₊ + 1 ≤ p := hyp
    have hpy : y < (p : ℝ) := by
      have : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
      linarith [Nat.lt_floor_add_one y]
    have hlogp : Real.log y ≤ Real.log p := Real.log_le_log (by linarith) (le_of_lt hpy)
    have hppos : (0 : ℝ) < (p : ℝ) ^ (-(1 + η)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hpp.pos) _
    have hratio : (1 : ℝ) ≤ Real.log p / Real.log y := by
      rw [le_div_iff₀ hLpos, one_mul]; exact hlogp
    rw [show (-1 - η : ℝ) = -(1 + η) from by ring, vonMangoldt_apply_prime hpp]
    calc (p : ℝ) ^ (-(1 + η)) = (p : ℝ) ^ (-(1 + η)) * 1 := (mul_one _).symm
      _ ≤ (p : ℝ) ^ (-(1 + η)) * (Real.log p / Real.log y) :=
          mul_le_mul_of_nonneg_left hratio (le_of_lt hppos)
      _ = (1 / Real.log y) * ((p : ℝ) ^ (-(1 + η)) * Real.log p) := by ring
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  -- extend the prime sum to `Icc 1 ⌊x⌋₊` and apply `lambda_tail_shift`
  have hsub : (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.one_lt.le, hp.1.2⟩
  have hcompare : (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime,
        ((p : ℝ) ^ (-(1 + η)) * (Λ p : ℝ)))
      ≤ ∑ i ∈ Finset.range ⌊x⌋₊, (((i + 1 : ℕ) : ℝ) ^ (-(1 + η)) * (Λ (i + 1) : ℝ)) := by
    rw [← sum_Icc_one_eq_sum_range (fun n => ((n : ℝ) ^ (-(1 + η)) * (Λ n : ℝ)))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) vonMangoldt_nonneg)
  have hbound := le_trans hcompare (lambda_tail_shift hηpos ⌊x⌋₊)
  calc (1 / Real.log y) * (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime,
          ((p : ℝ) ^ (-(1 + η)) * (Λ p : ℝ)))
      ≤ (1 / Real.log y) * ((Real.log 4 + 4) * (1 + 1 / η)) :=
        mul_le_mul_of_nonneg_left hbound (div_nonneg zero_le_one hLpos.le)
    _ ≤ 2 * (Real.log 4 + 4) := by
        have h1η : 1 / η = Real.log y := by rw [hη, one_div_one_div]
        rw [h1η]
        have hinvL : 1 / Real.log y ≤ 1 := by rw [div_le_one hLpos]; linarith
        have hLne : Real.log y ≠ 0 := hLpos.ne'
        have heq : (1 / Real.log y) * ((Real.log 4 + 4) * (1 + Real.log y))
            = (Real.log 4 + 4) * (1 / Real.log y + 1) := by field_simp
        rw [heq]
        nlinarith [hcpos, hinvL]

/-! ## HT-1 — the Hall–Tenenbaum core (`hall_tenenbaum_core`)

Route committed (freeze HT-1 ⟦R⟧): `S(x)·log x = ∑ F(n)·log(x/n) + ∑ F(n)·log n`;
the first term `≤ x·∑ F(n)/n` (pointwise `log t ≤ t − 1 ≤ t`); the second is
reindexed over exact prime-power divisors `p^k ∥ n` (`n = p^k·m`, `p ∤ m`,
`F n = F(p^k)·F m` by coprime multiplicativity).  The `k = 1` mass gives
`A·x·∑ F(m)/m` with `A = log 4` (θ-Chebyshev, `theta_le_log4_mul_x`), the `k ≥ 2`
mass gives `B·x` with `B` the absolutely-convergent prime-power constant, reattached
to `∑ F(m)/m` via `F 1 = 1 ⟹ ∑_{m≤x} F(m)/m ≥ 1`.  We never drop the `p^{-k}`
weight (that path hits `ψ(y) − θ(y) ~ √y`). -/

/-- **HT-1 first term.**  For `0 ≤ F` and `x > 0`, the "`log(x/n)`" half of the
Hall–Tenenbaum decomposition is bounded by `x·∑ F(n)/n`, pointwise via
`log t ≤ t − 1 ≤ t` (`Real.log_le_sub_one_of_pos`). -/
theorem ht_first_term {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, F n * Real.log (x / n)) ≤ x * ∑ n ∈ Finset.Icc 1 N, F n / n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hxn : (0 : ℝ) < x / n := div_pos hx hnpos
  have hlog : Real.log (x / n) ≤ x / n - 1 := Real.log_le_sub_one_of_pos hxn
  have hle : Real.log (x / n) ≤ x / n := by linarith
  calc F n * Real.log (x / n) ≤ F n * (x / n) := mul_le_mul_of_nonneg_left hle (hF0 n)
    _ = x * (F n / n) := by ring

/-- **HT-1 reattach.**  With `F 1 = 1` and `0 ≤ F`, the tail weight
`∑_{1 ≤ n ≤ N} F(n)/n ≥ 1` (the `n = 1` term alone is `1`).  This lets the `k ≥ 2`
mass `B·x` be reattached to `B·x·∑ F(m)/m`. -/
theorem ht_reattach {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) (hFone : F 1 = 1) {N : ℕ}
    (hN : 1 ≤ N) : 1 ≤ ∑ n ∈ Finset.Icc 1 N, F n / n := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
  have hnn : ∀ i ∈ Finset.Icc 1 N, 0 ≤ F i / (i : ℝ) := fun i _ =>
    div_nonneg (hF0 i) (by positivity)
  have := Finset.single_le_sum (f := fun n => F n / (n : ℝ)) hnn h1
  simpa [hFone] using this

/-- **HT-1 log-expansion + prime swap (Steps A,B).**  Expand `log n = ∑_{p∣n}
v_p(n)·log p` (`Real.log_nat_eq_sum_factorization`) and swap the order of summation
to the prime-outer form:

  `∑_{n≤N} F(n)·log n = ∑_{p≤N, p prime} log p · ∑_{n≤N, p∣n} F(n)·v_p(n)`.

The inner `n`-sum is exactly the object the per-prime valuation partition consumes. -/
theorem ht_second_term_swap {F : ℕ → ℝ} (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, F n * Real.log n)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          Real.log p * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
            F n * (n.factorization p : ℝ) := by
  set P := (Finset.Icc 1 N).filter Nat.Prime with hP
  -- Step 1+2: per `n`, `F n · log n = ∑_{p ∈ P} [p ∈ primeFactors n] · (F n · v_p(n) · log p)`.
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      F n * Real.log n
        = ∑ p ∈ P, (if p ∈ n.primeFactors then
            F n * (n.factorization p : ℝ) * Real.log p else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_Icc]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
      exact ⟨⟨hpp.one_lt.le, le_trans hple hn.2⟩, hpp⟩
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hP, Finset.mem_filter] at hp
  rw [← Finset.sum_filter]
  have hfe : (Finset.Icc 1 N).filter (fun n => p ∈ n.primeFactors)
      = (Finset.Icc 1 N).filter (fun n => p ∣ n) := by
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨hp.2, h, hn0⟩⟩
  rw [hfe, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _; ring

/-- **HT-1 valuation partition (Step C).**  For a prime `p`, the inner sum
`∑_{n≤N, p∣n} F(n)·v_p(n)` reindexes over exact prime-power divisors: writing
`n = p^k·m` with `k = v_p(n) ≥ 1` and `m = ordCompl[p] n` (`p ∤ m`), coprime
multiplicativity gives `F n = F(p^k)·F m`, so

  `∑_{n≤N, p∣n} F(n)·v_p(n) = ∑_{(k,m): p∤m, p^k·m ≤ N} k·F(p^k)·F(m)`.

The bijection is `n ↦ (v_p(n), ordCompl[p] n)` with inverse `(k,m) ↦ p^k·m`. -/
theorem ht_valuation_partition {F : ℕ → ℝ}
    (hmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b)
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), F n * (n.factorization p : ℝ))
      = ∑ q ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N),
          (q.1 : ℝ) * F (p ^ q.1) * F q.2 := by
  apply Finset.sum_nbij' (i := fun n => (n.factorization p, ordCompl[p] n))
    (j := fun q => p ^ q.1 * q.2)
  · -- hi : forward maps into the codomain
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpn⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hk1 : 1 ≤ n.factorization p := hp.factorization_pos_of_dvd hn0 hpn
    have hkN : n.factorization p ≤ N :=
      le_trans (le_of_lt (Nat.factorization_lt p hn0)) hnN
    have hoc_pos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hn0
    have hoc_le : ordCompl[p] n ≤ n := Nat.le_of_dvd (by omega) (Nat.ordCompl_dvd n p)
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hk1, hkN⟩, hoc_pos, le_trans hoc_le hnN⟩,
      Nat.not_dvd_ordCompl hp hn0, ?_⟩
    rw [Nat.ordProj_mul_ordCompl_eq_self n p]; exact hnN
  · -- hj : inverse maps into the domain
    intro q hq
    obtain ⟨k, m⟩ := q
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hk1, _⟩, hm1, _⟩, _, hpkm⟩ := hq
    have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith [hpk1, hm1], hpkm⟩, ?_⟩
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega : k ≠ 0)) m
  · -- left_inv : j (i n) = n
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  · -- right_inv : i (j q) = q
    intro q hq
    obtain ⟨k, m⟩ := q
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hk1, _⟩, hm1, _⟩, hpm, _⟩ := hq
    have hm0 : m ≠ 0 := by omega
    have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
    have hfp : (p ^ k * m).factorization p = k := by
      rw [Nat.factorization_mul hpk0 hm0, Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]
    have hoc : ordCompl[p] (p ^ k * m) = m := by
      show (p ^ k * m) / p ^ ((p ^ k * m).factorization p) = m
      rw [hfp, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hpk0)]
    change ((p ^ k * m).factorization p, ordCompl[p] (p ^ k * m)) = (k, m)
    rw [Prod.mk.injEq]; exact ⟨hfp, hoc⟩
  · -- summand match : f n = g (i n)
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, _⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hcop : Nat.Coprime (p ^ (n.factorization p)) (ordCompl[p] n) :=
      (Nat.coprime_ordCompl hp hn0).pow_left _
    have hFn : F n = F (p ^ (n.factorization p)) * F (ordCompl[p] n) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
      exact hmul _ _ hcop
    simp only
    rw [hFn]; ring

/-- **θ-Chebyshev bound (Finset form).**  `∑_{p≤M, p prime} log p ≤ log 4 · M`, the
`k = 1` (prime, not prime-power) Chebyshev input for the Hall–Tenenbaum `A`-term.
A wrapper on mathlib's `Chebyshev.theta_le_log4_mul_x` via `primesLE = filter Icc`. -/
theorem ht_theta_bound (M : ℕ) :
    (∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime, Real.log p) ≤ Real.log 4 * M := by
  rw [← Nat.primesLE_eq_filter_Icc_one M, ← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M)

/-! ## The prime-power tail constant `B` (HT-1 `k ≥ 2` mass) -/

/-- **Geometric tail.**  For `0 ≤ r ≤ 1/2` and any `N`,
`∑_{2 ≤ k ≤ N} k·r^k ≤ 6·r²`.  Reindex `k ↦ i+2`, bound the finite sum by the tail
`∑'_{i} f(i+2) = ∑' k·r^k − r = r/(1−r)² − r` (`tsum_coe_mul_geometric`), then
`r²(2−r)/(1−r)² ≤ 6r²` for `r ≤ 1/2`. -/
theorem ht_geom_tail {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 N, (k : ℝ) * r ^ k) ≤ 6 * r ^ 2 := by
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  set f : ℕ → ℝ := fun k => (k : ℝ) * r ^ k with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by rw [hf]; positivity
  have hsum : Summable f := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 hr1
    simpa [hf, pow_one] using h
  set g : ℕ → ℝ := fun k => if 2 ≤ k then f k else 0 with hg
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k; rw [hg]; dsimp only; split; exacts [hfnn k, le_refl 0]
  have hgle : ∀ k, g k ≤ f k := by
    intro k; rw [hg]; dsimp only; split; exacts [le_refl _, hfnn k]
  have hgsum : Summable g := Summable.of_nonneg_of_le hgnn hgle hsum
  have heq : (∑ k ∈ Finset.Icc 2 N, f k) = ∑ k ∈ Finset.Icc 2 N, g k := by
    apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_Icc] at hk
    rw [hg]; dsimp only; rw [if_pos hk.1]
  rw [heq]
  refine (Summable.sum_le_tsum (Finset.Icc 2 N) (fun k _ => hgnn k) hgsum).trans ?_
  -- `∑' g = ∑'_i f(i+2) = (∑' f) − r`
  have htf : (∑' k : ℕ, f k) = r / (1 - r) ^ 2 := by
    simpa [hf, pow_one] using tsum_coe_mul_geometric_of_norm_lt_one hr1
  have hg2 : ∀ i, g (i + 2) = f (i + 2) := fun i => by rw [hg]; dsimp only; rw [if_pos (by omega)]
  have hsumg2 : (∑ k ∈ Finset.range 2, g k) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hg]; simp
  have hsumf2 : (∑ k ∈ Finset.range 2, f k) = r := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; simp [hf]
  have hgtail := hgsum.sum_add_tsum_nat_add 2
  have hftail := hsum.sum_add_tsum_nat_add 2
  have htailval : (∑' k : ℕ, g k) = r / (1 - r) ^ 2 - r := by
    have e1 : (∑' i : ℕ, g (i + 2)) = ∑' i : ℕ, f (i + 2) := tsum_congr hg2
    have e2 : (∑' i : ℕ, f (i + 2)) = (∑' k : ℕ, f k) - r := by
      have h := hftail; rw [hsumf2] at h; linarith
    rw [← hgtail, hsumg2, zero_add, e1, e2, htf]
  rw [htailval]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg r) (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * r)
    (by linarith : (0 : ℝ) ≤ 4 - 3 * r))]

/-- Convergent `3/2`-power partial sum: `∑_{i<N} (i+1)^{-3/2} ≤ 3`.  Same
sum/integral engine as CHEB-Λ (`sum_range_rpow_neg_le_integral`), with
`∫₁ᴺ t^{-3/2} = 2(1 − N^{-1/2}) ≤ 2`. -/
theorem ht_rpow32_sum (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) ≤ 3 := by
  rcases Nat.eq_zero_or_pos N with h0 | h1
  · subst h0; simp
  refine (sum_range_rpow_neg_le_integral (by norm_num) h1).trans ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have hint : (∫ t in (1 : ℝ)..(N : ℝ), t ^ (-(3 / 2) : ℝ))
      = ((N : ℝ) ^ (-(1 / 2) : ℝ) - 1) / (-(1 / 2)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, by
        rw [Set.uIcc_of_le hN1]; intro h; rw [Set.mem_Icc] at h; linarith [h.1]⟩),
      show (-(3 / 2) + 1 : ℝ) = -(1 / 2) from by ring, Real.one_rpow]
  rw [hint]
  have hNn : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [div_neg, ← neg_div, neg_sub]
  have : (1 - (N : ℝ) ^ (-(1 / 2) : ℝ)) / (1 / 2) ≤ 2 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith [hNn]
  linarith

/-- **Prime `log p / p²` bound.**  `∑_{p≤N, p prime} log p / p² ≤ 6`, uniform in
`N`.  Per prime `log p ≤ 2√p` (from `log √p ≤ √p − 1`) gives `log p / p² ≤
2·p^{-3/2}`; extend the prime sum to all `n ≤ N` and apply `ht_rpow32_sum`. -/
theorem ht_log_p_sq_bound (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2) ≤ 6 := by
  have hper : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p / (p : ℝ) ^ 2 ≤ 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hlog : Real.log p ≤ 2 * Real.sqrt p := by
      have h1 : Real.log (Real.sqrt p) ≤ Real.sqrt p - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hppos)
      have h2 : Real.log p = 2 * Real.log (Real.sqrt p) := by
        rw [Real.log_sqrt hppos.le]; ring
      nlinarith [h1, h2, Real.sqrt_nonneg (p : ℝ)]
    have hconv : 2 * (p : ℝ) ^ (-(3 / 2) : ℝ) = 2 * Real.sqrt p / (p : ℝ) ^ 2 := by
      rw [Real.sqrt_eq_rpow, show (-(3 / 2) : ℝ) = (1 / 2) + (-2) from by ring,
        Real.rpow_add hppos, Real.rpow_neg hppos.le,
        show (p : ℝ) ^ (2 : ℝ) = (p : ℝ) ^ 2 from by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]]
      ring
    rw [hconv]
    gcongr
  refine (Finset.sum_le_sum hper).trans ?_
  have hstep : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, 2 * (p : ℝ) ^ (-(3 / 2) : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N, 2 * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  refine hstep.trans ?_
  rw [← Finset.mul_sum, sum_Icc_one_eq_sum_range (fun n => (n : ℝ) ^ (-(3 / 2) : ℝ))]
  have := ht_rpow32_sum N
  linarith

/-! ## HT-1 assembly -/

/-- **A-term per-`m` bound.**  `∑_{p prime, p·m ≤ N} log p ≤ log 4 · (N/m)`.  The
prime set `{p : p·m ≤ N}` equals `primesLE ⌊N/m⌋`, so this is `θ(N/m) ≤ log4·(N/m)`
(`ht_theta_bound`), with `⌊N/m⌋ ≤ N/m` closing the cast. -/
theorem ht_A_inner (m N : ℕ) (hm : 1 ≤ m) :
    (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p * m ≤ N), Real.log p)
      ≤ Real.log 4 * ((N : ℝ) / (m : ℝ)) := by
  have hset : (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p * m ≤ N)
      = (Finset.Icc 1 (N / m)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp1, _⟩, hpp, hpm⟩
      exact ⟨⟨hp1, (Nat.le_div_iff_mul_le hm).mpr hpm⟩, hpp⟩
    · rintro ⟨⟨hp1, hpdiv⟩, hpp⟩
      exact ⟨⟨hp1, le_trans hpdiv (Nat.div_le_self N m)⟩, hpp,
        (Nat.le_div_iff_mul_le hm).mp hpdiv⟩
  rw [hset]
  refine (ht_theta_bound (N / m)).trans ?_
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact mul_le_mul_of_nonneg_left Nat.cast_div_le hlog4

/-- **U_A bound (the `k = 1` mass).**  After dropping `F(p^k) ≤ 1`, the `k = 1`
part of the second term is `∑_p log p · ∑_{p∤m, p·m≤N} F m`; grouping by `m` and
applying `ht_A_inner` (θ-Chebyshev) bounds it by `log 4 · N · ∑ F m/m`. -/
theorem ht_UA_bound {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
       ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
           (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => q.1 = 1),
         (q.1 : ℝ) * F q.2)
      ≤ Real.log 4 * (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, F n / n) := by
  -- Step 1: rewrite the inner pair-sum as `∑_{m ∈ M_p} F m`.
  have hinner : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p * (∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
           (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => q.1 = 1),
         (q.1 : ℝ) * F q.2)
      ≤ Real.log p * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => p * m ≤ N), F m := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hset : (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => q.1 = 1)
        = ({1} : Finset ℕ) ×ˢ ((Finset.Icc 1 N).filter (fun m => ¬ p ∣ m ∧ p * m ≤ N)) := by
      ext ⟨k, m⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨_, hm⟩, hpm2, hpk⟩, hk1⟩
        subst hk1
        exact ⟨rfl, hm, hpm2, by simpa [pow_one] using hpk⟩
      · rintro ⟨rfl, hm, hpm2, hpm⟩
        exact ⟨⟨⟨⟨le_refl 1, hN⟩, hm⟩, hpm2, by simpa [pow_one] using hpm⟩, rfl⟩
    rw [hset, Finset.sum_product, Finset.sum_singleton]
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    calc (∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ p ∣ m ∧ p * m ≤ N), ((1 : ℕ) : ℝ) * F m)
        = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ p ∣ m ∧ p * m ≤ N), F m := by
          simp
      _ ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => p * m ≤ N), F m :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun m hm => by simp only [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.2⟩)
            (fun m _ _ => hF0 m)
  refine (Finset.sum_le_sum hinner).trans ?_
  -- Step 2: group by `m` (swap over the fixed sets `P`, `Icc 1 N`).
  have hstepa : ∀ p : ℕ, Real.log (p : ℝ) *
        ∑ m ∈ (Finset.Icc 1 N).filter (fun m => p * m ≤ N), F m
      = ∑ m ∈ Finset.Icc 1 N, if p * m ≤ N then Real.log (p : ℝ) * F m else 0 := by
    intro p
    rw [Finset.mul_sum]
    exact Finset.sum_filter (fun m => p * m ≤ N) (fun m => Real.log (p : ℝ) * F m)
  have hswap : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => p * m ≤ N), F m)
      = ∑ m ∈ Finset.Icc 1 N, F m *
          ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p * m ≤ N), Real.log p := by
    rw [Finset.sum_congr rfl (fun p _ => hstepa p), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum, ← Finset.filter_filter, ← Finset.sum_filter]
    apply Finset.sum_congr rfl; intro p _; rw [mul_comm]
  rw [hswap]
  have hfin : ∀ m ∈ Finset.Icc 1 N,
      F m * ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p * m ≤ N), Real.log p
        ≤ Real.log 4 * (N : ℝ) * (F m / m) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hmne : (m : ℝ) ≠ 0 := by positivity
    calc F m * ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p * m ≤ N), Real.log p
        ≤ F m * (Real.log 4 * ((N : ℝ) / (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (ht_A_inner m N hm1) (hF0 m)
      _ = Real.log 4 * (N : ℝ) * (F m / m) := by ring
  refine (Finset.sum_le_sum hfin).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]

/-- **U_B bound (the `k ≥ 2` mass).**  The `k ≥ 2` part decouples: `k·F m ≤
k·(N/p^k)·(F m/m)` (from `p^k·m ≤ N`), extend to the full product and factor into
`(∑_{k≥2} k·(1/p)^k)·(∑ F m/m)`; `ht_geom_tail` gives `≤ 6/p²` per prime and
`ht_log_p_sq_bound` sums `∑ log p/p² ≤ 6`, for the absolute constant `B = 36`. -/
theorem ht_UB_bound {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
       ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
           (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
         (q.1 : ℝ) * F q.2)
      ≤ 36 * (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, F n / n) := by
  set W : ℝ := ∑ n ∈ Finset.Icc 1 N, F n / n with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun n _ => div_nonneg (hF0 n) (by positivity))
  have hper : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      Real.log p * ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
        (q.1 : ℝ) * F q.2
      ≤ (6 * ((N : ℝ) * W)) * (Real.log p / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := hpp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hr : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    -- Inner bound: decouple and factor.
    have hinner : (∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
          (q.1 : ℝ) * F q.2)
        ≤ ((N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (k : ℝ) * (1 / (p : ℝ)) ^ k) * W := by
      have hstep1 : (∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
            (q.1 : ℝ) * F q.2)
          ≤ ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
            ((q.1 : ℝ) * ((N : ℝ) * (1 / (p : ℝ)) ^ q.1)) * (F q.2 / q.2) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_Icc] at hq
        obtain ⟨⟨⟨_, hm1, _⟩, _, hpkm⟩, _⟩ := hq
        have hmpos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast (by omega : 0 < q.2)
        have hpkpos : (0 : ℝ) < (p : ℝ) ^ q.1 := by positivity
        have hmle : (q.2 : ℝ) ≤ (N : ℝ) * (1 / (p : ℝ)) ^ q.1 := by
          rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpkpos]
          calc (q.2 : ℝ) * (p : ℝ) ^ q.1 = ((q.2 * p ^ q.1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (N : ℝ) := by exact_mod_cast (by rw [mul_comm]; exact hpkm : q.2 * p ^ q.1 ≤ N)
        have hFdiv : 0 ≤ F q.2 / q.2 := div_nonneg (hF0 q.2) hmpos.le
        have hknn : (0 : ℝ) ≤ (q.1 : ℝ) := by positivity
        have hFm : F q.2 = (q.2 : ℝ) * (F q.2 / q.2) := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hmle (mul_nonneg hknn hFdiv), hFm, hknn, hFdiv]
      refine hstep1.trans ?_
      have hsub : (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1)
          ⊆ (Finset.Icc 2 N) ×ˢ (Finset.Icc 1 N) := by
        intro q hq
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_Icc] at hq
        obtain ⟨⟨⟨⟨hk1, hkN⟩, hm1, hmN⟩, _⟩, hk1'⟩ := hq
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨by omega, hkN⟩, hm1, hmN⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => mul_nonneg (by positivity)
          (div_nonneg (hF0 q.2) (by positivity)))).trans (le_of_eq ?_)
      rw [Finset.sum_product]
      have hcollapse : ∀ k : ℕ, (∑ m ∈ Finset.Icc 1 N,
            (k : ℝ) * ((N : ℝ) * (1 / (p : ℝ)) ^ k) * (F m / m))
          = (k : ℝ) * ((N : ℝ) * (1 / (p : ℝ)) ^ k) * W := by
        intro k; rw [← Finset.mul_sum, ← hW]
      rw [Finset.sum_congr rfl (fun k _ => hcollapse k), ← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    -- geom tail + reattach constant
    refine (mul_le_mul_of_nonneg_left hinner hlogp).trans ?_
    have hgeom : (∑ k ∈ Finset.Icc 2 N, (k : ℝ) * (1 / (p : ℝ)) ^ k) ≤ 6 * (1 / (p : ℝ)) ^ 2 :=
      ht_geom_tail hr0 hr N
    have hgeom' : (N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (k : ℝ) * (1 / (p : ℝ)) ^ k
        ≤ (N : ℝ) * (6 / (p : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
      refine hgeom.trans (le_of_eq ?_)
      rw [div_pow, one_pow]; ring
    have hNW0 : 0 ≤ (N : ℝ) * W := mul_nonneg (Nat.cast_nonneg N) hW0
    calc Real.log p * (((N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (k : ℝ) * (1 / (p : ℝ)) ^ k) * W)
        ≤ Real.log p * (((N : ℝ) * (6 / (p : ℝ) ^ 2)) * W) := by
          apply mul_le_mul_of_nonneg_left _ hlogp
          exact mul_le_mul_of_nonneg_right hgeom' hW0
      _ = (6 * ((N : ℝ) * W)) * (Real.log p / (p : ℝ) ^ 2) := by ring
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  have hlogsum := ht_log_p_sq_bound N
  have hNW0 : 0 ≤ 6 * ((N : ℝ) * W) :=
    mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg N) hW0)
  calc (6 * ((N : ℝ) * W)) * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2
      ≤ (6 * ((N : ℝ) * W)) * 6 := mul_le_mul_of_nonneg_left hlogsum hNW0
    _ = 36 * (N : ℝ) * W := by ring

/-- **HT-1 — the Hall–Tenenbaum core.**  For non-negative multiplicative `F ≤ 1`
with `F 1 = 1` and `x ≥ 2`,

  `(∑_{n≤x} F n)·log x ≤ (1 + log 4 + 36)·x·∑_{n≤x} F n / n`.

The constant is `1 + A + B` with `A = log 4` (θ-Chebyshev) and `B = 36` (the
absolute prime-power-tail constant), matching the freeze shape.  Proof: split
`S(x)·log x = ∑ F(n)·log(x/n) + ∑ F(n)·log n`; the first term is `≤ x·∑F/n`
(`ht_first_term`); the second is reindexed over exact prime-power divisors
(`ht_second_term_swap` ∘ `ht_valuation_partition`), then split into the `k = 1`
mass (`ht_UA_bound`, `≤ log4·N·∑F/n`) and the `k ≥ 2` mass (`ht_UB_bound`,
`≤ 36·N·∑F/n`), with `N = ⌊x⌋ ≤ x`. -/
theorem hall_tenenbaum_core {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n)
    (hmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b)
    (hF1 : ∀ n, F n ≤ 1) (_hFone : F 1 = 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n) * Real.log x
      ≤ (1 + Real.log 4 + 36) * x * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n / n) := by
  set N := ⌊x⌋₊ with hNdef
  have hxpos : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hxpos.le
  set W := ∑ n ∈ Finset.Icc 1 N, F n / n with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun n _ => div_nonneg (hF0 n) (by positivity))
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- Decompose `log x = log(x/n) + log n`.
  have hdecomp : (∑ n ∈ Finset.Icc 1 N, F n) * Real.log x
      = (∑ n ∈ Finset.Icc 1 N, F n * Real.log (x / n))
        + ∑ n ∈ Finset.Icc 1 N, F n * Real.log n := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Real.log_div hxpos.ne' hnpos.ne']; ring
  rw [hdecomp]
  have hfirst : (∑ n ∈ Finset.Icc 1 N, F n * Real.log (x / n)) ≤ x * W :=
    ht_first_term hF0 hxpos N
  -- Second term ≤ (log4 + 36)·N·W.
  have hsecond : (∑ n ∈ Finset.Icc 1 N, F n * Real.log n) ≤ (Real.log 4 + 36) * N * W := by
    rw [ht_second_term_swap]
    -- Bound `F(p^k) ≤ 1`, reindex, giving the "U" sum.
    have hstep1 : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), F n * (n.factorization p : ℝ))
        ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F q.2 := by
      apply Finset.sum_le_sum; intro p hp
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      rw [ht_valuation_partition hmul hpp]
      apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
      apply Finset.sum_le_sum; intro q _
      have h0 : (0 : ℝ) ≤ (q.1 : ℝ) * F q.2 := mul_nonneg (by positivity) (hF0 q.2)
      nlinarith [mul_nonneg h0 (by linarith [hF1 (p ^ q.1)] : (0 : ℝ) ≤ 1 - F (p ^ q.1))]
    refine hstep1.trans ?_
    -- Split `U = U_A + U_B` by `k = 1` vs `k ≥ 2`.
    have hUsplit : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F q.2)
        = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
            ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => q.1 = 1),
              (q.1 : ℝ) * F q.2)
          + (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
            ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
              (q.1 : ℝ) * F q.2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← mul_add, Finset.sum_filter_add_sum_filter_not]
    rw [hUsplit]
    have hUA := ht_UA_bound hF0 hN1
    have hUB := ht_UB_bound hF0 hN1
    have hexp : (Real.log 4 + 36) * (N : ℝ) * W
        = Real.log 4 * (N : ℝ) * W + 36 * (N : ℝ) * W := by ring
    rw [hexp]; linarith [hUA, hUB]
  -- Combine.
  have hcomb : (Real.log 4 + 36) * (N : ℝ) * W ≤ (Real.log 4 + 36) * x * W := by
    apply mul_le_mul_of_nonneg_right _ hW0
    exact mul_le_mul_of_nonneg_left hNx (by linarith)
  have hid : (1 + Real.log 4 + 36) * x * W = x * W + (Real.log 4 + 36) * x * W := by ring
  linarith [hfirst, hsecond, hcomb, hid]

end Salt.MR
