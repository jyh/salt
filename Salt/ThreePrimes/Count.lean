/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.MajorArc

/-!
# Three primes: counting with weights

These are lemmas L1–L3 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 0 and 1).

The proof counts representations `N = n₁ + n₂ + n₃` with the weight `Λ(n₁)Λ(n₂)Λ(n₃)`:

  `R(N) = Σ_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃)`.

* **Counting becomes an integral.** Expanding `S(α)³` and integrating against `e(−Nα)`,
  orthogonality keeps exactly the triples summing to `N`, so `R(N) = ∫₀¹ S(α)³ e(−Nα) dα`. This is
  the identity the whole proof evaluates. It is the same computation as the singular integral's
  count, with the weights `Λ` in place of `1`.
* **The weights cost little, and they convert back to primes.** A triple of primes carries weight
  `log p₁ · log p₂ · log p₃ ≤ (log N)³`. Every other triple with nonzero weight has a proper prime
  power `p^k` (`k ≥ 2`) in some slot. Those powers weigh `ψ(N) − θ(N) ≤ 2√N log N` in total, and the
  other two slots weigh at most a constant times `N (log N)²`. So

    `R(N) ≤ (log N)³ · r(N) + C N^{3/2} (log N)³`,

  where `r(N)` counts the ordered triples of primes summing to `N`. Since the main term is of size
  `N²`, a lower bound `R(N) ≫ N²` forces `r(N) > 0`.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction
open Salt.ExpSum (eR norm_eR)

/-- **The weighted count** `R(N) = Σ_{n₁ + n₂ + n₃ = N} Λ(n₁) Λ(n₂) Λ(n₃)`, over `1 ≤ nᵢ ≤ N`. -/
noncomputable def weightedCount (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
    if a + b + c = N then vonMangoldt a * vonMangoldt b * vonMangoldt c else 0

/-- **The prime count** `r(N)`: the number of ordered triples of primes `(p₁, p₂, p₃)` with
`p₁ + p₂ + p₃ = N`. -/
noncomputable def primeTripleCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun t =>
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = N)).card

/-- **Expanding the weighted cube:** `S(α)³ e(−Nα)` is the triple sum of
`Λ(a) Λ(b) Λ(c) e((a + b + c − N)α)` over `a, b, c ∈ [1, N]`. -/
theorem primeExpSum_cube_expand (N : ℕ) (α : ℝ) :
    primeExpSum N α ^ 3 * eR (-(N : ℝ) * α) = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      ∑ c ∈ Finset.Icc 1 N, ((vonMangoldt a * vonMangoldt b * vonMangoldt c : ℝ) : ℂ) *
        Salt.LS.e ((((a + b + c : ℕ) : ℤ) - N : ℤ) * α) := by
  simp only [primeExpSum, pow_three, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  have he : eR ((((a + b + c : ℕ) : ℤ) - N : ℤ) * α)
      = eR (a * α) * eR (b * α) * eR (c * α) * eR (-(N : ℝ) * α) := by
    rw [← Salt.ExpSum.eR_add, ← Salt.ExpSum.eR_add, ← Salt.ExpSum.eR_add]
    congr 1
    push_cast
    ring
  rw [LS_e_eq_eR, he]
  push_cast
  ring

/-- **Counting becomes an integral:** `R(N) = ∫₀¹ S(α)³ e(−Nα) dα`. -/
theorem weightedCount_eq_integral (N : ℕ) :
    ((weightedCount N : ℝ) : ℂ)
      = ∫ α in (0 : ℝ)..1, primeExpSum N α ^ 3 * eR (-(N : ℝ) * α) := by
  have hcont : ∀ (w : ℂ) (k : ℤ), Continuous fun β : ℝ => w * Salt.LS.e ((k : ℝ) * β) :=
    fun w k => continuous_const.mul (Salt.LS.continuous_e.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_congr (fun α _ => primeExpSum_cube_expand N α),
    intervalIntegral.integral_finsetSum fun a _ => (continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun c _ => hcont _ _).intervalIntegrable _ _]
  rw [weightedCount, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum, intervalIntegral.integral_finsetSum fun b _ =>
    (continuous_finsetSum _ fun c _ => hcont _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.ofReal_sum, intervalIntegral.integral_finsetSum fun c _ =>
    (hcont _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [intervalIntegral.integral_const_mul, Salt.LS.integral_e_int]
  split_ifs with h1 h2 h2 <;> first | omega | simp

/-- **The weight of a non-prime:** `Λ(n)` if `n` is not prime, else `0`; it is nonzero exactly on
the proper prime powers. -/
noncomputable def nonPrimeWeight (n : ℕ) : ℝ := if ¬ n.Prime then vonMangoldt n else 0

/-- The non-prime weight is nonnegative. -/
theorem nonPrimeWeight_nonneg (n : ℕ) : 0 ≤ nonPrimeWeight n := by
  unfold nonPrimeWeight
  split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

/-- For `n ≤ N` the weight `Λ(n)` is at most `log N`. -/
theorem vonMangoldt_le_log_of_le {n N : ℕ} (hn : n ≤ N) : vonMangoldt n ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simpa using Real.log_natCast_nonneg N
  · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hn))

/-- `Σ_{1 ≤ n ≤ N} Λ(n) = ψ(N)`. -/
theorem sum_vonMangoldt_eq_psi (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n = Chebyshev.psi N := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  exact Finset.sum_congr (by ext; simp; omega) fun _ _ => rfl

/-- The proper prime powers up to `N` weigh `Σ_{1 ≤ n ≤ N} [n not prime] Λ(n) = ψ(N) − θ(N)`. -/
theorem sum_nonPrimeWeight_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, nonPrimeWeight n = Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  exact Finset.sum_congr (by ext; simp; omega) fun _ _ => rfl

/-- The prime count as a triple sum of indicators over `a, b, c ∈ [1, N]`. -/
theorem primeTripleCount_eq_sum (N : ℕ) : (primeTripleCount N : ℝ) =
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
      if a.Prime ∧ b.Prime ∧ c.Prime ∧ a + b + c = N then (1 : ℝ) else 0 := by
  simp only [primeTripleCount, Finset.card_filter, Finset.sum_product, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- **The last slot is determined:** when `a + b + c = N` fixes `c`, a triple sum of
`u(a) v(b) w(c)` is at most `(Σ u)(Σ v) L`, given `0 ≤ u, v` and `0 ≤ w ≤ L` on `[1, N]`. -/
theorem triple_sum_le_of_last {N : ℕ} {u v w : ℕ → ℝ} {L : ℝ} (hu : ∀ n, 0 ≤ u n)
    (hv : ∀ n, 0 ≤ v n) (hw : ∀ n ∈ Finset.Icc 1 N, w n ≤ L) (hL : 0 ≤ L) :
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
      (if a + b + c = N then u a * v b * w c else 0)
      ≤ (∑ a ∈ Finset.Icc 1 N, u a) * (∑ b ∈ Finset.Icc 1 N, v b) * L := by
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  have h0 : 0 ≤ u a * v b * L := mul_nonneg (mul_nonneg (hu a) (hv b)) hL
  calc ∑ c ∈ Finset.Icc 1 N, (if a + b + c = N then u a * v b * w c else 0)
      ≤ ∑ c ∈ Finset.Icc 1 N, (if N - (a + b) = c then u a * v b * L else 0) := by
        refine Finset.sum_le_sum fun c hc => ?_
        by_cases h : a + b + c = N
        · rw [if_pos h, if_pos (by omega)]
          exact mul_le_mul_of_nonneg_left (hw c hc) (mul_nonneg (hu a) (hv b))
        · rw [if_neg h]
          split_ifs
          · exact h0
          · exact le_rfl
    _ ≤ u a * v b * L := by
        rw [Finset.sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact h0

/-- **The middle slot is determined:** the same bound `(Σ u)(Σ w) L` when `0 ≤ v ≤ L` on
`[1, N]`, by swapping the inner two sums. -/
theorem triple_sum_le_of_middle {N : ℕ} {u v w : ℕ → ℝ} {L : ℝ} (hu : ∀ n, 0 ≤ u n)
    (hw : ∀ n, 0 ≤ w n) (hv : ∀ n ∈ Finset.Icc 1 N, v n ≤ L) (hL : 0 ≤ L) :
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
      (if a + b + c = N then u a * v b * w c else 0)
      ≤ (∑ a ∈ Finset.Icc 1 N, u a) * (∑ c ∈ Finset.Icc 1 N, w c) * L := by
  refine le_of_eq_of_le ?_ (triple_sum_le_of_last hu hw hv hL)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show a + c + b = a + b + c by omega, mul_right_comm (u a) (v b)]

/-- **One triple, split by primality:** a triple of primes weighs at most `(log N)³`; any other
weighted triple has a non-prime in some slot, and is counted by that slot's term. -/
theorem term_le {N a b c : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    (if a + b + c = N then vonMangoldt a * vonMangoldt b * vonMangoldt c else 0)
      ≤ Real.log N ^ 3 * (if a.Prime ∧ b.Prime ∧ c.Prime ∧ a + b + c = N then 1 else 0)
        + (if a + b + c = N then nonPrimeWeight a * vonMangoldt b * vonMangoldt c else 0)
        + (if a + b + c = N then vonMangoldt a * nonPrimeWeight b * vonMangoldt c else 0)
        + (if a + b + c = N then vonMangoldt a * vonMangoldt b * nonPrimeWeight c else 0) := by
  have hL := Real.log_natCast_nonneg N
  have h0 : ∀ n : ℕ, 0 ≤ vonMangoldt n := fun _ => vonMangoldt_nonneg
  have hq := nonPrimeWeight_nonneg
  by_cases hs : a + b + c = N
  · rw [if_pos hs, if_pos hs, if_pos hs, if_pos hs]
    have t1 := mul_nonneg (mul_nonneg (hq a) (h0 b)) (h0 c)
    have t2 := mul_nonneg (mul_nonneg (h0 a) (hq b)) (h0 c)
    have t3 := mul_nonneg (mul_nonneg (h0 a) (h0 b)) (hq c)
    by_cases hp : a.Prime ∧ b.Prime ∧ c.Prime
    · rw [if_pos ⟨hp.1, hp.2.1, hp.2.2, hs⟩, mul_one]
      have hab := mul_le_mul (vonMangoldt_le_log_of_le ha) (vonMangoldt_le_log_of_le hb)
        (h0 b) hL
      have habc := mul_le_mul hab (vonMangoldt_le_log_of_le hc) (h0 c) (mul_nonneg hL hL)
      nlinarith
    · rw [if_neg fun h => hp ⟨h.1, h.2.1, h.2.2.1⟩, mul_zero, zero_add]
      simp only [not_and_or] at hp
      rcases hp with h | h | h
      · rw [show nonPrimeWeight a = vonMangoldt a from if_pos h]; linarith
      · rw [show nonPrimeWeight b = vonMangoldt b from if_pos h]; linarith
      · rw [show nonPrimeWeight c = vonMangoldt c from if_pos h]; linarith
  · rw [if_neg hs, if_neg hs, if_neg hs, if_neg hs, if_neg fun h => hs h.2.2.2]
    simp

/-- **The prime-power error:** `ψ(N) − θ(N) ≤ 2 √N log N`, `ψ(N) ≤ (log 4 + 4) N`, so
`(ψ − θ) · ψ · log N ≤ 2 (log 4 + 4) N √N (log N)²`. -/
theorem psi_sub_theta_mul_psi_le {N : ℕ} (hN : 1 ≤ N) :
    (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N
      ≤ 2 * (Real.log 4 + 4) * (N * Real.sqrt N) * Real.log N ^ 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hN')
  have hP := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  have hD0 : 0 ≤ Chebyshev.psi N - Chebyshev.theta N := sub_nonneg.2 (Chebyshev.theta_le_psi _)
  have hL := Real.log_natCast_nonneg N
  have h1 := mul_le_mul hD hP (Chebyshev.psi_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 hL
  calc _ ≤ 2 * Real.sqrt N * Real.log N * ((Real.log 4 + 4) * N) * Real.log N := h2
    _ = _ := by ring

/-- **From weights back to primes:** there is a `C` with
`R(N) ≤ (log N)³ · r(N) + C N^{3/2} (log N)³` for every `N ≥ 2`. -/
theorem weightedCount_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      weightedCount N
        ≤ Real.log N ^ 3 * primeTripleCount N + C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3 := by
  refine ⟨12 * (Real.log 4 + 4), by positivity, fun N hN => ?_⟩
  have hL := Real.log_natCast_nonneg N
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hhalf : (1 : ℝ) / 2 ≤ Real.log N := by linarith [Real.log_two_gt_d9]
  have hvL : ∀ n ∈ Finset.Icc 1 N, vonMangoldt n ≤ Real.log N :=
    fun n hn => vonMangoldt_le_log_of_le (Finset.mem_Icc.1 hn).2
  have h0 : ∀ n : ℕ, 0 ≤ vonMangoldt n := fun _ => vonMangoldt_nonneg
  have hsplit : weightedCount N ≤ Real.log N ^ 3 * primeTripleCount N
      + (Chebyshev.psi N - Chebyshev.theta N) * Chebyshev.psi N * Real.log N
      + Chebyshev.psi N * (Chebyshev.psi N - Chebyshev.theta N) * Real.log N
      + Chebyshev.psi N * (Chebyshev.psi N - Chebyshev.theta N) * Real.log N := by
    have hpt : weightedCount N ≤ _ := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
      Finset.sum_le_sum fun c hc => term_le (Finset.mem_Icc.1 ha).2 (Finset.mem_Icc.1 hb).2
        (Finset.mem_Icc.1 hc).2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpt
    rw [primeTripleCount_eq_sum, ← sum_nonPrimeWeight_eq, ← sum_vonMangoldt_eq_psi]
    have e1 := triple_sum_le_of_last nonPrimeWeight_nonneg h0 hvL hL
    have e2 := triple_sum_le_of_last h0 nonPrimeWeight_nonneg hvL hL
    have e3 := triple_sum_le_of_middle h0 nonPrimeWeight_nonneg hvL hL
    linarith
  have hb := psi_sub_theta_mul_psi_le (N := N) (by omega)
  have hrpow : (N : ℝ) ^ ((3 : ℝ) / 2) = N * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by positivity) (by norm_num)]
    norm_num
  have hNs : 0 ≤ (N : ℝ) * Real.sqrt N := by positivity
  have hK : 0 ≤ Real.log 4 + 4 := by positivity
  have hsq : Real.log N ^ 2 ≤ 2 * Real.log N ^ 3 := by nlinarith
  have hfin := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hK) hNs)
  rw [hrpow]
  nlinarith

/-- **A large weighted count forces three primes:** if `R(N) > C N^{3/2} (log N)³`, with `C` the
constant of `weightedCount_le`, then `N` is a sum of three primes. -/
theorem exists_three_primes_of_weightedCount {C : ℝ}
    (hC : ∀ N : ℕ, 2 ≤ N →
      weightedCount N
        ≤ Real.log N ^ 3 * primeTripleCount N + C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3)
    {N : ℕ} (hN : 2 ≤ N)
    (hR : C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3 < weightedCount N) :
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  have hpos : 0 < Real.log N ^ 3 * primeTripleCount N := by linarith [hC N hN]
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hr : (0 : ℝ) < primeTripleCount N := pos_of_mul_pos_right hpos (by positivity)
  have hr' : 0 < primeTripleCount N := by exact_mod_cast hr
  rw [primeTripleCount] at hr'
  obtain ⟨t, ht⟩ := Finset.card_pos.1 hr'
  rw [Finset.mem_filter] at ht
  exact ⟨t.1, t.2.1, t.2.2, ht.2⟩

end Salt.ThreePrimes
