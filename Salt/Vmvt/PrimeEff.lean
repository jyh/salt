/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Dvd
import Salt.SW.SiegelClose

/-!
# The effective interval prime count (Erdős/Bertrand central-binomial route)

`primes_in_Ioc_eff` : there is an EXPLICIT threshold `y₁ ≤ 2^24` with
`y / (8 log y) ≤ #{p prime : y < p ≤ 2y}` for all `y ≥ y₁`.

This is the VMVT-SUMMIT-2 repair of catch #102: `primes_in_Ioc_ge`
(`PrimeCount.lean`) proves the same shape but only above a `k`-INDEPENDENT,
NON-EXPLICIT threshold `y₀ = max(⌈e^{6K}⌉, 1280000)` (`K` the unbounded SW/PNT
error constant), so no fixed-power trivial branch can bridge to it.  Here the
threshold is a pure explicit number (`2^22`), with no `e^{6K}` term.

## Route (the elementary Erdős argument)

Let `P = ∏_{y < p ≤ 2y} p`.  The central binomial `C(2y, y) = centralBinom y`
factors into three prime blocks:
* primes `p ≤ √(2y)`: each `p^{e_p} ≤ 2y`, count `≤ √(2y)`, block `≤ (2y)^{√(2y)}`;
* primes `√(2y) < p ≤ 2y/3`: `e_p ≤ 1`, block `≤ primorial(2y/3) ≤ 4^{2y/3}`;
* primes `2y/3 < p ≤ y`: `e_p = 0`; primes `y < p ≤ 2y`: `e_p ≤ 1`, block `≤ P`.

So `centralBinom y ≤ (2y)^{√(2y)}·4^{2y/3}·P`, while `P ≤ (2y)^{count}` and
`4^y < y·centralBinom y` (`four_pow_lt_mul_centralBinom`).  Taking logs and using
`log(2y) ≤ 1.1 log y` (`y ≥ 2^10`) and `10 log(2y) ≤ √(2y)` (`2y ≥ 2560000`)
yields `count ≥ y/(8 log y)` with comfortable margin.

No `sorry`, no `native_decide`, no new axioms.
-/

open Nat Finset

namespace Salt.Vmvt

/-! ## The nested-sqrt log bound (explicit, no PNT constant) -/

/-- **`10·log u ≤ √u` for `u ≥ 2560000`.**  Nested square roots: with `s₁ = √u`,
`s₂ = √s₁`, one has `log u = 2 log s₁ ≤ 4 s₂` (`log_le_two_sqrt`) and `√u = s₂²`,
reducing to `40 ≤ s₂ = u^{1/4}`, i.e. `u ≥ 40⁴ = 2560000`.  This is the sole
analytic input and it carries NO existential constant. -/
lemma ten_log_le_sqrt {u : ℝ} (hu : 2560000 ≤ u) : 10 * Real.log u ≤ Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := by linarith
  set s1 := Real.sqrt u with hs1
  set s2 := Real.sqrt s1 with hs2
  have hs1nn : 0 ≤ s1 := Real.sqrt_nonneg u
  have hs2nn : 0 ≤ s2 := Real.sqrt_nonneg s1
  have hs2sq : s2 * s2 = s1 := Real.mul_self_sqrt hs1nn
  have hs1sq : s1 * s1 = u := Real.mul_self_sqrt hu0.le
  have hs1ge : (1600 : ℝ) ≤ s1 := by
    have h2 : Real.sqrt (2560000 : ℝ) = 1600 := by
      rw [show (2560000 : ℝ) = 1600 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (1600 : ℝ) = Real.sqrt 2560000 := h2.symm
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
      _ = s1 := hs1.symm
  have hs2ge : (40 : ℝ) ≤ s2 := by
    have h2 : Real.sqrt (1600 : ℝ) = 40 := by
      rw [show (1600 : ℝ) = 40 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (40 : ℝ) = Real.sqrt 1600 := h2.symm
      _ ≤ Real.sqrt s1 := Real.sqrt_le_sqrt hs1ge
      _ = s2 := hs2.symm
  have hs1pos : 0 < s1 := by linarith
  have hlogs1 : Real.log s1 ≤ 2 * s2 := by
    have h := Salt.SW.log_le_two_sqrt hs1pos; rw [← hs2] at h; linarith
  have hlogu : Real.log u ≤ 4 * s2 := by
    have hlt : Real.log u = 2 * Real.log s1 := by
      rw [← hs1sq, Real.log_mul (ne_of_gt hs1pos) (ne_of_gt hs1pos)]; ring
    rw [hlt]; linarith
  calc 10 * Real.log u ≤ 10 * (4 * s2) := by linarith
    _ = 40 * s2 := by ring
    _ ≤ s2 * s2 := by nlinarith [hs2ge, hs2nn]
    _ = s1 := hs2sq

/-! ## The three-block decomposition of the central binomial coefficient -/

/-- **Small + middle blocks.**  The prime factors `p ≤ 2n/3` of `centralBinom n`
contribute `≤ (2n)^{√(2n)}·4^{2n/3}` (Erdős: primes `≤ √(2n)` each `≤ 2n` and are
`≤ √(2n)` in number; primes `√(2n) < p ≤ 2n/3` appear to the first power, product
`≤ primorial(2n/3) ≤ 4^{2n/3}`).  This mirrors the no-prime-free part of
`Nat.centralBinom_le_of_no_bertrand_prime`. -/
lemma centralBinom_small_block (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n2_pos : 1 ≤ 2 * n := by omega
  rw [← Finset.prod_filter_of_ne (p := Nat.Prime)
        (fun q _ hne => by
          by_contra hnp
          exact hne (by rw [Nat.factorization_eq_zero_of_not_prime _ hnp, Nat.pow_zero]))]
  rw [← Finset.prod_filter_mul_prod_filter_not
        (Finset.filter Nat.Prime (Finset.range (2 * n / 3 + 1))) (· ≤ Nat.sqrt (2 * n))]
  apply Nat.mul_le_mul
  · -- small primes: each `p^{e_p} ≤ 2n`, and there are `≤ √(2n)` of them
    refine (Finset.prod_le_prod' (g := fun _ => 2 * n) (fun p _ => ?_)).trans ?_
    · exact Nat.pow_factorization_choose_le (by omega)
    rw [Finset.prod_const]
    apply Nat.pow_le_pow_right n2_pos
    calc ((Finset.filter Nat.Prime (Finset.range (2 * n / 3 + 1))).filter
            (· ≤ Nat.sqrt (2 * n))).card
        ≤ (Finset.Icc 1 (Nat.sqrt (2 * n))).card := by
          apply Finset.card_le_card
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨hq1, hq2⟩ := hq
          rw [Finset.mem_filter] at hq1
          rw [Finset.mem_Icc]
          exact ⟨hq1.2.one_lt.le, hq2⟩
      _ = Nat.sqrt (2 * n) := by rw [Nat.card_Icc]; omega
  · -- middle primes: `e_p ≤ 1`, product `≤ primorial(2n/3) ≤ 4^{2n/3}`
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    unfold primorial
    refine (Finset.prod_le_prod' (g := fun p => p) (fun q hq => ?_)).trans ?_
    · rw [Finset.mem_filter] at hq
      obtain ⟨hq1, hq2⟩ := hq
      rw [Finset.mem_filter] at hq1
      calc q ^ (Nat.centralBinom n).factorization q ≤ q ^ 1 := by
            apply Nat.pow_le_pow_right hq1.2.pos
            exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.1 hq2))
        _ = q := pow_one q
    · refine Finset.prod_le_prod_of_subset_of_one_le' (fun q hq => ?_) (fun q hq _ => ?_)
      · rw [Finset.mem_filter] at hq ⊢
        exact ⟨(Finset.mem_filter.mp hq.1).1, (Finset.mem_filter.mp hq.1).2⟩
      · rw [Finset.mem_filter] at hq; exact hq.2.one_lt.le

/-- **Bertrand block.**  The prime factors `2n/3 < p ≤ 2n` of `centralBinom n`
contribute `≤ ∏_{n < p ≤ 2n} p`: primes `2n/3 < p ≤ n` have `e_p = 0`, primes
`n < p ≤ 2n` have `e_p ≤ 1`. -/
lemma centralBinom_bertrand_block (n : ℕ) (hn : 2 < n) :
    ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), p ^ (Nat.centralBinom n).factorization p
      ≤ ∏ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, p := by
  rw [← Finset.prod_filter_mul_prod_filter_not
        (Finset.Ico (2 * n / 3 + 1) (2 * n + 1)) (fun p => n < p ∧ p.Prime)]
  have hnot : ∏ p ∈ (Finset.Ico (2 * n / 3 + 1) (2 * n + 1)).filter
      (fun p => ¬(n < p ∧ p.Prime)), p ^ (Nat.centralBinom n).factorization p = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ico] at hp
    obtain ⟨⟨hp1, _⟩, hp3⟩ := hp
    rw [not_and_or] at hp3
    rcases hp3 with hpn | hpnp
    · rw [not_lt] at hpn
      by_cases hpp : p.Prime
      · have h0 : (Nat.centralBinom n).factorization p = 0 :=
          Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega)
        rw [h0, Nat.pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, Nat.pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpnp, Nat.pow_zero]
  rw [hnot, mul_one]
  have hset : (Finset.Ico (2 * n / 3 + 1) (2 * n + 1)).filter (fun p => n < p ∧ p.Prime)
      = (Finset.Ioc n (2 * n)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, h4⟩; exact ⟨⟨h3, by omega⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h1, h3⟩
  rw [hset]
  refine Finset.prod_le_prod' (fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hpn, _⟩, hpp⟩ := hp
  calc p ^ (Nat.centralBinom n).factorization p ≤ p ^ 1 := by
        apply Nat.pow_le_pow_right hpp.pos
        apply Nat.factorization_choose_le_one
        have hle : n + 1 ≤ p := hpn
        nlinarith [Nat.pow_le_pow_left hle 2]
    _ = p := pow_one p

/-- **The full central-binomial upper bound.**  `centralBinom n ≤
(2n)^{√(2n)}·4^{2n/3}·∏_{n<p≤2n} p`, splitting `∏_{p ≤ 2n} p^{e_p}` at `2n/3`. -/
lemma centralBinom_le_blocks (n : ℕ) (hn : 2 < n) :
    Nat.centralBinom n
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
        * ∏ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, p := by
  have hsplit : Nat.centralBinom n
      = (∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p)
        * ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1),
            p ^ (Nat.centralBinom n).factorization p := by
    rw [Finset.prod_range_mul_prod_Ico _ (show 2 * n / 3 + 1 ≤ 2 * n + 1 by omega)]
    exact (Nat.prod_pow_factorization_centralBinom n).symm
  rw [hsplit]
  exact Nat.mul_le_mul (centralBinom_small_block n (by omega)) (centralBinom_bertrand_block n hn)

/-- The Bertrand prime product is `≤ (2n)^{count}` (each prime `≤ 2n`). -/
lemma bertrand_prod_le_pow (n : ℕ) :
    (∏ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, p)
      ≤ (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  apply Finset.prod_le_pow_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  exact hp.1.2

/-! ## The effective interval prime count -/

/-- The nat backbone: `4^y ≤ y·(2y)^{√(2y)}·4^{2y/3}·(2y)^{count}`, from
`four_pow_lt_mul_centralBinom` and the three-block decomposition. -/
lemma four_pow_le_count_prod (y : ℕ) (hy2 : 2 < y) (hy4 : 4 ≤ y) :
    4 ^ y ≤ y * ((2 * y) ^ Nat.sqrt (2 * y) * 4 ^ (2 * y / 3)
      * (2 * y) ^ ((Finset.Ioc y (2 * y)).filter Nat.Prime).card) := by
  have h1 : 4 ^ y < y * Nat.centralBinom y := Nat.four_pow_lt_mul_centralBinom y hy4
  have h2 : Nat.centralBinom y
      ≤ (2 * y) ^ Nat.sqrt (2 * y) * 4 ^ (2 * y / 3)
        * (2 * y) ^ ((Finset.Ioc y (2 * y)).filter Nat.Prime).card :=
    le_trans (centralBinom_le_blocks y hy2)
      (Nat.mul_le_mul (le_refl _) (bertrand_prod_le_pow y))
  exact le_of_lt (lt_of_lt_of_le h1 (Nat.mul_le_mul (le_refl y) h2))

/-- **The effective interval prime count.**  There is an EXPLICIT threshold
`y₁ = 4194304 = 2²² ≤ 2²⁴` with `y/(8 log y) ≤ #{p prime : y < p ≤ 2y}` for all
`y ≥ y₁`.  This is the VMVT-SUMMIT-2 repair of catch #102: unlike
`primes_in_Ioc_ge`, the threshold is a pure number — no `e^{6K}` PNT existential. -/
theorem primes_in_Ioc_eff :
    ∃ y₁ : ℕ, y₁ ≤ 2 ^ 24 ∧ ∀ y : ℕ, y₁ ≤ y →
      (y : ℝ) / (8 * Real.log y)
        ≤ (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) := by
  refine ⟨4194304, by norm_num, fun y hy => ?_⟩
  have hy2 : 2 < y := by omega
  have hy4 : 4 ≤ y := by omega
  have hnat := four_pow_le_count_prod y hy2 hy4
  set c : ℕ := ((Finset.Ioc y (2 * y)).filter Nat.Prime).card with hc
  -- real casts and positivity
  have hy0R : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hyge : (2560000 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 2560000 ≤ y)
  have h2yge : (2560000 : ℝ) ≤ 2 * (y : ℝ) := by
    have h : (2560000 : ℕ) ≤ 2 * y := by omega
    have := (Nat.cast_le (α := ℝ)).mpr h; push_cast at this; linarith
  have h2y0 : (0 : ℝ) < 2 * (y : ℝ) := by linarith
  have hLypos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hL2ynn : 0 ≤ Real.log (2 * (y : ℝ)) := le_of_lt (Real.log_pos (by linarith))
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the log inequality from `hnat`
  have hnatR : (4 : ℝ) ^ y
      ≤ (y : ℝ) * ((2 * (y : ℝ)) ^ Nat.sqrt (2 * y) * (4 : ℝ) ^ (2 * y / 3)
          * (2 * (y : ℝ)) ^ c) := by exact_mod_cast hnat
  have hlogle : (y : ℝ) * Real.log 4
      ≤ Real.log (y : ℝ) + (Nat.sqrt (2 * y) : ℝ) * Real.log (2 * (y : ℝ))
        + ((2 * y / 3 : ℕ) : ℝ) * Real.log 4 + (c : ℝ) * Real.log (2 * (y : ℝ)) := by
    rw [← Real.log_pow]
    refine le_trans (Real.log_le_log (by positivity) hnatR) (le_of_eq ?_)
    rw [Real.log_mul (ne_of_gt hy0R) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  -- relax `Nat.sqrt(2y) ≤ √(2y)` and `⌊2y/3⌋ ≤ 2y/3`
  have hsN : (Nat.sqrt (2 * y) : ℝ) * Real.log (2 * (y : ℝ))
      ≤ Real.sqrt (2 * (y : ℝ)) * Real.log (2 * (y : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hL2ynn
    calc (Nat.sqrt (2 * y) : ℝ) ≤ Real.sqrt ((2 * y : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt (2 * (y : ℝ)) := by rw [Nat.cast_mul, Nat.cast_ofNat]
  have hm : ((2 * y / 3 : ℕ) : ℝ) * Real.log 4 ≤ 2 / 3 * ((y : ℝ) * Real.log 4) := by
    have hfloor : ((2 * y / 3 : ℕ) : ℝ) ≤ 2 / 3 * (y : ℝ) := by
      have h := Nat.div_mul_le_self (2 * y) 3
      have hc' := (Nat.cast_le (α := ℝ)).mpr h; push_cast at hc'; linarith
    nlinarith [hfloor, hlog4nn]
  -- (C): the count lower bound, grouping `y·log4` as one atom
  have hC : 1 / 3 * ((y : ℝ) * Real.log 4) - Real.log (y : ℝ)
        - Real.sqrt (2 * (y : ℝ)) * Real.log (2 * (y : ℝ))
      ≤ (c : ℝ) * Real.log (2 * (y : ℝ)) := by linarith [hlogle, hsN, hm]
  -- numeric bounds on the terms
  have hbig : (462 / 1000 : ℝ) * (y : ℝ) ≤ 1 / 3 * ((y : ℝ) * Real.log 4) := by
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    nlinarith [Real.log_two_gt_d9, hy0R, h42]
  have hsqrtlog : Real.sqrt (2 * (y : ℝ)) * Real.log (2 * (y : ℝ))
      ≤ (2 * (y : ℝ)) / 10 := by
    have hten := ten_log_le_sqrt h2yge
    nlinarith [hten, Real.sqrt_nonneg (2 * (y : ℝ)), Real.mul_self_sqrt h2y0.le]
  have hlogy_small : Real.log (y : ℝ) ≤ (y : ℝ) / 100 := by
    have hteny := ten_log_le_sqrt hyge
    have hsqy : Real.sqrt (y : ℝ) ≤ (y : ℝ) / 10 := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (y : ℝ) / 10 by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith [hyge])
    linarith
  -- `c·log(2y) ≥ 0.252 y`, then `log(2y) ≤ 1.5 log y`, then `8 c log y ≥ y`
  have hClow : (252 / 1000 : ℝ) * (y : ℝ) ≤ (c : ℝ) * Real.log (2 * (y : ℝ)) := by
    linarith [hC, hbig, hsqrtlog, hlogy_small]
  have hL2y_le : Real.log (2 * (y : ℝ)) ≤ 3 / 2 * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hy0R)]
    have hy4R : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : (4 : ℕ) ≤ y)
    have h4 : Real.log 4 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) hy4R
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    linarith
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hcL : (c : ℝ) * Real.log (2 * (y : ℝ)) ≤ 3 / 2 * ((c : ℝ) * Real.log (y : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hL2y_le hc0]
  have hfinal : (y : ℝ) ≤ 8 * ((c : ℝ) * Real.log (y : ℝ)) := by linarith [hClow, hcL]
  rw [div_le_iff₀ (mul_pos (by norm_num) hLypos)]
  calc (y : ℝ) ≤ 8 * ((c : ℝ) * Real.log (y : ℝ)) := hfinal
    _ = (c : ℝ) * (8 * Real.log y) := by ring

end Salt.Vmvt
