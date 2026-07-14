/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# PE3c-4a — totient / divisor helper lemmas

Prerequisite elementary helpers for the PE3c-4 gate
(`docs/blueprints/flags.md`, "2026-07-13 THE PE3c-4 GATE").  mathlib lacks these
facts; the gate's `hlarge` assembly consumes them:

* `totient_ratio_le_log` — `e/φ(e) ≤ 3·log e` for `3 ≤ e` (explicit `C = 3`);
* `totient_lcm_mul_totient_gcd` — `φ(lcm e f)·φ(gcd e f) = φ e·φ f`;
* `card_divisors_le_two_sqrt` — `d(e) ≤ 2·√e` for `1 ≤ e`;
* `sum_totient_divisors` / `sum_totient_div_self_le` — convenience re-exports.

The load-bearing item is `totient_ratio_le_log`.  Route: `e/φe = ∏_{p∣e} p/(p-1)`
(Euler's product), then the telescoping bound `∏_{p∈S} p/(p-1) ≤ |S| + 1` over any
finset of integers `≥ 2` (proved by inserting the maximum element,
`prod_ratio_le_card_succ`), and finally `ω(e) + 1 ≤ 3·log e` via `2^{ω(e)} ≤ e`.
-/

namespace Salt.Chen

open Nat Finset

/-- Telescoping bound: over any finset `S` of naturals each `≥ 2`, the product of
`p/(p-1)` is at most `|S| + 1`.  Proved by inserting the maximum element: the new
factor `a/(a-1)` multiplies `|s| + 1` by `1 + 1/(a-1)`, and `a ≥ |s| + 2` (the `s`
are distinct integers in `[2, a)`), so the product stays below `|s| + 2`. -/
theorem prod_ratio_le_card_succ (S : Finset ℕ) :
    (∀ p ∈ S, 2 ≤ p) →
      ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ (S.card : ℝ) + 1 := by
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hS
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have hs2 : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have has : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have ihs : ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) ≤ (s.card : ℝ) + 1 := ih hs2
    -- the elements of `s` are distinct integers in `[2, a)`, so `|s| ≤ a - 2`.
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx; rw [Finset.mem_Ico]; exact ⟨hs2 x hx, ha x hx⟩
    have hcardR : (s.card : ℝ) + 2 ≤ (a : ℝ) := by
      have hc : s.card ≤ a - 2 :=
        le_trans (Finset.card_le_card hsub) (by rw [Nat.card_Ico])
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have hA1 : (0 : ℝ) < (a : ℝ) - 1 := by linarith
    have hP0 : 0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hs2 p hp
      apply div_nonneg <;> linarith
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    push_cast
    rw [div_mul_eq_mul_div, div_le_iff₀ hA1]
    nlinarith [ihs, hP0, hcardR, haR,
      mul_le_mul_of_nonneg_left ihs (by linarith : (0 : ℝ) ≤ (a : ℝ))]

/-- Elementary polylog bound on `e/φ(e)`: for `3 ≤ e`, `e/φ(e) ≤ 3·log e`.
The constant `C = 3` is honest: `ω(e) + 1 ≤ 2·log e / log 2 ≤ 3·log e` since
`log 2 > 2/3`. -/
theorem totient_ratio_le_log (e : ℕ) (he : 3 ≤ e) :
    (e : ℝ) / (Nat.totient e : ℝ) ≤ 3 * Real.log (e : ℝ) := by
  have he1 : 1 < e := by omega
  have hφpos : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
  have hφR : (0 : ℝ) < (Nat.totient e : ℝ) := by exact_mod_cast hφpos
  have hlogpos : 0 < Real.log (e : ℝ) := Real.log_pos (by exact_mod_cast he1)
  have hp2 : ∀ p ∈ e.primeFactors, 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  -- `∏ (p - 1)` over the prime factors is positive.
  have hpm1R : (0 : ℝ) < ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2 p hp
    linarith
  -- rewrite the ℕ-subtraction cast of `∏ (p - 1)`.
  have hpm1cast :
      ∏ p ∈ e.primeFactors, (((p : ℕ) - 1 : ℕ) : ℝ)
        = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    have h1 : 1 ≤ p := by have := hp2 p hp; omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  -- Euler's product formula, transported to ℝ.
  have hmulR : (Nat.totient e : ℝ) * ∏ p ∈ e.primeFactors, (p : ℝ)
      = (e : ℝ) * ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    have hN := Nat.totient_mul_prod_primeFactors e
    have hcast : ((Nat.totient e * ∏ p ∈ e.primeFactors, p : ℕ) : ℝ)
               = ((e * ∏ p ∈ e.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at hcast
    rw [hpm1cast] at hcast
    linear_combination hcast
  -- the ratio equals `∏ p/(p-1)`.
  have hratio : (e : ℝ) / (Nat.totient e : ℝ)
      = ∏ p ∈ e.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφR.ne' hpm1R.ne']
    linear_combination -hmulR
  have hprod_le : ∏ p ∈ e.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
      ≤ (e.primeFactors.card : ℝ) + 1 :=
    prod_ratio_le_card_succ e.primeFactors hp2
  -- `2^{ω(e)} ≤ e`.
  have hpow : (2 : ℝ) ^ (e.primeFactors.card) ≤ (e : ℝ) := by
    calc (2 : ℝ) ^ (e.primeFactors.card)
        = ∏ _p ∈ e.primeFactors, (2 : ℝ) := (Finset.prod_const 2).symm
      _ ≤ ∏ p ∈ e.primeFactors, (p : ℝ) := by
          apply Finset.prod_le_prod
          · intro p _; norm_num
          · intro p hp; exact_mod_cast hp2 p hp
      _ = ((∏ p ∈ e.primeFactors, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
      _ ≤ (e : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd e)
  -- turn `2^ω ≤ e` into `ω·log 2 ≤ log e`.
  have hωlog : (e.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (e : ℝ) := by
    rw [← Real.log_pow]
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mpr hpow
  have hloge2 : Real.log 2 ≤ Real.log (e : ℝ) := by
    apply (Real.log_le_log_iff (by norm_num) (by positivity)).mpr
    exact_mod_cast (by omega : (2 : ℕ) ≤ e)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ge : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    have h' : (2 : ℝ) / 3 ≤ (0.6931471803 : ℝ) := by norm_num
    linarith
  -- `ω + 1 ≤ 3·log e`.
  have hfinal : (e.primeFactors.card : ℝ) + 1 ≤ 3 * Real.log (e : ℝ) := by
    have step : ((e.primeFactors.card : ℝ) + 1) * Real.log 2
        ≤ (3 * Real.log (e : ℝ)) * Real.log 2 := by
      nlinarith [hωlog, hloge2,
        mul_nonneg hlogpos.le (by linarith : (0 : ℝ) ≤ 3 * Real.log 2 - 2)]
    exact le_of_mul_le_mul_right step hlog2pos
  calc (e : ℝ) / (Nat.totient e : ℝ)
      = ∏ p ∈ e.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hratio
    _ ≤ (e.primeFactors.card : ℝ) + 1 := hprod_le
    _ ≤ 3 * Real.log (e : ℝ) := hfinal

/-- Totient bookkeeping: `φ(lcm e f)·φ(gcd e f) = φ e·φ f`.  Holds for all `e, f`
(the `e = 0` / `f = 0` cases are `0 = 0`).  Derived from mathlib's
`Nat.totient_gcd_mul_totient_mul` together with `gcd·lcm = e·f`. -/
theorem totient_lcm_mul_totient_gcd (e f : ℕ) :
    Nat.totient (Nat.lcm e f) * Nat.totient (Nat.gcd e f)
      = Nat.totient e * Nat.totient f := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  have hgpos : 0 < Nat.gcd e f := Nat.gcd_pos_of_pos_left f he
  have hφg : 0 < Nat.totient (Nat.gcd e f) := Nat.totient_pos.mpr hgpos
  have hgl : Nat.gcd e f ∣ Nat.lcm e f :=
    dvd_trans (Nat.gcd_dvd_left e f) (Nat.dvd_lcm_left e f)
  -- Step A: `φ(e·f) = φ(lcm e f)·gcd e f`.
  have HA : Nat.totient (e * f) = Nat.totient (Nat.lcm e f) * Nat.gcd e f := by
    have H := Nat.totient_gcd_mul_totient_mul (Nat.gcd e f) (Nat.lcm e f)
    rw [Nat.gcd_eq_left hgl, Nat.gcd_mul_lcm, mul_assoc] at H
    exact Nat.eq_of_mul_eq_mul_left hφg H
  -- Step B: substitute into `φ(gcd)·φ(e·f) = φ e·φ f·gcd`.
  have HB := Nat.totient_gcd_mul_totient_mul e f
  rw [HA] at HB
  apply Nat.eq_of_mul_eq_mul_right hgpos
  have hrw : Nat.totient (Nat.lcm e f) * Nat.totient (Nat.gcd e f) * Nat.gcd e f
      = Nat.totient (Nat.gcd e f) * (Nat.totient (Nat.lcm e f) * Nat.gcd e f) := by ring
  rw [hrw]; exact HB

/-- Divisor-count bound: `d(e) ≤ 2·√e` for `1 ≤ e`.  Each divisor `d` has either
`d ≤ √e` or `e/d ≤ √e`, so `divisors e ⊆ A ∪ (e/·)'' A` where `A` is the set of
divisors `≤ √e`; hence `d(e) ≤ 2·|A| ≤ 2·⌊√e⌋ ≤ 2·√e`. -/
theorem card_divisors_le_two_sqrt (e : ℕ) (he : 1 ≤ e) :
    ((Nat.divisors e).card : ℝ) ≤ 2 * Real.sqrt (e : ℝ) := by
  have he0 : e ≠ 0 := by omega
  set A : Finset ℕ := (Nat.divisors e).filter (· ≤ Nat.sqrt e) with hA
  -- every divisor, or its complementary divisor, lands in `A`.
  have hsub : Nat.divisors e ⊆ A ∪ A.image (e / ·) := by
    intro d hd
    have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
    have heq : e = d * (e / d) := (Nat.mul_div_cancel' hdvd).symm
    rcases Nat.le_sqrt_of_eq_mul heq with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, h1⟩)
    · -- `e/d ≤ √e`, and `d = e/(e/d)`, so `d ∈ (e/·)'' A`.
      have hdiv_dvd : (e / d) ∣ e := ⟨d, (Nat.div_mul_cancel hdvd).symm⟩
      have hmemA : (e / d) ∈ A :=
        Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv_dvd, he0⟩, h2⟩
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e / d, hmemA, ?_⟩)
      exact Nat.div_div_self hdvd he0
  -- `|A| ≤ √e` (nat).
  have hAcard : A.card ≤ Nat.sqrt e := by
    have hAsub : A ⊆ Finset.Icc 1 (Nat.sqrt e) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
    calc A.card ≤ (Finset.Icc 1 (Nat.sqrt e)).card := Finset.card_le_card hAsub
      _ = Nat.sqrt e := by rw [Nat.card_Icc]; omega
  -- assemble the nat bound `d(e) ≤ 2·⌊√e⌋`.
  have hnat : (Nat.divisors e).card ≤ 2 * Nat.sqrt e := by
    calc (Nat.divisors e).card
        ≤ (A ∪ A.image (e / ·)).card := Finset.card_le_card hsub
      _ ≤ A.card + (A.image (e / ·)).card := Finset.card_union_le _ _
      _ ≤ A.card + A.card := by
          have := Finset.card_image_le (s := A) (f := (e / ·))
          omega
      _ ≤ 2 * Nat.sqrt e := by omega
  -- cast and compare `⌊√e⌋ ≤ √e`.
  calc ((Nat.divisors e).card : ℝ)
      ≤ ((2 * Nat.sqrt e : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 2 * (Nat.sqrt e : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt (e : ℝ) := by
        have := Real.nat_sqrt_le_real_sqrt (a := e)
        linarith

/-- `∑_{g ∣ e} φ(g) = e` (re-export of `Nat.sum_totient` in the divisors-Finset
form the assembly consumes). -/
theorem sum_totient_divisors (e : ℕ) :
    ∑ g ∈ e.divisors, Nat.totient g = e := Nat.sum_totient e

/-- Each `φ(g)/g ≤ 1`, so `∑_{g ∣ e} φ(g)/g ≤ d(e)`. -/
theorem sum_totient_div_self_le (e : ℕ) :
    ∑ g ∈ e.divisors, (Nat.totient g : ℝ) / g ≤ (e.divisors.card : ℝ) := by
  calc ∑ g ∈ e.divisors, (Nat.totient g : ℝ) / g
      ≤ ∑ _g ∈ e.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
        rw [div_le_one (by exact_mod_cast hgpos)]
        exact_mod_cast Nat.totient_le g
    _ = (e.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Salt.Chen
