/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cMaster

/-!
# HB-L2c — the `E_L` odd-cover residual mop-up (node HB-L2c, Horn A keystone)

The last `E_L` residual of the L2c master: `L2cELuncov` (`Salt.HB.L2cMaster`) — the odd window
elements whose left summand is nonzero yet which sit in none of the six landed `E_L` slices.
By the support classification its nonzero terms are exactly the two freeze-acknowledged gaps
(freeze §S4 line 76-77 + house amendments):

* **class (b)** — the *mid-range squarefull corner*: `n₋ = p^a` a proper prime power with
  `Zz < p` and `z ≤ p^a`.  This file's `L2cMidSet`/`L2cMidSum` price it by a crude biUnion
  count with the geometric-tail majorant `1/p^a ≤ z^{-1/2}·(1/p)` (from `a ≥ 2`, `p^a ≥ z`),
  landing the frozen junkExpr `x/z^{1/8}` row at coefficient `1` (`L2cMid_bound`).

Single-writer file (`L2cMop.lean`); it imports the full landed L2c surface via
`Salt.HB.L2cMaster` and touches no other file.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the mid-range squarefull set and the reciprocal-decay primitive

`class (b)` is `n₋ = p^a` with `Zz < p`, `a ≥ 2`, `z ≤ p^a`.  A superset drops the `Zz < p`
guard (not needed for the bound): the geometric tail converges regardless because `p^a ≥ z`
and `a ≥ 2` give the decay `1/p^a ≤ z^{-1/2}·(1/p)`. -/

open Classical in
/-- **The mid-squarefull set**: window elements divisible by a squarefull (`a ≥ 2`) prime
    power `p^a ≥ z` (a superset of the freeze's class (b), on the `n`-side). -/
noncomputable def L2cMidSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    ∃ p a, p.Prime ∧ 2 ≤ a ∧ (z : ℝ) ≤ ((p ^ a : ℕ) : ℝ) ∧ p ^ a ∣ n)

/-- **The mid-squarefull sum** `Σ_{n ∈ L2cMidSet} (Λ̃−Λ)(n)·Λ̃(n+2)`. -/
noncomputable def L2cMidSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ L2cMidSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-- **The reciprocal-decay primitive.**  For a squarefull (`a ≥ 2`) prime power `p^a ≥ z`,
    `1/p^a ≤ z^{-1/2}·(1/p)` — the two facts `p^a ≥ z` and `p^a ≥ p²` combined under a square
    root: `(z^{1/2}·p)² = z·p² ≤ p^a·p^a = (p^a)²`. -/
lemma midjunk_recip {z p a : ℕ} (hp1 : 1 ≤ p) (ha : 2 ≤ a) (hz0 : (0 : ℝ) < z)
    (hzge : (z : ℝ) ≤ ((p ^ a : ℕ) : ℝ)) :
    (1 : ℝ) / ((p ^ a : ℕ) : ℝ) ≤ (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (p : ℝ)) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpaR : ((p ^ a : ℕ) : ℝ) = (p : ℝ) ^ a := by push_cast; ring
  have hp2le : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ a := pow_le_pow_right₀ hpR ha
  have hzge' : (z : ℝ) ≤ (p : ℝ) ^ a := by rw [← hpaR]; exact hzge
  have hzsq : (z : ℝ) * (p : ℝ) ^ 2 ≤ ((p : ℝ) ^ a) ^ 2 := by
    have h := mul_le_mul hzge' hp2le (by positivity) (by positivity)
    calc (z : ℝ) * (p : ℝ) ^ 2 ≤ (p : ℝ) ^ a * (p : ℝ) ^ a := h
      _ = ((p : ℝ) ^ a) ^ 2 := by ring
  have hsqrtbound : (z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ) ≤ (p : ℝ) ^ a := by
    have hlhs0 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ) := by positivity
    have hrhs0 : (0 : ℝ) ≤ (p : ℝ) ^ a := by positivity
    have hsqeq : ((z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ)) ^ 2 = (z : ℝ) * (p : ℝ) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hz0.le,
        show (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    calc (z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ)
        = Real.sqrt (((z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ)) ^ 2) := (Real.sqrt_sq hlhs0).symm
      _ = Real.sqrt ((z : ℝ) * (p : ℝ) ^ 2) := by rw [hsqeq]
      _ ≤ Real.sqrt (((p : ℝ) ^ a) ^ 2) := Real.sqrt_le_sqrt hzsq
      _ = (p : ℝ) ^ a := Real.sqrt_sq hrhs0
  have hden0 : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ) := by positivity
  rw [hpaR]
  calc (1 : ℝ) / ((p : ℝ) ^ a) ≤ 1 / ((z : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ)) :=
        one_div_le_one_div_of_le hden0 hsqrtbound
    _ = (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (p : ℝ)) := by rw [div_mul_div_comm, one_mul]

open Classical in
/-- **The mid-squarefull index pairs** `(p,a)`: `2 ≤ p ≤ 2x+2` prime, `2 ≤ a ≤ log₂(2x+2)`,
    `z ≤ p^a`. -/
noncomputable def L2cMidPairs (z x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
      ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2)))).filter
    (fun pe => (z : ℝ) ≤ ((pe.1 ^ pe.2 : ℕ) : ℝ))

/-- The mid-squarefull cover: every mid element is a multiple of some indexed `p^a`. -/
lemma L2cMidSet_subset_biUnion (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    L2cMidSet χ z x ⊆ (L2cMidPairs z x).biUnion
      (fun pe => (Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n)) := by
  intro n hn
  simp only [L2cMidSet, Finset.mem_filter] at hn
  obtain ⟨hnw, p, a, hp, ha2, hzle, hdvd⟩ := hn
  have hnI : n ∈ Finset.Ioc x (2 * x) := l2cWindow_subset χ z x hnw
  have hnIoc := Finset.mem_Ioc.mp hnI
  have hpa_le : p ^ a ≤ 2 * x + 2 :=
    le_trans (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have haE : a ≤ Nat.log 2 (2 * x + 2) :=
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_left hp.two_le a) hpa_le)
  have hple : p ≤ 2 * x + 2 := le_trans (Nat.le_self_pow (by omega) p) hpa_le
  rw [Finset.mem_biUnion]
  exact ⟨(p, a), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp⟩,
        Finset.mem_Icc.mpr ⟨ha2, haE⟩⟩, hzle⟩,
    Finset.mem_filter.mpr ⟨hnI, hdvd⟩⟩

/-! ## §2 — the mid-squarefull card bound -/

/-- **The mid-squarefull card bound.**  `#L2cMidSet ≤ 64·x·L'²/z^{1/2}` (per-pair count
    `≤ 2x/p^a ≤ 2x·z^{-1/2}·(1/p)`, `≤ 2L'` exponents, `Σ 1/p ≤ 16L'`). -/
lemma L2cMidSet_card_le (χ : DirichletCharacter ℂ q) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ((L2cMidSet χ z x).card : ℝ)
      ≤ 64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz0R : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by
    refine le_trans ?_ hzx
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast (by omega : 1 ≤ z) : (1 : ℝ) ≤ z) 3
    simpa using this
  have hx1 : 1 ≤ x := by exact_mod_cast hx1R
  -- step 1: biUnion cover
  have h1 : ((L2cMidSet χ z x).card : ℝ)
      ≤ ∑ pe ∈ L2cMidPairs z x,
          (((Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n)).card : ℝ) := by
    have hA := Finset.card_le_card (L2cMidSet_subset_biUnion χ z x)
    have hB := Finset.card_biUnion_le (s := L2cMidPairs z x)
      (t := fun pe => (Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n))
    exact_mod_cast le_trans hA hB
  -- step 2: each pair ≤ 2x·(1/z^{1/2})·(1/pe.1)
  have h2 : ∀ pe ∈ L2cMidPairs z x,
      (((Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n)).card : ℝ)
        ≤ 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (pe.1 : ℝ)) := by
    intro pe hpe
    simp only [L2cMidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpe
    obtain ⟨⟨⟨⟨hp2, _⟩, _⟩, ⟨ha2, _⟩⟩, hzle⟩ := hpe
    have hdpos : 0 < pe.1 ^ pe.2 := pow_pos (by omega) pe.2
    have hrecip := midjunk_recip (p := pe.1) (a := pe.2) (z := z) (by omega) ha2 hz0R hzle
    calc (((Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n)).card : ℝ)
        ≤ 2 * (x : ℝ) / ((pe.1 ^ pe.2 : ℕ) : ℝ) := cJunk_dvd_count x (pe.1 ^ pe.2) hdpos
      _ = 2 * (x : ℝ) * (1 / ((pe.1 ^ pe.2 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (x : ℝ) * ((1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (pe.1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (pe.1 : ℝ)) := by ring
  -- step 3: Σ over midPairs of 1/pe.1 ≤ 2L'·16L'
  have h3 : ∑ pe ∈ L2cMidPairs z x, (1 : ℝ) / pe.1 ≤ 2 * Lwin x * (16 * Lwin x) := by
    have hdrop : ∑ pe ∈ L2cMidPairs z x, (1 : ℝ) / pe.1
        ≤ ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
            ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro pe hpe; exact (Finset.mem_filter.mp hpe).1
      · intro pe _ _; positivity
    have hprod : ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
        ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1
        = ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime,
            ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ) * (1 / p) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun p _ => ?_
      trans (∑ _e ∈ Finset.Icc 2 (Nat.log 2 (2 * x + 2)), (1 : ℝ) / (p : ℝ))
      · exact Finset.sum_congr rfl fun e _ => rfl
      · rw [Finset.sum_const, nsmul_eq_mul]
    have hcardB : ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ) ≤ 2 * Lwin x := by
      have hc : (Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card ≤ Nat.log 2 (2 * x + 2) := by
        rw [Nat.card_Icc]; omega
      exact le_trans (by exact_mod_cast hc) (natLog_le_two_Lwin x)
    have hs0 : 0 ≤ ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p :=
      Finset.sum_nonneg fun p _ => by positivity
    calc ∑ pe ∈ L2cMidPairs z x, (1 : ℝ) / pe.1
        ≤ ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
            ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1 := hdrop
      _ = ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ)
            * ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p := by
          rw [hprod, Finset.mul_sum]
      _ ≤ 2 * Lwin x * (16 * Lwin x) :=
          mul_le_mul hcardB (sum_inv_prime_le x hx1) hs0 (by linarith [Lwin_nonneg x])
  -- assembly
  have hconst0 : (0 : ℝ) ≤ 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) := by positivity
  calc ((L2cMidSet χ z x).card : ℝ)
      ≤ ∑ pe ∈ L2cMidPairs z x,
          (((Finset.Ioc x (2 * x)).filter (fun n => pe.1 ^ pe.2 ∣ n)).card : ℝ) := h1
    _ ≤ ∑ pe ∈ L2cMidPairs z x, 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (1 / (pe.1 : ℝ)) :=
        Finset.sum_le_sum h2
    _ = 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2))
          * ∑ pe ∈ L2cMidPairs z x, (1 / (pe.1 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2 * (x : ℝ) * (1 / (z : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Lwin x * (16 * Lwin x)) :=
        mul_le_mul_of_nonneg_left h3 hconst0
    _ = 64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2) := by ring

/-! ## §3 — the class (b) junk budget (the frozen `x/z^{1/8}` junkExpr row) -/

/-- **`L2cMid_bound` — the mid-squarefull (class (b)) budget.**  The frozen junkExpr
    `x/z^{1/8}` shape at coefficient `1`: `L2cMidSum ≤ e^{2z₀}·(x/z^{1/8})·L'³`.  The
    per-summand crude cap `e^{2z₀}·L'²` (`left_summand_cap`) times the card bound
    `64·x·L'²/z^{1/2}` gives `64·e^{2z₀}·x·L'⁴/z^{1/2}`; the `z^{−3/8}` surplus over
    `z^{−1/8}` absorbs `64·L' ≤ z^{3/8}` (using `L' ≤ z^{1/8}` from `hz8` and `z^{1/4} ≥ 64`). -/
theorem L2cMid_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : (Lwin x) ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ x) :
    L2cMidSum χ z x
      ≤ Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * Lwin x ^ 3 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz0R : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hz100R : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by
    refine le_trans ?_ hzx
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by exact_mod_cast (by omega : 1 ≤ z) : (1 : ℝ) ≤ z) 3
    simpa using this
  have hx1 : 1 ≤ x := by exact_mod_cast hx1R
  have hL1 : (1 : ℝ) ≤ Lwin x := one_le_Lwin hx1
  have hL0 : 0 ≤ Lwin x := by linarith
  -- L' ≤ z^{1/8}
  have hLz : Lwin x ≤ (z : ℝ) ^ ((1 : ℝ) / 8) := by
    have h2 : ((Lwin x) ^ 8) ^ ((1 : ℝ) / 8) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hz8 (by norm_num)
    rwa [← Real.rpow_natCast (Lwin x) 8, ← Real.rpow_mul hL0,
      show ((8 : ℕ) : ℝ) * ((1 : ℝ) / 8) = 1 by norm_num, Real.rpow_one] at h2
  -- 64 ≤ z^{1/4}
  have h64z : (64 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    have hmono : ((100 : ℝ) ^ 16) ^ ((1 : ℝ) / 4) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hz100R (by norm_num)
    have heq : ((100 : ℝ) ^ 16) ^ ((1 : ℝ) / 4) = (100 : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast (100 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100),
        show ((16 : ℕ) : ℝ) * ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heq] at hmono; linarith [hmono]
  -- 64·L' ≤ z^{3/8}
  have h64L : 64 * Lwin x ≤ (z : ℝ) ^ ((3 : ℝ) / 8) := by
    have hz38 : (z : ℝ) ^ ((3 : ℝ) / 8) = (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hz0R]; norm_num
    calc 64 * Lwin x ≤ 64 * (z : ℝ) ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left hLz (by norm_num)
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right h64z (Real.rpow_nonneg hz0R.le _)
      _ = (z : ℝ) ^ ((3 : ℝ) / 8) := hz38.symm
  -- the decay 64·L'/z^{1/2} ≤ 1/z^{1/8}
  have hdecay : 64 * Lwin x / (z : ℝ) ^ ((1 : ℝ) / 2) ≤ 1 / (z : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hz0R _) (Real.rpow_pos_of_pos hz0R _), one_mul]
    have hz12 : (z : ℝ) ^ ((1 : ℝ) / 2)
        = (z : ℝ) ^ ((1 : ℝ) / 8) * (z : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_add hz0R]; norm_num
    rw [hz12]
    calc 64 * Lwin x * (z : ℝ) ^ ((1 : ℝ) / 8)
        ≤ (z : ℝ) ^ ((3 : ℝ) / 8) * (z : ℝ) ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right h64L (Real.rpow_nonneg hz0R.le _)
      _ = (z : ℝ) ^ ((1 : ℝ) / 8) * (z : ℝ) ^ ((3 : ℝ) / 8) := by ring
  -- sum ≤ card · summand-cap
  have hsub : L2cMidSet χ z x ⊆ l2cWindow χ z x := fun n hn => by
    simp only [L2cMidSet, Finset.mem_filter] at hn; exact hn.1
  have hsum : L2cMidSum χ z x
      ≤ ((L2cMidSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := by
    rw [L2cMidSum]
    have := Finset.sum_le_card_nsmul (L2cMidSet χ z x) _ _
      (fun n hn => left_summand_cap χ hsq hz2 (hsub hn))
    rwa [nsmul_eq_mul] at this
  have hM0 : (0 : ℝ) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hL0 2)
  have hcard := L2cMidSet_card_le χ hz100 hzx
  -- the core arithmetic: 64·x·L'⁴/z^{1/2} ≤ (x/z^{1/8})·L'³
  have hcore : 64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2) * Lwin x ^ 2
      ≤ (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) * Lwin x ^ 3 := by
    have hstep := mul_le_mul_of_nonneg_left hdecay
      (by positivity : (0 : ℝ) ≤ (x : ℝ) * Lwin x ^ 3)
    calc 64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2) * Lwin x ^ 2
        = (x : ℝ) * Lwin x ^ 3 * (64 * Lwin x / (z : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ (x : ℝ) * Lwin x ^ 3 * (1 / (z : ℝ) ^ ((1 : ℝ) / 8)) := hstep
      _ = (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) * Lwin x ^ 3 := by ring
  calc L2cMidSum χ z x
      ≤ ((L2cMidSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := hsum
    _ ≤ (64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2))
          * (Real.exp (2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right hcard hM0
    _ = Real.exp (2 * z0 z x)
          * (64 * (x : ℝ) * Lwin x ^ 2 / (z : ℝ) ^ ((1 : ℝ) / 2) * Lwin x ^ 2) := by ring
    _ ≤ Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) * Lwin x ^ 3) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
    _ = Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * Lwin x ^ 3 := by ring

/-! ## §4 — House Amendment 5 (catch #252): the residual-class sets and the junk bridges

The `E_L` odd-cover residual `L2cELuncov` (`Salt.HB.L2cMaster`) is closed as the union of
three classes (freeze §S4 taxonomy + Amendment 5):

* **class (a)** — the `T2`-mirror `TmirrorSet`: window `n` with `(n+2)₊` composite and the
  inline junk guard on the `z^{1/4}`-routed block `v = n₋` (the `(n+2)`-side mirror of
  `T2Set`).  Priced by the mirror fibration (`EL_TmirrorT2_bound`).
* **class (b)** — the mid-squarefull `L2cMidSet` (landed above, `L2cMid_bound`).
* **class (c)** — the minus-prime-pair `cPairSet`: `n₊` prime, `n₋ = v` a prime power `< z`,
  `(n+2)₊ = 1` (so `n+2` is a pure `χ=−1` prime power).  Priced under `hLz0` by the crude
  Chebyshev route (`EL_minusPrimePair_bound`). -/

/-- If `Λ̃(m) ≠ 0` then `m₋` is `1` or a prime power (the two-block kill `ω(m₋) ≥ 2 ⇒
    Λ̃(m) = 0`, contrapositive). -/
lemma lamTilde_ne_zero_nMinus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hne : LamTilde χ m ≠ 0) :
    nMinus χ m = 1 ∨ IsPrimePow (nMinus χ m) := by
  rcases Nat.lt_trichotomy (nMinus χ m).primeFactors.card 1 with h | h | h
  · left
    have hc0 : (nMinus χ m).primeFactors.card = 0 := by omega
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc0) with h0 | h1
    · exact absurd h0 (nMinus_pos χ m).ne'
    · exact h1
  · exact Or.inr (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  · exact absurd (LamTilde_eq_zero_of_two_le_card χ hsq hm0 hcop (by omega)) hne

/-- **Junk bridge (n side).**  A small-base squarefull block `p^e ∣ n` (`p ≤ Zz z`, `e ≥ 2`,
    `z^{1/4} < p^e`) puts a window element into `cJunkSet` (left disjunct). -/
lemma mem_cJunkSet_left (χ : DirichletCharacter ℂ q) {z x n p e : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hp : p.Prime) (hpZ : p ≤ Zz z) (he : 2 ≤ e)
    (hgt : (z : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ)) (hdvd : p ^ e ∣ n) :
    n ∈ cJunkSet χ z x := by
  simp only [cJunkSet, Finset.mem_filter]
  exact ⟨hn, p, e, hp, hpZ, he, hgt, Or.inl hdvd⟩

/-- **Junk bridge (n+2 side).**  A small-base squarefull block `p^e ∣ (n+2)` puts a window
    element into `cJunkSet` (right disjunct). -/
lemma mem_cJunkSet_right (χ : DirichletCharacter ℂ q) {z x n p e : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hp : p.Prime) (hpZ : p ≤ Zz z) (he : 2 ≤ e)
    (hgt : (z : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ)) (hdvd : p ^ e ∣ (n + 2)) :
    n ∈ cJunkSet χ z x := by
  simp only [cJunkSet, Finset.mem_filter]
  exact ⟨hn, p, e, hp, hpZ, he, hgt, Or.inr hdvd⟩

/-- **The mirror junk-block guard** (class (a), family-local; the `n`-side mirror of
    `T2JunkBlock`): `v = p^e`, `p` prime `≤ Zz z`, `e ≥ 2`, `z^{1/4} < v`. -/
def TmirrorJunkBlock (z v : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ v = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (v : ℝ)

open Classical in
/-- **The T2-mirror slice** (class (a)) — odd window elements with `(n+2)₊` composite,
    carrying the inline junk guard on the `z^{1/4}`-routed block `v = n₋`. -/
noncomputable def TmirrorSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    Odd n ∧ 1 < nPlus χ (n + 2) ∧ ¬ (nPlus χ (n + 2)).Prime ∧
      ¬ TmirrorJunkBlock z (nMinus χ n))

/-- **The T2-mirror family sum** (class (a)). -/
noncomputable def TmirrorSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ TmirrorSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
/-- **The minus-prime-pair slice** (class (c)) — odd window elements with `n₊` prime,
    `n₋` a prime power `< z`, and `(n+2)₊ = 1` (so `n+2` is a pure `χ=−1` prime power). -/
noncomputable def cPairSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    Odd n ∧ (nPlus χ n).Prime ∧ IsPrimePow (nMinus χ n) ∧ nMinus χ n < z ∧
      nPlus χ (n + 2) = 1 ∧ IsPrimePow (n + 2))

/-- **The minus-prime-pair family sum** (class (c)). -/
noncomputable def cPairSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ cPairSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-! ## §5 — the residual cover (M4): `L2cELuncov`'s support ⊆ (a) ∪ (b) ∪ (c) -/

open Classical in
/-- **The residual membership cover.**  A residual window element (odd, in none of the six
    landed `E_L` slices) with a nonzero left summand lies in class (a) `TmirrorSet`, class (b)
    `L2cMidSet`, or class (c) `cPairSet`.  The case analysis: the support classification forces
    `n₊` prime and `n₋` a prime power (the `n₋ = 1` / `n₊` composite branches land in
    `T2Set`/`cJunkSet`); then `(n+2)₊` composite ⇒ (a), `(n+2)₊ = 1` with `n₋ < z` ⇒ (c),
    `n₋` a squarefull `≥ z` ⇒ (b), and every remaining sub-case forces `T1slice`/`T3FSet`/
    `Tsw`/`cJunkSet` (contradiction with the residual guards). -/
lemma uncov_mem_cover (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz100 : 100 ^ 16 ≤ z)
    (hn : n ∈ l2cWindow χ z x) (hodd : Odd n)
    (hT1 : n ∉ T1slice χ z x) (hT2 : n ∉ T2Set χ z x) (hT3F : n ∉ T3FSet χ z x)
    (hTsw : n ∉ (l2cWindow χ z x).filter (fun m => IsTsw χ z m))
    (hcJ : n ∉ cJunkSet χ z x)
    (hsummand : (LamTilde χ n - Λ n) * LamTilde χ (n + 2) ≠ 0) :
    n ∈ TmirrorSet χ z x ∨ n ∈ L2cMidSet χ z x ∨ n ∈ cPairSet χ z x := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hn
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hn
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hn
  have hadvd : nMinus χ n ∣ n := t2_nMinus_dvd χ hsq hn0 hcop
  have hbdvd : nMinus χ (n + 2) ∣ (n + 2) := t2_nMinus_dvd χ hsq (by omega) hcop2
  have hZzz : Zz z < z := Zz_lt_z hz2
  have hLne : LamTilde χ n - Λ n ≠ 0 := fun h => hsummand (by rw [h, zero_mul])
  have hRne : LamTilde χ (n + 2) ≠ 0 := fun h => hsummand (by rw [h, mul_zero])
  obtain ⟨hnp, hn1, hcl⟩ := lamTilde_sub_support_classification χ hsq hn0 hcop hLne
  have hRcl : nMinus χ (n + 2) = 1 ∨ IsPrimePow (nMinus χ (n + 2)) :=
    lamTilde_ne_zero_nMinus χ hsq (by omega) hcop2 hRne
  -- junk on `n₋` or `(n+2)₋` puts `n` in `cJunkSet`, contradicting the residual guard
  have hjunk_a : ∀ p e : ℕ, p.Prime → p ≤ Zz z → 2 ≤ e → nMinus χ n = p ^ e →
      (z : ℝ) ^ ((1 : ℝ) / 4) < ((nMinus χ n : ℕ) : ℝ) → False := by
    intro p e hp hpZ he heq hgt
    exact hcJ (mem_cJunkSet_left χ hn hp hpZ he (by rw [← heq]; exact hgt) (heq ▸ hadvd))
  have hjunk_b : ∀ p e : ℕ, p.Prime → p ≤ Zz z → 2 ≤ e → nMinus χ (n + 2) = p ^ e →
      (z : ℝ) ^ ((1 : ℝ) / 4) < ((nMinus χ (n + 2) : ℕ) : ℝ) → False := by
    intro p e hp hpZ he heq hgt
    exact hcJ (mem_cJunkSet_right χ hn hp hpZ he (by rw [← heq]; exact hgt) (heq ▸ hbdvd))
  -- eliminate `n₋ = 1` and `n₊` composite: both land in `T2Set` (or `cJunkSet`)
  have hcomp_contra : 1 < nPlus χ n → ¬ (nPlus χ n).Prime → False := by
    intro hA1 hAcomp
    by_cases hjb : T2JunkBlock z (nMinus χ (n + 2))
    · obtain ⟨p, e, hp, hpZ, he, heq, hgt⟩ := hjb
      exact hjunk_b p e hp hpZ he heq hgt
    · exact hT2 (Finset.mem_filter.mpr ⟨hn, hodd, hA1, hAcomp, hjb⟩)
  obtain ⟨hpp_a, hAp⟩ : IsPrimePow (nMinus χ n) ∧ (nPlus χ n).Prime := by
    rcases hcl with h1 | ⟨hpp, hA1⟩
    · exfalso
      have hAn : nPlus χ n = n := by
        have hf := eq_nPlus_mul_nMinus χ hsq hn0 hcop
        rw [h1, mul_one] at hf; exact hf.symm
      exact hcomp_contra (by rw [hAn]; omega) (by rw [hAn]; exact hnp)
    · by_cases hAp : (nPlus χ n).Prime
      · exact ⟨hpp, hAp⟩
      · exact (hcomp_contra hA1 hAp).elim
  obtain ⟨pa, ka, hpa, hka, hapow⟩ := (isPrimePow_nat_iff _).mp hpp_a
  -- the class (b) membership, shared by the `n₋ ≥ z` squarefull sub-cases
  have hmid : 2 ≤ ka → z ≤ nMinus χ n → n ∈ L2cMidSet χ z x := by
    intro hk2 hazge
    have hdvd : pa ^ ka ∣ n := by rw [hapow]; exact hadvd
    have hzle : (z : ℝ) ≤ ((pa ^ ka : ℕ) : ℝ) := by rw [hapow]; exact_mod_cast hazge
    exact Finset.mem_filter.mpr ⟨hn, pa, ka, hpa, hk2, hzle, hdvd⟩
  -- the `n₋ = p prime ≥ z` sub-case forces `T3FSet` (or `cJunkSet`) — contradiction
  have hprime_contra : ka < 2 → z ≤ nMinus χ n → False := by
    intro hk1 hazge
    have haprime : (nMinus χ n).Prime := by
      rw [← hapow, show ka = 1 by omega, pow_one]; exact hpa
    by_cases hjb : T3FJunkBlock z (nMinus χ (n + 2))
    · obtain ⟨p, e, hp, hpZ, he, heq, hgt⟩ := hjb
      exact hjunk_b p e hp hpZ he heq hgt
    · exact hT3F (Finset.mem_filter.mpr ⟨hn, hAp, haprime, hazge, hodd, hjb⟩)
  -- case split on `(n+2)₊`
  rcases eq_or_ne (nPlus χ (n + 2)) 1 with hB1 | hBne1
  · -- `(n+2)₊ = 1`: `n+2` is a pure `χ=−1` prime power
    have hbeq : n + 2 = nMinus χ (n + 2) := by
      have hf := eq_nPlus_mul_nMinus χ hsq (show n + 2 ≠ 0 by omega) hcop2
      rw [hB1, one_mul] at hf; exact hf
    have hppn2 : IsPrimePow (n + 2) := by
      rcases hRcl with h | h
      · rw [h] at hbeq; omega
      · rw [hbeq]; exact h
    by_cases hazlt : nMinus χ n < z
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr
        ⟨hn, hodd, hAp, hpp_a, hazlt, hB1, hppn2⟩))
    · rw [not_lt] at hazlt
      rcases Nat.lt_or_ge ka 2 with hk1 | hk2
      · exact (hprime_contra hk1 hazlt).elim
      · exact Or.inr (Or.inl (hmid hk2 hazlt))
  · -- `(n+2)₊ ≠ 1`
    have hBpos : 0 < nPlus χ (n + 2) := nPlus_pos χ (n + 2)
    have hB1' : 1 < nPlus χ (n + 2) := by omega
    by_cases hBp : (nPlus χ (n + 2)).Prime
    · -- `(n+2)₊` prime
      by_cases hazlt : nMinus χ n < z
      · -- `n₋ < z`: `T1slice` (if `(n+2)₋ < z`) or `Tsw` (if `(n+2)₋ ≥ z`) — contradiction
        exfalso
        have ha1 : 1 < nMinus χ n := hpp_a.one_lt
        by_cases hbz : nMinus χ (n + 2) < z
        · exact hT1 (Finset.mem_filter.mpr ⟨hn, hodd, hAp, hBp, ha1, hazlt, hbz⟩)
        · rw [not_lt] at hbz
          have hppb : IsPrimePow (nMinus χ (n + 2)) := by
            rcases hRcl with h | h
            · rw [h] at hbz; omega
            · exact h
          obtain ⟨pb, kb, hpb, hkb, hbpow⟩ := (isPrimePow_nat_iff _).mp hppb
          -- `(n+2)₋ = pb^kb`; its roughness reduces to `Zz z < pb`
          by_cases hpbZ : Zz z < pb
          · have hbrough : ∀ p, p.Prime → p ∣ nMinus χ (n + 2) → Zz z < p := by
              intro p hp hpd
              rw [← hbpow] at hpd
              rw [(Nat.prime_dvd_prime_iff_eq hp hpb).mp (hp.dvd_of_dvd_pow hpd)]; exact hpbZ
            by_cases hvjunk : TswJunkV z (nMinus χ n)
            · obtain ⟨p, e, hp, hpZ, he, heq, hgt⟩ := hvjunk
              exact hjunk_a p e hp hpZ he heq hgt
            · exact hTsw (Finset.mem_filter.mpr
                ⟨hn, hAp, hpp_a, ha1, hazlt, hppb, hbz, hBp, hbrough, hvjunk, hodd⟩)
          · have hpbZz : pb ≤ Zz z := not_lt.mp hpbZ
            have hkb2 : 2 ≤ kb := by
              by_contra hlt
              have hkb1 : kb = 1 := by omega
              rw [hkb1, pow_one] at hbpow
              omega
            refine hjunk_b pb kb hpb hpbZz hkb2 hbpow.symm ?_
            rw [← hbpow]
            have hzR : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
            calc (z : ℝ) ^ ((1 : ℝ) / 4)
                < (z : ℝ) := by
                  have h := Real.rpow_lt_rpow_of_exponent_lt hzR (by norm_num : (1 : ℝ) / 4 < 1)
                  rwa [Real.rpow_one] at h
              _ ≤ (nMinus χ (n + 2) : ℝ) := by exact_mod_cast hbz
              _ = ((pb ^ kb : ℕ) : ℝ) := by rw [hbpow]
      · -- `n₋ ≥ z`: squarefull ⇒ (b), prime ⇒ `T3FSet`/`cJunkSet` contradiction
        rw [not_lt] at hazlt
        rcases Nat.lt_or_ge ka 2 with hk1 | hk2
        · exact (hprime_contra hk1 hazlt).elim
        · exact Or.inr (Or.inl (hmid hk2 hazlt))
    · -- `(n+2)₊` composite: class (a)
      left
      refine Finset.mem_filter.mpr ⟨hn, hodd, hB1', hBp, ?_⟩
      rintro ⟨p, e, hp, hpZ, he, heq, hgt⟩
      exact hjunk_a p e hp hpZ he heq hgt

open Classical in
/-- **The refined `E_L` odd-cover residual bound** (M4).  `L2cELuncov ≤ TmirrorSum +
    L2cMidSum + cPairSum` — the residual's nonzero support lands in class (a)/(b)/(c)
    (`uncov_mem_cover`), so its sum splits over the three class sums (all summands `≥ 0`). -/
lemma ELodd_cover' (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) :
    L2cELuncov χ z x ≤ TmirrorSum χ z x + L2cMidSum χ z x + cPairSum χ z x := by
  classical
  have hnn : ∀ n, 0 ≤ (LamTilde χ n - Λ n) * LamTilde χ (n + 2) :=
    fun n => EL_summand_nonneg χ hsq n
  have hite : ∀ (n : ℕ) (T : Finset ℕ),
      0 ≤ (if n ∈ T then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0) := by
    intro n T; split_ifs with h
    · exact hnn n
    · exact le_refl 0
  set W := (l2cWindow χ z x).filter (fun n => Odd n ∧ n ∉ T1slice χ z x ∧ n ∉ T2Set χ z x ∧
      n ∉ T3FSet χ z x ∧ n ∉ (l2cWindow χ z x).filter (fun m => IsTsw χ z m) ∧
      n ∉ cJunkSet χ z x ∧ n ∉ cornerSet χ z x) with hW
  have key : ∀ n ∈ W, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (if n ∈ TmirrorSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
        + (if n ∈ L2cMidSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
        + (if n ∈ cPairSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0) := by
    intro n hn
    rw [hW, Finset.mem_filter] at hn
    obtain ⟨hnwin, hodd, hT1, hT2, hT3F, hTsw, hcJ, _hcorner⟩ := hn
    by_cases hs : (LamTilde χ n - Λ n) * LamTilde χ (n + 2) = 0
    · have h0 := hite n (TmirrorSet χ z x)
      have h1 := hite n (L2cMidSet χ z x)
      have h2 := hite n (cPairSet χ z x)
      linarith [hs.le]
    · rcases uncov_mem_cover χ hsq hz100 hnwin hodd hT1 hT2 hT3F hTsw hcJ hs with h | h | h
      · simp only [if_pos h]
        linarith [hite n (L2cMidSet χ z x), hite n (cPairSet χ z x)]
      · simp only [if_pos h]
        linarith [hite n (TmirrorSet χ z x), hite n (cPairSet χ z x)]
      · simp only [if_pos h]
        linarith [hite n (TmirrorSet χ z x), hite n (L2cMidSet χ z x)]
  have hb1 : (∑ n ∈ W.filter (fun n => n ∈ TmirrorSet χ z x),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2)) ≤ TmirrorSum χ z x := by
    rw [TmirrorSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have hb2 : (∑ n ∈ W.filter (fun n => n ∈ L2cMidSet χ z x),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2)) ≤ L2cMidSum χ z x := by
    rw [L2cMidSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have hb3 : (∑ n ∈ W.filter (fun n => n ∈ cPairSet χ z x),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2)) ≤ cPairSum χ z x := by
    rw [cPairSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have hsum : L2cELuncov χ z x
      ≤ (∑ n ∈ W.filter (fun n => n ∈ TmirrorSet χ z x),
            (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ W.filter (fun n => n ∈ L2cMidSet χ z x),
            (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ W.filter (fun n => n ∈ cPairSet χ z x),
            (LamTilde χ n - Λ n) * LamTilde χ (n + 2)) := by
    rw [L2cELuncov, ← hW]
    refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_filter]
  exact le_trans hsum (add_le_add (add_le_add hb1 hb2) hb3)

/-! ## §6 — class (c): the minus-prime-pair budget (M3, under `hLz0`)

The per-`v` fibration (`v = n₋` a prime power `< z`): the cofactor `P = n/v = n₊` is a
`χ=+1` prime with `x/v < P ≤ 2x/v`, so the fiber injects into the `χ=+1` primes counted by
`chebyshev_chi_count` at the floor `log(x/v) ≥ log z`.  The weight `Λ(v)·L'` (via
`lamTilde_single_block_le` on `n`, the crude cap on `n+2`), the Mertens sum `Σ Λ(v)/v ≤
2L'`, and the `hLz0` absorption `z₀·e^{2·log2·z₀}·L'² ≤ e^{5z₀}` close it at `C = 4`. -/

open Classical in
/-- **The class (c) per-fiber count.**  For each `v`, the `v`-fiber of `cPairSet`
    (`n₋ = v`) has weighted count `Σ Λ(n₋) ≤ 2x·PS/(log z)·(Λ(v)/v)`: the cofactor
    `P = n₊ = n/v` is a `χ=+1` prime in `(x/v, 2x/v]`, counted by `chebyshev_chi_count`. -/
lemma cpair_fiber_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) (v : ℕ) :
    (∑ n ∈ (cPairSet χ z x).filter (fun n => nMinus χ n = v), Λ (nMinus χ n))
      ≤ 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z * (Λ v / v) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hxR : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hRHS0 : 0 ≤ 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z * (Λ v / v) :=
    mul_nonneg (div_nonneg (by positivity) hlogz.le)
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg v))
  have hconst : ∀ n ∈ (cPairSet χ z x).filter (fun n => nMinus χ n = v),
      Λ (nMinus χ n) = Λ v := fun n hn => by rw [(Finset.mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rcases Finset.eq_empty_or_nonempty ((cPairSet χ z x).filter (fun n => nMinus χ n = v))
    with he | ⟨n₀, hn₀⟩
  · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]; exact hRHS0
  · -- `v = n₋(n₀)` is a prime power `< z`; the fiber injects into the `χ=+1` primes of `(x/v,2x/v]`
    obtain ⟨hn₀c, hn₀v⟩ := Finset.mem_filter.mp hn₀
    simp only [cPairSet, Finset.mem_filter] at hn₀c
    obtain ⟨_, _, _, hvpp, hvz, _, _⟩ := hn₀c
    rw [hn₀v] at hvpp hvz
    have hv2 : 2 ≤ v := hvpp.two_le
    have hvpos : 0 < v := by omega
    have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hvpos
    -- `2v ≤ x` and `z·v ≤ x` (from `v < z` and `z³ ≤ x`)
    have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
    have hzv : (z : ℝ) * v ≤ x := by
      have h1 : (v : ℝ) < z := by exact_mod_cast hvz
      have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
      nlinarith [hzx, sq_nonneg ((z : ℝ) - v), hz1R]
    have hzvN : z * v ≤ x := by exact_mod_cast hzv
    have h2vN : 2 * v ≤ x := by
      have h := le_trans (mul_le_mul_of_nonneg_right hz2R (Nat.cast_nonneg (α := ℝ) v)) hzv
      exact_mod_cast h
    have hxvz : z ≤ x / v := (Nat.le_div_iff_mul_le hvpos).mpr hzvN
    have hxv1 : 1 < x / v := lt_of_lt_of_le (by omega) hxvz
    -- the injection into `G_v := (Ioc (x/v) (2x/v)) ∩ {χ=+1 primes}`
    set Gv := (Finset.Ioc (x / v) (2 * x / v)).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1)
      with hGv
    have hinj : ((cPairSet χ z x).filter (fun n => nMinus χ n = v)).card ≤ Gv.card := by
      refine Finset.card_le_card_of_injOn (fun n => nPlus χ n) ?_ ?_
      · intro n hn
        obtain ⟨hnc, hnv⟩ := Finset.mem_filter.mp hn
        simp only [cPairSet, Finset.mem_filter] at hnc
        obtain ⟨hnwin, _, hAp, _, _, _, _⟩ := hnc
        have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnwin
        have hcop : Nat.Coprime n q := l2cWindow_coprime χ hnwin
        have hfac : n = nPlus χ n * v := by
          rw [← hnv]; exact eq_nPlus_mul_nMinus χ hsq hn0 hcop
        have hnle : n ≤ 2 * x := l2cWindow_le χ hnwin
        have hnlt : x < n := l2cWindow_lt χ hnwin
        change nPlus χ n ∈ Gv
        rw [hGv]
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hAp, nPlus_dvd_sign hAp dvd_rfl⟩
        · rw [Nat.div_lt_iff_lt_mul hvpos, ← hfac]; exact hnlt
        · rw [Nat.le_div_iff_mul_le hvpos, ← hfac]; exact hnle
      · intro n hn m hm hnm
        rw [Finset.mem_coe, Finset.mem_filter] at hn hm
        have hnwin : n ∈ l2cWindow χ z x := (Finset.mem_filter.mp hn.1).1
        have hmwin : m ∈ l2cWindow χ z x := (Finset.mem_filter.mp hm.1).1
        have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnwin
        have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hmwin
        have hcn : Nat.Coprime n q := l2cWindow_coprime χ hnwin
        have hcm : Nat.Coprime m q := l2cWindow_coprime χ hmwin
        have hfn : n = nPlus χ n * v := by rw [← hn.2]; exact eq_nPlus_mul_nMinus χ hsq hn0 hcn
        have hfm : m = nPlus χ m * v := by rw [← hm.2]; exact eq_nPlus_mul_nMinus χ hsq hm0 hcm
        have hnm' : nPlus χ n = nPlus χ m := hnm
        rw [hfn, hfm, hnm']
    -- bound `card Gv` by `chebyshev_chi_count`
    have hcheb : (Gv.card : ℝ)
        ≤ ((2 * x / v : ℕ) : ℝ) / Real.log ((x / v : ℕ) : ℝ) * PretenseSum χ (2 * x + 2) :=
      chebyshev_chi_count χ hxv1 (le_trans (Nat.div_le_self (2 * x) v) (by omega))
    have hlogxv : Real.log z ≤ Real.log ((x / v : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) (by exact_mod_cast hxvz)
    have hlogxvpos : 0 < Real.log ((x / v : ℕ) : ℝ) := lt_of_lt_of_le hlogz hlogxv
    have hbR : ((2 * x / v : ℕ) : ℝ) ≤ 2 * (x : ℝ) / v := by
      calc ((2 * x / v : ℕ) : ℝ) ≤ ((2 * x : ℕ) : ℝ) / v := Nat.cast_div_le
        _ = 2 * (x : ℝ) / v := by push_cast; ring
    -- assemble
    have hcardR : (((cPairSet χ z x).filter (fun n => nMinus χ n = v)).card : ℝ) ≤ (Gv.card : ℝ) :=
      by exact_mod_cast hinj
    have hchain : (Gv.card : ℝ) ≤ 2 * (x : ℝ) / v / Real.log z * PretenseSum χ (2 * x + 2) := by
      refine le_trans hcheb ?_
      apply mul_le_mul_of_nonneg_right _ hPS0
      rw [div_le_div_iff₀ hlogxvpos hlogz]
      exact mul_le_mul hbR hlogxv hlogz.le (by positivity)
    calc (((cPairSet χ z x).filter (fun n => nMinus χ n = v)).card : ℝ) * Λ v
        ≤ (2 * (x : ℝ) / v / Real.log z * PretenseSum χ (2 * x + 2)) * Λ v :=
          mul_le_mul_of_nonneg_right (le_trans hcardR hchain) vonMangoldt_nonneg
      _ = 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z * (Λ v / v) := by ring

/-- **The class (c) per-summand cap.**  On `cPairSet`, `(Λ̃−Λ)(n)·Λ̃(n+2) ≤
    e^{2·log2·z₀}·(Λ(n₋)·L')` — the sharp single-block cap on `n` (`n₋` a prime power) times
    the crude cap on `n+2`. -/
lemma cpair_summand_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} (hz2 : 2 ≤ z)
    {n : ℕ} (hn : n ∈ cPairSet χ z x) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * (Λ (nMinus χ n) * Lwin x) := by
  simp only [cPairSet, Finset.mem_filter] at hn
  obtain ⟨hnwin, _, _, hvpp, _, _, _⟩ := hn
  have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnwin
  have hcop : Nat.Coprime n q := l2cWindow_coprime χ hnwin
  have hL : LamTilde χ n - Λ n ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ n) := by
    calc LamTilde χ n - Λ n ≤ LamTilde χ n := by linarith [vonMangoldt_nonneg (n := n)]
      _ ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ n) :=
          lamTilde_single_block_le χ hsq z x hz2 hn0 hcop
            (by have := l2cWindow_le χ hnwin; omega)
            (fun p hp hpd hchi => l2cWindow_rough χ hnwin hp hpd hchi) hvpp
  have hR : LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
    lamTilde_cap_window_add_two χ hsq hz2 hnwin
  have hLnn : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hRnn : 0 ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ n) :=
    mul_nonneg (Real.exp_pos _).le vonMangoldt_nonneg
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ n))
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x) := mul_le_mul hL hR hLnn hRnn
    _ = Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)
          * (Λ (nMinus χ n) * Lwin x) := by ring
    _ = Real.exp (2 * Real.log 2 * z0 z x) * (Λ (nMinus χ n) * Lwin x) := by
        rw [← Real.exp_add]; ring_nf

/-- **The class (c) exponent absorption** (uses `hLz0`).  `z₀·e^{2·log2·z₀}·L'² ≤ e^{5z₀}`
    (`z₀ ≤ e^{z₀}`, `2·log2 < 2`, `L'² ≤ e^{2z₀}` from `hLz0`). -/
lemma cpair_exp_absorb {z x : ℕ} (hz2 : 2 ≤ z) (hLz0 : Lwin x ≤ Real.exp (z0 z x)) :
    z0 z x * Real.exp (2 * Real.log 2 * z0 z x) * Lwin x ^ 2 ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
  have ht : z0 z x ≤ Real.exp (z0 z x) := by linarith [Real.add_one_le_exp (z0 z x)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hexp2log2 : Real.exp (2 * Real.log 2 * z0 z x) ≤ Real.exp (2 * z0 z x) :=
    Real.exp_le_exp.mpr (by nlinarith [hz0, hlog2, mul_nonneg hz0 (sub_nonneg.mpr hlog2)])
  have hL2 : Lwin x ^ 2 ≤ Real.exp (2 * z0 z x) := by
    calc Lwin x ^ 2 = Lwin x * Lwin x := by ring
      _ ≤ Real.exp (z0 z x) * Real.exp (z0 z x) := mul_le_mul hLz0 hLz0 hL0 (Real.exp_pos _).le
      _ = Real.exp (2 * z0 z x) := by rw [← Real.exp_add]; ring_nf
  have hstep : z0 z x * Real.exp (2 * Real.log 2 * z0 z x)
      ≤ Real.exp (z0 z x) * Real.exp (2 * z0 z x) :=
    mul_le_mul ht hexp2log2 (Real.exp_pos _).le (Real.exp_pos _).le
  calc z0 z x * Real.exp (2 * Real.log 2 * z0 z x) * Lwin x ^ 2
      ≤ Real.exp (z0 z x) * Real.exp (2 * z0 z x) * Real.exp (2 * z0 z x) :=
        mul_le_mul hstep hL2 (by positivity) (by positivity)
    _ = Real.exp (5 * z0 z x) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- **`EL_minusPrimePair_bound` — the class (c) budget** (M3, Amendment 5 route, under
    `hLz0`).  `cPairSum ≤ 4·(x/L')·e^{5z₀}·PS(2x+2)` (the `J2` row at `C = 4`): the
    per-summand cap `e^{2·log2·z₀}·Λ(n₋)·L'`, the `v`-fibration count via
    `chebyshev_chi_count`, the Mertens sum `Σ Λ(v)/v ≤ 2L'`, and the `hLz0` absorption. -/
theorem EL_minusPrimePair_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hLz0 : Lwin x ≤ Real.exp (z0 z x)) :
    cPairSum χ z x
      ≤ 4 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
  have _ := hz8
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hL100 : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hL0 : 0 ≤ Lwin x := by linarith
  have hLpos : 0 < Lwin x := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  -- step 1: the per-summand cap, weight factored out
  have hcap : cPairSum χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
          * ∑ n ∈ cPairSet χ z x, Λ (nMinus χ n) := by
    rw [cPairSum]
    calc ∑ n ∈ cPairSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
        ≤ ∑ n ∈ cPairSet χ z x,
            Real.exp (2 * Real.log 2 * z0 z x) * (Λ (nMinus χ n) * Lwin x) :=
          Finset.sum_le_sum (fun n hn => cpair_summand_cap χ hsq hz2 hn)
      _ = Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
            * ∑ n ∈ cPairSet χ z x, Λ (nMinus χ n) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
  -- step 2: the fibration `Σ Λ(n₋) ≤ 4x·z₀·PS`
  have hfib : ∑ n ∈ cPairSet χ z x, Λ (nMinus χ n)
      ≤ 4 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2) := by
    have hmaps : ∀ n ∈ cPairSet χ z x, nMinus χ n ∈ Finset.range (2 * x + 3) := by
      intro n hn
      have hnwin : n ∈ l2cWindow χ z x := (Finset.mem_filter.mp hn).1
      have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hnwin
      have hcop : Nat.Coprime n q := l2cWindow_coprime χ hnwin
      have hnle : n ≤ 2 * x := l2cWindow_le χ hnwin
      have hvle : nMinus χ n ≤ n :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (t2_nMinus_dvd χ hsq hn0 hcop)
      rw [Finset.mem_range]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => Λ (nMinus χ n))]
    have hper : ∀ v ∈ Finset.range (2 * x + 3),
        (∑ n ∈ (cPairSet χ z x).filter (fun n => nMinus χ n = v), Λ (nMinus χ n))
          ≤ 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z * (Λ v / v) :=
      fun v _ => cpair_fiber_le χ hsq hz100 hzx v
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
    -- `Σ_v Λ(v)/v ≤ 2L'` (Mertens over `range (2x+3)`), then fold `L'/log z = z₀`
    have hmert : ∑ v ∈ Finset.range (2 * x + 3), Λ v / v ≤ 2 * Lwin x := by
      have heq : ∑ v ∈ Finset.range (2 * x + 3), Λ v / v
          = ∑ v ∈ Finset.Ioc 0 (2 * x + 2), Λ v / v := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro u hu; rw [Finset.mem_Ioc] at hu; rw [Finset.mem_range]; omega
        · intro u hu hnot
          rw [Finset.mem_range] at hu; rw [Finset.mem_Ioc] at hnot
          have hu0 : u = 0 := by omega
          subst hu0; simp
      rw [heq]
      have h3 := mertens_vonMangoldt_div_le (N := 2 * x + 2) (by omega)
      have hlogeq : Real.log ((2 * x + 2 : ℕ) : ℝ) = Lwin x := by
        rw [Lwin]; push_cast; ring_nf
      have h5 : Real.log 4 + 4 ≤ 7 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
      rw [hlogeq] at h3; linarith [hL100]
    have hc0 : 0 ≤ 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z :=
      div_nonneg (by positivity) hlogz.le
    calc 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z
            * ∑ v ∈ Finset.range (2 * x + 3), Λ v / v
        ≤ 2 * (x : ℝ) * PretenseSum χ (2 * x + 2) / Real.log z * (2 * Lwin x) :=
          mul_le_mul_of_nonneg_left hmert hc0
      _ = 4 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2) := by
          rw [z0, Lwin]; field_simp; ring
  -- assembly + `hLz0` absorption
  have hcombine : Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
        * (4 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2))
      ≤ 4 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
    have habs := cpair_exp_absorb (x := x) hz2 hLz0
    have hpre0 : 0 ≤ 4 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg x) hL0)) hPS0
    calc Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
            * (4 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2))
        = 4 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
            * (z0 z x * Real.exp (2 * Real.log 2 * z0 z x) * Lwin x ^ 2) := by
          field_simp
      _ ≤ 4 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2) * Real.exp (5 * z0 z x) :=
          mul_le_mul_of_nonneg_left habs hpre0
      _ = 4 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by ring
  calc cPairSum χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
          * ∑ n ∈ cPairSet χ z x, Λ (nMinus χ n) := hcap
    _ ≤ Real.exp (2 * Real.log 2 * z0 z x) * Lwin x
          * (4 * (x : ℝ) * z0 z x * PretenseSum χ (2 * x + 2)) :=
        mul_le_mul_of_nonneg_left hfib (mul_nonneg (Real.exp_pos _).le hL0)
    _ ≤ 4 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := hcombine

/-! ## §7 — class (a): the T2-mirror budget (M2)

The `(n+2)`-side mirror of `EL_T2`: `(n+2)₊` composite, so with `p'' := minFac((n+2)₊)`
(a `χ=+1` prime `≥ z`) and `c' := (n+2)₊/p'' ≥ z`, the `n+2`-side modulus
`d₂ := (n+2)₋·p'' = (n+2)/c' ≤ (2x+2)/z`, while `v := n₋` routes at `z^{1/4}`.  The engine
lemmas (`t2_totient_ratio`, `t2_summand_cap`, `t2_wt_sum_le`, `t2_inv_logZz_sq`,
`exp_absorption`, `sum_inv_plusprime_le_pretense`) are reused verbatim; only the modulus law,
legality, count kernel, and fibrations are mirrored. -/

/-- **The T2-mirror REPAIRED modulus law.**  For a window element with `(n+2)₊` composite:
    a `χ=+1` prime `p''` and cofactor `c' ≥ z` with `p'' ≥ z`, `c'·((n+2)₋·p'') = n+2`, and
    `((n+2)₋·p'')·z ≤ 2x+2` (the `n+2`-side modulus `d₂ := (n+2)₋·p'' = (n+2)/c' ≤ (2x+2)/z`). -/
lemma tm_modulus_law (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hn1 : 1 < nPlus χ (n + 2)) (hcomp : ¬ (nPlus χ (n + 2)).Prime) :
    ∃ p'' c' : ℕ, p'' = (nPlus χ (n + 2)).minFac ∧ p''.Prime ∧ chiRe χ p'' = 1 ∧ z ≤ p'' ∧
      z ≤ c' ∧ c' ∣ nPlus χ (n + 2) ∧ c' * (nMinus χ (n + 2) * p'') = n + 2 ∧
      (nMinus χ (n + 2) * p'') * z ≤ 2 * x + 2 := by
  have hn0 : n + 2 ≠ 0 := by omega
  have hcop : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hn
  have hfact : n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) := eq_nPlus_mul_nMinus χ hsq hn0 hcop
  have hnP0 : nPlus χ (n + 2) ≠ 0 := (nPlus_pos χ (n + 2)).ne'
  have hnP1 : nPlus χ (n + 2) ≠ 1 := by omega
  have hPdvdn : nPlus χ (n + 2) ∣ (n + 2) := ⟨nMinus χ (n + 2), hfact⟩
  set p'' := (nPlus χ (n + 2)).minFac with hp''def
  have hp''prime : p''.Prime := Nat.minFac_prime hnP1
  have hp''dvdP : p'' ∣ nPlus χ (n + 2) := Nat.minFac_dvd _
  have hp''dvdn : p'' ∣ (n + 2) := hp''dvdP.trans hPdvdn
  have hp''mem : p'' ∈ (nPlus χ (n + 2)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp''prime, hp''dvdP, hnP0⟩
  have hp''sign : chiRe χ p'' = 1 := nPlus_sign hp''mem
  have hzp'' : z ≤ p'' :=
    l2cWindow_rough_add_two χ hn hp''prime hp''dvdn (by rw [hp''sign]; norm_num)
  set c' := nPlus χ (n + 2) / p'' with hc'def
  have hpc : p'' * c' = nPlus χ (n + 2) := by rw [hc'def]; exact Nat.mul_div_cancel' hp''dvdP
  clear_value c'
  have hc2 : 2 ≤ c' := by
    by_contra hcon
    have hcc : c' = 0 ∨ c' = 1 := by omega
    rcases hcc with h0 | h1
    · rw [h0, mul_zero] at hpc; exact hnP0 hpc.symm
    · rw [h1, mul_one] at hpc; exact hcomp (hpc ▸ hp''prime)
  have hcne1 : c' ≠ 1 := by omega
  obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd hcne1
  have hcdvdP : c' ∣ nPlus χ (n + 2) := ⟨p'', by rw [mul_comm]; exact hpc.symm⟩
  have hrdvdP : r ∣ nPlus χ (n + 2) := hrc.trans hcdvdP
  have hrmem : r ∈ (nPlus χ (n + 2)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hrdvdP, hnP0⟩
  have hrsign : chiRe χ r = 1 := nPlus_sign hrmem
  have hrdvdn : r ∣ (n + 2) := hrdvdP.trans hPdvdn
  have hzr : z ≤ r := l2cWindow_rough_add_two χ hn hr hrdvdn (by rw [hrsign]; norm_num)
  have hzc : z ≤ c' := le_trans hzr (Nat.le_of_dvd (by omega) hrc)
  have hcprod : c' * (nMinus χ (n + 2) * p'') = n + 2 := by
    calc c' * (nMinus χ (n + 2) * p'') = (p'' * c') * nMinus χ (n + 2) := by ring
      _ = nPlus χ (n + 2) * nMinus χ (n + 2) := by rw [hpc]
      _ = n + 2 := hfact.symm
  refine ⟨p'', c', hp''def, hp''prime, hp''sign, hzp'', hzc, hcdvdP, hcprod, ?_⟩
  have hnle : n + 2 ≤ 2 * x + 2 := l2cWindow_add_two_le χ hn
  calc (nMinus χ (n + 2) * p'') * z ≤ (nMinus χ (n + 2) * p'') * c' :=
        Nat.mul_le_mul (le_refl _) hzc
    _ = c' * (nMinus χ (n + 2) * p'') := by ring
    _ = n + 2 := hcprod
    _ ≤ 2 * x + 2 := hnle

/-- **The T2-mirror legality at the `Zz` floor.**  With the `n+2`-side modulus law
    `d₂·z ≤ 2x+2` and the `v`-route `d₁ ≤ z^{1/4}`:
    `d₁d₂·Zz⁸·(log Zz)² ≤ z^{1/4}·d₂·z^{1/2}·(z^{1/4}/4) = d₂·z/4 ≤ (x+1)/2 ≤ 32x`. -/
lemma tm_legality {z x d₁ d₂ : ℕ} (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ x)
    (hmod : (d₂ : ℝ) * z ≤ 2 * x + 2) (hd₁4 : (d₁ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)) :
    (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2 ≤ 32 * x := by
  have hz1 : 1 ≤ z := le_trans (Nat.one_le_pow _ _ (by norm_num)) hz100
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hd₂0 : (0 : ℝ) ≤ (d₂ : ℝ) := Nat.cast_nonneg _
  have h3 : (Zz z : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := Zz_pow8_le hz1
  have h4 : (Real.log (Zz z)) ^ 2 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
    have ha := logsq_Zz_le hz100
    have hb := log_sq_le_rpow_quarter hz1
    linarith
  have hABA : (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 2) * (z : ℝ) ^ ((1 : ℝ) / 4)
      = (z : ℝ) := by
    rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos]; norm_num
  have s1 : (d₁ * d₂ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) * (d₂ : ℝ) :=
    mul_le_mul_of_nonneg_right hd₁4 hd₂0
  have s2 : (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8
      ≤ ((z : ℝ) ^ ((1 : ℝ) / 4) * (d₂ : ℝ)) * (z : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_le_mul s1 h3 (by positivity) (by positivity)
  have s3 : (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2
      ≤ ((z : ℝ) ^ ((1 : ℝ) / 4) * (d₂ : ℝ)) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * ((z : ℝ) ^ ((1 : ℝ) / 4) / 4) :=
    mul_le_mul s2 h4 (sq_nonneg _) (by positivity)
  calc (d₁ * d₂ : ℝ) * (Zz z : ℝ) ^ 8 * (Real.log (Zz z)) ^ 2
      ≤ ((z : ℝ) ^ ((1 : ℝ) / 4) * (d₂ : ℝ)) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * ((z : ℝ) ^ ((1 : ℝ) / 4) / 4) := s3
    _ = (d₂ : ℝ) * ((z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 2)
          * (z : ℝ) ^ ((1 : ℝ) / 4)) / 4 := by ring
    _ = (d₂ : ℝ) * z / 4 := by rw [hABA]
    _ ≤ (2 * (x : ℝ) + 2) / 4 := by linarith [hmod]
    _ ≤ 32 * x := by linarith [hx1]

open Classical in
/-- **The T2-mirror count kernel.**  The `Zz`-sifted pair count at a mirror-legal pair
    `(d₁, d₂)` (`d₂` big, `d₁ ≤ z^{1/4}`): `≤ 1458·(x/(d₁d₂))/(log Zz)²`. -/
lemma tm_count_kernel {z x d₁ d₂ : ℕ} (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ x)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ho1 : Odd d₁) (ho2 : Odd d₂)
    (hcop : Nat.Coprime d₁ d₂)
    (hratio : ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2 ≤ (729 / 64 : ℝ))
    (hmod : (d₂ : ℝ) * z ≤ 2 * x + 2) (hd₁4 : (d₁ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial (Zz z)) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / (d₁ * d₂)) / (Real.log (Zz z)) ^ 2 := by
  have hZz := Zz_ge_100 hz100
  have hleg := tm_legality hz100 hx1 hmod hd₁4
  have hcount := l2c_pair_count_clean (x := x) hZz hd₁ hd₂ ho1 ho2 hcop hleg
  refine le_trans hcount ?_
  have hlogZzpos : (0 : ℝ) < (Real.log (Zz z)) ^ 2 := by
    have h1 : (1 : ℝ) < (Zz z : ℝ) := by exact_mod_cast (by omega : 1 < Zz z)
    exact pow_pos (Real.log_pos h1) 2
  rw [div_le_div_iff₀ hlogZzpos hlogZzpos]
  have h128 : 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2 ≤ 1458 := by
    linarith [hratio]
  have hstep : 128 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2
        * ((x : ℝ) / (d₁ * d₂))
      ≤ 1458 * ((x : ℝ) / (d₁ * d₂)) :=
    mul_le_mul_of_nonneg_right h128 (by positivity)
  exact mul_le_mul_of_nonneg_right hstep hlogZzpos.le

open Classical in
/-- Unpack membership in the T2-mirror slice. -/
lemma TmirrorSet_mem (χ : DirichletCharacter ℂ q) {z x m : ℕ} (hm : m ∈ TmirrorSet χ z x) :
    m ∈ l2cWindow χ z x ∧ Odd m ∧ 1 < nPlus χ (m + 2) ∧ ¬ (nPlus χ (m + 2)).Prime ∧
      ¬ TmirrorJunkBlock z (nMinus χ m) := by
  classical
  exact Finset.mem_filter.mp hm

open Classical in
lemma TmirrorSet_subset_window (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    TmirrorSet χ z x ⊆ l2cWindow χ z x := Finset.filter_subset _ _

/-- The `Odd n` guard in divisibility form. -/
lemma TmirrorSet_not_two_dvd (χ : DirichletCharacter ℂ q) {z x m : ℕ}
    (hm : m ∈ TmirrorSet χ z x) : ¬ 2 ∣ m := by
  have hodd := (TmirrorSet_mem χ hm).2.1
  rw [Nat.odd_iff] at hodd; omega

/-- **The per-element T2-mirror packet.**  Every element carries the mirror modulus law. -/
lemma TmirrorSet_packet (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x m : ℕ}
    (hm : m ∈ TmirrorSet χ z x) :
    ∃ c' : ℕ, (nPlus χ (m + 2)).minFac.Prime ∧ chiRe χ ((nPlus χ (m + 2)).minFac) = 1 ∧
      z ≤ (nPlus χ (m + 2)).minFac ∧ z ≤ c' ∧ c' ∣ nPlus χ (m + 2) ∧
      c' * (nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac) = m + 2 ∧
      (nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac) * z ≤ 2 * x + 2 := by
  obtain ⟨hwin, _, hn1, hcomp, _⟩ := TmirrorSet_mem χ hm
  obtain ⟨p'', c', hpdef, hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ :=
    tm_modulus_law χ hsq hwin hn1 hcomp
  subst hpdef
  exact ⟨c', hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩

/-- `n₋ ∣ n` (for `n` coprime to `q`). -/
lemma tm_nMinus_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ} (hm0 : m ≠ 0)
    (hcop : Nat.Coprime m q) : nMinus χ m ∣ m :=
  ⟨nPlus χ m, by rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩

open Classical in
/-- **Route-A fiber subset** (mirror).  The `(v, w, p'')`-fiber (`v = n₋ ≤ z^{1/4}`) lands
    in the `Zz`-sifted base set at `(d₁, d₂) = (v, w·p'')`: the `n`-cofactor is `n₊`, the
    `n+2`-cofactor is the `≥ z` factor `c'` of the mirror modulus law. -/
lemma tm_fiberA_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (v w p'' : ℕ) :
    ((TmirrorSet χ z x).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (v, w, p'')))
      ⊆ (baseSet x v (w * p'')).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / v) * ((n + 2) / (w * p'')))) := by
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmT, hkey⟩ := hm
  rw [Prod.mk.injEq, Prod.mk.injEq] at hkey
  obtain ⟨hkv, hkw, hkp⟩ := hkey
  subst hkv; subst hkw; subst hkp
  obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hmT
  obtain ⟨c', hpp, hsign, hzp, hzc, hcdvd, hcprod, _⟩ := TmirrorSet_packet χ hsq hmT
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hvdvd : nMinus χ m ∣ m := tm_nMinus_dvd χ hsq hm0 hcopq
  have hd₂dvd : nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac ∣ m + 2 :=
    ⟨c', by rw [mul_comm]; exact hcprod.symm⟩
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, hvdvd, hd₂dvd⟩
  · have hd₂pos : 0 < nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac :=
      Nat.mul_pos (nMinus_pos χ (m + 2)) hpp.pos
    have hdiv1 : m / nMinus χ m = nPlus χ m :=
      Nat.div_eq_of_eq_mul_left (nMinus_pos χ m) (eq_nPlus_mul_nMinus χ hsq hm0 hcopq)
    have hdiv2 : (m + 2) / (nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac) = c' :=
      Nat.div_eq_of_eq_mul_left hd₂pos hcprod.symm
    rw [hdiv1, hdiv2]
    refine t2_coprime_primorial fun r hr hrdvd => ?_
    have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
    rcases hr.dvd_mul.mp hrdvd with hrP | hrc
    · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrP
      have hrm : r ∣ m := hrP.trans ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcopq⟩
      have hzr : z ≤ r := l2cWindow_rough χ hwin hr hrm (by rw [hrsign]; norm_num)
      omega
    · have hrnP : r ∣ nPlus χ (m + 2) := hrc.trans hcdvd
      have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrnP
      have hrm2 : r ∣ m + 2 :=
        hrnP.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
      have hzr : z ≤ r := l2cWindow_rough_add_two χ hwin hr hrm2 (by rw [hrsign]; norm_num)
      omega

open Classical in
/-- **The route-A fiber count** (mirror).  Under the weight-structure hypotheses on
    `(v, w)`, the `(v, w, p'')`-fiber of the modulus route (`v ≤ z^{1/4}`) has
    `≤ 1458·(x/(v·w·p''))/(log Zz)²` elements. -/
lemma tm_fiberA_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ x) {v w p'' : ℕ}
    (hv : v = 1 ∨ IsPrimePow v) (hw : w = 1 ∨ IsPrimePow w) :
    ((((TmirrorSet χ z x).filter
          (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (v, w, p''))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / ((v : ℝ) * w * p'')) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty (((TmirrorSet χ z x).filter
      (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (v, w, p'')))
    with he | ⟨n₀, hn₀⟩
  · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · rw [Finset.mem_filter] at hn₀
    obtain ⟨hn₀SA, hkey⟩ := hn₀
    rw [Finset.mem_filter] at hn₀SA
    obtain ⟨hn₀T, hrouteA⟩ := hn₀SA
    rw [Prod.mk.injEq, Prod.mk.injEq] at hkey
    obtain ⟨hkv, hkw, hkp⟩ := hkey
    subst hkv; subst hkw; subst hkp
    obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hn₀T
    have hodd' : ¬ 2 ∣ n₀ := TmirrorSet_not_two_dvd χ hn₀T
    obtain ⟨c', hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := TmirrorSet_packet χ hsq hn₀T
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq : Nat.Coprime n₀ q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n₀ + 2) q := l2cWindow_coprime_add_two χ hwin
    have hodd2 : ¬ 2 ∣ (n₀ + 2) := by omega
    have hvdvd : nMinus χ n₀ ∣ n₀ := tm_nMinus_dvd χ hsq hm0 hcopq
    have hwdvd : nMinus χ (n₀ + 2) ∣ n₀ + 2 := tm_nMinus_dvd χ hsq (by omega) hcopq2
    have hd₂dvd : nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac ∣ n₀ + 2 :=
      ⟨c', by rw [mul_comm]; exact hcprod.symm⟩
    have hp''dvd : (nPlus χ (n₀ + 2)).minFac ∣ n₀ + 2 :=
      (Nat.minFac_dvd _).trans ⟨nMinus χ (n₀ + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
    have hd₂pos : 0 < nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac :=
      Nat.mul_pos (nMinus_pos χ (n₀ + 2)) hpp.pos
    have hvpos : 0 < nMinus χ n₀ := nMinus_pos χ n₀
    have ho1 : Odd (nMinus χ n₀) := t2_odd_of_dvd hvdvd hodd'
    have ho2 : Odd (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) := t2_odd_of_dvd hd₂dvd hodd2
    have hv2 : ¬ 2 ∣ nMinus χ n₀ := fun h => hodd' (h.trans hvdvd)
    have hw2 : ¬ 2 ∣ nMinus χ (n₀ + 2) := fun h => hodd2 (h.trans hwdvd)
    have hp2 : ¬ 2 ∣ (nPlus χ (n₀ + 2)).minFac := fun h => hodd2 (h.trans hp''dvd)
    -- coprimalities: `v ⊥ p''`, `p'' ⊥ w`, `v ⊥ w`
    have hcpw : Nat.Coprime ((nPlus χ (n₀ + 2)).minFac) (nMinus χ (n₀ + 2)) := by
      refine (hpp.coprime_iff_not_dvd).mpr fun hdvd => ?_
      have hneg := nMinus_dvd_sign hpp hdvd; rw [hsign] at hneg; norm_num at hneg
    have hvw : Nat.Coprime (nMinus χ n₀) (nMinus χ (n₀ + 2)) := by
      by_contra hnc
      obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hnc
      have h1 : r ∣ n₀ := (hrg.trans (Nat.gcd_dvd_left _ _)).trans hvdvd
      have h2 : r ∣ n₀ + 2 := (hrg.trans (Nat.gcd_dvd_right _ _)).trans hwdvd
      have h3 : r ∣ 2 := by have := Nat.dvd_sub h2 h1; rwa [Nat.add_sub_cancel_left] at this
      have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
      exact hodd' (hr2 ▸ h1)
    have hvp : Nat.Coprime (nMinus χ n₀) ((nPlus χ (n₀ + 2)).minFac) := by
      by_contra hnc
      obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hnc
      have h1 : r ∣ n₀ := (hrg.trans (Nat.gcd_dvd_left _ _)).trans hvdvd
      have h2 : r ∣ n₀ + 2 := (hrg.trans (Nat.gcd_dvd_right _ _)).trans hp''dvd
      have h3 : r ∣ 2 := by have := Nat.dvd_sub h2 h1; rwa [Nat.add_sub_cancel_left] at this
      have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
      exact hodd' (hr2 ▸ h1)
    have hcop12 : Nat.Coprime (nMinus χ n₀) (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) :=
      Nat.Coprime.mul_right hvw hvp
    have hratio := t2_totient_ratio hv hw hpp hv2 hw2 hp2 hvp
      (Nat.coprime_mul_iff_left.mpr ⟨hvw, hcpw⟩)
    have hratio' : ((↑(nMinus χ n₀) * ↑(nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) : ℝ)
          / (Nat.totient (nMinus χ n₀ * (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)) : ℝ)) ^ 2
        ≤ (729 / 64 : ℝ) := by
      have he1 : (↑(nMinus χ n₀) * ↑(nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) : ℝ)
          = (nMinus χ n₀ : ℝ) * ((nPlus χ (n₀ + 2)).minFac : ℝ) * (nMinus χ (n₀ + 2) : ℝ) := by
        push_cast; ring
      have he2 : nMinus χ n₀ * (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)
          = nMinus χ n₀ * (nPlus χ (n₀ + 2)).minFac * nMinus χ (n₀ + 2) := by ring
      rw [he1, he2]; exact hratio
    have hmod : ((nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac : ℕ) : ℝ) * z ≤ 2 * x + 2 := by
      exact_mod_cast hmodz
    have hkernel := tm_count_kernel hz100 hx1 hvpos hd₂pos ho1 ho2 hcop12 hratio' hmod hrouteA
    have hsub : (((TmirrorSet χ z x).filter
          (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac)
          = (nMinus χ n₀, nMinus χ (n₀ + 2), (nPlus χ (n₀ + 2)).minFac)))
        ⊆ (baseSet x (nMinus χ n₀) (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)).filter
          (fun n => Nat.Coprime (primorial (Zz z))
            ((n / nMinus χ n₀) * ((n + 2) / (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)))) := by
      refine Finset.Subset.trans ?_ (tm_fiberA_subset χ hsq hz100 _ _ _)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    refine le_trans (le_trans (by exact_mod_cast Finset.card_le_card hsub) hkernel)
      (le_of_eq ?_)
    push_cast
    ring

open Classical in
/-- **Route-B fiber subset** (mirror).  On the cofactor route (`v > z^{1/4}`, `v` a prime
    power) the `(w, p'')`-fiber lands in the `Zz`-sifted base set at `(d₁, d₂) = (1, w·p'')`:
    the whole cofactor `n = n₊·v` is `Zz`-rough — `n₊` by roughness, `v` because the junk
    guard (+ primality at `e = 1`) pushes its base above `Zz`. -/
lemma tm_fiberB_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (w p'' : ℕ) :
    ((((TmirrorSet χ z x).filter
          (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ n))).filter
        (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (w, p'')))
      ⊆ (baseSet x 1 (w * p'')).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / (w * p'')))) := by
  intro m hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨⟨⟨hmT, hrouteB⟩, hppv⟩, hkey⟩ := hm
  rw [Prod.mk.injEq] at hkey
  obtain ⟨hkw, hkp⟩ := hkey
  subst hkw; subst hkp
  obtain ⟨hwin, _, _, _, hguard⟩ := TmirrorSet_mem χ hmT
  obtain ⟨c', hpp, hsign, hzp, hzc, hcdvd, hcprod, _⟩ := TmirrorSet_packet χ hsq hmT
  have hm0 : m ≠ 0 := l2cWindow_ne_zero χ hwin
  have hcopq : Nat.Coprime m q := l2cWindow_coprime χ hwin
  have hcopq2 : Nat.Coprime (m + 2) q := l2cWindow_coprime_add_two χ hwin
  have hd₂dvd : nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac ∣ m + 2 :=
    ⟨c', by rw [mul_comm]; exact hcprod.symm⟩
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨l2cWindow_lt χ hwin, l2cWindow_le χ hwin⟩, one_dvd _, hd₂dvd⟩
  · have hd₂pos : 0 < nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac :=
      Nat.mul_pos (nMinus_pos χ (m + 2)) hpp.pos
    have hdiv2 : (m + 2) / (nMinus χ (m + 2) * (nPlus χ (m + 2)).minFac) = c' :=
      Nat.div_eq_of_eq_mul_left hd₂pos hcprod.symm
    rw [Nat.div_one, hdiv2]
    refine t2_coprime_primorial fun r hr hrdvd => ?_
    have hZzz : Zz z < z := Zz_lt_z (le_trans (by norm_num) hz100)
    rcases hr.dvd_mul.mp hrdvd with hrm | hrc
    · have hsplit := eq_nPlus_mul_nMinus χ hsq hm0 hcopq
      have hrPv : r ∣ nPlus χ m * nMinus χ m := hsplit ▸ hrm
      rcases hr.dvd_mul.mp hrPv with hrP | hrv
      · have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrP
        have hrm' : r ∣ m := hrP.trans ⟨nMinus χ m, hsplit⟩
        have hzr : z ≤ r := l2cWindow_rough χ hwin hr hrm' (by rw [hrsign]; norm_num)
        omega
      · obtain ⟨s, k, hs, hk, hsk⟩ := (isPrimePow_nat_iff _).mp hppv
        rw [← hsk] at hrv
        have hrs : r = s := (Nat.prime_dvd_prime_iff_eq hr hs).mp (hr.dvd_of_dvd_pow hrv)
        have hs_gt : Zz z < s := by
          rcases eq_or_lt_of_le (show 1 ≤ k by omega) with hk1 | hk2
          · have hvs : nMinus χ m = s := by rw [← hsk, ← hk1, pow_one]
            have hvR : (z : ℝ) ^ ((1 : ℝ) / 4) < (nMinus χ m : ℝ) := not_le.mp hrouteB
            have hZzR : (Zz z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
              Zz_le_quarter (le_trans (by norm_num) hz100)
            have hlt : (Zz z : ℝ) < (s : ℝ) := by rw [← hvs]; exact lt_of_le_of_lt hZzR hvR
            exact_mod_cast hlt
          · rcases Nat.lt_or_ge (Zz z) s with hgt | hle
            · exact hgt
            · exact absurd ⟨s, k, hs, hle, by omega, hsk.symm, not_le.mp hrouteB⟩ hguard
        rw [hrs]; exact hs_gt
    · have hrnP : r ∣ nPlus χ (m + 2) := hrc.trans hcdvd
      have hrsign : chiRe χ r = 1 := nPlus_dvd_sign hr hrnP
      have hrm2 : r ∣ m + 2 :=
        hrnP.trans ⟨nMinus χ (m + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
      have hzr : z ≤ r := l2cWindow_rough_add_two χ hwin hr hrm2 (by rw [hrsign]; norm_num)
      omega

open Classical in
/-- **The route-B fiber count** (mirror).  Under the weight-structure hypothesis on `w`, the
    `(w, p'')`-fiber of the cofactor route has `≤ 1458·(x/(w·p''))/(log Zz)²` elements. -/
lemma tm_fiberB_card (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ x) {w p'' : ℕ} (hw : w = 1 ∨ IsPrimePow w) :
    (((((TmirrorSet χ z x).filter
          (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ n))).filter
        (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (w, p''))).card : ℝ)
      ≤ 1458 * ((x : ℝ) / ((w : ℝ) * p'')) / (Real.log (Zz z)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty ((((TmirrorSet χ z x).filter
      (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ n))).filter
      (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (w, p'')))
    with he | ⟨n₀, hn₀⟩
  · rw [he]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · simp only [Finset.mem_filter] at hn₀
    obtain ⟨⟨⟨hn₀T, _⟩, _⟩, hkey⟩ := hn₀
    rw [Prod.mk.injEq] at hkey
    obtain ⟨hkw, hkp⟩ := hkey
    subst hkw; subst hkp
    obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hn₀T
    have hodd' : ¬ 2 ∣ n₀ := TmirrorSet_not_two_dvd χ hn₀T
    obtain ⟨c', hpp, hsign, hzp, hzc, hcdvd, hcprod, hmodz⟩ := TmirrorSet_packet χ hsq hn₀T
    have hm0 : n₀ ≠ 0 := l2cWindow_ne_zero χ hwin
    have hcopq2 : Nat.Coprime (n₀ + 2) q := l2cWindow_coprime_add_two χ hwin
    have hodd2 : ¬ 2 ∣ (n₀ + 2) := by omega
    have hwdvd : nMinus χ (n₀ + 2) ∣ n₀ + 2 := tm_nMinus_dvd χ hsq (by omega) hcopq2
    have hd₂dvd : nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac ∣ n₀ + 2 :=
      ⟨c', by rw [mul_comm]; exact hcprod.symm⟩
    have hp''dvd : (nPlus χ (n₀ + 2)).minFac ∣ n₀ + 2 :=
      (Nat.minFac_dvd _).trans ⟨nMinus χ (n₀ + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩
    have hd₂pos : 0 < nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac :=
      Nat.mul_pos (nMinus_pos χ (n₀ + 2)) hpp.pos
    have ho2 : Odd (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) := t2_odd_of_dvd hd₂dvd hodd2
    have hw2 : ¬ 2 ∣ nMinus χ (n₀ + 2) := fun h => hodd2 (h.trans hwdvd)
    have hp2 : ¬ 2 ∣ (nPlus χ (n₀ + 2)).minFac := fun h => hodd2 (h.trans hp''dvd)
    have hcpw : Nat.Coprime ((nPlus χ (n₀ + 2)).minFac) (nMinus χ (n₀ + 2)) := by
      refine (hpp.coprime_iff_not_dvd).mpr fun hdvd => ?_
      have hneg := nMinus_dvd_sign hpp hdvd; rw [hsign] at hneg; norm_num at hneg
    have hratio := t2_totient_ratio hw (Or.inl rfl) hpp hw2 (by norm_num) hp2 hcpw.symm
      (Nat.coprime_one_right _)
    have hratio' : ((↑(1 : ℕ) * ↑(nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) : ℝ)
          / (Nat.totient (1 * (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)) : ℝ)) ^ 2
        ≤ (729 / 64 : ℝ) := by
      have he1 : (↑(1 : ℕ) * ↑(nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac) : ℝ)
          = (nMinus χ (n₀ + 2) : ℝ) * ((nPlus χ (n₀ + 2)).minFac : ℝ) * ((1 : ℕ) : ℝ) := by
        push_cast; ring
      have he2 : 1 * (nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac)
          = nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac * 1 := by ring
      rw [he1, he2]; exact hratio
    have hmod : ((nMinus χ (n₀ + 2) * (nPlus χ (n₀ + 2)).minFac : ℕ) : ℝ) * z ≤ 2 * x + 2 := by
      exact_mod_cast hmodz
    have hone : ((1 : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Nat.cast_one]
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
        _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num)
              (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
    have hkernel := tm_count_kernel hz100 hx1 (by omega : 0 < 1) hd₂pos odd_one ho2
      (Nat.coprime_one_left _) hratio' hmod hone
    have hsub := tm_fiberB_subset (x := x) χ hsq hz100 (nMinus χ (n₀ + 2))
      ((nPlus χ (n₀ + 2)).minFac)
    refine le_trans (le_trans (by exact_mod_cast Finset.card_le_card hsub) hkernel) (le_of_eq ?_)
    push_cast
    ring

/-- `1 ≤ x` in the master regime. -/
lemma tm_x_ge_one {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) : (1 : ℝ) ≤ x := by
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100
  calc (1 : ℝ) ≤ (z : ℝ) ^ 3 := one_le_pow₀ hz1R
    _ ≤ (x : ℝ) := hzx

open Classical in
/-- **The route-A sum** (mirror).  The modulus route (`v ≤ z^{1/4}`), fibered over
    `(v, w, p'')` and priced by Mertens × Mertens × PretenseSum: `≤ 13436928·x·z₀³·PS/L'`. -/
lemma tm_routeA_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (TmirrorSet χ z x).filter
        (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 13436928 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hx1 : (1 : ℝ) ≤ x := tm_x_ge_one hz100 hzx
  have hmaps : ∀ n ∈ (TmirrorSet χ z x).filter
      (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac)
        ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
            ×ˢ ((Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))) := by
    intro n hn
    have hnT : n ∈ TmirrorSet χ z x := Finset.mem_of_mem_filter n hn
    obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hnT
    obtain ⟨c', hpp, hsign, hzp, _, _, _, _⟩ := TmirrorSet_packet χ hsq hnT
    have hn0 : n ≠ 0 := l2cWindow_ne_zero χ hwin
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hvle : nMinus χ n ≤ n := Nat.le_of_dvd hnpos (tm_nMinus_dvd χ hsq hn0 hcopq)
    have hwle : nMinus χ (n + 2) ≤ n + 2 :=
      Nat.le_of_dvd (by omega) (tm_nMinus_dvd χ hsq (by omega) hcopq2)
    have hple : (nPlus χ (n + 2)).minFac ≤ n + 2 :=
      Nat.le_of_dvd (by omega) ((Nat.minFac_dvd _).trans
        ⟨nMinus χ (n + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, by omega, hpp, hsign, hzp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))]
  have hperk : ∀ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
      ×ˢ ((Finset.range (2 * x + 3)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))),
      (∑ n ∈ ((TmirrorSet χ z x).filter
          (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = k),
        T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
          * ((T2Wt x k.1 / k.1) * ((T2Wt x k.2.1 / k.2.1) * (1 / k.2.2))) := by
    intro k _
    obtain ⟨v, w, p''⟩ := k
    have hconst : ∀ n ∈ ((TmirrorSet χ z x).filter
        (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (v, w, p'')),
        T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) = T2Wt x v * T2Wt x w := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      rw [Prod.mk.injEq, Prod.mk.injEq] at hk
      rw [hk.1, hk.2.1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    by_cases hWv : T2Wt x v = 0
    · simp [hWv]
    by_cases hWw : T2Wt x w = 0
    · simp [hWw]
    have hv : v = 1 ∨ IsPrimePow v := by
      rcases eq_or_ne v 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWv ?_)
        rw [T2Wt, if_neg h1]; exact vonMangoldt_eq_zero_iff.mpr hnp
    have hw : w = 1 ∨ IsPrimePow w := by
      rcases eq_or_ne w 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWw ?_)
        rw [T2Wt, if_neg h1]; exact vonMangoldt_eq_zero_iff.mpr hnp
    have hcard := tm_fiberA_card (x := x) (p'' := p'') χ hsq hz100 hx1 hv hw
    have hWnn : (0 : ℝ) ≤ T2Wt x v * T2Wt x w := mul_nonneg (T2Wt_nonneg x v) (T2Wt_nonneg x w)
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * w * p'') := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hWnn
    calc (((TmirrorSet χ z x).filter
          (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => (nMinus χ n, nMinus χ (n + 2), (nPlus χ (n + 2)).minFac)
            = (v, w, p''))).card * (T2Wt x v * T2Wt x w)
        ≤ (1458 * ((x : ℝ) / ((v : ℝ) * w * p'')) / (Real.log (Zz z)) ^ 2)
            * (T2Wt x v * T2Wt x w) := mul_le_mul_of_nonneg_right hcard hWnn
      _ = (1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * w * p''))
            * (1 / (Real.log (Zz z)) ^ 2) := by ring
      _ ≤ (1458 * (x : ℝ) * (T2Wt x v * T2Wt x w) / ((v : ℝ) * w * p''))
            * (1024 * (z0 z x / Lwin x) ^ 2) := mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
            * ((T2Wt x v / v) * ((T2Wt x w / w) * (1 / p''))) := by ring
  refine le_trans (Finset.sum_le_sum hperk) ?_
  have hfact : ∑ k ∈ (Finset.range (2 * x + 1)) ×ˢ ((Finset.range (2 * x + 3))
      ×ˢ ((Finset.range (2 * x + 3)).filter
        (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p))),
      (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
        * ((T2Wt x k.1 / k.1) * ((T2Wt x k.2.1 / k.2.1) * (1 / k.2.2)))
      = (∑ v ∈ Finset.range (2 * x + 1),
          (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * ((∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
          * (∑ p ∈ (Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfact]
  have hx1N : 1 ≤ x := by exact_mod_cast hx1
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hg : ∑ v ∈ Finset.range (2 * x + 1), T2Wt x v / v ≤ 3 * Lwin x :=
    t2_wt_sum_le hz100 hzx (by omega) (by omega)
  have hh : ∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w ≤ 3 * Lwin x := by
    have := t2_wt_sum_le (N := 2 * x + 2) hz100 hzx (by omega) (by omega)
    simpa using this
  have hp : ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p
      ≤ PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
    have hps := sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1'
    have hconv : PretenseSum χ (2 * x + 2) / Real.log z
        = PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
      rw [div_eq_mul_one_div, t2_inv_log_z hz100 hzx]
    rw [← hconv]; exact hps
  have hSg0 : (0 : ℝ) ≤ ∑ v ∈ Finset.range (2 * x + 1), T2Wt x v / v :=
    Finset.sum_nonneg fun v _ => div_nonneg (T2Wt_nonneg x v) (Nat.cast_nonneg v)
  have hSh0 : (0 : ℝ) ≤ ∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w :=
    Finset.sum_nonneg fun w _ => div_nonneg (T2Wt_nonneg x w) (Nat.cast_nonneg w)
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  have hin : (∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
          (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)
      ≤ (3 * Lwin x) * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x)) :=
    mul_le_mul hh hp hSp0 (by linarith)
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 := by positivity
  have hgC : ∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x) := by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hg hC0
  calc (∑ v ∈ Finset.range (2 * x + 1),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x v / v))
        * ((∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w)
          * (∑ p ∈ (Finset.range (2 * x + 3)).filter
              (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p))
      ≤ ((1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x))
          * ((3 * Lwin x) * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x))) :=
        mul_le_mul hgC hin (mul_nonneg hSh0 hSp0) (mul_nonneg hC0 (by linarith))
    _ = 13436928 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
        field_simp; ring

open Classical in
/-- **The route-B sum** (mirror).  The cofactor route (`v > z^{1/4}`): the vanishing
    reduction to prime-power `v`, the crude `L'` cap on the `v`-weight, and the `(w, p'')`
    fibration: `≤ 4478976·x·z₀³·PS/L'`. -/
lemma tm_routeB_sum (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ∑ n ∈ (TmirrorSet χ z x).filter
        (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hx1 : (1 : ℝ) ≤ x := tm_x_ge_one hz100 hzx
  have hz14 : (1 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 4) := (Real.one_rpow _).symm
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num)
            (by exact_mod_cast le_trans (by norm_num : 1 ≤ 100 ^ 16) hz100) (by norm_num)
  have hvanish : ∀ n ∈ (TmirrorSet χ z x).filter
      (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) ≠ 0
        → IsPrimePow (nMinus χ n) := by
    intro n hn hne
    have hB : ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := (Finset.mem_filter.mp hn).2
    have hWv : T2Wt x (nMinus χ n) ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hne1 : nMinus χ n ≠ 1 := by
      rintro h1; exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    rw [T2Wt, if_neg hne1] at hWv
    by_contra hnp; exact hWv (vonMangoldt_eq_zero_iff.mpr hnp)
  rw [← Finset.sum_filter_of_ne hvanish]
  have hcapv : ∀ n ∈ ((TmirrorSet χ z x).filter
      (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ n)),
      T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
        ≤ T2Wt x (nMinus χ (n + 2)) * Lwin x := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnSB, _⟩ := hn
    have hB : ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := (Finset.mem_filter.mp hnSB).2
    have hnT : n ∈ TmirrorSet χ z x := Finset.mem_of_mem_filter n hnSB
    obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hnT
    have hcopq : Nat.Coprime n q := l2cWindow_coprime χ hwin
    have hne1 : nMinus χ n ≠ 1 := by
      rintro h1; exact hB (by rw [h1, Nat.cast_one]; exact hz14)
    have hvle : nMinus χ n ≤ 2 * x :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (l2cWindow_ne_zero χ hwin))
        (tm_nMinus_dvd χ hsq (l2cWindow_ne_zero χ hwin) hcopq)) (l2cWindow_le χ hwin)
    have hcap : T2Wt x (nMinus χ n) ≤ Lwin x := by
      rw [T2Wt, if_neg hne1]
      calc Λ (nMinus χ n) ≤ Real.log (nMinus χ n) := vonMangoldt_le_log
        _ ≤ Lwin x := by
            rw [Lwin]
            exact Real.log_le_log (by exact_mod_cast nMinus_pos χ n)
              (by exact_mod_cast (by omega : nMinus χ n ≤ 2 * x + 2))
    calc T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
        ≤ Lwin x * T2Wt x (nMinus χ (n + 2)) :=
          mul_le_mul_of_nonneg_right hcap (T2Wt_nonneg x _)
      _ = T2Wt x (nMinus χ (n + 2)) * Lwin x := by ring
  refine le_trans (Finset.sum_le_sum hcapv) ?_
  rw [← Finset.sum_mul]
  have hmaps : ∀ n ∈ ((TmirrorSet χ z x).filter
      (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
      (fun n => IsPrimePow (nMinus χ n)),
      (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac)
        ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)) := by
    intro n hn
    have hnT : n ∈ TmirrorSet χ z x :=
      Finset.mem_of_mem_filter n (Finset.mem_of_mem_filter n hn)
    obtain ⟨hwin, _, _, _, _⟩ := TmirrorSet_mem χ hnT
    obtain ⟨c', hpp, hsign, hzp, _, _, _, _⟩ := TmirrorSet_packet χ hsq hnT
    have hnle : n ≤ 2 * x := l2cWindow_le χ hwin
    have hcopq2 : Nat.Coprime (n + 2) q := l2cWindow_coprime_add_two χ hwin
    have hwle : nMinus χ (n + 2) ≤ n + 2 :=
      Nat.le_of_dvd (by omega) (tm_nMinus_dvd χ hsq (by omega) hcopq2)
    have hple : (nPlus χ (n + 2)).minFac ≤ n + 2 :=
      Nat.le_of_dvd (by omega) ((Nat.minFac_dvd _).trans
        ⟨nMinus χ (n + 2), eq_nPlus_mul_nMinus χ hsq (by omega) hcopq2⟩)
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨by omega, by omega, hpp, hsign, hzp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => T2Wt x (nMinus χ (n + 2)))]
  have hperk : ∀ k ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (∑ n ∈ (((TmirrorSet χ z x).filter
          (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ n))).filter
          (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = k),
        T2Wt x (nMinus χ (n + 2)))
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2)
          * ((T2Wt x k.1 / k.1) * (1 / k.2)) := by
    intro k _
    obtain ⟨w, p''⟩ := k
    have hconst : ∀ n ∈ (((TmirrorSet χ z x).filter
        (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
        (fun n => IsPrimePow (nMinus χ n))).filter
        (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (w, p'')),
        T2Wt x (nMinus χ (n + 2)) = T2Wt x w := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      rw [Prod.mk.injEq] at hk
      rw [hk.1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    by_cases hWw : T2Wt x w = 0
    · simp [hWw]
    have hw : w = 1 ∨ IsPrimePow w := by
      rcases eq_or_ne w 1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (by_contra fun hnp => hWw ?_)
        rw [T2Wt, if_neg h1]; exact vonMangoldt_eq_zero_iff.mpr hnp
    have hcard := tm_fiberB_card (x := x) (p'' := p'') χ hsq hz100 hx1 hw
    have hWnn : (0 : ℝ) ≤ T2Wt x w := T2Wt_nonneg x w
    have hconv := t2_inv_logZz_sq hz100 hzx
    have hfac : (0 : ℝ) ≤ 1458 * (x : ℝ) * T2Wt x w / ((w : ℝ) * p'') := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg x)) hWnn
    calc ((((TmirrorSet χ z x).filter
          (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4))).filter
          (fun n => IsPrimePow (nMinus χ n))).filter
          (fun n => (nMinus χ (n + 2), (nPlus χ (n + 2)).minFac) = (w, p''))).card * T2Wt x w
        ≤ (1458 * ((x : ℝ) / ((w : ℝ) * p'')) / (Real.log (Zz z)) ^ 2) * T2Wt x w :=
          mul_le_mul_of_nonneg_right hcard hWnn
      _ = (1458 * (x : ℝ) * T2Wt x w / ((w : ℝ) * p'')) * (1 / (Real.log (Zz z)) ^ 2) := by ring
      _ ≤ (1458 * (x : ℝ) * T2Wt x w / ((w : ℝ) * p''))
            * (1024 * (z0 z x / Lwin x) ^ 2) := mul_le_mul_of_nonneg_left hconv hfac
      _ = (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * ((T2Wt x w / w) * (1 / p'')) := by ring
  refine le_trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum hperk) (Lwin_nonneg x)) ?_
  have hfact : (∑ k ∈ (Finset.range (2 * x + 3)) ×ˢ ((Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p)),
      (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * ((T2Wt x k.1 / k.1) * (1 / k.2)))
      = (∑ w ∈ Finset.range (2 * x + 3),
          (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun w _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hfact]
  have hx1N : 1 ≤ x := by exact_mod_cast hx1
  have hz1' : 1 < z := lt_of_lt_of_le (by norm_num) hz100
  have hg : ∑ w ∈ Finset.range (2 * x + 3), T2Wt x w / w ≤ 3 * Lwin x := by
    have := t2_wt_sum_le (N := 2 * x + 2) hz100 hzx (by omega) (by omega)
    simpa using this
  have hp : ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p
      ≤ PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
    have hps := sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1'
    have hconv : PretenseSum χ (2 * x + 2) / Real.log z
        = PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x) := by
      rw [div_eq_mul_one_div, t2_inv_log_z hz100 hzx]
    rw [← hconv]; exact hps
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.range (2 * x + 3)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hL0 : Lwin x ≠ 0 := by linarith
  have hC0 : (0 : ℝ) ≤ 1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2 := by positivity
  have hgC : ∑ w ∈ Finset.range (2 * x + 3),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w)
      ≤ (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x) := by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hg hC0
  calc ((∑ w ∈ Finset.range (2 * x + 3),
        (1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (T2Wt x w / w))
        * (∑ p ∈ (Finset.range (2 * x + 3)).filter
            (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p), (1 : ℝ) / p)) * Lwin x
      ≤ (((1458 * 1024 * (x : ℝ) * (z0 z x / Lwin x) ^ 2) * (3 * Lwin x))
          * (PretenseSum χ (2 * x + 2) * (z0 z x / Lwin x))) * Lwin x := by
        refine mul_le_mul_of_nonneg_right ?_ (Lwin_nonneg x)
        exact mul_le_mul hgC hp hSp0 (mul_nonneg hC0 (by linarith))
    _ = 4478976 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
        field_simp; ring

open Classical in
/-- **`EL_TmirrorT2_bound` — the class (a) budget** (M2).  Over `TmirrorSet` (`n` odd,
    `(n+2)₊` composite, junk guard on `n₋`): `TmirrorSum ≤ 17915904·(x/L')·e^{5z₀}·PS(2x+2)`,
    `Cmirror = 17915904` absolute (the `(n+2)`-side mirror of `EL_T2_bound`). -/
theorem EL_TmirrorT2_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : (Lwin x) ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    TmirrorSum χ z x
      ≤ 17915904 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have _ := hz8
  have hL : 100 ≤ Lwin x := t2_Lwin_ge hz100 hzx
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hcap : TmirrorSum χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * ∑ n ∈ TmirrorSet χ z x,
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) := by
    rw [TmirrorSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    exact t2_summand_cap χ hsq hz2 (TmirrorSet_subset_window χ z x hn)
  have hsplit : ∑ n ∈ TmirrorSet χ z x, T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      = (∑ n ∈ (TmirrorSet χ z x).filter
            (fun n => (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)))
        + ∑ n ∈ (TmirrorSet χ z x).filter
            (fun n => ¬ (nMinus χ n : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4)),
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hmain : ∑ n ∈ TmirrorSet χ z x, T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2))
      ≤ 17915904 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x := by
    rw [hsplit]
    refine le_trans (add_le_add (tm_routeA_sum χ hsq hz100 hzx)
      (tm_routeB_sum χ hsq hz100 hzx)) (le_of_eq ?_)
    ring
  have hxL0 : (0 : ℝ) ≤ (x : ℝ) / Lwin x := div_nonneg (Nat.cast_nonneg x) (by linarith)
  calc TmirrorSum χ z x
      ≤ Real.exp (2 * Real.log 2 * z0 z x) * ∑ n ∈ TmirrorSet χ z x,
          T2Wt x (nMinus χ n) * T2Wt x (nMinus χ (n + 2)) := hcap
    _ ≤ Real.exp (2 * Real.log 2 * z0 z x)
          * (17915904 * (x : ℝ) * (z0 z x) ^ 3 * PretenseSum χ (2 * x + 2) / Lwin x) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ = 17915904 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * ((z0 z x) ^ 3 * Real.exp (2 * Real.log 2 * z0 z x)) := by ring
    _ ≤ 17915904 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * Real.exp (5 * z0 z x) := by
        refine mul_le_mul_of_nonneg_left (exp_absorption hz2) ?_
        exact mul_nonneg (mul_nonneg (by norm_num) hxL0) hPS0
    _ = 17915904 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

/-! ## §8 — the composed residual bound (M5) and the final corollary (M6) -/

/-- **`EL_uncov_bound` — the composed `E_L` odd-cover residual bound** (M5, under `hLz0`).
    Matches the amended `hEL_uncov` hypothesis of `hb_l2c_master_of_count`: `J2` at the
    re-tallied coefficient `2^26` (mirror `17915904` + class (c) `4` ≤ `2^26`), junk at `1`.
    Composes `ELodd_cover'` (a)∪(b)∪(c) with `EL_TmirrorT2_bound`, `L2cMid_bound`,
    `EL_minusPrimePair_bound`. -/
theorem EL_uncov_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hLz0 : Lwin x ≤ Real.exp (z0 z x)) :
    L2cELuncov χ z x
      ≤ 2 ^ 26 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
        + Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * Lwin x ^ 3 := by
  have hcover := ELodd_cover' (x := x) χ hsq hz100
  have ha := EL_TmirrorT2_bound χ hsq hz100 hz8 hzx
  have hb := L2cMid_bound χ hsq hz100 hz8 hzx
  have hc := EL_minusPrimePair_bound χ hsq hz100 hz8 hzx hLz0
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := t2_pretenseSum_nonneg χ _
  have hA0 : 0 ≤ (x : ℝ) / Lwin x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) :=
    mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg x) (Lwin_nonneg x))
      (Real.exp_pos _).le) hPS0
  linarith [hcover, ha, hb, hc, hA0]

open Classical in
/-- **`hb_l2c_master_final` — the L2c master, residual-closed** (M6).  The `hb_lemma2`
    conclusion shape on the exact identity, conditional on the SINGLE remaining residual
    `hcount` (the `ER_Tsw'` `CHI-SIEVE` count).  The `E_L` odd-cover residual is discharged
    by `EL_uncov_bound` under the Amendment-5 packet hypothesis `hLz0` (trivial downstream).

    SUPERSEDED as the campaign surface (A4, ratified 2026-07-20): use
    `hb_l2c_master_unconditional` (`Salt/HB/L2cMasterUncond.lean`) — same conclusion,
    bare packet, no `hLz0`/`hcount`.  Kept as a landed intermediate. -/
theorem hb_l2c_master_final (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hLz0 : Lwin x ≤ Real.exp (z0 z x))
    (hcount : ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
        Λ (nMinus χ (n + 2))
        ≤ 524288 * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2) :
    S2 χ (l2cWindow χ z x) - S1 (l2cWindow χ z x)
      ≤ L2cCmain * ((x : ℝ) / z0 z x)
        + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
            * PretenseSum χ (2 * x + 2)
        + L2cCmain * Real.exp (2 * z0 z x)
            * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3 :=
  hb_l2c_master_of_count χ hsq hz100 hz8 hzx hcount (EL_uncov_bound χ hsq hz100 hz8 hzx hLz0)

end Salt.HB
