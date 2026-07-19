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

end Salt.HB
