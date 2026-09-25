/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M4 — the finite Euler product reaches `1/Π₂`

Statement frozen at salt `66fd0d0d`. -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-! ## M4 helpers — `betaT m / m` as a multiplicative arithmetic function -/

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

lemma betaT_of_not_odd {m : ℕ} (h : ¬ Odd m) : betaT m = 0 := by
  simp [betaT, h]

lemma betaT_one : betaT 1 = 1 := by
  simp [betaT]

/-- `m ↦ betaT m / m` as an arithmetic function. -/
noncomputable def betaDiv : ArithmeticFunction ℝ :=
  ⟨fun m => betaT m / m, by simp⟩

lemma betaDiv_apply (m : ℕ) : betaDiv m = betaT m / m := rfl

lemma isMultiplicative_betaDiv : betaDiv.IsMultiplicative := by
  refine ⟨by simp [betaDiv_apply, betaT_one], ?_⟩
  intro a b hab
  simp only [betaDiv_apply, Nat.cast_mul]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [betaT_mul ha hb hab, mul_div_mul_comm]
    · rw [betaT_of_not_odd hb, betaT_of_not_odd (fun h => hb (Nat.odd_mul.mp h).2)]
      simp
  · rw [betaT_of_not_odd ha, betaT_of_not_odd (fun h => ha (Nat.odd_mul.mp h).1)]
    simp

lemma sum_divisors_betaT (n : ℕ) :
    ∑ m ∈ n.divisors, betaT m / m = (betaDiv * (ζ : ArithmeticFunction ℝ)) n := by
  rw [coe_mul_zeta_apply]
  rfl

lemma betaDivZeta_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : ℕ) :
    (betaDiv * (ζ : ArithmeticFunction ℝ)) (p ^ K)
      = ∑ k ∈ Finset.range (K + 1), betaLoc k / (p : ℝ) ^ k := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [betaDiv_apply, betaT_prime_pow hp hp2, Nat.cast_pow]

/-- The truncated local factor in closed form. -/
lemma localFactor_eq {p : ℝ} (hp : 3 ≤ p) (J : ℕ) :
    ∑ k ∈ Finset.range (J + 3), betaLoc k / p ^ k
      = 1 + 1 / (p * (p - 2)) * (1 - (2 / p) ^ (J + 1)) := by
  have hp0 : p ≠ 0 := by positivity
  have hp2 : p - 2 ≠ 0 := by
    have : (0 : ℝ) < p - 2 := by linarith
    exact this.ne'
  induction J with
  | zero =>
    simp [Finset.sum_range_succ, betaLoc]
    field_simp
  | succ J ih =>
    rw [show J + 1 + 3 = (J + 3) + 1 by ring, Finset.sum_range_succ, ih]
    have hb : betaLoc (J + 3) = (2 : ℝ) ^ (J + 1) := by
      simp [betaLoc, show J + 3 - 2 = J + 1 by omega]
    rw [hb]
    have hq : (2 : ℝ) ^ (J + 1) / p ^ (J + 1 + 2) = (2 / p) ^ (J + 1) / p ^ 2 := by
      rw [div_pow]
      field_simp
      ring
    rw [show J + 3 = J + 1 + 2 by ring, hq, pow_succ (2 / p) (J + 1)]
    generalize (2 / p) ^ (J + 1) = q
    field_simp
    ring

/-- The local factor bound `F_p ≥ (1 + x_p)(1 − t)`. -/
lemma localFactor_ge {p t : ℝ} (hp : 3 ≤ p) (J : ℕ) (ht0 : 0 ≤ t)
    (ht : (2 / p) ^ (J + 1) ≤ t) :
    (1 + 1 / (p * (p - 2))) * (1 - t)
      ≤ ∑ k ∈ Finset.range (J + 3), betaLoc k / p ^ k := by
  rw [localFactor_eq hp J]
  have hx : 0 ≤ 1 / (p * (p - 2)) := by
    have : 0 ≤ p - 2 := by linarith
    positivity
  have hr : 0 ≤ (2 / p) ^ (J + 1) := by
    have : 0 ≤ 2 / p := by positivity
    positivity
  nlinarith [mul_le_mul_of_nonneg_left ht hx, mul_nonneg hx ht0]

/-- `1 + 1/(p(p−2)) = (1 − (p−1)⁻²)⁻¹`. -/
lemma one_add_x_eq {p : ℝ} (hp : 3 ≤ p) :
    1 + 1 / (p * (p - 2)) = (1 - ((p - 1) ^ 2)⁻¹)⁻¹ := by
  have hp0 : p ≠ 0 := by positivity
  have hp2 : p - 2 ≠ 0 := by
    have : (0 : ℝ) < p - 2 := by linarith
    exact this.ne'
  have hp1 : p - 1 ≠ 0 := by
    have : (0 : ℝ) < p - 1 := by linarith
    exact this.ne'
  have hne : 1 - ((p - 1) ^ 2)⁻¹ ≠ 0 := by
    have hz : (4 : ℝ) ≤ (p - 1) ^ 2 := by nlinarith
    have : ((p - 1) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
    have : (4 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  refine eq_inv_of_mul_eq_one_left ?_
  field_simp
  ring

/-! ## M4 — the finite Euler product reaches `1/Π₂` -/

/-- **M4.** -/
theorem betaSum_ge {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, Odd R ∧ (1 - η) / Pi2 ≤ ∑ m ∈ R.divisors, betaT m / m := by
  have hPi : 0 < Pi2 := pi2_pos
  rcases le_or_gt 1 η with h1 | h1
  · refine ⟨1, odd_one, ?_⟩
    have hL : (1 - η) / Pi2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hPi.le
    refine hL.trans (Finset.sum_nonneg (fun m _ => ?_))
    exact div_nonneg (betaT_nonneg m) (Nat.cast_nonneg m)
  -- choose `Q`
  obtain ⟨Q, hQ⟩ := exists_nat_gt (4 + 16 / (3 * Pi2 * η))
  have hc : 0 < 3 * Pi2 * η := by positivity
  have hQ4 : 4 ≤ Q := by
    have : (4 : ℝ) < Q := by
      have : 0 < 16 / (3 * Pi2 * η) := by positivity
      linarith
    exact_mod_cast this.le
  set d : ℝ := (Q : ℝ) - 1 with hd
  have hd0 : 0 < d := by
    have : (4 : ℝ) ≤ Q := by exact_mod_cast hQ4
    linarith
  have hQd : 8 / 3 * d⁻¹ ≤ Pi2 * η / 2 := by
    have h16 : 16 < d * (3 * Pi2 * η) := by
      have : 16 / (3 * Pi2 * η) < d := by linarith
      exact (div_lt_iff₀ hc).mp this
    rw [show 8 / 3 * d⁻¹ = (8 / 3) / d by ring, div_le_iff₀ hd0]
    nlinarith
  -- choose `J`
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < η / (2 * ((Q : ℝ) + 1)) by positivity)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  set t : ℝ := (2 / 3 : ℝ) ^ (J + 1) with ht
  have ht0 : 0 ≤ t := by positivity
  have htJ : t ≤ (2 / 3 : ℝ) ^ J :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ J)
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set S := Salt.Mertens.gt2Primes Q with hS
  have hSmem : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := fun p hp => by
    have := Salt.Mertens.mem_gt2Primes.mp hp
    exact ⟨this.2.1, by omega⟩
  set n := S.card with hn
  have hnQ : (n : ℝ) ≤ (Q : ℝ) + 1 := by
    have : n ≤ Q + 1 := by
      rw [hn, hS]
      refine (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans ?_)
      simp
    exact_mod_cast this
  have hnt : (n : ℝ) * t ≤ η / 2 := by
    have h2 : (n : ℝ) * t ≤ ((Q : ℝ) + 1) * (η / (2 * ((Q : ℝ) + 1))) := by
      apply mul_le_mul hnQ (htJ.trans hJ.le) ht0 hQ1.le
    rw [show ((Q : ℝ) + 1) * (η / (2 * ((Q : ℝ) + 1))) = η / 2 by field_simp] at h2
    exact h2
  -- the modulus
  refine ⟨∏ p ∈ S, p ^ (J + 2), ?_, ?_⟩
  · refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun p hp => ?_)
    obtain ⟨hpp, hp3⟩ := hSmem p hp
    exact (hpp.odd_of_ne_two (by omega)).pow
  -- the Euler product
  have hmul := isMultiplicative_betaDiv.mul
    (isMultiplicative_zeta.natCast (R := ℝ))
  have hcop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ (J + 2)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hSmem p hp).1 (hSmem q hq).1).mpr hpq)
  rw [sum_divisors_betaT, hmul.map_prod _ S hcop]
  have hfac : ∀ p ∈ S, (betaDiv * (ζ : ArithmeticFunction ℝ)) (p ^ (J + 2))
      = ∑ k ∈ Finset.range (J + 3), betaLoc k / (p : ℝ) ^ k := fun p hp => by
    obtain ⟨hpp, hp3⟩ := hSmem p hp
    rw [betaDivZeta_prime_pow hpp (by omega)]
  rw [Finset.prod_congr rfl hfac]
  -- local lower bounds
  have hloc : ∀ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)⁻¹ * (1 - t)
      ≤ ∑ k ∈ Finset.range (J + 3), betaLoc k / (p : ℝ) ^ k := fun p hp => by
    obtain ⟨_, hp3⟩ := hSmem p hp
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    rw [← one_add_x_eq hp3']
    refine localFactor_ge hp3' J ht0 ?_
    have h0 : (0 : ℝ) ≤ 2 / p := by positivity
    have h23 : (2 : ℝ) / p ≤ 2 / 3 := by gcongr
    exact pow_le_pow_left₀ h0 h23 (J + 1)
  have hnn : ∀ p ∈ S, 0 ≤ (1 - (((p : ℝ) - 1) ^ 2)⁻¹)⁻¹ * (1 - t) := fun p hp => by
    obtain ⟨_, hp3⟩ := hSmem p hp
    exact mul_nonneg (inv_nonneg.mpr (Salt.Mertens.factorN_pos hp3).le) (by linarith)
  refine le_trans ?_ (Finset.prod_le_prod hnn hloc)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_inv_distrib]
  set P := ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) with hP
  have hP0 : 0 < P := Finset.prod_pos (fun p hp => Salt.Mertens.factorN_pos (hSmem p hp).2)
  have hPle : P ≤ Pi2 * (1 + η / 2) := by
    have habs := Salt.Mertens.abs_prodFactor_sub_twinC2_le hQ4
    have h := (abs_sub_le_iff.mp habs).1
    have hPi2 : Pi2 = Salt.TwinBar.twinC2 := rfl
    rw [← hPi2] at h
    rw [← hd] at h
    change P - Pi2 ≤ _ at h
    nlinarith
  have hbern : 1 - η / 2 ≤ (1 - t) ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) n
    rw [show (1 : ℝ) + -t = 1 - t by ring] at this
    nlinarith
  have hstep1 : (1 - η) / Pi2 ≤ (1 - η / 2) / (Pi2 * (1 + η / 2)) := by
    rw [div_le_div_iff₀ hPi (by positivity)]
    nlinarith
  refine hstep1.trans ?_
  rw [← div_eq_inv_mul]
  exact div_le_div₀ (by positivity) hbern hP0 hPle

end Salt.HardyLittlewood.Sel
