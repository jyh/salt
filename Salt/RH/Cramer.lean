/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.VonKochFinal

/-!
# O106 row R3 — Cramér's gap bound, weak form: `RiemannHypothesis → CramerGap 3`

The core, `cramerGap_of_vonKoch : VonKochPsi 3 → CramerGap 3`, carries NO hypothesis on ζ. If
`(p, p + h]` held no prime, `θ` would not move there, so `ψ(p + h) − ψ(p) ≤ (ψ − θ)(p + h) ≤
2 √(p+h) log(p+h)` (Mathlib's `psi_sub_theta_le`), while `VonKochPsi 3` forces
`ψ(p + h) − ψ(p) ≥ h − O(√p (log p)³)`. At `h = B √p (log p)³` with `B` large, that is a
contradiction. When `h ≥ p`, Bertrand's postulate already gives a prime in `(p, 2p]`.
Then RH enters only through R1: `cramerGap_three_of_RH`.
-/

namespace Salt.RH

open Chebyshev

/-- `θ` does not move across an interval of naturals that holds no prime. -/
theorem theta_eq_of_no_prime {a b : ℕ} (hab : a ≤ b) (h : ∀ q : ℕ, a < q → q ≤ b → ¬ q.Prime) :
    Chebyshev.theta (b : ℝ) = Chebyshev.theta (a : ℝ) := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  have : ∑ q ∈ Finset.Ioc a b, (if q.Prime then Real.log q else 0) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hq
    rw [if_neg (h q h1 h2)]
  rw [this, add_zero]

/-- The prime after `p_n` is at most any prime beyond `p_n`. -/
theorem nth_prime_succ_le {n q : ℕ} (hq : q.Prime) (hlt : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  by_contra h
  push Not at h
  have := Nat.le_nth_of_lt_nth_succ h hq
  omega

/-- **The short-interval prime**, from `VonKochPsi 3` alone. -/
theorem exists_prime_short_of_vonKoch (hV : VonKochPsi 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : ℕ, 2 ≤ p →
      ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) ≤ p + B * Real.sqrt p * Real.log p ^ 3 := by
  obtain ⟨C₀, hC₀⟩ := hV
  set C₁ : ℝ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hC : ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C₁ * Real.sqrt x * Real.log x ^ 3 := by
    intro x hx
    refine (hC₀ x hx).trans ?_
    have : 0 ≤ Real.sqrt x * Real.log x ^ 3 :=
      mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.log_nonneg (by linarith)) _)
    have := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) this
    linarith [mul_assoc C₀ (Real.sqrt x) (Real.log x ^ 3),
      mul_assoc C₁ (Real.sqrt x) (Real.log x ^ 3)]
  set B : ℝ := 12 * (2 * C₁ + 2) + 1 with hB
  refine ⟨B, by positivity, fun p hp => ?_⟩
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set L : ℝ := Real.log p with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set h : ℝ := B * Real.sqrt p * L ^ 3 with hh
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hh0 : 0 < h := by positivity
  by_cases hbig : (p : ℝ) ≤ h
  · obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul p (by omega)
    refine ⟨q, hq, hpq, ?_⟩
    have : (q : ℝ) ≤ 2 * p := by exact_mod_cast hq2
    linarith
  · push Not at hbig
    by_contra hno
    push Not at hno
    set b : ℕ := ⌊(p : ℝ) + h⌋₊ with hb
    have hpb : p ≤ b := Nat.le_floor (by linarith)
    have hnoP : ∀ q : ℕ, p < q → q ≤ b → ¬ q.Prime := by
      intro q h1 h2 hq
      have hqb : (q : ℝ) ≤ b := by exact_mod_cast h2
      have hbx : (b : ℝ) ≤ p + h := Nat.floor_le (by positivity)
      exact absurd (hno q hq h1) (not_lt.mpr (by linarith))
    have hθ := theta_eq_of_no_prime hpb hnoP
    have hψb : ψ ((p : ℝ) + h) = ψ (b : ℝ) := by
      rw [Chebyshev.psi_eq_psi_coe_floor ((p : ℝ) + h)]
    have hb1 : (1 : ℝ) ≤ b := by
      have : (2 : ℕ) ≤ b := le_trans hp hpb
      exact_mod_cast this.trans' (by norm_num)
    have hbx : (b : ℝ) ≤ p + h := Nat.floor_le (by positivity)
    -- upper bound on the increment
    have hup : ψ ((p : ℝ) + h) - ψ (p : ℝ) ≤ 2 * Real.sqrt b * Real.log b := by
      have h1 := Chebyshev.psi_sub_theta_le hb1
      have h2 := Chebyshev.theta_le_psi (p : ℝ)
      rw [hψb]; linarith
    -- lower bound on the increment
    have hx2 : (2 : ℝ) ≤ p + h := by linarith
    have hlow : (p + h) - p - (C₁ * Real.sqrt (p + h) * Real.log (p + h) ^ 3
        + C₁ * Real.sqrt p * L ^ 3) ≤ ψ ((p : ℝ) + h) - ψ (p : ℝ) := by
      have a1 := (abs_le.mp (hC _ hx2)).1
      have a2 := (abs_le.mp (hC _ hp')).2
      linarith
    -- sizes, with p + h ≤ 2p
    have h2p : (p : ℝ) + h ≤ 2 * p := by linarith
    have hl2p : Real.log (2 * p) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) hp0.ne']
      have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hp'
      linarith
    have hs2p : Real.sqrt (2 * p) ≤ 3 / 2 * Real.sqrt p := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_le_mul_of_nonneg_right this hsp.le
    have hl1 : 1 ≤ Real.log (2 * p) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9; linarith
    have hS : Real.sqrt (p + h) * Real.log (p + h) ^ 3 ≤ 12 * (Real.sqrt p * L ^ 3) := by
      have e1 : Real.sqrt (p + h) ≤ Real.sqrt (2 * p) := Real.sqrt_le_sqrt h2p
      have e2 : Real.log (p + h) ≤ Real.log (2 * p) := Real.log_le_log (by linarith) h2p
      have e2' : Real.log (p + h) ^ 3 ≤ (2 * L) ^ 3 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (e2.trans hl2p) 3
      calc Real.sqrt (p + h) * Real.log (p + h) ^ 3 ≤ (3 / 2 * Real.sqrt p) * (2 * L) ^ 3 :=
            mul_le_mul (e1.trans hs2p) e2' (pow_nonneg (Real.log_nonneg (by linarith)) 3)
              (by positivity)
        _ = 12 * (Real.sqrt p * L ^ 3) := by ring
    have hT : 2 * Real.sqrt b * Real.log b ≤ 2 * (12 * (Real.sqrt p * L ^ 3)) := by
      have e1 : Real.sqrt b ≤ Real.sqrt (2 * p) := Real.sqrt_le_sqrt (by linarith)
      have e2 : Real.log b ≤ Real.log (2 * p) := Real.log_le_log (by linarith) (by linarith)
      have e3 : Real.log (2 * p) ≤ Real.log (2 * p) ^ 3 := by
        nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) hl1 2]
      have e4 : Real.log (2 * p) ^ 3 ≤ (2 * L) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hl2p 3
      have hlb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
      calc 2 * Real.sqrt b * Real.log b ≤ 2 * (3 / 2 * Real.sqrt p) * (2 * L) ^ 3 := by
            have := mul_le_mul (e1.trans hs2p) (e2.trans (e3.trans e4)) hlb0 (by positivity)
            nlinarith
        _ = 2 * (12 * (Real.sqrt p * L ^ 3)) := by ring
    have hpL : Real.sqrt p * L ^ 3 ≤ 12 * (Real.sqrt p * L ^ 3) := by
      have : 0 ≤ Real.sqrt p * L ^ 3 := by positivity
      linarith
    have hfinal : h ≤ 12 * (2 * C₁ + 2) * (Real.sqrt p * L ^ 3) := by
      have k1 : C₁ * (Real.sqrt (p + h) * Real.log (p + h) ^ 3)
          ≤ C₁ * (12 * (Real.sqrt p * L ^ 3)) := mul_le_mul_of_nonneg_left hS hC₁0
      have k2 : C₁ * (Real.sqrt p * L ^ 3) ≤ C₁ * (12 * (Real.sqrt p * L ^ 3)) :=
        mul_le_mul_of_nonneg_left hpL hC₁0
      have : (p + h) - p = h := by ring
      nlinarith [mul_assoc C₁ (Real.sqrt (p + h)) (Real.log (p + h) ^ 3),
        mul_assoc C₁ (Real.sqrt p) (L ^ 3)]
    have hpos : 0 < Real.sqrt p * L ^ 3 := by positivity
    have : h = (12 * (2 * C₁ + 2) + 1) * (Real.sqrt p * L ^ 3) := by rw [hh, hB]; ring
    linarith

/-- **R3, the core: `VonKochPsi 3 → CramerGap 3`** (no hypothesis on `ζ`). -/
theorem cramerGap_of_vonKoch (hV : VonKochPsi 3) : CramerGap 3 := by
  obtain ⟨B, hB0, hB⟩ := exists_prime_short_of_vonKoch hV
  refine ⟨B, fun n => ?_⟩
  set p : ℕ := Nat.nth Nat.Prime n with hp
  have hpp : p.Prime := Nat.prime_nth_prime n
  obtain ⟨q, hq, hpq, hqb⟩ := hB p hpp.two_le
  have hle : Nat.nth Nat.Prime (n + 1) ≤ q := nth_prime_succ_le hq hpq
  have : ((Nat.nth Nat.Prime (n + 1) : ℕ) : ℝ) ≤ q := by exact_mod_cast hle
  linarith

/-- **R3.** Under RH, `p_{n+1} − p_n ≤ C √p_n (log p_n)³` (Cramér's bound at log power 3). -/
theorem cramerGap_three_of_RH (hRH : RiemannHypothesis) : CramerGap 3 :=
  cramerGap_of_vonKoch (vonKochPsi_three_of_RH hRH)

end Salt.RH
