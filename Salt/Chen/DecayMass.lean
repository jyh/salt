/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpStep
import Salt.Chen.AbelStep
import Salt.BrunLower.MertensWindow

/-!
# C1c⁹ — the `hh` decay-mass sum (the LAST gap of `StepHyp`)

`SharpStep.hh_reduced` factored `W` out of the `h`-part Stieltjes sum, leaving the pure
*decay-mass prime sum*

  `Σ_p (1/(p−1))·(log z/log p)·h(σ_p)`,   `σ_p = logRatio p (cdiv D' p)`.

This file discharges that sum by the **antitone dyadic-piece comparison** the C1c⁸ flag
specified, closing the `h`-comparison `hh` and hence — via `AbelStep.stepHyp_of_comparisons`
(`hf` from C1c⁸ + this `hh`) — `StepHyp` modulo only the sieve-class side conditions and the
τ-recursion.

## The route (the C1c⁸ flags spec)

The mandatory pushforward is already done (`hh_reduced`).  What remains, `decay_mass_le`:

1. **Antitone control** (`hBJS_antitone`): `h` is non-increasing on `ℝ` (`e⁻²` then `e⁻ˢ`
   then `3s⁻¹e⁻ˢ`).  With `σ_p ≥ u_p − 1` (`cdiv D' p ≥ D'/p`) and `log z/log p ≤ u_p`
   (`log z ≤ log D'`), each summand is `≤ (1/(p−1))·u_p·h(u_p−1)`, `u_p = log D'/log p`.
2. **Dyadic (unit-`u`) partition** by `k = ⌊u_p⌋₊`: on the fiber `k ≤ u_p < k+1` the summand
   is `≤ (1/(p−1))·(k+1)·h(k−1)`, and the fiber's reciprocal mass is `≤ log(k+1) + 19/log2 + 2`
   (`prime_tail_mass_le`, the real-`K` generalisation of `SharpStep.prime_support_mass_le`).
3. **The geometric close**: `Σ_k (k+1)·h(k−1)·(log(k+1)+C₀)` is bounded by
   `Σ_k C₀·(k+1)²·e^{−(k−1)} ≤ 3C₀e·Σ_k (2/e)^k = Cabs`, an explicit absolute constant
   (`h(k−1) ≤ e^{−(k−1)}`, `(k+1)² ≤ 3·2^k`, `2 < e`).
4. **Compose** (`hh_of_window`): `hh_reduced` + `decay_mass_le` + the operating-window slack
   `1 ≤ (n+3)e^{n+3}·h(S)` (`one_le_window_hBJS`) close `hh` at the explicit
   `c_h = ch_const n ε = (1+ε)·Cabs·(n+3)·e^{n+3}`.  Then `stepHyp_of_comparisons`
   (C1c⁸ `hf` + this) yields `StepHyp` modulo the sieve-class conditions + `hτrec`.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — `hBJS` antitone and the exponential shift majorant -/

/-- **`hBJS` is antitone on `ℝ`** (constant `e⁻²`, then decreasing `e⁻ˢ`, then decreasing
`3s⁻¹e⁻ˢ`).  The core monotone comparison for the dyadic pieces. -/
theorem hBJS_antitone {a b : ℝ} (hab : a ≤ b) : hBJS b ≤ hBJS a := by
  rcases le_total b 2 with hb2 | hb2
  · rw [hBJS_le2 (hab.trans hb2), hBJS_le2 hb2]
  · rcases le_total a 2 with ha2 | ha2
    · rw [hBJS_le2 ha2]; exact hBJS_le_exp2 b
    · rcases le_total a 3 with ha3 | ha3
      · rw [hBJS_mid ha2 ha3]
        rcases le_total b 3 with hb3 | hb3
        · rw [hBJS_mid hb2 hb3]; exact Real.exp_le_exp.mpr (by linarith)
        · calc hBJS b ≤ Real.exp (-b) := hBJS_le_exp_of_ge hb2
            _ ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
      · have hb3 : 3 ≤ b := le_trans ha3 hab
        rw [hBJS_ge3 ha3, hBJS_ge3 hb3]
        have ha0 : (0 : ℝ) < a := by linarith
        have hb0 : (0 : ℝ) < b := by linarith
        have hinv : b⁻¹ ≤ a⁻¹ := by
          rw [inv_le_inv₀ hb0 ha0]; exact hab
        have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
        calc 3 * b⁻¹ * Real.exp (-b) ≤ 3 * a⁻¹ * Real.exp (-a) :=
              mul_le_mul (by nlinarith [hinv]) hexp (Real.exp_pos _).le
                (mul_nonneg (by norm_num) (inv_nonneg.mpr ha0.le))

/-- **The exponential shift majorant** `h(k−1) ≤ e^{−(k−1)}` for every `k : ℕ`.  For `k ≤ 3`
the constant branch `e⁻²` is `≤ e^{−(k−1)}` (since `k−1 ≤ 2`); for `k ≥ 4` it is
`hBJS_le_exp_of_ge`. -/
theorem hBJS_shift_le_exp (k : ℕ) : hBJS ((k : ℝ) - 1) ≤ Real.exp (-((k : ℝ) - 1)) := by
  rcases le_total ((k : ℝ) - 1) 2 with h2 | h2
  · rw [hBJS_le2 h2]; exact Real.exp_le_exp.mpr (by linarith)
  · exact hBJS_le_exp_of_ge h2

/-- **The operating-window slack (product form)** `1 ≤ (n+3)·e^{n+3}·h(S)` on `S ≤ n+3`.
From `h` antitone (`h(S) ≥ h(n+3)`) and `h(n+3) = 3(n+3)⁻¹e^{−(n+3)}`. -/
theorem one_le_window_hBJS {n : ℕ} {S : ℝ} (hSn : S ≤ (n : ℝ) + 3) :
    1 ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S := by
  set m3 : ℝ := (n : ℝ) + 3 with hm3
  have hn3 : (3 : ℝ) ≤ m3 := by
    rw [hm3]; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hge : hBJS m3 ≤ hBJS S := hBJS_antitone hSn
  rw [hBJS_ge3 hn3] at hge
  have hn3pos : (0 : ℝ) < m3 := by linarith
  set E : ℝ := Real.exp m3 with hE
  have hkey : m3 * E * (3 * m3⁻¹ * Real.exp (-m3)) = 3 := by
    rw [hE, show Real.exp (-m3) = (Real.exp m3)⁻¹ by rw [← Real.exp_neg]]
    field_simp
  calc (1 : ℝ) ≤ 3 := by norm_num
    _ = m3 * E * (3 * m3⁻¹ * Real.exp (-m3)) := hkey.symm
    _ ≤ m3 * E * hBJS S := mul_le_mul_of_nonneg_left hge (by positivity)

/-! ## Part B — the elementary polynomial/geometric tail tools -/

/-- `2k+3 ≤ 3·2^k` (the inductive workhorse for `poly_two_pow_le`). -/
theorem two_mul_add_three_le (k : ℕ) : 2 * (k : ℝ) + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    push_cast
    calc 2 * ((m : ℝ) + 1) + 3 = (2 * (m : ℝ) + 3) + 2 := by ring
      _ ≤ 3 * 2 ^ m + 2 := by linarith
      _ ≤ 3 * 2 ^ (m + 1) := by rw [pow_succ]; nlinarith [h2]

/-- **`(k+1)² ≤ 3·2^k`** for every `k : ℕ` (the polynomial-vs-geometric bound making the
dyadic tail summable at ratio `2/e < 1`). -/
theorem poly_two_pow_le (k : ℕ) : ((k : ℝ) + 1) ^ 2 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have haux := two_mul_add_three_le m
    push_cast
    calc ((m : ℝ) + 1 + 1) ^ 2 = ((m : ℝ) + 1) ^ 2 + (2 * (m : ℝ) + 3) := by ring
      _ ≤ 3 * 2 ^ m + 3 * 2 ^ m := by linarith
      _ = 3 * 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- `2 < e`. -/
theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9; linarith

/-! ## Part C — the real-`K` prime tail mass bound (the dyadic piece mass) -/

/-- **The prime tail mass bound** (real-`K` generalisation of
`SharpStep.prime_support_mass_le`).  For a finite set `T` of primes `p < D'` with
`log D' < K·log p` (i.e. `p > D'^{1/K}`), `Σ_{p∈T} 1/(p−1) ≤ log K + 19/log2 + 2`, **uniform
in `D'`**: the tail's loglog-length is `log K` whatever `D'`.  Applied per dyadic piece with
`K = k+1`.  (Same two-regime PM1 + `1/(p−1)`-bridge + `Σ1/p²` telescope as the `n+3` version.) -/
theorem prime_tail_mass_le (D' : ℕ) (K : ℝ) (hK : 1 ≤ K) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ (p : ℝ) < D' ∧ Real.log D' < K * Real.log p) :
    ∑ p ∈ T, 1 / ((p : ℝ) - 1) ≤ Real.log K + 19 / Real.log 2 + 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn3pos : (0 : ℝ) < K := by linarith
  have hlogn3 : (0 : ℝ) ≤ Real.log K := Real.log_nonneg hK
  -- (1) the PM1 loglog bound  Σ 1/p ≤ log K + 19/log 2
  have hLn : ∑ p ∈ T, (1 : ℝ) / p ≤ Real.log K + 19 / Real.log 2 := by
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · rw [hTe, Finset.sum_empty]; positivity
    · obtain ⟨p0, hp0⟩ := hTne
      obtain ⟨hp0p, hp0D, _⟩ := hT p0 hp0
      have hp02R : (2 : ℝ) ≤ (p0 : ℝ) := by exact_mod_cast hp0p.two_le
      have hD3R : (3 : ℝ) ≤ (D' : ℝ) := by
        have hD2 : 2 < D' := by exact_mod_cast (lt_of_le_of_lt hp02R hp0D)
        have : 3 ≤ D' := hD2
        exact_mod_cast this
      have hlogD : 0 < Real.log D' := Real.log_pos (by linarith)
      set L := Real.log D' with hLdef
      by_cases hcase : K * Real.log 2 ≤ L
      · -- large-D' regime: base w = exp(L/K) ≥ 2
        set w := Real.exp (L / K) with hwdef
        have hwpos : 0 < w := Real.exp_pos _
        have hlogw : Real.log w = L / K := by rw [hwdef, Real.log_exp]
        have hwlog2 : Real.log 2 ≤ Real.log w := by
          rw [hlogw, le_div_iff₀ hn3pos]; linarith [hcase]
        have hw2 : (2 : ℝ) ≤ w := by
          have h := Real.exp_le_exp.mpr hwlog2
          rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hwpos] at h
        have hwD : w ≤ (D' : ℝ) := by
          have h1 : L / K ≤ L := by rw [div_le_iff₀ hn3pos]; nlinarith [hlogD, hK]
          have h := Real.exp_le_exp.mpr h1
          rw [hLdef] at h
          rwa [Real.exp_log (show (0 : ℝ) < (D' : ℝ) by linarith)] at h
        have hpm := Salt.BrunLower.sum_inv_le_of_prime_window (w := w) (z := (D' : ℝ)) hw2 hwD
          (S := T) (fun p hp => by
            obtain ⟨hpp, hpD, hplog⟩ := hT p hp
            have hppos : (0 : ℝ) < (p : ℝ) := by
              have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
              linarith
            refine ⟨hpp, ?_, hpD⟩
            have hlp : L / K < Real.log p := by
              rw [div_lt_iff₀ hn3pos]; linarith [hplog]
            have h := Real.exp_le_exp.mpr hlp.le
            rwa [Real.exp_log hppos] at h)
        have hratio : L / Real.log w = K := by
          rw [hlogw, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (ne_of_gt hlogD),
            mul_one]
        have hlogratio : Real.log (L / Real.log w) = Real.log K := by rw [hratio]
        have h19 : 19 / Real.log w ≤ 19 / Real.log 2 :=
          div_le_div_of_nonneg_left (by norm_num) hlog2 hwlog2
        calc ∑ p ∈ T, (1 : ℝ) / p ≤ Real.log (L / Real.log w) + 19 / Real.log w := hpm
          _ ≤ Real.log K + 19 / Real.log 2 := by rw [hlogratio]; linarith [h19]
      · -- small-D' regime: base w = 2
        replace hcase : L < K * Real.log 2 := not_le.mp hcase
        have hpm := Salt.BrunLower.sum_inv_le_of_prime_window (w := 2) (z := (D' : ℝ)) le_rfl
          (by linarith) (S := T) (fun p hp => by
            obtain ⟨hpp, hpD, _⟩ := hT p hp
            exact ⟨hpp, by exact_mod_cast hpp.two_le, hpD⟩)
        have hlt : L / Real.log 2 < K := by rw [div_lt_iff₀ hlog2]; linarith [hcase]
        have hlogle : Real.log (L / Real.log 2) ≤ Real.log K :=
          Real.log_le_log (by positivity) hlt.le
        calc ∑ p ∈ T, (1 : ℝ) / p
            ≤ Real.log (Real.log D' / Real.log 2) + 19 / Real.log 2 := hpm
          _ ≤ Real.log K + 19 / Real.log 2 := by rw [← hLdef]; linarith [hlogle]
  -- (2) the 1/(p−1) bridge and the Σ 1/p² telescope
  have hbridge : ∀ p ∈ T, 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 2 / (p : ℝ) ^ 2 := by
    intro p hp
    obtain ⟨hpp, _, _⟩ := hT p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_add_div _ _ (ne_of_gt hp0) (by positivity : ((p : ℝ) ^ 2) ≠ 0),
      div_le_div_iff₀ hp1 (by positivity)]
    nlinarith [mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
  have hsub : T ⊆ Finset.Icc 2 D' := by
    intro p hp
    obtain ⟨hpp, hpD, _⟩ := hT p hp
    rw [Finset.mem_Icc]
    have : p < D' := by exact_mod_cast hpD
    exact ⟨hpp.two_le, by omega⟩
  have htail : ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) ≤ 2 := by
    have h1 : ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) = 2 * ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    have h2 : ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ ∑ p ∈ Finset.Icc 2 D', 1 / ((p : ℝ) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have h3 := Salt.BrunLower.sum_one_div_sq_le (M := 2) (K := D') (by norm_num)
    have hle1 : ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ 1 :=
      le_trans h2 (le_trans h3 (by norm_num))
    rw [h1]; linarith [hle1]
  calc ∑ p ∈ T, 1 / ((p : ℝ) - 1)
      ≤ ∑ p ∈ T, (1 / (p : ℝ) + 2 / (p : ℝ) ^ 2) := Finset.sum_le_sum hbridge
    _ = (∑ p ∈ T, 1 / (p : ℝ)) + ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) := Finset.sum_add_distrib
    _ ≤ (Real.log K + 19 / Real.log 2) + 2 := by linarith [hLn, htail]
    _ = Real.log K + 19 / Real.log 2 + 2 := by ring

/-- **The geometric tail** `Σ_{k<N} (2/e)^k ≤ e/(e−2)` (ratio `2/e < 1`). -/
theorem geom_two_over_e_le (N : ℕ) :
    ∑ k ∈ Finset.range N, ((2 : ℝ) / Real.exp 1) ^ k ≤ Real.exp 1 / (Real.exp 1 - 2) := by
  have he := two_lt_exp_one
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) / Real.exp 1 := by positivity
  have hr1 : (2 : ℝ) / Real.exp 1 < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hrne : (2 : ℝ) / Real.exp 1 ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hrne N]
  have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have he2 : Real.exp 1 - 2 ≠ 0 := by linarith
  have hden : (2 : ℝ) / Real.exp 1 - 1 < 0 := by linarith
  have hpow0 : (0 : ℝ) ≤ ((2 : ℝ) / Real.exp 1) ^ N := by positivity
  rw [div_le_iff_of_neg hden]
  have hEq : Real.exp 1 / (Real.exp 1 - 2) * ((2 : ℝ) / Real.exp 1 - 1) = -1 := by
    field_simp
    ring
  rw [hEq]; linarith

/-- `2^j·e^{−(j−1)} = e·(2/e)^j` (the dyadic-term-to-geometric rewrite). -/
theorem two_pow_exp_eq (j : ℕ) :
    (2 : ℝ) ^ j * Real.exp (-((j : ℝ) - 1)) = Real.exp 1 * ((2 : ℝ) / Real.exp 1) ^ j := by
  have hexpj : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by rw [← Real.exp_nat_mul]; norm_num
  have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  rw [neg_sub, Real.exp_sub, hexpj, div_pow]
  field_simp

/-! ## Part D — the decay-mass sum bound (the antitone dyadic-piece close) -/

/-- The explicit absolute constant closing the decay-mass sum: `Cabs = 3C₀e·(e/(e−2))`,
`C₀ = 19/log2 + 2` (the geometric total of `Σ_k C₀(k+1)²e^{−(k−1)}`). -/
noncomputable def Cabs : ℝ :=
  3 * (19 / Real.log 2 + 2) * Real.exp 1 * (Real.exp 1 / (Real.exp 1 - 2))

/-- **The decay-mass sum bound** (the isolated `h`-remainder of `hh`, closed).  For primes
`p < D'` with `0 < log z ≤ log D'`, the pure decay-mass prime sum is bounded by the absolute
constant `Cabs`, uniformly in `z, D'`.  Route: dyadic partition by `k = ⌊log D'/log p⌋₊`,
antitone `h(σ_p) ≤ h(k−1)` and `log z/log p ≤ k+1` per piece, `prime_tail_mass_le` for the
piece mass, `h(k−1) ≤ e^{−(k−1)}` and `(k+1)² ≤ 3·2^k` for the geometric close. -/
theorem decay_mass_le (z D' : ℕ) (T : Finset ℕ) (hD : 1 ≤ D')
    (hlogz : 0 < Real.log z) (hzD : Real.log z ≤ Real.log D')
    (hT : ∀ p ∈ T, p.Prime ∧ (p : ℝ) < D') :
    ∑ p ∈ T, 1 / ((p : ℝ) - 1) * (Real.log z / Real.log p) * hBJS (logRatio p (cdiv D' p))
      ≤ Cabs := by
  classical
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set C₀ : ℝ := 19 / Real.log 2 + 2 with hC₀
  have hC₀1 : (1 : ℝ) ≤ C₀ := by
    rw [hC₀]
    have h19 : (0 : ℝ) < 19 / Real.log 2 := by positivity
    linarith
  have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith
  set f : ℕ → ℝ := fun p =>
    1 / ((p : ℝ) - 1) * (Real.log z / Real.log p) * hBJS (logRatio p (cdiv D' p)) with hf
  set φ : ℕ → ℕ := fun p => ⌊Real.log D' / Real.log p⌋₊ with hφ
  set Kmax : ℕ := ⌊Real.log D' / Real.log 2⌋₊ with hKmax
  -- the fiber index maps into range (Kmax+1)
  have hmaps : ∀ p ∈ T, φ p ∈ Finset.range (Kmax + 1) := by
    intro p hp
    obtain ⟨hpp, hpD⟩ := hT p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hle : Real.log D' / Real.log p ≤ Real.log D' / Real.log 2 := by
      have hlp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
      exact div_le_div_of_nonneg_left hlogD.le hlog2 hlp2
    rw [Finset.mem_range]
    have hfl : ⌊Real.log D' / Real.log p⌋₊ ≤ ⌊Real.log D' / Real.log 2⌋₊ := Nat.floor_le_floor hle
    simp only [hφ, hKmax]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  -- per-fiber bound
  have hfiber : ∀ j ∈ Finset.range (Kmax + 1),
      ∑ p ∈ T.filter (fun p => φ p = j), f p
        ≤ C₀ * ((j : ℝ) + 1) ^ 2 * Real.exp (-((j : ℝ) - 1)) := by
    intro j _
    set A : ℝ := (j : ℝ) + 1 with hA
    have hA1 : (1 : ℝ) ≤ A := by rw [hA]; have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have hHE : hBJS ((j : ℝ) - 1) ≤ Real.exp (-((j : ℝ) - 1)) := hBJS_shift_le_exp j
    have hE0 : (0 : ℝ) ≤ Real.exp (-((j : ℝ) - 1)) := (Real.exp_pos _).le
    have hH0 : (0 : ℝ) ≤ hBJS ((j : ℝ) - 1) := (hBJS_pos _).le
    -- per-term bound on the fiber
    have hterm : ∀ p ∈ T.filter (fun p => φ p = j),
        f p ≤ 1 / ((p : ℝ) - 1) * (A * hBJS ((j : ℝ) - 1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpT, hpj⟩ := hp
      simp only [hφ] at hpj
      obtain ⟨hpp, hpD⟩ := hT p hpT
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      -- fiber bounds: j ≤ u_p < j+1
      have hu0 : (0 : ℝ) ≤ Real.log D' / Real.log p := by positivity
      have hjle : (j : ℝ) ≤ Real.log D' / Real.log p := by
        have h := Nat.floor_le hu0; rw [hpj] at h; exact_mod_cast h
      have hltj : Real.log D' / Real.log p < (j : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one (Real.log D' / Real.log p); rw [hpj] at h; exact_mod_cast h
      -- (log z / log p) ≤ A
      have hlz : Real.log z / Real.log p ≤ A := by
        rw [hA]
        calc Real.log z / Real.log p ≤ Real.log D' / Real.log p := by gcongr
          _ ≤ (j : ℝ) + 1 := hltj.le
      have hlz0 : (0 : ℝ) ≤ Real.log z / Real.log p := by positivity
      -- σ_p ≥ u_p - 1 ≥ j - 1
      have hcdiv1 : (1 : ℝ) ≤ (cdiv D' p : ℝ) := by exact_mod_cast one_le_cdiv D' p
      have hp1n : 1 ≤ p := hpp.one_le
      have hDlemul : (D' : ℝ) ≤ (p : ℝ) * (cdiv D' p : ℝ) := by
        have h := (mul_lt_iff_lt_cdiv hp1n hD (cdiv D' p)).not.mpr (lt_irrefl (cdiv D' p))
        have : D' ≤ p * cdiv D' p := Nat.not_lt.mp h
        exact_mod_cast this
      have hcdivpos : (0 : ℝ) < (cdiv D' p : ℝ) := by linarith
      have hlogcdiv : Real.log D' - Real.log p ≤ Real.log (cdiv D' p) := by
        have hle : (D' : ℝ) / p ≤ (cdiv D' p : ℝ) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ))]; linarith [hDlemul]
        have := Real.log_le_log (by positivity) hle
        rwa [Real.log_div (by positivity) (by positivity)] at this
      have hσ : (j : ℝ) - 1 ≤ logRatio p (cdiv D' p) := by
        rw [logRatio, le_div_iff₀ hlogp]
        have hjlp : (j : ℝ) * Real.log p ≤ Real.log D' := (le_div_iff₀ hlogp).mp hjle
        have hexp : ((j : ℝ) - 1) * Real.log p = (j : ℝ) * Real.log p - Real.log p := by ring
        rw [hexp]; linarith [hjlp, hlogcdiv]
      have hBJSle : hBJS (logRatio p (cdiv D' p)) ≤ hBJS ((j : ℝ) - 1) := hBJS_antitone hσ
      -- assemble the per-term bound
      have hinv0 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
      calc f p
          = 1 / ((p : ℝ) - 1) * ((Real.log z / Real.log p) * hBJS (logRatio p (cdiv D' p))) := by
            simp only [hf]; ring
        _ ≤ 1 / ((p : ℝ) - 1) * (A * hBJS ((j : ℝ) - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hinv0
            exact mul_le_mul hlz hBJSle (hBJS_pos _).le hA0
    -- mass of the fiber via prime_tail_mass_le at K = j+1
    have hmass : ∑ p ∈ T.filter (fun p => φ p = j), 1 / ((p : ℝ) - 1) ≤ Real.log A + C₀ := by
      have := prime_tail_mass_le D' A hA1 (T.filter (fun p => φ p = j)) (fun p hp => by
        rw [Finset.mem_filter] at hp
        obtain ⟨hpT, hpj⟩ := hp
        simp only [hφ] at hpj
        obtain ⟨hpp, hpD⟩ := hT p hpT
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
        refine ⟨hpp, hpD, ?_⟩
        have hltj : Real.log D' / Real.log p < (j : ℝ) + 1 := by
          have h := Nat.lt_floor_add_one (Real.log D' / Real.log p)
          rw [hpj] at h; exact_mod_cast h
        rw [hA]; exact (div_lt_iff₀ hlogp).mp hltj)
      rw [hC₀]; linarith [this]
    -- combine: fiber sum ≤ (A·h(j−1))·mass ≤ C₀·A²·e^{−(j−1)}
    have hAH0 : (0 : ℝ) ≤ A * hBJS ((j : ℝ) - 1) := mul_nonneg hA0 hH0
    have hlogA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hMle : Real.log A + C₀ ≤ C₀ * A := by
      nlinarith [hlogA, mul_nonneg (by linarith : (0 : ℝ) ≤ A - 1) (by linarith : (0 : ℝ) ≤ C₀ - 1)]
    calc ∑ p ∈ T.filter (fun p => φ p = j), f p
        ≤ ∑ p ∈ T.filter (fun p => φ p = j), 1 / ((p : ℝ) - 1) * (A * hBJS ((j : ℝ) - 1)) :=
          Finset.sum_le_sum hterm
      _ = (A * hBJS ((j : ℝ) - 1)) * ∑ p ∈ T.filter (fun p => φ p = j), 1 / ((p : ℝ) - 1) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ (A * hBJS ((j : ℝ) - 1)) * (Real.log A + C₀) :=
          mul_le_mul_of_nonneg_left hmass hAH0
      _ ≤ (A * Real.exp (-((j : ℝ) - 1))) * (C₀ * A) := by
          apply mul_le_mul _ hMle (by linarith [Real.log_nonneg hA1]) (by positivity)
          exact mul_le_mul_of_nonneg_left hHE hA0
      _ = C₀ * A ^ 2 * Real.exp (-((j : ℝ) - 1)) := by ring
  -- sum the per-fiber bounds; geometric close
  calc ∑ j ∈ Finset.range (Kmax + 1), ∑ p ∈ T.filter (fun p => φ p = j), f p
      ≤ ∑ j ∈ Finset.range (Kmax + 1), C₀ * ((j : ℝ) + 1) ^ 2 * Real.exp (-((j : ℝ) - 1)) :=
        Finset.sum_le_sum hfiber
    _ ≤ ∑ j ∈ Finset.range (Kmax + 1), C₀ * (3 * Real.exp 1) * ((2 : ℝ) / Real.exp 1) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        have hpoly := poly_two_pow_le j
        have hE0 : (0 : ℝ) ≤ Real.exp (-((j : ℝ) - 1)) := (Real.exp_pos _).le
        calc C₀ * ((j : ℝ) + 1) ^ 2 * Real.exp (-((j : ℝ) - 1))
            = C₀ * (((j : ℝ) + 1) ^ 2 * Real.exp (-((j : ℝ) - 1))) := by ring
          _ ≤ C₀ * (3 * 2 ^ j * Real.exp (-((j : ℝ) - 1))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly hE0) hC₀0
          _ = C₀ * (3 * Real.exp 1) * ((2 : ℝ) / Real.exp 1) ^ j := by
              rw [show (3 : ℝ) * 2 ^ j * Real.exp (-((j : ℝ) - 1))
                    = 3 * ((2 : ℝ) ^ j * Real.exp (-((j : ℝ) - 1))) by ring, two_pow_exp_eq j]; ring
    _ = C₀ * (3 * Real.exp 1) * ∑ j ∈ Finset.range (Kmax + 1), ((2 : ℝ) / Real.exp 1) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ C₀ * (3 * Real.exp 1) * (Real.exp 1 / (Real.exp 1 - 2)) :=
        mul_le_mul_of_nonneg_left (geom_two_over_e_le (Kmax + 1))
          (by positivity)
    _ = Cabs := by unfold Cabs; rw [hC₀]; ring

/-- `0 ≤ Cabs`. -/
theorem Cabs_nonneg : (0 : ℝ) ≤ Cabs := by
  have he := two_lt_exp_one
  unfold Cabs
  have h1 : (0 : ℝ) ≤ 3 * (19 / Real.log 2 + 2) * Real.exp 1 := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp 1 / (Real.exp 1 - 2) := div_nonneg (Real.exp_pos 1).le (by linarith)
  exact mul_nonneg h1 h2

/-! ## Part E — the assembled `h`-comparison `hh` (the explicit `c_h`) -/

/-- The explicit `h`-coefficient `c_h(n, ε)` (any per-`n` value closes the τ-recursion, per
AbelStep's `ledger_collect`).  Collects the `(1+ε)` (hyp (4)), the absolute decay-mass constant
`Cabs`, and the operating-window slack `(n+3)·e^{n+3}` (`one_le_window_hBJS`). -/
noncomputable def ch_const (n : ℕ) (ε : ℝ) : ℝ :=
  (1 + ε) * Cabs * ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3)

/-- **The sharp `h`-comparison `hh`** (BJS (32)–(34), assembled), conditional on the same
sieve-class inputs as `SharpStep.hf_of_window`: the density bound `ν q ≤ 1/(q−1)`, the catch-#22
threshold guard at each sifting prime, and the operating window `1 ≤ σ z D' ≤ n+3`.  With the
explicit `c_h = ch_const n ε`,

  `Σ_{p ∈ window} ν(p)·V(p)·h(σ_p) ≤ W·(c_h·h(σ_z))`,   `σ = logRatio`.

Route: `hh_reduced` factors `W` out (hyp (4)); `decay_mass_le` bounds the remaining decay-mass
prime sum by the absolute constant `Cabs`; and `one_le_window_hBJS` supplies the `s`-uniform
`1 ≤ (n+3)e^{n+3}·h(S)` slack. -/
theorem hh_of_window (s' : BoundingSieve) (ε : ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (_hn : 1 ≤ n) (hD : 1 ≤ D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSn : logRatio z D' ≤ (n : ℝ) + 3) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s' * (ch_const n ε * hBJS (logRatio z D')) := by
  have hW := Salt.BrunLower.W_pos s'
  set S := logRatio z D' with hSdef
  -- log positivity from the operating window
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rcases (Nat.cast_nonneg z : (0 : ℝ) ≤ (z : ℝ)).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, Real.log_zero] at hlogz; exact lt_irrefl 0 hlogz
  have hDpos : (0 : ℝ) < (D' : ℝ) := by exact_mod_cast hD
  have hzleD : (z : ℝ) ≤ (D' : ℝ) := by
    have := Real.exp_le_exp.mpr hzD
    rwa [Real.exp_log hzpos, Real.exp_log hDpos] at this
  -- the window primes are `< D'`
  have hT : ∀ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
      p.Prime ∧ (p : ℝ) < D' := by
    intro p hp
    have hpf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    refine ⟨Nat.prime_of_mem_primeFactors hpf, ?_⟩
    have : (p : ℝ) < (z : ℝ) := by exact_mod_cast hz p hpf
    linarith [hzleD]
  have hCabs0 : (0 : ℝ) ≤ Cabs := Cabs_nonneg
  have hcoef0 : (0 : ℝ) ≤ (1 + ε) * Salt.BrunLower.W s' := mul_nonneg (by linarith) hW.le
  have hone : (1 : ℝ) ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S :=
    one_le_window_hBJS hSn
  calc (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
      ≤ (1 + ε) * Salt.BrunLower.W s'
          * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p)) :=
        hh_reduced s' ε z side' D' hε hz hguard hnu
    _ ≤ (1 + ε) * Salt.BrunLower.W s' * Cabs :=
        mul_le_mul_of_nonneg_left
          (decay_mass_le z D' _ hD hlogz hzD hT) hcoef0
    _ ≤ Salt.BrunLower.W s' * (ch_const n ε * hBJS S) := by
        have hbase : (0 : ℝ) ≤ (1 + ε) * Salt.BrunLower.W s' * Cabs :=
          mul_nonneg hcoef0 hCabs0
        have hstep : (1 + ε) * Salt.BrunLower.W s' * Cabs
            ≤ (1 + ε) * Salt.BrunLower.W s' * Cabs
                * (((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S) := by
          nlinarith [mul_nonneg hbase (sub_nonneg.mpr hone)]
        calc (1 + ε) * Salt.BrunLower.W s' * Cabs
            ≤ (1 + ε) * Salt.BrunLower.W s' * Cabs
                * (((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S) := hstep
          _ = Salt.BrunLower.W s' * (ch_const n ε * hBJS S) := by unfold ch_const; ring

/-! ## Part F — the pointwise `StepHyp` closure (both comparisons composed at one operating point)

The two sharp Stieltjes comparisons `hf_of_window` (C1c⁸) and `hh_of_window` (this file) now
compose, via `AbelStep.stepHyp_lhs_eq` + `AbelStep.ledger_collect`, to the *per-instance*
`StepHyp` inequality — BJS's (34)–(38) peel bound at a single operating point — under the
sieve-class side conditions BJS Theorem 6 already carries plus the τ-recursion in the closing
direction.  This is the analytic keystone realised: for every operating-window `(z, D', n)` the
`p`-sum is bounded by the parent `fseqBound'`, fully machine-checked.

**Why the full `StepHyp` (`AbelStep.StepHyp`, a bare `∀`) is not landed here.**
`AbelStep.stepHyp_of_comparisons` reduces `StepHyp` to `hf`/`hh` *slots whose only hypotheses
are* `side' ∈ {1,2}`, `1 ≤ D'`, `1 ≤ n`, `∀ q ∈ primeFactors, q < z` — they carry **no**
`hguard`/`hnu` (the catch-#22 threshold + density bound) and **no** operating window
`1 ≤ logRatio z D' ≤ n+3`.  Our `hf_of_window`/`hh_of_window` genuinely need all four.  So the
window lemmas cannot fill those bare slots, and `StepHyp`'s bare `∀ s' z D' n` even ranges over
`(z, D', n)` *outside* the operating window (where the comparisons are simply false as stated).
Closing the full `StepHyp` therefore needs a *windowed* `StepHyp` contract (the sieve-class
conditions + operating window threaded as ambient hypotheses of the whole BJS Theorem-6 chain) —
a design/threading change to the `StepHyp`/`stepHyp_of_comparisons` interface, above this node's
tier.  See `docs/blueprints/flags.md`. -/

/-- **The pointwise `StepHyp` inequality** (both comparisons composed).  For a single operating
point `(s', z, side', D', n)` inside the operating window and satisfying the sieve-class
conditions, with the τ-recursion `hτrec` at `(cf_const n ε, ch_const n ε)`, the BJS (34)–(38)
peel bound holds: `Σ_p ν(p)·fseqBound'(sub-sieve) ≤ fseqBound'(parent)`.  This is
`AbelStep.stepHyp_of_comparisons`'s body with the *conditional* window comparisons plugged in. -/
theorem stepHyp_pointwise (s' : BoundingSieve) (ε : ℝ) (tau : ℕ → ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (hn : 1 ≤ n) (hD : 1 ≤ D') (hτ0 : 0 ≤ tau n) (_hside : side' = 1 ∨ side' = 2)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSn : logRatio z D' ≤ (n : ℝ) + 3)
    (hτrec : cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1)) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' logRatio ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' logRatio ε tau s' z side' D' (n + 1) := by
  rw [stepHyp_lhs_eq logRatio ε tau s' side' D' n]
  simp only [fseqBound']
  have hsplit :
      (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p
            * (fseq n (logRatio p (cdiv D' p))
                + ε * tau n * Real.exp 2 * hBJS (logRatio p (cdiv D' p))))
        = (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
          + ε * tau n * Real.exp 2
            * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
                s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit]
  exact ledger_collect (Salt.BrunLower.W_pos s').le hε (Real.exp_pos 2).le (hBJS_pos _).le
    hτ0
    (hf_of_window s' ε z side' D' n hε hn hD hz hguard hnu hS1 hSn)
    (hh_of_window s' ε z side' D' n hε hn hD hz hguard hnu hS1 hSn) hτrec

end Salt.Chen
