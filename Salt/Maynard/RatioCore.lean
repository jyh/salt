/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Transfer
import Salt.Maynard.TransferSharp
import Salt.Maynard.HA11
import Salt.Maynard.Tuple

/-!
# RATIO CORE — the sharp lower bound on the sieve ratio `k·B₁²/A₁`

Feeding the landed sharp one-dimensional transfers (`B1_lower_sharp`,
`A1_upper_sharp` of `Salt.Maynard.TransferSharp`) through the large-`R`/large-`k`
regime gives a clean lower bound on the Maynard sieve ratio `k·B₁²/A₁`.

With `b := bParam k R = k·log k/log R`, `Q := (φW/W)·b⁻¹` and `L := log k`, the
key identity is `k·b⁻¹ = log R/log k`, i.e. `k·Q·L² = (φW/W)·log R·log k`.

The derivation, in three steps:

* **`B1_ratio_lower`** : `B₁ ≥ Q·L/18`.  From `B1_lower_sharp`,
  `B₁ ≥ Q·log(1 + b·log(R₀−1)) − errB1`; with `b·log(R₀−1) ≥ k^{1/9}` (the
  `hbLo` regime hypothesis) the log-term is `≥ (1/9)·L`, and `errB1 ≤ Q·L/18`
  (the `hEB` regime hypothesis, genuine "R large" since `errB1` is a fixed
  `W`-only constant while `Q → ∞`).
* **`A1_ratio_upper`** : `A₁ ≤ 9·Q`.  From `A1_upper_sharp` the three summands
  are bounded by `4Q + 4Q + Q`: the first factor `(1 − s⁻¹) ≤ 1`; the second,
  `4(φW/W)·log R₀·(1+b·log(R₀−1))⁻²`, uses `b·log R₀ ≤ k^{1/8} ≤ k^{2/9} ≤
  (1+b·log(R₀−1))²`; and `errA1 ≤ Q` (the `hEA` regime hypothesis).
* **`ratio_core_lower`** : combining, `k·B₁²/A₁ ≥ k·(Q·L/18)²/(9Q) = k·Q·L²/2916
  = (φW/W)·log R·log k/2916`.

The three side hypotheses `hbLo`, `hEA`, `hEB` are all genuine large-parameter
statements (never the conclusion): `hbLo` is "R large enough that `b·log(R₀−1)
≥ k^{1/9}`" and `hEA`/`hEB` are "R large enough to absorb the fixed `W`-only
error constants".  The caller supplies `R = ⌊N^{1/5}⌋` with `N` huge, which
meets any finite threshold.
-/

open Finset

namespace Salt.Maynard

/-- **`B1_ratio_lower`.** `Q·log k/18 ≤ B₁`, with `Q = (φW/W)·b⁻¹`.  Uses the
sharp lower bound `B1_lower_sharp`, the regime hypothesis `hbLo` (giving
`log(1+b·log(R₀−1)) ≥ (1/9)·log k`), and `hEB` (absorbing the `W`-only error
`errB1` into `Q·log k/18`). -/
theorem B1_ratio_lower (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k R T)
    (hbLo : (k : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEB : errB1 k W ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ * Real.log k / 18) :
    (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ * Real.log k / 18 ≤ B1 k R W T := by
  have hbpos : 0 < bParam k R := bParam_pos (by omega) hR
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  have hφWpos : (0 : ℝ) < (Nat.totient W / W : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
  have hQ0 : 0 ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ :=
    (mul_pos hφWpos (inv_pos.mpr hbpos)).le
  have hsharp := B1_lower_sharp k R W T hW hk hR hT1 hX
  have hk19nn : (0 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_nonneg hkpos.le _
  -- `log(1 + b·log(R₀−1)) ≥ (1/9)·log k`
  have hM : (1 / 9 : ℝ) * Real.log k
      ≤ Real.log (1 + bParam k R * Real.log (R0 k R T - 1)) := by
    have hk19pos : (0 : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hkpos _
    have hle : (k : ℝ) ^ ((1 : ℝ) / 9) ≤ 1 + bParam k R * Real.log (R0 k R T - 1) := by
      linarith [hbLo]
    have h := Real.log_le_log hk19pos hle
    rwa [Real.log_rpow hkpos] at h
  have hQM := mul_le_mul_of_nonneg_left hM hQ0
  -- abstract the heavy sums and monomials to opaque reals
  set Q := (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ with hQdef
  set L := Real.log k with hLdef
  set b := B1 k R W T with hbdef
  clear_value Q L b
  nlinarith [hsharp, hQM, hEB]

/-- **`A1_ratio_upper`.** `A₁ ≤ 9·Q`, with `Q = (φW/W)·b⁻¹`.  Uses the sharp
upper bound `A1_upper_sharp`; the three summands are bounded by `4Q`, `4Q`, `Q`
respectively.  The middle bound uses `b·log R₀ ≤ k^{1/8} ≤ k^{2/9} ≤
(1+b·log(R₀−1))²` (from `hT` and `hbLo`); `hEA` absorbs the `W`-only error
`errA1`. -/
theorem A1_ratio_upper (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k R T)
    (hbLo : (k : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k W ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹) :
    A1 k R W T ≤ 9 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) := by
  have hbpos : 0 < bParam k R := bParam_pos (by omega) hR
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hlogkpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogkne : Real.log k ≠ 0 := ne_of_gt hlogkpos
  have hlogRpos : 0 < Real.log R := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hlogRne : Real.log R ≠ 0 := ne_of_gt hlogRpos
  have hR0_1 : 1 ≤ R0 k R T := by omega
  have hLR0nn : 0 ≤ Real.log (R0 k R T) := Real.log_nonneg (by exact_mod_cast hR0_1)
  have hk19nn : (0 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_nonneg hkpos.le _
  have hPpos : 0 < 1 + bParam k R * Real.log (R0 k R T - 1) := by linarith [hbLo]
  have hP2 : 0 < (1 + bParam k R * Real.log (R0 k R T - 1)) ^ 2 := pow_pos hPpos 2
  -- `b·log R₀ ≤ k^{1/8}`
  have hlogR0 : Real.log (R0 k R T) ≤ (T / (k : ℝ)) * Real.log R := log_R0_le hR hR0_1
  have hbTk : bParam k R * ((T / (k : ℝ)) * Real.log R) = (k : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [hT]; unfold bParam; field_simp
  have hbU : bParam k R * Real.log (R0 k R T) ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := by
    calc bParam k R * Real.log (R0 k R T)
        ≤ bParam k R * ((T / (k : ℝ)) * Real.log R) :=
          mul_le_mul_of_nonneg_left hlogR0 hbpos.le
      _ = (k : ℝ) ^ ((1 : ℝ) / 8) := hbTk
  -- `k^{1/8} ≤ k^{2/9}`
  have hk18le29 : (k : ℝ) ^ ((1 : ℝ) / 8) ≤ (k : ℝ) ^ ((2 : ℝ) / 9) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k)) (by norm_num)
  -- `b·log R₀ ≤ (1 + b·log(R₀−1))²`
  have hkey : bParam k R * Real.log (R0 k R T)
      ≤ (1 + bParam k R * Real.log (R0 k R T - 1)) ^ 2 := by
    calc bParam k R * Real.log (R0 k R T)
        ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := hbU
      _ ≤ (k : ℝ) ^ ((2 : ℝ) / 9) := hk18le29
      _ = ((k : ℝ) ^ ((1 : ℝ) / 9)) ^ 2 := by
          rw [pow_two, ← Real.rpow_add hkpos]; norm_num
      _ ≤ (1 + bParam k R * Real.log (R0 k R T - 1)) ^ 2 :=
          pow_le_pow_left₀ hk19nn (by linarith [hbLo]) 2
  -- the "star" inequality: `log R₀·(1+b·log(R₀−1))⁻² ≤ b⁻¹`
  have hstar : Real.log (R0 k R T)
        * ((1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) ^ 2 ≤ (bParam k R)⁻¹ := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hP2, inv_mul_eq_div, le_div_iff₀ hbpos]
    nlinarith [hkey]
  have harg_pos : 0 < 1 + bParam k R * Real.log (R0 k R T) := by
    linarith [mul_nonneg hbpos.le hLR0nn]
  have hQ0 : 0 ≤ (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ := by
    have hWpos : 0 < W := Nat.pos_of_ne_zero hW
    have hφWpos : (0 : ℝ) < (Nat.totient W / W : ℝ) :=
      div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
    exact (mul_pos hφWpos (inv_pos.mpr hbpos)).le
  -- term 1: `4·Q·(1 − s(R₀)⁻¹) ≤ 4·Q`
  have hT1b : 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * (1 - (1 + bParam k R * Real.log (R0 k R T))⁻¹)
      ≤ 4 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) := by
    have hinv0 : 0 ≤ (1 + bParam k R * Real.log (R0 k R T))⁻¹ := inv_nonneg.mpr harg_pos.le
    have hle1 : 1 - (1 + bParam k R * Real.log (R0 k R T))⁻¹ ≤ 1 := by linarith
    have hC0 : 0 ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ := by nlinarith [hQ0]
    calc 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
            * (1 - (1 + bParam k R * Real.log (R0 k R T))⁻¹)
        ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hle1 hC0
      _ = 4 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) := by ring
  -- term 2: `4·(φW/W)·log R₀·(1+b·log(R₀−1))⁻² ≤ 4·Q`
  have hT2b : 4 * (Nat.totient W / W : ℝ) * Real.log (R0 k R T)
        * ((1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) ^ 2
      ≤ 4 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) := by
    have h4φ : 0 ≤ 4 * (Nat.totient W / W : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hstar h4φ
    calc 4 * (Nat.totient W / W : ℝ) * Real.log (R0 k R T)
            * ((1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) ^ 2
        = 4 * (Nat.totient W / W : ℝ)
            * (Real.log (R0 k R T)
              * ((1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) ^ 2) := by ring
      _ ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹ := hmul
      _ = 4 * ((Nat.totient W / W : ℝ) * (bParam k R)⁻¹) := by ring
  have hsharp := A1_upper_sharp k R W T hW hk hR hT1 hX
  linarith [hsharp, add_le_add (add_le_add hT1b hT2b) hEA]

/-- **RATIO CORE (`ratio_core_lower`).** A clean lower bound on the Maynard
sieve ratio: `(φW/W)·log R·log k/2916 ≤ k·B₁²/A₁`, in the large-`R`/large-`k`
regime isolated by `hbLo`/`hEA`/`hEB` (all genuine largeness statements, never
the conclusion).  Here `W = W k` is the fixed sieve modulus. -/
theorem ratio_core_lower (k R : ℕ) (T : ℝ)
    (hk : 3 ≤ k) (hR : 2 ≤ R)
    (hT : T = (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) (hT1 : 1 ≤ T)
    (hX : 4 ≤ R0 k R T)
    (hbLo : (k : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k R * Real.log (R0 k R T - 1))
    (hEA : errA1 k (W k) ≤ (Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹)
    (hEB : errB1 k (W k)
        ≤ (Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹ * Real.log k / 18) :
    (Nat.totient (W k) / W k : ℝ) * Real.log R * Real.log k / 2916
      ≤ (k : ℝ) * (B1 k R (W k) T) ^ 2 / (A1 k R (W k) T) := by
  have hW : W k ≠ 0 := (W_squarefree k).ne_zero
  have hbpos : 0 < bParam k R := bParam_pos (by omega) hR
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hlogkpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogkne : Real.log k ≠ 0 := ne_of_gt hlogkpos
  have hWpos : 0 < W k := Nat.pos_of_ne_zero hW
  have hWRne : (W k : ℝ) ≠ 0 := by exact_mod_cast hW
  have hφWpos : (0 : ℝ) < (Nat.totient (W k) / W k : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
  have hQpos : 0 < (Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹ :=
    mul_pos hφWpos (inv_pos.mpr hbpos)
  -- the two ratio bounds
  have hBlo := B1_ratio_lower k R (W k) T hW hk hR hT1 hX hbLo hEB
  have hAup := A1_ratio_upper k R (W k) T hW hk hR hT hT1 hX hbLo hEA
  -- `A₁ > 0` (the `r = 1` term is `fWt(1)²/φ(1) = 1`)
  have ha0 : 0 < A1 k R (W k) T := by
    have h1mem : 1 ∈ sqfCop (R0 k R T) (W k) := by
      rw [sqfCop, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, squarefree_one, Nat.coprime_one_left (W k)⟩
    unfold A1
    apply Finset.sum_pos'
    · intro r _; positivity
    · refine ⟨1, h1mem, ?_⟩
      have hf : 0 < fWt k R 1 := fWt_pos (le_refl 1) hR
      have hφ1 : (Nat.totient 1 : ℝ) = 1 := by simp
      rw [hφ1, div_one]
      exact pow_pos hf 2
  -- LHS identity: `(φW/W)·log R·log k = k·Q·(log k)²`
  have hbinv : (bParam k R)⁻¹ = Real.log R / ((k : ℝ) * Real.log k) := by
    unfold bParam; rw [inv_div]
  have hkey2 : (Nat.totient (W k) / W k : ℝ) * Real.log R * Real.log k
      = (k : ℝ) * ((Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹) * (Real.log k) ^ 2 := by
    rw [hbinv]; field_simp
  -- abstract
  set Q := (Nat.totient (W k) / W k : ℝ) * (bParam k R)⁻¹ with hQdef
  set L := Real.log k with hLdef
  set a := A1 k R (W k) T with hadef
  set b := B1 k R (W k) T with hbdef
  clear_value Q L a b
  rw [hkey2, le_div_iff₀ ha0]
  -- goal: `k·Q·L²/2916 · a ≤ k·b²`
  have hbnn : 0 ≤ Q * L / 18 := div_nonneg (mul_nonneg hQpos.le hlogkpos.le) (by norm_num)
  have hbsq : (Q * L / 18) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hbnn hBlo 2
  have hVnn : 0 ≤ (k : ℝ) * Q * L ^ 2 / 2916 :=
    div_nonneg (mul_nonneg (mul_nonneg hkpos.le hQpos.le) (sq_nonneg L)) (by norm_num)
  calc (k : ℝ) * Q * L ^ 2 / 2916 * a
      ≤ (k : ℝ) * Q * L ^ 2 / 2916 * (9 * Q) := mul_le_mul_of_nonneg_left hAup hVnn
    _ = (k : ℝ) * (Q * L / 18) ^ 2 := by ring
    _ ≤ (k : ℝ) * b ^ 2 := mul_le_mul_of_nonneg_left hbsq hkpos.le

end Salt.Maynard
