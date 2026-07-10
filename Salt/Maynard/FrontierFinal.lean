/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.FrontierDischarge

/-!
# M7 capstone — discharging the analytic frontier

Regime-threshold real-analysis plus final assembly.  Builds on the R-uniform
infrastructure of `FrontierDischarge`.  No new mathematics.
-/

open Finset Filter

namespace Salt.Maynard

/-! ## k₀-regime elementary facts -/

/-- For `L ≥ 256`, `L ≤ exp(L/8)`.  (Two linear `add_one_le_exp` steps squared.) -/
lemma le_exp_eighth {L : ℝ} (hL : 256 ≤ L) : L ≤ Real.exp (L / 8) := by
  have h16 : L / 16 ≤ Real.exp (L / 16) := by
    have := Real.add_one_le_exp (L / 16); linarith
  have hnn : (0 : ℝ) ≤ L / 16 := by linarith
  have hsq : (L / 16) ^ 2 ≤ (Real.exp (L / 16)) ^ 2 := pow_le_pow_left₀ hnn h16 2
  have hexp2 : (Real.exp (L / 16)) ^ 2 = Real.exp (L / 8) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hLsq : L ≤ (L / 16) ^ 2 := by nlinarith [hL]
  calc L ≤ (L / 16) ^ 2 := hLsq
    _ ≤ (Real.exp (L / 16)) ^ 2 := hsq
    _ = Real.exp (L / 8) := hexp2

/-- `log k ≤ k^{1/8}` once `log k ≥ 256`. -/
lemma logk_le_k18 {k : ℕ} (hk : 0 < k) (hlogk : 256 ≤ Real.log k) :
    Real.log k ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hre : (k : ℝ) ^ ((1 : ℝ) / 8) = Real.exp (Real.log k / 8) := by
    rw [Real.rpow_def_of_pos hkpos]; ring_nf
  rw [hre]; exact le_exp_eighth hlogk

/-- `k^{1/9} ≥ 4` when `log k ≥ 300`. -/
lemma k19_ge_four {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    (4 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 9) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos hkpos]
  have h1 : (300 : ℝ) / 9 ≤ Real.log k * (1 / 9) := by linarith
  have h2 : Real.exp ((300 : ℝ) / 9) ≤ Real.exp (Real.log k * (1 / 9)) := Real.exp_le_exp.mpr h1
  have h3 : (4 : ℝ) ≤ Real.exp ((300 : ℝ) / 9) := by
    have := Real.add_one_le_exp ((300 : ℝ) / 9); linarith
  linarith

/-- `k^{1/72} ≥ 2` when `log k ≥ 300`. -/
lemma k172_ge_two {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    (2 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 72) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [Real.rpow_def_of_pos hkpos]
  have h1 : (300 : ℝ) / 72 ≤ Real.log k * (1 / 72) := by linarith
  have h2 : Real.exp ((300 : ℝ) / 72) ≤ Real.exp (Real.log k * (1 / 72)) := Real.exp_le_exp.mpr h1
  have h3 : (2 : ℝ) ≤ Real.exp ((300 : ℝ) / 72) := by
    have := Real.add_one_le_exp ((300 : ℝ) / 72); linarith
  linarith

/-- `k^{1/8} = k^{1/9}·k^{1/72}`. -/
lemma k18_eq_k19_k172 {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ ((1 : ℝ) / 8) = (k : ℝ) ^ ((1 : ℝ) / 9) * (k : ℝ) ^ ((1 : ℝ) / 72) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [← Real.rpow_add hkpos]; norm_num

/-- `k^{1/9} + 1 ≤ k^{1/8}` (so `k^{1/9} ≤ k^{1/8} − 1`) when `log k ≥ 300`. -/
lemma k19_add_one_le_k18 {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    (k : ℝ) ^ ((1 : ℝ) / 9) + 1 ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := by
  have h9 : (4 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 9) := k19_ge_four hk hlogk
  have h72 : (2 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 72) := k172_ge_two hk hlogk
  have hsplit := k18_eq_k19_k172 hk
  have h9nn : (0 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 9) := by positivity
  nlinarith [hsplit, h9, h72, h9nn]

/-- `5 ≤ k^{1/8}` when `log k ≥ 300`. -/
lemma k18_ge_five {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    (5 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 8) := by
  have := k19_ge_four hk hlogk
  have := k19_add_one_le_k18 hk hlogk
  linarith

/-- The frozen `T = k^{1/8}/log k` satisfies `1 ≤ T` when `log k ≥ 300`. -/
lemma T_ge_one {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    1 ≤ (k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k := by
  have hlogkpos : (0 : ℝ) < Real.log k := by linarith
  rw [le_div_iff₀ hlogkpos, one_mul]
  exact logk_le_k18 hk (by linarith)

/-- The frozen `T` satisfies `5·T ≤ k` when `log k ≥ 300`, `k ≥ 1`. -/
lemma five_T_le {k : ℕ} (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    5 * ((k : ℝ) ^ ((1 : ℝ) / 8) / Real.log k) ≤ (k : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlogkpos : (0 : ℝ) < Real.log k := by linarith
  have hk18le : (k : ℝ) ^ ((1 : ℝ) / 8) ≤ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    calc (k : ℝ) ^ ((1 : ℝ) / 8) ≤ (k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (k : ℝ) := Real.rpow_one _
  rw [← mul_div_assoc, div_le_iff₀ hlogkpos]
  nlinarith [hk18le, hlogkpos, hkpos, hlogk]

/-! ## Facts about `R = ⌊N'^{1/5}⌋₊` -/

/-- `log R ≥ (1/6)·log N'` for `N' ≥ 2^30`. -/
lemma logR_lower (N' : ℕ) (hN' : (2 : ℝ) ^ 30 ≤ (N' : ℝ)) :
    Real.log N' / 6 ≤ Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by nlinarith [hN']
  have hxpos : (0 : ℝ) < x := by linarith
  set R := ⌊x ^ ((1 : ℝ) / 5)⌋₊ with hR
  have h30 : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 30) := by
    have h2 : ((2 : ℝ) ^ (30 : ℕ)) ^ ((1 : ℝ) / 30) ≤ x ^ ((1 : ℝ) / 30) :=
      Real.rpow_le_rpow (by positivity) hN' (by norm_num)
    have he : ((2 : ℝ) ^ (30 : ℕ)) ^ ((1 : ℝ) / 30) = 2 := by
      rw [← Real.rpow_natCast 2 30, ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [he] at h2
  have hsplit : x ^ ((1 : ℝ) / 5) = x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 30) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hx6pos : (0 : ℝ) < x ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
  have hx6ge1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 6) := Real.one_le_rpow hx1 (by norm_num)
  have hbig : 2 * x ^ ((1 : ℝ) / 6) ≤ x ^ ((1 : ℝ) / 5) := by
    rw [hsplit]; nlinarith [h30, hx6pos]
  have hfloor : x ^ ((1 : ℝ) / 5) - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 5)); rw [← hR] at this; linarith
  have hRge : x ^ ((1 : ℝ) / 6) ≤ (R : ℝ) := by nlinarith [hfloor, hbig, hx6ge1]
  have hlog := Real.log_le_log hx6pos hRge
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- `log R ≤ (1/5)·log N'` for `N' ≥ 1`. -/
lemma logR_upper (N' : ℕ) (hN' : 1 ≤ N') :
    Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ≤ Real.log N' / 5 := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos _
  have hx5ge1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 5) := Real.one_le_rpow hx1 (by norm_num)
  have hRle : (⌊x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ≤ x ^ ((1 : ℝ) / 5) := Nat.floor_le hx5pos.le
  have hRpos : (0 : ℝ) < (⌊x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x ^ ((1 : ℝ) / 5)⌋₊ := Nat.le_floor (by exact_mod_cast hx5ge1)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlog := Real.log_le_log hRpos hRle
  rw [Real.log_rpow hxpos] at hlog
  linarith [hlog]

/-- `2 ≤ R` for `N' ≥ 32`. -/
lemma R_ge_two (N' : ℕ) (hN' : (32 : ℝ) ≤ (N' : ℝ)) :
    2 ≤ ⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ := by
  set x := (N' : ℝ) with hx
  have hge : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 5) := by
    have h2 : ((32 : ℝ)) ^ ((1 : ℝ) / 5) ≤ x ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (by norm_num) hN' (by norm_num)
    have he : ((32 : ℝ)) ^ ((1 : ℝ) / 5) = 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← Real.rpow_natCast 2 5,
        ← Real.rpow_mul (by norm_num)]; norm_num
    rwa [he] at h2
  exact Nat.le_floor (by exact_mod_cast hge)

/-- `R ≤ N'` for `N' ≥ 1`. -/
lemma R_le_N' (N' : ℕ) (hN' : 1 ≤ N') :
    ⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ ≤ N' := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hle : x ^ ((1 : ℝ) / 5) ≤ x := by
    calc x ^ ((1 : ℝ) / 5) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one _
  calc ⌊x ^ ((1 : ℝ) / 5)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hle
    _ = N' := by rw [hx, Nat.floor_natCast]

/-- The EH modulus range `W·R² ≤ ⌊N'^{1/2}⌋₊` for `N' ≥ (W k₀)^{10}`. -/
lemma EH_range (k₀ N' : ℕ) (hN' : ((W k₀ : ℝ)) ^ (10 : ℕ) ≤ (N' : ℝ)) (hN1 : 1 ≤ N') :
    W k₀ * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) ^ 2 ≤ ⌊(N' : ℝ) ^ ((1 : ℝ) / 2)⌋₊ := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN1
  have hxpos : (0 : ℝ) < x := by linarith
  set R := ⌊x ^ ((1 : ℝ) / 5)⌋₊ with hR
  have hWpos : (0 : ℝ) < (W k₀ : ℝ) := by
    have : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
    exact_mod_cast this
  have hx5pos : (0 : ℝ) < x ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos _
  have hRle : (R : ℝ) ≤ x ^ ((1 : ℝ) / 5) := Nat.floor_le hx5pos.le
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := by positivity
  -- R² ≤ x^{2/5}
  have hR2 : (R : ℝ) ^ 2 ≤ x ^ ((2 : ℝ) / 5) := by
    have h1 : (R : ℝ) ^ 2 ≤ (x ^ ((1 : ℝ) / 5)) ^ 2 := by
      apply pow_le_pow_left₀ hRnn hRle
    have h2 : (x ^ ((1 : ℝ) / 5)) ^ 2 = x ^ ((2 : ℝ) / 5) := by
      rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 5)) 2, ← Real.rpow_mul hxpos.le]; norm_num
    rwa [h2] at h1
  -- W ≤ x^{1/10}
  have hWle : (W k₀ : ℝ) ≤ x ^ ((1 : ℝ) / 10) := by
    have h1 : ((W k₀ : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) ≤ x ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hN' (by norm_num)
    have he : ((W k₀ : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) = (W k₀ : ℝ) := by
      rw [← Real.rpow_natCast (W k₀ : ℝ) 10, ← Real.rpow_mul hWpos.le]; norm_num
    rwa [he] at h1
  -- W·R² ≤ x^{1/2}
  have hmul : (W k₀ : ℝ) * (R : ℝ) ^ 2 ≤ x ^ ((1 : ℝ) / 2) := by
    have hstep : (W k₀ : ℝ) * (R : ℝ) ^ 2 ≤ x ^ ((1 : ℝ) / 10) * x ^ ((2 : ℝ) / 5) := by
      apply mul_le_mul hWle hR2 (by positivity) (by positivity)
    have he : x ^ ((1 : ℝ) / 10) * x ^ ((2 : ℝ) / 5) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hxpos]; norm_num
    rwa [he] at hstep
  apply Nat.le_floor
  push_cast
  exact hmul

/-! ## `eventually` engines: `log R` and `(φW/W)·log R` grow without bound -/

/-- Eventually `log R ≥ t`, for `R = ⌊N'^{1/5}⌋₊`. -/
lemma eventually_logR_ge (t : ℝ) :
    ∀ᶠ N' : ℕ in atTop, t ≤ Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by
  have htend : Filter.Tendsto (fun N' : ℕ => Real.log (N' : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop ((2 ^ 30 : ℕ)), htend.eventually_ge_atTop (6 * t)]
    with N' h30 hlog
  have hN30 : (2 : ℝ) ^ 30 ≤ (N' : ℝ) := by exact_mod_cast h30
  have := logR_lower N' hN30
  linarith [this, hlog]

/-- Eventually `(T/k₀)·log R ≥ t`, given `0 < T/k₀`. -/
lemma eventually_rho_logR_ge (k₀ : ℕ) (T t : ℝ) (hρ : 0 < T / (k₀ : ℝ)) :
    ∀ᶠ N' : ℕ in atTop,
      t ≤ T / (k₀ : ℝ) * Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by
  filter_upwards [eventually_logR_ge (t / (T / (k₀ : ℝ)))] with N' h
  rw [div_le_iff₀ hρ] at h
  rw [mul_comm]; exact h

/-- Eventually `(φW/W)·log R ≥ C`. -/
lemma eventually_phiW_logR_ge (k₀ : ℕ) (C : ℝ) :
    ∀ᶠ N' : ℕ in atTop,
      C ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by
  have hWpos : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
  have hφpos : (0 : ℝ) < (Nat.totient (W k₀) / W k₀ : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
  filter_upwards [eventually_logR_ge (C / (Nat.totient (W k₀) / W k₀ : ℝ))] with N' h
  rw [div_le_iff₀ hφpos] at h
  rw [mul_comm]; exact h

/-! ## The R₀/`bParam` sharp-regime atoms -/

/-- Key identity `b·(T/k₀·log R) = k₀^{1/8}`. -/
lemma bParam_rho_logR (k₀ R : ℕ) (T : ℝ) (hk : 2 ≤ k₀) (hR : 2 ≤ R)
    (hT : T = (k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀) :
    bParam k₀ R * (T / (k₀ : ℝ) * Real.log R) = (k₀ : ℝ) ^ ((1 : ℝ) / 8) := by
  have hlogk : (0 : ℝ) < Real.log k₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < k₀))
  have hlogR : (0 : ℝ) < Real.log R := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hk0 : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  rw [hT]; unfold bParam; field_simp

/-- `4 ≤ R0 k₀ R T` from `(T/k₀)·log R ≥ log 8`. -/
lemma R0_ge_four (k₀ R : ℕ) (T : ℝ) (hR : 2 ≤ R)
    (hρR : Real.log 8 ≤ T / (k₀ : ℝ) * Real.log R) :
    4 ≤ R0 k₀ R T := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hexp : (R : ℝ) ^ (T / (k₀ : ℝ)) = Real.exp (T / (k₀ : ℝ) * Real.log R) := by
    rw [Real.rpow_def_of_pos hRpos, mul_comm]
  have h8 : (8 : ℝ) ≤ (R : ℝ) ^ (T / (k₀ : ℝ)) := by
    rw [hexp]
    calc (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (T / (k₀ : ℝ) * Real.log R) := Real.exp_le_exp.mpr hρR
  have h4 : 4 ≤ ⌊(R : ℝ) ^ (T / (k₀ : ℝ))⌋₊ := Nat.le_floor (by push_cast; linarith)
  rwa [R0]

/-- `(T/k₀)·log R − log 2 ≤ log(R0−1)` from `(T/k₀)·log R ≥ log 8`. -/
lemma logR0m1_lower (k₀ R : ℕ) (T : ℝ) (hR : 2 ≤ R)
    (hρR : Real.log 8 ≤ T / (k₀ : ℝ) * Real.log R) :
    T / (k₀ : ℝ) * Real.log R - Real.log 2 ≤ Real.log ((R0 k₀ R T : ℝ) - 1) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  set Rρ := (R : ℝ) ^ (T / (k₀ : ℝ)) with hRρ
  have hexp : Rρ = Real.exp (T / (k₀ : ℝ) * Real.log R) := by
    rw [hRρ, Real.rpow_def_of_pos hRpos, mul_comm]
  have hRρ8 : (8 : ℝ) ≤ Rρ := by
    rw [hexp]
    calc (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hρR
  have hlogRρ : Real.log Rρ = T / (k₀ : ℝ) * Real.log R := by rw [hexp, Real.log_exp]
  have hR0eq : R0 k₀ R T = ⌊Rρ⌋₊ := by rw [R0, hRρ]
  have hlt := Nat.lt_floor_add_one Rρ
  rw [← hR0eq] at hlt
  have hR0ge : Rρ - 1 ≤ (R0 k₀ R T : ℝ) := by linarith [hlt]
  have hpos : (0 : ℝ) < Rρ / 2 := by linarith
  have hle : Rρ / 2 ≤ (R0 k₀ R T : ℝ) - 1 := by linarith
  have hmono := Real.log_le_log hpos hle
  rw [Real.log_div (by linarith) (by norm_num), hlogRρ] at hmono
  linarith [hmono]

/-- `bParam·log 2 ≤ 1` from `log R ≥ k₀·log k₀·log 2`. -/
lemma bParam_log2_le (k₀ R : ℕ) (_hk : 2 ≤ k₀) (hR : 2 ≤ R)
    (hlogR : (k₀ : ℝ) * Real.log k₀ * Real.log 2 ≤ Real.log R) :
    bParam k₀ R * Real.log 2 ≤ 1 := by
  have hlogR0 : (0 : ℝ) < Real.log R := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  unfold bParam
  rw [div_mul_eq_mul_div, div_le_one hlogR0]
  linarith [hlogR]

/-- The `hbLo` atom: `k₀^{1/9} ≤ b·log(R0−1)`. -/
lemma hbLo_of (k₀ R : ℕ) (T : ℝ) (hk : 3072 ≤ k₀) (hR : 2 ≤ R)
    (hlogk : 300 ≤ Real.log k₀)
    (hT : T = (k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀)
    (hρR : Real.log 8 ≤ T / (k₀ : ℝ) * Real.log R)
    (hblog2 : bParam k₀ R * Real.log 2 ≤ 1) :
    (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) := by
  have hbpos := bParam_pos (show 2 ≤ k₀ by omega) hR
  have hlow := logR0m1_lower k₀ R T hR hρR
  have hmul := mul_le_mul_of_nonneg_left hlow hbpos.le
  have hid := bParam_rho_logR k₀ R T (by omega) hR hT
  have hk18 := k19_add_one_le_k18 (show 0 < k₀ by omega) hlogk
  have hexpand : bParam k₀ R * (T / (k₀ : ℝ) * Real.log R - Real.log 2)
      = bParam k₀ R * (T / (k₀ : ℝ) * Real.log R) - bParam k₀ R * Real.log 2 := by ring
  rw [hexpand, hid] at hmul
  linarith [hmul, hk18, hblog2]

/-- The `hb4` atom follows from `hbLo` and `4 ≤ k₀^{1/9}`. -/
lemma hb4_of (k₀ R : ℕ) (T : ℝ) (hlogk : 300 ≤ Real.log k₀) (hk₀ : 0 < k₀)
    (hbLo : (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1)) :
    4 ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) := by
  have := k19_ge_four hk₀ hlogk
  linarith

/-! ## The four error atoms (`errA1`/`errB1` in both regime shapes) -/

/-- `(bParam k₀ R)⁻¹ = log R / (k₀·log k₀)`. -/
lemma bParam_inv (k₀ R : ℕ) :
    (bParam k₀ R)⁻¹ = Real.log R / ((k₀ : ℝ) * Real.log k₀) := by
  unfold bParam; rw [inv_div]

/-- `errA1`, ratio form: `errA1 ≤ (φW/W)·b⁻¹`. -/
lemma hEA_ratio_of (k₀ R : ℕ) (hk : 2 ≤ k₀) (_hR : 2 ≤ R)
    (hthr : errA1 k₀ (W k₀) * ((k₀ : ℝ) * Real.log k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R) :
    errA1 k₀ (W k₀) ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹ := by
  have hlogk : (0 : ℝ) < Real.log k₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < k₀))
  have hk0 : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  rw [bParam_inv, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  linarith [hthr]

/-- `errB1`, ratio form: `errB1 ≤ (φW/W)·b⁻¹·log k₀/18`. -/
lemma hEB_ratio_of (k₀ R : ℕ) (hk : 2 ≤ k₀) (_hR : 2 ≤ R)
    (hthr : 18 * (k₀ : ℝ) * errB1 k₀ (W k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R) :
    errB1 k₀ (W k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹ * Real.log k₀ / 18 := by
  have hlogk : (0 : ℝ) < Real.log k₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < k₀))
  have hlogkne : Real.log k₀ ≠ 0 := ne_of_gt hlogk
  have hk0 : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  have hk0ne : (k₀ : ℝ) ≠ 0 := ne_of_gt hk0
  rw [bParam_inv]
  have heq : (Nat.totient (W k₀) / W k₀ : ℝ) * (Real.log R / ((k₀ : ℝ) * Real.log k₀))
        * Real.log k₀ / 18
      = (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R / (18 * (k₀ : ℝ)) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith [hthr]

/-- `errA1`, cheb form: `errA1 ≤ (1/100)·((φW/W)·b⁻¹)·log k₀`. -/
lemma hEA_cheb_of (k₀ R : ℕ) (hk : 2 ≤ k₀) (_hR : 2 ≤ R)
    (hthr : 100 * (k₀ : ℝ) * errA1 k₀ (W k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R) :
    errA1 k₀ (W k₀)
      ≤ (1 / 100) * ((Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹) * Real.log k₀ := by
  have hlogk : (0 : ℝ) < Real.log k₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < k₀))
  have hlogkne : Real.log k₀ ≠ 0 := ne_of_gt hlogk
  have hk0 : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  have hk0ne : (k₀ : ℝ) ≠ 0 := ne_of_gt hk0
  rw [bParam_inv]
  have heq : (1 / 100) * ((Nat.totient (W k₀) / W k₀ : ℝ)
        * (Real.log R / ((k₀ : ℝ) * Real.log k₀))) * Real.log k₀
      = (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R / (100 * (k₀ : ℝ)) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith [hthr]

/-- `errB1`, cheb form: `errB1 ≤ (1/100)·((φW/W)·b⁻¹)`. -/
lemma hEB_cheb_of (k₀ R : ℕ) (hk : 2 ≤ k₀) (_hR : 2 ≤ R)
    (hthr : 100 * (k₀ : ℝ) * Real.log k₀ * errB1 k₀ (W k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R) :
    errB1 k₀ (W k₀)
      ≤ (1 / 100) * ((Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹) := by
  have hlogk : (0 : ℝ) < Real.log k₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < k₀))
  have hlogkne : Real.log k₀ ≠ 0 := ne_of_gt hlogk
  have hk0 : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  have hk0ne : (k₀ : ℝ) ≠ 0 := ne_of_gt hk0
  rw [bParam_inv]
  have heq : (1 / 100) * ((Nat.totient (W k₀) / W k₀ : ℝ)
        * (Real.log R / ((k₀ : ℝ) * Real.log k₀)))
      = (Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R / (100 * ((k₀ : ℝ) * Real.log k₀)) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith [hthr]

/-! ## Part C: routine thresholds (`hδlb`, `herr1`, `herr2`) -/

/-- `R² ≤ N'^{2/5}`. -/
lemma R_sq_le (N' : ℕ) (hN' : 1 ≤ N') :
    (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2 ≤ (N' : ℝ) ^ ((2 : ℝ) / 5) := by
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hN'
  have hxpos : (0 : ℝ) < x := by linarith
  have hx5pos : (0 : ℝ) < x ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos _
  have hRle : (⌊x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ≤ x ^ ((1 : ℝ) / 5) := Nat.floor_le hx5pos.le
  have hRnn : (0 : ℝ) ≤ (⌊x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) := by positivity
  calc (⌊x ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2 ≤ (x ^ ((1 : ℝ) / 5)) ^ 2 := pow_le_pow_left₀ hRnn hRle 2
    _ = x ^ ((2 : ℝ) / 5) := by
        rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 5)) 2, ← Real.rpow_mul hxpos.le]; norm_num

/-- Eventually `D₀ k₀ ≤ c·N'/(2·log N')`. -/
lemma eventually_D0_le (k₀ : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N' : ℕ in atTop, (D₀ k₀ : ℝ) ≤ c * (N' : ℝ) / (2 * Real.log N') := by
  have hev := eventually_poly_beats_polylog 1 1 (2 * (D₀ k₀ : ℝ) / c) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 2] with N' hN' hN2
  have hlogpos : (0 : ℝ) < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  simp only [pow_one, Real.rpow_one] at hN'
  have hD0nn : (0 : ℝ) ≤ (D₀ k₀ : ℝ) := by positivity
  have hN'' : 2 * (D₀ k₀ : ℝ) * (1 + Real.log N') ≤ c * (N' : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hN'; nlinarith [hN']
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hN'', hlogpos, hD0nn]

/-- Eventually `Cs·R²·(1+log R)^{4k₀+2} ≤ 126·N'/W` for `Cs ≥ 0`. -/
lemma eventually_herr1 (k₀ : ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∀ᶠ N' : ℕ in atTop,
      Cs * (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ) ^ 2
          * (1 + Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ)) ^ (4 * k₀ + 2)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) := by
  have hWpos : (0 : ℝ) < (W k₀ : ℝ) := by
    have : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
    exact_mod_cast this
  have hev := eventually_poly_beats_polylog (4 * k₀ + 2) (3 / 5)
    (Cs * (W k₀ : ℝ) / 126) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 2] with N' hpoly hN2
  set x := (N' : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast (by omega : 1 ≤ N')
  have hxpos : (0 : ℝ) < x := by linarith
  set R := ⌊x ^ ((1 : ℝ) / 5)⌋₊ with hR
  have hR1 : (1 : ℕ) ≤ R := by
    rw [hR]; exact Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_rpow hx1 (by norm_num))
  have hRr1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hLRnn : (0 : ℝ) ≤ Real.log (R : ℝ) := Real.log_nonneg hRr1
  have hR2 : (R : ℝ) ^ 2 ≤ x ^ ((2 : ℝ) / 5) := R_sq_le N' (by omega)
  have hLRle : Real.log (R : ℝ) ≤ Real.log x / 5 := logR_upper N' (by omega)
  have hpow : (1 + Real.log (R : ℝ)) ^ (4 * k₀ + 2) ≤ (1 + Real.log x) ^ (4 * k₀ + 2) := by
    apply pow_le_pow_left₀ (by linarith) (by linarith [hLRle])
  have hLNnn : (0 : ℝ) ≤ (1 + Real.log x) ^ (4 * k₀ + 2) := by positivity
  have hchain : Cs * (R : ℝ) ^ 2 * (1 + Real.log (R : ℝ)) ^ (4 * k₀ + 2)
      ≤ Cs * x ^ ((2 : ℝ) / 5) * (1 + Real.log x) ^ (4 * k₀ + 2) := by
    have h1 : Cs * (R : ℝ) ^ 2 ≤ Cs * x ^ ((2 : ℝ) / 5) := mul_le_mul_of_nonneg_left hR2 hCs
    have h2 : (0 : ℝ) ≤ Cs * (R : ℝ) ^ 2 := by positivity
    calc Cs * (R : ℝ) ^ 2 * (1 + Real.log (R : ℝ)) ^ (4 * k₀ + 2)
        ≤ Cs * (R : ℝ) ^ 2 * (1 + Real.log x) ^ (4 * k₀ + 2) :=
          mul_le_mul_of_nonneg_left hpow h2
      _ ≤ Cs * x ^ ((2 : ℝ) / 5) * (1 + Real.log x) ^ (4 * k₀ + 2) :=
          mul_le_mul_of_nonneg_right h1 hLNnn
  have hxx : x ^ ((2 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) = x := by
    rw [← Real.rpow_add hxpos, show (2 : ℝ) / 5 + 3 / 5 = 1 by norm_num, Real.rpow_one]
  have hmul := mul_le_mul_of_nonneg_left hpoly
    (show (0 : ℝ) ≤ 126 / (W k₀ : ℝ) * x ^ ((2 : ℝ) / 5) by positivity)
  have hfin : Cs * x ^ ((2 : ℝ) / 5) * (1 + Real.log x) ^ (4 * k₀ + 2) ≤ 126 * x / (W k₀ : ℝ) := by
    calc Cs * x ^ ((2 : ℝ) / 5) * (1 + Real.log x) ^ (4 * k₀ + 2)
        = 126 / (W k₀ : ℝ) * x ^ ((2 : ℝ) / 5)
            * (Cs * (W k₀ : ℝ) / 126 * (1 + Real.log x) ^ (4 * k₀ + 2)) := by
          field_simp
      _ ≤ 126 / (W k₀ : ℝ) * x ^ ((2 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) := hmul
      _ = 126 * x / (W k₀ : ℝ) := by rw [mul_assoc, hxx]; ring
  linarith [hchain, hfin]

/-- Eventually `k₀·(C₀·(1+log R)^{2k₀+2}·N'/(log N')^{2k₀+4}) ≤ 126·N'/W` for `C₀ ≥ 0`. -/
lemma eventually_herr2 (k₀ : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ N' : ℕ in atTop,
      (k₀ : ℝ) * (C₀ * (1 + Real.log (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ : ℝ)) ^ (2 * k₀ + 2)
          * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) := by
  have hWpos : (0 : ℝ) < (W k₀ : ℝ) := by
    have : 0 < W k₀ := Nat.pos_of_ne_zero (W_squarefree k₀).ne_zero
    exact_mod_cast this
  set M : ℝ := (k₀ : ℝ) * C₀ * 2 ^ (2 * k₀ + 2) * (W k₀ : ℝ) / 126 with hM
  have hMnn : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have htend : Filter.Tendsto (fun N' : ℕ => Real.log (N' : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max (Real.sqrt M) 1), eventually_ge_atTop 3]
    with N' hmax hN3
  have hlogpos : (0 : ℝ) < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  have hsqrt : Real.sqrt M ≤ Real.log N' := le_trans (le_max_left _ _) hmax
  have hlog1 : (1 : ℝ) ≤ Real.log N' := le_trans (le_max_right _ _) hmax
  have hNpos : (0 : ℝ) < (N' : ℝ) := by positivity
  set x := (N' : ℝ) with hx
  set R := ⌊x ^ ((1 : ℝ) / 5)⌋₊ with hR
  have hR1 : (1 : ℕ) ≤ R := by
    rw [hR]; exact Nat.le_floor (by
      rw [Nat.cast_one]; exact Real.one_le_rpow (by rw [hx]; exact_mod_cast (by omega : 1 ≤ N'))
        (by norm_num))
  have hRr1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hLRnn : (0 : ℝ) ≤ Real.log (R : ℝ) := Real.log_nonneg hRr1
  have hLRle : Real.log (R : ℝ) ≤ Real.log x / 5 := logR_upper N' (by omega)
  have hbound : (1 : ℝ) + Real.log (R : ℝ) ≤ 2 * Real.log x := by
    have hll : Real.log (R : ℝ) ≤ Real.log x := by linarith [hLRle, hlogpos]
    linarith [hll, hlog1]
  have hMsq : M ≤ (Real.log x) ^ 2 := by
    have h2 : (Real.sqrt M) ^ 2 ≤ (Real.log x) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg M) hsqrt 2
    rwa [Real.sq_sqrt hMnn] at h2
  have hpow : (1 + Real.log (R : ℝ)) ^ (2 * k₀ + 2)
      ≤ 2 ^ (2 * k₀ + 2) * (Real.log x) ^ (2 * k₀ + 2) := by
    have hle : (1 + Real.log (R : ℝ)) ^ (2 * k₀ + 2) ≤ (2 * Real.log x) ^ (2 * k₀ + 2) :=
      pow_le_pow_left₀ (by linarith) hbound (2 * k₀ + 2)
    rwa [mul_pow] at hle
  have hlogxpos : (0 : ℝ) < Real.log x := by rw [hx]; exact hlogpos
  have hlogpow_pos : (0 : ℝ) < (Real.log x) ^ (2 * k₀ + 4) := by positivity
  have hden : (Real.log x) ^ (2 * k₀ + 4) = (Real.log x) ^ (2 * k₀ + 2) * (Real.log x) ^ 2 := by
    rw [show 2 * k₀ + 4 = (2 * k₀ + 2) + 2 by omega, pow_add]
  have hkey : (k₀ : ℝ) * (C₀ * (1 + Real.log (R : ℝ)) ^ (2 * k₀ + 2) * x
        / (Real.log x) ^ (2 * k₀ + 4)) ≤ 126 * x / (W k₀ : ℝ) := by
    rw [mul_div_assoc', div_le_div_iff₀ hlogpow_pos hWpos]
    have hlpp2 : (0 : ℝ) ≤ (Real.log x) ^ (2 * k₀ + 2) := by positivity
    have hstep : (k₀ : ℝ) * C₀ * (1 + Real.log (R : ℝ)) ^ (2 * k₀ + 2) * (W k₀ : ℝ)
        ≤ 126 * (Real.log x) ^ (2 * k₀ + 4) := by
      calc (k₀ : ℝ) * C₀ * (1 + Real.log (R : ℝ)) ^ (2 * k₀ + 2) * (W k₀ : ℝ)
          ≤ (k₀ : ℝ) * C₀ * (2 ^ (2 * k₀ + 2) * (Real.log x) ^ (2 * k₀ + 2)) * (W k₀ : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hWpos.le
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((k₀ : ℝ) * C₀ * 2 ^ (2 * k₀ + 2) * (W k₀ : ℝ) / 126) * 126
              * (Real.log x) ^ (2 * k₀ + 2) := by ring
        _ ≤ (Real.log x) ^ 2 * 126 * (Real.log x) ^ (2 * k₀ + 2) := by
            apply mul_le_mul_of_nonneg_right _ hlpp2
            apply mul_le_mul_of_nonneg_right _ (by norm_num)
            rw [← hM]; exact hMsq
        _ = 126 * (Real.log x) ^ (2 * k₀ + 4) := by rw [hden]; ring
    nlinarith [hstep, hNpos]
  exact hkey

/-! ## The `S₁` conjunct with an `N`-free constant -/

/-- The `S₁` upper bound with the constant `2^{k+1}·C0` supplied externally (so it
is `N`-free, obtainable before the window base is chosen).  Body mirrors
`S1_upper_A1_uniform`. -/
lemma S1_conj_of (k K₀ N R ν₀ : ℕ) (T : ℝ) (C0 : ℝ)
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀) (hR : 2 ≤ R) (_hC0 : 0 ≤ C0)
    (hC0le : ∀ (R : ℕ), 2 ≤ R → ∀ (y : (Fin k → ℕ) → ℝ), (∀ r, |y r| ≤ 1) →
      (∑ d ∈ kSieveIndex k R (W k), |lam k R (W k) y d|) ^ 2
        ≤ C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :
    S1 k K₀ N R (W k) ν₀ (yTensor k R T)
      ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + 2 ^ (k + 1) * C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  have hsol : ∀ d ∈ kSieveIndex k R (W k), ∀ e ∈ kSieveIndex k R (W k),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i) := by
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvable k d e ν₀ hWpos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => compat_lcm_coprime k R hd he hcompat hij)
  have hfmono : ∀ d n : ℕ, d ∣ n → 0 < d → fTilde k R T n ≤ fTilde k R T d := by
    intro d n hdn hd0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : (0 : ℕ) ∉ sqfCop (R0 k R T) (W k) := by
        rw [sqfCop, Finset.mem_filter]
        rintro ⟨-, hsq, -⟩
        exact hsq.ne_zero rfl
      rw [show fTilde k R T 0 = 0 by simp only [fTilde, if_neg h0]]
      exact fTilde_nonneg k R T d hR
    · exact fTilde_anti k R T hR d n hn hdn
  have hL3 := S1_le k K₀ N R (W k) ν₀ (yTensor k R T) (fTilde k R T)
    (fun n => ⟨fTilde_nonneg k R T n hR, fTilde_le_one k R T hR n⟩) hfmono (fun r => rfl) rfl
    hk hD hK₀ hsol
  have htriv := hC0le R hR (yTensor k R T) (yTensor_abs_le_one k R T hR)
  have hyside := yside_le_A1pow k R T
  have hcoef : (0 : ℝ) ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    have h2 : (0 : ℝ) ≤ ((K₀ - 1) * N / (W k) : ℝ) :=
      div_nonneg (mul_nonneg h1 (Nat.cast_nonneg N)) (Nat.cast_nonneg _)
    linarith
  calc S1 k K₀ N R (W k) ν₀ (yTensor k R T)
      ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ)
          * (∑ r ∈ kSieveIndex k R (W k), (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R (W k), |lam k R (W k) (yTensor k R T) d|) ^ 2 :=
        hL3
    _ ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hyside hcoef)
          (mul_le_mul_of_nonneg_left htriv (by positivity))
    _ = 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + 2 ^ (k + 1) * C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

/-! ## Port-blocker (Part A): the compat main-term lower bound

Discharging the compat diagonal conjunct requires an `R`-uniform bound on the
`s2main_lower_rel`/`lemma53` constant `C` (so that `32·C·log R ≤ B₁·D₀` holds in
the sharp regime).  That constant is `R`-free in value but exposed only as an
`∃`; making it `R`-uniform and dominating it by `(φW/W)·k₀²/576` needs a
restatement of `lemma53` that is not carried out here.  We isolate exactly this
one fact: the compat main-term lower bound at large window bases. -/

/-- The compat diagonal main-term lower bound, at window parameter
`R = ⌊N'^{1/5}⌋₊`, holds eventually.  (Part-A port-blocker.) -/
def CompatFrontier (k₀ : ℕ) (T : ℝ) : Prop :=
  ∀ᶠ N' : ℕ in atTop, ∀ m : Fin k₀,
    (1 / 16 : ℝ) * (B1 k₀ (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) (W k₀) T) ^ 2
        * (A1 k₀ (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) (W k₀) T) ^ (k₀ - 1)
      ≤ s2CompatFormM k₀ (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) (W k₀) m
          (yTensor k₀ (⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊) T)

/-! ## The analytic frontier (with the sharp `k₀` floor) -/

/-- **The analytic frontier**, proved for a tuple width with the honest floor
`300 ≤ log k₀` (the sharp regime needs it; the `3072` floor of `AnalyticFrontier`
is too low — see the report).  Modulo the Part-A port-blocker `CompatFrontier`. -/
theorem analyticFrontier_holds' (k₀ : ℕ) (c : ℝ) (Nc : ℕ) (hEH : EH (1 / 2))
    (hk3072 : 3072 ≤ k₀) (hlogk : 300 ≤ Real.log k₀) (hc0 : 0 < c)
    (_hdom : (282175488 : ℝ) ≤ c * Real.log k₀)
    (hckey : ∀ N : ℕ, Nc ≤ N → c * (N : ℝ) / Real.log N
      ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ))
    (hCompat : CompatFrontier k₀ ((k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀))
    (N : ℕ) :
    ∃ (N' R ν₀ : ℕ) (T C₀ Cs : ℝ), N ≤ N' ∧ 0 < N' ∧ 0 < Real.log N' ∧
      1 ≤ A1 k₀ R (W k₀) T ∧
      (∀ m : Fin k₀,
        c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) ≤ deltaPi k₀ 64 N' m) ∧
      (∀ m : Fin k₀,
        (1 / 16 : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 * (A1 k₀ R (W k₀) T) ^ (k₀ - 1)
          ≤ s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)) ∧
      (∀ m : Fin k₀,
        deltaPi k₀ 64 N' m / (Nat.totient (W k₀) : ℝ)
            * s2CompatFormM k₀ R (W k₀) m (yTensor k₀ R T)
          - C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4)
            ≤ S2m k₀ 64 N' R ν₀ m (yTensor k₀ R T)) ∧
      (S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
          + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)) ∧
      ((Nat.totient (W k₀) / W k₀ : ℝ) * Real.log R * Real.log k₀ / 2916
        ≤ (k₀ : ℝ) * (B1 k₀ R (W k₀) T) ^ 2 / (A1 k₀ R (W k₀) T)) ∧
      (c * (N' : ℝ) / (2 * Real.log N')
        ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ)) ∧
      (Real.log N' / 6 ≤ Real.log R) ∧
      (Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2)
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) ∧
      ((k₀ : ℝ)
          * (C₀ * (1 + Real.log R) ^ (2 * k₀ + 2) * (N' : ℝ) / (Real.log N') ^ (2 * k₀ + 4))
        ≤ 126 * (N' : ℝ) / (W k₀ : ℝ)) := by
  classical
  have hk0pos : 0 < k₀ := by omega
  have hlogkpos : (0 : ℝ) < Real.log k₀ := by linarith
  have hkR : (1 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 1 < k₀)
  set T := (k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀ with hTdef
  have hTpos : (0 : ℝ) < T := by
    rw [hTdef]; positivity
  have hT1 : 1 ≤ T := T_ge_one hk0pos hlogk
  have hρpos : (0 : ℝ) < T / (k₀ : ℝ) := div_pos hTpos (by exact_mod_cast hk0pos)
  have hD : 12 * k₀ ^ 2 ≤ D₀ k₀ := by
    have h1 : (12 : ℕ) * k₀ ^ 2 ≤ k₀ ^ 3 := by
      calc 12 * k₀ ^ 2 ≤ k₀ * k₀ ^ 2 := by
            apply Nat.mul_le_mul_right; omega
        _ = k₀ ^ 3 := by ring
    exact le_trans h1 (le_max_left _ _)
  -- offsets / uniform constants (obtained before choosing N')
  obtain ⟨ν₀, hν₀⟩ := exists_nu0 k₀
  obtain ⟨C₀, N₀eh, hC₀0, hEHfun⟩ :=
    S2m_ge_compatMain_eh_uniform k₀ 64 (by omega) (by norm_num) hEH
  obtain ⟨C0s, hC0s0, hC0sle⟩ := S1_trivial_error_le'_uniform k₀ (W k₀)
  set Cs := 2 ^ (k₀ + 1) * C0s with hCsdef
  have hCs0 : 0 ≤ Cs := by rw [hCsdef]; positivity
  -- the largeness threshold (Nat)
  have hWr0 : (0 : ℝ) ≤ (W k₀ : ℝ) ^ (10 : ℕ) := by positivity
  set B : ℕ := max (2 ^ 30) (max N₀eh (max (⌈(W k₀ : ℝ) ^ (10 : ℕ)⌉₊) Nc)) with hBdef
  -- combine all eventually facts
  have hcombined := hCompat.and ((eventually_D0_le k₀ c hc0).and ((eventually_herr1 k₀ Cs hCs0).and
    ((eventually_herr2 k₀ C₀ hC₀0).and ((eventually_rho_logR_ge k₀ T (Real.log 8) hρpos).and
    ((eventually_logR_ge ((k₀ : ℝ) * Real.log k₀ * Real.log 2)).and
    ((eventually_phiW_logR_ge k₀ (errA1 k₀ (W k₀) * ((k₀ : ℝ) * Real.log k₀))).and
    ((eventually_phiW_logR_ge k₀ (18 * (k₀ : ℝ) * errB1 k₀ (W k₀))).and
    (eventually_ge_atTop B))))))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hcombined
  set N' := max N₀ N with hN'def
  have hgeN₀ : N₀ ≤ N' := le_max_left _ _
  have hNleN' : N ≤ N' := le_max_right _ _
  obtain ⟨hcompat', hD0', herr1', herr2', hrho', hlogRbig, hthrA', hthrB', hgeB⟩ :=
    hN₀ N' hgeN₀
  -- unpack the Nat threshold
  have hB1 : (2 : ℕ) ^ 30 ≤ N' := le_trans (le_max_left _ _) hgeB
  have hBN₀eh : N₀eh ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hgeB
  have hBceil : ⌈(W k₀ : ℝ) ^ (10 : ℕ)⌉₊ ≤ N' :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hgeB
  have hBNc : Nc ≤ N' :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hgeB
  have hN'2 : 2 ≤ N' := le_trans (by norm_num) hB1
  have hN'pos : 0 < N' := by omega
  have hN'r2 : (2 : ℝ) ^ 30 ≤ (N' : ℝ) := by exact_mod_cast hB1
  have h32 : (32 : ℝ) ≤ (N' : ℝ) := by
    have : (32 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    linarith [hN'r2]
  have hW10 : (W k₀ : ℝ) ^ (10 : ℕ) ≤ (N' : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hBceil
  have hlogN'pos : 0 < Real.log N' := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
  -- R and its facts
  set R := ⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ with hRdef
  have hR : 2 ≤ R := R_ge_two N' h32
  have hRleN' : R ≤ N' := R_le_N' N' (by omega)
  have hrange : W k₀ * R ^ 2 ≤ ⌊(N' : ℝ) ^ ((1 : ℝ) / 2)⌋₊ := EH_range k₀ N' hW10 (by omega)
  -- sharp-regime atoms
  have hρR : Real.log 8 ≤ T / (k₀ : ℝ) * Real.log (R : ℝ) := hrho'
  have hX : 4 ≤ R0 k₀ R T := R0_ge_four k₀ R T hR hρR
  have hblog2 : bParam k₀ R * Real.log 2 ≤ 1 := bParam_log2_le k₀ R (by omega) hR hlogRbig
  have hbLo : (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) :=
    hbLo_of k₀ R T hk3072 hR hlogk hTdef hρR hblog2
  have hEA_r := hEA_ratio_of k₀ R (by omega) hR hthrA'
  have hEB_r := hEB_ratio_of k₀ R (by omega) hR hthrB'
  -- conjuncts
  refine ⟨N', R, ν₀, T, C₀, Cs, hNleN', hN'pos, hlogN'pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1 ≤ A1
    exact A1_ge_one k₀ R T (by omega)
  · -- hDpi
    intro m
    have hd := deltaPi_lower_of k₀ c Nc hckey m N' hBNc
    have hhs : (hSeq k₀ m : ℝ) ≤ (D₀ k₀ : ℝ) := by exact_mod_cast hSeq_le_D₀ k₀ m
    linarith [hd, hhs]
  · -- hcompat (port-blocker)
    exact hcompat'
  · -- hEHres
    intro m
    exact hEHfun R ν₀ T hR hν₀ N' hBN₀eh hRleN' hrange m
  · -- hS1
    have hS1' := S1_conj_of k₀ 64 N' R ν₀ T C0s (by omega) hD (by norm_num) hR hC0s0 hC0sle
    calc S1 k₀ 64 N' R (W k₀) ν₀ (yTensor k₀ R T)
        ≤ 2 * ((64 - 1) * N' / (W k₀) : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
            + 2 ^ (k₀ + 1) * C0s * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2) := hS1'
      _ = 126 * (N' : ℝ) / (W k₀ : ℝ) * (A1 k₀ R (W k₀) T) ^ k₀
            + Cs * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k₀ + 2) := by rw [hCsdef]; ring
  · -- hratio
    exact ratio_core_lower k₀ R T (by omega) hR hTdef hT1 hX hbLo hEA_r hEB_r
  · -- hδlb
    have hhalf : c * (N' : ℝ) / Real.log N' - c * (N' : ℝ) / (2 * Real.log N')
        = c * (N' : ℝ) / (2 * Real.log N') := by
      field_simp; ring
    linarith [hD0', hhalf.le, hhalf.ge]
  · -- hlogR
    exact logR_lower N' hN'r2
  · -- herr1
    exact herr1'
  · -- herr2
    exact herr2'

/-! ## The unconditional capstone (modulo the Part-A port-blocker) -/

/-- **M7 — bounded gaps from Elliott–Halberstam.**  Assembled from
`analyticFrontier_holds'` via `bounded_gaps_reduces` + `win_core`, choosing the
tuple width `k₀` large enough for both the dominance threshold and the sharp
regime `300 ≤ log k₀`.  Carries the single Part-A port-blocker `hCompat`
(the compat main-term lower bound, universal over the `k₀`-regime). -/
theorem bounded_gaps_from_eh_final
    (hCompat : ∀ k₀ : ℕ, 3072 ≤ k₀ → 300 ≤ Real.log k₀ →
      CompatFrontier k₀ ((k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀)) :
    BoundedGapsFromEH := by
  intro hEH
  obtain ⟨c, Nc, hc0, hckey⟩ := primes_in_interval_ge
  set k₀ := max (max 3072 ⌈Real.exp (282175488 / c)⌉₊) ⌈Real.exp 300⌉₊ with hk₀def
  have hk3072 : 3072 ≤ k₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hlogk : (300 : ℝ) ≤ Real.log k₀ := by
    have h1 : Real.exp 300 ≤ (k₀ : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_max_right _ _
    have h2 : Real.log (Real.exp 300) ≤ Real.log k₀ := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hdom : (282175488 : ℝ) ≤ c * Real.log k₀ := by
    have hM : (282175488 : ℝ) / c ≤ Real.log k₀ := by
      have h1 : Real.exp (282175488 / c) ≤ (k₀ : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        have : (⌈Real.exp (282175488 / c)⌉₊ : ℝ) ≤ (k₀ : ℝ) := by
          exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
        exact this
      have h2 : Real.log (Real.exp (282175488 / c)) ≤ Real.log k₀ :=
        Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have h := mul_le_mul_of_nonneg_left hM hc0.le
    have e : c * (282175488 / c) = 282175488 := by field_simp
    linarith [h, e.le, e.ge]
  refine bounded_gaps_reduces k₀ (fun N => ?_)
  obtain ⟨N', R, ν₀, T, C₀, Cs, hNleN', hNpos, hlogNpos, hA1ge1, hDpi, hcompat,
    hEHres, hS1, hratio, hδlb, hlogR, herr1, herr2⟩ :=
    analyticFrontier_holds' k₀ c Nc hEH hk3072 hlogk hc0 hdom hckey
      (hCompat k₀ hk3072 hlogk) N
  have hδ0 : 0 ≤ c * (N' : ℝ) / Real.log N' - (D₀ k₀ : ℝ) :=
    le_trans (by positivity) hδlb
  refine ⟨N', R, ν₀, yTensor k₀ R T, hNleN', ?_⟩
  exact win_core k₀ N' R ν₀ T c C₀ Cs (by omega) hNpos hlogNpos hc0 hδ0 hA1ge1
    hDpi hcompat hEHres hS1 hratio hδlb hlogR hdom herr1 herr2

end Salt.Maynard
