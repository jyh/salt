/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.LevelRange
import Salt.Maynard.FrontierDischarge

/-!
# B4.5c helpers — vanishing rates at `R = ⌊N'^{9999/40000}⌋₊` (C1, k = 105)

Public ports of the private vanishing-rate helpers of `Salt/Twelve/GapsUncond.lean`
(there at `R = ⌊N'^{1999/4000}⌋₊`) to the window exponent `ρ = 9999/40000`, with the
level-`1/2` range facts of `LevelRange` (`R_ge_two_rho`, threshold 32; `R_sq_le_half`).

`eventually_DL_105` is the `Δπ` pinning: with the log-`R` pin
`4999/20000` and `c_DL = 15746/1000`, `c_DL · N' ≤ δ · log R` eventually, where
`δ = (63 − 1/1000)·N'/log N' − 743`. Nothing here bears on twin primes.
-/

namespace Salt.MaynardK

open Finset Filter Topology
open Salt.Maynard Salt.MaynardK

lemma eventually_logN_ge_rho (M : ℝ) : ∀ᶠ N' : ℕ in atTop, M ≤ Real.log N' :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

lemma eventually_logR_ge_rho (b : ℝ) :
    ∀ᶠ N' : ℕ in atTop, b ≤ Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by
  filter_upwards [eventually_logR_lower_rho (1/8) (by norm_num) (by norm_num),
    eventually_logN_ge_rho (8 * b)] with N' h1 h2
  linarith

lemma eventually_div_logR_le_rho (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N' : ℕ in atTop,
      C / Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ≤ ε := by
  filter_upwards [eventually_logR_ge_rho (max C 1 / ε), eventually_logR_ge_rho 1] with N' hge hpos
  set L := Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  rw [div_le_iff₀ hLpos]
  have hCle : C ≤ max C 1 := le_max_left _ _
  have h2 : max C 1 / ε ≤ L := hge
  calc C ≤ max C 1 := hCle
    _ = (max C 1 / ε) * ε := by field_simp
    _ ≤ L * ε := mul_le_mul_of_nonneg_right h2 hε.le
    _ = ε * L := by ring

lemma eventually_polylog_ratio_le_rho (p q : ℕ) (A K : ℝ) (hpq : p < q)
    (hK : 0 < K) (hA : 0 ≤ A) :
    ∀ᶠ N' : ℕ in atTop,
      A * (1 + Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ)) ^ p / (Real.log N') ^ q
        ≤ K := by
  filter_upwards [eventually_logN_ge_rho (max 1 (2 ^ p * A / K)), eventually_ge_atTop 32]
    with N' hlogN hN32
  have hlog1 : (1 : ℝ) ≤ Real.log N' := le_trans (le_max_left _ _) hlogN
  have hlogNpos : 0 < Real.log N' := by linarith
  set R := ⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ with hRdef
  have hRleN : R ≤ N' := R_le_N'_rho N' (by omega)
  have hR2 : 2 ≤ R := R_ge_two_rho N' (by exact_mod_cast hN32)
  have hlogRle : Real.log R ≤ Real.log N' := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < R)
    · exact_mod_cast hRleN
  have hlogRnn : 0 ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hbase : 1 + Real.log R ≤ 2 * Real.log N' := by linarith
  have hbasenn : 0 ≤ 1 + Real.log R := by linarith
  have hpow : (1 + Real.log R) ^ p ≤ 2 ^ p * (Real.log N') ^ p := by
    calc (1 + Real.log R) ^ p ≤ (2 * Real.log N') ^ p :=
          pow_le_pow_left₀ hbasenn hbase p
      _ = 2 ^ p * (Real.log N') ^ p := by rw [mul_pow]
  have hqp : 1 ≤ q - p := by omega
  have hLqp : (Real.log N') ^ (q - p) ≥ Real.log N' := by
    calc Real.log N' = (Real.log N') ^ 1 := (pow_one _).symm
      _ ≤ (Real.log N') ^ (q - p) := pow_le_pow_right₀ hlog1 hqp
  have hThr : 2 ^ p * A / K ≤ Real.log N' := le_trans (le_max_right _ _) hlogN
  rw [div_le_iff₀ (by positivity)]
  have hsplit : (Real.log N') ^ q = (Real.log N') ^ p * (Real.log N') ^ (q - p) := by
    rw [← pow_add]; congr 1; omega
  have hAle : A * (2 ^ p * (Real.log N') ^ p)
      ≤ K * ((Real.log N') ^ p * (Real.log N') ^ (q - p)) := by
    have h1 : A * 2 ^ p ≤ K * (Real.log N') ^ (q - p) := by
      have : A * 2 ^ p ≤ K * Real.log N' := by
        rw [mul_comm A (2^p)]
        have := (div_le_iff₀ hK).mp hThr
        linarith only [this]
      nlinarith only [hK, hLqp, this]
    nlinarith only [h1, pow_nonneg hlogNpos.le p]
  calc A * (1 + Real.log R) ^ p
      ≤ A * (2 ^ p * (Real.log N') ^ p) := mul_le_mul_of_nonneg_left hpow hA
    _ ≤ K * ((Real.log N') ^ p * (Real.log N') ^ (q - p)) := hAle
    _ = K * (Real.log N') ^ q := by rw [← hsplit]

lemma eventually_poly_o_linear_rho (n : ℕ) (K C : ℝ) (hK : 0 < K) (hC : 0 ≤ C) :
    ∀ᶠ N' : ℕ in atTop,
      C * (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) ^ 2
          * (1 + Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ)) ^ n
        ≤ K * (N':ℝ) := by
  have hev := eventually_poly_beats_polylog n (20002 / 40000) (C / K) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 32] with N' hpoly hN32
  set R := ⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ with hRdef
  have hN1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hNpos : (0:ℝ) < (N':ℝ) := by linarith
  have hR2n : 2 ≤ R := R_ge_two_rho N' (by exact_mod_cast hN32)
  have hRleN : R ≤ N' := R_le_N'_rho N' (by omega)
  have hRsq : (R:ℝ) ^ 2 ≤ (N':ℝ) ^ (19998 / 40000 : ℝ) := R_sq_le_half N' (by omega)
  have hlogRle : Real.log R ≤ Real.log N' :=
    Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < R)) (by exact_mod_cast hRleN)
  have hlogRnn : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hpolylog : (1 + Real.log R) ^ n ≤ (1 + Real.log N') ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) n
  have hpolyK : C * (1 + Real.log N') ^ n ≤ K * (N':ℝ) ^ (20002 / 40000 : ℝ) := by
    have h := hpoly
    rw [div_mul_eq_mul_div, div_le_iff₀ hK] at h
    linarith [h]
  have hrpow : (N':ℝ) ^ (19998 / 40000 : ℝ) * (N':ℝ) ^ (20002 / 40000 : ℝ) = (N':ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hRsqnn : 0 ≤ (N':ℝ) ^ (19998 / 40000 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hCpolyR_nn : 0 ≤ C * (1 + Real.log R) ^ n := by positivity
  calc C * (R:ℝ) ^ 2 * (1 + Real.log R) ^ n
      = (C * (1 + Real.log R) ^ n) * (R:ℝ) ^ 2 := by ring
    _ ≤ (C * (1 + Real.log R) ^ n) * (N':ℝ) ^ (19998 / 40000 : ℝ) :=
        mul_le_mul_of_nonneg_left hRsq hCpolyR_nn
    _ ≤ (C * (1 + Real.log N') ^ n) * (N':ℝ) ^ (19998 / 40000 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpolylog hC) hRsqnn
    _ ≤ (K * (N':ℝ) ^ (20002 / 40000 : ℝ)) * (N':ℝ) ^ (19998 / 40000 : ℝ) :=
        mul_le_mul_of_nonneg_right hpolyK hRsqnn
    _ = K * ((N':ℝ) ^ (19998 / 40000 : ℝ) * (N':ℝ) ^ (20002 / 40000 : ℝ)) := by ring
    _ = K * (N':ℝ) := by rw [hrpow]

lemma eventually_R_ge_rho (Rb : ℕ) :
    ∀ᶠ N' : ℕ in atTop, Rb ≤ ⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ := by
  have htend : Tendsto (fun N' : ℕ => (N':ℝ) ^ (9999 / 40000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (Rb:ℝ)] with N' h
  exact Nat.le_floor h

/-- `δ = (63 − 1/1000)·N'/log N' − 743 ≥ 0` eventually. -/
lemma delta_nonneg_105 :
    ∀ᶠ N' : ℕ in atTop, 0 ≤ (63 - 1 / 1000) * (N':ℝ) / Real.log N' - 743 := by
  have hbeat := eventually_poly_beats_polylog 1 1 310000 (by norm_num)
  have hbeatN := tendsto_natCast_atTop_atTop.eventually hbeat
  filter_upwards [hbeatN, eventually_ge_atTop 2] with N' hbeat hN2
  have hN1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hL : 0 < Real.log (N':ℝ) := Real.log_pos hN1
  simp only [pow_one, Real.rpow_one] at hbeat
  rw [sub_nonneg, le_div_iff₀ hL]
  linarith only [hbeat, hL]

/-- The `Δπ` lower-bound pinning `(15746/1000)·N' ≤ δ·log R` at k = 105 (v2 §2). -/
lemma eventually_DL_105 :
    ∀ᶠ N' : ℕ in atTop,
      (15746 : ℝ) / 1000 * N'
        ≤ ((63 - 1 / 1000) * (N':ℝ) / Real.log N' - 743)
            * Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) := by
  have hpin := eventually_logR_lower_rho (4999 / 20000) (by norm_num) (by norm_num)
  have hbeat := eventually_poly_beats_polylog 1 1 310000 (by norm_num)
  have hbeatN := tendsto_natCast_atTop_atTop.eventually hbeat
  filter_upwards [hpin, hbeatN, eventually_ge_atTop 2] with N' hpin hbeat hN2
  set L := Real.log (N':ℝ) with hLdef
  set LR := Real.log (⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ : ℝ) with hLRdef
  have hN1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hL : 0 < L := Real.log_pos hN1
  simp only [pow_one, Real.rpow_one] at hbeat
  -- hbeat : 310000 * (1 + L) ≤ N'
  have hδ0 : 0 ≤ (63 - 1 / 1000) * (N':ℝ) / L - 743 := by
    rw [sub_nonneg, le_div_iff₀ hL]
    linarith only [hbeat, hL]
  set δ : ℝ := (63 - 1 / 1000) * (N':ℝ) / L - 743 with hδdef
  have hδL : δ * L = (63 - 1 / 1000) * (N':ℝ) - 743 * L := by
    rw [hδdef]; field_simp
  have hstep : δ * (4999 / 20000 * L) ≤ δ * LR :=
    mul_le_mul_of_nonneg_left hpin hδ0
  have hkey : δ * (4999 / 20000 * L) = 4999 / 20000 * ((63 - 1 / 1000) * (N':ℝ) - 743 * L) := by
    rw [show δ * (4999 / 20000 * L) = 4999 / 20000 * (δ * L) by ring, hδL]
  rw [hkey] at hstep
  linarith only [hstep, hbeat, hL]


end Salt.MaynardK
