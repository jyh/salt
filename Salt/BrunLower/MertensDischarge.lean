/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.WRatio
import Salt.BrunLower.MertensWindow
import Salt.Brun.Sieve

/-!
# The twin `hMert` discharge (blueprint `p0`, node PM2)

Discharges the density-ratio hypothesis `hMert` of `Wratio_le_exp`/`windowSum_le`
(node B3b, `Salt/BrunLower/WRatio.lean`) at the twin instance, following H-R's
p.104–106 argument with the explicit ladder scale (2.18)
`Λ = λ·(1 − B₁/loglog z)` (H-R's `(2λ/A)(1+B₁/loglog z)⁻¹` at `A = 2`, subtractive
form). `Halberstam–Richert, "A new look at Brun's sieve", Mém. SMF 25 (1971) 97–106`.

## The route (all constants owned here)

For a `BoundingSieve` whose sifting densities obey `ν(2) ≤ 1/2`, `ν(p) ≤ 2/p` (odd `p`)
— exactly the twin values `ρ(2)/2 = 1/2`, `ρ(p)/p = 2/p` — and whose sifting primes are
all `< z`:

1. **Pointwise** (`neg_log_one_sub_nu_le`): `−log(1−ν(p)) ≤ 2/p + 12/p²`.  For odd `p`,
   `−log(1−ν(p)) ≤ −log(1−2/p) ≤ (2/p)/(1−2/p) = 2/(p−2) = 2/p + 4/(p(p−2)) ≤ 2/p + 12/p²`
   (the quadratic slack via `−log(1−x) ≤ x/(1−x)`, i.e. `log t ≤ t−1` at `t = (1−x)⁻¹`);
   for `p = 2`, `−log(1−ν(2)) ≤ log 2 ≤ 1 = 2/2`.
2. **Ladder + PM1** (`log_Wratio_le_ladder`): summing, the main term `2·Σ 1/p` is bounded
   by PM1 (`sum_inv_le_of_prime_window`, `C₃ = 19`) at the window base `w_n = max(z_n, 2)`,
   whose `log(log z/log w_n) ≤ nΛ` is the ladder identity; the quadratic tail `12·Σ 1/p²`
   telescopes to `≤ 12/(w_n−1) ≤ 12/log w_n`.  Total decaying budget `C₄ = 50`:
   `log(Wratio) ≤ 2nΛ + 50·e^{nΛ}/log z`  (this is the uniform "step-3" bound).
3. **Endpoint convexity** (`exp_mul_le_max_mul`): `e^{nΛ} ≤ M·n` on `[1, r]` with
   `M = max(e^Λ, e^{rΛ}/r)`, from convexity of `exp` (the U-shape `e^{nΛ}/n` peaks at the
   endpoints); `M` is bounded by the (2.14) minimality of `r = minLevel`.
4. **The Λ-gap close** (`hMert_twin`): the budget `2n(λ−Λ) = 2nλ·B₁/loglog z` swallows
   `50·M·n/log z` once `z ≥ z₀ = exp(exp(100/λ))` and `B₁ = 120`, giving
   `log(Wratio) ≤ 2nλ`.

`z₀` is astronomical (`exp(exp(400))` at `λ = 1/4`) — expected and harmless: B5 is stated
hypothesis-parameterized, and the level gate `u(Λ) → 10.08⁺` survives (see `p0.md` PM2).
-/

open Finset
open scoped BigOperators

namespace Salt.BrunLower

open BoundingSieve

/-! ## The ladder scale (2.18) and the astronomical threshold -/

/-- H-R's (2.18) ladder scale at the twin instance (`A = 2`), subtractive form:
`Λ(z) = λ·(1 − B₁/loglog z)` with `B₁ = 120` explicit.  Strictly below the nominal `λ`,
rising to it as `z → ∞`. -/
noncomputable def LamTwin (lam z : ℝ) : ℝ := lam * (1 - 120 / Real.log (Real.log z))

/-- The explicit `z`-threshold `z₀ = exp(exp(100/λ))` above which (2.18) is valid and the
Λ-gap close holds.  Astronomical by design (H-R's "z large"). -/
noncomputable def zThresh (lam : ℝ) : ℝ := Real.exp (Real.exp (100 / lam))

/-! ## Threshold-derived facts on `z` -/

/-- `log z ≥ exp(100/λ)` for `z ≥ z₀` (`λ > 0`). -/
lemma logz_ge {lam z : ℝ} (hz : zThresh lam ≤ z) :
    Real.exp (100 / lam) ≤ Real.log z := by
  have he1 : (0:ℝ) < Real.exp (Real.exp (100 / lam)) := Real.exp_pos _
  have := Real.log_le_log he1 hz
  rwa [Real.log_exp] at this

/-- `loglog z ≥ 100/λ` for `z ≥ z₀` (`λ > 0`). -/
lemma loglog_ge {lam z : ℝ} (hz : zThresh lam ≤ z) :
    100 / lam ≤ Real.log (Real.log z) := by
  have hexppos : (0:ℝ) < Real.exp (100 / lam) := Real.exp_pos _
  have := Real.log_le_log hexppos (logz_ge hz)
  rwa [Real.log_exp] at this

/-- The bundle of `z`-facts used by the close (`z ≥ z₀`, `0 < λ ≤ 1/4`). -/
lemma zThresh_facts {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) :
    100 / lam ≤ Real.log (Real.log z) ∧ (400:ℝ) ≤ Real.log (Real.log z) ∧
      0 < Real.log z ∧ 0 < Real.log (Real.log z) ∧
      Real.log z = Real.exp (Real.log (Real.log z)) ∧
      25 * Real.log (Real.log z) ≤ lam * Real.log z ∧ (2:ℝ) ≤ z := by
  have hlogz_ge : Real.exp (100 / lam) ≤ Real.log z := logz_ge hz
  have hexp100pos : (0:ℝ) < Real.exp (100 / lam) := Real.exp_pos _
  have hlz_pos : 0 < Real.log z := lt_of_lt_of_le hexp100pos hlogz_ge
  have hllz : 100 / lam ≤ Real.log (Real.log z) := loglog_ge hz
  have h400 : (400:ℝ) ≤ Real.log (Real.log z) := by
    have : (400:ℝ) ≤ 100 / lam := by
      rw [le_div_iff₀ hlam]; nlinarith [hlam']
    linarith
  have hllz_pos : 0 < Real.log (Real.log z) := by linarith
  have hlz_eq : Real.log z = Real.exp (Real.log (Real.log z)) := (Real.exp_log hlz_pos).symm
  -- log z = exp(loglog z) ≥ (loglog z)²/4
  have hexpge : (Real.log (Real.log z))^2 / 4 ≤ Real.exp (Real.log (Real.log z)) := by
    have h := Real.add_one_le_exp (Real.log (Real.log z) / 2)
    have hexppos : 0 < Real.exp (Real.log (Real.log z) / 2) := Real.exp_pos _
    have h2 : (1 + Real.log (Real.log z) / 2)^2 ≤ (Real.exp (Real.log (Real.log z) / 2))^2 := by
      apply sq_le_sq' <;> nlinarith [hexppos, hllz_pos]
    have h3 : (Real.exp (Real.log (Real.log z) / 2))^2 = Real.exp (Real.log (Real.log z)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    nlinarith [h2, h3, hllz_pos]
  have hquad : (Real.log (Real.log z))^2 / 4 ≤ Real.log z := by linarith [hexpge, hlz_eq]
  have hkey : 25 * Real.log (Real.log z) ≤ lam * Real.log z := by
    have h100 : (100:ℝ) ≤ Real.log (Real.log z) * lam := (div_le_iff₀ hlam).mp hllz
    have hprod : 25 * Real.log (Real.log z) ≤ lam * ((Real.log (Real.log z))^2 / 4) := by
      nlinarith [h100, hllz_pos]
    linarith [mul_le_mul_of_nonneg_left hquad hlam.le, hprod]
  have hz2 : (2:ℝ) ≤ z := by
    have h1 : (1:ℝ) ≤ Real.exp (100 / lam) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
    have h2t : (2:ℝ) ≤ Real.exp (Real.exp (100 / lam)) := by
      calc (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
        _ ≤ Real.exp (Real.exp (100 / lam)) := Real.exp_le_exp.mpr h1
    have hzu : Real.exp (Real.exp (100 / lam)) ≤ z := hz
    linarith [h2t, hzu]
  exact ⟨hllz, h400, hlz_pos, hllz_pos, hlz_eq, hkey, hz2⟩

/-- **Support lemma**: `0 < LamTwin lam z` for `z ≥ z₀`. -/
lemma LamTwin_pos {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) : 0 < LamTwin lam z := by
  obtain ⟨_, h400, _, hllz_pos, _, _, _⟩ := zThresh_facts hlam hlam' hz
  rw [LamTwin]
  apply mul_pos hlam
  have hlt : 120 / Real.log (Real.log z) < 1 := by
    rw [div_lt_one hllz_pos]; linarith
  linarith

/-- **Support lemma**: `LamTwin lam z ≤ lam` for `z ≥ z₀`. -/
lemma LamTwin_le_lam {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) : LamTwin lam z ≤ lam := by
  obtain ⟨_, _, _, hllz_pos, _, _, _⟩ := zThresh_facts hlam hlam' hz
  rw [LamTwin]
  have : 0 ≤ 120 / Real.log (Real.log z) := by positivity
  nlinarith [hlam.le, this]

/-- **Support lemma**: `LamTwin lam z ≤ 1` for `z ≥ z₀` (uses `λ ≤ 1/4`). -/
lemma LamTwin_le_one {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) : LamTwin lam z ≤ 1 :=
  le_trans (LamTwin_le_lam hlam hlam' hz) (by linarith)

/-- The gap `λ − Λ = λ·B₁/loglog z` (exact). -/
lemma lam_sub_LamTwin {lam z : ℝ} : lam - LamTwin lam z = lam * 120 / Real.log (Real.log z) := by
  rw [LamTwin]; ring

/-! ## Step 1 — the pointwise bound `−log(1−ν(p)) ≤ 2/p + 12/p²` -/

/-- **Pointwise bound.** For a sifting prime `p` with `ν(2) ≤ 1/2`, `ν(p) ≤ 2/p` (odd `p`):
`−log(1−ν(p)) ≤ 2/p + 12/p²`. -/
lemma neg_log_one_sub_nu_le (s : BoundingSieve) {p : ℕ}
    (hmem : p ∈ s.prodPrimes.primeFactors)
    (hnu2 : (2 : ℕ) ∈ s.prodPrimes.primeFactors → s.nu 2 ≤ 1 / 2)
    (hnuodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 → s.nu q ≤ 2 / q) :
    - Real.log (1 - s.nu p) ≤ 2 / (p:ℝ) + 12 / (p:ℝ)^2 := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
  have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hmem
  have hnupos : 0 < s.nu p := s.nu_pos_of_prime p hp hdvd
  have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hp hdvd
  by_cases hp2 : p = 2
  · subst hp2
    have hnu : s.nu 2 ≤ 1/2 := hnu2 hmem
    have h12 : (1:ℝ)/2 ≤ 1 - s.nu 2 := by linarith
    have hlog : Real.log ((1:ℝ)/2) ≤ Real.log (1 - s.nu 2) :=
      Real.log_le_log (by norm_num) h12
    rw [show (1:ℝ)/2 = 2⁻¹ by norm_num, Real.log_inv] at hlog
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have hR : (2:ℝ) / ((2:ℕ):ℝ) + 12 / ((2:ℕ):ℝ)^2 = 4 := by norm_num
    rw [hR]; linarith
  · -- odd prime, p ≥ 3
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hnu : s.nu p ≤ 2 / (p:ℝ) := hnuodd p hmem hp2
    have hpp : (0:ℝ) < (p:ℝ) := by linarith
    have h2p : 2 / (p:ℝ) < 1 := by rw [div_lt_one hpp]; linarith
    -- monotone: -log(1-ν) ≤ -log(1-2/p)
    have hmono : - Real.log (1 - s.nu p) ≤ - Real.log (1 - 2 / (p:ℝ)) := by
      have h1 : (0:ℝ) < 1 - 2 / (p:ℝ) := by linarith
      have h2 : 1 - 2 / (p:ℝ) ≤ 1 - s.nu p := by linarith
      have := Real.log_le_log h1 h2
      linarith
    have hpm2 : (0:ℝ) < (p:ℝ) - 2 := by linarith
    -- -log(1-2/p) ≤ (1-2/p)⁻¹ - 1 = 2/(p-2)
    have hquad : - Real.log (1 - 2/(p:ℝ)) ≤ 2 / ((p:ℝ) - 2) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - 2/(p:ℝ))⁻¹ by positivity)
      rw [Real.log_inv] at h
      have he : (1 - 2/(p:ℝ))⁻¹ - 1 = 2 / ((p:ℝ) - 2) := by
        rw [show (1:ℝ) - 2/(p:ℝ) = ((p:ℝ) - 2)/(p:ℝ) by field_simp, inv_div]
        rw [div_sub_one hpm2.ne', show (p:ℝ) - ((p:ℝ)-2) = 2 by ring]
      linarith [he ▸ h]
    -- 2/(p-2) = 2/p + 4/(p(p-2)) ≤ 2/p + 12/p²
    have hsplit : 2 / ((p:ℝ) - 2) = 2 / (p:ℝ) + 4 / ((p:ℝ) * ((p:ℝ) - 2)) := by
      field_simp; ring
    have htail : 4 / ((p:ℝ) * ((p:ℝ) - 2)) ≤ 12 / (p:ℝ)^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hpR]
    calc - Real.log (1 - s.nu p)
        ≤ - Real.log (1 - 2/(p:ℝ)) := hmono
      _ ≤ 2 / ((p:ℝ) - 2) := hquad
      _ = 2 / (p:ℝ) + 4 / ((p:ℝ) * ((p:ℝ) - 2)) := hsplit
      _ ≤ 2 / (p:ℝ) + 12 / (p:ℝ)^2 := by linarith [htail]

/-! ## The quadratic-tail telescoping `Σ 1/m² ≤ 1/(M−1)` -/

/-- Telescoping: `Σ_{m=M}^{K} (1/(m−1) − 1/m) = 1/(M−1) − 1/K` for `2 ≤ M ≤ K`. -/
lemma sum_telescope {M : ℕ} (hM : 2 ≤ M) : ∀ K, M ≤ K →
    ∑ m ∈ Finset.Icc M K, ((1:ℝ)/((m:ℝ) - 1) - 1/(m:ℝ)) = 1/((M:ℝ)-1) - 1/(K:ℝ) := by
  intro K
  induction K with
  | zero => omega
  | succ K ih =>
    intro hMK
    rcases Nat.lt_or_ge M (K+1) with hlt | hge
    · have hMKle : M ≤ K := by omega
      rw [Finset.sum_Icc_succ_top (by omega : M ≤ K + 1), ih hMKle]
      push_cast
      rw [show ((K:ℝ)+1-1) = (K:ℝ) from by ring]
      ring
    · have hMe : M = K + 1 := by omega
      subst hMe
      rw [Finset.Icc_self, Finset.sum_singleton]

/-- `Σ_{m ∈ Icc M K} 1/m² ≤ 1/(M−1)` for `2 ≤ M`. -/
lemma sum_one_div_sq_le {M K : ℕ} (hM : 2 ≤ M) :
    ∑ m ∈ Finset.Icc M K, (1:ℝ)/(m:ℝ)^2 ≤ 1/((M:ℝ) - 1) := by
  have hM1 : (0:ℝ) < (M:ℝ) - 1 := by
    have : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  rcases Nat.lt_or_ge K M with hMK | hMK
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hle : ∑ m ∈ Finset.Icc M K, (1:ℝ)/(m:ℝ)^2
        ≤ ∑ m ∈ Finset.Icc M K, ((1:ℝ)/((m:ℝ)-1) - 1/(m:ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast le_trans hM hm.1
      have hm0 : (0:ℝ) < (m:ℝ) := by linarith
      have hm10 : (0:ℝ) < (m:ℝ) - 1 := by linarith
      have hid : (1:ℝ)/((m:ℝ)-1) - 1/(m:ℝ) = 1/((m:ℝ)*((m:ℝ)-1)) := by
        field_simp; ring
      rw [hid]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hm2]
    calc ∑ m ∈ Finset.Icc M K, (1:ℝ)/(m:ℝ)^2
        ≤ ∑ m ∈ Finset.Icc M K, ((1:ℝ)/((m:ℝ)-1) - 1/(m:ℝ)) := hle
      _ = 1/((M:ℝ)-1) - 1/(K:ℝ) := sum_telescope hM K hMK
      _ ≤ 1/((M:ℝ)-1) := by
          have : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
          linarith

/-! ## Step 2 — the uniform ladder bound `log(Wratio) ≤ 2nΛ + 50·e^{nΛ}/log z` -/

/-- **Step-3 (uniform ladder) bound.**  `log(W(z_n)/W(z)) ≤ 2nΛ + 50·e^{nΛ}/log z` for all
`n ≥ 1`, from the pointwise bound, the ladder identity `log(log z/log z_n) = nΛ`, PM1
(`sum_inv_le_of_prime_window`, `C₃ = 19`) for the main term, and telescoping for the tail.
Generic in `Lam` (`0 ≤ Lam`). -/
lemma log_Wratio_le_ladder (s : BoundingSieve) {Lam z : ℝ} {n : ℕ}
    (hLam : 0 ≤ Lam) (hz2 : 2 ≤ z)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hnu2 : (2 : ℕ) ∈ s.prodPrimes.primeFactors → s.nu 2 ≤ 1 / 2)
    (hnuodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 → s.nu q ≤ 2 / q) :
    Real.log (Wratio s Lam z n) ≤ 2 * (n:ℝ) * Lam + 50 * Real.exp ((n:ℝ) * Lam) / Real.log z := by
  set W := max (zLev Lam z n) 2 with hW
  have hz1 : (1:ℝ) < z := by linarith
  have hzpos : (0:ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hznpos : 0 < zLev Lam z n := Real.exp_pos _
  have hW2 : (2:ℝ) ≤ W := le_max_right _ _
  have hWzn : zLev Lam z n ≤ W := le_max_left _ _
  have hWpos : (0:ℝ) < W := by linarith
  have hlogW : 0 < Real.log W := Real.log_pos (by linarith)
  -- z_n ≤ z
  have hznz : zLev Lam z n ≤ z := by
    have := (zLev_antitone hLam (by linarith : (1:ℝ) ≤ z)) (Nat.zero_le n)
    rwa [zLev_zero Lam z hzpos] at this
  have hWz : W ≤ z := max_le hznz hz2
  -- log z_n = e^{-nΛ} log z
  have hlogzn : Real.log (zLev Lam z n) = Real.exp (-((n:ℝ) * Lam)) * Real.log z := by
    rw [zLev, Real.log_exp]
  -- log W ≥ log z_n
  have hlogWge : Real.log (zLev Lam z n) ≤ Real.log W := Real.log_le_log hznpos hWzn
  -- 1/log W ≤ e^{nΛ}/log z
  have hinvW : 1 / Real.log W ≤ Real.exp ((n:ℝ) * Lam) / Real.log z := by
    have hb : Real.exp (-((n:ℝ) * Lam)) * Real.log z ≤ Real.log W := by
      rw [← hlogzn]; exact hlogWge
    have hbpos : 0 < Real.exp (-((n:ℝ) * Lam)) * Real.log z := by positivity
    have h1 : 1 / Real.log W ≤ 1 / (Real.exp (-((n:ℝ) * Lam)) * Real.log z) :=
      one_div_le_one_div_of_le hbpos hb
    have h2 : 1 / (Real.exp (-((n:ℝ) * Lam)) * Real.log z)
        = Real.exp ((n:ℝ) * Lam) / Real.log z := by
      rw [Real.exp_neg]
      field_simp
    rwa [h2] at h1
  -- log(log z/log W) ≤ nΛ
  have hlog_ratio : Real.log (Real.log z / Real.log W) ≤ (n:ℝ) * Lam := by
    have hratio_pos : 0 < Real.log z / Real.log W := by positivity
    have hle : Real.log z / Real.log W ≤ Real.exp ((n:ℝ) * Lam) := by
      rw [div_le_iff₀ hlogW]
      have : Real.exp ((n:ℝ) * Lam) * Real.log W ≥ Real.exp ((n:ℝ) * Lam)
          * (Real.exp (-((n:ℝ) * Lam)) * Real.log z) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [← hlogzn]; exact hlogWge
      have hcancel : Real.exp ((n:ℝ) * Lam) * (Real.exp (-((n:ℝ) * Lam)) * Real.log z)
          = Real.log z := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [hcancel] at this
      linarith
    calc Real.log (Real.log z / Real.log W)
        ≤ Real.log (Real.exp ((n:ℝ) * Lam)) := Real.log_le_log hratio_pos hle
      _ = (n:ℝ) * Lam := Real.log_exp _
  -- the window as a prime set
  have hwindow_sub : ∀ q ∈ windowPrimes s Lam z n, Nat.Prime q ∧ W ≤ (q:ℝ) ∧ (q:ℝ) < z := by
    intro q hq
    rw [windowPrimes, Finset.mem_filter] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    have hqmem : q ∈ s.prodPrimes.primeFactors := hq.1
    refine ⟨hqp, ?_, hp q hqmem⟩
    have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqp.two_le
    exact max_le hq.2 hq2
  -- MAIN TERM: 2·Σ 1/p ≤ 2nΛ + 38/log W
  have hmain : ∑ p ∈ windowPrimes s Lam z n, (2:ℝ) / p ≤ 2 * (n:ℝ) * Lam + 38 / Real.log W := by
    have hpm1 := sum_inv_le_of_prime_window (w := W) (z := z) hW2 hWz hwindow_sub
    have hrw : ∑ p ∈ windowPrimes s Lam z n, (2:ℝ)/p
        = 2 * ∑ p ∈ windowPrimes s Lam z n, (1:ℝ)/p := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [hrw]
    have : 2 * ∑ p ∈ windowPrimes s Lam z n, (1:ℝ)/p
        ≤ 2 * (Real.log (Real.log z / Real.log W) + 19 / Real.log W) := by
      apply mul_le_mul_of_nonneg_left hpm1 (by norm_num)
    calc 2 * ∑ p ∈ windowPrimes s Lam z n, (1:ℝ)/p
        ≤ 2 * (Real.log (Real.log z / Real.log W) + 19 / Real.log W) := this
      _ ≤ 2 * ((n:ℝ) * Lam + 19 / Real.log W) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hlog_ratio]
      _ = 2 * (n:ℝ) * Lam + 38 / Real.log W := by ring
  -- TAIL: 12·Σ 1/p² ≤ 12/(W-1) ≤ 12/log W
  have htail : ∑ p ∈ windowPrimes s Lam z n, (12:ℝ) / (p:ℝ)^2 ≤ 12 / Real.log W := by
    set M := ⌈W⌉₊ with hMdef
    have hMge : 2 ≤ M := by
      have : ⌈(2:ℝ)⌉₊ ≤ ⌈W⌉₊ := Nat.ceil_mono hW2
      simpa using this
    have hsub : windowPrimes s Lam z n ⊆ Finset.Icc M ⌊z⌋₊ := by
      intro q hq
      obtain ⟨hqp, hWq, hqz⟩ := hwindow_sub q hq
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hWq, Nat.le_floor hqz.le⟩
    have hstep : ∑ p ∈ windowPrimes s Lam z n, (12:ℝ)/(p:ℝ)^2
        ≤ ∑ p ∈ Finset.Icc M ⌊z⌋₊, (12:ℝ)/(p:ℝ)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _; positivity
    have hfactor : ∑ p ∈ Finset.Icc M ⌊z⌋₊, (12:ℝ)/(p:ℝ)^2
        = 12 * ∑ p ∈ Finset.Icc M ⌊z⌋₊, (1:ℝ)/(p:ℝ)^2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    have htel := sum_one_div_sq_le (M := M) (K := ⌊z⌋₊) hMge
    have hMreal : W ≤ (M:ℝ) := Nat.le_ceil W
    have hM1 : (0:ℝ) < (M:ℝ) - 1 := by
      have : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hMge
      linarith
    have hWm1 : (0:ℝ) < W - 1 := by linarith
    have hinv : 1/((M:ℝ) - 1) ≤ 1/(W - 1) := by
      apply one_div_le_one_div_of_le hWm1; linarith
    have hlogWsub : Real.log W ≤ W - 1 := Real.log_le_sub_one_of_pos hWpos
    have hinv2 : 1/(W - 1) ≤ 1/Real.log W := one_div_le_one_div_of_le hlogW hlogWsub
    calc ∑ p ∈ windowPrimes s Lam z n, (12:ℝ)/(p:ℝ)^2
        ≤ ∑ p ∈ Finset.Icc M ⌊z⌋₊, (12:ℝ)/(p:ℝ)^2 := hstep
      _ = 12 * ∑ p ∈ Finset.Icc M ⌊z⌋₊, (1:ℝ)/(p:ℝ)^2 := hfactor
      _ ≤ 12 * (1/((M:ℝ) - 1)) := by apply mul_le_mul_of_nonneg_left htel (by norm_num)
      _ ≤ 12 * (1/Real.log W) := by
          apply mul_le_mul_of_nonneg_left (le_trans hinv hinv2) (by norm_num)
      _ = 12 / Real.log W := by ring
  -- combine pointwise into the window
  have hsum_le : Real.log (Wratio s Lam z n)
      ≤ ∑ p ∈ windowPrimes s Lam z n, ((2:ℝ)/p + 12/(p:ℝ)^2) := by
    rw [log_Wratio_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp'
    rw [windowPrimes, Finset.mem_filter] at hp'
    exact neg_log_one_sub_nu_le s hp'.1 hnu2 hnuodd
  have hsplit_sum : ∑ p ∈ windowPrimes s Lam z n, ((2:ℝ)/p + 12/(p:ℝ)^2)
      = (∑ p ∈ windowPrimes s Lam z n, (2:ℝ)/p)
        + ∑ p ∈ windowPrimes s Lam z n, (12:ℝ)/(p:ℝ)^2 := Finset.sum_add_distrib
  -- combine everything
  have hcombine : Real.log (Wratio s Lam z n)
      ≤ 2 * (n:ℝ) * Lam + 50 * (1 / Real.log W) := by
    calc Real.log (Wratio s Lam z n)
        ≤ (∑ p ∈ windowPrimes s Lam z n, (2:ℝ)/p)
            + ∑ p ∈ windowPrimes s Lam z n, (12:ℝ)/(p:ℝ)^2 := hsum_le.trans_eq hsplit_sum
      _ ≤ (2 * (n:ℝ) * Lam + 38 / Real.log W) + 12 / Real.log W := by
          apply add_le_add hmain htail
      _ = 2 * (n:ℝ) * Lam + 50 * (1 / Real.log W) := by ring
  -- 50/log W ≤ 50 e^{nΛ}/log z
  have hfinal : 50 * (1 / Real.log W) ≤ 50 * Real.exp ((n:ℝ) * Lam) / Real.log z := by
    have := mul_le_mul_of_nonneg_left hinvW (by norm_num : (0:ℝ) ≤ 50)
    calc 50 * (1 / Real.log W) ≤ 50 * (Real.exp ((n:ℝ) * Lam) / Real.log z) := this
      _ = 50 * Real.exp ((n:ℝ) * Lam) / Real.log z := by ring
  linarith [hcombine, hfinal]

/-! ## Step 3 — the endpoint convexity bound `e^{nΛ} ≤ M·n` -/

/-- **Endpoint bound.**  On `n ∈ [1, r]` (`r = minLevel`), `e^{nΛ} ≤ M·n` with
`M = max(e^Λ, e^{rΛ}/r)` — the U-shape `e^{nΛ}/n` peaks at the endpoints, proved from
convexity of `exp`. -/
lemma exp_mul_le_max_mul {Lam z : ℝ} (hLam : 0 < Lam) (hz1 : 1 < z) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 (minLevel Lam z)) :
    Real.exp ((n:ℝ) * Lam)
      ≤ max (Real.exp Lam) (Real.exp ((minLevel Lam z : ℝ) * Lam) / (minLevel Lam z : ℝ))
        * (n:ℝ) := by
  set r := minLevel Lam z with hr
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hnr⟩ := hn
  have hr1 : 1 ≤ r := (minLevel_mem hLam hz1).1
  set M := max (Real.exp Lam) (Real.exp ((r:ℝ) * Lam) / (r:ℝ)) with hM
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr1
  have hMA : Real.exp Lam ≤ M := le_max_left _ _
  have hMB : Real.exp ((r:ℝ) * Lam) ≤ (r:ℝ) * M := by
    have h := le_max_right (Real.exp Lam) (Real.exp ((r:ℝ) * Lam) / (r:ℝ))
    rw [div_le_iff₀ hrpos] at h
    calc Real.exp ((r:ℝ) * Lam) ≤ M * (r:ℝ) := h
      _ = (r:ℝ) * M := by ring
  rcases Nat.lt_or_ge 1 r with hr2 | hr2
  · -- r ≥ 2: convexity
    have hr1r : (1:ℝ) < (r:ℝ) := by exact_mod_cast hr2
    set t := ((n:ℝ) - 1) / ((r:ℝ) - 1) with ht
    have hrm1 : (0:ℝ) < (r:ℝ) - 1 := by linarith
    have hnr' : (n:ℝ) ≤ (r:ℝ) := by exact_mod_cast hnr
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have ht0 : 0 ≤ t := by rw [ht]; apply div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hrm1]; linarith
    have hcombo : (n:ℝ) = (1 - t) * 1 + t * (r:ℝ) := by
      rw [ht]; field_simp; ring
    have hLamcombo : (n:ℝ) * Lam = (1 - t) * Lam + t * ((r:ℝ) * Lam) := by
      rw [hcombo]; ring
    have hconv := convexOn_exp.2 (Set.mem_univ Lam) (Set.mem_univ ((r:ℝ) * Lam))
      (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    rw [hLamcombo]
    calc Real.exp ((1 - t) * Lam + t * ((r:ℝ) * Lam))
        ≤ (1 - t) * Real.exp Lam + t * Real.exp ((r:ℝ) * Lam) := by
          simpa using hconv
      _ ≤ (1 - t) * M + t * ((r:ℝ) * M) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left hMA (by linarith)
          · apply mul_le_mul_of_nonneg_left hMB ht0
      _ = M * ((1 - t) * 1 + t * (r:ℝ)) := by ring
      _ = M * (n:ℝ) := by rw [← hcombo]
  · -- r = 1: n = 1
    have hne : n = 1 := by omega
    rw [hne]
    simp only [Nat.cast_one, one_mul, mul_one]
    exact hMA

/-! ## Step 4 — the `M`-bound and the final discharge -/

/-- The endpoint constant `M = max(e^Λ, e^{rΛ}/r)` obeys `50·M·loglog z ≤ 240·λ·log z`, from
the (2.14) minimality of `r` (`e^{(r−1)Λ} < log z/log 2` and `e^{rΛ} ≥ log z/log 2`) and the
threshold facts.  This is the arithmetic heart of the Λ-gap close. -/
lemma M_bound {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z) :
    50 * (max (Real.exp (LamTwin lam z))
      (Real.exp ((minLevel (LamTwin lam z) z : ℝ) * LamTwin lam z)
        / (minLevel (LamTwin lam z) z : ℝ))) * Real.log (Real.log z)
      ≤ 240 * lam * Real.log z := by
  obtain ⟨hllz, h400, hlz_pos, hllz_pos, hlz_eq, hkey, hz2⟩ := zThresh_facts hlam hlam' hz
  set Lam := LamTwin lam z with hLdef
  have hLampos : 0 < Lam := LamTwin_pos hlam hlam' hz
  have hLamle : Lam ≤ lam := LamTwin_le_lam hlam hlam' hz
  have hLam1 : Lam ≤ 1 := LamTwin_le_one hlam hlam' hz
  have hz1 : (1:ℝ) < z := by linarith
  set r := minLevel Lam z with hr
  have hr1 : 1 ≤ r := (minLevel_mem hLampos hz1).1
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr1
  -- e^Λ ≤ 3
  have hexpLam3 : Real.exp Lam ≤ 3 := by
    calc Real.exp Lam ≤ Real.exp 1 := Real.exp_le_exp.mpr hLam1
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- log 2 facts
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ge : (0.6931:ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- loglog2 < 0
  have hll2 : Real.log (Real.log 2) < 0 :=
    Real.log_neg hlog2pos (by have := Real.log_two_lt_d9; linarith)
  -- BRANCH A: 50·e^Λ·loglog z ≤ 240 λ log z
  have hbranchA : 50 * Real.exp Lam * Real.log (Real.log z) ≤ 240 * lam * Real.log z := by
    have h1 : 50 * Real.exp Lam * Real.log (Real.log z) ≤ 150 * Real.log (Real.log z) := by
      nlinarith [hexpLam3, hllz_pos]
    -- 150 loglog z ≤ 240 λ log z since λ log z ≥ 25 loglog z
    nlinarith [hkey, hllz_pos]
  -- BRANCH B: 50·(e^{rΛ}/r)·loglog z ≤ 240 λ log z
  have hbranchB : 50 * (Real.exp ((r:ℝ) * Lam) / (r:ℝ)) * Real.log (Real.log z)
      ≤ 240 * lam * Real.log z := by
    -- e^{rΛ} ≤ e^Λ · log z/log 2  (from minimality of r) and r ≥ (loglog z - loglog2)/Λ
    have hexpr_ub : Real.exp ((r:ℝ) * Lam) ≤ Real.exp Lam * (Real.log z / Real.log 2) := by
      rcases Nat.lt_or_ge 1 r with hr2 | hr2
      · -- r ≥ 2: e^{(r-1)Λ} < log z/log 2
        have hrm1 : 1 ≤ r - 1 := by omega
        have hlt : zLev Lam z (r - 1) > 2 := by
          by_contra h
          have := minLevel_le (Lam := Lam) (z := z) (n := r - 1) hrm1 (not_lt.mp h)
          omega
        have hkey2 : Real.exp (((r-1 : ℕ):ℝ) * Lam) < Real.log z / Real.log 2 := by
          by_contra h
          have := (zLev_le_two_iff Lam z (r-1) hz1).2 (not_lt.mp h)
          linarith
        have hcast : ((r-1 : ℕ):ℝ) = (r:ℝ) - 1 := by
          have : 1 ≤ r := hr1
          push_cast [Nat.cast_sub this]; ring
        rw [hcast] at hkey2
        have hsplit : Real.exp ((r:ℝ) * Lam) = Real.exp Lam * Real.exp (((r:ℝ)-1) * Lam) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hsplit]
        apply mul_le_mul_of_nonneg_left hkey2.le (Real.exp_pos _).le
      · -- r = 1
        have hre : r = 1 := by omega
        rw [hre]
        simp only [Nat.cast_one, one_mul]
        have hlogzlog2 : (1:ℝ) ≤ Real.log z / Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          have : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) (by linarith)
          linarith
        nlinarith [Real.exp_pos Lam, hlogzlog2]
    -- r ≥ (loglog z - loglog 2)/Λ, i.e. rΛ ≥ loglog z - loglog 2
    have hr_lb : Real.log (Real.log z) - Real.log (Real.log 2) ≤ (r:ℝ) * Lam := by
      have h := exp_minLevel_ge (Lam := Lam) (z := z) hLampos hz1
      -- log z/log 2 ≤ e^{rΛ}, take log
      have hlogdiv : Real.log (Real.log z / Real.log 2)
          = Real.log (Real.log z) - Real.log (Real.log 2) :=
        Real.log_div hlz_pos.ne' hlog2pos.ne'
      have hdivpos : 0 < Real.log z / Real.log 2 := by positivity
      have := Real.log_le_log hdivpos h
      rwa [hlogdiv, Real.log_exp] at this
    -- (loglog z - loglog 2) > 0
    have hdiffpos : 0 < Real.log (Real.log z) - Real.log (Real.log 2) := by linarith
    -- 1/r ≤ Λ/(loglog z - loglog 2)
    have hinv_r : (1:ℝ)/(r:ℝ) ≤ Lam / (Real.log (Real.log z) - Real.log (Real.log 2)) := by
      rw [div_le_div_iff₀ hrpos hdiffpos, one_mul]
      linarith [hr_lb]
    -- assemble: e^{rΛ}/r ≤ e^Λ (log z/log2) · Λ/(loglog z - loglog 2)
    have hexppos : 0 < Real.exp ((r:ℝ) * Lam) := Real.exp_pos _
    have hchain : Real.exp ((r:ℝ) * Lam) / (r:ℝ)
        ≤ (Real.exp Lam * (Real.log z / Real.log 2))
          * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2))) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul hexpr_ub hinv_r (by positivity) (by positivity)
    -- now bound the RHS: loglog z/(loglog z - loglog2) ≤ 1, Λ ≤ λ, e^Λ ≤ 3, log2 ≥ 0.6931
    have hratio1 : Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2)) ≤ 1 := by
      rw [div_le_one hdiffpos]; linarith
    -- 50 · RHS · loglog z ≤ 240 λ log z
    have hstep : 50 * ((Real.exp Lam * (Real.log z / Real.log 2))
          * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2)))) * Real.log (Real.log z)
        ≤ 240 * lam * Real.log z := by
      -- rewrite: = 50 e^Λ Λ log z/log2 · (loglog z/(loglog z - loglog2))
      have hpos1 : 0 < Real.log z / Real.log 2 := by positivity
      have hexpr : 50 * ((Real.exp Lam * (Real.log z / Real.log 2))
            * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2)))) * Real.log (Real.log z)
          = (50 * Real.exp Lam * Lam * (Real.log z / Real.log 2))
            * (Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2))) := by
        ring
      rw [hexpr]
      -- ≤ 50 e^Λ Λ log z/log2 · 1
      have hfac_nonneg : 0 ≤ 50 * Real.exp Lam * Lam * (Real.log z / Real.log 2) := by positivity
      have h1 : (50 * Real.exp Lam * Lam * (Real.log z / Real.log 2))
            * (Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2)))
          ≤ (50 * Real.exp Lam * Lam * (Real.log z / Real.log 2)) * 1 :=
        mul_le_mul_of_nonneg_left hratio1 hfac_nonneg
      -- 50 e^Λ Λ log z/log2 ≤ 240 λ log z
      have h2 : (50 * Real.exp Lam * Lam * (Real.log z / Real.log 2)) * 1
          ≤ 240 * lam * Real.log z := by
        rw [mul_one]
        -- 50·3·λ·(log z/0.6931) ≤ 240 λ log z  ⟺  150/0.6931 ≤ 240
        have hbound : 50 * Real.exp Lam * Lam ≤ 150 * lam := by
          nlinarith [hexpLam3, hLamle, hLampos.le, hlam.le]
        have hlogz_div : Real.log z / Real.log 2 ≤ Real.log z / 0.6931 := by
          apply div_le_div_of_nonneg_left hlz_pos.le (by norm_num) hlog2ge
        calc (50 * Real.exp Lam * Lam) * (Real.log z / Real.log 2)
            ≤ (150 * lam) * (Real.log z / 0.6931) := by
              apply mul_le_mul hbound hlogz_div (by positivity) (by positivity)
          _ ≤ 240 * lam * Real.log z := by
              rw [div_eq_mul_inv]
              nlinarith [hlz_pos.le, hlam.le, mul_nonneg hlam.le hlz_pos.le]
      linarith [h1, h2]
    calc 50 * (Real.exp ((r:ℝ) * Lam) / (r:ℝ)) * Real.log (Real.log z)
        ≤ 50 * ((Real.exp Lam * (Real.log z / Real.log 2))
            * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2)))) * Real.log (Real.log z) := by
          apply mul_le_mul_of_nonneg_right _ hllz_pos.le
          apply mul_le_mul_of_nonneg_left hchain (by norm_num)
      _ ≤ 240 * lam * Real.log z := hstep
  -- combine the two branches through the max
  rcases max_cases (Real.exp Lam) (Real.exp ((r:ℝ) * Lam) / (r:ℝ)) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact hbranchA
  · rw [he]; exact hbranchB

/-- **PM2 — the twin `hMert` discharge.**  For `z ≥ z₀ = exp(exp(100/λ))`, `0 < λ ≤ 1/4`, a
`BoundingSieve` with all sifting primes `< z` and twin densities (`ν(2) ≤ 1/2`,
`ν(p) ≤ 2/p` odd), the ladder scale `Λ = LamTwin λ z` gives
`log(W(z_n)/W(z)) ≤ n·(2λ)` for every `n ∈ [1, r]` — i.e. `hMert` at `κ = 2λ`
(`hkappa = le_refl`), feeding `Wratio_le_exp`/`windowSum_le` (B3b). -/
theorem hMert_twin (s : BoundingSieve) {lam z : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hnu2 : (2 : ℕ) ∈ s.prodPrimes.primeFactors → s.nu 2 ≤ 1 / 2)
    (hnuodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 → s.nu q ≤ 2 / q) :
    ∀ n ∈ Finset.Icc 1 (minLevel (LamTwin lam z) z),
      Real.log (Wratio s (LamTwin lam z) z n) ≤ (n : ℝ) * (2 * lam) := by
  intro n hn
  obtain ⟨hllz, h400, hlz_pos, hllz_pos, hlz_eq, hkey, hz2⟩ := zThresh_facts hlam hlam' hz
  set Lam := LamTwin lam z with hLdef
  have hLampos : 0 < Lam := LamTwin_pos hlam hlam' hz
  have hz1 : (1:ℝ) < z := by linarith
  set r := minLevel Lam z with hr
  set M := max (Real.exp Lam) (Real.exp ((r:ℝ) * Lam) / (r:ℝ)) with hM
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  -- step 3 (ladder)
  have hladder := log_Wratio_le_ladder s (Lam := Lam) (z := z) (n := n)
    hLampos.le hz2 hp hnu2 hnuodd
  -- step (endpoint): e^{nΛ} ≤ M·n
  have hendpoint := exp_mul_le_max_mul (Lam := Lam) (z := z) hLampos hz1 hn
  -- M-bound: 50 M loglog z ≤ 240 λ log z
  have hMbound := M_bound hlam hlam' hz
  -- turn hMbound into 50 M/log z ≤ 2(λ - Λ)
  have hgap : lam - Lam = lam * 120 / Real.log (Real.log z) := lam_sub_LamTwin
  have hMdivz : 50 * M / Real.log z ≤ 2 * (lam - Lam) := by
    have h2lamLam : 2 * (lam - Lam) = 240 * lam / Real.log (Real.log z) := by
      rw [hgap]; ring
    rw [h2lamLam, div_le_div_iff₀ hlz_pos hllz_pos]
    have : 50 * M * Real.log (Real.log z) ≤ 240 * lam * Real.log z := hMbound
    nlinarith [this]
  -- assemble
  -- log Wratio ≤ 2nΛ + 50 e^{nΛ}/log z ≤ 2nΛ + 50 M n/log z ≤ 2nΛ + 2n(λ-Λ) = 2nλ
  have hexp_bound : 50 * Real.exp ((n:ℝ) * Lam) / Real.log z ≤ 50 * (M * (n:ℝ)) / Real.log z := by
    have hnum : 50 * Real.exp ((n:ℝ) * Lam) ≤ 50 * (M * (n:ℝ)) :=
      mul_le_mul_of_nonneg_left hendpoint (by norm_num)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hlz_pos.le)
  have hMn : 50 * (M * (n:ℝ)) / Real.log z ≤ 2 * (n:ℝ) * (lam - Lam) := by
    rw [show 50 * (M * (n:ℝ)) / Real.log z = (50 * M / Real.log z) * (n:ℝ) by ring]
    calc (50 * M / Real.log z) * (n:ℝ)
        ≤ (2 * (lam - Lam)) * (n:ℝ) := by apply mul_le_mul_of_nonneg_right hMdivz hnpos.le
      _ = 2 * (n:ℝ) * (lam - Lam) := by ring
  have hfinal : Real.log (Wratio s Lam z n) ≤ (n:ℝ) * (2 * lam) := by
    calc Real.log (Wratio s Lam z n)
        ≤ 2 * (n:ℝ) * Lam + 50 * Real.exp ((n:ℝ) * Lam) / Real.log z := hladder
      _ ≤ 2 * (n:ℝ) * Lam + 50 * (M * (n:ℝ)) / Real.log z := by linarith [hexp_bound]
      _ ≤ 2 * (n:ℝ) * Lam + 2 * (n:ℝ) * (lam - Lam) := by linarith [hMn]
      _ = (n:ℝ) * (2 * lam) := by ring
  exact hfinal

/-! ## The TwinSieve-facing corollary -/

/-- **PM2 at the twin instance.**  The `Salt.TwinSieve.sieve` densities (`ν(2) = 1/2`,
`ν(p) = 2/p`) discharge the `ν`-hypotheses directly (via `rho_two`/`rho_odd_prime`), so
PM2 lands `hMert` (`κ = 2λ`) for the actual twin sieve, given `z ≥ z₀` and all prime
factors of the sifting modulus `P` below `z`. -/
theorem hMert_twinSieve {N P : ℕ} (hP : Squarefree P) {lam z : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    ∀ n ∈ Finset.Icc 1 (minLevel (LamTwin lam z) z),
      Real.log (Wratio (Salt.TwinSieve.sieve N P hP) (LamTwin lam z) z n)
        ≤ (n : ℝ) * (2 * lam) := by
  apply hMert_twin (Salt.TwinSieve.sieve N P hP) hlam hlam' hz
  · intro p hpm
    rw [Salt.TwinSieve.sieve_prodPrimes] at hpm
    exact hpz p hpm
  · intro _
    rw [Salt.TwinSieve.sieve_nu, Salt.TwinSieve.nu_apply, rho_two]; norm_num
  · intro q hqm hq2
    rw [Salt.TwinSieve.sieve_prodPrimes] at hqm
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqm
    rw [Salt.TwinSieve.sieve_nu, Salt.TwinSieve.nu_apply, rho_odd_prime hqp hq2]
    norm_num

end Salt.BrunLower
