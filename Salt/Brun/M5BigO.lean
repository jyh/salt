/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.M5Assembly
import Salt.Brun

/-!
# N5.3 — absorbing N5.2 into a clean `O(N / (log N)²)`

Combines `Salt.M5Assembly.N5_2` with two `isLittleO` absorptions (of the
sieve error terms `N^(4/5)` and `z N` into `N/(log N)²`) and a log(z N)
vs log(N) comparison to get an eventual `ℕ`-indexed bound
`twinPrimeCounting N ≤ C * N / (log N)²`. A generic floor-vs-real transfer
lemma then upgrades this to the `TwinCountingBigO` statement over `ℝ`.

No constant here is tight; every threshold is chosen generously so that
`norm_num`/`nlinarith` close easily.
-/

open Filter Asymptotics Salt.M5Assembly

namespace Salt.M5BigO

/-! ## Part A — the ℕ-indexed absorption -/

/-! ### A1 — `log (z N) ≥ (1/20) log N` eventually -/

/-- Concrete threshold: `2^100 ≤ N`. Chosen as a power of `2` so that
`log N0 = 100 * log 2` is exact (no decimal `exp` estimates needed), and
`N0 ^ (1/10) = 2^10 = 1024` is also exact. -/
def N0 : ℕ := 2 ^ 100

lemma N0_cast : (N0 : ℝ) = (2 : ℝ) ^ (100 : ℕ) := by
  unfold N0; push_cast; ring

/-- `N0 ^ (1/10 : ℝ) = 1024`, computed exactly via `rpow_mul`. -/
lemma N0_rpow_tenth : (N0 : ℝ) ^ (1 / 10 : ℝ) = 1024 := by
  rw [N0_cast, ← Real.rpow_natCast (2 : ℝ) 100,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `N ^ (1/10) ≥ 1024` for `N ≥ N0`. -/
lemma rpow_tenth_ge {N : ℕ} (hN : N0 ≤ N) : (1024 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  have hcast : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N0:ℝ)) hcast (by norm_num : (0:ℝ) ≤ 1/10)
  rwa [N0_rpow_tenth] at this

/-- `log N0 = 100 * log 2 ≥ 20 * log 2`, hence `log N ≥ 20 * log 2` for `N ≥ N0`. -/
lemma log_ge_20log2 {N : ℕ} (hN : N0 ≤ N) : (20 : ℝ) * Real.log 2 ≤ Real.log N := by
  have hcast : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0pos : (0:ℝ) < (N0 : ℝ) := by
    rw [N0_cast]; positivity
  have hmono : Real.log N0 ≤ Real.log N := Real.log_le_log hN0pos hcast
  have hlogN0 : Real.log (N0 : ℝ) = 100 * Real.log 2 := by
    rw [N0_cast, Real.log_pow]; norm_num
  have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hmono, hlogN0, hlog2pos]

/-- `z N ≥ z0` (i.e. `100 ≤ z N`) for `N ≥ N0`. -/
lemma zN_ge_z0 {N : ℕ} (hN : N0 ≤ N) : Salt.M3Assembly.z0 ≤ z N := by
  have h1024 := rpow_tenth_ge hN
  have hlt : (N : ℝ) ^ (1 / 10 : ℝ) < (z N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hzR : (159 : ℝ) ≤ (z N : ℝ) := by linarith
  have : (159 : ℕ) ≤ z N := by exact_mod_cast hzR
  unfold Salt.M3Assembly.z0
  omega

/-- **A1.** `log (z N) ≥ (1/20) * log N` for `N ≥ N0`. -/
lemma logZ_ge {N : ℕ} (hN : N0 ≤ N) : (1 / 20 : ℝ) * Real.log N ≤ Real.log (z N) := by
  have h1024 := rpow_tenth_ge hN
  have hlt : (N : ℝ) ^ (1 / 10 : ℝ) < (z N : ℝ) + 1 := Nat.lt_floor_add_one _
  -- (z N : ℝ) > N^(1/10) - 1 ≥ N^(1/10)/2  (since N^(1/10) ≥ 1024 ≥ 2)
  have hhalf : (N : ℝ) ^ (1 / 10 : ℝ) - 1 ≥ (N : ℝ) ^ (1 / 10 : ℝ) / 2 := by linarith
  have hzgt : (z N : ℝ) > (N : ℝ) ^ (1 / 10 : ℝ) / 2 := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) / 2 := by linarith
  have hmono : Real.log ((N : ℝ) ^ (1 / 10 : ℝ) / 2) ≤ Real.log (z N : ℝ) :=
    Real.log_le_log hpos (le_of_lt hzgt)
  have hN0ge1 : (1 : ℕ) ≤ N0 := by unfold N0; exact Nat.one_le_two_pow
  have hN1 : (1 : ℕ) ≤ N := le_trans hN0ge1 hN
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogdiv : Real.log ((N : ℝ) ^ (1 / 10 : ℝ) / 2)
      = Real.log ((N : ℝ) ^ (1 / 10 : ℝ)) - Real.log 2 :=
    Real.log_div (by positivity) (by norm_num)
  have hlogrpow : Real.log ((N : ℝ) ^ (1 / 10 : ℝ)) = (1 / 10) * Real.log N :=
    Real.log_rpow hNpos _
  have h20log2 : (20 : ℝ) * Real.log 2 ≤ Real.log N := log_ge_20log2 hN
  rw [hlogdiv, hlogrpow] at hmono
  linarith

/-! ### A2 — chain to `N / S(N) ≤ 25600 * N / (log N)^2` -/

/-- **A2.** For `N ≥ N0` (and `1 ≤ N`), the sieve bounding sum bound
`N / S(N) ≤ 25600 * N / (log N)^2`. -/
lemma A2 {N : ℕ} (hN0 : N0 ≤ N) (hN : 1 ≤ N) :
    (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
      ≤ 25600 * (N : ℝ) / (Real.log N) ^ 2 := by
  have hz100 : Salt.M3Assembly.z0 ≤ z N := zN_ge_z0 hN0
  have hS := selbergBoundingSum_ge_log_sq N hN hz100
  have hlogZge := logZ_ge hN0
  have hlogNpos : (0:ℝ) < Real.log N := by
    have := log_ge_20log2 hN0
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hlogZpos : (0:ℝ) ≤ (1/20:ℝ) * Real.log N := by linarith
  have hsq : ((1/20:ℝ) * Real.log N)^2 ≤ (Real.log (z N))^2 :=
    pow_le_pow_left₀ hlogZpos hlogZge 2
  have hLbound : (1/64:ℝ) * ((1/20:ℝ) * Real.log N)^2 ≤ (1/64:ℝ) * (Real.log (z N))^2 := by
    nlinarith [hsq]
  have hLeq : (1/64:ℝ) * ((1/20:ℝ) * Real.log N)^2 = (Real.log N)^2 / 25600 := by ring
  rw [hLeq] at hLbound
  have hSge : Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN) ≥
      (Real.log N)^2 / 25600 := le_trans hLbound hS
  have hLpos : (0:ℝ) < (Real.log N)^2 / 25600 := by positivity
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hdiv : (N:ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSelbergSieve N hN)
      ≤ (N:ℝ) / ((Real.log N)^2 / 25600) :=
    div_le_div_of_nonneg_left hNnn hLpos hSge
  have heq : (N:ℝ) / ((Real.log N)^2 / 25600) = 25600 * (N:ℝ) / (Real.log N)^2 := by
    field_simp
  rwa [heq] at hdiv

/-! ### A3 — `256 * N^(4/5) ≤ N / (log N)^2` eventually -/

/-- **A3.** For `N` large enough (depending on the `isLittleO` witness),
`256 * N^(4/5) ≤ N / (log N)^2`. -/
lemma A3 : ∃ N3 : ℕ, 2 ≤ N3 ∧ ∀ N : ℕ, N3 ≤ N →
    256 * (N : ℝ) ^ (4 / 5 : ℝ) ≤ (N : ℝ) / (Real.log N) ^ 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (2:ℝ)) =o[atTop] fun x : ℝ => x ^ (1 / 5 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1/5)
  have hbound := hlo.bound (show (0:ℝ) < 1/256 by norm_num)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max ⌈a⌉₊ 2, le_max_right _ _, ?_⟩
  intro N hN
  have hNa : a ≤ (N:ℝ) := by
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈a⌉₊ ≤ N := le_trans (le_max_left _ _) hN
      exact_mod_cast this
    linarith
  have hN2 : (2:ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hN2R : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hkey := ha (N:ℝ) hNa
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by linarith
  have habs1 : ‖Real.log N ^ (2:ℝ)‖ = Real.log N ^ (2:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs2 : ‖(N:ℝ) ^ (1/5:ℝ)‖ = (N:ℝ) ^ (1/5:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs1, habs2] at hkey
  rw [Real.rpow_two] at hkey
  -- hkey : (Real.log N)^2 ≤ (1/256) * N^(1/5)
  have hstep : 256 * (N:ℝ)^(4/5:ℝ) * (Real.log N)^2
      ≤ 256 * (N:ℝ)^(4/5:ℝ) * ((1/256) * (N:ℝ)^(1/5:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hkey
    positivity
  have hadd : (N:ℝ)^(4/5:ℝ) * (N:ℝ)^(1/5:ℝ) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (4/5:ℝ) + (1/5:ℝ) = 1 by norm_num, Real.rpow_one]
  have hprod : 256 * (N:ℝ)^(4/5:ℝ) * ((1/256) * (N:ℝ)^(1/5:ℝ)) = (N:ℝ) := by
    rw [show (256:ℝ) * (N:ℝ)^(4/5:ℝ) * ((1/256) * (N:ℝ)^(1/5:ℝ))
        = (N:ℝ)^(4/5:ℝ) * (N:ℝ)^(1/5:ℝ) by ring]
    exact hadd
  rw [hprod] at hstep
  have hlogsqpos : (0:ℝ) < (Real.log N)^2 := pow_pos hlogNpos 2
  rw [le_div_iff₀ hlogsqpos]
  linarith [hstep]

/-! ### A4 — `(z N : ℝ) + 1 ≤ N / (log N)^2` eventually -/

/-- **A4.** For `N` large enough, `(z N : ℝ) + 1 ≤ N / (log N)^2`. -/
lemma A4 : ∃ N4 : ℕ, 2 ≤ N4 ∧ ∀ N : ℕ, N4 ≤ N →
    (z N : ℝ) + 1 ≤ (N : ℝ) / (Real.log N) ^ 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (2:ℝ)) =o[atTop] fun x : ℝ => x ^ (9 / 10 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 9/10)
  have hbound := hlo.bound (show (0:ℝ) < 1/2 by norm_num)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max ⌈a⌉₊ 2, le_max_right _ _, ?_⟩
  intro N hN
  have hNa : a ≤ (N:ℝ) := by
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈a⌉₊ ≤ N := le_trans (le_max_left _ _) hN
      exact_mod_cast this
    linarith
  have hN2 : (2:ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hN2R : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hkey := ha (N:ℝ) hNa
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have habs1 : ‖Real.log N ^ (2:ℝ)‖ = Real.log N ^ (2:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs2 : ‖(N:ℝ) ^ (9/10:ℝ)‖ = (N:ℝ) ^ (9/10:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs1, habs2] at hkey
  rw [Real.rpow_two] at hkey
  -- hkey : (Real.log N)^2 ≤ (1/2) * N^(9/10)
  have hzle : (z N : ℝ) ≤ (N:ℝ) ^ (1/10:ℝ) := Nat.floor_le (by positivity)
  have hNtenth_pos : (0:ℝ) < (N:ℝ) ^ (1/10:ℝ) := by positivity
  have hNtenth_ge1 : (1:ℝ) ≤ (N:ℝ) ^ (1/10:ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hzp1 : (z N : ℝ) + 1 ≤ 2 * (N:ℝ) ^ (1/10:ℝ) := by linarith
  have hstep : 2 * (N:ℝ)^(1/10:ℝ) * (Real.log N)^2 ≤
      2 * (N:ℝ)^(1/10:ℝ) * ((1/2) * (N:ℝ)^(9/10:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hkey
    positivity
  have hadd : (N:ℝ)^(1/10:ℝ) * (N:ℝ)^(9/10:ℝ) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (1/10:ℝ) + (9/10:ℝ) = 1 by norm_num, Real.rpow_one]
  have hprod : 2 * (N:ℝ)^(1/10:ℝ) * ((1/2) * (N:ℝ)^(9/10:ℝ)) = (N:ℝ) := by
    rw [show (2:ℝ) * (N:ℝ)^(1/10:ℝ) * ((1/2) * (N:ℝ)^(9/10:ℝ))
        = (N:ℝ)^(1/10:ℝ) * (N:ℝ)^(9/10:ℝ) by ring]
    exact hadd
  rw [hprod] at hstep
  have hlogsqpos : (0:ℝ) < (Real.log N)^2 := pow_pos hlogNpos 2
  have hfinal : 2 * (N:ℝ)^(1/10:ℝ) ≤ (N:ℝ) / (Real.log N)^2 := by
    rw [le_div_iff₀ hlogsqpos]
    linarith [hstep]
  linarith [hzp1, hfinal]

/-! ### Combine A2 + A3 + A4 with N5_2 -/

/-- **nat_absorb.** For `N` large enough, `twinPrimeCounting N ≤ 25700 * N / (log N)^2`. -/
lemma nat_absorb : ∃ N1 : ℕ, ∀ N ≥ N1,
    (twinPrimeCounting N : ℝ) ≤ 25700 * (N : ℝ) / (Real.log N) ^ 2 := by
  obtain ⟨Ns2, hNs2⟩ := Salt.M5Assembly.N5_2
  obtain ⟨N3, _, hN3⟩ := A3
  obtain ⟨N4, _, hN4⟩ := A4
  refine ⟨max (max N0 Ns2) (max N3 N4), fun N hN => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNs2' : Ns2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4' : N4 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := by
    have : (2:ℕ) ≤ N0 := by unfold N0; norm_num
    omega
  have hstep2 := hNs2 N hNs2' hN1
  have hA2 := A2 hN0 hN1
  have hA3 := hN3 N hN3'
  have hA4 := hN4 N hN4'
  have hXnn : (0:ℝ) ≤ (N:ℝ) / (Real.log N) ^ 2 := by positivity
  have heq : 25600 * (N:ℝ) / (Real.log N) ^ 2 + (N:ℝ) / (Real.log N) ^ 2
      + (N:ℝ) / (Real.log N) ^ 2 = 25602 * ((N:ℝ) / (Real.log N) ^ 2) := by ring
  have hfinal : 25602 * ((N:ℝ) / (Real.log N) ^ 2) ≤ 25700 * (N:ℝ) / (Real.log N) ^ 2 := by
    have heq2 : 25700 * (N:ℝ) / (Real.log N) ^ 2 = 25700 * ((N:ℝ) / (Real.log N) ^ 2) := by ring
    rw [heq2]; nlinarith [hXnn]
  linarith [hstep2, hA2, hA3, hA4, heq, hfinal]

/-! ## Part B — the floor-transfer lemma (generic, independent of Part A) -/

/-- **Part B.** `⌊x⌋₊ / (log ⌊x⌋₊)²` is `O(x / (log x)²)` as `x → ∞`. -/
lemma floor_ratio_isBigO :
    (fun x : ℝ => (⌊x⌋₊ : ℝ) / (Real.log ⌊x⌋₊) ^ 2)
      =O[Filter.atTop] (fun x : ℝ => x / Real.log x ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ)] with x hx4
  have hxnn : (0:ℝ) ≤ x := by linarith
  have hfloorle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxnn
  have hfloorgt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hfloorgt2 : (⌊x⌋₊ : ℝ) > x / 2 := by linarith
  have hxhalfpos : (0:ℝ) < x / 2 := by linarith
  have hxne : x ≠ 0 := by positivity
  have hlogdiv : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div hxne (by norm_num)
  have hlogfloor_ge : Real.log (x / 2) ≤ Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_le_log hxhalfpos (le_of_lt hfloorgt2)
  have hlog4eq : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have hlog4le : Real.log (4:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx4
  have hlogxpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hhalflog : Real.log x / 2 ≤ Real.log x - Real.log 2 := by linarith [hlog4le, hlog4eq]
  have hlogfloor_ge2 : Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
    rw [hlogdiv] at hlogfloor_ge; linarith
  have hsq : (Real.log x / 2) ^ 2 ≤ (Real.log (⌊x⌋₊ : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlogfloor_ge2 2
  have hstep1 : (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊:ℝ)) ^ 2 ≤ x / (Real.log (⌊x⌋₊:ℝ)) ^ 2 :=
    div_le_div_of_nonneg_right hfloorle (sq_nonneg _)
  have hstep2 : x / (Real.log (⌊x⌋₊:ℝ)) ^ 2 ≤ x / (Real.log x / 2) ^ 2 :=
    div_le_div_of_nonneg_left hxnn (by positivity) hsq
  have heq : x / (Real.log x / 2) ^ 2 = 4 * (x / Real.log x ^ 2) := by
    field_simp; ring
  have hfinal : (⌊x⌋₊ : ℝ) / (Real.log (⌊x⌋₊:ℝ)) ^ 2 ≤ 4 * (x / Real.log x ^ 2) := by
    rw [← heq]; exact le_trans hstep1 hstep2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  exact hfinal

/-! ## Part C — assemble -/

/-- **N5.3.** `twinPrimeCounting N` is `O(N / (log N)²)`. -/
theorem N5_3 : TwinCountingBigO := by
  unfold TwinCountingBigO
  obtain ⟨N₁, hN₁⟩ := nat_absorb
  have hstep1 : (fun x : ℝ => (twinPrimeCounting ⌊x⌋₊ : ℝ))
      =O[Filter.atTop] (fun x : ℝ => (⌊x⌋₊:ℝ) / (Real.log ⌊x⌋₊)^2) := by
    apply Asymptotics.IsBigO.of_bound 25700
    have hev : ∀ᶠ (N:ℕ) in Filter.atTop, (twinPrimeCounting N : ℝ)
        ≤ 25700 * ((N:ℝ) / (Real.log N)^2) := by
      filter_upwards [Filter.eventually_ge_atTop N₁] with N hN
      calc (twinPrimeCounting N:ℝ) ≤ 25700 * (N:ℝ) / (Real.log N)^2 := hN₁ N hN
        _ = 25700 * ((N:ℝ) / (Real.log N)^2) := by ring
    have htendsto := (tendsto_nat_floor_atTop (α := ℝ)).eventually hev
    filter_upwards [htendsto] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact hx
  exact hstep1.trans floor_ratio_isBigO

end Salt.M5BigO
