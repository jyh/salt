/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MoebiusRateSharp
import Salt.SW.GrahamWeights

/-!
# The log-weighted Möbius constant and the sharp Barban–Vehov cancellation

This module lands two targets feeding the `dh_repulsion` mollifier input:

1. `abs_sum_moebius_div_mul_log_le` — the `O(1)` bound on the log-weighted Möbius sum
   `∃ C > 0, ∀ z ≥ 1, |Σ_{d≤z} (μ(d)/d)·log d| ≤ C`. (Classically the sum → −1;
   the BOUNDED form suffices here.)
2. `abs_sum_grahamTheta_div_le_inv_log` — the SHARP Barban–Vehov value bound
   `∃ C > 0, ∀ z ≥ 3, |Σ_{d≤z} θ_d/d| ≤ C / log z`, upgrading the crude
   `≤ 1 + log z` of `abs_sum_grahamTheta_div_le` (GrahamWeights).

## Route for target 1 (Abel summation)

Abel-sum `Σ_{d≤z} μ(d)·(log d/d)` against `M_μ(t) = Σ_{n≤t} μ(n)` with weight
`f(t) = log t/t`, `f'(t) = (1 − log t)/t²`
(`sum_mul_eq_sub_integral_mul₀'`, mirroring `Salt.SW.MoebiusRateSharp`):
`S(z) = (log z/z)·M_μ(z) − ∫_{Ioc 1 z} f'(t)·M_μ(⌊t⌋)`.
With `mmuRate` at `A = 3` (`|M_μ| ≤ C₃·t/(log t)³`): the boundary is `≤ C₃/(log z)² ≤ C₃`,
and the integrand is dominated by `8C₃/(t log²t)` (integrable, `Salt.SW`'s reused tail
`integral_inv_tlogsq_Ioi'`), so `∫_{Ioi 1}|φ|` is a finite constant. The small window
`z < max(x₀,3)` folds in via the crude harmonic bound `Σ (log d)/d ≤ log z·(1+log z)`.

## Route for target 2 (composition)

`θ_d = μ(d)·(log z − log d)/log z` on `d ≤ z`, so
`Σ_{d≤z} θ_d/d = Mw(z) − (1/log z)·Σ_{d≤z}(μ(d)/d)·log d`
(`Mw = mwWeighted`); both terms are `≤ (·)/log z` via the LANDED
`abs_mwWeighted_le_div_log` and target 1.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open MeasureTheory Filter Topology Finset ArithmeticFunction

namespace Salt.SW

open Salt.TwinBar (Mmu)

/-! ## The weight `f(t) = log t/t`, its derivative, and integrability data -/

/-- `f(t) = log t/t` has derivative `(1 − log t)/t²` for `t > 0` (quotient rule). -/
theorem hasDerivAt_logDiv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t / t) ((1 - Real.log x) / x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h := (Real.hasDerivAt_log hx0).div (hasDerivAt_id x) hx0
  simp only [id_eq, mul_one] at h
  rw [inv_mul_cancel₀ hx0] at h
  exact h

/-- The `deriv` form of `hasDerivAt_logDiv`. -/
theorem deriv_logDiv {x : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ => Real.log t / t) x = (1 - Real.log x) / x ^ 2 :=
  (hasDerivAt_logDiv hx).deriv

/-- `f = log·/·` is differentiable on `[1, ∞)`. -/
private theorem hf_diff_aux_log :
    ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => Real.log x / x) t :=
  fun _t ht => (hasDerivAt_logDiv (lt_of_lt_of_le one_pos ht)).differentiableAt

/-- `deriv (log·/·)` is locally integrable on `[1, ∞)` (it agrees with the continuous
`(1 − log t)/t²` there). -/
private theorem hf_int_aux_log :
    LocallyIntegrableOn (deriv (fun x : ℝ => Real.log x / x)) (Set.Ici (1 : ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Ici (1 : ℝ)) := by
    apply ContinuousOn.div
    · exact continuousOn_const.sub (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le one_pos hx)))
    · exact (continuous_pow 2).continuousOn
    · intro x hx; exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos hx))
  have hLI : LocallyIntegrableOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Ici (1 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ici
  refine hLI.congr ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ (fun x hx => ?_))
  exact (deriv_logDiv (lt_of_lt_of_le one_pos hx)).symm

/-! ## The Abel summand `φ t = f'(t)·M_μ(⌊t⌋)` and its pointwise domination -/

/-- The Abel summand for the log-weighted sum. -/
noncomputable def logDivPhi (t : ℝ) : ℝ :=
  deriv (fun x : ℝ => Real.log x / x) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ)

/-- The pointwise bound `‖φ t‖ ≤ 8C₃/(t log²t)` for `t ≥ max(x₀,3)`, from `mmuRate` at
`A = 3`. Extra `log t` (vs the `x⁻¹` case) is absorbed: `|f'(t)| ≤ log t/t²`. -/
theorem norm_logDivPhi_le {C₃ : ℝ} {x₀ : ℕ} (hC₃ : 0 < C₃)
    (hb₃ : ∀ y : ℕ, x₀ ≤ y → |Mmu y| ≤ C₃ * y / (Real.log y) ^ (3 : ℝ))
    {t : ℝ} (ht : max (x₀ : ℝ) 3 ≤ t) :
    ‖logDivPhi t‖ ≤ 8 * C₃ * (t * Real.log t ^ 2)⁻¹ := by
  have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htx0 : (x₀ : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  have hfloor3 : 3 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht3)
  have hx0n : x₀ ≤ ⌊t⌋₊ := Nat.le_floor htx0
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h1logt : (1 : ℝ) ≤ Real.log t := by
    have hexp : Real.exp 1 ≤ t :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) ht3
    exact (Real.le_log_iff_exp_le htpos).mpr hexp
  have hfloorR3 : (3 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor3
  have hLn : (0 : ℝ) < Real.log ⌊t⌋₊ := Real.log_pos (by linarith)
  have A2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
  have hfloor_ge : t - 1 < (⌊t⌋₊ : ℝ) := by have := Nat.lt_floor_add_one t; linarith
  have htsq : t ≤ (⌊t⌋₊ : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) - (t - 1) by linarith)
      (show (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) + (t - 1) by linarith), ht3, sq_nonneg (t - 2)]
  have hlogt_le : Real.log t ≤ 2 * Real.log ⌊t⌋₊ := by
    have h := Real.log_le_log htpos htsq
    rw [Real.log_pow] at h; push_cast at h; linarith
  have B3 : (Real.log t) ^ 3 ≤ 8 * (Real.log ⌊t⌋₊) ^ 3 := by
    have e : (2 * Real.log ⌊t⌋₊) ^ 3 = 8 * (Real.log ⌊t⌋₊) ^ 3 := by ring
    rw [← e]
    exact pow_le_pow_left₀ hlogt.le hlogt_le 3
  have hrp3 : (Real.log ⌊t⌋₊) ^ (3 : ℝ) = (Real.log ⌊t⌋₊) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hMmuSum : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ) = Mmu ⌊t⌋₊ :=
    sum_Icc_zero_moebius ⌊t⌋₊
  have A1 : |Mmu ⌊t⌋₊| ≤ C₃ * ⌊t⌋₊ / (Real.log ⌊t⌋₊) ^ 3 := by
    have := hb₃ ⌊t⌋₊ hx0n; rwa [hrp3] at this
  rw [logDivPhi, deriv_logDiv htpos, hMmuSum, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg (sq_nonneg t)]
  set M := |Mmu ⌊t⌋₊| with hM
  have hLn3pos : (0 : ℝ) < (Real.log ⌊t⌋₊) ^ 3 := by positivity
  have B1 : M * (Real.log ⌊t⌋₊) ^ 3 ≤ C₃ * ⌊t⌋₊ := (le_div_iff₀ hLn3pos).mp A1
  have hnum : |1 - Real.log t| ≤ Real.log t := by
    rw [abs_of_nonpos (by linarith : 1 - Real.log t ≤ 0)]; linarith
  have key : M * (Real.log t) ^ 3 ≤ 8 * C₃ * t := by
    calc M * (Real.log t) ^ 3
        ≤ M * (8 * (Real.log ⌊t⌋₊) ^ 3) := mul_le_mul_of_nonneg_left B3 (abs_nonneg _)
      _ = 8 * (M * (Real.log ⌊t⌋₊) ^ 3) := by ring
      _ ≤ 8 * (C₃ * ⌊t⌋₊) := mul_le_mul_of_nonneg_left B1 (by norm_num)
      _ ≤ 8 * (C₃ * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left A2 hC₃.le) (by norm_num)
      _ = 8 * C₃ * t := by ring
  have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
  have step1 : |1 - Real.log t| / t ^ 2 * M ≤ Real.log t / t ^ 2 * M := by
    gcongr
  have step2 : Real.log t / t ^ 2 * M ≤ 8 * C₃ * (t * Real.log t ^ 2)⁻¹ := by
    rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_le_div_iff₀ ht2pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key htpos.le]
  exact le_trans step1 step2

/-! ## The `bigO` domination and integrability on `(1, ∞)` -/

/-- `φ = O(1/(t log²t))` (from `mmuRate` at `A = 3`), feeding the Abel integrability. -/
theorem logDivSummand_isBigO :
    (fun t : ℝ => deriv (fun x : ℝ => Real.log x / x) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ))
      =O[atTop] (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) := by
  obtain ⟨C₃, x₀, hC₃, hb₃⟩ := mmuRate_holds 3 (by norm_num)
  rw [Asymptotics.isBigO_iff]
  refine ⟨8 * C₃, ?_⟩
  filter_upwards [eventually_ge_atTop (max (x₀ : ℝ) 3)] with t ht
  have hnn : (0 : ℝ) ≤ (t * (Real.log t) ^ 2)⁻¹ := by
    have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    positivity
  change ‖logDivPhi t‖ ≤ 8 * C₃ * ‖(t * (Real.log t) ^ 2)⁻¹‖
  refine le_trans (norm_logDivPhi_le hC₃ hb₃ ht) (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]

/-- `φ` is integrable on `(1, ∞)`: locally integrable + `bigO`-integrable tail. -/
theorem integrableOn_logDivPhi_Ioi_one : IntegrableOn logDivPhi (Set.Ioi 1) := by
  have hmulLI : LocallyIntegrableOn
      (fun t => deriv (fun x : ℝ => Real.log x / x) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ)) (Set.Ici 1) :=
    locallyIntegrableOn_mul_sum_Icc (fun k => ((moebius k : ℤ) : ℝ)) (m := 0)
      zero_le_one hf_int_aux_log
  have hIci : IntegrableOn
      (fun t => deriv (fun x : ℝ => Real.log x / x) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((moebius k : ℤ) : ℝ)) (Set.Ici 1) :=
    hmulLI.integrableOn_of_isBigO_atTop logDivSummand_isBigO integrableAtFilter_inv_mul_log_sq
  exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi hIci

/-! ## The summation-index matching identity -/

/-- `Σ_{k∈Icc 0 z} f(k)·μ(k) = Σ_{d∈Icc 1 z} (μ(d)/d)·log d` (the `k = 0` term vanishes). -/
private theorem hsum_aux_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (fun x : ℝ => Real.log x / x) (k : ℝ) * ((moebius k : ℤ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℝ) / (d : ℝ)) * Real.log (d : ℝ) := by
  rw [← Finset.sum_subset (show Finset.Icc 1 n ⊆ Finset.Icc 0 n from by
        intro x hx; rw [Finset.mem_Icc] at *; omega) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    change Real.log (k : ℝ) / (k : ℝ) * ((moebius k : ℤ) : ℝ)
      = ((moebius k : ℝ) / (k : ℝ)) * Real.log (k : ℝ)
    ring
  · intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    have hx0 : x = 0 := by omega
    subst hx0; simp

/-! ## Target 1 — the `O(1)` log-weighted Möbius sum -/

/-- **The log-weighted Möbius constant.** `∃ C > 0, ∀ z ≥ 1, |Σ_{d≤z} (μ(d)/d)·log d| ≤ C`.
The load-bearing prerequisite of the sharp Barban–Vehov cancellation. Route: the finite Abel
identity `S(z) = (log z/z)·M_μ(z) − ∫_{Ioc 1 z} φ`, `mmuRate` at `A = 3` for the boundary
`≤ C₃` and the finite tail `∫_{Ioi 1}|φ|`, and a crude harmonic bound on the small window. -/
theorem abs_sum_moebius_div_mul_log_le :
    ∃ C, 0 < C ∧ ∀ z : ℕ, 1 ≤ z →
      |∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d| ≤ C := by
  obtain ⟨C₃, x₀, hC₃, hb₃⟩ := mmuRate_holds 3 (by norm_num)
  set W : ℕ := max x₀ 3 with hWdef
  have hInt_Ioi1 : IntegrableOn logDivPhi (Set.Ioi 1) := integrableOn_logDivPhi_Ioi_one
  have hInt_norm : IntegrableOn (fun t => ‖logDivPhi t‖) (Set.Ioi 1) := hInt_Ioi1.norm
  set K : ℝ := ∫ t in Set.Ioi (1 : ℝ), ‖logDivPhi t‖ with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact integral_nonneg (fun t => norm_nonneg _)
  set C : ℝ := max (C₃ + K) (Real.log (W : ℝ) * (1 + Real.log (W : ℝ))) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨C, hCpos, fun z hz => ?_⟩
  rcases le_or_gt W z with hWz | hzW
  · -- large case `z ≥ W ≥ 3`: the Abel split
    have hz3 : 3 ≤ z := le_trans (le_max_right x₀ 3) hWz
    have hx0z : x₀ ≤ z := le_trans (le_max_left x₀ 3) hWz
    have hzpos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
    have hzR3 : (3 : ℝ) ≤ z := by exact_mod_cast hz3
    have hlogz_pos : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
    have h1logz : 1 ≤ Real.log z := by
      have hexp : Real.exp 1 ≤ (z : ℝ) :=
        le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hzR3
      exact (Real.le_log_iff_exp_le hzpos).mpr hexp
    have hzne : (z : ℝ) ≠ 0 := ne_of_gt hzpos
    have hlogzne : Real.log (z : ℝ) ≠ 0 := ne_of_gt hlogz_pos
    have habel := sum_mul_eq_sub_integral_mul₀' (fun k : ℕ => ((moebius k : ℤ) : ℝ)) (by simp) z
      (fun t ht => hf_diff_aux_log t (Set.Icc_subset_Ici_self ht))
      (hf_int_aux_log.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
    rw [hsum_aux_log z, sum_Icc_zero_moebius z] at habel
    have hval : (∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d)
        = Real.log (z : ℝ) / (z : ℝ) * Mmu z - ∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t := habel
    have hrp3 : (Real.log (z : ℝ)) ^ (3 : ℝ) = (Real.log (z : ℝ)) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hbdry : |Real.log (z : ℝ) / (z : ℝ) * Mmu z| ≤ C₃ := by
      have hb := hb₃ z hx0z
      rw [hrp3] at hb
      rw [abs_mul, abs_div, abs_of_nonneg hlogz_pos.le, Nat.abs_cast]
      calc Real.log (z : ℝ) / (z : ℝ) * |Mmu z|
          ≤ Real.log (z : ℝ) / (z : ℝ) * (C₃ * (z : ℝ) / (Real.log (z : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg hlogz_pos.le hzpos.le)
        _ = C₃ / (Real.log (z : ℝ)) ^ 2 := by field_simp
        _ ≤ C₃ := div_le_self hC₃.le (by nlinarith [h1logz])
    have htail : |∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t| ≤ K := by
      calc |∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t|
          = ‖∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Set.Ioc (1 : ℝ) (z : ℝ), ‖logDivPhi t‖ := norm_integral_le_integral_norm _
        _ ≤ K := by
            rw [hKdef]
            exact setIntegral_mono_set hInt_norm (ae_of_all _ (fun t => norm_nonneg _))
              (ae_of_all _ (fun x hx => Set.Ioc_subset_Ioi_self hx))
    rw [hval]
    calc |Real.log (z : ℝ) / (z : ℝ) * Mmu z - ∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t|
        ≤ |Real.log (z : ℝ) / (z : ℝ) * Mmu z|
          + |∫ t in Set.Ioc (1 : ℝ) (z : ℝ), logDivPhi t| := by
          rw [sub_eq_add_neg]
          refine le_trans (abs_add_le _ _) (le_of_eq ?_)
          rw [abs_neg]
      _ ≤ C₃ + K := add_le_add hbdry htail
      _ ≤ C := le_max_left _ _
  · -- small window `1 ≤ z < W`: crude harmonic bound
    have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hlogz_nonneg : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg hz1R
    have hzWR : (z : ℝ) ≤ (W : ℝ) := by exact_mod_cast le_of_lt hzW
    have hlogzW : Real.log (z : ℝ) ≤ Real.log (W : ℝ) := Real.log_le_log (by linarith) hzWR
    have hlogW_nonneg : 0 ≤ Real.log (W : ℝ) := le_trans hlogz_nonneg hlogzW
    have hstep : |∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d|
        ≤ ∑ d ∈ Finset.Icc 1 z, Real.log (d : ℝ) / (d : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
      rw [Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hlogd_nonneg : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
      have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
      rw [abs_mul, abs_div, Nat.abs_cast, abs_of_nonneg hlogd_nonneg]
      calc |((moebius d : ℤ) : ℝ)| / (d : ℝ) * Real.log (d : ℝ)
          ≤ 1 / (d : ℝ) * Real.log (d : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlogd_nonneg
            exact (div_le_div_iff_of_pos_right hdpos).mpr hmu
        _ = Real.log (d : ℝ) / (d : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
    have hsum2 : ∑ d ∈ Finset.Icc 1 z, Real.log (d : ℝ) / (d : ℝ)
        ≤ Real.log (z : ℝ) * (1 + Real.log (z : ℝ)) := by
      calc ∑ d ∈ Finset.Icc 1 z, Real.log (d : ℝ) / (d : ℝ)
          ≤ ∑ d ∈ Finset.Icc 1 z, Real.log (z : ℝ) * (d : ℝ)⁻¹ := by
            refine Finset.sum_le_sum (fun d hd => ?_)
            rw [Finset.mem_Icc] at hd
            have hd1 : 1 ≤ d := hd.1
            have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
            have hlogd_le : Real.log (d : ℝ) ≤ Real.log (z : ℝ) :=
              Real.log_le_log hdpos (by exact_mod_cast hd.2)
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hlogd_le (by positivity)
        _ = Real.log (z : ℝ) * ∑ d ∈ Finset.Icc 1 z, (d : ℝ)⁻¹ := by rw [← Finset.mul_sum]
        _ ≤ Real.log (z : ℝ) * (1 + Real.log (z : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_Icc_le z) hlogz_nonneg
    have hmono : Real.log (z : ℝ) * (1 + Real.log (z : ℝ))
        ≤ Real.log (W : ℝ) * (1 + Real.log (W : ℝ)) :=
      mul_le_mul hlogzW (by linarith) (by linarith) hlogW_nonneg
    calc |∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d|
        ≤ ∑ d ∈ Finset.Icc 1 z, Real.log (d : ℝ) / (d : ℝ) := hstep
      _ ≤ Real.log (z : ℝ) * (1 + Real.log (z : ℝ)) := hsum2
      _ ≤ Real.log (W : ℝ) * (1 + Real.log (W : ℝ)) := hmono
      _ ≤ C := le_max_right _ _

/-! ## Target 2 — the sharp Barban–Vehov value bound `≍ 1/log z` -/

/-- The Barban–Vehov decomposition `Σ_{d≤z} θ_d/d = Mw(z) − (1/log z)·Σ (μ(d)/d)·log d`,
from `θ_d = μ(d)·(log z − log d)/log z` on `d ≤ z`. -/
private theorem grahamTheta_div_eq {z : ℕ} (hz : 3 ≤ z) :
    ∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ)
      = mwWeighted z
        - (Real.log (z : ℝ))⁻¹ * ∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d := by
  rw [mwWeighted, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hdz⟩ := hd
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hzne : (z : ℝ) ≠ 0 := ne_of_gt hzpos
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogzne : Real.log (z : ℝ) ≠ 0 := ne_of_gt hlogz_pos
  rw [grahamTheta_of_le hdz, Real.log_div hzne hdne]
  field_simp

/-- **The sharp Barban–Vehov value bound.** `∃ C > 0, ∀ z ≥ 3, |Σ_{d≤z} θ_d/d| ≤ C / log z`.
The `1/log z` gain over `abs_sum_grahamTheta_div_le`'s crude `≤ 1 + log z`; the mollifier input
to the `dh_repulsion` chain. Combines `abs_mwWeighted_le_div_log` and target 1. -/
theorem abs_sum_grahamTheta_div_le_inv_log :
    ∃ C, 0 < C ∧ ∀ z : ℕ, 3 ≤ z →
      |∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ)| ≤ C / Real.log z := by
  obtain ⟨Cmw, hCmw, hmw⟩ := abs_mwWeighted_le_div_log
  obtain ⟨Cs, hCs, hs⟩ := abs_sum_moebius_div_mul_log_le
  refine ⟨Cmw + Cs, by linarith, fun z hz => ?_⟩
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  rw [grahamTheta_div_eq hz]
  have h1 : |mwWeighted z| ≤ Cmw / Real.log z := hmw z hz
  have h2 : |∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d| ≤ Cs := hs z (by omega)
  calc |mwWeighted z
          - (Real.log (z : ℝ))⁻¹ * ∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d|
      ≤ |mwWeighted z|
          + |(Real.log (z : ℝ))⁻¹ * ∑ d ∈ Finset.Icc 1 z, ((moebius d : ℝ) / d) * Real.log d| := by
        rw [sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) (le_of_eq ?_)
        rw [abs_neg]
    _ ≤ Cmw / Real.log z + (Real.log (z : ℝ))⁻¹ * Cs := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_inv, abs_of_nonneg hlogz_pos.le]
        exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlogz_pos.le)
    _ = (Cmw + Cs) / Real.log z := by rw [inv_mul_eq_div, ← add_div]

end Salt.SW
