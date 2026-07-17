/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The log-sampling measure (Chowla / entropy-decrement spine, sprint-3 wave I)

The log-sampled random integer of Tao 1509.05422 §3: on the window `n ∈ (x/ω, x]`
the sampling probability is `ℙ(n) ∝ 1/n`. This file freezes the measure
`logMeasure x ω`, its probability/finite-support structure, the singleton-mass
formula, and the crude Mertens-style two-sided bound `log ω ± 1` on the
normalizer `Σ 1/n`. Waves II+ mount the window random variables `X_H`, `Y_H` on
this measure.

Hypotheses are drawn only from the `ChowlaRegime` field list (`2 ≤ x`, `2 ≤ ω`,
`ω ≤ x`); no new parameters are introduced.
-/
import Mathlib
import Salt.Entropy.Measure

open MeasureTheory Real Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- The log-sampling measure on `(x/ω, x]`: `ℙ(n) ∝ 1/n`. -/
noncomputable def logMeasure (x ω : ℕ) : Measure ℕ :=
  ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹)⁻¹) •
    ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹ • Measure.dirac n

/-- The measure of any set as a normalized weighted sum of Dirac point masses. -/
theorem logMeasure_apply (x ω : ℕ) (S : Set ℕ) :
    logMeasure x ω S
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹ * (Measure.dirac n) S := by
  unfold logMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Every element of the window is `≥ 1` (so its reciprocal is finite and nonzero). -/
theorem window_one_le {x ω n : ℕ} (hn : n ∈ Finset.Ioc (x / ω) x) : 1 ≤ n := by
  rw [Finset.mem_Ioc] at hn
  have : 0 ≤ x / ω := Nat.zero_le _
  omega

/-- The window `(x/ω, x]` is nonempty when `2 ≤ x`, `2 ≤ ω` (as `x/ω ≤ x/2 < x`). -/
theorem window_nonempty {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    (Finset.Ioc (x / ω) x).Nonempty := by
  rw [Finset.nonempty_Ioc]; exact Nat.div_lt_self (by omega) (by omega)

/-- The normalizing sum `Σ 1/n` is finite: each summand `(n)⁻¹` with `n ≥ 1` is. -/
theorem norm_ne_top (x ω : ℕ) :
    (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹) ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  refine ENNReal.sum_lt_top.mpr (fun n hn => ?_)
  rw [ENNReal.inv_lt_top]
  have : 0 < n := window_one_le hn
  exact_mod_cast this

/-- The normalizing sum `Σ 1/n` is nonzero: the window is nonempty. -/
theorem norm_ne_zero {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹) ≠ 0 := by
  intro hsum
  rw [Finset.sum_eq_zero_iff] at hsum
  obtain ⟨n, hn⟩ := window_nonempty hx hω
  have hz := hsum n hn
  rw [ENNReal.inv_eq_zero] at hz
  exact ENNReal.natCast_ne_top n hz

/-- `logMeasure x ω` is a probability measure when `2 ≤ x`, `2 ≤ ω`. -/
theorem isProbabilityMeasure_logMeasure {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    IsProbabilityMeasure (logMeasure x ω) := by
  constructor
  rw [logMeasure_apply]
  have : (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹ * (Measure.dirac n) Set.univ)
      = ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹ :=
    Finset.sum_congr rfl (fun n _ => by simp)
  rw [this, ENNReal.inv_mul_cancel (norm_ne_zero hx hω) (norm_ne_top x ω)]

/-- `logMeasure x ω` is supported on the finite window `(x/ω, x]` (unconditional). -/
instance instFiniteSupport (x ω : ℕ) : FiniteSupport (logMeasure x ω) := by
  refine ⟨Finset.Ioc (x / ω) x, ?_⟩
  rw [ae_iff, logMeasure_apply]
  have hz : (∑ n ∈ Finset.Ioc (x / ω) x,
      (n : ℝ≥0∞)⁻¹ * (Measure.dirac n) {a | a ∉ Finset.Ioc (x / ω) x}) = 0 :=
    Finset.sum_eq_zero (fun n hn => by
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hn), mul_zero])
  rw [hz, mul_zero]

/-- The mass at `m` in the window is `(1/m) / Σ`. -/
theorem logMeasure_apply_singleton {x ω m : ℕ} (hm : m ∈ Finset.Ioc (x / ω) x) :
    logMeasure x ω {m}
      = (m : ℝ≥0∞)⁻¹ / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹) := by
  rw [logMeasure_apply, div_eq_mul_inv, mul_comm]
  congr 1
  rw [Finset.sum_eq_single m
    (fun n _ hnm => by
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hnm), mul_zero])
    (fun h => absurd hm h),
    Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr rfl), mul_one]

/-- The normalizer as a harmonic difference: `Σ_{(a,b]} 1/n = H_b − H_a` (`1 ≤ a ≤ b`). -/
theorem sum_Ioc_inv_eq_harmonic {a b : ℕ} (h1 : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (n : ℝ)⁻¹ = (harmonic b : ℝ) - (harmonic a : ℝ) := by
  have hcast : ∀ m : ℕ, (harmonic m : ℝ) = ∑ i ∈ Finset.Icc 1 m, (i : ℝ)⁻¹ := by
    intro m; rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hunion : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hcast, hcast, hunion,
    Finset.sum_union (Finset.disjoint_left.mpr (fun n hn hn' => by
      rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ioc] at hn'; omega))]
  ring

/-- Crude Mertens-style two-sided bound: `log ω − 1 ≤ Σ_{(x/ω, x]} 1/n ≤ log ω + 1`
    under the regime floors `2 ≤ x`, `2 ≤ ω`, `ω ≤ x`. -/
theorem harmonic_window_bounds {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ ∧
      ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ ≤ Real.log ω + 1 := by
  have h1 : 1 ≤ x / ω := Nat.div_pos hωx (by omega)
  have hab : x / ω ≤ x := Nat.div_le_self x ω
  have hsum := sum_Ioc_inv_eq_harmonic h1 hab
  have hLx : Real.log (x + 1) ≤ (harmonic x : ℝ) := by
    have := log_add_one_le_harmonic x; push_cast at this; linarith
  have hUx : (harmonic x : ℝ) ≤ 1 + Real.log x := harmonic_le_one_add_log x
  have hLa : Real.log (((x / ω : ℕ) : ℝ) + 1) ≤ (harmonic (x / ω) : ℝ) := by
    have := log_add_one_le_harmonic (x / ω); push_cast at this; linarith
  have hUa : (harmonic (x / ω) : ℝ) ≤ 1 + Real.log ((x / ω : ℕ) : ℝ) :=
    harmonic_le_one_add_log (x / ω)
  have hlowerkey : Real.log ω ≤ Real.log (x + 1) - Real.log ((x / ω : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < ((x / ω : ℕ) : ℝ) * (ω : ℕ) :=
      by exact_mod_cast Nat.mul_pos (by omega) (by omega)
    have hle : ((x / ω : ℕ) : ℝ) * ω ≤ (x : ℝ) + 1 := by
      have : (x / ω) * ω ≤ x := Nat.div_mul_le_self x ω
      have : ((x / ω : ℕ) : ℝ) * ω ≤ x := by exact_mod_cast this
      linarith
    have hmono := Real.log_le_log hpos hle
    rw [Real.log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))] at hmono
    linarith
  have hupperkey : Real.log x - Real.log (((x / ω : ℕ) : ℝ) + 1) ≤ Real.log ω := by
    have hlt : x < (x / ω + 1) * ω := by
      have hdm := Nat.div_add_mod x ω
      have hmod : x % ω < ω := Nat.mod_lt x (by omega)
      calc x = ω * (x / ω) + x % ω := hdm.symm
        _ < ω * (x / ω) + ω := by omega
        _ = (x / ω + 1) * ω := by ring
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hle : (x : ℝ) ≤ (((x / ω : ℕ) : ℝ) + 1) * ω := by
      have : (x : ℝ) ≤ (((x / ω + 1) * ω : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_lt hlt
      push_cast at this; linarith
    have hmono := Real.log_le_log hxpos hle
    rw [Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (by omega))] at hmono
    linarith
  refine ⟨?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith

/-- Bridge: the `ℝ≥0∞` normalizer's real part equals the real harmonic-window sum. -/
theorem norm_toReal (x ω : ℕ) :
    (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ≥0∞)⁻¹).toReal
      = ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  rw [ENNReal.toReal_sum (fun n hn =>
    (ENNReal.inv_lt_top.mpr (by exact_mod_cast (window_one_le hn : 0 < n))).ne)]
  exact Finset.sum_congr rfl (fun n _ => by rw [ENNReal.toReal_inv, ENNReal.toReal_natCast])

end Salt.Entropy.Chowla
