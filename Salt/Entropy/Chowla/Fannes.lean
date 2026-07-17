/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The entropy-comparison (Fannes-type) lemma (Chowla / entropy-decrement spine)

This file provides the wave-II inputs of the entropy-decrement argument
(Tao 1509.05422 §3):

* `entropy_sub_le_of_l1` (node D-d0): an elementary discrete Fannes bound.  For
  probability measures `μ, ν` supported on a finite set `A` with `ℓ¹` distance
  `d = ∑_{s∈A} |μ.real{s} − ν.real{s}| ≤ 1/e`,
    `|Hm[μ] − Hm[ν]| ≤ d · log |A| + binEntropy d`.
  This is a safe over-estimate of the sharp Fannes–Audenaert inequality; its
  proof is the per-point modulus of continuity of `negMulLog` combined with
  Jensen's inequality (concavity of `negMulLog`).

* `logMeasure_norm_ge_half` (node B2): the robust positive normalizer floor
  `1 − 1/ω ≤ ∑_{(x/ω, x]} 1/n` (the log-lower-bound of `harmonic_window_bounds`
  is vacuous for `ω ≤ e`, but the invariance `ℓ¹` estimate needs `Σ ≥ 1/2`).
-/
import Mathlib
import Salt.Entropy.Measure
import Salt.Entropy.Chowla.LogMeasure

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### Analytic helpers for `negMulLog` -/

/-- Subadditivity of `negMulLog` on `[0,∞)` (concavity + `negMulLog 0 = 0`). -/
private lemma nml_subadd {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    negMulLog (s + t) ≤ negMulLog s + negMulLog t := by
  rcases eq_or_lt_of_le (add_nonneg hs ht) with hst | hst
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0]
  have hmemst : (s + t) ∈ Set.Ici (0 : ℝ) := hst.le
  have hmem0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have hsum1 : s / (s + t) + t / (s + t) = 1 := by
    rw [← add_div, div_self hst.ne']
  have key1 : s / (s + t) * negMulLog (s + t) ≤ negMulLog s := by
    have hc := concaveOn_negMulLog.2 hmemst hmem0
      (by positivity : (0 : ℝ) ≤ s / (s + t)) (by positivity : (0 : ℝ) ≤ t / (s + t)) hsum1
    simp only [smul_eq_mul, negMulLog_zero, mul_zero, add_zero] at hc
    rwa [div_mul_cancel₀ _ hst.ne'] at hc
  have key2 : t / (s + t) * negMulLog (s + t) ≤ negMulLog t := by
    have hc := concaveOn_negMulLog.2 hmemst hmem0
      (by positivity : (0 : ℝ) ≤ t / (s + t)) (by positivity : (0 : ℝ) ≤ s / (s + t))
      (by rw [add_comm]; exact hsum1)
    simp only [smul_eq_mul, negMulLog_zero, mul_zero, add_zero] at hc
    rwa [div_mul_cancel₀ _ hst.ne'] at hc
  have hcomb : (s / (s + t) + t / (s + t)) * negMulLog (s + t)
      ≤ negMulLog s + negMulLog t := by
    rw [add_mul]; linarith
  rwa [hsum1, one_mul] at hcomb

/-- For `0 ≤ x ≤ 1/e`, `x ≤ negMulLog x` (uses `log x ≤ -1`). -/
private lemma nml_ge_self {x : ℝ} (hx : 0 ≤ x) (h : x ≤ Real.exp (-1)) :
    x ≤ negMulLog x := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp
  · have hlog : Real.log x ≤ -1 := by
      have := Real.log_le_log hx0 h
      rwa [Real.log_exp] at this
    rw [negMulLog, neg_mul]
    nlinarith [mul_nonneg hx (show (0 : ℝ) ≤ -1 - Real.log x by linarith)]

/-- For `x ≤ 1`, `negMulLog (1 - x) ≤ x`. -/
private lemma nml_one_sub_le {x : ℝ} (hx1 : x ≤ 1) : negMulLog (1 - x) ≤ x := by
  have := Real.negMulLog_le_one_sub_self (show (0 : ℝ) ≤ 1 - x by linarith)
  linarith

/-- The map `b ↦ negMulLog b − negMulLog (b + δ)` is monotone on `[0, 1 − δ]`
    (its derivative `log (b + δ) − log b ≥ 0`). -/
private lemma nml_incr_mono {δ : ℝ} (hδ : 0 < δ) :
    MonotoneOn (fun b : ℝ => negMulLog b - negMulLog (b + δ)) (Set.Icc 0 (1 - δ)) := by
  have hcont : ContinuousOn (fun b : ℝ => negMulLog b - negMulLog (b + δ))
      (Set.Icc 0 (1 - δ)) :=
    (Real.continuous_negMulLog.continuousOn).sub
      ((Real.continuous_negMulLog.comp (continuous_id.add continuous_const)).continuousOn)
  have key : ∀ b ∈ Set.Ioo (0 : ℝ) (1 - δ),
      HasDerivAt (fun b : ℝ => negMulLog b - negMulLog (b + δ))
        ((-Real.log b - 1) - (-Real.log (b + δ) - 1)) b := by
    intro b hb
    obtain ⟨hbl, hbr⟩ := hb
    have hb0 : b ≠ 0 := ne_of_gt hbl
    have hbδ : b + δ ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < b + δ)
    have h1 : HasDerivAt (fun b : ℝ => b + δ) 1 b := (hasDerivAt_id b).add_const δ
    have hcomp := (Real.hasDerivAt_negMulLog hbδ).comp b h1
    simp only [Function.comp_def, mul_one] at hcomp
    exact (Real.hasDerivAt_negMulLog hb0).sub hcomp
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
  · rw [interior_Icc]
    intro b hb
    exact (key b hb).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Icc] at hb
    obtain ⟨hbl, hbr⟩ := hb
    rw [(key b ⟨hbl, hbr⟩).deriv]
    have hmono : Real.log b ≤ Real.log (b + δ) :=
      Real.log_le_log hbl (by linarith)
    linarith

/-- One-sided per-point modulus: `η a − η b ≤ η |a − b|` for `a, b ∈ [0,1]` with
    `|a − b| ≤ 1/e`.  The `b ≤ a` branch is subadditivity; the `a ≤ b` branch uses
    the increment monotonicity together with `η(1−δ) ≤ δ ≤ η(δ)`. -/
private lemma nml_diff_le {a b : ℝ}
    (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : |a - b| ≤ Real.exp (-1)) :
    negMulLog a - negMulLog b ≤ negMulLog |a - b| := by
  rcases le_total b a with hba | hab'
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    have hsub := nml_subadd (show (0 : ℝ) ≤ a - b by linarith) hb0
    rw [sub_add_cancel] at hsub
    linarith
  · have habs : |a - b| = b - a := by rw [abs_of_nonpos (by linarith), neg_sub]
    have hba_le : b - a ≤ Real.exp (-1) := habs ▸ hab
    rw [habs]
    rcases eq_or_lt_of_le hab' with rfl | hlt
    · simp
    · set δ := b - a with hδdef
      have hδ0 : 0 < δ := by rw [hδdef]; linarith
      have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
      have hmono := nml_incr_mono hδ0
      have ha_mem : a ∈ Set.Icc (0 : ℝ) (1 - δ) := ⟨ha0, by rw [hδdef]; linarith⟩
      have hend_mem : (1 - δ) ∈ Set.Icc (0 : ℝ) (1 - δ) := ⟨by linarith, le_refl _⟩
      have hle := hmono ha_mem hend_mem (by rw [hδdef]; linarith)
      dsimp only at hle
      have hab_eq : a + δ = b := by rw [hδdef]; ring
      have h1δ : 1 - δ + δ = 1 := by ring
      rw [hab_eq, h1δ, negMulLog_one, sub_zero] at hle
      have h2 : negMulLog (1 - δ) ≤ δ := nml_one_sub_le hδ1
      have h3 : δ ≤ negMulLog δ := nml_ge_self hδ0.le hba_le
      linarith

/-- The two-sided per-point modulus of continuity of `negMulLog`. -/
private lemma nml_modulus {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : |a - b| ≤ Real.exp (-1)) :
    |negMulLog a - negMulLog b| ≤ negMulLog |a - b| := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := nml_diff_le hb0 hb1 ha0 ha1 (by rw [abs_sub_comm]; exact hab)
    rw [abs_sub_comm] at h
    linarith
  · exact nml_diff_le ha0 ha1 hb0 hb1 hab

/-- Jensen's inequality for `negMulLog`: for nonnegative weights `δ` on a nonempty
    finite set `A` with total `D = ∑ δ`,
      `∑_{s∈A} negMulLog (δ s) ≤ D · log |A| + negMulLog D`. -/
private lemma nml_jensen {S : Type*} (A : Finset S) (hA : A.Nonempty) (δ : S → ℝ)
    (hδ : ∀ s ∈ A, 0 ≤ δ s) :
    ∑ s ∈ A, negMulLog (δ s)
      ≤ (∑ s ∈ A, δ s) * Real.log A.card + negMulLog (∑ s ∈ A, δ s) := by
  set N : ℝ := (A.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hA
  set D : ℝ := ∑ s ∈ A, δ s with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg hδ
  have hjen : ∑ s ∈ A, N⁻¹ * negMulLog (δ s)
      ≤ negMulLog (∑ s ∈ A, N⁻¹ * δ s) := by
    have h := concaveOn_negMulLog.le_map_sum (t := A) (w := fun _ => N⁻¹) (p := δ)
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, ← hN, mul_inv_cancel₀ hNpos.ne'])
      (fun i hi => hδ i hi)
    simpa using h
  have hstep : ∑ s ∈ A, negMulLog (δ s) ≤ N * negMulLog (∑ s ∈ A, N⁻¹ * δ s) := by
    have hrw : ∑ s ∈ A, negMulLog (δ s) = N * ∑ s ∈ A, N⁻¹ * negMulLog (δ s) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hjen hNpos.le
  have hsum : ∑ s ∈ A, N⁻¹ * δ s = N⁻¹ * D := by rw [Finset.mul_sum]
  rw [hsum] at hstep
  refine hstep.trans (le_of_eq ?_)
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · rw [← hD0']; simp
  · rw [negMulLog, negMulLog, Real.log_mul (inv_ne_zero hNpos.ne') hDpos.ne', Real.log_inv]
    field_simp
    ring

/-! ### D-d0 : the discrete Fannes bound -/

/-- **D-d0.**  Elementary `ℓ¹`-Fannes bound (support-Finset form).  For probability
    measures `μ, ν` supported on a finite set `A` with `ℓ¹` distance `d ≤ 1/e`,
      `|Hm[μ] − Hm[ν]| ≤ d · log |A| + binEntropy d`. -/
theorem entropy_sub_le_of_l1
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Finset S) (hμ : μ Aᶜ = 0) (hν : ν Aᶜ = 0)
    (d : ℝ) (hd : d = ∑ s ∈ A, |μ.real {s} - ν.real {s}|)
    (hd1 : d ≤ Real.exp (-1)) :
    |Hm[μ] - Hm[ν]| ≤ d * Real.log (A.card : ℝ) + Real.binEntropy d := by
  have hAne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · exfalso
      simp only [Finset.coe_empty, Set.compl_empty, measure_univ] at hμ
      exact one_ne_zero hμ
    · exact h
  have hp1 : ∀ s : S, μ.real {s} ≤ 1 := fun s => by
    have h := measureReal_mono (μ := μ) (Set.subset_univ ({s} : Set S))
    rwa [show μ.real Set.univ = 1 from by simp [Measure.real, measure_univ]] at h
  have hq1 : ∀ s : S, ν.real {s} ≤ 1 := fun s => by
    have h := measureReal_mono (μ := ν) (Set.subset_univ ({s} : Set S))
    rwa [show ν.real Set.univ = 1 from by simp [Measure.real, measure_univ]] at h
  have hEμ : Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) :=
    measureEntropy_of_isProbabilityMeasure_finite hμ
  have hEν : Hm[ν] = ∑ s ∈ A, negMulLog (ν.real {s}) :=
    measureEntropy_of_isProbabilityMeasure_finite hν
  have hd0 : 0 ≤ d := by rw [hd]; exact Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hd_le1 : d ≤ 1 := le_trans hd1 (by
    have := Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num); linarith)
  have hterm_le : ∀ s ∈ A, |μ.real {s} - ν.real {s}| ≤ d := by
    intro s hs
    rw [hd]
    exact Finset.single_le_sum (f := fun s => |μ.real {s} - ν.real {s}|)
      (fun i _ => abs_nonneg _) hs
  calc |Hm[μ] - Hm[ν]|
      = |∑ s ∈ A, (negMulLog (μ.real {s}) - negMulLog (ν.real {s}))| := by
        rw [hEμ, hEν, ← Finset.sum_sub_distrib]
    _ ≤ ∑ s ∈ A, |negMulLog (μ.real {s}) - negMulLog (ν.real {s})| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ A, negMulLog |μ.real {s} - ν.real {s}| := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        exact nml_modulus measureReal_nonneg (hp1 s) measureReal_nonneg (hq1 s)
          (le_trans (hterm_le s hs) hd1)
    _ ≤ (∑ s ∈ A, |μ.real {s} - ν.real {s}|) * Real.log A.card
          + negMulLog (∑ s ∈ A, |μ.real {s} - ν.real {s}|) :=
        nml_jensen A hAne (fun s => |μ.real {s} - ν.real {s}|) (fun s _ => abs_nonneg _)
    _ = d * Real.log A.card + negMulLog d := by rw [← hd]
    _ ≤ d * Real.log A.card + Real.binEntropy d := by
        have hle : negMulLog d ≤ Real.binEntropy d := by
          rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
          have : 0 ≤ negMulLog (1 - d) := Real.negMulLog_nonneg (by linarith) (by linarith)
          linarith
        linarith

/-! ### B2 : the robust normalizer floor -/

/-- **B2.**  The robust positive normalizer floor: `1 − 1/ω ≤ ∑_{(x/ω, x]} 1/n`
    (each `1/n ≥ 1/x`, and the window has `x − x/ω ≥ x(1 − 1/ω)` points).  In
    particular `Σ ≥ 1/2` when `ω ≥ 2`. -/
theorem logMeasure_norm_ge_half {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (_hωx : ω ≤ x) :
    (1 : ℝ) - 1 / (ω : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hω0 : (0 : ℝ) < ω := by exact_mod_cast (show 0 < ω by omega)
  have hlb : ((Finset.Ioc (x / ω) x).card : ℝ) * (x : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by have := Nat.zero_le (x / ω); omega
    have hnx : (n : ℝ) ≤ x := by exact_mod_cast hn.2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    exact inv_anti₀ hnpos hnx
  rw [Nat.card_Ioc] at hlb
  have hle : x / ω ≤ x := Nat.div_le_self x ω
  have hdm : ((x / ω : ℕ) : ℝ) * ω ≤ x := by exact_mod_cast Nat.div_mul_le_self x ω
  have hbx1 : ((x / ω : ℕ) : ℝ) / x ≤ 1 / ω := by
    rw [div_le_iff₀ hx0, div_mul_eq_mul_div, one_mul, le_div_iff₀ hω0]
    exact hdm
  have key : (1 : ℝ) - 1 / ω ≤ ((x - x / ω : ℕ) : ℝ) * (x : ℝ)⁻¹ := by
    rw [Nat.cast_sub hle, sub_mul, mul_inv_cancel₀ hx0.ne', ← div_eq_mul_inv]
    linarith [hbx1]
  linarith [hlb, key]

end Salt.Entropy.Chowla
