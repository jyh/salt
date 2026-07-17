/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The residue near-uniformity (Chowla / entropy-decrement spine, Tao (3.9))

This file is the LOWER-bound companion to `entropy_residueWindow_le_log_PH`
(`PrimeWindow.lean`).  The upper bound `H[Y_H] ≤ log P_H` holds for *any* measure;
the content here is that under the log-sampling measure `logMeasure x ω` the law of
`Y_H = residueWindow` is *nearly uniform* on `ZMod P_H`, so its entropy is close to
the maximal `log P_H`.

## The honest quantitative shape (no `o`-notation)

Two exports, in ascending strength:

* `entropy_ge_of_mass_ub` — the entropy corollary from a *hypothesized* uniformity:
  if every residue class has `logMeasure`-mass `≤ (1+δ)/P_H`, the entropy is
  `≥ log P_H − log(1+δ)`.  Pure `negMulLog` convexity; no arithmetic input.

* `residueWindow_mass_sub_le` — the class-mass comparison: each residue class `r`
  has `logMeasure`-mass within `8·P_H·ω/x` of the uniform `1/P_H`.  Proof: the
  shift `n ↦ n + t` relates class `r` to class `r + t` with `ℓ¹` cost `≤ 8·t·ω/x`
  (the SAME telescoping as `Step.lean`'s `base_l1_le`/`joint_l1_le`, re-derived
  here since this file may not import `Step`), and any two residues differ by a
  shift `t < P_H`.

* `entropy_residueWindow_ge` — combining the two: with `δ = 8·P_H²·ω/x`,
  `H[Y_H ; logMeasure x ω] ≥ log P_H − log(1 + 8·P_H²·ω/x) ≥ log P_H − 8·P_H²·ω/x`.

## THE REGIME TENSION (house re-freeze question, flagged — see the report)

`8·P_H²·ω/x` is small only when `P_H² ≪ x/ω`.  The landed `ChowlaRegime` supplies
`H ≤ Hhi ≤ x/ω` (`hheadroom`), but `P_H` can be as large as `4^{ε²H}` — exponential
in `H`, hence potentially `≫ x/ω`.  So the regime as landed does NOT supply the
`P_H`-vs-`x/ω` headroom this bound needs; the theorems below therefore take the
smallness as an EXPLICIT hypothesis (`hHead : (P_H)²·ω ≤ x`-shaped), and whether a
new regime field is needed is a house decision, not this node's to make.
-/
import Mathlib
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Entropy.Chowla.LogMeasure
import Salt.Entropy.Basic

open MeasureTheory Real Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## The entropy corollary from a hypothesized uniformity -/

/-- Pointwise `negMulLog` lower bound: for `p ≥ 0`, if either `p = 0` or
    `c ≤ −log p`, then `p·c ≤ negMulLog p`. -/
private lemma negMulLog_ge {p c : ℝ} (hp : 0 ≤ p) (h : p = 0 ∨ c ≤ -Real.log p) :
    p * c ≤ Real.negMulLog p := by
  rcases h with rfl | h
  · simp [Real.negMulLog]
  · calc p * c ≤ p * (-Real.log p) := mul_le_mul_of_nonneg_left h hp
      _ = Real.negMulLog p := by rw [Real.negMulLog]; ring

/-- **The entropy corollary (PB-floor: hypothesized uniformity).**  If a probability
    law `ν` on `ZMod P` has every singleton mass `≤ (1+δ)/P` (near-uniform within a
    factor `1+δ`), then `Hm[ν] ≥ log P − log(1+δ)`.  Pure `negMulLog` monotonicity:
    each `−mass·log mass ≥ mass·(log P − log(1+δ))`, summed against `∑ mass = 1`. -/
lemma entropy_ge_of_mass_ub {P : ℕ} [NeZero P] (ν : Measure (ZMod P))
    [IsProbabilityMeasure ν] {δ : ℝ} (hδ : 0 ≤ δ)
    (hub : ∀ r : ZMod P, ν.real {r} ≤ (1 + δ) / (P : ℝ)) :
    Real.log P - Real.log (1 + δ) ≤ Hm[ν] := by
  classical
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have hδ1 : (0 : ℝ) < 1 + δ := by linarith
  set c : ℝ := Real.log P - Real.log (1 + δ) with hc
  have htotal : ∑ r : ZMod P, ν.real {r} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, measureReal_def, measure_univ,
        ENNReal.toReal_one]
  rw [measureEntropy_of_isProbabilityMeasure_finite
        (A := Finset.univ) (show ν (↑(Finset.univ : Finset (ZMod P)))ᶜ = 0 by simp)]
  calc c = c * ∑ r : ZMod P, ν.real {r} := by rw [htotal]; ring
    _ = ∑ r : ZMod P, ν.real {r} * c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
    _ ≤ ∑ r : ZMod P, Real.negMulLog (ν.real {r}) := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        refine negMulLog_ge measureReal_nonneg ?_
        rcases eq_or_lt_of_le (measureReal_nonneg (μ := ν) (s := {r})) with h0 | hpos
        · exact Or.inl h0.symm
        · refine Or.inr ?_
          have hlog := Real.log_le_log hpos (hub r)
          rw [Real.log_div hδ1.ne' hPpos.ne'] at hlog
          rw [hc]; linarith

/-! ## Ported `ℓ¹`-shift machinery (private; verbatim from `Step`/`Invariance`/`Fannes`)

This file may not import `Step`/`Invariance`/`Fannes`, so the four ℓ¹ helpers those
files export are re-derived here as file-local `private` copies (suffix `_ru`).  Each
proof body is a verbatim port of an already kernel-checked lemma. -/

/-- Port of `logMeasure_norm_ge_half` (`Fannes.lean`). -/
private lemma norm_ge_half_ru {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (_hωx : ω ≤ x) :
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
    rw [div_le_iff₀ hx0, div_mul_eq_mul_div, one_mul, le_div_iff₀ hω0]; exact hdm
  have key : (1 : ℝ) - 1 / ω ≤ ((x - x / ω : ℕ) : ℝ) * (x : ℝ)⁻¹ := by
    rw [Nat.cast_sub hle, sub_mul, mul_inv_cancel₀ hx0.ne', ← div_eq_mul_inv]
    linarith [hbx1]
  linarith [hlb, key]

/-- Port of `harmonic_shift_l1_le` (`Invariance.lean`): `2·A_t/Σ ≤ 8·t·ω/x`. -/
private lemma harmonic_shift_l1_le_ru {x ω t : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    2 * (∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹)
        / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ 8 * t * ω / x := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hω0 : (0 : ℝ) < ω := by exact_mod_cast (show 0 < ω by omega)
  set Sden : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hSdef
  set A : ℝ := ∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹ with hAdef
  have hωR : (2 : ℝ) ≤ ω := by exact_mod_cast hω
  have hinv : (1 : ℝ) / ω ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hωR
  have hShalf : (1 : ℝ) / 2 ≤ Sden := by
    have h := norm_ge_half_ru hx hω hωx
    rw [hSdef]; linarith
  have hSpos : (0 : ℝ) < Sden := by linarith
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun m _ => by positivity)
  have hterm : ∀ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹ ≤ 2 * ω / x := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    obtain ⟨hlo, _hhi⟩ := hm
    have hm1 : x / ω + 1 ≤ m := hlo
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hlo
    have hxlt : x < ω * m := by
      have hdm : ω * (x / ω) + x % ω = x := Nat.div_add_mod x ω
      have hmod : x % ω < ω := Nat.mod_lt x (by omega)
      have hml : ω * (x / ω + 1) ≤ ω * m := Nat.mul_le_mul (le_refl ω) hm1
      have he : ω * (x / ω + 1) = ω * (x / ω) + ω := by ring
      calc x = ω * (x / ω) + x % ω := hdm.symm
        _ < ω * (x / ω) + ω := by omega
        _ = ω * (x / ω + 1) := he.symm
        _ ≤ ω * m := hml
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hmne : (m : ℝ) ≠ 0 := hmR.ne'
    have hxltR : (x : ℝ) < ω * m := by exact_mod_cast hxlt
    rw [le_div_iff₀ hx0]
    have hle : (m : ℝ)⁻¹ * x ≤ (m : ℝ)⁻¹ * (ω * m) :=
      mul_le_mul_of_nonneg_left hxltR.le (by positivity)
    have hcancel : (m : ℝ)⁻¹ * (ω * m) = ω := by
      rw [mul_comm (ω : ℝ) m, ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]
    rw [hcancel] at hle
    linarith [hle, hω0]
  have hAle : A ≤ (t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
    calc A ≤ ∑ _m ∈ Finset.Ioc (x / ω) (x / ω + t), (2 * (ω : ℝ) / (x : ℝ)) :=
            Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (x / ω) (x / ω + t)).card : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
            rw [Nat.card_Ioc, show x / ω + t - x / ω = t from by omega]
  have hstep : 2 * A / Sden ≤ 4 * A := by
    rw [div_le_iff₀ hSpos]
    nlinarith [mul_nonneg hA0 (show (0 : ℝ) ≤ 2 * Sden - 1 by linarith)]
  have hfin : 4 * A ≤ 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := by
    have h4 : 4 * A ≤ 4 * ((t : ℝ) * (2 * (ω : ℝ) / (x : ℝ))) := by linarith [hAle]
    have heq : 4 * ((t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)))
        = 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := by ring
    linarith [h4, heq.le]
  linarith [hstep, hfin]

/-- Port of `map_real_eq_sum_filter` (`Step.lean`). -/
private lemma map_real_eq_sum_filter_ru {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (P : Measure ℕ) [IsFiniteMeasure P] (g : ℕ → β) (hg : Measurable g)
    (A : Finset ℕ) (hPA : P ((A : Set ℕ)ᶜ) = 0) (s : β) :
    (P.map g).real {s} = ∑ n ∈ A.filter (fun n => g n = s), P.real {n} := by
  rw [map_measureReal_apply hg (measurableSet_singleton s),
     sum_measureReal_singleton (A.filter (fun n => g n = s))]
  apply measureReal_congr
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · apply measure_mono_null _ hPA
    intro n hn
    obtain ⟨hn1, hn2⟩ := hn
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hn1
    rw [Set.mem_compl_iff, Finset.mem_coe]
    intro hnA
    exact hn2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hnA, hn1⟩))
  · have hemp : (↑(A.filter (fun n => g n = s)) : Set ℕ) \ g ⁻¹' {s} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro n hn
      obtain ⟨hn1, hn2⟩ := hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn1
      exact hn2 (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hn1.2))
    rw [hemp, measure_empty]

/-- Port of `map_real_l1_le` (`Step.lean`): pushforward `ℓ¹` contraction. -/
private lemma map_real_l1_le_ru {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (P Q : Measure ℕ) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : ℕ → β) (hg : Measurable g) (B : Finset β) (A : Finset ℕ)
    (hPA : P ((A : Set ℕ)ᶜ) = 0) (hQA : Q ((A : Set ℕ)ᶜ) = 0)
    (hgAB : ∀ n ∈ A, g n ∈ B) :
    (∑ s ∈ B, |(P.map g).real {s} - (Q.map g).real {s}|)
      ≤ ∑ n ∈ A, |P.real {n} - Q.real {n}| := by
  classical
  have hkey : ∀ s ∈ B, |(P.map g).real {s} - (Q.map g).real {s}|
      ≤ ∑ n ∈ A.filter (fun n => g n = s), |P.real {n} - Q.real {n}| := by
    intro s _
    rw [map_real_eq_sum_filter_ru P g hg A hPA s, map_real_eq_sum_filter_ru Q g hg A hQA s,
        ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans (Finset.sum_le_sum hkey) (le_of_eq ?_)
  exact Finset.sum_fiberwise_of_maps_to hgAB (fun n => |P.real {n} - Q.real {n}|)

/-- Port of `base_l1_le` (`Step.lean`): the shifted-vs-unshifted log-sampling laws
    differ in `ℓ¹` over the covering window `(0, x+t]` by at most `2·A_t/Σ`. -/
private lemma base_l1_le_ru {x ω t : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    ∑ n ∈ Finset.Ioc 0 (x + t),
        |((logMeasure x ω).map (fun n => n + t)).real {n} - (logMeasure x ω).real {n}|
      ≤ 2 * (∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹)
          / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
  haveI hμprob : IsProbabilityMeasure (logMeasure x ω) := isProbabilityMeasure_logMeasure hx hω
  haveI hPprob : IsProbabilityMeasure ((logMeasure x ω).map (fun n => n + t)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hm1 : 1 ≤ x / ω := Nat.div_pos hωx (by omega)
  have hshift : Measurable (fun n : ℕ => n + t) := measurable_of_countable _
  set S : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hSdef
  have hSpos : 0 < S := by
    have h := norm_ge_half_ru hx hω hωx
    rw [← hSdef] at h
    have hωR : (2 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
    have hinv : (1 : ℝ) / (ω : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hωR
    linarith
  have hμwin : (logMeasure x ω) ((Finset.Ioc (x / ω) x : Set ℕ)ᶜ) = 0 := by
    rw [logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (x / ω) x,
        (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) ((Finset.Ioc (x / ω) x : Set ℕ)ᶜ)) = 0 :=
      Finset.sum_eq_zero (fun m hm => by
        rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hm), mul_zero])
    rw [hz, mul_zero]
  have hWnull : (logMeasure x ω) ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  have hPWnull : ((logMeasure x ω).map (fun n => n + t))
      ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
    rw [Measure.map_apply hshift (Finset.measurableSet _).compl]
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  have hq_in : ∀ n ∈ Finset.Ioc (x / ω) x,
      (logMeasure x ω).real {n} = (n : ℝ)⁻¹ / S := by
    intro n hn
    rw [measureReal_def, logMeasure_apply_singleton hn, ENNReal.toReal_div, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, norm_toReal, ← hSdef]
  have hq_out : ∀ n : ℕ, n ∉ Finset.Ioc (x / ω) x → (logMeasure x ω).real {n} = 0 := by
    intro n hn
    rw [measureReal_def, logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (x / ω) x,
        (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) {n}) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmn : m ≠ n := fun h => hn (h ▸ hm)
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hmn), mul_zero]
    rw [hz, mul_zero, ENNReal.toReal_zero]
  have hp_in : ∀ n : ℕ, t ≤ n → ((logMeasure x ω).map (fun n => n + t)).real {n}
      = (logMeasure x ω).real {n - t} := by
    intro n ht
    rw [map_measureReal_apply hshift (measurableSet_singleton n)]
    congr 1
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  have hqsum : ∑ n ∈ Finset.Ioc 0 (x + t), (logMeasure x ω).real {n} = 1 := by
    rw [sum_measureReal_singleton]
    have hc0 : (logMeasure x ω).real ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
      rw [measureReal_eq_zero_iff]; exact hWnull
    have hcompl := measureReal_add_measureReal_compl
      (μ := logMeasure x ω) (Finset.measurableSet (Finset.Ioc 0 (x + t)))
    rw [hc0, add_zero] at hcompl
    rw [hcompl]; simp [measureReal_def]
  have hpsum : ∑ n ∈ Finset.Ioc 0 (x + t),
      ((logMeasure x ω).map (fun n => n + t)).real {n} = 1 := by
    rw [sum_measureReal_singleton]
    have hc0 : ((logMeasure x ω).map (fun n => n + t)).real
        ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
      rw [measureReal_eq_zero_iff]; exact hPWnull
    have hcompl := measureReal_add_measureReal_compl
      (μ := (logMeasure x ω).map (fun n => n + t)) (Finset.measurableSet (Finset.Ioc 0 (x + t)))
    rw [hc0, add_zero] at hcompl
    rw [hcompl]; simp [measureReal_def]
  have habs : ∀ u : ℝ, |u| = 2 * max u 0 - u := by
    intro u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  have hsum_eq : ∑ n ∈ Finset.Ioc 0 (x + t),
        |((logMeasure x ω).map (fun n => n + t)).real {n} - (logMeasure x ω).real {n}|
      = 2 * ∑ n ∈ Finset.Ioc 0 (x + t),
          max ((logMeasure x ω).real {n}
            - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0 := by
    have hzero : ∑ n ∈ Finset.Ioc 0 (x + t),
        ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) = 0 := by
      rw [Finset.sum_sub_distrib, hqsum, hpsum, sub_self]
    calc ∑ n ∈ Finset.Ioc 0 (x + t),
          |((logMeasure x ω).map (fun n => n + t)).real {n} - (logMeasure x ω).real {n}|
        = ∑ n ∈ Finset.Ioc 0 (x + t),
            (2 * max ((logMeasure x ω).real {n}
                - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0
              - ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n})) :=
          Finset.sum_congr rfl (fun n _ => by rw [abs_sub_comm]; exact habs _)
      _ = 2 * ∑ n ∈ Finset.Ioc 0 (x + t),
            max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0
          - ∑ n ∈ Finset.Ioc 0 (x + t),
            ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 2 * ∑ n ∈ Finset.Ioc 0 (x + t),
            max ((logMeasure x ω).real {n}
              - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0 := by
          rw [hzero, sub_zero]
  have hvanish : ∀ n ∈ Finset.Ioc 0 (x + t), n ∉ Finset.Ioc (x / ω) (x / ω + t) →
      max ((logMeasure x ω).real {n}
        - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0 = 0 := by
    intro n hnW hnnot
    apply max_eq_right
    rw [Finset.mem_Ioc] at hnW
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hnnot
    have hpn : 0 ≤ ((logMeasure x ω).map (fun n => n + t)).real {n} := measureReal_nonneg
    rcases hnnot with hle | hgt
    · have hqn0 : (logMeasure x ω).real {n} = 0 := hq_out n (by rw [Finset.mem_Ioc]; omega)
      rw [hqn0]; linarith
    · by_cases hnx : n ≤ x
      · have hmem : n ∈ Finset.Ioc (x / ω) x := Finset.mem_Ioc.mpr ⟨by omega, hnx⟩
        have htn : t ≤ n := by omega
        have hmemS : n - t ∈ Finset.Ioc (x / ω) x := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        rw [hq_in n hmem, hp_in n htn, hq_in (n - t) hmemS]
        have hnt_pos : (0 : ℝ) < ((n - t : ℕ) : ℝ) := by
          have : 0 < n - t := by omega
          exact_mod_cast this
        have hnt_le : ((n - t : ℕ) : ℝ) ≤ (n : ℝ) := by
          have : n - t ≤ n := by omega
          exact_mod_cast this
        have hinv : (n : ℝ)⁻¹ ≤ ((n - t : ℕ) : ℝ)⁻¹ := inv_anti₀ hnt_pos hnt_le
        have hdiv := div_le_div_of_nonneg_right hinv hSpos.le
        linarith
      · have hqn0 : (logMeasure x ω).real {n} = 0 := hq_out n (by rw [Finset.mem_Ioc]; omega)
        rw [hqn0]; linarith
  have hbound : ∑ n ∈ Finset.Ioc 0 (x + t),
        max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0
      ≤ (∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹) / S := by
    rw [← Finset.sum_subset
          (Finset.Ioc_subset_Ioc (Nat.zero_le _) (Nat.add_le_add_right (Nat.div_le_self x ω) t))
          hvanish, Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hqle : (logMeasure x ω).real {n} ≤ (n : ℝ)⁻¹ / S := by
      by_cases hnx : n ≤ x
      · exact le_of_eq (hq_in n (Finset.mem_Ioc.mpr ⟨by omega, hnx⟩))
      · have hqn0 : (logMeasure x ω).real {n} = 0 := hq_out n (by rw [Finset.mem_Ioc]; omega)
        rw [hqn0]; exact div_nonneg (by positivity) hSpos.le
    have hpn : 0 ≤ ((logMeasure x ω).map (fun n => n + t)).real {n} := measureReal_nonneg
    have hmaxle :
        max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0
          ≤ (logMeasure x ω).real {n} := max_le (by linarith) measureReal_nonneg
    linarith
  rw [hsum_eq, mul_div_assoc]
  linarith [hbound]

/-! ## The residue class-mass near-uniformity

These are stated in *explicitly-hypothesized* form (`2 ≤ x`, `2 ≤ ω`, `ω ≤ x`) rather
than `ChowlaRegime`-parametric: this respects the file's import list (`Regime` is not
imported) and is strictly more general — a `ChowlaRegime R` instantiates with
`x := R.x`, `ω := R.ω`, `eps := R.eps`, `hx := R.hx`, `hω := R.hω`, `hωx := R.hωx`. -/

/-- The residue-only `ℓ¹` shift estimate (analogue of `joint_l1_le` for the single
    datum `Y_H`).  The residue law shifted by `t` differs from the unshifted one in
    `ℓ¹` (over `ZMod P_H`) by at most `8·t·ω/x`. -/
private theorem residue_l1_le {x ω : ℕ} (eps : ℚ) (H t : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    (∑ s : ZMod (PH eps H),
      |(((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {s}
        - ((logMeasure x ω).map (residueWindow eps H)).real {s}|)
      ≤ 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := by
  haveI hμprob : IsProbabilityMeasure (logMeasure x ω) := isProbabilityMeasure_logMeasure hx hω
  haveI hPprob : IsProbabilityMeasure ((logMeasure x ω).map (fun n => n + t)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hshift : Measurable (fun n : ℕ => n + t) := measurable_of_countable _
  have hm1 : 1 ≤ x / ω := Nat.div_pos hωx (by omega)
  have hμwin : (logMeasure x ω) ((Finset.Ioc (x / ω) x : Set ℕ)ᶜ) = 0 := by
    rw [logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (x / ω) x,
        (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) ((Finset.Ioc (x / ω) x : Set ℕ)ᶜ)) = 0 :=
      Finset.sum_eq_zero (fun m hm => by
        rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hm), mul_zero])
    rw [hz, mul_zero]
  have hQA : (logMeasure x ω) ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  have hPA : ((logMeasure x ω).map (fun n => n + t))
      ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
    rw [Measure.map_apply hshift (Finset.measurableSet _).compl]
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  calc (∑ s : ZMod (PH eps H),
        |(((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {s}
          - ((logMeasure x ω).map (residueWindow eps H)).real {s}|)
      ≤ ∑ n ∈ Finset.Ioc 0 (x + t),
          |((logMeasure x ω).map (fun n => n + t)).real {n} - (logMeasure x ω).real {n}| :=
        map_real_l1_le_ru ((logMeasure x ω).map (fun n => n + t)) (logMeasure x ω)
          (residueWindow eps H) (measurable_residueWindow eps H)
          Finset.univ (Finset.Ioc 0 (x + t)) hPA hQA (fun n _ => Finset.mem_univ _)
    _ ≤ 2 * (∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹)
          / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := base_l1_le_ru hx hω hωx
    _ ≤ 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := harmonic_shift_l1_le_ru hx hω hωx

/-- Shift-commute identity: pushing `logMeasure` forward by the `ℕ`-shift `+t` and
    then by `residueWindow` re-labels the residue law by `· + t`, so the mass at `s`
    of the shifted law is the mass at `s − t` of the unshifted one. -/
private lemma map_shift_residue (x ω : ℕ) (eps : ℚ) (H t : ℕ) (s : ZMod (PH eps H)) :
    (((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {s}
      = ((logMeasure x ω).map (residueWindow eps H)).real {s - (t : ZMod (PH eps H))} := by
  have hY : Measurable (residueWindow eps H) := measurable_residueWindow eps H
  have hshift : Measurable (fun n : ℕ => n + t) := measurable_of_countable _
  have hadd : Measurable (fun y : ZMod (PH eps H) => y + (t : ZMod (PH eps H))) :=
    measurable_of_countable _
  have hcomm : (residueWindow eps H) ∘ (fun n => n + t)
      = (fun y : ZMod (PH eps H) => y + (t : ZMod (PH eps H))) ∘ (residueWindow eps H) := by
    funext n
    simp only [Function.comp_apply, residueWindow, Nat.cast_add]
  rw [Measure.map_map hY hshift, hcomm, ← Measure.map_map hadd hY,
      map_measureReal_apply hadd (measurableSet_singleton s)]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h; exact eq_sub_of_add_eq h
  · intro h; rw [h]; abel

/-- **Pairwise class-mass comparison.**  Any two residue classes have `logMeasure`-mass
    within `8·P_H·ω/x`: they differ by a shift `t = (r'−r).val < P_H`, whose `ℓ¹` cost
    is `≤ 8·t·ω/x ≤ 8·P_H·ω/x` by `residue_l1_le`. -/
lemma residueWindow_mass_pair_le {x ω : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (r r' : ZMod (PH eps H)) :
    |((logMeasure x ω).map (residueWindow eps H)).real {r}
        - ((logMeasure x ω).map (residueWindow eps H)).real {r'}|
      ≤ 8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hωnn : (0 : ℝ) ≤ ω := by positivity
  set t : ℕ := (r' - r).val with htdef
  have hct : (t : ZMod (PH eps H)) = r' - r := by rw [htdef]; exact ZMod.natCast_zmod_val _
  have htle : (t : ℝ) ≤ (PH eps H : ℝ) := by
    rw [htdef]; exact_mod_cast (ZMod.val_lt (r' - r)).le
  have hmass_r :
      (((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {r'}
        = ((logMeasure x ω).map (residueWindow eps H)).real {r} := by
    rw [map_shift_residue x ω eps H t r', hct, show r' - (r' - r) = r from by abel]
  calc |((logMeasure x ω).map (residueWindow eps H)).real {r}
          - ((logMeasure x ω).map (residueWindow eps H)).real {r'}|
      = |(((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {r'}
          - ((logMeasure x ω).map (residueWindow eps H)).real {r'}| := by rw [hmass_r]
    _ ≤ ∑ s : ZMod (PH eps H),
          |(((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {s}
            - ((logMeasure x ω).map (residueWindow eps H)).real {s}| :=
        Finset.single_le_sum (f := fun s : ZMod (PH eps H) =>
          |(((logMeasure x ω).map (fun n => n + t)).map (residueWindow eps H)).real {s}
            - ((logMeasure x ω).map (residueWindow eps H)).real {s}|)
          (fun s _ => abs_nonneg _) (Finset.mem_univ r')
    _ ≤ 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := residue_l1_le eps H t hx hω hωx
    _ ≤ 8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ) := by
        have hnum : 8 * (t : ℝ) * ω ≤ 8 * (PH eps H : ℝ) * ω := by nlinarith [htle, hωnn]
        exact div_le_div_of_nonneg_right hnum hxpos.le

/-- **The class-mass near-uniformity (PB-floor: the class-mass comparison).**  Each
    residue class `r` has `logMeasure`-mass within `8·P_H·ω/x` of the uniform `1/P_H`:
    averaging the pairwise bound against the total mass `1`. -/
lemma residueWindow_mass_sub_le {x ω : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (r : ZMod (PH eps H)) :
    |((logMeasure x ω).map (residueWindow eps H)).real {r} - 1 / (PH eps H : ℝ)|
      ≤ 8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ) := by
  haveI := isProbabilityMeasure_logMeasure hx hω
  haveI : IsProbabilityMeasure ((logMeasure x ω).map (residueWindow eps H)) :=
    Measure.isProbabilityMeasure_map (measurable_residueWindow eps H).aemeasurable
  have hPpos : (0 : ℝ) < (PH eps H : ℝ) := by exact_mod_cast PH_pos eps H
  have hcard : (Finset.univ : Finset (ZMod (PH eps H))).card = PH eps H := by
    rw [Finset.card_univ, ZMod.card]
  have htotal : ∑ r' : ZMod (PH eps H),
      ((logMeasure x ω).map (residueWindow eps H)).real {r'} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, measureReal_def, measure_univ,
        ENNReal.toReal_one]
  have hid : ((logMeasure x ω).map (residueWindow eps H)).real {r} - 1 / (PH eps H : ℝ)
      = (1 / (PH eps H : ℝ)) * ∑ r' : ZMod (PH eps H),
          (((logMeasure x ω).map (residueWindow eps H)).real {r}
            - ((logMeasure x ω).map (residueWindow eps H)).real {r'}) := by
    rw [Finset.sum_sub_distrib, htotal, Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (by positivity)]
  calc (1 / (PH eps H : ℝ)) * |∑ r' : ZMod (PH eps H),
          (((logMeasure x ω).map (residueWindow eps H)).real {r}
            - ((logMeasure x ω).map (residueWindow eps H)).real {r'})|
      ≤ (1 / (PH eps H : ℝ)) * ∑ r' : ZMod (PH eps H),
          |((logMeasure x ω).map (residueWindow eps H)).real {r}
            - ((logMeasure x ω).map (residueWindow eps H)).real {r'}| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / (PH eps H : ℝ))
          * ∑ _r' : ZMod (PH eps H), (8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun r' _ => residueWindow_mass_pair_le eps H hx hω hωx r r'))
          (by positivity)
    _ = 8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, one_div,
            inv_mul_cancel₀ hPpos.ne', one_mul]

/-- **The residue near-uniformity entropy bound (Tao's (3.9), honest quantitative
    form).**  Under `2 ≤ x`, `2 ≤ ω`, `ω ≤ x`, the residue datum `Y_H` has entropy at
    least `log P_H − log(1 + 8·P_H²·ω/x)` — the lower companion to
    `entropy_residueWindow_le_log_PH`.  The correction is small precisely when
    `P_H² ≪ x/ω`; see the file header on the regime tension. -/
theorem entropy_residueWindow_ge {x ω : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    Real.log (PH eps H) - Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
      ≤ H[residueWindow eps H ; logMeasure x ω] := by
  haveI := isProbabilityMeasure_logMeasure hx hω
  haveI : IsProbabilityMeasure ((logMeasure x ω).map (residueWindow eps H)) :=
    Measure.isProbabilityMeasure_map (measurable_residueWindow eps H).aemeasurable
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hPpos : (0 : ℝ) < (PH eps H : ℝ) := by exact_mod_cast PH_pos eps H
  set δ : ℝ := 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hub : ∀ r : ZMod (PH eps H),
      ((logMeasure x ω).map (residueWindow eps H)).real {r} ≤ (1 + δ) / (PH eps H : ℝ) := by
    intro r
    have h := (abs_le.mp (residueWindow_mass_sub_le eps H hx hω hωx r)).2
    have heq : (1 + δ) / (PH eps H : ℝ)
        = 1 / (PH eps H : ℝ) + 8 * (PH eps H : ℝ) * (ω : ℝ) / (x : ℝ) := by
      rw [hδdef]; field_simp
    rw [heq]; linarith
  rw [entropy_def]
  exact entropy_ge_of_mass_ub _ hδ0 hub

end Salt.Entropy.Chowla
