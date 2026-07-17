/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The (3.11) step inequality (Chowla / entropy-decrement spine, node D-e)

Closes the two D-d obligations and assembles Tao 1509.05422 (3.11).

**Obligation (1), the ℓ¹ value**: the joint pushforward laws of `(X_H, Y_H)` under
`(T_{jH})_*μ` vs `μ` differ in `ℓ¹` by at most `8·jH·ω/x` (`joint_l1_le`) — the
pushforward `ℓ¹` contraction (`map_real_l1_le`, fiber-partition over preimages)
composed with the base telescoping bound `‖(T_t)_*μ − μ‖₁ ≤ 2·A_t/Σ`
(`base_l1_le`, edge/overlap split) and the landed `harmonic_shift_l1_le`.

**Obligation (2), the budget**: `|jointSupport| = 2^H·P_H` with
`log ≤ (3/2)·H·log 2` (`jointSupport_card`, `log_jointSupport_card_le`, via
`log_PH_le` and `ε ≤ 1/2`), and the crude-but-sufficient real-analysis chain
`(3/2)·H·log2/(logH)² + log2 ≤ H/(4·logH·logloglogH)` (`budget_real`, ≥ 3.6×
slack at the regime floor `H ≥ 4·10⁶`); `hheadroom'` gives `d ≤ 1/(logH)²`.

These feed the landed Fannes bridge `condEntropy_shift_le_of_l1`, yielding the
frozen D-d headline `condEntropy_shift_le`.  The (3.11) assembly then follows:
conditional concatenation subadditivity (`condEntropy_kwindow_le`, the
`finProdFinEquiv` reindex of `liouvilleWindow_block` plus the iterated
`entropy_triple_add_entropy_le`/`chain_rule` pair bound — invariance-free),
the per-shift headline, `mutualInfo_eq_entropy_sub_condEntropy`, and the
`ℍ(Y_H) ≤ log P_H ≤ ε²H·log 4` ceiling, divided by `kH` (`step_ineq_3_11`).
-/
import Mathlib
import Salt.Entropy.Basic
import Salt.Entropy.Chowla.InvarianceHead
import Salt.Entropy.Chowla.Windows

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### Obligation (1): the joint-law `ℓ¹` value -/

/-- Per-singleton pushforward mass as a fiber sum over `A`. -/
private lemma map_real_eq_sum_filter {β : Type*} [MeasurableSpace β]
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

/-- **Part (1i): pushforward ℓ¹ contraction.**  A pushforward under a measurable
    `g` mapping a support finset `A` into `B` does not increase the singleton ℓ¹
    distance. -/
lemma map_real_l1_le {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
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
    rw [map_real_eq_sum_filter P g hg A hPA s, map_real_eq_sum_filter Q g hg A hQA s,
        ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans (Finset.sum_le_sum hkey) (le_of_eq ?_)
  exact Finset.sum_fiberwise_of_maps_to hgAB (fun n => |P.real {n} - Q.real {n}|)

/-- **Part (1ii): base ℓ¹ bound.**  The shifted vs. unshifted log-sampling laws on
    `ℕ` differ in ℓ¹ (over the covering window `(0, x+t]`) by at most `2 A_t / Σ`. -/
lemma base_l1_le {x ω t : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
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
    have h := logMeasure_norm_ge_half hx hω hωx
    rw [← hSdef] at h
    have hωR : (2 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
    have hinv : (1 : ℝ) / (ω : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hωR
    linarith
  -- support nullity facts
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
  have hPWnull : ((logMeasure x ω).map (fun n => n + t)) ((Finset.Ioc 0 (x + t) : Set ℕ)ᶜ) = 0 := by
    rw [Measure.map_apply hshift (Finset.measurableSet _).compl]
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  -- singleton values of the unshifted law
  have hq_in : ∀ n ∈ Finset.Ioc (x / ω) x, (logMeasure x ω).real {n} = (n : ℝ)⁻¹ / S := by
    intro n hn
    rw [measureReal_def, logMeasure_apply_singleton hn, ENNReal.toReal_div, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, norm_toReal, ← hSdef]
  have hq_out : ∀ n : ℕ, n ∉ Finset.Ioc (x / ω) x → (logMeasure x ω).real {n} = 0 := by
    intro n hn
    rw [measureReal_def, logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (x / ω) x, (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) {n}) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmn : m ≠ n := fun h => hn (h ▸ hm)
      rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hmn), mul_zero]
    rw [hz, mul_zero, ENNReal.toReal_zero]
  -- singleton values of the shifted law
  have hp_in : ∀ n : ℕ, t ≤ n → ((logMeasure x ω).map (fun n => n + t)).real {n}
      = (logMeasure x ω).real {n - t} := by
    intro n ht
    rw [map_measureReal_apply hshift (measurableSet_singleton n)]
    congr 1
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  -- total masses
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
  -- pointwise `|u| = 2·max u 0 − u`
  have habs : ∀ u : ℝ, |u| = 2 * max u 0 - u := by
    intro u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  -- rewrite the ℓ¹ sum as twice the positive-part sum
  have hsum_eq : ∑ n ∈ Finset.Ioc 0 (x + t),
        |((logMeasure x ω).map (fun n => n + t)).real {n} - (logMeasure x ω).real {n}|
      = 2 * ∑ n ∈ Finset.Ioc 0 (x + t),
          max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0 := by
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
  -- the positive part vanishes off the left edge `(x/ω, x/ω+t]`
  have hvanish : ∀ n ∈ Finset.Ioc 0 (x + t), n ∉ Finset.Ioc (x / ω) (x / ω + t) →
      max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0 = 0 := by
    intro n hnW hnnot
    apply max_eq_right
    rw [Finset.mem_Ioc] at hnW
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hnnot
    have hpn : 0 ≤ ((logMeasure x ω).map (fun n => n + t)).real {n} := measureReal_nonneg
    rcases hnnot with hle | hgt
    · have hqn0 : (logMeasure x ω).real {n} = 0 :=
        hq_out n (by rw [Finset.mem_Ioc]; omega)
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
      · have hqn0 : (logMeasure x ω).real {n} = 0 :=
          hq_out n (by rw [Finset.mem_Ioc]; omega)
        rw [hqn0]; linarith
  -- the positive-part sum is at most `A_t / Σ`
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
      · have hqn0 : (logMeasure x ω).real {n} = 0 :=
          hq_out n (by rw [Finset.mem_Ioc]; omega)
        rw [hqn0]
        exact div_nonneg (by positivity) hSpos.le
    have hpn : 0 ≤ ((logMeasure x ω).map (fun n => n + t)).real {n} := measureReal_nonneg
    have hmaxle :
        max ((logMeasure x ω).real {n} - ((logMeasure x ω).map (fun n => n + t)).real {n}) 0
          ≤ (logMeasure x ω).real {n} := max_le (by linarith) measureReal_nonneg
    linarith
  -- combine
  rw [hsum_eq, mul_div_assoc]
  linarith [hbound]

/-- **The joint-law ℓ¹ estimate.**  The two joint pushforward laws
    `(T_{jH})_*μ .map (X_H,Y_H)` and `μ .map (X_H,Y_H)` differ in ℓ¹ by at most
    `8·(jH)·ω/x`. -/
theorem joint_l1_le (R : ChowlaRegime) (H j : ℕ) :
    (∑ s ∈ jointSupport R.eps H,
      |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
        - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
      ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
  haveI hμprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  haveI hPprob : IsProbabilityMeasure ((logMeasure R.x R.ω).map (fun n => n + j * H)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hm1 : 1 ≤ R.x / R.ω := Nat.div_pos R.hωx (by have := R.hω; omega)
  have hshift : Measurable (fun n : ℕ => n + j * H) := measurable_of_countable _
  have hμwin : (logMeasure R.x R.ω) ((Finset.Ioc (R.x / R.ω) R.x : Set ℕ)ᶜ) = 0 := by
    rw [logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (R.x / R.ω) R.x,
        (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) ((Finset.Ioc (R.x / R.ω) R.x : Set ℕ)ᶜ)) = 0 :=
      Finset.sum_eq_zero (fun m hm => by
        rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hm), mul_zero])
    rw [hz, mul_zero]
  have hQA : (logMeasure R.x R.ω) ((Finset.Ioc 0 (R.x + j * H) : Set ℕ)ᶜ) = 0 := by
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  have hPA : ((logMeasure R.x R.ω).map (fun n => n + j * H))
      ((Finset.Ioc 0 (R.x + j * H) : Set ℕ)ᶜ) = 0 := by
    rw [Measure.map_apply hshift (Finset.measurableSet _).compl]
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  calc (∑ s ∈ jointSupport R.eps H,
        |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
          - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
      ≤ ∑ n ∈ Finset.Ioc 0 (R.x + j * H),
          |((logMeasure R.x R.ω).map (fun n => n + j * H)).real {n}
            - (logMeasure R.x R.ω).real {n}| :=
        map_real_l1_le ((logMeasure R.x R.ω).map (fun n => n + j * H)) (logMeasure R.x R.ω)
          (jointWindow R.eps H 0) (measurable_jointWindow R.eps H 0)
          (jointSupport R.eps H) (Finset.Ioc 0 (R.x + j * H)) hPA hQA
          (fun n _ => jointWindow_mem_jointSupport R.eps H 0 n)
    _ ≤ 2 * (∑ m ∈ Finset.Ioc (R.x / R.ω) (R.x / R.ω + j * H), (m : ℝ)⁻¹)
          / (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) :=
        base_l1_le R.hx R.hω R.hωx
    _ ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) :=
        harmonic_shift_l1_le R.hx R.hω R.hωx

/-! ### Obligation (2): the Fannes budget arithmetic -/

private lemma log_le_half (t : ℝ) (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have hsqrt : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hls : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  have hle : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hsqrt
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  nlinarith [sq_nonneg (Real.sqrt t - 2), hls, hle, hsq]

private lemma exp15_le : Real.exp 15 ≤ 4000000 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h15 : Real.exp 15 = (Real.exp 5) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h5b : Real.exp 5 ≤ 148.42 := by
    rw [h5]
    calc (Real.exp 1) ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := by gcongr
      _ ≤ 148.42 := by norm_num
  rw [h15]
  calc (Real.exp 5) ^ 3 ≤ (148.42 : ℝ) ^ 3 := by gcongr
    _ ≤ 4000000 := by norm_num

private lemma log15_le : Real.log 15 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 15)]
  have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hlo : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  rw [h3]
  calc (15:ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
    _ ≤ (Real.exp 1) ^ 3 := by gcongr

theorem budget_real {H : ℕ} (hH : 4000000 ≤ H) :
    (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 + Real.log 2
      ≤ (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  set a := Real.log H with ha
  have hHR : (4000000:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  have hHpos : (0:ℝ) < (H:ℝ) := by linarith
  have ha15 : (15:ℝ) ≤ a := by
    rw [ha, Real.le_log_iff_exp_le hHpos]; exact le_trans exp15_le hHR
  have hapos : (0:ℝ) < a := by linarith
  have hT2 : Real.log a ≤ a / 5 := by
    have hval : (15:ℝ) * (a / 15) = a := by ring
    have hlogmul : Real.log a = Real.log 15 + Real.log (a / 15) := by
      rw [← Real.log_mul (by norm_num) (div_ne_zero (ne_of_gt hapos) (by norm_num)), hval]
    have hlog_a15 : Real.log (a / 15) ≤ a / 15 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hapos (by norm_num))
    have hstep : Real.log a ≤ 2 + a / 15 := by rw [hlogmul]; linarith [log15_le, hlog_a15]
    linarith [hstep, ha15]
  have hloga_pos : (0:ℝ) < Real.log a := by
    calc (0:ℝ) = Real.log 1 := Real.log_one.symm
      _ < Real.log a := Real.log_lt_log (by norm_num) (by linarith : (1:ℝ) < a)
  have hC1 : Real.log (Real.log a) ≤ a / 10 := by
    have h1 := log_le_half (Real.log a) hloga_pos; linarith [hT2]
  have hlla_pos : (0:ℝ) < Real.log (Real.log a) := by
    have h1e : (1:ℝ) < Real.log a := by
      have hlt : Real.exp 1 < a := by have := Real.exp_one_lt_d9; linarith
      have hll := Real.log_lt_log (Real.exp_pos 1) hlt
      rwa [Real.log_exp] at hll
    calc (0:ℝ) = Real.log 1 := Real.log_one.symm
      _ < Real.log (Real.log a) := Real.log_lt_log (by norm_num) h1e
  have hT4 : a ^ 2 ≤ (H:ℝ) := by
    have hsH_pos : (0:ℝ) < Real.sqrt (H:ℝ) := Real.sqrt_pos.mpr hHpos
    have hls : Real.log (Real.sqrt (H:ℝ)) = Real.log (H:ℝ) / 2 := Real.log_sqrt hHpos.le
    have hT1 : Real.log (Real.sqrt (H:ℝ)) ≤ Real.sqrt (H:ℝ) / 2 := log_le_half _ hsH_pos
    have ha_le : a ≤ Real.sqrt (H:ℝ) := by rw [ha]; rw [hls] at hT1; linarith
    have hsq : Real.sqrt (H:ℝ) ^ 2 = (H:ℝ) := Real.sq_sqrt hHpos.le
    nlinarith [ha_le, hapos, hsq, Real.sqrt_nonneg (H:ℝ)]
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have a2pos : (0:ℝ) < a ^ 2 := pow_pos hapos 2
  have hdenom_pos : (0:ℝ) < 4 * a * Real.log (Real.log a) :=
    mul_pos (mul_pos (by norm_num) hapos) hlla_pos
  have key : (3/2) * (H:ℝ) * Real.log 2 + Real.log 2 * a ^ 2 ≤ (5/2) * (H:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hT4 hlog2_pos.le, hlog2, hHpos, hlog2_pos]
  have step1 : (5 * (H:ℝ)) / (2 * a ^ 2) ≤ (H:ℝ) / (4 * a * Real.log (Real.log a)) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) a2pos) hdenom_pos]
    nlinarith [hC1, mul_pos hHpos hapos, hHpos, hapos]
  have step2 : (3/2) * (H:ℝ) * Real.log 2 / a ^ 2 + Real.log 2 ≤ (5 * (H:ℝ)) / (2 * a ^ 2) := by
    rw [div_add' _ _ _ (ne_of_gt a2pos), div_le_div_iff₀ a2pos (mul_pos (by norm_num) a2pos)]
    nlinarith [key, a2pos]
  calc (3/2) * (H:ℝ) * Real.log 2 / a ^ 2 + Real.log 2
      ≤ (5 * (H:ℝ)) / (2 * a ^ 2) := step2
    _ ≤ (H:ℝ) / (4 * a * Real.log (Real.log a)) := step1

/-! ### Obligation (2): the joint-support cardinality -/

/-- The joint support cardinality `2^H · P_H`. -/
lemma jointSupport_card (eps : ℚ) (H : ℕ) :
    (jointSupport eps H).card = 2 ^ H * PH eps H := by
  rw [jointSupport, Finset.card_product, Fintype.card_piFinset_const, Finset.card_univ,
    ZMod.card, Finset.card_pair (show (-1:ℤ) ≠ 1 by norm_num)]

/-- `log |jointSupport| ≤ (3/2)·H·log 2`. -/
lemma log_jointSupport_card_le (R : ChowlaRegime) (H : ℕ) :
    Real.log ((jointSupport R.eps H).card : ℝ) ≤ (3/2) * (H:ℝ) * Real.log 2 := by
  have hPHpos : (0:ℝ) < PH R.eps H := by exact_mod_cast PH_pos R.eps H
  have hcard : ((jointSupport R.eps H).card : ℝ) = (2:ℝ) ^ H * (PH R.eps H : ℝ) := by
    rw [jointSupport_card]; push_cast; ring
  rw [hcard, Real.log_mul (by positivity) hPHpos.ne', Real.log_pow]
  have hlogPH : Real.log (PH R.eps H) ≤ (R.eps:ℝ)^2 * (H:ℝ) * Real.log 4 := log_PH_le R.eps H
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hHnn : (0:ℝ) ≤ (H:ℝ) := by positivity
  have heps2 : (R.eps:ℝ)^2 ≤ 1/4 := by
    have hq : R.eps ^ 2 ≤ 1/4 := by nlinarith [R.heps, R.heps1]
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc; linarith [hc]
  have key : Real.log (PH R.eps H) ≤ (1/2) * (H:ℝ) * Real.log 2 := by
    rw [hlog4] at hlogPH
    nlinarith [hlogPH,
      mul_le_mul_of_nonneg_right heps2 (show (0:ℝ) ≤ (H:ℝ) * (2 * Real.log 2) by positivity)]
  linarith [key]

/-! ### The D-d headline -/

/-- **D-d headline** (frozen wave-II statement `condEntropy_shift_le`): the per-shift
    conditional-entropy gap is bounded by the Fannes budget. -/
theorem condEntropy_shift_le (R : ChowlaRegime) {H k j : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (hj : j < k) (_ha : R.a ∣ H) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  set d : ℝ := ∑ s ∈ jointSupport R.eps H,
      |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
        - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}| with hd_def
  have hd0 : 0 ≤ d := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hjl1 : d ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
    rw [hd_def]; exact joint_l1_le R H j
  have hk1 : 1 ≤ k := by omega
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (4000000:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHfloor
  have hjHle : j * H ≤ R.Hhi := by
    have hle : j * H ≤ k * H := by gcongr
    omega
  have hHhile : H ≤ R.Hhi := by
    have hle : H ≤ k * H := by
      calc H = 1 * H := (one_mul H).symm
        _ ≤ k * H := by gcongr
    omega
  have hHhipos : 0 < R.Hhi := by omega
  have hxR : (0:ℝ) < R.x := by exact_mod_cast (show 0 < R.x from by have := R.hx; omega)
  have hωR : (0:ℝ) < R.ω := by exact_mod_cast (show 0 < R.ω from by have := R.hω; omega)
  have hlogH : (0:ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogHhi : (0:ℝ) < Real.log R.Hhi :=
    Real.log_pos (by exact_mod_cast (show 1 < R.Hhi by omega))
  have hlogle : Real.log H ≤ Real.log R.Hhi :=
    Real.log_le_log (by exact_mod_cast hHpos) (by exact_mod_cast hHhile)
  -- d ≤ 1/(log H)^2
  have hd_small : d ≤ 1 / (Real.log H)^2 := by
    have h1 : d ≤ 8 * (R.Hhi:ℝ) * (R.ω:ℝ) / (R.x:ℝ) := by
      refine le_trans hjl1 ?_
      gcongr
    have hkey : 8 * (R.Hhi:ℝ) * (Real.log R.Hhi)^2 ≤ (R.x:ℝ)/(R.ω:ℝ) := by
      have hhr := R.hheadroom'
      have hdivle : ((R.x / R.ω : ℕ):ℝ) ≤ (R.x:ℝ)/(R.ω:ℝ) := Nat.cast_div_le
      calc 8 * (R.Hhi:ℝ) * (Real.log R.Hhi)^2
          = 8 * (R.Hhi:ℝ) * Real.log R.Hhi * Real.log R.Hhi := by ring
        _ ≤ ((R.x / R.ω : ℕ):ℝ) := hhr
        _ ≤ (R.x:ℝ)/(R.ω:ℝ) := hdivle
    have h2 : 8 * (R.Hhi:ℝ) * (R.ω:ℝ) / (R.x:ℝ) ≤ 1/(Real.log R.Hhi)^2 := by
      rw [div_le_div_iff₀ hxR (pow_pos hlogHhi 2)]
      have hm := mul_le_mul_of_nonneg_right hkey hωR.le
      have hxω : (R.x:ℝ)/(R.ω:ℝ) * (R.ω:ℝ) = (R.x:ℝ) := by field_simp
      rw [hxω] at hm
      nlinarith [hm]
    have hsqle : (Real.log H)^2 ≤ (Real.log R.Hhi)^2 := by nlinarith [hlogle, hlogH]
    have h3 : 1/(Real.log R.Hhi)^2 ≤ 1/(Real.log H)^2 :=
      one_div_le_one_div_of_le (pow_pos hlogH 2) hsqle
    linarith [h1, h2, h3]
  -- d ≤ exp(-1)
  have hd1 : d ≤ Real.exp (-1) := by
    have hlogH2 : (2:ℝ) ≤ Real.log H := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast hHpos)]
      have hexp2 : Real.exp 2 ≤ 8 := by
        have h := Real.exp_one_lt_d9
        have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [he2]; nlinarith [Real.exp_pos 1, h]
      linarith [hexp2, hHR]
    have hsq : (4:ℝ) ≤ (Real.log H)^2 := by nlinarith [hlogH2]
    have hq : 1/(Real.log H)^2 ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hsq
    have he : (1:ℝ)/4 ≤ Real.exp (-1) := by
      have hexp1 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) hexp1
    linarith [hd_small, hq, he]
  -- budget
  have hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
      ≤ (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
    have hL0 : 0 ≤ Real.log ((jointSupport R.eps H).card : ℝ) := by
      apply Real.log_nonneg
      rw [jointSupport_card]; push_cast
      have h2H : (1:ℝ) ≤ (2:ℝ)^H := one_le_pow₀ (by norm_num)
      have hPH1 : (1:ℝ) ≤ (PH R.eps H : ℝ) := by exact_mod_cast PH_pos R.eps H
      nlinarith [h2H, hPH1]
    have hLub := log_jointSupport_card_le R H
    have hbin : Real.binEntropy d ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hdL : d * Real.log ((jointSupport R.eps H).card : ℝ)
        ≤ (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 := by
      calc d * Real.log ((jointSupport R.eps H).card : ℝ)
          ≤ (1/(Real.log H)^2) * Real.log ((jointSupport R.eps H).card : ℝ) :=
            mul_le_mul_of_nonneg_right hd_small hL0
        _ ≤ (1/(Real.log H)^2) * ((3/2) * (H:ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hLub (by positivity)
        _ = (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 := by ring
    calc d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 + Real.log 2 := by linarith
      _ ≤ (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := budget_real hHfloor
  exact condEntropy_shift_le_of_l1 R H j d hd_def hd1 hbudget

/-! ### Conditional concatenation subadditivity -/

/-- Conditional entropy is invariant under an injective post-map of `X`. -/
lemma condEntropy_comp_of_injective {Ω S T S' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace S'] [MeasurableSingletonClass S'] [Countable S']
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    (φ : S → S') (hφ : Function.Injective φ) :
    H[fun ω => φ (X ω) | Y ; μ] = H[X | Y ; μ] := by
  have hφ_m : Measurable φ := .of_discrete
  have hφX : Measurable (fun ω => φ (X ω)) := hφ_m.comp hX
  haveI hfrφX : FiniteRange (fun ω => φ (X ω)) := inferInstanceAs (FiniteRange (φ ∘ X))
  have hpair : H[fun ω => (φ (X ω), Y ω) ; μ] = H[fun ω => (X ω, Y ω) ; μ] := by
    rw [show (fun ω => (φ (X ω), Y ω))
        = (fun p : S × T => (φ p.1, p.2)) ∘ (fun ω => (X ω, Y ω)) from rfl]
    refine entropy_comp_of_injective μ (hX.prodMk hY) (fun p : S × T => (φ p.1, p.2)) ?_
    intro p q h
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨hφ h.1, h.2⟩
  have hcr1 := chain_rule μ hφX hY
  have hcr0 := chain_rule μ hX hY
  rw [hpair] at hcr1
  linarith [hcr1, hcr0]

/-- Conditional pair subadditivity `H[(A,B)|Y] ≤ H[A|Y] + H[B|Y]`. -/
lemma condEntropy_pair_le {Ω S1 S2 T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S1] [MeasurableSingletonClass S1] [Countable S1]
    [MeasurableSpace S2] [MeasurableSingletonClass S2] [Countable S2]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] {A : Ω → S1} {B : Ω → S2} {Y : Ω → T}
    (hA : Measurable A) (hB : Measurable B) (hY : Measurable Y)
    [FiniteRange A] [FiniteRange B] [FiniteRange Y] :
    H[fun ω => (A ω, B ω) | Y ; μ] ≤ H[A | Y ; μ] + H[B | Y ; μ] := by
  have htriple := entropy_triple_add_entropy_le (μ := μ) hA hB hY
  have hreassoc : H[fun ω => ((A ω, B ω), Y ω) ; μ] = H[fun ω => (A ω, (B ω, Y ω)) ; μ] := by
    rw [show (fun ω => (A ω, (B ω, Y ω)))
        = (fun p : (S1 × S2) × T => (p.1.1, (p.1.2, p.2))) ∘ (fun ω => ((A ω, B ω), Y ω))
        from rfl]
    refine (entropy_comp_of_injective μ ((hA.prodMk hB).prodMk hY)
      (fun p : (S1 × S2) × T => (p.1.1, (p.1.2, p.2))) ?_).symm
    intro p q h
    obtain ⟨⟨a1, a2⟩, a3⟩ := p
    obtain ⟨⟨b1, b2⟩, b3⟩ := q
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  have hcr_pair := chain_rule μ (hA.prodMk hB) hY
  have hcrA := chain_rule μ hA hY
  have hcrB := chain_rule μ hB hY
  rw [hreassoc] at hcr_pair
  linarith [htriple, hcr_pair, hcrA, hcrB]

/-- Conditional `Fin k`-tuple subadditivity, by induction on `k`. -/
lemma condEntropy_finPi_le {Ω T : Type*} {H : ℕ} [MeasurableSpace Ω]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] {Y : Ω → T} (hY : Measurable Y)
    [FiniteRange Y] : ∀ (k : ℕ) (W : Fin k → Ω → (Fin H → ℤ)),
      (∀ b, Measurable (W b)) → (∀ b, FiniteRange (W b)) →
      H[fun ω => (fun b => W b ω) | Y ; μ] ≤ ∑ b : Fin k, H[W b | Y ; μ] := by
  intro k
  induction k with
  | zero =>
    intro W hW hWfr
    have hmeas : Measurable (fun ω => (fun b : Fin 0 => W b ω)) :=
      measurable_pi_lambda _ (fun b => hW b)
    haveI hfr : FiniteRange (fun ω => (fun b : Fin 0 => W b ω)) := by
      apply finiteRange_of_finset _
        (Fintype.piFinset (fun b : Fin 0 => @FiniteRange.toFinset _ _ (W b) (hWfr b)))
      intro ω
      rw [Fintype.mem_piFinset]
      intro b
      exact @FiniteRange.mem _ _ (W b) (hWfr b) ω
    have hzero : ∑ b : Fin 0, H[W b | Y ; μ] = 0 := by simp
    rw [hzero]
    calc H[fun ω => (fun b : Fin 0 => W b ω) | Y ; μ]
        ≤ H[fun ω => (fun b : Fin 0 => W b ω) ; μ] := condEntropy_le_entropy μ hmeas hY
      _ ≤ Real.log (Fintype.card (Fin 0 → (Fin H → ℤ))) := entropy_le_log_card _ μ
      _ = 0 := by rw [Fintype.card_unique, Nat.cast_one, Real.log_one]
  | succ k ih =>
    intro W hW hWfr
    have hA_meas : Measurable (W 0) := hW 0
    have hB_meas : Measurable (fun ω => (fun b : Fin k => W b.succ ω)) :=
      measurable_pi_lambda _ (fun b => hW b.succ)
    haveI hA_fr : FiniteRange (W 0) := hWfr 0
    haveI hB_fr : FiniteRange (fun ω => (fun b : Fin k => W b.succ ω)) := by
      apply finiteRange_of_finset _
        (Fintype.piFinset (fun b : Fin k => @FiniteRange.toFinset _ _ (W b.succ) (hWfr b.succ)))
      intro ω
      rw [Fintype.mem_piFinset]
      intro b
      exact @FiniteRange.mem _ _ (W b.succ) (hWfr b.succ) ω
    have hcons_eq : (fun ω => (fun b : Fin (k+1) => W b ω))
        = (fun ω => Fin.cons (W 0 ω) (fun b : Fin k => W b.succ ω)) := by
      funext ω i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    have hcons_inj : Function.Injective
        (fun p : (Fin H → ℤ) × (Fin k → Fin H → ℤ) =>
          (Fin.cons p.1 p.2 : Fin (k+1) → (Fin H → ℤ))) := by
      have hli : Function.LeftInverse
          (fun v : Fin (k+1) → (Fin H → ℤ) => (v 0, Fin.tail v))
          (fun p : (Fin H → ℤ) × (Fin k → Fin H → ℤ) =>
            (Fin.cons p.1 p.2 : Fin (k+1) → (Fin H → ℤ))) := by
        intro p
        simp [Fin.tail_cons]
      exact hli.injective
    have hstep1 : H[fun ω => (fun b : Fin (k+1) => W b ω) | Y ; μ]
        = H[fun ω => (W 0 ω, fun b : Fin k => W b.succ ω) | Y ; μ] := by
      rw [hcons_eq]
      exact condEntropy_comp_of_injective μ (hA_meas.prodMk hB_meas) hY
        (fun p : (Fin H → ℤ) × (Fin k → Fin H → ℤ) =>
          (Fin.cons p.1 p.2 : Fin (k+1) → (Fin H → ℤ))) hcons_inj
    have hstep2 : H[fun ω => (W 0 ω, fun b : Fin k => W b.succ ω) | Y ; μ]
        ≤ H[W 0 | Y ; μ] + H[fun ω => (fun b : Fin k => W b.succ ω) | Y ; μ] :=
      condEntropy_pair_le μ hA_meas hB_meas hY
    have hstep3 : H[fun ω => (fun b : Fin k => W b.succ ω) | Y ; μ]
        ≤ ∑ b : Fin k, H[W b.succ | Y ; μ] :=
      ih (fun b => W b.succ) (fun b => hW b.succ) (fun b => hWfr b.succ)
    rw [Fin.sum_univ_succ]
    calc H[fun ω => (fun b : Fin (k+1) => W b ω) | Y ; μ]
        = H[fun ω => (W 0 ω, fun b : Fin k => W b.succ ω) | Y ; μ] := hstep1
      _ ≤ H[W 0 | Y ; μ] + H[fun ω => (fun b : Fin k => W b.succ ω) | Y ; μ] := hstep2
      _ ≤ H[W 0 | Y ; μ] + ∑ b : Fin k, H[W b.succ | Y ; μ] := by linarith [hstep3]

/-- **Conditional concatenation subadditivity.**  The `kH`-window's conditional
    entropy is at most the sum of its `k` shifted `H`-block conditional entropies
    (the `finProdFinEquiv` reindex of `liouvilleWindow_block`; invariance-free). -/
theorem condEntropy_kwindow_le (R : ChowlaRegime) (H k : ℕ) :
    H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ ∑ b ∈ Finset.range k,
          H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasure R.x R.ω] := by
  set μ := logMeasure R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]; exact isProbabilityMeasure_logMeasure R.hx R.hω
  have hφ_inj : Function.Injective
      (fun F : Fin k → (Fin H → ℤ) =>
        fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
    intro F G h
    funext b j
    have hcong := congrFun h (finProdFinEquiv (b, j))
    simpa [Equiv.symm_apply_apply] using hcong
  haveI hfrX : FiniteRange (fun n : ℕ => (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n)) := by
    apply finiteRange_of_finset _
      (Fintype.piFinset (fun _ : Fin k =>
        Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ))))
    intro n
    rw [Fintype.mem_piFinset]
    intro b
    exact liouvilleWindowShift_mem_piFinset H (b : ℕ) n
  have hkey : liouvilleWindow (k * H)
      = fun n => (fun F : Fin k → (Fin H → ℤ) =>
          fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
            (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n) := by
    funext n i
    change liouvilleWindow (k * H) n i
        = liouvilleWindowShift H ((finProdFinEquiv.symm i).1 : ℕ) n (finProdFinEquiv.symm i).2
    calc liouvilleWindow (k * H) n i
        = liouvilleWindow (k * H) n (finProdFinEquiv (finProdFinEquiv.symm i)) := by
          rw [finProdFinEquiv.apply_symm_apply]
      _ = liouvilleWindow H
            (n + ((finProdFinEquiv.symm i).1 : ℕ) * H) (finProdFinEquiv.symm i).2 :=
          liouvilleWindow_block k H n (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
      _ = liouvilleWindowShift H ((finProdFinEquiv.symm i).1 : ℕ) n (finProdFinEquiv.symm i).2 :=
          rfl
  rw [hkey]
  rw [condEntropy_comp_of_injective μ
      (measurable_of_countable (fun n : ℕ => (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n)))
      (measurable_residueWindow R.eps H)
      (fun F : Fin k → (Fin H → ℤ) =>
        fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
      hφ_inj]
  rw [← Fin.sum_univ_eq_sum_range
      (fun b => H[liouvilleWindowShift H b | residueWindow R.eps H ; μ]) k]
  exact condEntropy_finPi_le μ (measurable_residueWindow R.eps H) k
    (fun b : Fin k => liouvilleWindowShift H (b : ℕ))
    (fun b => measurable_liouvilleWindowShift H (b : ℕ))
    (fun b => instFiniteRangeShift H (b : ℕ))

/-! ### The (3.11) step inequality -/

/-- **The (3.11) per-step inequality** (`step_ineq_3_11`): the entropy-per-symbol of the
    `kH`-window drops by the mutual-information term plus the two explicit errors. -/
theorem step_ineq_3_11 (R : ChowlaRegime) {H k : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (ha : R.a ∣ H) (hk : 1 ≤ k) :
    H[liouvilleWindow (k * H) ; logMeasure R.x R.ω] / ((k : ℝ) * H)
      ≤ H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ)
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] / (H : ℝ)
        + ((R.eps : ℝ) ^ 2 * Real.log 4) / (k : ℝ)
        + 1 / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  haveI : IsProbabilityMeasure (logMeasure R.x R.ω) := isProbabilityMeasure_logMeasure R.hx R.hω
  have hYmeas : Measurable (residueWindow R.eps H) := measurable_residueWindow R.eps H
  have hXkHmeas : Measurable (liouvilleWindow (k * H)) := measurable_liouvilleWindow (k * H)
  have hXwinmeas : Measurable (liouvilleWindow H) := measurable_liouvilleWindow H
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hHpos
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkH : (0:ℝ) < (k:ℝ) * H := mul_pos hkpos hHR
  have hlogH : (0:ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  -- logloglogH > 0
  have hlogloglog_pos : 0 < Real.log (Real.log (Real.log H)) := by
    have hlogH3 : (3:ℝ) < Real.log H := by
      rw [Real.lt_log_iff_exp_lt hHR]
      have hexp3 : Real.exp 3 ≤ 21 := by
        have h := Real.exp_one_lt_d9
        have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; norm_num
        rw [he3]; nlinarith [Real.exp_pos 1, h]
      have h21 : (21:ℝ) < (H:ℝ) := by
        have : (4000000:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHfloor
        linarith
      linarith
    have hloglogH1 : (1:ℝ) < Real.log (Real.log H) := by
      have hlt : Real.exp 1 < Real.log H := by have := Real.exp_one_lt_d9; linarith
      have hll := Real.log_lt_log (Real.exp_pos 1) hlt
      rwa [Real.log_exp] at hll
    calc (0:ℝ) = Real.log 1 := Real.log_one.symm
      _ < Real.log (Real.log (Real.log H)) := Real.log_lt_log (by norm_num) hloglogH1
  have hDpos : (0:ℝ) < 4 * Real.log H * Real.log (Real.log (Real.log H)) := by positivity
  -- Step 1: H[XkH|Y] ≤ k*H[Xwin|Y] + k*(H/D)
  have hstep1 : H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ (k:ℝ) * H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (k:ℝ) * ((H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
    have hkw := condEntropy_kwindow_le R H k
    have hbound : ∀ b ∈ Finset.range k,
        H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasure R.x R.ω]
          ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
            + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) :=
      fun b hb => condEntropy_shift_le R hH hcpl (Finset.mem_range.mp hb) ha
    calc H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ ∑ b ∈ Finset.range k,
            H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasure R.x R.ω] := hkw
      _ ≤ ∑ _b ∈ Finset.range k,
            (H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
              + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) :=
          Finset.sum_le_sum hbound
      _ = (k:ℝ) * (H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
              + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = _ := by ring
  -- Step 2: H[XkH] ≤ H[Y] + H[XkH|Y]
  have hstep2 : H[liouvilleWindow (k * H) ; logMeasure R.x R.ω]
      ≤ H[residueWindow R.eps H ; logMeasure R.x R.ω]
        + H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω] := by
    have hcr := chain_rule (logMeasure R.x R.ω) hXkHmeas hYmeas
    have hcr' := chain_rule' (logMeasure R.x R.ω) hXkHmeas hYmeas
    have hnn := condEntropy_nonneg (residueWindow R.eps H) (liouvilleWindow (k * H))
      (logMeasure R.x R.ω)
    linarith [hcr, hcr', hnn]
  -- Step 3: H[Xwin|Y] = H[Xwin] - I
  have hstep3 : H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
      = H[liouvilleWindow H ; logMeasure R.x R.ω]
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
    have := mutualInfo_eq_entropy_sub_condEntropy hXwinmeas hYmeas (logMeasure R.x R.ω)
    linarith [this]
  -- Step 4: H[Y] ≤ eps²·H·log4
  have hstep4 : H[residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ (R.eps:ℝ)^2 * (H:ℝ) * Real.log 4 := by
    have h1 := entropy_residueWindow_le_log_PH R.eps H (logMeasure R.x R.ω)
    have h2 := log_PH_le R.eps H
    linarith [h1, h2]
  -- Combine into hmain
  rw [hstep3] at hstep1
  have hmain : H[liouvilleWindow (k * H) ; logMeasure R.x R.ω]
      ≤ (R.eps:ℝ)^2 * (H:ℝ) * Real.log 4
        + (k:ℝ) * (H[liouvilleWindow H ; logMeasure R.x R.ω]
            - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω])
        + (k:ℝ) * ((H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
    linarith [hstep1, hstep2, hstep4]
  -- Division
  rw [div_le_iff₀ hkH]
  refine hmain.trans (le_of_eq ?_)
  have hHne : (H:ℝ) ≠ 0 := hHR.ne'
  have hkne : (k:ℝ) ≠ 0 := hkpos.ne'
  have hDne : (4 * Real.log H * Real.log (Real.log (Real.log H))) ≠ 0 := hDpos.ne'
  field_simp
  ring

end Salt.Entropy.Chowla
