/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun
import Salt.Brun.M5BigO
import Salt.Brun.M6

/-!
# N6.2 — Brun's theorem via Abel summation

Assembles `Salt.M5BigO.N5_3` (`TwinCountingBigO`) and
`integrableAtFilter_inv_id_mul_log_sq` (N6.1) through mathlib's
`summable_mul_of_bigO_atTop'` Abel-summation tool to conclude
`BrunStatement`: the sum of reciprocals of twin primes converges.
-/

open Filter Asymptotics MeasureTheory Set Finset

namespace Salt.N6

/-- The function `f` in the Abel-summation instantiation: `f t = 1/t`. -/
noncomputable def f6 : ℝ → ℝ := fun t => t⁻¹

/-- The coefficient sequence `c` in the Abel-summation instantiation: the
twin-prime indicator. -/
def c6 : ℕ → ℝ := fun n => if n.Prime ∧ (n + 2).Prime then (1 : ℝ) else 0

/-- The dominating function `g` in the Abel-summation instantiation. -/
noncomputable def g6 : ℝ → ℝ := fun t => 1 / (t * Real.log t ^ 2)

/-! ## `hf_diff` -/

/-- **`hf_diff`.** `‖f6 ·‖` is differentiable on `Ici 1`. (Reproduced
near-verbatim from the brief; confirmed to compile standalone.) -/
theorem hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => ‖f6 x‖) t := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have heq : (fun x : ℝ => ‖f6 x‖) =ᶠ[nhds t] (fun x => x⁻¹) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < t by linarith)] with x hx
    rw [f6, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
  exact (differentiableAt_inv (by linarith : t ≠ 0)).congr_of_eventuallyEq heq

/-! ## `hf_int` -/

/-- The pointwise value of `deriv (‖f6 ·‖)` on `Ici 1`. (Reproduced
near-verbatim from the brief; confirmed to compile standalone.) -/
theorem deriv_normf (t : ℝ) (ht : (1 : ℝ) ≤ t) :
    deriv (fun x : ℝ => ‖f6 x‖) t = -(t ^ 2)⁻¹ := by
  have heq : (fun x : ℝ => ‖f6 x‖) =ᶠ[nhds t] (fun x => x⁻¹) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < t by linarith)] with x hx
    rw [f6, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact (hasDerivAt_inv (by linarith : t ≠ 0)).deriv

/-- The simple continuous comparison function `fun t => -(t^2)⁻¹` is locally
integrable on `Ici 1` (it's continuous there, since `t ≠ 0`). -/
theorem locallyIntegrableOn_negInvSq :
    LocallyIntegrableOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Ici 1) := by
  have hcont : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Ici 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact (continuous_pow 2).continuousOn
    · intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht
      positivity
  exact hcont.locallyIntegrableOn measurableSet_Ici

/-- **`hf_int`.** `deriv (‖f6 ·‖)` is locally integrable on `Ici 1`, transported
from `locallyIntegrableOn_negInvSq` via the pointwise equality `deriv_normf`. -/
theorem hf_int : LocallyIntegrableOn (deriv (fun t : ℝ => ‖f6 t‖)) (Set.Ici 1) := by
  have heqOn : (fun t : ℝ => -(t ^ 2)⁻¹) =ᵐ[volume.restrict (Set.Ici 1)]
      deriv (fun t : ℝ => ‖f6 t‖) :=
    (ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ (fun x hx => (deriv_normf x hx).symm))
  exact locallyIntegrableOn_negInvSq.congr heqOn

/-! ## `h_bdd` -/

/-- The key counting identity: summing the twin-prime indicator over
`Icc 1 n` recovers `twinPrimeCounting n`. (Bookkeeping mirrors the
`Nat.count_eq_card_filter_range` idiom used in `Salt.M5Assembly.N5_2`.) -/
theorem sum_c_eq_twinPrimeCounting (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, c6 k = (twinPrimeCounting n : ℝ) := by
  classical
  have hstep1 : ∑ k ∈ Finset.Icc 1 n, c6 k
      = (((Finset.Icc 1 n).filter (fun k => k.Prime ∧ (k + 2).Prime)).card : ℝ) := by
    unfold c6
    exact (Finset.natCast_card_filter (R := ℝ) (fun k => k.Prime ∧ (k + 2).Prime)
      (Finset.Icc 1 n)).symm
  rw [hstep1]
  have hcount : twinPrimeCounting n
      = ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card := by
    unfold twinPrimeCounting
    rw [Nat.count_eq_card_filter_range]
  rw [hcount]
  have hset_eq : (Finset.Icc 1 n).filter (fun k => k.Prime ∧ (k + 2).Prime)
      = (Finset.range (n + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hkn⟩, hkp⟩
      exact ⟨by omega, hkp⟩
    · rintro ⟨hkn, hkp⟩
      exact ⟨⟨hkp.1.pos, by omega⟩, hkp⟩
  rw [hset_eq]

/-- **`h_bdd`.** `(fun n ↦ ‖f6 n‖ * ∑ k ∈ Icc 1 n, ‖c6 k‖) =O[atTop] fun _ ↦ 1`. -/
theorem h_bdd :
    (fun n : ℕ => ‖f6 n‖ * ∑ k ∈ Finset.Icc 1 n, ‖c6 k‖) =O[atTop] fun _ : ℕ => (1 : ℝ) := by
  -- `TwinCountingBigO`, transported to `ℕ`.
  have hN5_3 := Salt.M5BigO.N5_3
  unfold TwinCountingBigO at hN5_3
  have hnat := hN5_3.natCast_atTop (R := ℝ)
  simp only [Nat.floor_natCast] at hnat
  -- `hnat : (fun n : ℕ ↦ (twinPrimeCounting n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n:ℝ) / Real.log n ^ 2)`
  obtain ⟨C, hCpos, hC⟩ := bound_of_isBigO_nat_atTop hnat
  apply Asymptotics.IsBigO.of_bound (C + 1)
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n := by
    have := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact this.eventually_ge_atTop 1
  have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℕ) ≤ n := Filter.eventually_ge_atTop 1
  filter_upwards [hev1, hev2] with n hlog1 hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hval : ‖f6 (n : ℝ)‖ * ∑ k ∈ Finset.Icc 1 n, ‖c6 k‖
      = (n : ℝ)⁻¹ * (twinPrimeCounting n : ℝ) := by
    have hc6nn : ∀ k, ‖c6 k‖ = c6 k := by
      intro k
      unfold c6
      split
      · simp
      · simp
    simp only [hc6nn]
    rw [sum_c_eq_twinPrimeCounting]
    congr 1
    unfold f6
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)]
  rw [hval]
  have hlogsq : (1 : ℝ) ≤ Real.log n ^ 2 := by
    have heqsq : Real.log n ^ 2 = Real.log n * Real.log n := by ring
    rw [heqsq]; nlinarith [hlog1]
  have hlogsqpos : (0 : ℝ) < Real.log n ^ 2 := by linarith
  have hgpos : (0 : ℝ) < (n : ℝ) / Real.log n ^ 2 := div_pos hnpos hlogsqpos
  have hbound : (twinPrimeCounting n : ℝ) ≤ C * ((n : ℝ) / Real.log n ^ 2) := by
    have := hC hgpos.ne'
    rwa [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hgpos.le] at this
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hCpos
  have hprod : (n : ℝ)⁻¹ * (twinPrimeCounting n : ℝ)
      ≤ (n : ℝ)⁻¹ * (C * ((n : ℝ) / Real.log n ^ 2)) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hnpos))
  have heq : (n : ℝ)⁻¹ * (C * ((n : ℝ) / Real.log n ^ 2)) = C / Real.log n ^ 2 := by
    field_simp
  rw [heq] at hprod
  have hfrac : C / Real.log n ^ 2 ≤ C := by
    rw [div_le_iff₀ hlogsqpos]
    nlinarith [hCnn, hlogsq]
  have hfinal : (n : ℝ)⁻¹ * (twinPrimeCounting n : ℝ) ≤ C := le_trans hprod hfrac
  have hnormeq : ‖(n : ℝ)⁻¹ * (twinPrimeCounting n : ℝ)‖
      = (n : ℝ)⁻¹ * (twinPrimeCounting n : ℝ) := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [hnormeq, norm_one, mul_one]
  linarith [hfinal]

/-! ## `hg₁` -/

/-- **`hg₁`.** `(fun t ↦ deriv (‖f6·‖) t * ∑ k ∈ Icc 1 ⌊t⌋₊, ‖c6 k‖) =O[atTop] g6`. -/
theorem hg₁ :
    (fun t : ℝ => deriv (fun t : ℝ => ‖f6 t‖) t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖c6 k‖)
      =O[atTop] g6 := by
  have hN5_3 := Salt.M5BigO.N5_3
  unfold TwinCountingBigO at hN5_3
  obtain ⟨C, hC⟩ := isBigO_iff.mp hN5_3
  apply Asymptotics.IsBigO.of_bound (|C| + 1)
  have hev1 : ∀ᶠ t : ℝ in atTop, (1 : ℝ) < t := eventually_gt_atTop 1
  filter_upwards [hev1, hC] with t ht1 htC
  have ht1' : (1 : ℝ) ≤ t := le_of_lt ht1
  have hderiv_eq : deriv (fun t : ℝ => ‖f6 t‖) t = -(t ^ 2)⁻¹ := deriv_normf t ht1'
  have hsum_eq : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖c6 k‖ = (twinPrimeCounting ⌊t⌋₊ : ℝ) := by
    have hc6nn : ∀ k, ‖c6 k‖ = c6 k := by
      intro k; unfold c6; split <;> simp
    simp only [hc6nn]
    exact sum_c_eq_twinPrimeCounting ⌊t⌋₊
  rw [hderiv_eq, hsum_eq]
  have htpos : (0 : ℝ) < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hlogtpos : (0 : ℝ) < Real.log t := Real.log_pos ht1
  have heqg : -(t ^ 2)⁻¹ * (twinPrimeCounting ⌊t⌋₊ : ℝ)
      = -((t ^ 2)⁻¹ * (twinPrimeCounting ⌊t⌋₊ : ℝ)) := by ring
  rw [heqg, norm_neg, Real.norm_of_nonneg (by positivity)]
  have htC' : ‖(twinPrimeCounting ⌊t⌋₊ : ℝ)‖ ≤ C * ‖t / Real.log t ^ 2‖ := htC
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)] at htC'
  have htC'' : (twinPrimeCounting ⌊t⌋₊ : ℝ) ≤ |C| * ‖t / Real.log t ^ 2‖ :=
    le_trans htC' (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  have hnormtL : ‖t / Real.log t ^ 2‖ = t / Real.log t ^ 2 :=
    Real.norm_of_nonneg (by positivity)
  rw [hnormtL] at htC''
  have hstep : (t ^ 2)⁻¹ * (twinPrimeCounting ⌊t⌋₊ : ℝ)
      ≤ (t ^ 2)⁻¹ * (|C| * (t / Real.log t ^ 2)) :=
    mul_le_mul_of_nonneg_left htC'' (by positivity)
  have heqfinal : (t ^ 2)⁻¹ * (|C| * (t / Real.log t ^ 2)) = |C| * (1 / (t * Real.log t ^ 2)) := by
    have ht2ne : t ^ 2 ≠ 0 := pow_ne_zero 2 htne
    have hLne : Real.log t ^ 2 ≠ 0 := by positivity
    field_simp
  rw [heqfinal] at hstep
  have hg6eq : ‖g6 t‖ = 1 / (t * Real.log t ^ 2) := by
    unfold g6
    exact Real.norm_of_nonneg (by positivity)
  rw [hg6eq]
  nlinarith [hstep, (by positivity : (0 : ℝ) ≤ 1 / (t * Real.log t ^ 2))]

/-! ## `hg₂` -/

/-- **`hg₂`.** `g6` is integrable at the `atTop` filter — literally N6.1. -/
theorem hg₂ : IntegrableAtFilter g6 atTop := integrableAtFilter_inv_id_mul_log_sq

/-! ## Assembly -/

/-- The pointwise identity connecting the Abel-summation product `f6 n * c6 n`
to the twin-prime indicator sequence in `BrunStatement`. -/
theorem indicator_eq (n : ℕ) :
    f6 n * c6 n = Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun n => (1 : ℝ) / n) n := by
  unfold f6 c6
  by_cases h : n.Prime ∧ (n + 2).Prime
  · have hmem : n ∈ {p : ℕ | p.Prime ∧ (p + 2).Prime} := h
    rw [if_pos h, Set.indicator_of_mem hmem (fun n => (1 : ℝ) / n), one_div, mul_one]
  · have hnmem : n ∉ {p : ℕ | p.Prime ∧ (p + 2).Prime} := h
    rw [if_neg h, Set.indicator_of_notMem hnmem (fun n => (1 : ℝ) / n), mul_zero]

/-- **N6.2.** Brun's theorem: the sum of reciprocals of twin primes converges. -/
theorem N6_2 : BrunStatement := by
  have hsummable : Summable (fun n : ℕ => f6 n * c6 n) :=
    summable_mul_of_bigO_atTop' c6 hf_diff hf_int h_bdd hg₁ hg₂
  unfold BrunStatement
  exact hsummable.congr indicator_eq

end Salt.N6
