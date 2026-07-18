/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.MoebiusDiv

/-!
# The sharp weighted-Möbius rate `|Mw(n)| ≤ C / log n`

This module lands `abs_mwWeighted_le_div_log`, the quantitative decay
`∃ C, 0 < C ∧ ∀ n ≥ 3, |Mw(n)| ≤ C / log n` for the weighted Möbius partial sum
`Mw(n) = Σ_{d≤n} μ(d)/d`, the input to the sharp Barban–Vehov cancellation.

## Route (the Abel split, now cheap since `L = 0`)

MOEB-DIV landed `mwWeighted_tendsto_zero : Mw(n) → 0` and the Abel machinery. The
finite Abel identity (`sum_mul_eq_sub_integral_mul₀'` with `f = (·)⁻¹`, `c = μ`)
reads
  `Mw(n) = M_μ(n)/n − ∫_{Ioc 1 n} φ`,   `φ t = (·)⁻¹'(t) · M_μ(⌊t⌋)`.
Re-invoking mathlib's Abel-limit theorem and matching against the LANDED limit `0`
forces the improper `∫_{Ioi 1} φ = 0`. Splitting `Ioi 1 = Ioc 1 n ∪ Ioi n` gives
  `Mw(n) = M_μ(n)/n + ∫_{Ioi n} φ`,
so `|Mw(n)| ≤ |M_μ(n)|/n + ∫_{Ioi n} |φ|`. With `mmuRate` at `A = 2`,
`|φ t| ≤ 4C₂/(t log²t)` for `t ≥ max(x₀,3)` (the `abelSummand_isBigO` pointwise
computation), and `∫_{Ioi n} (t log²t)⁻¹ = 1/log n`, whence
  `|Mw(n)| ≤ C₂/(log n)² + 4C₂/log n ≤ 5C₂/log n`   (`n ≥ max(x₀,3)`),
the finite window `3 ≤ n < max(x₀,3)` absorbed via `|Mw| ≤ 1` into the constant.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open MeasureTheory Filter Topology Finset

namespace Salt.SW

open Salt.TwinBar (Mmu)

/-! ## The tail integral `∫_{Ioi a} (t log²t)⁻¹ = 1/log a` for `a > 1` -/

/-- `t ↦ -(log t)⁻¹` is an antiderivative of `(t log²t)⁻¹` on `(1, ∞)`. -/
theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
  have hx0 : x ≠ 0 := by positivity
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have h2 : HasDerivAt (fun x => (Real.log x)⁻¹) (-x⁻¹ / (Real.log x) ^ 2) x :=
    (Real.hasDerivAt_log hx0).inv hlog0
  have h3 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-x⁻¹ / (Real.log x) ^ 2)) x := h2.neg
  convert h3 using 1
  field_simp

/-- `(t log²t)⁻¹` is integrable on `(a, ∞)` for `a > 1`. -/
theorem integrableOn_inv_tlogsq_Ioi' {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun t => (t * Real.log t ^ 2)⁻¹) (Set.Ioi a) := by
  have htend : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa using h1.neg
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_neg_inv_log (lt_of_lt_of_le ha (Set.mem_Ici.mp hx)))
    (fun x hx => ?_) htend
  have hx1 : a < x := Set.mem_Ioi.mp hx
  have hx2 : (0 : ℝ) < x := by linarith
  positivity

/-- `∫_{Ioi a} (t log²t)⁻¹ = 1/log a` for `a > 1`. -/
theorem integral_inv_tlogsq_Ioi' {a : ℝ} (ha : 1 < a) :
    ∫ t in Set.Ioi a, (t * Real.log t ^ 2)⁻¹ = (Real.log a)⁻¹ := by
  have htend : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa using h1.neg
  have hkey := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_neg_inv_log (lt_of_lt_of_le ha (Set.mem_Ici.mp hx)))
    (fun x hx => by
      have hx1 : a < x := Set.mem_Ioi.mp hx
      have hx2 : (0 : ℝ) < x := by linarith
      positivity)
    htend
  simpa using hkey

/-! ## The pointwise bound on the Abel summand `φ t = (·)⁻¹'(t)·M_μ(⌊t⌋)` -/

/-- The Abel summand `φ`. -/
noncomputable def abelPhi (t : ℝ) : ℝ :=
  deriv (fun x : ℝ => x⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℝ)

/-- The pointwise domination `‖φ t‖ ≤ 4C₂/(t log²t)` for `t ≥ max(x₀,3)`, from `mmuRate`
at `A = 2` (the `abelSummand_isBigO` computation, made pointwise). -/
theorem norm_abelPhi_le {C₂ : ℝ} {x₀ : ℕ} (hC₂ : 0 < C₂)
    (hb₂ : ∀ y : ℕ, x₀ ≤ y → |Mmu y| ≤ C₂ * y / (Real.log y) ^ (2 : ℝ))
    {t : ℝ} (ht : max (x₀ : ℝ) 3 ≤ t) :
    ‖abelPhi t‖ ≤ 4 * C₂ * (t * Real.log t ^ 2)⁻¹ := by
  have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htx0 : (x₀ : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  have hfloor3 : 3 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht3)
  have hx0n : x₀ ≤ ⌊t⌋₊ := Nat.le_floor htx0
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hfloorR3 : (3 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor3
  have hLn : (0 : ℝ) < Real.log ⌊t⌋₊ := Real.log_pos (by linarith)
  have A2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
  have hfloor_ge : t - 1 < (⌊t⌋₊ : ℝ) := by have := Nat.lt_floor_add_one t; linarith
  have htsq : t ≤ (⌊t⌋₊ : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) - (t - 1) by linarith)
      (show (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) + (t - 1) by linarith), ht3, sq_nonneg (t - 2)]
  have hlogt_le : Real.log t ≤ 2 * Real.log ⌊t⌋₊ := by
    have h := Real.log_le_log htpos htsq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have B3 : (Real.log t) ^ 2 ≤ 4 * (Real.log ⌊t⌋₊) ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * Real.log ⌊t⌋₊ - Real.log t by linarith)
      (show (0 : ℝ) ≤ 2 * Real.log ⌊t⌋₊ + Real.log t by linarith)]
  have hrp : (Real.log ⌊t⌋₊) ^ (2 : ℝ) = (Real.log ⌊t⌋₊) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hMmuSum : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℝ) = Mmu ⌊t⌋₊ :=
    sum_Icc_zero_moebius ⌊t⌋₊
  have A1 : |Mmu ⌊t⌋₊| ≤ C₂ * ⌊t⌋₊ / (Real.log ⌊t⌋₊) ^ 2 := by
    have := hb₂ ⌊t⌋₊ hx0n
    rwa [hrp] at this
  rw [abelPhi, deriv_inv, hMmuSum, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
  set M := |Mmu ⌊t⌋₊| with hM
  have hLn2 : (0 : ℝ) < (Real.log ⌊t⌋₊) ^ 2 := pow_pos hLn 2
  have B1 : M * (Real.log ⌊t⌋₊) ^ 2 ≤ C₂ * ⌊t⌋₊ := (le_div_iff₀ hLn2).mp A1
  have key : M * (t * (Real.log t) ^ 2) ≤ 4 * C₂ * t ^ 2 := by
    calc M * (t * (Real.log t) ^ 2)
        ≤ M * (t * (4 * (Real.log ⌊t⌋₊) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left B3 htpos.le) (abs_nonneg _)
      _ = 4 * t * (M * (Real.log ⌊t⌋₊) ^ 2) := by ring
      _ ≤ 4 * t * (C₂ * ⌊t⌋₊) := mul_le_mul_of_nonneg_left B1 (by linarith)
      _ ≤ 4 * t * (C₂ * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left A2 hC₂.le) (by linarith)
      _ = 4 * C₂ * t ^ 2 := by ring
  rw [← div_eq_inv_mul, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (mul_pos htpos (pow_pos hlogt 2))]
  exact key

/-! ## The improper integral `∫_{Ioi 1} φ` : integrability and the value `0` -/

/-- `(·)⁻¹` is differentiable on `[1, ∞)`. -/
private theorem hf_diff_aux : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t :=
  fun _t ht => (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le one_pos ht))).differentiableAt

/-- `deriv (·)⁻¹` is locally integrable on `[1, ∞)`. -/
private theorem hf_int_aux : LocallyIntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Ici (1 : ℝ)) := by
  rw [deriv_inv']
  refine ((ContinuousOn.inv₀ ((continuous_pow 2).continuousOn) ?_).neg).locallyIntegrableOn
    measurableSet_Ici
  intro x hx
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos hx))

/-- The weighted-sum matching identity `Σ_{k∈Icc 0 n} k⁻¹·μ(k) = Mw(n)`. -/
private theorem hsum_aux (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n,
        (fun x : ℝ => x⁻¹) (k : ℝ) * ((ArithmeticFunction.moebius k : ℤ) : ℝ) = mwWeighted n := by
  rw [mwWeighted]
  rw [← Finset.sum_subset (show Finset.Icc 1 n ⊆ Finset.Icc 0 n from by
        intro x hx; rw [Finset.mem_Icc] at *; omega) ?_]
  · exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm, ← div_eq_mul_inv])
  · intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    have hx0 : x = 0 := by omega
    subst hx0; simp

/-- `φ` is integrable on `(1, ∞)`: locally integrable (mathlib's `mul_sum` lemma) plus the
`bigO`-integrable tail `1/(t log²t)` (`abelSummand_isBigO`). -/
theorem integrableOn_abelPhi_Ioi_one : IntegrableOn abelPhi (Set.Ioi 1) := by
  have hmulLI : LocallyIntegrableOn
      (fun t => deriv (fun x : ℝ => x⁻¹) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℝ)) (Set.Ici 1) :=
    locallyIntegrableOn_mul_sum_Icc (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ))
      (m := 0) zero_le_one hf_int_aux
  have hIci : IntegrableOn
      (fun t => deriv (fun x : ℝ => x⁻¹) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℝ)) (Set.Ici 1) :=
    hmulLI.integrableOn_of_isBigO_atTop abelSummand_isBigO integrableAtFilter_inv_mul_log_sq
  exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi hIci

/-- **The improper integral vanishes:** `∫_{Ioi 1} φ = 0`. Re-invoking mathlib's Abel-limit
theorem gives `Mw(n) → 0 − ∫_{Ioi 1} φ`; matching with the LANDED `mwWeighted_tendsto_zero`
forces the integral to `0`. -/
theorem integral_abelPhi_Ioi_one : ∫ t in Set.Ioi (1 : ℝ), abelPhi t = 0 := by
  have h_lim : Tendsto (fun n : ℕ => (fun x : ℝ => x⁻¹) (n : ℝ)
      * ∑ k ∈ Finset.Icc 0 n, ((ArithmeticFunction.moebius k : ℤ) : ℝ)) atTop (𝓝 0) := by
    refine Mmu_div_tendsto_zero.congr' ?_
    filter_upwards with n
    rw [sum_Icc_zero_moebius n, div_eq_inv_mul]
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (fun k : ℕ => ((ArithmeticFunction.moebius k : ℤ) : ℝ)) (by simp) hf_diff_aux hf_int_aux
    h_lim abelSummand_isBigO integrableAtFilter_inv_mul_log_sq
  have key' : Tendsto mwWeighted atTop (𝓝 (0 - ∫ t in Set.Ioi (1 : ℝ), abelPhi t)) :=
    key.congr (fun n => hsum_aux n)
  have huniq : (0 : ℝ) = 0 - ∫ t in Set.Ioi (1 : ℝ), abelPhi t :=
    tendsto_nhds_unique mwWeighted_tendsto_zero key'
  linarith [huniq]

/-! ## The sharp rate `|Mw(n)| ≤ C / log n` -/

/-- **The quantitative weighted-Möbius rate.** `∃ C > 0, ∀ n ≥ 3, |Mw(n)| ≤ C / log n`. The
input to the sharp Barban–Vehov cancellation (feeding the `dh_repulsion` chain). Route: the
finite Abel identity `Mw(n) = M_μ(n)/n − ∫_{Ioc 1 n} φ`, the improper `∫_{Ioi 1} φ = 0`, and
`mmuRate` at `A = 2` giving `∫_{Ioi n} |φ| ≤ 4C₂/log n`. -/
theorem abs_mwWeighted_le_div_log :
    ∃ C, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → |mwWeighted n| ≤ C / Real.log n := by
  obtain ⟨C₂, x₀, hC₂, hb₂⟩ := mmuRate_holds 2 (by norm_num)
  set N₀ : ℕ := max x₀ 3 with hN0def
  have hx0N0 : x₀ ≤ N₀ := le_max_left x₀ 3
  set C : ℝ := max (5 * C₂) (Real.log N₀) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hCpos, fun n hn3 => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp3 : Real.exp 1 ≤ (n : ℝ) := by
    have hlt3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    linarith
  have h1log : (1 : ℝ) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hexp3
  have hlogn : (0 : ℝ) < Real.log n := lt_of_lt_of_le one_pos h1log
  rcases le_or_gt N₀ n with hN0n | hnN0
  · -- Large case `n ≥ max(x₀,3)`: the Abel split.
    have hx0n : x₀ ≤ n := le_trans hx0N0 hN0n
    have hng1 : (1 : ℝ) < (n : ℝ) := by
      have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      linarith
    have h1n : (1 : ℝ) ≤ (n : ℝ) := le_of_lt hng1
    -- finite Abel identity
    have hfin : mwWeighted n
        = (n : ℝ)⁻¹ * Mmu n - ∫ t in Set.Ioc (1 : ℝ) (n : ℝ), abelPhi t := by
      have habel := sum_mul_eq_sub_integral_mul₀'
        (fun k : ℕ => ((ArithmeticFunction.moebius k : ℤ) : ℝ)) (by simp) n
        (fun t ht => hf_diff_aux t (Set.Icc_subset_Ici_self ht))
        (hf_int_aux.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
      rw [← hsum_aux n, ← sum_Icc_zero_moebius n]
      exact habel
    -- split of the improper integral against `∫_{Ioi 1} φ = 0`
    have hInt_Ioi1 := integrableOn_abelPhi_Ioi_one
    have hInt_Ioc : IntegrableOn abelPhi (Set.Ioc 1 (n : ℝ)) :=
      hInt_Ioi1.mono_set Set.Ioc_subset_Ioi_self
    have hInt_Ioin : IntegrableOn abelPhi (Set.Ioi (n : ℝ)) :=
      hInt_Ioi1.mono_set (Set.Ioi_subset_Ioi h1n)
    have hsplit : (0 : ℝ)
        = (∫ t in Set.Ioc (1 : ℝ) (n : ℝ), abelPhi t) + ∫ t in Set.Ioi (n : ℝ), abelPhi t := by
      rw [← integral_abelPhi_Ioi_one,
        ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hInt_Ioc hInt_Ioin,
        Set.Ioc_union_Ioi_eq_Ioi h1n]
    have hval : mwWeighted n = (n : ℝ)⁻¹ * Mmu n + ∫ t in Set.Ioi (n : ℝ), abelPhi t := by
      rw [hfin]; linarith [hsplit]
    -- boundary bound `|M_μ(n)/n| ≤ C₂/log n`
    have hMbound : |(n : ℝ)⁻¹ * Mmu n| ≤ C₂ / Real.log n := by
      have hb := hb₂ n hx0n
      have hrp : (Real.log (n : ℝ)) ^ (2 : ℝ) = (Real.log (n : ℝ)) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hrp] at hb
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      have hLsq : (0 : ℝ) < (Real.log (n : ℝ)) ^ 2 := pow_pos hlogn 2
      have h1 : |(n : ℝ)⁻¹ * Mmu n| = (n : ℝ)⁻¹ * |Mmu n| := by
        rw [abs_mul, abs_inv, Nat.abs_cast]
      have h2 : (n : ℝ)⁻¹ * |Mmu n| ≤ (n : ℝ)⁻¹ * (C₂ * (n : ℝ) / (Real.log (n : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have h3 : (n : ℝ)⁻¹ * (C₂ * (n : ℝ) / (Real.log (n : ℝ)) ^ 2)
          = C₂ / (Real.log (n : ℝ)) ^ 2 := by field_simp
      have h4 : C₂ / (Real.log (n : ℝ)) ^ 2 ≤ C₂ / Real.log n := by
        rw [div_le_div_iff₀ hLsq hlogn]
        nlinarith [mul_nonneg (mul_nonneg hC₂.le hlogn.le)
          (show (0 : ℝ) ≤ Real.log (n : ℝ) - 1 by linarith [h1log])]
      rw [h1]; linarith [h2, h3, h4]
    -- tail bound `∫_{Ioi n} |φ| ≤ 4C₂/log n`
    have hN0R : max (x₀ : ℝ) 3 ≤ (n : ℝ) := by
      have hx0n' : (x₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx0n
      have h3n' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      exact max_le hx0n' h3n'
    have htail : |∫ t in Set.Ioi (n : ℝ), abelPhi t| ≤ 4 * C₂ / Real.log n := by
      have hdom_int : IntegrableOn (fun t => 4 * C₂ * (t * Real.log t ^ 2)⁻¹)
          (Set.Ioi (n : ℝ)) := (integrableOn_inv_tlogsq_Ioi' hng1).const_mul _
      have hbound : ∀ t ∈ Set.Ioi (n : ℝ), ‖abelPhi t‖ ≤ 4 * C₂ * (t * Real.log t ^ 2)⁻¹ := by
        intro t ht
        have htn : (n : ℝ) < t := ht
        exact norm_abelPhi_le hC₂ hb₂ (le_of_lt (lt_of_le_of_lt hN0R htn))
      calc |∫ t in Set.Ioi (n : ℝ), abelPhi t|
          = ‖∫ t in Set.Ioi (n : ℝ), abelPhi t‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Set.Ioi (n : ℝ), ‖abelPhi t‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Set.Ioi (n : ℝ), 4 * C₂ * (t * Real.log t ^ 2)⁻¹ :=
            setIntegral_mono_on hInt_Ioin.norm hdom_int measurableSet_Ioi hbound
        _ = 4 * C₂ * ∫ t in Set.Ioi (n : ℝ), (t * Real.log t ^ 2)⁻¹ := by
            rw [integral_const_mul]
        _ = 4 * C₂ * (Real.log n)⁻¹ := by rw [integral_inv_tlogsq_Ioi' hng1]
        _ = 4 * C₂ / Real.log n := by rw [← div_eq_mul_inv]
    -- assemble
    calc |mwWeighted n|
        = |(n : ℝ)⁻¹ * Mmu n + ∫ t in Set.Ioi (n : ℝ), abelPhi t| := by rw [hval]
      _ ≤ |(n : ℝ)⁻¹ * Mmu n| + |∫ t in Set.Ioi (n : ℝ), abelPhi t| := abs_add_le _ _
      _ ≤ C₂ / Real.log n + 4 * C₂ / Real.log n := add_le_add hMbound htail
      _ = 5 * C₂ / Real.log n := by ring
      _ ≤ C / Real.log n := (div_le_div_iff_of_pos_right hlogn).mpr (le_max_left _ _)
  · -- Small window `3 ≤ n < max(x₀,3)`: fold into the constant via `|Mw| ≤ 1`.
    have hbound1 : |mwWeighted n| ≤ 1 := abs_mwWeighted_le_one (by omega : 1 ≤ n)
    have hnN0R : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast le_of_lt hnN0
    have hlogle : Real.log n ≤ Real.log N₀ := Real.log_le_log hn0 hnN0R
    have hlogC : Real.log n ≤ C := le_trans hlogle (le_max_right _ _)
    calc |mwWeighted n| ≤ 1 := hbound1
      _ ≤ C / Real.log n := by rw [le_div_iff₀ hlogn, one_mul]; exact hlogC

end Salt.SW
