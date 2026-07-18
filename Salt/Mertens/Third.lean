/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Mertens.Second
import Salt.Mertens.ZetaSide
import Salt.Mertens.GammaIntegral

/-!
# The identification `M = γ − B` and Mertens' third theorem (MERTENS arc, MERT-3c/4)

This file closes the MERTENS arc.  It assembles the four landed inputs

* `mertens_second_sharp` (sharp Mertens-2, `Second.lean`),
* `primeZeta_tendsto` (`P(s) + log(s−1) → −B`, `ZetaSide.lean`),
* `loglog_integral_asymp` (`(s−1)·∫₂^∞ loglog·t^{−s} + log(s−1) → −γ`, `GammaIntegral.lean`),
* `neg_log_prod_eq` / `mertensB_tail_le` (Euler-product bridge, `PrimePower.lean`)

into:

* **MERT-3c** `mertensM_eq_sub` : the Meissel–Mertens constant equals `γ − B`,
  proved by the Abelian comparison `P(s) = (s−1)∫₂^∞ S(t)·t^{−s} dt` and uniqueness of
  limits, together with the interface lemma `mertens_M_unique` and the strong restatement
  `mertens_second_sharp'` (the sharp estimate holds with the explicit constant `γ − B`);
* **MERT-4** `mertens_third_log` (log-form) and `mertens_third` (product form): Mertens'
  third theorem.
-/

open Finset MeasureTheory Set Filter Topology intervalIntegral

namespace Salt.Mertens

open Salt.Maynard Salt.BrunLower

/-! ## Part A — the real-variable sharp Mertens second theorem

`mertens_second_sharp` is stated for integer `n`; the Abelian comparison needs the estimate
for the real step function `S(t) = ∑_{p ≤ t} 1/p`.  The proof is identical to the integer
case (it goes through `sum_inv_eq` directly), so we simply re-run it at real `t`. -/

/-- The real prime-reciprocal partial sum `S(t) = ∑_{p ≤ t} 1/p`. -/
noncomputable def SPartial (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊t⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- The Meissel–Mertens constant, named as the explicit value appearing in
`mertens_second_sharp`. -/
noncomputable def mertensM : ℝ := 1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2 : ℝ), hInt t

/-- `S(t) = ∑_{k ≤ ⌊t⌋} mF k · mC k` — the Abel LHS of the corpus machinery. -/
theorem SPartial_eq_sum (t : ℝ) :
    SPartial t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mF k * mC k := by
  rw [SPartial, sum_mF_mul_mC_eq t]

/-- **Real-variable sharp Mertens-2.**  `|S(t) − (log log t + M)| ≤ 12 / log t` for `t ≥ 2`. -/
theorem mertens_second_sharp_real {t : ℝ} (ht : 2 ≤ t) :
    |SPartial t - (Real.log (Real.log t) + mertensM)| ≤ 12 / Real.log t := by
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hinvnn : (0 : ℝ) ≤ (Real.log t)⁻¹ := le_of_lt (by positivity)
  rw [SPartial_eq_sum, sum_inv_eq ht]
  -- collapse to `E(t)/log t − ∫_{Ioi t} hInt`
  have hdiff : 1 + (Sfun t - Real.log t) * (Real.log t)⁻¹
        + (Real.log (Real.log t) - Real.log (Real.log 2)) + (∫ u in (2 : ℝ)..t, hInt u)
        - (Real.log (Real.log t) + mertensM)
      = (Sfun t - Real.log t) * (Real.log t)⁻¹ - ∫ u in Set.Ioi t, hInt u := by
    rw [mertensM, interval_eq_Ioi_sub ht]; ring
  rw [hdiff]
  have hb1 : |(Sfun t - Real.log t) * (Real.log t)⁻¹| ≤ 6 * (Real.log t)⁻¹ := by
    rw [abs_mul, abs_of_nonneg hinvnn]
    exact mul_le_mul_of_nonneg_right (abs_Sfun_sub_log_le ht) hinvnn
  have hb2 : |∫ u in Set.Ioi t, hInt u| ≤ 6 * (Real.log t)⁻¹ := abs_tail_le ht
  calc |(Sfun t - Real.log t) * (Real.log t)⁻¹ - ∫ u in Set.Ioi t, hInt u|
      ≤ |(Sfun t - Real.log t) * (Real.log t)⁻¹| + |∫ u in Set.Ioi t, hInt u| := by
        rw [sub_eq_add_neg, ← abs_neg (∫ u in Set.Ioi t, hInt u)]; exact abs_add_le _ _
    _ ≤ 6 * (Real.log t)⁻¹ + 6 * (Real.log t)⁻¹ := by linarith [hb1, hb2]
    _ = 12 / Real.log t := by rw [div_eq_mul_inv]; ring

/-! ## Part B — uniqueness of the Meissel–Mertens constant -/

/-- **Uniqueness of the Mertens constant.**  Any two constants for which the sharp Mertens-2
estimate holds coincide (`|M₁ − M₂| ≤ (C₁+C₂)/log n → 0`). -/
theorem mertens_M_unique {M₁ M₂ C₁ C₂ : ℝ}
    (h₁ : ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - (Real.log (Real.log n) + M₁)| ≤ C₁ / Real.log n)
    (h₂ : ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
        - (Real.log (Real.log n) + M₂)| ≤ C₂ / Real.log n) :
    M₁ = M₂ := by
  -- `(C₁+C₂)/log n → 0`
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hf : Tendsto (fun n : ℕ => (C₁ + C₂) * (Real.log n)⁻¹) atTop (𝓝 0) := by
    simpa using hlog.inv_tendsto_atTop.const_mul (C₁ + C₂)
  -- eventually `|M₁ − M₂| ≤ (C₁+C₂)·(log n)⁻¹`
  have hev : ∀ᶠ n : ℕ in atTop, |M₁ - M₂| ≤ (C₁ + C₂) * (Real.log n)⁻¹ := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have e₁ := h₁ n hn
    have e₂ := h₂ n hn
    set S := (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p) with hS
    have hkey : |M₁ - M₂|
        ≤ |S - (Real.log (Real.log n) + M₂)| + |S - (Real.log (Real.log n) + M₁)| := by
      have heq : M₁ - M₂
          = (S - (Real.log (Real.log n) + M₂)) - (S - (Real.log (Real.log n) + M₁)) := by ring
      rw [heq, sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg]
    have hsum : C₁ / Real.log n + C₂ / Real.log n = (C₁ + C₂) * (Real.log n)⁻¹ := by
      rw [← add_div, div_eq_mul_inv]
    linarith [hkey, e₁, e₂, hsum.ge, hsum.le]
  have : |M₁ - M₂| ≤ 0 := ge_of_tendsto hf hev
  have := abs_nonpos_iff.mp this
  linarith

/-! ## Part C — integrability infrastructure on `Ioi 2`

The `ζ`-side Abel integrand is `S(t)·t^{−s}`, a (step-sum)·(smooth) product.  We need it, and
the auxiliary `loglog·t^{−s}`, `log·t^{−s}` integrands, integrable on `Ioi 2` for `s > 1`.
(`GammaIntegral`'s version of `loglog·t^{−s}` is `private`, so we re-derive.) -/

/-- `|log y| ≤ y` for `y ≥ log 2` (the crossover is safely below `log 2`). -/
theorem abs_log_le_self {y : ℝ} (hy : Real.log 2 ≤ y) : |Real.log y| ≤ y := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hypos : 0 < y := lt_of_lt_of_le h2 hy
  by_cases h1 : 1 ≤ y
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos hypos]
  · replace h1 := not_le.mp h1
    rw [abs_of_nonpos (Real.log_nonpos hypos.le h1.le)]
    have hll2 : -Real.log 2 ≤ Real.log (Real.log 2) := by
      have h12 : Real.log (2⁻¹ : ℝ) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) (by nlinarith [Real.log_two_gt_d9])
      rwa [Real.log_inv] at h12
    have hmono : Real.log (Real.log 2) ≤ Real.log y := Real.log_le_log h2 hy
    linarith

/-- `|log log t| ≤ log t` for `t ≥ 2`. -/
theorem abs_loglog_le_log {t : ℝ} (ht : 2 ≤ t) : |Real.log (Real.log t)| ≤ Real.log t :=
  abs_log_le_self (Real.log_le_log (by norm_num) ht)

/-- `log t · t^{−s}` is integrable on `(2,∞)` for `s > 1` (dominated by `(2/ε)·t^{−1−ε/2}`). -/
theorem integrableOn_log_rpow_neg {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => Real.log t * t ^ (-s)) (Set.Ioi 2) := by
  set ε := s - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hg : IntegrableOn (fun t : ℝ => (2 / ε) * t ^ (-1 - ε / 2)) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  refine hg.mono' ?_ ?_
  · refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioi
    · exact Real.continuousOn_log.mono (fun x hx =>
        Set.mem_compl_singleton_iff.mpr (ne_of_gt (by simp only [Set.mem_Ioi] at hx; linarith)))
    · exact continuousOn_id.rpow_const
        (fun x hx => Or.inl (by simp only [Set.mem_Ioi] at hx; positivity))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [Set.mem_Ioi] at ht
    have htpos : (0:ℝ) < t := by linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    rw [abs_of_pos hlogpos]
    have h2 : Real.log t ≤ t ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div htpos.le (by positivity)
    have hpow : t ^ (ε / 2) * t ^ (-s) = t ^ (-1 - ε / 2) := by
      rw [← Real.rpow_add htpos]; congr 1; rw [hε]; ring
    calc Real.log t * t ^ (-s)
        ≤ (t ^ (ε / 2) / (ε / 2)) * t ^ (-s) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg htpos.le _)
      _ = (2 / ε) * t ^ (-1 - ε / 2) := by
          rw [div_mul_eq_mul_div, hpow, div_eq_mul_inv, inv_div,
            mul_comm (t ^ (-1 - ε / 2)) (2 / ε)]

/-- **Log-growth domination.**  If `|φ| ≤ A·log t + B` on `(2,∞)` and `φ` is measurable there,
then `φ·t^{−s}` is integrable on `(2,∞)`. -/
theorem integrableOn_mul_rpow_of_bound {s : ℝ} (hs : 1 < s) {φ : ℝ → ℝ} {A B : ℝ}
    (hmeas : AEStronglyMeasurable φ (volume.restrict (Set.Ioi 2)))
    (hbd : ∀ t ∈ Set.Ioi (2 : ℝ), |φ t| ≤ A * Real.log t + B) :
    IntegrableOn (fun t => φ t * t ^ (-s)) (Set.Ioi 2) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) (by norm_num)
  have hg : IntegrableOn (fun t => A * (Real.log t * t ^ (-s)) + B * t ^ (-s)) (Set.Ioi 2) :=
    ((integrableOn_log_rpow_neg hs).const_mul A).add (hrpow.const_mul B)
  refine Integrable.mono' hg ?_ ?_
  · refine hmeas.mul ?_
    exact (continuousOn_id.rpow_const
      (fun x hx => Or.inl (by simp only [Set.mem_Ioi] at hx; positivity))).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htpos : (0:ℝ) < t := by simp only [Set.mem_Ioi] at ht; linarith
    have hrnn : (0:ℝ) ≤ t ^ (-s) := Real.rpow_nonneg htpos.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrnn]
    calc |φ t| * t ^ (-s) ≤ (A * Real.log t + B) * t ^ (-s) :=
          mul_le_mul_of_nonneg_right (hbd t ht) hrnn
      _ = A * (Real.log t * t ^ (-s)) + B * t ^ (-s) := by ring

/-- `S(t) = ∑_{p≤t} 1/p` is measurable (a step function of `⌊t⌋`). -/
theorem measurable_SPartial : Measurable SPartial := by
  have : SPartial = (fun n : ℕ =>
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p) ∘ Nat.floor := rfl
  rw [this]
  exact (measurable_from_top).comp Nat.measurable_floor

/-- `S(t) ≥ 0`. -/
theorem SPartial_nonneg (t : ℝ) : 0 ≤ SPartial t :=
  Finset.sum_nonneg (fun p _ => by positivity)

/-- `S(t)·t^{−s}` is integrable on `(2,∞)` for `s > 1`. -/
theorem integrableOn_SPartial_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => SPartial t * t ^ (-s)) (Set.Ioi 2) := by
  refine integrableOn_mul_rpow_of_bound hs
    (measurable_SPartial.aestronglyMeasurable) (A := 1) (B := mertensM + 12 / Real.log 2)
    (fun t ht => ?_)
  simp only [Set.mem_Ioi] at ht
  have ht2 : (2:ℝ) ≤ t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
  have hsharp := mertens_second_sharp_real ht2
  rw [abs_of_nonneg (SPartial_nonneg t)]
  -- S t ≤ loglog t + M + 12/log t ≤ log t + (M + 12/log 2)
  have h1 : SPartial t ≤ Real.log (Real.log t) + mertensM + 12 / Real.log t := by
    have := abs_le.mp hsharp
    linarith [this.2]
  have h2 : Real.log (Real.log t) ≤ Real.log t := by
    linarith [Real.log_le_sub_one_of_pos hlogt]
  have h3 : 12 / Real.log t ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2 hlog2t
  linarith

/-- `loglog t · t^{−s}` is integrable on `(2,∞)` for `s > 1` (public version). -/
theorem integrableOn_loglog_rpow_neg {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => Real.log (Real.log t) * t ^ (-s)) (Set.Ioi 2) := by
  refine integrableOn_mul_rpow_of_bound hs ?_ (A := 1) (B := 0) (fun t ht => ?_)
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine Real.continuousOn_log.comp (Real.continuousOn_log.mono ?_) ?_
    · exact fun x hx => Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (by simp only [Set.mem_Ioi] at hx; linarith))
    · exact fun x hx => Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (Real.log_pos (by simp only [Set.mem_Ioi] at hx; linarith)))
  · simp only [Set.mem_Ioi] at ht
    have : |Real.log (Real.log t)| ≤ Real.log t := abs_loglog_le_log (by linarith)
    linarith

/-! ## Part C2 — the Abel identity `P(s) = (s−1)·∫₂^∞ S(t)·t^{−s} dt`

Abel summation of `P(s) = ∑_p p^{−s}` against `S(t) = ∑_{p≤t} 1/p`, run through the corpus
`sum_mul_eq_sub_integral_mul₁` with weight `f(t) = t^{1−s}` and coefficient `cS k = mF k · mC k`,
then passed to the limit `b = N → ∞`. -/

/-- The Abel weight `f(t) = t^{1−s}`. -/
noncomputable def fpow (s t : ℝ) : ℝ := t ^ (1 - s)

/-- The Abel coefficient `cS k = mF k · mC k = [k prime]/k`. -/
noncomputable def cS (k : ℕ) : ℝ := mF k * mC k

theorem cS_zero : cS 0 = 0 := by rw [cS, mC_zero, mul_zero]

theorem cS_one : cS 1 = 0 := by rw [cS, mC_one, mul_zero]

theorem sum_cS_eq_SPartial (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cS k = SPartial t := by
  rw [SPartial_eq_sum]; exact Finset.sum_congr rfl (fun k _ => rfl)

/-- `f'(t) = (1−s)·t^{−s}` for `t > 0`. -/
theorem hasDerivAt_fpow {s t : ℝ} (ht : 0 < t) :
    HasDerivAt (fpow s) ((1 - s) * t ^ (-s)) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := 1 - s) (Or.inl (ne_of_gt ht))
  have he : (1 - s) - 1 = -s := by ring
  rw [he] at h
  exact h

/-- The summand identity `f(k)·cS k = [k prime]·k^{−s}`, i.e. the prime-zeta term. -/
theorem fpow_cS_eq {s : ℝ} (k : ℕ) :
    fpow s k * cS k = Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => (n : ℝ) ^ (-s)) k := by
  rw [Set.indicator_apply]
  by_cases hk : k ∈ {p : ℕ | Nat.Prime p}
  · have hkp : Nat.Prime k := hk
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hkp.one_lt
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hklog : Real.log (k : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hk1)
    rw [if_pos hk]
    have hcS : cS k = (k : ℝ)⁻¹ := by rw [cS, mF, mC, if_pos hkp]; field_simp
    rw [hcS, fpow, ← Real.rpow_neg_one (k : ℝ), ← Real.rpow_add hkpos]
    congr 1; ring
  · have hknp : ¬ Nat.Prime k := hk
    rw [if_neg hk]
    have hcS : cS k = 0 := by rw [cS, mC, if_neg hknp]; ring
    rw [hcS, mul_zero]

/-- **The finite Abel identity** at `b = N` (`N ≥ 2`):
`∑_{k≤N} f(k)·cS k = f(N)·S(N) − ∫_{(2,N]} (1−s)·t^{−s}·S(t) dt`. -/
theorem abel_finite {s : ℝ} (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Icc 0 N, fpow s k * cS k
      = fpow s N * SPartial N - ∫ t in Set.Ioc 2 (N : ℝ), (1 - s) * t ^ (-s) * SPartial t := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hint : IntegrableOn (deriv (fpow s)) (Set.Icc 2 (N : ℝ)) := by
    have hne : ∀ x ∈ Set.Icc (2 : ℝ) (N : ℝ), (x : ℝ) ≠ 0 ∨ (0 : ℝ) ≤ -s :=
      fun x hx => Or.inl (ne_of_gt (by simp only [Set.mem_Icc] at hx; linarith [hx.1]))
    have hcont : ContinuousOn (fun t : ℝ => (1 - s) * t ^ (-s)) (Set.Icc 2 (N : ℝ)) :=
      (continuousOn_id.rpow_const hne).const_mul (1 - s)
    refine (hcont.integrableOn_compact isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht; simp only [Set.mem_Icc] at ht
    exact ((hasDerivAt_fpow (show (0 : ℝ) < t by linarith [ht.1])).deriv).symm
  have hb := sum_mul_eq_sub_integral_mul₁ cS cS_zero cS_one (N : ℝ)
    (fun u hu => (hasDerivAt_fpow (s := s)
      (show (0 : ℝ) < u by simp only [Set.mem_Icc] at hu; linarith [hu.1])).differentiableAt)
    hint
  calc ∑ k ∈ Finset.Icc 0 N, fpow s ↑k * cS k
      = ∑ k ∈ Finset.Icc 0 ⌊(N : ℝ)⌋₊, fpow s ↑k * cS k := by rw [Nat.floor_natCast]
    _ = fpow s ↑N * ∑ k ∈ Finset.Icc 0 ⌊(N : ℝ)⌋₊, cS k
        - ∫ t in Set.Ioc 2 (N : ℝ), deriv (fpow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cS k := hb
    _ = fpow s ↑N * SPartial ↑N
        - ∫ t in Set.Ioc 2 (N : ℝ), (1 - s) * t ^ (-s) * SPartial t := by
        rw [sum_cS_eq_SPartial (N : ℝ)]
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht; simp only [Set.mem_Ioc] at ht
        change deriv (fpow s) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cS k = (1 - s) * t ^ (-s) * SPartial t
        rw [(hasDerivAt_fpow (show (0 : ℝ) < t by linarith [ht.1])).deriv, sum_cS_eq_SPartial]

/-! ## Part C3 — the three limits and the assembled Abel identity -/

/-- **L1.** `∑_{k≤N} f(k)·cS k → P(s)` as `N → ∞` (partial sums of the prime-zeta series). -/
theorem tendsto_abelLHS {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, fpow s k * cS k) atTop (𝓝 (primeZeta s)) := by
  set g : ℕ → ℝ := Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ => (n : ℝ) ^ (-s)) with hg
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    (Real.summable_nat_rpow_inv.mpr hs).congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) s).symm)
  have hgsummable : Summable g :=
    Summable.of_nonneg_of_le
      (fun k => Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) k)
      (fun k => Set.indicator_le_self' (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) k) hbase
  have hgtsum : ∑' k, g k = primeZeta s := by
    rw [hg, ← tsum_subtype {p : ℕ | Nat.Prime p} (fun n : ℕ => (n : ℝ) ^ (-s))]
    rfl
  have hHS : HasSum g (primeZeta s) := hgtsum ▸ hgsummable.hasSum
  have hEq : ∀ N : ℕ, ∑ k ∈ Finset.Icc 0 N, fpow s k * cS k = ∑ k ∈ Finset.range (N + 1), g k := by
    intro N
    rw [show Finset.Icc 0 N = Finset.range (N + 1) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega]
    exact Finset.sum_congr rfl (fun k _ => fpow_cS_eq k)
  simp only [hEq]
  exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- **L2.** `f(N)·S(N) = N^{1−s}·S(N) → 0` as `N → ∞`. -/
theorem tendsto_abelBoundary {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ => fpow s N * SPartial N) atTop (𝓝 0) := by
  set δ := (s - 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set C := |mertensM| + 12 / Real.log 2 with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]; positivity
  have hbnd_tendsto : Tendsto (fun N : ℕ => (1 / δ + C) * (N : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul (1 / δ + C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbnd_tendsto
    (Filter.Eventually.of_forall (fun N => ?_)) ?_
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (SPartial_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- S(N) ≤ log N + C
    have hSbd : SPartial N ≤ Real.log N + C := by
      have hsharp := abs_le.mp (mertens_second_sharp_real hN2)
      have h2 : Real.log (Real.log N) ≤ Real.log N := by
        linarith [Real.log_le_sub_one_of_pos hlogN]
      have h3 : 12 / Real.log N ≤ 12 / Real.log 2 :=
        div_le_div_of_nonneg_left (by norm_num) hlog2 (Real.log_le_log (by norm_num) hN2)
      have hMle : mertensM ≤ |mertensM| := le_abs_self _
      have := hsharp.2
      rw [hCdef]; linarith
    -- log N + C ≤ (1/δ + C)·N^δ
    have hNδ1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ.le
    have hlogNδ : Real.log N ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hNpos.le hδ
    have hstep : Real.log N + C ≤ (1 / δ + C) * (N : ℝ) ^ δ := by
      have hc1 : Real.log N ≤ (1 / δ) * (N : ℝ) ^ δ := by
        rw [one_div, ← div_eq_inv_mul]; exact hlogNδ
      have hc2 : C ≤ C * (N : ℝ) ^ δ := le_mul_of_one_le_right hC hNδ1
      calc Real.log N + C ≤ (1 / δ) * (N : ℝ) ^ δ + C * (N : ℝ) ^ δ := by linarith
        _ = (1 / δ + C) * (N : ℝ) ^ δ := by ring
    -- combine
    have hfpow : fpow s N = (N : ℝ) ^ (1 - s) := rfl
    have hpowmul : (N : ℝ) ^ (1 - s) * (N : ℝ) ^ δ = (N : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hNpos]; congr 1; rw [hδdef]; ring
    have hfpownn : (0 : ℝ) ≤ (N : ℝ) ^ (1 - s) := Real.rpow_nonneg hNpos.le _
    calc fpow s N * SPartial N = (N : ℝ) ^ (1 - s) * SPartial N := by rw [hfpow]
      _ ≤ (N : ℝ) ^ (1 - s) * ((1 / δ + C) * (N : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left (le_trans hSbd hstep) hfpownn
      _ = (1 / δ + C) * ((N : ℝ) ^ (1 - s) * (N : ℝ) ^ δ) := by ring
      _ = (1 / δ + C) * (N : ℝ) ^ (-δ) := by rw [hpowmul]

/-- **L3.** `∫_{(2,N]} (1−s)·t^{−s}·S(t) → ∫_{(2,∞)} (1−s)·t^{−s}·S(t)` as `N → ∞`. -/
theorem tendsto_abelIntegral {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∫ t in Set.Ioc 2 (N : ℝ), (1 - s) * t ^ (-s) * SPartial t) atTop
      (𝓝 (∫ t in Set.Ioi 2, (1 - s) * t ^ (-s) * SPartial t)) := by
  have hintegrable : IntegrableOn (fun t => (1 - s) * t ^ (-s) * SPartial t) (Set.Ioi 2) := by
    have hbase : IntegrableOn (fun t => (1 - s) * (SPartial t * t ^ (-s))) (Set.Ioi 2) :=
      (integrableOn_SPartial_rpow hs).const_mul (1 - s)
    exact hbase.congr_fun (fun t _ => by ring) measurableSet_Ioi
  have hmono : Monotone (fun N : ℕ => Set.Ioc (2 : ℝ) (N : ℝ)) :=
    fun N M hNM => Set.Ioc_subset_Ioc_right (by exact_mod_cast hNM)
  have hunion : (⋃ N : ℕ, Set.Ioc (2 : ℝ) (N : ℝ)) = Set.Ioi 2 := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨N, hN, _⟩; exact hN
    · intro ht; obtain ⟨N, hN⟩ := exists_nat_ge t; exact ⟨N, ht, hN⟩
  have hint_union : IntegrableOn (fun t => (1 - s) * t ^ (-s) * SPartial t)
      (⋃ N : ℕ, Set.Ioc (2 : ℝ) (N : ℝ)) := by rw [hunion]; exact hintegrable
  have hlim := tendsto_setIntegral_of_monotone (fun N => measurableSet_Ioc) hmono hint_union
  rwa [hunion] at hlim

/-- **The Abel identity for the prime zeta function.**  For `s > 1`,
`P(s) = (s − 1)·∫₂^∞ S(t)·t^{−s} dt`. -/
theorem abel_primeZeta {s : ℝ} (hs : 1 < s) :
    primeZeta s = (s - 1) * ∫ t in Set.Ioi 2, SPartial t * t ^ (-s) := by
  have hEqEv : ∀ᶠ N : ℕ in atTop, ∑ k ∈ Finset.Icc 0 N, fpow s k * cS k
      = fpow s N * SPartial N - ∫ t in Set.Ioc 2 (N : ℝ), (1 - s) * t ^ (-s) * SPartial t := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact abel_finite N hN
  have hrhs : Tendsto (fun N : ℕ =>
      fpow s N * SPartial N - ∫ t in Set.Ioc 2 (N : ℝ), (1 - s) * t ^ (-s) * SPartial t)
      atTop (𝓝 (0 - ∫ t in Set.Ioi 2, (1 - s) * t ^ (-s) * SPartial t)) :=
    (tendsto_abelBoundary hs).sub (tendsto_abelIntegral hs)
  have hlhs' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N, fpow s k * cS k) atTop
      (𝓝 (0 - ∫ t in Set.Ioi 2, (1 - s) * t ^ (-s) * SPartial t)) :=
    hrhs.congr' (hEqEv.mono (fun N h => h.symm))
  have heq := tendsto_nhds_unique (tendsto_abelLHS hs) hlhs'
  rw [heq, zero_sub, ← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht; ring

/-! ## Part D — the substitution `S = loglog + M + E` and the identification -/

/-- The sharp-Mertens error `E(t) = S(t) − log log t − M`. -/
noncomputable def Ereal (t : ℝ) : ℝ := SPartial t - Real.log (Real.log t) - mertensM

theorem measurable_Ereal : Measurable Ereal := by
  unfold Ereal
  exact (measurable_SPartial.sub (Real.measurable_log.comp Real.measurable_log)).sub_const mertensM

/-- `|E(t)| ≤ 12/log t` for `t ≥ 2` — the sharp-Mertens error bound. -/
theorem Ereal_abs_le {t : ℝ} (ht : 2 ≤ t) : |Ereal t| ≤ 12 / Real.log t := by
  have h := mertens_second_sharp_real ht
  have he : Ereal t = SPartial t - (Real.log (Real.log t) + mertensM) := by unfold Ereal; ring
  rw [he]; exact h

/-- `E(t)·t^{−s}` is integrable on `(2,∞)` for `s > 1` (bounded error `× t^{−s}`). -/
theorem integrableOn_Ereal_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => Ereal t * t ^ (-s)) (Set.Ioi 2) := by
  refine integrableOn_mul_rpow_of_bound hs measurable_Ereal.aestronglyMeasurable
    (A := 0) (B := 12 / Real.log 2) (fun t ht => ?_)
  simp only [Set.mem_Ioi] at ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : |Ereal t| ≤ 12 / Real.log t := Ereal_abs_le (by linarith)
  have h2 : 12 / Real.log t ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2 (Real.log_le_log (by norm_num) (by linarith))
  simp only [zero_mul, zero_add]
  linarith

/-- `∫₂^∞ t^{−s} = 2^{1−s}/(s−1)` for `s > 1`. -/
theorem integral_rpow_neg_Ioi2 {s : ℝ} (hs : 1 < s) :
    (∫ t in Set.Ioi 2, t ^ (-s)) = (2 : ℝ) ^ (1 - s) / (s - 1) := by
  rw [integral_Ioi_rpow_of_lt (show -s < -1 by linarith) (show (0 : ℝ) < 2 by norm_num),
    show (-s + 1 : ℝ) = 1 - s by ring]
  have hne : (1 : ℝ) - s ≠ 0 := ne_of_lt (by linarith)
  have hne2 : (s : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The integral of `(S − loglog)·t^{−s}` splits as `M·∫t^{−s} + ∫E·t^{−s}`. -/
theorem integral_SPartial_sub_loglog {s : ℝ} (hs : 1 < s) :
    (∫ t in Set.Ioi 2, SPartial t * t ^ (-s))
        - (∫ t in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s))
      = mertensM * (∫ t in Set.Ioi 2, t ^ (-s)) + ∫ t in Set.Ioi 2, Ereal t * t ^ (-s) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) (by norm_num)
  rw [← MeasureTheory.integral_sub (integrableOn_SPartial_rpow hs)
      (integrableOn_loglog_rpow_neg hs),
    ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add (hrpow.const_mul mertensM) (integrableOn_Ereal_rpow hs)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold Ereal
  ring

/-- **The algebraic identity feeding the limit.**  For `s > 1`,
`P(s) − (s−1)·∫₂^∞ loglog·t^{−s} = M·2^{1−s} + (s−1)·∫₂^∞ E·t^{−s}`. -/
theorem hDval {s : ℝ} (hs : 1 < s) :
    primeZeta s - (s - 1) * (∫ t in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s))
      = mertensM * (2 : ℝ) ^ (1 - s) + (s - 1) * ∫ t in Set.Ioi 2, Ereal t * t ^ (-s) := by
  have hne : (s : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [abel_primeZeta hs, ← mul_sub, integral_SPartial_sub_loglog hs, integral_rpow_neg_Ioi2 hs,
    mul_add]
  congr 1
  rw [← mul_assoc]
  field_simp

/-- `(s−1)·∫_{Ioi c} t^{−s} = c^{1−s}` for `c > 0`, `s > 1`. -/
theorem mul_integral_rpow_neg_Ioi {c s : ℝ} (hc : 0 < c) (hs : 1 < s) :
    (s - 1) * (∫ t in Set.Ioi c, t ^ (-s)) = c ^ (1 - s) := by
  rw [integral_Ioi_rpow_of_lt (show -s < -1 by linarith) hc, show (-s + 1 : ℝ) = 1 - s by ring]
  have hne : (1 : ℝ) - s ≠ 0 := ne_of_lt (by linarith)
  field_simp
  ring

/-- **h1.**  `M·2^{1−s} → M` as `s → 1⁺`. -/
theorem tendsto_mertensM_rpow :
    Tendsto (fun s : ℝ => mertensM * (2 : ℝ) ^ (1 - s)) (𝓝[>] 1) (𝓝 mertensM) := by
  have hc : Continuous (fun s : ℝ => (2 : ℝ) ^ (1 - s)) :=
    (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
      (continuous_const.sub continuous_id)
  have hlim : Tendsto (fun s : ℝ => (2 : ℝ) ^ (1 - s)) (𝓝[>] 1) (𝓝 1) := by
    have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
    simpa using h
  simpa using hlim.const_mul mertensM

/-- **h2 (the δ-squeeze).**  `(s−1)·∫₂^∞ E·t^{−s} → 0` as `s → 1⁺`.  Split at `T` with
`12/log T ≤ ε/2`: the tail contributes `≤ (12/log T)·T^{1−s} ≤ ε/2`, and the finite part
`≤ (s−1)·(12/log 2)·(T−2) → 0`. -/
theorem tendsto_ints_Ereal :
    Tendsto (fun s : ℝ => (s - 1) * ∫ t in Set.Ioi 2, Ereal t * t ^ (-s)) (𝓝[>] 1) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- choose T := exp(max (24/ε) (log 2)): T ≥ 2 and 12/log T ≤ ε/2
  set m : ℝ := max (24 / ε) (Real.log 2) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hlog2 (le_max_right _ _)
  set T : ℝ := Real.exp m with hT
  have hTpos : 0 < T := Real.exp_pos m
  have hT2 : (2 : ℝ) ≤ T := by
    rw [hT, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  have hlogT : Real.log T = m := by rw [hT, Real.log_exp]
  have hlogTpos : 0 < Real.log T := by rw [hlogT]; exact hmpos
  have h24em : (24 : ℝ) ≤ ε * m := by
    rw [mul_comm]; exact (div_le_iff₀ hε).mp (le_max_left (24 / ε) (Real.log 2))
  have h12logT : 12 / Real.log T ≤ ε / 2 := by
    rw [hlogT, div_le_iff₀ hmpos]
    have hrw : ε / 2 * m = ε * m / 2 := by ring
    rw [hrw]; linarith
  -- the finite-part constant
  set K : ℝ := (12 / Real.log 2) * (T - 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    have hT2' : (0 : ℝ) ≤ T - 2 := by linarith
    positivity
  refine ⟨ε / (2 * (K + 1)), by positivity, fun x hxmem hxdist => ?_⟩
  have hx1 : 1 < x := hxmem
  have hxsub : 0 < x - 1 := by linarith
  have hxne : x - 1 ≠ 0 := ne_of_gt hxsub
  have hxdist' : x - 1 < ε / (2 * (K + 1)) := by
    rwa [Real.dist_eq, abs_of_pos hxsub] at hxdist
  -- integrability pieces
  have hErx : IntegrableOn (fun t => Ereal t * t ^ (-x)) (Set.Ioi 2) := integrableOn_Ereal_rpow hx1
  have hErx_Ioc : IntegrableOn (fun t => Ereal t * t ^ (-x)) (Set.Ioc 2 T) :=
    hErx.mono_set Set.Ioc_subset_Ioi_self
  have hErx_Ioi : IntegrableOn (fun t => Ereal t * t ^ (-x)) (Set.Ioi T) :=
    hErx.mono_set (Set.Ioi_subset_Ioi hT2)
  have hrpowT : IntegrableOn (fun t : ℝ => t ^ (-x)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (show -x < -1 by linarith) hTpos
  -- split the integral
  have hsplit : (∫ t in Set.Ioi 2, Ereal t * t ^ (-x))
      = (∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x)) + ∫ t in Set.Ioi T, Ereal t * t ^ (-x) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT2]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hErx_Ioc hErx_Ioi
  -- finite bound: |∫_{Ioc 2 T}| ≤ K
  have hfin : |∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x)| ≤ K := by
    have hbound : ∀ t ∈ Set.Ioc (2 : ℝ) T, ‖Ereal t * t ^ (-x)‖ ≤ 12 / Real.log 2 := by
      intro t ht
      simp only [Set.mem_Ioc] at ht
      have htpos : (0 : ℝ) < t := by linarith [ht.1]
      have hlogt : Real.log 2 < Real.log t := Real.log_lt_log (by norm_num) ht.1
      have hpow1 : t ^ (-x) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)
      have hpownn : (0 : ℝ) ≤ t ^ (-x) := Real.rpow_nonneg htpos.le _
      have hE : |Ereal t| ≤ 12 / Real.log t := Ereal_abs_le (by linarith [ht.1])
      have hE2 : 12 / Real.log t ≤ 12 / Real.log 2 :=
        div_le_div_of_nonneg_left (by norm_num) hlog2 hlogt.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownn]
      calc |Ereal t| * t ^ (-x) ≤ (12 / Real.log 2) * 1 :=
            mul_le_mul (le_trans hE hE2) hpow1 hpownn (by positivity)
        _ = 12 / Real.log 2 := by ring
    have hvol : volume (Set.Ioc (2 : ℝ) T) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have hvolreal : volume.real (Set.Ioc (2 : ℝ) T) = T - 2 := by
      rw [Real.volume_real_Ioc, max_eq_left (by linarith)]
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x)‖
        ≤ (12 / Real.log 2) * (volume.real (Set.Ioc (2 : ℝ) T)) :=
          norm_setIntegral_le_of_norm_le_const hvol hbound
      _ = K := by rw [hvolreal, hK]
  -- tail bound: (x-1)·|∫_{Ioi T}| ≤ (12/log T)·T^{1-x}
  have htail : (x - 1) * |∫ t in Set.Ioi T, Ereal t * t ^ (-x)|
      ≤ (12 / Real.log T) * T ^ (1 - x) := by
    have hb : |∫ t in Set.Ioi T, Ereal t * t ^ (-x)|
        ≤ (12 / Real.log T) * ∫ t in Set.Ioi T, t ^ (-x) := by
      have hmono : (∫ t in Set.Ioi T, |Ereal t * t ^ (-x)|)
          ≤ ∫ t in Set.Ioi T, (12 / Real.log T) * t ^ (-x) := by
        refine setIntegral_mono_on hErx_Ioi.norm (hrpowT.const_mul _) measurableSet_Ioi
          (fun t ht => ?_)
        simp only [Set.mem_Ioi] at ht
        have htpos : (0 : ℝ) < t := by linarith
        have hlogtT : Real.log T ≤ Real.log t := Real.log_le_log hTpos ht.le
        have hpownn : (0 : ℝ) ≤ t ^ (-x) := Real.rpow_nonneg htpos.le _
        have hE : |Ereal t| ≤ 12 / Real.log t := Ereal_abs_le (by linarith)
        have hE2 : 12 / Real.log t ≤ 12 / Real.log T :=
          div_le_div_of_nonneg_left (by norm_num) hlogTpos hlogtT
        rw [abs_mul, abs_of_nonneg hpownn]
        exact mul_le_mul_of_nonneg_right (le_trans hE hE2) hpownn
      calc |∫ t in Set.Ioi T, Ereal t * t ^ (-x)|
          = ‖∫ t in Set.Ioi T, Ereal t * t ^ (-x)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Set.Ioi T, ‖Ereal t * t ^ (-x)‖ := norm_integral_le_integral_norm _
        _ = ∫ t in Set.Ioi T, |Ereal t * t ^ (-x)| := by simp only [Real.norm_eq_abs]
        _ ≤ ∫ t in Set.Ioi T, (12 / Real.log T) * t ^ (-x) := hmono
        _ = (12 / Real.log T) * ∫ t in Set.Ioi T, t ^ (-x) := MeasureTheory.integral_const_mul _ _
    calc (x - 1) * |∫ t in Set.Ioi T, Ereal t * t ^ (-x)|
        ≤ (x - 1) * ((12 / Real.log T) * ∫ t in Set.Ioi T, t ^ (-x)) :=
          mul_le_mul_of_nonneg_left hb hxsub.le
      _ = (12 / Real.log T) * ((x - 1) * ∫ t in Set.Ioi T, t ^ (-x)) := by ring
      _ = (12 / Real.log T) * T ^ (1 - x) := by rw [mul_integral_rpow_neg_Ioi hTpos hx1]
  -- combine
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hxsub, hsplit]
  have hfin_lt : (x - 1) * K < ε / 2 := by
    have h1 : (x - 1) * (K + 1) < ε / 2 := by
      calc (x - 1) * (K + 1) < (ε / (2 * (K + 1))) * (K + 1) :=
            mul_lt_mul_of_pos_right hxdist' (by positivity)
        _ = ε / 2 := by field_simp
    nlinarith [hxsub, hKnn]
  have htail_lt : (12 / Real.log T) * T ^ (1 - x) ≤ ε / 2 := by
    have hT1x : T ^ (1 - x) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc (12 / Real.log T) * T ^ (1 - x) ≤ (12 / Real.log T) * 1 :=
          mul_le_mul_of_nonneg_left hT1x (by positivity)
      _ = 12 / Real.log T := by ring
      _ ≤ ε / 2 := h12logT
  calc (x - 1) * |(∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x))
          + ∫ t in Set.Ioi T, Ereal t * t ^ (-x)|
      ≤ (x - 1) * (|∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x)|
          + |∫ t in Set.Ioi T, Ereal t * t ^ (-x)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hxsub.le
    _ = (x - 1) * |∫ t in Set.Ioc 2 T, Ereal t * t ^ (-x)|
          + (x - 1) * |∫ t in Set.Ioi T, Ereal t * t ^ (-x)| := by ring
    _ ≤ (x - 1) * K + (12 / Real.log T) * T ^ (1 - x) :=
        add_le_add (mul_le_mul_of_nonneg_left hfin hxsub.le) htail
    _ < ε := by linarith

/-! ## Part E — the identification `M = γ − B` (MERT-3c) -/

/-- **MERT-3c, the identification.**  The Meissel–Mertens constant equals `γ − B`:
`mertensM = eulerMascheroniConstant − mertensB`.  Proved by uniqueness of the limit of
`D(s) = P(s) − (s−1)·∫₂^∞ loglog·t^{−s}`, which tends to `M` (Abelian comparison) and to
`γ − B` (the two landed asymptotics). -/
theorem mertensM_eq_sub :
    mertensM = Real.eulerMascheroniConstant - mertensB := by
  -- D(s) → M  (Abelian comparison, via `hDval` + `h1` + `h2`)
  have hD2 : Tendsto (fun s : ℝ => primeZeta s
      - (s - 1) * ∫ t in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s)) (𝓝[>] 1) (𝓝 mertensM) := by
    have hRHS : Tendsto (fun s : ℝ => mertensM * (2 : ℝ) ^ (1 - s)
        + (s - 1) * ∫ t in Set.Ioi 2, Ereal t * t ^ (-s)) (𝓝[>] 1) (𝓝 mertensM) := by
      have h := tendsto_mertensM_rpow.add tendsto_ints_Ereal
      rwa [add_zero] at h
    refine hRHS.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hDval (Set.mem_Ioi.mp hs)).symm
  -- D(s) → γ − B  (the two landed limits)
  have hD1 : Tendsto (fun s : ℝ => primeZeta s
      - (s - 1) * ∫ t in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s)) (𝓝[>] 1)
      (𝓝 (Real.eulerMascheroniConstant - mertensB)) := by
    have h := primeZeta_tendsto.sub loglog_integral_asymp
    rw [show -mertensB - -Real.eulerMascheroniConstant
      = Real.eulerMascheroniConstant - mertensB by ring] at h
    refine h.congr' ?_
    filter_upwards with s
    ring
  exact tendsto_nhds_unique hD2 hD1

/-- **The sharp Mertens second theorem, with the explicit constant.**  The Meissel–Mertens
constant is `γ − B`: `|∑_{p≤n} 1/p − (log log n + (γ − B))| ≤ 12 / log n` for `n ≥ 2`. -/
theorem mertens_second_sharp' :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
          - (Real.log (Real.log n) + (Real.eulerMascheroniConstant - mertensB))|
        ≤ C / Real.log n := by
  refine ⟨12, by norm_num, fun n hn => ?_⟩
  have hx : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkey := mertens_second_sharp_real hx
  rw [← mertensM_eq_sub]
  rwa [show SPartial (n : ℝ)
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p from by
    rw [SPartial, Nat.floor_natCast]] at hkey

/-! ## Part F — Mertens' third theorem (MERT-4) -/

/-- **Mertens' third theorem (log form).**  For `n ≥ 3`,
`|log ∏_{p≤n} (1 − 1/p) + log log n + γ| ≤ 14 / log n`. -/
theorem mertens_third_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      |Real.log (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))
          + Real.log (Real.log n) + Real.eulerMascheroniConstant|
        ≤ C / Real.log n := by
  refine ⟨14, by norm_num, fun n hn => ?_⟩
  have hn1 : 1 < n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hgamma : Real.eulerMascheroniConstant = mertensM + mertensB := by
    have := mertensM_eq_sub; linarith
  set S := (Finset.range (n + 1)).filter Nat.Prime with hSdef
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hnlp := neg_log_prod_eq S hSprime
  have hSsum : (∑ p ∈ S, (1 : ℝ) / p) = SPartial (n : ℝ) := by
    rw [SPartial, Nat.floor_natCast, hSdef]
  have hBpart : (∑ p ∈ S, ppInner p) = mertensB_partial (n + 1) := by
    rw [mertensB_partial, hSdef]; rfl
  have hlogprod : Real.log (∏ p ∈ S, (1 - 1 / (p : ℝ)))
      = -(SPartial (n : ℝ)) - mertensB_partial (n + 1) := by
    rw [hSsum, hBpart] at hnlp; linarith [hnlp]
  have hb1 : |SPartial (n : ℝ) - (Real.log (Real.log n) + mertensM)| ≤ 12 / Real.log n :=
    mertens_second_sharp_real hnR
  have hb2 : |mertensB - mertensB_partial (n + 1)| ≤ 2 / (n : ℝ) := by
    have h := mertensB_tail_le (n + 1) (by omega)
    rwa [show ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) from by push_cast; ring] at h
  have h2n : 2 / (n : ℝ) ≤ 2 / Real.log n := by
    apply div_le_div_of_nonneg_left (by norm_num) hlogn
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith)]
  rw [hlogprod, hgamma]
  have hrw : -(SPartial (n : ℝ)) - mertensB_partial (n + 1)
        + Real.log (Real.log n) + (mertensM + mertensB)
      = -(SPartial (n : ℝ) - (Real.log (Real.log n) + mertensM))
        + (mertensB - mertensB_partial (n + 1)) := by ring
  rw [hrw]
  calc |-(SPartial (n : ℝ) - (Real.log (Real.log n) + mertensM))
          + (mertensB - mertensB_partial (n + 1))|
      ≤ |-(SPartial (n : ℝ) - (Real.log (Real.log n) + mertensM))|
          + |mertensB - mertensB_partial (n + 1)| := abs_add_le _ _
    _ = |SPartial (n : ℝ) - (Real.log (Real.log n) + mertensM)|
          + |mertensB - mertensB_partial (n + 1)| := by rw [abs_neg]
    _ ≤ 12 / Real.log n + 2 / (n : ℝ) := add_le_add hb1 hb2
    _ ≤ 12 / Real.log n + 2 / Real.log n := by linarith [h2n]
    _ = 14 / Real.log n := by ring

/-- **Mertens' third theorem (product form).**  For `n ≥ 3`,
`|∏_{p≤n} (1 − 1/p) · log n − e^{−γ}| ≤ C / log n`. -/
theorem mertens_third :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      |(∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log n
          - Real.exp (-Real.eulerMascheroniConstant)| ≤ C / Real.log n := by
  obtain ⟨C₀, hC₀, hlog⟩ := mertens_third_log
  set g := Real.eulerMascheroniConstant with hgdef
  refine ⟨Real.exp (-g) * Real.exp (C₀ / Real.log 3) * C₀,
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hC₀, fun n hn => ?_⟩
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog3n : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogbnd := hlog n hn
  set P := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) with hPdef
  -- P > 0
  have hP : 0 < P := by
    rw [hPdef]
    refine Finset.prod_pos (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hp2
    linarith
  have hw : 0 < P * Real.log n := mul_pos hP hlogn
  -- |log(P·log n) + γ| ≤ C₀/log n
  have hbnd : |Real.log (P * Real.log n) + g| ≤ C₀ / Real.log n := by
    rw [Real.log_mul (ne_of_gt hP) (ne_of_gt hlogn)]; exact hlogbnd
  set a := C₀ / Real.log n with hadef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have habs := abs_le.mp hbnd
  -- exp bounds for w := P·log n
  have hwexp : P * Real.log n = Real.exp (Real.log (P * Real.log n)) := (Real.exp_log hw).symm
  have hupper : P * Real.log n ≤ Real.exp (-g) * Real.exp a := by
    rw [hwexp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [habs.2])
  have hlower : Real.exp (-g) * Real.exp (-a) ≤ P * Real.log n := by
    rw [hwexp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [habs.1])
  -- |P·log n - e^{-γ}| ≤ e^{-γ}·(e^a - 1)
  have hexpge : Real.exp (-g) * (Real.exp (-a)) ≤ Real.exp (-g) * Real.exp a :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
  have hsym : 1 - Real.exp (-a) ≤ Real.exp a - 1 := by
    nlinarith [Real.add_one_le_exp a, Real.add_one_le_exp (-a), Real.exp_pos a]
  have habsw : |P * Real.log n - Real.exp (-g)| ≤ Real.exp (-g) * (Real.exp a - 1) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [hlower, (Real.exp_pos (-g)), hsym]
    · nlinarith [hupper, (Real.exp_pos (-g))]
  -- e^a - 1 ≤ a·e^{C₀/log 3}
  have hprod : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hexpm1 : Real.exp a - 1 ≤ a * Real.exp (C₀ / Real.log 3) := by
    have hstep1 : Real.exp a - 1 ≤ a * Real.exp a := by
      nlinarith [mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-a)) (Real.exp_pos a).le, hprod]
    have hstep2 : Real.exp a ≤ Real.exp (C₀ / Real.log 3) := by
      apply Real.exp_le_exp.mpr
      rw [hadef]
      exact div_le_div_of_nonneg_left hC₀ hlog3 hlog3n
    calc Real.exp a - 1 ≤ a * Real.exp a := hstep1
      _ ≤ a * Real.exp (C₀ / Real.log 3) := mul_le_mul_of_nonneg_left hstep2 ha0
  -- assemble
  calc |P * Real.log n - Real.exp (-g)|
      ≤ Real.exp (-g) * (Real.exp a - 1) := habsw
    _ ≤ Real.exp (-g) * (a * Real.exp (C₀ / Real.log 3)) :=
        mul_le_mul_of_nonneg_left hexpm1 (Real.exp_pos _).le
    _ = (Real.exp (-g) * Real.exp (C₀ / Real.log 3) * C₀) / Real.log n := by
        rw [hadef]; field_simp

end Salt.Mertens
