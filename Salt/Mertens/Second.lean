/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Mertens
import Salt.BrunLower.MertensWindow

/-!
# The sharp Mertens second theorem

`∃ M C, 0 ≤ C ∧ ∀ n ≥ 2, |Σ_{p≤n} 1/p − (log log n + M)| ≤ C / log n`.

Route (classical Abel summation against the two-sided Mertens-1 window):
The corpus provides the Abel identity `Σ_{p≤x} 1/p = mF x · Sfun x − ∫₂ˣ mF'·Sfun`
(`sum_mul_eq_sub_integral_mul₁`) and the load-bearing two-sided estimate
`|Sfun t − log t| ≤ 6` (`abs_Sfun_sub_log_le`).  Writing `Sfun = log + E`
(`|E| ≤ 6`), the `log`-part yields `1 + log log x − log log 2`, and the
`E`-part is the improper integral `∫₂^∞ E(t)/(t log²t) dt`, which converges
absolutely (`|E| ≤ 6`, `∫ (t log²t)⁻¹ < ∞`).  The Meissel–Mertens constant is
`M := 1 − log log 2 + ∫₂^∞ E/(t log²t)`; the error is
`E(x)/log x − ∫ₓ^∞ E/(t log²t)`, each piece `≤ 6/log x`, so `C = 12`.
-/

open Finset MeasureTheory Set Filter Topology intervalIntegral

namespace Salt.Mertens

open Salt.Maynard Salt.BrunLower

/-- The `E`-part integrand `E(t)/(t log²t)` where `E(t) = Sfun t − log t`. -/
noncomputable def hInt (t : ℝ) : ℝ := (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹

/-! ## Tail integrals of the dominating function `(t log²t)⁻¹` on `Ioi a` -/

/-- `t ↦ -(log t)⁻¹` is an antiderivative of `(t log²t)⁻¹` for `t ≥ 2`. -/
theorem hasDerivAt_negInvLog {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
  have h := (hasDerivAt_mF hx).neg
  rw [neg_neg] at h
  exact h

/-- `-(log t)⁻¹ → 0` at `atTop`. -/
theorem tendsto_negInvLog : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  simpa using h1.neg

/-- The dominating function `(t log²t)⁻¹` is integrable on `(a, ∞)` for `a ≥ 2`. -/
theorem integrableOn_invtlogsq_Ioi {a : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun t => (t * Real.log t ^ 2)⁻¹) (Set.Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_negInvLog (le_trans ha (Set.mem_Ici.mp hx))) (fun x hx => ?_)
    tendsto_negInvLog
  have hx2 : (0:ℝ) < x := by have := Set.mem_Ioi.mp hx; linarith
  positivity

/-- `∫ₐ^∞ (t log²t)⁻¹ = 1/log a` for `a ≥ 2`. -/
theorem integral_invtlogsq_Ioi {a : ℝ} (ha : 2 ≤ a) :
    ∫ t in Set.Ioi a, (t * Real.log t ^ 2)⁻¹ = (Real.log a)⁻¹ := by
  have hkey := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_negInvLog (le_trans ha (Set.mem_Ici.mp hx)))
    (fun x hx => by
      have hx2 : (0:ℝ) < x := by have := Set.mem_Ioi.mp hx; linarith
      positivity)
    tendsto_negInvLog
  simpa using hkey

/-! ## Integrability of the `E`-part integrand `hInt` -/

/-- `hInt` is integrable on the compact `[2, x]`.  It equals the corpus-integrable
`−(mF'·Sfun) − (t log t)⁻¹`, whose pieces are individually integrable. -/
theorem integrableOn_hInt_Icc {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn hInt (Set.Icc 2 x) := by
  have h1 : IntegrableOn (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      (Set.Icc 2 x) :=
    integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF_real hx)
  have h2 : IntegrableOn (fun t => (t * Real.log t)⁻¹) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.Icc 2 x) := by
      have := continuousOn_inv_tlog_real (a := 2) (b := x) le_rfl hx
      rwa [Set.uIcc_of_le hx] at this
    exact hc.integrableOn_compact isCompact_Icc
  have hsub : IntegrableOn (fun t => -(deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      - (t * Real.log t)⁻¹) (Set.Icc 2 x) := h1.neg.sub h2
  refine hsub.congr_fun (fun t ht => ?_) measurableSet_Icc
  simp only [Set.mem_Icc] at ht
  have ht2 : (2:ℝ) ≤ t := ht.1
  have ht0 : (0:ℝ) < t := by linarith
  have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  change -(deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k) - (t * Real.log t)⁻¹
      = (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹
  rw [deriv_mF ht2, show Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k from rfl]
  field_simp

/-- `hInt` is interval-integrable on `[2, x]`. -/
theorem intervalIntegrable_hInt {x : ℝ} (hx : 2 ≤ x) : IntervalIntegrable hInt volume 2 x :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (integrableOn_hInt_Icc hx)

/-- The dominating pointwise bound: `|hInt t| ≤ 6 (t log²t)⁻¹` for `t ≥ 2`. -/
theorem norm_hInt_le {t : ℝ} (ht : 2 ≤ t) : ‖hInt t‖ ≤ 6 * (t * Real.log t ^ 2)⁻¹ := by
  have hinvnn : (0:ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by
    have ht0 : (0:ℝ) < t := by linarith
    positivity
  have hE : |Sfun t - Real.log t| ≤ 6 := abs_Sfun_sub_log_le ht
  rw [hInt, Real.norm_eq_abs, abs_mul, abs_of_nonneg hinvnn]
  exact mul_le_mul_of_nonneg_right hE hinvnn

/-- The `[2,x]` norm-integral of `hInt` is bounded by `6/log 2`, uniformly in `x`. -/
theorem integral_norm_hInt_le {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, ‖hInt t‖ ≤ 6 * (Real.log 2)⁻¹ := by
  have hstep : ∫ t in (2:ℝ)..x, ‖hInt t‖
      ≤ ∫ t in (2:ℝ)..x, 6 * (t * Real.log t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hx
    · exact (intervalIntegrable_hInt hx).norm
    · exact ((continuousOn_inv_tlogsq_real le_rfl hx).intervalIntegrable).const_mul 6
    · intro t ht
      simp only [Set.mem_Icc] at ht
      exact norm_hInt_le ht.1
  have heval : ∫ t in (2:ℝ)..x, 6 * (t * Real.log t ^ 2)⁻¹
      = 6 * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_tlogsq_real le_rfl hx]
  rw [heval] at hstep
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have : (0:ℝ) ≤ (Real.log x)⁻¹ := by positivity
  nlinarith [hstep]

/-- **`hInt` is integrable on `(2, ∞)`.**  The improper integral defining the
Mertens constant converges absolutely. -/
theorem integrableOn_hInt_Ioi : IntegrableOn hInt (Set.Ioi 2) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (6 * (Real.log 2)⁻¹) 2
    (b := fun n : ℕ => (n:ℝ) + 2)
    (fun n => (intervalIntegrable_hInt (le_add_of_nonneg_left (Nat.cast_nonneg n))).1)
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    (Filter.Eventually.of_forall
      (fun n => integral_norm_hInt_le (le_add_of_nonneg_left (Nat.cast_nonneg n))))

/-! ## The Abel identity, tail split, and assembly -/

/-- **The Abel identity for `Σ_{p≤x} 1/p`, decomposed.**  For `x ≥ 2`,
`Σ_{p≤x} 1/p = 1 + E(x)/log x + (log log x − log log 2) + ∫₂ˣ E/(t log²t)`,
where `E = Sfun − log`.  This is Abel summation with the `log`-part integrated
explicitly and the `E`-part left as `∫ hInt`. -/
theorem sum_inv_eq {x : ℝ} (hx : 2 ≤ x) :
    ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mF k * mC k
      = 1 + (Sfun x - Real.log x) * (Real.log x)⁻¹
        + (Real.log (Real.log x) - Real.log (Real.log 2)) + ∫ t in (2:ℝ)..x, hInt t := by
  have hlogxne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have habel := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one x
    (fun t ht => differentiableAt_mF (by simp only [Set.mem_Icc] at ht; exact ht.1))
    (integrableOn_deriv_mF_real hx)
  rw [← intervalIntegral.integral_of_le hx] at habel
  -- boundary term
  have hbdry : mF x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mC k)
      = 1 + (Sfun x - Real.log x) * (Real.log x)⁻¹ := by
    rw [show (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mC k) = Sfun x from rfl, mF]
    field_simp
    ring
  -- integral term
  have hIInf : IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) volume 2 x :=
    ((continuousOn_inv_tlog_real le_rfl hx).intervalIntegrable).neg
  have hintterm : (∫ t in (2:ℝ)..x, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = -(Real.log (Real.log x) - Real.log (Real.log 2)) - ∫ t in (2:ℝ)..x, hInt t := by
    have hcongr : (∫ t in (2:ℝ)..x, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
        = ∫ t in (2:ℝ)..x, (-(t * Real.log t)⁻¹ - hInt t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have ht2 : (2:ℝ) ≤ t := ht.1
      have ht0 : (0:ℝ) < t := by linarith
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      change deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k
          = -(t * Real.log t)⁻¹ - (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹
      rw [deriv_mF ht2, show Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k from rfl]
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_sub hIInf (intervalIntegrable_hInt hx),
      intervalIntegral.integral_neg, integral_inv_tlog_real le_rfl hx]
  rw [hbdry, hintterm] at habel
  rw [habel]; ring

/-- The interval integral `∫₂ˣ hInt` equals the improper tail split
`(∫_{Ioi 2} hInt) − (∫_{Ioi x} hInt)` for `x ≥ 2`. -/
theorem interval_eq_Ioi_sub {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, hInt t
      = (∫ t in Set.Ioi (2:ℝ), hInt t) - ∫ t in Set.Ioi x, hInt t := by
  have hI2 : IntegrableOn hInt (Set.Ioi 2) := integrableOn_hInt_Ioi
  have hIoc : IntegrableOn hInt (Set.Ioc 2 x) := hI2.mono_set Set.Ioc_subset_Ioi_self
  have hIoix : IntegrableOn hInt (Set.Ioi x) := hI2.mono_set (Set.Ioi_subset_Ioi hx)
  have hunion : ∫ t in Set.Ioi (2:ℝ), hInt t
      = (∫ t in Set.Ioc 2 x, hInt t) + ∫ t in Set.Ioi x, hInt t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoix
  rw [intervalIntegral.integral_of_le hx, hunion]; ring

/-- **Tail bound.** `|∫_{Ioi x} hInt| ≤ 6/log x` for `x ≥ 2` — the improper
integral's tail, dominated by `6·∫ₓ^∞ (t log²t)⁻¹ = 6/log x`. -/
theorem abs_tail_le {x : ℝ} (hx : 2 ≤ x) :
    |∫ t in Set.Ioi x, hInt t| ≤ 6 * (Real.log x)⁻¹ := by
  have hIoix : IntegrableOn hInt (Set.Ioi x) :=
    integrableOn_hInt_Ioi.mono_set (Set.Ioi_subset_Ioi hx)
  have hdomint : IntegrableOn (fun t => 6 * (t * Real.log t ^ 2)⁻¹) (Set.Ioi x) :=
    (integrableOn_invtlogsq_Ioi hx).const_mul 6
  calc |∫ t in Set.Ioi x, hInt t|
      = ‖∫ t in Set.Ioi x, hInt t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Set.Ioi x, ‖hInt t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi x, 6 * (t * Real.log t ^ 2)⁻¹ := by
        refine setIntegral_mono_on hIoix.norm hdomint measurableSet_Ioi (fun t ht => ?_)
        exact norm_hInt_le (le_of_lt (lt_of_le_of_lt hx (Set.mem_Ioi.mp ht)))
    _ = 6 * ∫ t in Set.Ioi x, (t * Real.log t ^ 2)⁻¹ := integral_const_mul _ _
    _ = 6 * (Real.log x)⁻¹ := by rw [integral_invtlogsq_Ioi hx]

/-- **The sharp Mertens second theorem.**  There is a constant `M` (the
Meissel–Mertens constant, identified as `γ − B` only downstream) with
`|Σ_{p≤n} 1/p − (log log n + M)| ≤ 12 / log n` for all `n ≥ 2`. -/
theorem mertens_second_sharp :
    ∃ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p)
        - (Real.log (Real.log n) + M)| ≤ C / Real.log n := by
  refine ⟨1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2:ℝ), hInt t, 12, by norm_num, ?_⟩
  intro n hn
  have hx : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlogx : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hinvnn : (0:ℝ) ≤ (Real.log (n:ℝ))⁻¹ := le_of_lt (by positivity)
  -- rewrite the prime sum as the Abel value, then decompose it
  have hLHS : (∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p)
      = ∑ k ∈ Finset.Icc 0 ⌊(n:ℝ)⌋₊, mF k * mC k := by
    rw [sum_mF_mul_mC_eq (n:ℝ), Nat.floor_natCast]
  rw [hLHS, sum_inv_eq hx]
  -- collapse the difference to `E(n)/log n − ∫_{Ioi n} hInt`
  have hdiff : 1 + (Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
        + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log 2))
        + (∫ t in (2:ℝ)..(n:ℝ), hInt t)
        - (Real.log (Real.log (n:ℝ))
            + (1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2:ℝ), hInt t))
      = (Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
          - ∫ t in Set.Ioi (n:ℝ), hInt t := by
    rw [interval_eq_Ioi_sub hx]; ring
  rw [hdiff]
  -- triangle inequality + the two `≤ 6/log n` bounds
  have hb1 : |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹|
      ≤ 6 * (Real.log (n:ℝ))⁻¹ := by
    rw [abs_mul, abs_of_nonneg hinvnn]
    exact mul_le_mul_of_nonneg_right (abs_Sfun_sub_log_le hx) hinvnn
  have hb2 : |∫ t in Set.Ioi (n:ℝ), hInt t| ≤ 6 * (Real.log (n:ℝ))⁻¹ := abs_tail_le hx
  calc |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
          - ∫ t in Set.Ioi (n:ℝ), hInt t|
      ≤ |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹|
          + |∫ t in Set.Ioi (n:ℝ), hInt t| := by
        rw [sub_eq_add_neg, ← abs_neg (∫ t in Set.Ioi (n:ℝ), hInt t)]
        exact abs_add_le _ _
    _ ≤ 6 * (Real.log (n:ℝ))⁻¹ + 6 * (Real.log (n:ℝ))⁻¹ := by linarith [hb1, hb2]
    _ = 12 / Real.log (n:ℝ) := by rw [div_eq_mul_inv]; ring

end Salt.Mertens
