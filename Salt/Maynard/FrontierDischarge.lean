/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Final

/-!
# M7 discharge — the analytic frontier, toward the capstone `EH (1/2) → bounded gaps`

This file discharges the `AnalyticFrontier` hypothesis of `bounded_gaps_from_eh`, toward
`bounded_gaps_from_eh_final` (`FrontierFinal.lean`, which keeps `hCompat`; `Complete` drops it).

The work is entirely quantifier-reordering plumbing plus regime-threshold real
analysis (no new mathematics).  The heart is making the three error constants
(`Cs` of `S1_upper_A1`, `C₀` of `S2m_ge_compatMain_eh`, and the compat constant
of `s2CompatFormM_ge_sixteenth`) *uniform in `R`*: their values factor through
`rankin_bound`/`phi_ratio_le`/`eh_error_pow`, all of which are `R`-free, so we
restate each producer with its constant quantified *before* `R`.  Three of those restatements
now sit beside their producers, each producer being its instance: `lam_abs_le_sharp_uniform`
(`LamBoundSharp`), `abs_S2m_sub_compatMain_le_disc_R_uniform` and `S2m_ge_compatMain_eh_uniform`
(`S2CompatEHFinal`).  The `S₁` restatements remain here.
-/

open Finset

namespace Salt.Maynard

set_option linter.unusedSectionVars false
variable [TupleChoice]

/-! ## R-uniform trivial `S₁` error and the assembled `S₁` upper bound -/

omit [TupleChoice] in
/-- **R-uniform `S1_trivial_error_le'`.**  The trivial error's constant `Cl²`
(from the uniform `λ`-bound) is `R`-free. -/
theorem S1_trivial_error_le'_uniform (k W' : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ), 2 ≤ R → ∀ (y : (Fin k → ℕ) → ℝ), (∀ r, |y r| ≤ 1) →
      (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
        ≤ C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  obtain ⟨Cl, hCl1, hCl⟩ := lam_abs_le_sharp_uniform k W'
  have hCl0 : (0 : ℝ) ≤ Cl := le_trans zero_le_one hCl1
  refine ⟨Cl ^ 2, by positivity, ?_⟩
  intro R hR y hy1
  have hlog0 : (0 : ℝ) ≤ 1 + Real.log R := by
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
    have := Real.log_pos hR1; linarith
  have hsum : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ (kSieveIndex k R W').card • (Cl * (1 + Real.log R) ^ (k + 1)) :=
    Finset.sum_le_card_nsmul _ _ _ (fun d hd => hCl R hR y hy1 d hd)
  rw [nsmul_eq_mul] at hsum
  have hcard := kSieveIndex_card_le k R W' hR
  have hsum0 : (0 : ℝ) ≤ ∑ d ∈ kSieveIndex k R W', |lam k R W' y d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hchain : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by
    have hexp : k + (k + 1) = 2 * k + 1 := by ring
    calc ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
        ≤ ((kSieveIndex k R W').card : ℝ) * (Cl * (1 + Real.log R) ^ (k + 1)) := hsum
      _ ≤ ((R : ℝ) * (1 + Real.log R) ^ k) * (Cl * (1 + Real.log R) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCl0 (pow_nonneg hlog0 _))
      _ = Cl * (R : ℝ) * ((1 + Real.log R) ^ k * (1 + Real.log R) ^ (k + 1)) := by ring
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (k + (k + 1)) := by rw [← pow_add]
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by rw [hexp]
  have hee : (2 * k + 1) * 2 = 4 * k + 2 := by ring
  calc (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
      ≤ (Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1)) ^ 2 :=
        pow_le_pow_left₀ hsum0 hchain 2
    _ = Cl ^ 2 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
        rw [mul_pow, mul_pow, ← pow_mul, hee]

/-- **R-uniform `S1_upper_A1`.**  A single constant `Cs = 2^{k+1}·Cl²` serves
every `R ≥ 2`: `S₁ ≤ 2((K₀−1)N/W)·A₁^k + Cs·R²·(1+log R)^{4k+2}`. -/
theorem S1_upper_A1_uniform (k K₀ N ν₀ : ℕ) (T : ℝ)
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ), 2 ≤ R →
      S1 k K₀ N R (W k) ν₀ (yTensor k R T)
        ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
          + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  obtain ⟨C0, hC0, hC0le⟩ := S1_trivial_error_le'_uniform k (W k)
  refine ⟨2 ^ (k + 1) * C0, by positivity, ?_⟩
  intro R hR
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  -- solvability of compat pairs (as in `S1_upper_tensor`)
  have hsol : ∀ d ∈ kSieveIndex k R (W k), ∀ e ∈ kSieveIndex k R (W k),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i) := by
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvable k d e ν₀ hWpos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => compat_lcm_coprime k R hd he hcompat hij)
  -- `fTilde` divisor-antitone (as in `S1_upper_tensor`)
  have hfmono : ∀ d n : ℕ, d ∣ n → 0 < d → fTilde k R T n ≤ fTilde k R T d := by
    intro d n hdn hd0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : (0 : ℕ) ∉ sqfCop (R0 k R T) (W k) := by
        rw [sqfCop, Finset.mem_filter]
        rintro ⟨-, hsq, -⟩
        exact hsq.ne_zero rfl
      rw [show fTilde k R T 0 = 0 by simp only [fTilde, if_neg h0]]
      exact fTilde_nonneg k R T d hR
    · exact fTilde_anti k R T hR d n hn hdn
  have hL3 := S1_le k K₀ N R (W k) ν₀ (yTensor k R T) (fTilde k R T)
    (fun n => ⟨fTilde_nonneg k R T n hR, fTilde_le_one k R T hR n⟩) hfmono (fun r => rfl) rfl
    hk hD hK₀ hsol
  have htriv := hC0le R hR (yTensor k R T) (yTensor_abs_le_one k R T hR)
  have hyside := yside_le_A1pow k R T
  have hcoef : (0 : ℝ) ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    have h2 : (0 : ℝ) ≤ ((K₀ - 1) * N / (W k) : ℝ) :=
      div_nonneg (mul_nonneg h1 (Nat.cast_nonneg N)) (Nat.cast_nonneg _)
    linarith
  calc S1 k K₀ N R (W k) ν₀ (yTensor k R T)
      ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ)
          * (∑ r ∈ kSieveIndex k R (W k), (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R (W k), |lam k R (W k) (yTensor k R T) d|) ^ 2 :=
        hL3
    _ ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hyside hcoef)
          (mul_le_mul_of_nonneg_left htriv (by positivity))
    _ = 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + (2 ^ (k + 1) * C0) * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

/-! ## Regime threshold real-analysis: polynomial beats polylog

The `herr1`/`herr2`/`hδlb` thresholds all reduce to "a fixed power of `1+log x`
is eventually dominated by a positive power of `x`". -/

open Filter Asymptotics in
omit [TupleChoice] in
/-- **Polynomial beats polylog.**  For any degree `n`, exponent `a > 0`, and
coefficient `K`, eventually `K·(1+log x)^n ≤ x^a`.  This is the analytic core of
the `herr` thresholds (`R²·(1+log R)^{4k+2} = o(N')` at `R = ⌊N'^{1/5}⌋`). -/
theorem eventually_poly_beats_polylog (n : ℕ) (a K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ n ≤ x ^ a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero, mul_one]
    filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop K] with x hx using hx
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set r := a / (2 * n) with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    have hlog := isLittleO_log_rpow_atTop hrpos
    have hev1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ r := by
      filter_upwards [hlog.eventuallyLE, (eventually_gt_atTop (0 : ℝ))] with x hx hx0
      calc Real.log x ≤ |Real.log x| := le_abs_self _
        _ ≤ |x ^ r| := hx
        _ = x ^ r := abs_of_nonneg (Real.rpow_nonneg hx0.le r)
    have hev2 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x ^ r :=
      (tendsto_rpow_atTop hrpos).eventually_ge_atTop 1
    have hev3 : ∀ᶠ x : ℝ in atTop, K * 2 ^ n ≤ x ^ (a / 2) :=
      (tendsto_rpow_atTop (by positivity : (0 : ℝ) < a / 2)).eventually_ge_atTop (K * 2 ^ n)
    filter_upwards [hev1, hev2, hev3, (eventually_ge_atTop (1 : ℝ))]
      with x hlx h1x h3x hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hbase_nn : 0 ≤ 1 + Real.log x := by linarith
    have hstep : 1 + Real.log x ≤ 2 * x ^ r := by linarith [hlx, h1x]
    -- `(x^r)^n = x^(a/2)` since `r·n = a/2`.
    have hpow : (x ^ r) ^ n = x ^ (a / 2) := by
      rw [← Real.rpow_natCast (x ^ r) n, ← Real.rpow_mul hx0.le]
      congr 1
      rw [hr]; field_simp
    have hxa2nn : (0 : ℝ) ≤ x ^ (a / 2) := Real.rpow_nonneg hx0.le _
    have hxann : (0 : ℝ) ≤ x ^ a := Real.rpow_nonneg hx0.le _
    by_cases hK : 0 ≤ K
    · calc K * (1 + Real.log x) ^ n
          ≤ K * (2 * x ^ r) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hstep n) hK
        _ = K * 2 ^ n * x ^ (a / 2) := by rw [mul_pow, hpow]; ring
        _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right h3x hxa2nn
        _ = x ^ a := by rw [← Real.rpow_add hx0]; congr 1; ring
    · have hle0 : K * (1 + Real.log x) ^ n ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hK)) (pow_nonneg hbase_nn n)
      linarith [hxann]

end Salt.Maynard
