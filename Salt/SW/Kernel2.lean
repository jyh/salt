/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Kernel

/-!
# B2 — the kernel node K: the TWICE-smoothed Riesz kernel

`(1 - u)²₊ ↔ 2·y^w/(w(w+1)(w+2))`: the `Kernel.lean` deliverables (`kern`, `hasMellin_kern`,
`verticalIntegrable_mellin_kern`, `kernel_identity`, `kernel_sum_swap`) re-run with one more
pole. The `1/|w|³` decay (`norm_inv_denom2_cubic_le`, with NO `c`-dependent constant) is what
lets Jutila's Lemma 6 contour sit at `Re = 1/2` against the corpus's `(1 + |t|)` growth
(`LFunction_growth`); the `(1/c)`-weighted quadratic bound `norm_inv_denom2_le` is an
integrability tool only. Nothing in `Kernel.lean` moves.

## The measured control (§2(a) of the design cut)

The residues of `2·y^w/(w(w+1)(w+2))` at `w = 0, -1, -2` sum to `1 - 2/y + 1/y² = (1 - 1/y)²`;
at `y = 2` that reads `1/4`, and the numeric inversion agrees (`0.25000`, imaginary part
`-2.6e-17`); at `y = 1/2 < 1` the integral is `0.00000`.  The `example` beside
`kernel_identity_2` is the Lean form of that check.

## The honest label

The row W7's contour bound consumes is `norm_inv_denom2_cubic_le` — the CUBIC decay with no
`c`-dependent constant.  `norm_inv_denom2_le`, whose constant `1/c` blows up as `c → 0⁺`, is
an integrability tool only and is used only as such here.  The contour node itself is W7's
own work, not this file's.
-/

open MeasureTheory Complex Set

noncomputable section
namespace Salt.SW

/-- The twice-smoothed profile `t ↦ ((1 - t)₊)²`, ℂ-valued. -/
def kern2 : ℝ → ℂ := fun t => (((max 0 (1 - t)) ^ 2 : ℝ) : ℂ)

theorem kern2_eq_sq_kern (t : ℝ) : kern2 t = kern t ^ 2 := by
  simp [kern2, kern]

theorem continuous_kern2 : Continuous kern2 := by
  have h : Continuous fun t : ℝ => (max 0 (1 - t)) ^ 2 :=
    (continuous_const.max (continuous_const.sub continuous_id)).pow 2
  exact Complex.continuous_ofReal.comp h

/-- On `t > 0` the twice-smoothed profile is the `Ioc 0 1` indicator combination
`1 - 2·t + t²` — the `kern_eq_indicator_diff` shape with a third term. -/
private lemma kern2_eq_indicator_comb {t : ℝ} (ht : 0 < t) :
    kern2 t = Set.indicator (Ioc 0 1) (fun _ => (1 : ℂ)) t
        - (2 : ℂ) • Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ)) t
        + Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (2 : ℕ)) t := by
  simp only [kern2, smul_eq_mul]
  by_cases h : t ≤ 1
  · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht, h⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      max_eq_right (by linarith : (0:ℝ) ≤ 1 - t)]
    push_cast; ring
  · rw [not_le] at h
    have hnot : t ∉ Ioc (0:ℝ) 1 := by
      simp only [Set.mem_Ioc, not_and, not_le]; intro _; exact h
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot,
      Set.indicator_of_notMem hnot, max_eq_left (by linarith : (1:ℝ) - t ≤ 0)]
    push_cast; ring

theorem hasMellin_kern2 {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent kern2 s ∧ mellin kern2 s = 2 / (s * (s + 1) * (s + 2)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre : (s + 2).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.re_ofNat] at hre
    linarith
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (s := s) (1 : ℂ) (by rw [Complex.one_re]; linarith)
  simp only [Complex.cpow_one] at h2
  have h3 := hasMellin_cpow_Ioc (s := s) (2 : ℂ) (by rw [Complex.re_ofNat]; linarith)
  simp only [Complex.cpow_two] at h3
  have h2' := hasMellin_const_smul h2.1 (2 : ℂ)
  have hsub := hasMellin_sub h1.1 h2'.1
  have hadd := hasMellin_add hsub.1 h3.1
  rw [hsub.2, h1.2, h2'.2, h2.2, h3.2] at hadd
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent]
    refine hadd.1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [kern2_eq_indicator_comb ht]
  · have hmel : mellin kern2 s
        = mellin (fun t => Set.indicator (Ioc 0 1) (fun _ => (1 : ℂ)) t
          - (2 : ℂ) • Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ)) t
          + Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (2 : ℕ)) t) s := by
      simp only [mellin]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp only [kern2_eq_indicator_comb ht]
    rw [hmel, hadd.2, smul_eq_mul]
    field_simp
    ring

theorem s2_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c : ℂ) + (t : ℂ) * I + 2) ≠ 0 := by
  have hre : ((c:ℂ) + (t:ℂ) * I + 2).re = c + 2 := by simp
  intro h; rw [h] at hre; simp at hre; linarith

theorem norm_inv_denom2_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1) * ((c : ℂ) + (t : ℂ) * I + 2))⁻¹‖
      ≤ (1 / c) * (c ^ 2 + t ^ 2)⁻¹ := by
  have hnC : ‖(c : ℂ) + (t : ℂ) * I + 2‖ = Real.sqrt ((c + 2) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hC : c ≤ ‖(c : ℂ) + (t : ℂ) * I + 2‖ := by
    calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ Real.sqrt ((c + 2) ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
      _ = ‖(c : ℂ) + (t : ℂ) * I + 2‖ := hnC.symm
  have h1 : ‖((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)‖⁻¹ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
    have h := norm_inv_denom_le hc t
    rwa [norm_inv] at h
  have h2 : ‖(c : ℂ) + (t : ℂ) * I + 2‖⁻¹ ≤ 1 / c := by
    rw [one_div]; exact inv_anti₀ hc hC
  rw [norm_inv, norm_mul, mul_inv]
  calc ‖((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)‖⁻¹
        * ‖(c : ℂ) + (t : ℂ) * I + 2‖⁻¹
      ≤ (c ^ 2 + t ^ 2)⁻¹ * (1 / c) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (1 / c) * (c ^ 2 + t ^ 2)⁻¹ := mul_comm _ _

theorem norm_inv_denom2_cubic_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1) * ((c : ℂ) + (t : ℂ) * I + 2))⁻¹‖
      ≤ ((c ^ 2 + t ^ 2) ^ (3 / 2 : ℝ))⁻¹ := by
  have hS0 : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg t)
  have hA : ‖(c : ℂ) + (t : ℂ) * I‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hB : ‖(c : ℂ) + (t : ℂ) * I + 1‖ = Real.sqrt ((c + 1) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hC : ‖(c : ℂ) + (t : ℂ) * I + 2‖ = Real.sqrt ((c + 2) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hcube : (c ^ 2 + t ^ 2) ^ (3 / 2 : ℝ) = Real.sqrt (c ^ 2 + t ^ 2) ^ 3 := by
    have h32 : ((3 : ℝ) / 2) = (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) := by norm_num
    rw [h32, Real.rpow_mul hS0.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hprod : (c ^ 2 + t ^ 2) ^ (3 / 2 : ℝ)
      ≤ ‖((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1) * ((c : ℂ) + (t : ℂ) * I + 2)‖ := by
    rw [norm_mul, norm_mul, hA, hB, hC, hcube]
    have h0 : (0 : ℝ) ≤ Real.sqrt (c ^ 2 + t ^ 2) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (c ^ 2 + t ^ 2) ≤ Real.sqrt ((c + 1) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hc.le, sq_nonneg t])
    have h2 : Real.sqrt (c ^ 2 + t ^ 2) ≤ Real.sqrt ((c + 2) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hc.le, sq_nonneg t])
    calc Real.sqrt (c ^ 2 + t ^ 2) ^ 3
        = Real.sqrt (c ^ 2 + t ^ 2) * Real.sqrt (c ^ 2 + t ^ 2) * Real.sqrt (c ^ 2 + t ^ 2) := by
          ring
      _ ≤ Real.sqrt (c ^ 2 + t ^ 2) * Real.sqrt ((c + 1) ^ 2 + t ^ 2)
            * Real.sqrt ((c + 2) ^ 2 + t ^ 2) := by gcongr
  rw [norm_inv]
  exact inv_anti₀ (by positivity) hprod

theorem verticalIntegrable_mellin_kern2 {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable (mellin kern2) c := by
  have hint : Integrable (fun t : ℝ =>
      (((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1) * ((c:ℂ) + (t:ℂ) * I + 2))⁻¹) := by
    refine ((integrable_inv_c_sq_add_sq hc).const_mul (1 / c)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      apply Continuous.inv₀
      · fun_prop
      · intro t
        exact mul_ne_zero (mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)) (s2_ne_zero hc t)
    · filter_upwards with t; exact norm_inv_denom2_le hc t
  rw [Complex.VerticalIntegrable]
  refine (hint.const_mul 2).congr ?_
  filter_upwards with t
  have hsre : 0 < ((c:ℂ) + (t:ℂ) * I).re := by simp; linarith
  rw [(hasMellin_kern2 hsre).2, div_eq_mul_inv]

theorem kern2_value {y : ℝ} (hy : 0 < y) :
    kern2 (1 / y) = if 1 ≤ y then (1 - 1 / (y : ℂ)) ^ 2 else 0 := by
  rw [kern2_eq_sq_kern, kern_value hy]
  split_ifs with h
  · rfl
  · exact zero_pow two_ne_zero

theorem kernel_identity_2 {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) • ∫ t : ℝ,
        2 * (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1) * ((c : ℂ) + (t : ℂ) * I + 2))
      = if 1 ≤ y then (1 - 1 / (y : ℂ)) ^ 2 else 0 := by
  have hx : (0 : ℝ) < 1 / y := by positivity
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hMC : MellinConvergent kern2 (↑c) := (hasMellin_kern2 hcre).1
  have hVI : Complex.VerticalIntegrable (mellin kern2) c := verticalIntegrable_mellin_kern2 hc
  have hCont : ContinuousAt kern2 (1 / y) := continuous_kern2.continuousAt
  have key := mellinInv_mellin_eq c kern2 hx hMC hVI hCont
  rw [kern2_value hy] at key
  rw [← key, mellinInv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs_def
  have hsre : 0 < s.re := by rw [hs_def]; simpa using hc
  rw [(hasMellin_kern2 hsre).2, reflect hy s, smul_eq_mul]
  ring

/-- The §2(a) control for K: the inversion at `y = 2`, `c = 1` reads `(1 - 1/2)² = 1/4`.
It INVOKES `kernel_identity_2`; the mutation `2 → 1` in the numerator would make it `1/8`. -/
example : (1 / (2 * Real.pi)) • ∫ t : ℝ,
    2 * ((2 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * I) /
      ((((1 : ℝ) : ℂ) + (t : ℂ) * I) * (((1 : ℝ) : ℂ) + (t : ℂ) * I + 1)
        * (((1 : ℝ) : ℂ) + (t : ℂ) * I + 2)) = 1 / 4 := by
  rw [kernel_identity_2 (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem integrable_Fterm2 (w : ℂ) {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => 2 * w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2))) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have hzero : (fun t : ℝ => 2 * w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2))) = fun _ => 0 := by
      funext t
      rw [← hb0, Complex.ofReal_zero, Complex.zero_cpow (s_ne_zero hc t)]; ring
    rw [hzero]; exact integrable_zero _ _ _
  · refine ((integrable_inv_c_sq_add_sq hc).const_mul (‖2 * w‖ * b ^ c * (1 / c))).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      refine Continuous.div (continuous_const.mul (Continuous.const_cpow (by fun_prop)
        (Or.inl (Complex.ofReal_ne_zero.mpr hbpos.ne')))) (by fun_prop) ?_
      intro t
      exact mul_ne_zero (mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)) (s2_ne_zero hc t)
    · filter_upwards with t
      have hnorm : ‖2 * w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2))‖
          = (‖2 * w‖ * b ^ c)
            * ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
                * ((c : ℂ) + (t : ℂ) * I + 2))⁻¹‖ := by
        rw [norm_div, norm_mul, norm_ofReal_cpow_vert hbpos.le hc, norm_inv]; ring
      rw [hnorm]
      have hd := norm_inv_denom2_le hc t
      have hK : (0 : ℝ) ≤ ‖2 * w‖ * b ^ c := by positivity
      have hmul := mul_le_mul_of_nonneg_left hd hK
      linarith [hmul]

theorem kernel_sum_swap_2 (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (x / n) ^ c)) :
    ∑' n : ℕ, (∫ t : ℝ, 2 * a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2)))
      = ∫ t : ℝ, 2 * (∑' n : ℕ, a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2)) := by
  have hb : ∀ n : ℕ, (0 : ℝ) ≤ x / n := fun n => by positivity
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hInt : ∀ n : ℕ, Integrable (fun t : ℝ =>
      2 * a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2))) :=
    fun n => integrable_Fterm2 (a n) (hb n) hc
  have hSum : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖2 * a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
            * ((c : ℂ) + (t : ℂ) * I + 2))‖) := by
    have heq : (fun n : ℕ => ∫ t : ℝ,
        ‖2 * a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
              * ((c : ℂ) + (t : ℂ) * I + 2))‖)
        = fun n : ℕ => 2 * (‖a n‖ * (x / n) ^ c)
            * ∫ t : ℝ, ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)
                * ((c : ℂ) + (t : ℂ) * I + 2))⁻¹‖ := by
      funext n
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      rw [norm_div, norm_mul, norm_ofReal_cpow_vert (hb n) hc, norm_inv, norm_mul, h2n]
      ring
    rw [heq]; exact (hsum.mul_left 2).mul_right _
  rw [integral_tsum_of_summable_integral_norm hInt hSum]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [tsum_div_const]
  congr 1
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

end Salt.SW
