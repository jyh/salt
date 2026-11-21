/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.PerronPsi
import Salt.RH.VonKochRect

/-!
# O106 row R1, node N7 — von Koch from RH: `RiemannHypothesis → VonKochPsi 3`

At `y ≥ 55` at distance `≥ 1/2` from every integer, take `σ₀ = 1/2 + 1/log y`, `c₀ = 1 + 1/log y`
and `T = y²`. The rectangle identity (N5) says bottom − top + `I`·right − `I`·left `= 2πi·y`. The
right edge is the Perron integral (N4a), within `8e(log y + 1080 log 2)` of `2πi ψ(y)` (N4b). The
other three edges are bounded through N3 (N6). Here `y^{c₀} = e·y` and `y^{σ₀} = e·√y`, so all of
it is `≪ √y (log y)³`. Then every `x ≥ 56` is moved to `y = ⌊x⌋ + 1/2` (same `ψ`, `|x − y| ≤ 1/2`),
and `2 ≤ x < 56` is bounded by `ψ(x) ≤ x log x`.

`RiemannHypothesis` is Mathlib's, carried as a NAMED HYPOTHESIS (the O106 exception).
-/

namespace Salt.RH

open Complex Salt.SW Salt.MR ArithmeticFunction

theorem exp_four_lt : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e4]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 55 := by norm_num

theorem rpow_inv_log {y : ℝ} (hy : 1 < y) : y ^ (1 / Real.log y) = Real.exp 1 := by
  have hL : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  rw [Real.rpow_def_of_pos (by linarith), mul_one_div_cancel hL]

/-- `ψ(x) ≤ x log x` for `x ≥ 1`. -/
theorem psi_le_mul_log {x : ℝ} (hx : 1 ≤ x) : Chebyshev.psi x ≤ x * Real.log x := by
  unfold Chebyshev.psi
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log x := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
        have hnx' : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp hnx
        exact vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnx')
    _ = (⌊x⌋₊ : ℝ) * Real.log x := by simp
    _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) hlx

/-- The closing real arithmetic of N7a. -/
theorem final_arith {e K L s P B Q F : ℝ} (he : 0 < e) (hK : 0 ≤ K) (hL : 4 ≤ L) (hs : 1 ≤ s)
    (hP : P ≤ 8 * e * (L + 760)) (hB : B ≤ (4 + 6 * K * L ^ 2) * e)
    (hQ : Q ≤ (4 + 6 * K * L ^ 2) * e)
    (hF : F ≤ (4 + 6 * K * L ^ 2) * (s * e) * (8 * (3 * L))) :
    P + B + Q + F ≤ e * (8 * 761 + 25 * (4 + 6 * K)) * s * L ^ 3 := by
  set A : ℝ := 4 + 6 * K * L ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hL3 : L ≤ L ^ 3 := by nlinarith
  have hL3' : 1 ≤ L ^ 3 := by nlinarith
  have hsL3 : L ^ 3 ≤ s * L ^ 3 := by nlinarith
  have hAL : A * L ≤ (4 + 6 * K) * L ^ 3 := by
    have : 4 * L ≤ 4 * L ^ 3 := by linarith
    have : 6 * K * L ^ 2 * L = 6 * K * L ^ 3 := by ring
    rw [hA, add_mul]
    nlinarith
  -- P
  have e1 : P ≤ 8 * 761 * e * (s * L ^ 3) := by
    have h : L + 760 ≤ 761 * (s * L ^ 3) := by nlinarith
    calc P ≤ 8 * e * (L + 760) := hP
      _ ≤ 8 * e * (761 * (s * L ^ 3)) := by gcongr
      _ = 8 * 761 * e * (s * L ^ 3) := by ring
  -- B + Q + F
  have e2 : B + Q + F ≤ 25 * e * s * (A * L) := by
    have hBQ : B + Q ≤ 2 * A * e := by linarith
    have h2 : 2 * A * e ≤ A * e * s * L := by
      have : 2 ≤ s * L := by nlinarith
      have : 0 ≤ A * e := by positivity
      nlinarith
    have hF' : F ≤ 24 * A * e * s * L := by
      have : A * (s * e) * (8 * (3 * L)) = 24 * A * e * s * L := by ring
      linarith
    have : 2 * A * e + 24 * A * e * s * L ≤ 25 * e * s * (A * L) := by nlinarith
    linarith
  have e3 : 25 * e * s * (A * L) ≤ 25 * e * s * ((4 + 6 * K) * L ^ 3) := by
    have : 0 ≤ 25 * e * s := by positivity
    exact mul_le_mul_of_nonneg_left hAL this
  have : e * (8 * 761 + 25 * (4 + 6 * K)) * s * L ^ 3
      = 8 * 761 * e * (s * L ^ 3) + 25 * e * s * ((4 + 6 * K) * L ^ 3) := by ring
  linarith

set_option maxHeartbeats 800000 in -- four edge integrals in one context: whnf times out at 200000
/-- **N7a.** Under RH, at `y ≥ 55` at distance `≥ 1/2` from every integer,
`|ψ(y) − y| ≤ C √y (log y)³`. -/
theorem psi_sub_le_halfint (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 55 ≤ y → (∀ m : ℕ, 1 / 2 ≤ |y - m|) →
      |Chebyshev.psi y - y| ≤ C * Real.sqrt y * Real.log y ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := zc_logDeriv_near_half hRH
  set e : ℝ := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  refine ⟨e * (8 * 761 + 25 * (4 + 6 * K)) / (2 * Real.pi), by positivity, fun y hy hyn => ?_⟩
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  set L : ℝ := Real.log y with hL
  have hL4 : 4 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hy0]; linarith [exp_four_lt]
  have hL0 : 0 < L := by linarith
  set σ₀ : ℝ := 1 / 2 + 1 / L with hσ₀
  set c₀ : ℝ := 1 + 1 / L with hc₀
  set T : ℝ := y ^ 2 with hT
  have hiL : 1 / L ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hL4
  have hiL0 : 0 < 1 / L := by positivity
  have hσa : 1 / 2 < σ₀ := by linarith
  have hσb : σ₀ ≤ 3 / 4 := by linarith
  have hσc : σ₀ < 1 := by linarith
  have hca : 1 < c₀ := by linarith
  have hcb : c₀ ≤ 2 := by linarith
  have hσc₀ : σ₀ ≤ c₀ := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hT0 : 0 < T := by linarith
  -- the powers of `y`
  have hyc : y ^ c₀ = y * e := by
    rw [hc₀, Real.rpow_add hy0, Real.rpow_one, rpow_inv_log hy1]
  have hys : y ^ σ₀ = Real.sqrt y * e := by
    rw [hσ₀, Real.rpow_add hy0, rpow_inv_log hy1, Real.sqrt_eq_rpow]
  -- N5, unfolded
  have h5 := rectBI_phiR_eq hRH hy0 hσa hσc hca hT0
  unfold rectBI at h5
  have hzr : ((σ₀ : ℂ) - (T : ℂ) * I).re = σ₀ := by simp
  have hzi : ((σ₀ : ℂ) - (T : ℂ) * I).im = -T := by simp
  have hwr : ((c₀ : ℂ) + (T : ℂ) * I).re = c₀ := by simp
  have hwi : ((c₀ : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [hzr, hzi, hwr, hwi] at h5
  set Bt := ∫ x : ℝ in σ₀..c₀, phiR y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)
      / (((x : ℂ) + ((-T : ℝ) : ℂ) * I) - 1) with hBt
  set Tp := ∫ x : ℝ in σ₀..c₀, phiR y ((x : ℂ) + (T : ℂ) * I)
      / (((x : ℂ) + (T : ℂ) * I) - 1) with hTp
  set R := ∫ v : ℝ in (-T)..T, phiR y ((c₀ : ℂ) + (v : ℂ) * I)
      / (((c₀ : ℂ) + (v : ℂ) * I) - 1) with hR
  set Lf := ∫ v : ℝ in (-T)..T, phiR y ((σ₀ : ℂ) + (v : ℂ) * I)
      / (((σ₀ : ℂ) + (v : ℂ) * I) - 1) with hLf
  have h5' : Bt - Tp + I * R - I * Lf = 2 * (Real.pi : ℂ) * I * y := h5
  -- the right edge is the Perron integral
  have hRP : R = ∫ v : ℝ in (-T)..T, LSeries (fun n => (Λ n : ℂ)) ((c₀ : ℂ) + (v : ℂ) * I)
      * pk y ((c₀ : ℂ) + (v : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun v _ => ?_
    have hre : 1 < ((c₀ : ℂ) + (v : ℂ) * I).re := by
      rw [show ((c₀ : ℂ) + (v : ℂ) * I).re = c₀ by simp]; exact hca
    have hs1 : ((c₀ : ℂ) + (v : ℂ) * I) ≠ 1 := by
      intro h; rw [h] at hre; simp at hre
    have hz : riemannZeta ((c₀ : ℂ) + (v : ℂ) * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hre.le
    rw [phiR_div_eq hs1 hz, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, logDeriv_apply,
      neg_div]
  have hyn' : ∀ m : ℕ, (m : ℝ) ≠ y := by
    intro m h
    have := hyn m
    rw [h, sub_self, abs_zero] at this
    norm_num at this
  have hP := perron_psi hy1 hyn' hca hT0
  rw [← hRP] at hP
  have hE := perron_psi_error_le hy1.le hyn hca hcb hT0
  have hc1 : 1 / (c₀ - 1) = L := by
    rw [show c₀ - 1 = 1 / L by rw [hc₀]; ring, one_div_one_div]
  rw [hc1, hyc] at hE
  -- the other edges
  have hLfb := left_edge_le hK0.le hK hy0 hσa hσb hT0.le
  have hBtb := horiz_edge_le (b := -T) hK0.le hK hy1.le hσa hσc₀ hcb
    (by rw [abs_neg, abs_of_pos hT0]; exact hT1)
  have hTpb := horiz_edge_le (b := T) hK0.le hK hy1.le hσa hσc₀ hcb
    (by rw [abs_of_pos hT0]; exact hT1)
  rw [abs_neg, abs_of_pos hT0] at hBtb
  rw [abs_of_pos hT0] at hTpb
  have hσL : 1 / (σ₀ - 1 / 2) = L := by
    rw [show σ₀ - 1 / 2 = 1 / L by rw [hσ₀]; ring, one_div_one_div]
  rw [hσL, hys] at hLfb
  rw [hσL, hyc] at hBtb hTpb
  -- the triangle inequality
  have hkey : (2 * (Real.pi : ℂ) * I) * ((Chebyshev.psi y : ℂ) - y)
      = -(I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)) - Bt + Tp + I * Lf := by
    linear_combination h5'
  have hnorm : 2 * Real.pi * |Chebyshev.psi y - y|
      ≤ ‖I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
    have h1 : ‖(2 * (Real.pi : ℂ) * I) * ((Chebyshev.psi y : ℂ) - y)‖
        = 2 * Real.pi * |Chebyshev.psi y - y| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    rw [← h1, hkey]
    have := norm_add_le (-(I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)) - Bt + Tp)
      (I * Lf)
    have h2 := norm_add_le (-(I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)) - Bt) Tp
    have h3 := norm_sub_le (-(I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ))) Bt
    rw [norm_neg] at h3
    rw [norm_mul, Complex.norm_I, one_mul] at this
    linarith
  -- sizes
  have hA : 4 + K * Real.log (T + 3) * (1 + L) ≤ 4 + 6 * K * L ^ 2 := by
    have hT3 : T + 3 ≤ y ^ 3 := by rw [hT]; nlinarith
    have hlog : Real.log (T + 3) ≤ 3 * L := by
      have := Real.log_le_log (by positivity) hT3
      rwa [Real.log_pow] at this
    have h1L : 1 + L ≤ 2 * L := by linarith
    have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    have h3 : Real.log (T + 3) * (1 + L) ≤ 3 * L * (2 * L) :=
      mul_le_mul hlog h1L (by linarith) (by linarith)
    have h4 : K * Real.log (T + 3) * (1 + L) ≤ K * (3 * L * (2 * L)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hK0.le
    have h5 : K * (3 * L * (2 * L)) = 6 * K * L ^ 2 := by ring
    linarith
  have hlog1T : Real.log (1 + T) ≤ 3 * L := by
    have h : 1 + T ≤ y ^ 3 := by rw [hT]; nlinarith
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_pow] at this
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hl2 : Real.log 2 < 7 / 10 := by
    have := Real.log_two_lt_d9; linarith
  set A : ℝ := 4 + 6 * K * L ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hAA : 4 + K * Real.log (T + 3) * (1 + L) ≤ A := hA
  have hcs : c₀ - σ₀ = 1 / 2 := by rw [hc₀, hσ₀]; ring
  have hE' : ‖I * R - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)‖ ≤ 8 * e * (L + 760) := by
    have h1 := le_trans hP hE
    have hq : 8 * y * (y * e) / T = 8 * e := by rw [hT]; field_simp
    rw [hq] at h1
    nlinarith
  have hBt' : ‖Bt‖ ≤ A * e := by
    have hq : y * e / T * (c₀ - σ₀) ≤ e := by
      rw [hcs, hT, show y * e / y ^ 2 * (1 / 2) = e / (2 * y) by field_simp]
      exact div_le_self he0.le (by linarith)
    calc ‖Bt‖ ≤ (4 + K * Real.log (T + 3) * (1 + L)) * (y * e / T) * (c₀ - σ₀) := hBtb
      _ = (4 + K * Real.log (T + 3) * (1 + L)) * (y * e / T * (c₀ - σ₀)) := by ring
      _ ≤ A * e := mul_le_mul hAA hq (by have := hσc₀; positivity) hA0
  have hTp' : ‖Tp‖ ≤ A * e := by
    have hq : y * e / T * (c₀ - σ₀) ≤ e := by
      rw [hcs, hT, show y * e / y ^ 2 * (1 / 2) = e / (2 * y) by field_simp]
      exact div_le_self he0.le (by linarith)
    calc ‖Tp‖ ≤ (4 + K * Real.log (T + 3) * (1 + L)) * (y * e / T) * (c₀ - σ₀) := hTpb
      _ = (4 + K * Real.log (T + 3) * (1 + L)) * (y * e / T * (c₀ - σ₀)) := by ring
      _ ≤ A * e := mul_le_mul hAA hq (by have := hσc₀; positivity) hA0
  have hLf' : ‖Lf‖ ≤ A * (Real.sqrt y * e) * (8 * (3 * L)) := by
    calc ‖Lf‖ ≤ (4 + K * Real.log (T + 3) * (1 + L)) * (Real.sqrt y * e)
          * (8 * Real.log (1 + T)) := hLfb
      _ ≤ A * (Real.sqrt y * e) * (8 * (3 * L)) := by
          have h0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
          gcongr
  -- assemble
  have htot : 2 * Real.pi * |Chebyshev.psi y - y|
      ≤ e * (8 * 761 + 25 * (4 + 6 * K)) * Real.sqrt y * L ^ 3 :=
    le_trans hnorm (final_arith he0 hK0.le hL4 hsq1 hE' hBt' hTp' hLf')
  calc |Chebyshev.psi y - y|
      = 2 * Real.pi * |Chebyshev.psi y - y| / (2 * Real.pi) := by field_simp
    _ ≤ e * (8 * 761 + 25 * (4 + 6 * K)) * Real.sqrt y * L ^ 3 / (2 * Real.pi) := by
        gcongr
    _ = e * (8 * 761 + 25 * (4 + 6 * K)) / (2 * Real.pi) * Real.sqrt y * L ^ 3 := by ring

/-- A half-integer is at distance `≥ 1/2` from every natural number. -/
theorem half_int_dist (n m : ℕ) : 1 / 2 ≤ |((n : ℝ) + 1 / 2) - m| := by
  rcases le_or_gt m n with h | h
  · have : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

/-- **N7 — von Koch from RH.** `RiemannHypothesis → VonKochPsi 3`:
`|ψ(x) − x| ≤ C √x (log x)³` for every `x ≥ 2`. -/
theorem vonKochPsi_three_of_RH (hRH : RiemannHypothesis) : VonKochPsi 3 := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_le_halfint hRH
  refine ⟨max (16 * C + 1) 840, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hM : 16 * C + 1 ≤ max (16 * C + 1) 840 := le_max_left _ _
  have hM' : (840 : ℝ) ≤ max (16 * C + 1) 840 := le_max_right _ _
  by_cases hx56 : 56 ≤ x
  · set n : ℕ := ⌊x⌋₊ with hn
    set y : ℝ := (n : ℝ) + 1 / 2 with hy
    have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hn56 : (56 : ℝ) ≤ n := by
      have : (56 : ℕ) ≤ n := Nat.le_floor (by exact_mod_cast hx56)
      exact_mod_cast this
    have hy55 : 55 ≤ y := by linarith
    have hfl : ⌊y⌋₊ = n := by
      rw [Nat.floor_eq_iff (by linarith)]; constructor <;> linarith
    have hpsi : Chebyshev.psi x = Chebyshev.psi y := by
      rw [Chebyshev.psi_eq_psi_coe_floor x, Chebyshev.psi_eq_psi_coe_floor y, hfl]
    have hmain := hC y hy55 (fun m => half_int_dist n m)
    have hxy : |y - x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    -- compare y with x
    have hsy : Real.sqrt y ≤ 2 * Real.sqrt x := by
      have : Real.sqrt y ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at this
      exact this
    have hly : Real.log y ≤ 2 * Real.log x := by
      have h : y ≤ x ^ 2 := by nlinarith
      have := Real.log_le_log (by linarith) h
      rwa [Real.log_pow] at this
    have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hly3 : Real.log y ^ 3 ≤ 8 * Real.log x ^ 3 := by
      have := pow_le_pow_left₀ hly0 hly 3
      nlinarith
    have hlx1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      have := Real.exp_one_lt_d9; linarith
    have hsx1 : 1 ≤ Real.sqrt x := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hone : (1 : ℝ) ≤ Real.sqrt x * Real.log x ^ 3 := by
      have : 1 ≤ Real.log x ^ 3 := one_le_pow₀ hlx1
      nlinarith
    have hbig : C * Real.sqrt y * Real.log y ^ 3 ≤ 16 * C * (Real.sqrt x * Real.log x ^ 3) := by
      have h1 : Real.sqrt y * Real.log y ^ 3 ≤ (2 * Real.sqrt x) * (8 * Real.log x ^ 3) :=
        mul_le_mul hsy hly3 (by positivity) (by positivity)
      nlinarith
    calc |Chebyshev.psi x - x| = |(Chebyshev.psi y - y) + (y - x)| := by rw [hpsi]; ring_nf
      _ ≤ |Chebyshev.psi y - y| + |y - x| := abs_add_le _ _
      _ ≤ 16 * C * (Real.sqrt x * Real.log x ^ 3) + 1 := by linarith
      _ ≤ (16 * C + 1) * (Real.sqrt x * Real.log x ^ 3) := by nlinarith
      _ ≤ max (16 * C + 1) 840 * Real.sqrt x * Real.log x ^ 3 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hM (by positivity)
  · replace hx56 : x < 56 := lt_of_not_ge hx56
    have hpsi0 := Chebyshev.psi_nonneg x
    have hpsi : Chebyshev.psi x ≤ 56 * 5 := by
      have h1 := psi_le_mul_log (show (1 : ℝ) ≤ x by linarith)
      have hl56 : Real.log x < 5 := by
        rw [Real.log_lt_iff_lt_exp hx0]
        have : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have e5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e5]
        have : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 := by gcongr
        nlinarith
      nlinarith
    have habs : |Chebyshev.psi x - x| ≤ 336 := by
      rw [abs_le]; constructor <;> linarith
    have hsq2 : (1.41 : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; nlinarith
    have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hlow : (2 / 5 : ℝ) ≤ Real.sqrt x * Real.log x ^ 3 := by
      have h3 : (0.6931471803 : ℝ) ^ 3 ≤ Real.log x ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 3
      have : (1.41 : ℝ) * 0.6931471803 ^ 3 ≤ Real.sqrt x * Real.log x ^ 3 :=
        mul_le_mul hsq2 h3 (by positivity) hsx.le
      have : (2 / 5 : ℝ) ≤ 1.41 * 0.6931471803 ^ 3 := by norm_num
      linarith
    calc |Chebyshev.psi x - x| ≤ 336 := habs
      _ = 840 * (2 / 5) := by norm_num
      _ ≤ 840 * (Real.sqrt x * Real.log x ^ 3) := by gcongr
      _ ≤ max (16 * C + 1) 840 * (Real.sqrt x * Real.log x ^ 3) :=
          mul_le_mul_of_nonneg_right hM' (by positivity)
      _ = max (16 * C + 1) 840 * Real.sqrt x * Real.log x ^ 3 := by ring

end Salt.RH
