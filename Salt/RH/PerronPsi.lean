/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronTrunc

/-!
# O106 row R1, node N4a — truncated Perron for `ψ`

For `y > 1` not an integer, `c > 1` and `T > 0`,

`‖I ∫_{-T}^{T} L(Λ, c+iv) y^{c+iv}/(c+iv) dv − 2πi ψ(y)‖ ≤ ∑' m, Λ(m) · 2 (y/m)^c / (T |log(y/m)|)`.

Route: the Dirichlet series `L(Λ, s)` converges absolutely on `Re s = c`, so the integral of the
series is the series of integrals (Mathlib's
`intervalIntegral.hasSum_integral_of_dominated_convergence`, dominated by `Λ(m) (y/m)^c / c`).
The `m`-th integral is `Λ(m)` times the Perron contour at `y/m`, which the landed
`Salt.MR.perron_trunc` (the decay branch) compares with `2πi [m < y]`. The
indicator sum is `2πi ψ(y)`.
-/

namespace Salt.RH

open Complex MeasureTheory intervalIntegral Salt.MR ArithmeticFunction

/-- `(a/b)^s = a^s / b^s` for positive reals `a, b`. -/
theorem ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    (((a / b : ℝ)) : ℂ) ^ s = (a : ℂ) ^ s / (b : ℂ) ^ s := by
  have harg : (b : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, div_eq_mul_inv]

/-- The `m`-th term of the series under the integral. -/
noncomputable def psiTerm (y c : ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  (Λ m : ℂ) * pk (y / m) ((c : ℂ) + (v : ℂ) * I)

theorem norm_pk_le {z c v : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    ‖pk z ((c : ℂ) + (v : ℂ) * I)‖ ≤ z ^ c / c := by
  unfold pk
  rw [norm_div]
  have hs : c ≤ ‖(c : ℂ) + (v : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + (v : ℂ) * I)
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    rwa [hre, abs_of_pos hc] at this
  have hnum : ‖(z : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)‖ ≤ z ^ c := by
    rcases hz.lt_or_eq with hz0 | rfl
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hz0]
      simp
    · rw [Complex.ofReal_zero, Complex.zero_cpow (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)]
      simp [Real.zero_rpow hc.ne']
  have hc' : 0 < ‖(c : ℂ) + (v : ℂ) * I‖ := lt_of_lt_of_le hc hs
  calc ‖(z : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)‖ / ‖(c : ℂ) + (v : ℂ) * I‖
      ≤ z ^ c / ‖(c : ℂ) + (v : ℂ) * I‖ := by gcongr
    _ ≤ z ^ c / c := by
      apply div_le_div_of_nonneg_left (by positivity) hc hs

/-- The series of `psiTerm` sums to `L(Λ, s) · y^s / s` on `Re s = c > 1`. -/
theorem hasSum_psiTerm {y c : ℝ} (hy : 0 < y) (hc : 1 < c) (v : ℝ) :
    HasSum (fun m => psiTerm y c m v)
      (LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
  set s : ℂ := (c : ℂ) + (v : ℂ) * I with hs
  have hre : 1 < s.re := by simp [hs, hc]
  have hsum := (LSeriesSummable_vonMangoldt hre).hasSum
  have h := hsum.mul_right (pk y s)
  have hfun : (fun m => psiTerm y c m v)
      = fun m => LSeries.term (fun n => (Λ n : ℂ)) s m * pk y s := by
    funext m
    unfold psiTerm
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [LSeries.term_of_ne_zero hm.ne']
      unfold pk
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      rw [ofReal_div_cpow hy hm' s]
      push_cast
      ring
  rw [hfun]
  exact h

theorem continuous_pk_line {z c : ℝ} (hc : 0 < c) :
    Continuous fun v : ℝ => pk z ((c : ℂ) + (v : ℂ) * I) := by
  have hne : ∀ v : ℝ, (c : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro v h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous fun v : ℝ => (c : ℂ) + (v : ℂ) * I := by fun_prop
  unfold pk
  exact (hcont.const_cpow (Or.inr hne)).div hcont hne

/-- The dominating series: `Λ(m) (y/m)^c / c` is summable for `c > 1`. -/
theorem summable_psiBound {y c : ℝ} (hy : 0 < y) (hc : 1 < c) :
    Summable fun m : ℕ => Λ m * ((y / m) ^ c / c) := by
  have hre : 1 < ((c : ℂ)).re := by simp [hc]
  have hs := (LSeriesSummable_vonMangoldt hre).norm
  have hfun : (fun m : ℕ => Λ m * ((y / m) ^ c / c))
      = fun m => (y ^ c / c) * ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) m‖ := by
    funext m
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg hm.ne']
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      rw [Real.div_rpow hy.le hm'.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      simp only [Complex.ofReal_re]
      field_simp
  rw [hfun]
  exact hs.mul_left _

/-- **N4a — truncated Perron for `ψ`, decay branch.** -/
theorem perron_psi {y c T : ℝ} (hy : 1 < y) (hyn : ∀ m : ℕ, (m : ℝ) ≠ y) (hc : 1 < c)
    (hT : 0 < T) :
    ‖I * (∫ v in (-T)..T,
        LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I))
      - 2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)‖
      ≤ ∑' m : ℕ, Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  -- A: the integral of the series is the series of integrals
  have hA : HasSum (fun m => ∫ v in (-T)..T, psiTerm y c m v)
      (∫ v in (-T)..T,
        LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => Λ m * ((y / m) ^ c / c)) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact (continuous_const.mul (continuous_pk_line hc0)).aestronglyMeasurable
    · intro m
      refine Filter.Eventually.of_forall fun v _ => ?_
      unfold psiTerm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (norm_pk_le (by positivity) hc0) vonMangoldt_nonneg
    · exact Filter.Eventually.of_forall fun v _ => summable_psiBound hy0 hc
    · exact _root_.intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun v _ => hasSum_psiTerm hy0 hc v
  -- B: each integral is `Λ(m)` times a Perron contour
  have hB : ∀ m, I * ∫ v in (-T)..T, psiTerm y c m v = (Λ m : ℂ) * perronContour (y / m) c T := by
    intro m
    unfold psiTerm perronContour
    rw [intervalIntegral.integral_const_mul]
    ring
  have hC : HasSum (fun m => (Λ m : ℂ) * perronContour (y / m) c T)
      (I * ∫ v in (-T)..T,
        LSeries (fun n => (Λ n : ℂ)) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
    have := hA.mul_left I
    simp only [hB] at this
    exact this
  -- D: the indicator sum is `2πi ψ(y)`
  have hD : HasSum (fun m : ℕ => (Λ m : ℂ) * (2 * (Real.pi : ℂ) * I
      * (if 1 < y / m then (1 : ℂ) else 0)))
      (2 * (Real.pi : ℂ) * I * (Chebyshev.psi y : ℂ)) := by
    have hfin : HasSum (fun m : ℕ => (Λ m : ℂ) * (2 * (Real.pi : ℂ) * I
        * (if 1 < y / m then (1 : ℂ) else 0)))
        (∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, (Λ m : ℂ) * (2 * (Real.pi : ℂ) * I
          * (if 1 < y / m then (1 : ℂ) else 0))) := hasSum_sum_of_ne_finset_zero (by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · have hmy : ⌊y⌋₊ < m := by
          by_contra h
          exact hm (Finset.mem_Ioc.mpr ⟨hm0, not_lt.mp h⟩)
        have hym : y < m := by
          have := Nat.lt_floor_add_one y
          have : (⌊y⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hmy
          linarith
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
        have : ¬ (1 < y / m) := by
          rw [one_lt_div hm']; linarith
        simp [this])
    convert hfin using 1
    unfold Chebyshev.psi
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm0, hmf⟩ := Finset.mem_Ioc.mp hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hmy : (m : ℝ) < y := by
      have hle : (m : ℝ) ≤ y := (Nat.le_floor_iff hy0.le).mp hmf
      exact lt_of_le_of_ne hle (hyn m)
    have : 1 < y / m := by rw [one_lt_div hm']; exact hmy
    simp [this]
    ring
  -- E: subtract and bound termwise
  have hE := hC.sub hD
  have hbound : ∀ m : ℕ, ‖(Λ m : ℂ) * perronContour (y / m) c T
      - (Λ m : ℂ) * (2 * (Real.pi : ℂ) * I * (if 1 < y / m then (1 : ℂ) else 0))‖
      ≤ Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
    intro m
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      have hym : y / m ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hm'.ne'] at h
        exact hyn m h.symm
      exact mul_le_mul_of_nonneg_left
        (perron_trunc (by positivity) hym hc0 hT) vonMangoldt_nonneg
  have hgs : Summable fun m : ℕ => Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_psiBound hy0 hc).mul_left (2 * c / (T * Real.log 2))) ?_
    have hev : ∀ᶠ m : ℕ in Filter.atTop, 2 * y ≤ m :=
      Filter.eventually_ge_atTop ⌈2 * y⌉₊ |>.mono fun m hm => by
        have := Nat.le_ceil (2 * y)
        have : (⌈2 * y⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
        linarith
    refine hev.mono fun m hm => ?_
    have hm' : (0 : ℝ) < m := by linarith
    have hlog : Real.log 2 ≤ |Real.log (y / m)| := by
      have hlt : y / m ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hm' (by norm_num)]; linarith
      have hpos : 0 < y / m := by positivity
      have hneg : Real.log (y / m) ≤ -Real.log 2 := by
        have := Real.log_le_log hpos hlt
        rwa [one_div, Real.log_inv] at this
      rw [abs_of_neg (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])]
      linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity))]
    have hz : 0 ≤ (y / m) ^ c := by positivity
    have key : (y / m) ^ c / (T * |Real.log (y / m)|) ≤ (y / m) ^ c / (T * Real.log 2) :=
      div_le_div_of_nonneg_left hz (by positivity) (mul_le_mul_of_nonneg_left hlog hT.le)
    have e : 2 * c / (T * Real.log 2) * (Λ m * ((y / m) ^ c / c))
        = Λ m * (2 * ((y / m) ^ c / (T * Real.log 2))) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg
  exact hE.norm_le_of_bounded hgs.hasSum hbound

end Salt.RH
