/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.PerronPsi

/-!
# O106 row R5b, node M4 — truncated Perron for the twisted `ψ(y, χ)`

For a Dirichlet character `χ` mod `q`, `y > 1` not an integer, `c > 1` and `T > 0`,

`‖I ∫_{-T}^{T} L(χΛ, c+iv) y^{c+iv}/(c+iv) dv − 2πi ψ(y, χ)‖`
`≤ ∑' m, Λ(m) · 2 (y/m)^c / (T |log(y/m)|)`,

where `ψ(y, χ) = ∑_{m ≤ y} χ(m) Λ(m)`. The right side is the untwisted error of `perron_psi`, which
`perron_psi_error_le` already bounds: `|χ| ≤ 1` costs nothing. The proof is `perron_psi`'s with the
coefficient `χ(m) Λ(m)` in place of `Λ(m)`.
-/

namespace Salt.RH

open Complex MeasureTheory intervalIntegral Salt.MR ArithmeticFunction
open scoped LSeries.notation

/-- The twisted Chebyshev function `ψ(y, χ) = ∑_{m ≤ y} χ(m) Λ(m)`. -/
noncomputable def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, χ (m : ZMod q) * (Λ m : ℂ)

theorem psiChi_eq_floor {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    psiChi χ y = psiChi χ (⌊y⌋₊ : ℝ) := by
  unfold psiChi
  rw [Nat.floor_natCast]

/-- `‖ψ(y, χ)‖ ≤ ψ(y)`. -/
theorem norm_psiChi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    ‖psiChi χ y‖ ≤ Chebyshev.psi y := by
  unfold psiChi Chebyshev.psi
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

/-- The `m`-th term of the twisted series under the integral. -/
noncomputable def psiTermChi {q : ℕ} (χ : DirichletCharacter ℂ q) (y c : ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  χ (m : ZMod q) * (Λ m : ℂ) * pk (y / m) ((c : ℂ) + (v : ℂ) * I)

theorem norm_twist_le {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖χ (m : ZMod q) * (Λ m : ℂ)‖ ≤ Λ m := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

theorem hasSum_psiTermChi {q : ℕ} (χ : DirichletCharacter ℂ q) {y c : ℝ} (hy : 0 < y)
    (hc : 1 < c) (v : ℝ) :
    HasSum (fun m => psiTermChi χ y c m v)
      (LSeries (↗χ * ↗Λ) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
  set s : ℂ := (c : ℂ) + (v : ℂ) * I with hs
  have hre : 1 < s.re := by simp [hs, hc]
  have hsum := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hre).hasSum
  have h := hsum.mul_right (pk y s)
  have hfun : (fun m => psiTermChi χ y c m v)
      = fun m => LSeries.term (↗χ * ↗Λ) s m * pk y s := by
    funext m
    unfold psiTermChi
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [LSeries.term_of_ne_zero hm.ne']
      unfold pk
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      rw [ofReal_div_cpow hy hm' s]
      simp only [Pi.mul_apply]
      push_cast
      ring
  rw [hfun]
  exact h

/-- The Perron error series is summable. -/
theorem summable_perronErr {y c T : ℝ} (hy0 : 0 < y) (hc : 1 < c) (hT : 0 < T) :
    Summable fun m : ℕ => Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
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
  have hc0 : 0 < c := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity))]
  have hz : 0 ≤ (y / m) ^ c := by positivity
  have key : (y / m) ^ c / (T * |Real.log (y / m)|) ≤ (y / m) ^ c / (T * Real.log 2) :=
    div_le_div_of_nonneg_left hz (by positivity) (mul_le_mul_of_nonneg_left hlog hT.le)
  have e : 2 * c / (T * Real.log 2) * (Λ m * ((y / m) ^ c / c))
      = Λ m * (2 * ((y / m) ^ c / (T * Real.log 2))) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg

/-- **M4 — truncated Perron for `ψ(y, χ)`, decay branch.** -/
theorem perron_psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) {y c T : ℝ} (hy : 1 < y)
    (hyn : ∀ m : ℕ, (m : ℝ) ≠ y) (hc : 1 < c) (hT : 0 < T) :
    ‖I * (∫ v in (-T)..T,
        LSeries (↗χ * ↗Λ) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I))
      - 2 * (Real.pi : ℂ) * I * psiChi χ y‖
      ≤ ∑' m : ℕ, Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  -- A: the integral of the series is the series of integrals
  have hA : HasSum (fun m => ∫ v in (-T)..T, psiTermChi χ y c m v)
      (∫ v in (-T)..T,
        LSeries (↗χ * ↗Λ) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => Λ m * ((y / m) ^ c / c)) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact (continuous_const.mul (continuous_pk_line hc0)).aestronglyMeasurable
    · intro m
      refine Filter.Eventually.of_forall fun v _ => ?_
      unfold psiTermChi
      rw [norm_mul]
      exact mul_le_mul (norm_twist_le χ m) (norm_pk_le (by positivity) hc0) (norm_nonneg _)
        vonMangoldt_nonneg
    · exact Filter.Eventually.of_forall fun v _ => summable_psiBound hy0 hc
    · exact _root_.intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun v _ => hasSum_psiTermChi χ hy0 hc v
  -- B: each integral is `χ(m)Λ(m)` times a Perron contour
  have hB : ∀ m, I * ∫ v in (-T)..T, psiTermChi χ y c m v
      = (χ (m : ZMod q) * (Λ m : ℂ)) * perronContour (y / m) c T := by
    intro m
    unfold psiTermChi perronContour
    rw [intervalIntegral.integral_const_mul]
    ring
  have hC : HasSum (fun m : ℕ => (χ (m : ZMod q) * (Λ m : ℂ)) * perronContour (y / m) c T)
      (I * ∫ v in (-T)..T,
        LSeries (↗χ * ↗Λ) ((c : ℂ) + (v : ℂ) * I) * pk y ((c : ℂ) + (v : ℂ) * I)) := by
    have := hA.mul_left I
    simp only [hB] at this
    exact this
  -- D: the indicator sum is `2πi ψ(y, χ)`
  have hD : HasSum (fun m : ℕ => (χ (m : ZMod q) * (Λ m : ℂ)) * (2 * (Real.pi : ℂ) * I
      * (if 1 < y / m then (1 : ℂ) else 0)))
      (2 * (Real.pi : ℂ) * I * psiChi χ y) := by
    have hfin : HasSum (fun m : ℕ => (χ (m : ZMod q) * (Λ m : ℂ)) * (2 * (Real.pi : ℂ) * I
        * (if 1 < y / m then (1 : ℂ) else 0)))
        (∑ m ∈ Finset.Ioc 0 ⌊y⌋₊, (χ (m : ZMod q) * (Λ m : ℂ)) * (2 * (Real.pi : ℂ) * I
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
    unfold psiChi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm0, hmf⟩ := Finset.mem_Ioc.mp hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hmy : (m : ℝ) < y := by
      have hle : (m : ℝ) ≤ y := (Nat.le_floor_iff hy0.le).mp hmf
      exact lt_of_le_of_ne hle (hyn m)
    have : 1 < y / m := by rw [one_lt_div hm']; exact hmy
    simp only [this, if_true]
    ring
  -- E: subtract and bound termwise
  have hE := hC.sub hD
  have hbound : ∀ m : ℕ, ‖(χ (m : ZMod q) * (Λ m : ℂ)) * perronContour (y / m) c T
      - (χ (m : ZMod q) * (Λ m : ℂ)) * (2 * (Real.pi : ℂ) * I
        * (if 1 < y / m then (1 : ℂ) else 0))‖
      ≤ Λ m * (2 * ((y / m) ^ c / (T * |Real.log (y / m)|))) := by
    intro m
    rw [← mul_sub, norm_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      have hym : y / m ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hm'.ne'] at h
        exact hyn m h.symm
      exact mul_le_mul (norm_twist_le χ m) (perron_trunc (by positivity) hym hc0 hT)
        (norm_nonneg _) vonMangoldt_nonneg
  exact hE.norm_le_of_bounded (summable_perronErr hy0 hc hT).hasSum hbound

/-- The bridge on `Re s > 1`: `L(χΛ, s) = −logDeriv L(·, χ) s`. -/
theorem LSeries_twist_vonMangoldt_eq_neg_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗χ * ↗Λ) s = -logDeriv (DirichletCharacter.LFunction χ) s := by
  rw [Salt.HB.logDeriv_LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, logDeriv_apply, neg_div]

end Salt.RH
