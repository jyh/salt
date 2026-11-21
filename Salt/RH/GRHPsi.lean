/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.GRHLogDeriv
import Salt.RH.GRHPerron
import Salt.RH.VonKochFinal

/-!
# O106 row R5b, nodes M5, M6, M7 — `ψ(x, χ) ≪ √x log³(qx)` under GRH

For `χ ≠ 1` mod `q`, `L(·, χ)` is entire, and under `GRHDirichlet` it has no zero on `Re s > 1/2`,
so `g(s) := −logDeriv L(·, χ)(s) · y^s / s` is holomorphic on every closed rectangle in
`Re s > 1/2`, and its boundary integral is `0` (Goursat; there is no residue, unlike N5).

* **M5** `rectBI_gChi_eq_zero` — the rectangle identity.
* **M6** `gChi_left_edge_le`, `gChi_horiz_edge_le` — the three other edges, from M3.
* **M7** `psiTwist_le_of_GRH` — `GRHDirichlet → ∃ C, ∀ q, ∀ χ ≠ 1 mod q, ∀ x ≥ 2,
  ‖ψ(x, χ)‖ ≤ C √x (log(qx))³`, with `C` absolute.

`GRHDirichlet` is carried as a NAMED HYPOTHESIS (the O106 exception).
-/

namespace Salt.RH

open Complex Salt.SW Salt.MR ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-- The contour integrand `−logDeriv L(·, χ)(s) · y^s / s`. -/
noncomputable def gChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (LFunction χ) s * pk y s

theorem differentiableAt_logDeriv_LFunction {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (logDeriv (LFunction χ)) s := by
  have han : AnalyticAt ℂ (LFunction χ) s := (differentiable_LFunction hχ).analyticAt s
  have hd : DifferentiableAt ℂ (deriv (LFunction χ)) s := han.deriv.differentiableAt
  have : logDeriv (LFunction χ) = fun z => deriv (LFunction χ) z / LFunction χ z := by
    funext z; rw [logDeriv_apply]
  rw [this]
  exact hd.div (differentiable_LFunction hχ s) hs

theorem differentiableAt_gChi (hGRH : GRHDirichlet) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ} (hy : 0 < y) {s : ℂ}
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (gChi χ y) s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hZ := differentiableAt_logDeriv_LFunction hχ (LFunction_ne_zero_of_half_lt hGRH hχ hs)
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (y : ℂ) ^ z) s :=
    (differentiableAt_id.const_cpow (Or.inl hy0))
  have hpk : DifferentiableAt ℂ (pk y) s := by
    unfold pk
    exact hpow.div differentiableAt_id hs0
  unfold gChi
  exact hZ.neg.mul hpk

/-- **M5.** Under GRH, for `1/2 < σ₀ ≤ c₀`, the boundary integral of `gChi` over
`[σ₀, c₀] × [−T, T]` vanishes. -/
theorem rectBI_gChi_eq_zero (hGRH : GRHDirichlet) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y σ₀ c₀ T : ℝ} (hy : 0 < y)
    (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ c₀) :
    rectBI ((σ₀ : ℂ) - (T : ℂ) * I) ((c₀ : ℂ) + (T : ℂ) * I) (gChi χ y) = 0 := by
  refine rectBI_eq_zero_of_differentiableOn fun s hs => ?_
  have hre : s.re ∈ Set.uIcc σ₀ c₀ := by
    have := (Complex.mem_reProdIm.mp hs).1
    simpa using this
  have hre' : σ₀ ≤ s.re := by
    rw [Set.uIcc_of_le h01] at hre; exact hre.1
  exact (differentiableAt_gChi hGRH hχ hy (by linarith)).differentiableWithinAt

/-- On `Re s > 1`, `gChi` is the Perron integrand of `perron_psiTwist`. -/
theorem gChi_eq_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) {s : ℂ}
    (hs : 1 < s.re) : gChi χ y s = LSeries (↗χ * ↗Λ) s * pk y s := by
  rw [gChi, LSeries_twist_vonMangoldt_eq_neg_logDeriv χ hs]

/-! ## M6 — the three other edges -/

/-- The pointwise edge bound, from M3's constant `K`. -/
theorem norm_gChi_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {K y : ℝ}
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv (LFunction χ) s‖ ≤ K * Real.log (q * (|s.im| + 3)) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 0 < y) {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re ≤ 23 / 10) :
    ‖gChi χ y s‖
      ≤ K * Real.log (q * (|s.im| + 3)) * (1 + 1 / (s.re - 1 / 2)) * (y ^ s.re / ‖s‖) := by
  rw [gChi, norm_mul, norm_neg, norm_pk_eq hy]
  exact mul_le_mul_of_nonneg_right (hK s h1 h2) (by positivity)

/-- **M6, the left edge.** For `1/2 < σ₀ ≤ 3/4`, `T ≥ 0`:
`‖∫_{−T}^{T} g(σ₀ + iv) dv‖ ≤ A · y^{σ₀} · 8 log(1 + T)`,
`A = K log(q(T + 3))(1 + 1/(σ₀ − 1/2))`. -/
theorem gChi_left_edge_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {K y σ₀ T : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv (LFunction χ) s‖ ≤ K * Real.log (q * (|s.im| + 3)) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 0 < y) (h0 : 1 / 2 < σ₀) (h1 : σ₀ ≤ 3 / 4) (hT : 0 ≤ T) :
    ‖∫ v in (-T)..T, gChi χ y ((σ₀ : ℂ) + (v : ℂ) * I)‖
      ≤ K * Real.log (q * (T + 3)) * (1 + 1 / (σ₀ - 1 / 2)) * y ^ σ₀
        * (8 * Real.log (1 + T)) := by
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  set A : ℝ := K * Real.log (q * (T + 3)) * (1 + 1 / (σ₀ - 1 / 2)) with hA
  have hd0 : 0 < σ₀ - 1 / 2 := by linarith
  have hlogT : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hA0 : 0 ≤ A := by positivity
  have hbound : ∀ v : ℝ, v ∈ Set.Ioc (-T) T →
      ‖gChi χ y ((σ₀ : ℂ) + (v : ℂ) * I)‖ ≤ A * y ^ σ₀ * (4 * (1 / (1 + |v|))) := by
    intro v hv
    set s : ℂ := (σ₀ : ℂ) + (v : ℂ) * I with hs
    have hre : s.re = σ₀ := by simp [hs]
    have him : s.im = v := by simp [hs]
    have hpt := norm_gChi_le hK hy (s := s) (by rw [hre]; exact h0) (by rw [hre]; linarith)
    rw [hre, him] at hpt
    have hvT : |v| ≤ T := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
    have hlog : Real.log (q * (|v| + 3)) ≤ Real.log (q * (T + 3)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hfac : K * Real.log (q * (|v| + 3)) * (1 + 1 / (σ₀ - 1 / 2)) ≤ A := by
      rw [hA]
      have : K * Real.log (q * (|v| + 3)) ≤ K * Real.log (q * (T + 3)) :=
        mul_le_mul_of_nonneg_left hlog hK0
      nlinarith [show (0 : ℝ) ≤ 1 + 1 / (σ₀ - 1 / 2) by positivity]
    have hsn : (1 + |v|) / 4 ≤ ‖s‖ := by
      have hr := Complex.abs_re_le_norm s
      have hi := Complex.abs_im_le_norm s
      rw [hre, abs_of_pos (by linarith)] at hr
      rw [him] at hi
      linarith
    have hsn0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) hsn
    have hinv : y ^ σ₀ / ‖s‖ ≤ y ^ σ₀ * (4 * (1 / (1 + |v|))) := by
      rw [div_le_iff₀ hsn0]
      have hy0 : 0 ≤ y ^ σ₀ := by positivity
      have : 1 ≤ 4 * (1 / (1 + |v|)) * ‖s‖ := by
        rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      nlinarith
    have hlogv : 0 ≤ Real.log (q * (|v| + 3)) := Real.log_nonneg (by nlinarith [abs_nonneg v])
    calc ‖gChi χ y s‖
        ≤ K * Real.log (q * (|v| + 3)) * (1 + 1 / (σ₀ - 1 / 2)) * (y ^ σ₀ / ‖s‖) := hpt
      _ ≤ A * (y ^ σ₀ * (4 * (1 / (1 + |v|)))) :=
          mul_le_mul hfac hinv (by positivity) hA0
      _ = A * y ^ σ₀ * (4 * (1 / (1 + |v|))) := by ring
  have hcont : Continuous fun v : ℝ => 1 / (1 + |v|) := by
    refine Continuous.div continuous_const (by fun_prop) fun v => ?_
    have := abs_nonneg v; linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (MeasureTheory.ae_of_all MeasureTheory.volume hbound)
    ((hcont.const_mul 4).const_mul (A * y ^ σ₀) |>.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_one_add_abs hT] at hle
  linarith

/-- **M6, a horizontal edge** at height `b` with `|b| ≥ 1`, over `[σ₀, c₀]` with
`1/2 < σ₀ ≤ c₀ ≤ 2` and `y ≥ 1`. -/
theorem gChi_horiz_edge_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {K y σ₀ c₀ b : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 23 / 10 →
      ‖logDeriv (LFunction χ) s‖ ≤ K * Real.log (q * (|s.im| + 3)) * (1 + 1 / (s.re - 1 / 2)))
    (hy : 1 ≤ y) (h0 : 1 / 2 < σ₀) (h01 : σ₀ ≤ c₀) (h1 : c₀ ≤ 2) (hb : 1 ≤ |b|) :
    ‖∫ x in σ₀..c₀, gChi χ y ((x : ℂ) + (b : ℂ) * I)‖
      ≤ K * Real.log (q * (|b| + 3)) * (1 + 1 / (σ₀ - 1 / 2)) * (y ^ c₀ / |b|) * (c₀ - σ₀) := by
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  set A : ℝ := K * Real.log (q * (|b| + 3)) * (1 + 1 / (σ₀ - 1 / 2)) with hA
  have hd0 : 0 < σ₀ - 1 / 2 := by linarith
  have hb0 : 0 < |b| := by linarith
  have hlb : 0 ≤ K * Real.log (q * (|b| + 3)) :=
    mul_nonneg hK0 (Real.log_nonneg (by nlinarith))
  have hpt : ∀ x ∈ Set.uIoc σ₀ c₀,
      ‖gChi χ y ((x : ℂ) + (b : ℂ) * I)‖ ≤ A * (y ^ c₀ / |b|) := by
    intro x hx
    rw [Set.uIoc_of_le h01] at hx
    set s : ℂ := (x : ℂ) + (b : ℂ) * I with hs
    have hre : s.re = x := by simp [hs]
    have him : s.im = b := by simp [hs]
    have hx0 : 1 / 2 < x := by linarith [hx.1]
    have hpt0 := norm_gChi_le (y := y) hK (by linarith) (s := s) (by rw [hre]; exact hx0)
      (by rw [hre]; linarith [hx.2])
    rw [hre, him] at hpt0
    have hfac : K * Real.log (q * (|b| + 3)) * (1 + 1 / (x - 1 / 2)) ≤ A := by
      rw [hA]
      have h1' : 1 / (x - 1 / 2) ≤ 1 / (σ₀ - 1 / 2) :=
        one_div_le_one_div_of_le hd0 (by linarith [hx.1])
      nlinarith
    have hsn : |b| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s; rwa [him] at this
    have hyx : y ^ x ≤ y ^ c₀ := Real.rpow_le_rpow_of_exponent_le hy (by linarith [hx.2])
    have hq : y ^ x / ‖s‖ ≤ y ^ c₀ / |b| :=
      div_le_div₀ (by positivity) hyx hb0 hsn
    have hfac0 : 0 ≤ K * Real.log (q * (|b| + 3)) * (1 + 1 / (x - 1 / 2)) := by
      have : 0 < x - 1 / 2 := by linarith
      positivity
    calc _ ≤ K * Real.log (q * (|b| + 3)) * (1 + 1 / (x - 1 / 2)) * (y ^ x / ‖s‖) := hpt0
      _ ≤ A * (y ^ c₀ / |b|) := mul_le_mul hfac hq (by positivity) (le_trans hfac0 hfac)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (show (0 : ℝ) ≤ c₀ - σ₀ by linarith)] at this
  exact this

/-! ## M7 — the assembly -/

/-- The closing real arithmetic of M7a in the fine shape (`A = 6 K log(qy) log y`). -/
theorem final_arith_fine {e K Ly Lq s P B Q F : ℝ} (he : 0 < e) (hK : 0 ≤ K) (hLy : 4 ≤ Ly)
    (hLq : Ly ≤ Lq) (hs : 1 ≤ s) (hP : P ≤ 8 * e * (Ly + 760))
    (hB : B ≤ 6 * K * Lq * Ly * e) (hQ : Q ≤ 6 * K * Lq * Ly * e)
    (hF : F ≤ 6 * K * Lq * Ly * (s * e) * (8 * (3 * Ly))) :
    P + B + Q + F ≤ e * (6088 + 156 * K) * s * Lq * Ly ^ 2 := by
  have hLy1 : 1 ≤ Ly := by linarith
  have hLq1 : 1 ≤ Lq := by linarith
  have hX : Ly ≤ s * Lq * Ly ^ 2 := by
    have h1 : Ly ≤ Lq * Ly ^ 2 := by nlinarith
    have h2 : 0 ≤ Lq * Ly ^ 2 := by positivity
    nlinarith
  have hY : Lq * Ly ≤ s * Lq * Ly ^ 2 := by
    have h1 : Lq * Ly ≤ Lq * Ly ^ 2 := by
      have : Ly ≤ Ly ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have h2 : 0 ≤ Lq * Ly ^ 2 := by positivity
    nlinarith
  have e1 : P ≤ 6088 * e * (s * Lq * Ly ^ 2) := by
    have : Ly + 760 ≤ 761 * Ly := by linarith
    have h8 : 8 * e * (Ly + 760) ≤ 8 * e * (761 * Ly) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h9 : 8 * e * (761 * Ly) ≤ 8 * e * (761 * (s * Lq * Ly ^ 2)) := by gcongr
    linarith
  have e2 : B + Q ≤ 12 * K * e * (s * Lq * Ly ^ 2) := by
    have : 6 * K * Lq * Ly * e = 6 * K * e * (Lq * Ly) := by ring
    have h1 : 6 * K * e * (Lq * Ly) ≤ 6 * K * e * (s * Lq * Ly ^ 2) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    linarith
  have e3 : F ≤ 144 * K * e * (s * Lq * Ly ^ 2) := by
    have : 6 * K * Lq * Ly * (s * e) * (8 * (3 * Ly)) = 144 * K * e * (s * Lq * Ly ^ 2) := by ring
    linarith
  have : e * (6088 + 156 * K) * s * Lq * Ly ^ 2
      = 6088 * e * (s * Lq * Ly ^ 2) + 12 * K * e * (s * Lq * Ly ^ 2)
        + 144 * K * e * (s * Lq * Ly ^ 2) := by ring
  linarith

set_option maxHeartbeats 800000 in -- four edge integrals in one context, as in N7a
/-- **M7a, the fine shape.** Under GRH, at `y ≥ 55` at distance `≥ 1/2` from every integer, for
every `χ ≠ 1` mod `q`: `‖ψ(y, χ)‖ ≤ C √y log(qy) (log y)²`, with `C` absolute. -/
theorem psiTwist_le_halfint_fine (hGRH : GRHDirichlet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ y : ℝ, 55 ≤ y → (∀ m : ℕ, 1 / 2 ≤ |y - m|) →
        ‖psiTwist χ y‖ ≤ C * Real.sqrt y * Real.log (q * y) * Real.log y ^ 2 := by
  obtain ⟨K, hK0, hKall⟩ := LFunction_logDeriv_near_half hGRH
  set e : ℝ := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  refine ⟨e * (6088 + 156 * K) / (2 * Real.pi), by positivity,
    fun q _ χ hχ y hy hyn => ?_⟩
  have hK := hKall q χ hχ
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  set Ly : ℝ := Real.log y with hL
  have hL4 : 4 ≤ Ly := by
    rw [hL, Real.le_log_iff_exp_le hy0]; linarith [exp_four_lt]
  have hL0 : 0 < Ly := by linarith
  set Lq : ℝ := Real.log (q * y) with hLq
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hLqe : Lq = Real.log q + Ly := by
    rw [hLq, hL, Real.log_mul (by positivity) (by positivity)]
  have hLLq : Ly ≤ Lq := by rw [hLqe]; linarith
  have hLq4 : 4 ≤ Lq := by linarith
  set σ₀ : ℝ := 1 / 2 + 1 / Ly with hσ₀
  set c₀ : ℝ := 1 + 1 / Ly with hc₀
  set T : ℝ := y ^ 2 with hT
  have hiL : 1 / Ly ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hL4
  have hiL0 : 0 < 1 / Ly := by positivity
  have hσa : 1 / 2 < σ₀ := by linarith
  have hσb : σ₀ ≤ 3 / 4 := by linarith
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
  -- M5, unfolded
  have h5 := rectBI_gChi_eq_zero hGRH hχ (T := T) hy0 hσa hσc₀
  unfold rectBI at h5
  have hzr : ((σ₀ : ℂ) - (T : ℂ) * I).re = σ₀ := by simp
  have hzi : ((σ₀ : ℂ) - (T : ℂ) * I).im = -T := by simp
  have hwr : ((c₀ : ℂ) + (T : ℂ) * I).re = c₀ := by simp
  have hwi : ((c₀ : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [hzr, hzi, hwr, hwi] at h5
  set Bt := ∫ x : ℝ in σ₀..c₀, gChi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x : ℝ in σ₀..c₀, gChi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set R := ∫ v : ℝ in (-T)..T, gChi χ y ((c₀ : ℂ) + (v : ℂ) * I) with hR
  set Lf := ∫ v : ℝ in (-T)..T, gChi χ y ((σ₀ : ℂ) + (v : ℂ) * I) with hLf
  have h5' : Bt - Tp + I * R - I * Lf = 0 := h5
  -- the right edge is the Perron integral
  have hRP : R = ∫ v : ℝ in (-T)..T, LSeries (↗χ * ↗Λ) ((c₀ : ℂ) + (v : ℂ) * I)
      * pk y ((c₀ : ℂ) + (v : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun v _ => ?_
    have hre : 1 < ((c₀ : ℂ) + (v : ℂ) * I).re := by
      rw [show ((c₀ : ℂ) + (v : ℂ) * I).re = c₀ by simp]; exact hca
    exact gChi_eq_perron χ y hre
  have hyn' : ∀ m : ℕ, (m : ℝ) ≠ y := by
    intro m h
    have := hyn m
    rw [h, sub_self, abs_zero] at this
    norm_num at this
  have hP := perron_psiTwist χ hy1 hyn' hca hT0
  rw [← hRP] at hP
  have hE := perron_psi_error_le hy1.le hyn hca hcb hT0
  have hc1 : 1 / (c₀ - 1) = Ly := by
    rw [show c₀ - 1 = 1 / Ly by rw [hc₀]; ring, one_div_one_div]
  rw [hc1, hyc] at hE
  -- the other edges
  have hLfb := gChi_left_edge_le hK0.le hK hy0 hσa hσb hT0.le
  have hBtb := gChi_horiz_edge_le (b := -T) hK0.le hK hy1.le hσa hσc₀ hcb
    (by rw [abs_neg, abs_of_pos hT0]; exact hT1)
  have hTpb := gChi_horiz_edge_le (b := T) hK0.le hK hy1.le hσa hσc₀ hcb
    (by rw [abs_of_pos hT0]; exact hT1)
  rw [abs_neg, abs_of_pos hT0] at hBtb
  rw [abs_of_pos hT0] at hTpb
  have hσLy : 1 / (σ₀ - 1 / 2) = Ly := by
    rw [show σ₀ - 1 / 2 = 1 / Ly by rw [hσ₀]; ring, one_div_one_div]
  rw [hσLy, hys] at hLfb
  rw [hσLy, hyc] at hBtb hTpb
  -- the triangle inequality
  have hkey : (2 * (Real.pi : ℂ) * I) * psiTwist χ y
      = -(I * R - 2 * (Real.pi : ℂ) * I * psiTwist χ y) - Bt + Tp + I * Lf := by
    linear_combination h5'
  have hnorm : 2 * Real.pi * ‖psiTwist χ y‖
      ≤ ‖I * R - 2 * (Real.pi : ℂ) * I * psiTwist χ y‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
    have h1 : ‖(2 * (Real.pi : ℂ) * I) * psiTwist χ y‖ = 2 * Real.pi * ‖psiTwist χ y‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have htri : ∀ a b c d : ℂ, ‖-a - b + c + I * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      intro a b c d
      have h4 := norm_add_le (-a - b + c) (I * d)
      have h5 := norm_add_le (-a - b) c
      have h6 := norm_sub_le (-a) b
      rw [norm_neg] at h6
      rw [norm_mul, Complex.norm_I, one_mul] at h4
      linarith
    have h7 := htri (I * R - 2 * (Real.pi : ℂ) * I * psiTwist χ y) Bt Tp Lf
    rw [← hkey, h1] at h7
    exact h7
  -- sizes
  have hA : K * Real.log (q * (T + 3)) * (1 + Ly) ≤ 6 * K * Lq * Ly := by
    have hT3 : T + 3 ≤ y ^ 3 := by rw [hT]; nlinarith
    have hlog : Real.log (q * (T + 3)) ≤ 3 * Lq := by
      have h1 : Real.log (q * (T + 3)) ≤ Real.log (q * y ^ 3) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (x := (q : ℝ)) (y := y ^ 3) (by positivity) (by positivity),
        Real.log_pow] at h1
      rw [hLqe]; push_cast at h1; nlinarith
    have h1L : 1 + Ly ≤ 2 * Ly := by linarith
    have hlog0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
    have h3 : Real.log (q * (T + 3)) * (1 + Ly) ≤ 3 * Lq * (2 * Ly) :=
      mul_le_mul hlog h1L (by linarith) (by linarith)
    have h4 : K * Real.log (q * (T + 3)) * (1 + Ly) ≤ K * (3 * Lq * (2 * Ly)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hK0.le
    have h5 : K * (3 * Lq * (2 * Ly)) = 6 * K * Lq * Ly := by ring
    linarith
  have hlog1T : Real.log (1 + T) ≤ 3 * Ly := by
    have h : 1 + T ≤ y ^ 3 := by rw [hT]; nlinarith
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  set A : ℝ := 6 * K * Lq * Ly with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hAA : K * Real.log (q * (T + 3)) * (1 + Ly) ≤ A := hA
  have hcs : c₀ - σ₀ = 1 / 2 := by rw [hc₀, hσ₀]; ring
  have hE' : ‖I * R - 2 * (Real.pi : ℂ) * I * psiTwist χ y‖ ≤ 8 * e * (Ly + 760) := by
    have h1 := le_trans hP hE
    have hq : 8 * y * (y * e) / T = 8 * e := by rw [hT]; field_simp
    rw [hq] at h1
    have hl2 : Real.log 2 < 7 / 10 := by
      have := Real.log_two_lt_d9; linarith
    have : 8 * e * (Ly + 1080 * Real.log 2) ≤ 8 * e * (Ly + 760) := by
      have : Ly + 1080 * Real.log 2 ≤ Ly + 760 := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hBt' : ‖Bt‖ ≤ A * e := by
    have hq : y * e / T * (c₀ - σ₀) ≤ e := by
      rw [hcs, hT, show y * e / y ^ 2 * (1 / 2) = e / (2 * y) by field_simp]
      exact div_le_self he0.le (by linarith)
    have hBt0 : 0 ≤ K * Real.log (q * (T + 3)) * (1 + Ly) := by
      have : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
      positivity
    calc ‖Bt‖ ≤ K * Real.log (q * (T + 3)) * (1 + Ly) * (y * e / T) * (c₀ - σ₀) := hBtb
      _ = K * Real.log (q * (T + 3)) * (1 + Ly) * (y * e / T * (c₀ - σ₀)) := by ring
      _ ≤ A * e := mul_le_mul hAA hq (by have := hσc₀; positivity) hA0
  have hTp' : ‖Tp‖ ≤ A * e := by
    have hq : y * e / T * (c₀ - σ₀) ≤ e := by
      rw [hcs, hT, show y * e / y ^ 2 * (1 / 2) = e / (2 * y) by field_simp]
      exact div_le_self he0.le (by linarith)
    calc ‖Tp‖ ≤ K * Real.log (q * (T + 3)) * (1 + Ly) * (y * e / T) * (c₀ - σ₀) := hTpb
      _ = K * Real.log (q * (T + 3)) * (1 + Ly) * (y * e / T * (c₀ - σ₀)) := by ring
      _ ≤ A * e := mul_le_mul hAA hq (by have := hσc₀; positivity) hA0
  have hLf' : ‖Lf‖ ≤ A * (Real.sqrt y * e) * (8 * (3 * Ly)) := by
    calc ‖Lf‖ ≤ K * Real.log (q * (T + 3)) * (1 + Ly) * (Real.sqrt y * e)
          * (8 * Real.log (1 + T)) := hLfb
      _ ≤ A * (Real.sqrt y * e) * (8 * (3 * Ly)) := by
          have h0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
          gcongr
  -- assemble
  have htot : 2 * Real.pi * ‖psiTwist χ y‖
      ≤ e * (6088 + 156 * K) * Real.sqrt y * Lq * Ly ^ 2 :=
    le_trans hnorm (final_arith_fine he0 hK0.le hL4 hLLq hsq1 hE' hBt' hTp' hLf')
  calc ‖psiTwist χ y‖
      = 2 * Real.pi * ‖psiTwist χ y‖ / (2 * Real.pi) := by field_simp
    _ ≤ e * (6088 + 156 * K) * Real.sqrt y * Lq * Ly ^ 2 / (2 * Real.pi) := by
        gcongr
    _ = e * (6088 + 156 * K) / (2 * Real.pi) * Real.sqrt y * Lq * Ly ^ 2 := by ring


/-- **M7a.** Under GRH, at `y ≥ 55` at distance `≥ 1/2` from every integer, for every `χ ≠ 1`
mod `q`: `‖ψ(y, χ)‖ ≤ C √y (log(qy))³`, with `C` absolute (from the fine shape). -/
theorem psiTwist_le_halfint (hGRH : GRHDirichlet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ y : ℝ, 55 ≤ y → (∀ m : ℕ, 1 / 2 ≤ |y - m|) →
        ‖psiTwist χ y‖ ≤ C * Real.sqrt y * Real.log (q * y) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := psiTwist_le_halfint_fine hGRH
  refine ⟨C, hC0, fun q _ χ hχ y hy hyn => le_trans (hC q χ hχ y hy hyn) ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hy0 : 0 < y := by linarith
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hly : Real.log y ≤ Real.log (q * y) := Real.log_le_log hy0 (by nlinarith)
  have hl2 : Real.log y ^ 2 ≤ Real.log (q * y) ^ 2 := pow_le_pow_left₀ hly0 hly 2
  have hlq0 : 0 ≤ Real.log (q * y) := le_trans hly0 hly
  have : Real.log (q * y) * Real.log y ^ 2 ≤ Real.log (q * y) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hl2 hlq0
    nlinarith
  have hCs : 0 ≤ C * Real.sqrt y := by positivity
  calc C * Real.sqrt y * Real.log (q * y) * Real.log y ^ 2
      = C * Real.sqrt y * (Real.log (q * y) * Real.log y ^ 2) := by ring
    _ ≤ C * Real.sqrt y * Real.log (q * y) ^ 3 := mul_le_mul_of_nonneg_left this hCs

/-- **M7, the fine shape.** `GRHDirichlet → ‖ψ(x, χ)‖ ≤ C √x log(qx) (log x)²` for every `χ ≠ 1`
mod `q` and every `x ≥ 2`, with `C` absolute. -/
theorem psiTwist_le_fine_of_GRH (hGRH : GRHDirichlet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 2 ≤ x →
        ‖psiTwist χ x‖ ≤ C * Real.sqrt x * Real.log (q * x) * Real.log x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := psiTwist_le_halfint_fine hGRH
  refine ⟨max (16 * C) 700, le_trans (by norm_num) (le_max_right _ _),
    fun q _ χ hχ x hx => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hx0 : 0 < x := by linarith
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hqx : x ≤ q * x := by nlinarith
  have hlqx : Real.log x ≤ Real.log (q * x) := Real.log_le_log hx0 hqx
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hM : 16 * C ≤ max (16 * C) 700 := le_max_left _ _
  have hM' : (700 : ℝ) ≤ max (16 * C) 700 := le_max_right _ _
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
    have hpsi : psiTwist χ x = psiTwist χ y := by
      rw [psiTwist_eq_floor χ x, psiTwist_eq_floor χ y, hfl]
    have hmain := hC q χ hχ y hy55 (fun m => half_int_dist n m)
    have hsy : Real.sqrt y ≤ 2 * Real.sqrt x := by
      have : Real.sqrt y ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at this
      exact this
    have hly : Real.log (q * y) ≤ 2 * Real.log (q * x) := by
      have h : q * y ≤ (q * x) ^ 2 := by nlinarith
      have := Real.log_le_log (by positivity) h
      rwa [Real.log_pow] at this
    have hly0 : 0 ≤ Real.log (q * y) := Real.log_nonneg (by nlinarith)
    have hlyy : Real.log y ≤ 2 * Real.log x := by
      have h : y ≤ x ^ 2 := by nlinarith
      have := Real.log_le_log (by linarith) h
      rwa [Real.log_pow] at this
    have hlyy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hly2 : Real.log y ^ 2 ≤ 4 * Real.log x ^ 2 := by
      have := pow_le_pow_left₀ hlyy0 hlyy 2
      nlinarith
    have hlx1 : 0 ≤ Real.log (q * x) := by linarith
    have hprod : Real.log (q * y) * Real.log y ^ 2
        ≤ (2 * Real.log (q * x)) * (4 * Real.log x ^ 2) :=
      mul_le_mul hly hly2 (by positivity) (by positivity)
    have hbig : C * Real.sqrt y * Real.log (q * y) * Real.log y ^ 2
        ≤ 16 * C * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2)) := by
      have h1 : Real.sqrt y * (Real.log (q * y) * Real.log y ^ 2)
          ≤ (2 * Real.sqrt x) * ((2 * Real.log (q * x)) * (4 * Real.log x ^ 2)) :=
        mul_le_mul hsy hprod (by positivity) (by positivity)
      have e1 : C * Real.sqrt y * Real.log (q * y) * Real.log y ^ 2
          = C * (Real.sqrt y * (Real.log (q * y) * Real.log y ^ 2)) := by ring
      have e2 : 16 * C * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2))
          = C * ((2 * Real.sqrt x) * ((2 * Real.log (q * x)) * (4 * Real.log x ^ 2))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h1 hC0
    calc ‖psiTwist χ x‖ = ‖psiTwist χ y‖ := by rw [hpsi]
      _ ≤ 16 * C * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2)) := le_trans hmain hbig
      _ ≤ max (16 * C) 700 * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2)) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = max (16 * C) 700 * Real.sqrt x * Real.log (q * x) * Real.log x ^ 2 := by ring
  · replace hx56 : x < 56 := lt_of_not_ge hx56
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
    have hnorm : ‖psiTwist χ x‖ ≤ 280 := le_trans (norm_psiTwist_le χ x) (by linarith)
    have hsq2 : (1.41 : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; nlinarith
    have hl : Real.log 2 ≤ Real.log (q * x) :=
      le_trans (Real.log_le_log (by norm_num) hx) hlqx
    have hlx2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hlow : (2 / 5 : ℝ) ≤ Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2) := by
      have h2 : (0.6931471803 : ℝ) ^ 2 ≤ Real.log x ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have h3 : (0.6931471803 : ℝ) * 0.6931471803 ^ 2 ≤ Real.log (q * x) * Real.log x ^ 2 :=
        mul_le_mul (by linarith) h2 (by positivity) (by linarith)
      have : (1.41 : ℝ) * (0.6931471803 * 0.6931471803 ^ 2)
          ≤ Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2) :=
        mul_le_mul hsq2 h3 (by positivity) hsx.le
      have : (2 / 5 : ℝ) ≤ 1.41 * (0.6931471803 * 0.6931471803 ^ 2) := by norm_num
      linarith
    calc ‖psiTwist χ x‖ ≤ 280 := hnorm
      _ = 700 * (2 / 5) := by norm_num
      _ ≤ 700 * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2)) := by gcongr
      _ ≤ max (16 * C) 700 * (Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2)) :=
          mul_le_mul_of_nonneg_right hM' (by positivity)
      _ = max (16 * C) 700 * Real.sqrt x * Real.log (q * x) * Real.log x ^ 2 := by ring

/-- **M7.** `GRHDirichlet → ‖ψ(x, χ)‖ ≤ C √x (log(qx))³` for every `χ ≠ 1` mod `q` and every
`x ≥ 2`, with `C` absolute (from the fine shape). -/
theorem psiTwist_le_of_GRH (hGRH : GRHDirichlet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ‖psiTwist χ x‖ ≤ C * Real.sqrt x * Real.log (q * x) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := psiTwist_le_fine_of_GRH hGRH
  refine ⟨C, hC0, fun q _ χ hχ x hx => le_trans (hC q χ hχ x hx) ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by
    have := NeZero.ne q
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlx : Real.log x ≤ Real.log (q * x) := Real.log_le_log hx0 (by nlinarith)
  have hl2 : Real.log x ^ 2 ≤ Real.log (q * x) ^ 2 := pow_le_pow_left₀ hlx0 hlx 2
  have hlq0 : 0 ≤ Real.log (q * x) := le_trans hlx0 hlx
  have : Real.log (q * x) * Real.log x ^ 2 ≤ Real.log (q * x) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hl2 hlq0
    nlinarith
  have hCs : 0 ≤ C * Real.sqrt x := by positivity
  calc C * Real.sqrt x * Real.log (q * x) * Real.log x ^ 2
      = C * Real.sqrt x * (Real.log (q * x) * Real.log x ^ 2) := by ring
    _ ≤ C * Real.sqrt x * Real.log (q * x) ^ 3 := mul_le_mul_of_nonneg_left this hCs

end Salt.RH
