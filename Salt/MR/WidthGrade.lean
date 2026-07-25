/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HeadGrade
import Salt.MR.WindowBridge

/-!
# The width-decoupled Plancherel close (`WidthGrade`)

`HeadGrade` grades the `crossKer` head by a second moment whose Lorentzian **width** is tied
to the band half-length `T₀ := 2(X+h)/h`.  That tie is a convenience, not a constraint: the
Plancherel keystone `widthA_plancherel` and the whole sharp off-diagonal ladder
(`hband_discharge`, `offdiag_widthA_final`, `offdiag_widthA_final_low`) already carry the
width `a` as a FREE parameter.  Freeing it is worth a full power of `L`:

* the band domination pays `(A² + T₀²) ≤ 2T₀²` instead of `2T₀²` at width `T₀` — no loss;
* the Plancherel evaluation returns `π/A` instead of `π/T₀` — a gain of `T₀/A`;
* the off-diagonal decays like `1/A` instead of `1/T₀` — a further gain of `T₀/A`.

Net: the head's amplitude carries `T₀²/A²`, an ABSOLUTE constant once `A ≍ T₀`, where the
width-`T₀` grade carried `T₀ ≍ √L`.  The y-gate `2A⁸ ≤ n` — the only price — is true BY
CONSTRUCTION at the consumer's `A := (y/2)^{1/8}` (then `2A⁸ = y < n` on the window).

The tail is closed the same way (`tail_lorentz_grade`, the ONE new analytic stone): the
branch-2 Lorentzian `1/(cw²+τ²)` is dominated by `2/(A²+τ²)` on `|τ| > T₀ ≥ A`, so the tail
cross-integral is a FULL-LINE Lorentzian-weighted Cauchy–Schwarz (`mixed_weight_cs`) which
`widthA_plancherel` evaluates at width `A` — the tail's mass² collapses to the geometric mean
`√(Σ₋Σ₊)`, the `min¹` the σ-page needs, with the `T₀/A²` suppression on top.

## The stones

1. `band_second_moment_width` — the band moment at a width `A` decoupled from `T₀`.
2. `head_second_moment_grade_width` / `_low_width` — the two per-leg head grades at width `A`.
3. `tail_lorentz_grade` — the Plancherelized tail (the new analytic stone).
4. `crossKer_grade_width` — the τ-split composition at the free width.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## A-1 — the band second moment at a decoupled width (`band_second_moment_width`)

`band_second_moment` (HeadGrade) minorizes the width-`a` Lorentzian on the band `|τ| ≤ a`,
where the width and the band half-length are the SAME `a`.  Here they are independent: on
`|τ| ≤ T₀` the width-`A` Lorentzian obeys `1/(A²+τ²) ≥ 1/(A²+T₀²) ≥ 1/(2T₀²)` (using
`A ≤ T₀`), so the raw band moment is dominated by `2T₀²` times the FULL-LINE width-`A`
Lorentzian moment — which `widthA_plancherel` evaluates at `π/A`, not `π/T₀`. -/

/-- The Dirichlet polynomial `∑ bₙ/n^{c+iτ}` is continuous in `τ`.  Re-derivation of
`HeadGrade`'s private `continuous_dirichletPoly` (the whole content is the `cpow`
continuity at a nonvanishing base). -/
private lemma continuous_dirichletPolyW (F : Finset ℕ) (b : ℕ → ℂ) (c : ℝ)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    Continuous (fun τ : ℝ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)) := by
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn0 : n ≠ 0 := by have := hF n hn; omega
  have hbC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hne : ∀ τ : ℝ, (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro τ; rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, _⟩; exact hbC h0
  have hf : Continuous (fun τ : ℝ => (c : ℂ) + (τ : ℂ) * I) := by fun_prop
  simp_rw [div_eq_mul_inv]
  exact continuous_const.mul ((hf.const_cpow (Or.inl hbC)).inv₀ hne)

/-- **A-1 — the width-decoupled band second moment** (`band_second_moment_width`).  For a
finite window `F` of positive integers, any line `c`, a width `0 < A` and a band half-length
`T₀ ≥ A`, the raw second moment over `|τ| ≤ T₀` is dominated by `2T₀²` times the full-line
width-`A` Lorentzian-weighted moment.  The clone of `band_second_moment` with the Lorentzian
width freed from the band half-length. -/
theorem band_second_moment_width (F : Finset ℕ) (b : ℕ → ℂ) {c A T₀ : ℝ} (hA : 0 < A)
    (hAT : A ≤ T₀) (hF : ∀ n ∈ F, 1 ≤ n) :
    (∫ τ in Set.Icc (-T₀) T₀, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2)
      ≤ 2 * T₀ ^ 2 * ∫ τ : ℝ,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2) := by
  set P : ℝ → ℂ := fun τ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I) with hP
  set M : ℝ := ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c with hM
  have hT₀ : (0 : ℝ) < T₀ := lt_of_lt_of_le hA hAT
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => by positivity)
  have hcont : Continuous P := continuous_dirichletPolyW F b c hF
  have hnormle : ∀ τ : ℝ, ‖P τ‖ ≤ M := by
    intro τ
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun n hn => ?_)))
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
    have hre : ((c : ℂ) + (τ : ℂ) * I).re = c := by simp
    rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]
  have hLint : Integrable (fun τ : ℝ => ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) volume :=
      ((hcont.norm.pow 2).div (by fun_prop) (fun τ => by positivity)).aestronglyMeasurable
    refine ((Salt.SW.integrable_inv_c_sq_add_sq hA).const_mul (M ^ 2)).mono' hmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
    gcongr
    exact hnormle τ
  have hband : IntegrableOn (fun τ : ℝ => ‖P τ‖ ^ 2) (Set.Icc (-T₀) T₀) volume :=
    (hcont.norm.pow 2).integrableOn_Icc
  have hpt : ∀ τ ∈ Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2 ≤ 2 * T₀ ^ 2 * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by
    intro τ hτ
    rw [Set.mem_Icc] at hτ
    have hd : (0 : ℝ) < A ^ 2 + τ ^ 2 := by positivity
    have hτ2 : τ ^ 2 ≤ T₀ ^ 2 := by nlinarith [hτ.1, hτ.2]
    have hA2 : A ^ 2 ≤ T₀ ^ 2 := by nlinarith
    have hratio : (1 : ℝ) ≤ 2 * T₀ ^ 2 / (A ^ 2 + τ ^ 2) := by
      rw [le_div_iff₀ hd]; linarith
    calc ‖P τ‖ ^ 2 = ‖P τ‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P τ‖ ^ 2 * (2 * T₀ ^ 2 / (A ^ 2 + τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = 2 * T₀ ^ 2 * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by ring
  calc (∫ τ in Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2)
      ≤ ∫ τ in Set.Icc (-T₀) T₀, 2 * T₀ ^ 2 * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) :=
        setIntegral_mono_on hband ((hLint.const_mul (2 * T₀ ^ 2)).integrableOn)
          measurableSet_Icc hpt
    _ = 2 * T₀ ^ 2 * ∫ τ in Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2) :=
        integral_const_mul _ _
    _ ≤ 2 * T₀ ^ 2 * ∫ τ : ℝ, ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hLint (Filter.Eventually.of_forall (fun τ => by positivity)))
          (by positivity)

/-! ## A-2 — the per-leg head grades at the free width

Byte-faithful clones of `head_second_moment_grade` / `head_second_moment_grade_low`
(HeadGrade) with `band_second_moment_width` in place of `band_second_moment` and every
width-carrying stone instantiated at `A` rather than `T₀`.  **The off-diagonal ladder is pure
INSTANTIATION**: `hband_discharge`, `offdiag_widthA_final` and `offdiag_widthA_final_low`
already take the width as a free parameter `a` (only `4 ≤ a`, `c ≤ a` and the y-gate
`2a⁸ ≤ n` constrain it), so nothing below re-proves any of that page.

Exit (high leg): `∫_{|τ|≤T₀} ‖P‖²/√(cw²+τ²) ≤ (2π T₀²/(A·cw))·(diag + 4C/(A−c+1)·mass)`.
The `T₀²/A` prefactor against the `1/A` off-diagonal decay is `T₀²/A²` — ABSOLUTE at
`A ≍ T₀`, where the width-`T₀` grade of `HeadGrade` carried `T₀ ≍ √L`. -/

/-- **A-2 (high leg) — the width-decoupled head second moment** (`head_second_moment_grade_width`).
The `head_second_moment_grade` page at a Lorentzian width `A` free of the band half-length
`T₀`: for `1 ≤ c ≤ A`, `4 ≤ A ≤ T₀`, `Λ`-bounded coefficients and the y-gate `2A⁸ ≤ n`,

  `∫_{|τ|≤T₀} ‖P(c+iτ)‖²/√(cw²+τ²) ≤ (2π T₀²/(A cw))·(diagonal + 4C/(A−c+1)·mass)`,

`C` the absolute constant of `shortInterval_vonMangoldt_le`. -/
theorem head_second_moment_grade_width {F : Finset ℕ} {b : ℕ → ℂ} {c cw A T₀ : ℝ}
    (hc : 1 ≤ c) (hcw : 0 < cw) (hA4 : 4 ≤ A) (hAT : A ≤ T₀) (hcA : c ≤ A)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
        ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw)
            * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
              + 4 * Cb / (A - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le hA0 hAT
  obtain ⟨C, hC0, hoff⟩ := offdiag_widthA_final hc hcA hA4 hF hb hygate
  have hden_pos : ∀ τ : ℝ, (0 : ℝ) < cw ^ 2 + τ ^ 2 := fun τ => by
    have h := pow_pos hcw 2; linarith [sq_nonneg τ]
  have hPcont : Continuous (fun τ : ℝ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)) :=
    continuous_dirichletPolyW F b c hF
  have hcw_le_sqrt : ∀ τ : ℝ, cw ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    calc cw = Real.sqrt (cw ^ 2) := (Real.sqrt_sq hcw.le).symm
      _ ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg τ])
  have hIntW : IntegrableOn (fun τ : ℝ =>
      ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      (Set.Icc (-T₀) T₀) :=
    ((hPcont.norm.pow 2).div (Real.continuous_sqrt.comp (by fun_prop))
      (fun τ => (Real.sqrt_pos.mpr (hden_pos τ)).ne')).integrableOn_Icc
  have hIntQ : IntegrableOn (fun τ : ℝ =>
      cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2)
      (Set.Icc (-T₀) T₀) :=
    (continuous_const.mul (hPcont.norm.pow 2)).integrableOn_Icc
  have hstep1 : (∫ τ in Set.Icc (-T₀) T₀,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hIntW hIntQ measurableSet_Icc (fun τ _ => ?_)
    calc ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)
        ≤ ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / cw :=
          div_le_div_of_nonneg_left (by positivity) hcw (hcw_le_sqrt τ)
      _ = cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := div_eq_inv_mul _ _
  have hbsm := band_second_moment_width F b (c := c) hA0 hAT hF
  have hplanch := widthA_plancherel F b (c := c) hA0 hF
  have hRe_le_K : ∀ m n : ℕ,
      (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|))
        ≤ ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)) := by
    intro m n
    have hre : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * starRingEnd ℂ (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(A * |Real.log m - Real.log n|)) := by positivity
    calc (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|))
        = (b m * starRingEnd ℂ (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  have hper_m : ∀ m ∈ F,
      (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c
          + ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
    intro m hm
    have he1 : (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ∑ n ∈ F, ((if m = n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)
            + (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : m = n
      · rw [if_pos h, if_neg (by simp [h]), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    rw [he1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq F m (fun n => ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(A * |Real.log m - Real.log n|))), if_pos hm,
      sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, ← pow_two]
  have hKsplit : (∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
          + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
    rw [Finset.sum_congr rfl hper_m, Finset.sum_add_distrib]
  have hfinal_planch : (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
          + 4 * C / (A - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
    calc (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)))
        ≤ ∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)) :=
          Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hRe_le_K m n))
      _ = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
            + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
                * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := hKsplit
      _ ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / (A - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c :=
          add_le_add le_rfl hoff
  have hpref0 : (0 : ℝ) ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw) :=
    div_nonneg (by positivity) (by positivity)
  refine ⟨C, hC0, ?_⟩
  calc (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := hstep1
    _ ≤ cw⁻¹ * (2 * T₀ ^ 2 * ∫ τ : ℝ,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbsm (inv_nonneg.mpr hcw.le)
    _ = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / A
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)))) := by rw [hplanch]
    _ = 2 * Real.pi * T₀ ^ 2 / (A * cw)
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) := by
        rw [show (2 : ℝ) * Real.pi * T₀ ^ 2 / (A * cw)
              = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / A)) from by field_simp]
        ring
    _ ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw)
          * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / (A - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left hfinal_planch hpref0

/-- **A-2 (low leg) — the width-decoupled head second moment at a sub-unit line**
(`head_second_moment_grade_low_width`).  The `head_second_moment_grade_low` page at a
Lorentzian width `A` free of the band half-length `T₀`: for `0 < c ≤ 1`, `4 ≤ A ≤ T₀`,
`Λ`-bounded coefficients, the y-gate `2A⁸ ≤ n` and the window `n ≤ Q`,

  `∫_{|τ|≤T₀} ‖P(c+iτ)‖²/√(cw²+τ²) ≤ (2π T₀²/(A cw))·(diagonal + 4C/A·(Q^{1−c}·mass))`. -/
theorem head_second_moment_grade_low_width {F : Finset ℕ} {b : ℕ → ℂ} {c cw A T₀ Q : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hcw : 0 < cw) (hA4 : 4 ≤ A) (hAT : A ≤ T₀)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) (hQ : ∀ n ∈ F, (n : ℝ) ≤ Q) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
        ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw)
            * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
              + 4 * Cb / A * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le hA0 hAT
  have hcA : c ≤ A := by linarith
  obtain ⟨C, hC0, hoff⟩ := offdiag_widthA_final_low hc0 hc1 hcA hA4 hF hb hygate hQ
  have hden_pos : ∀ τ : ℝ, (0 : ℝ) < cw ^ 2 + τ ^ 2 := fun τ => by
    have h := pow_pos hcw 2; linarith [sq_nonneg τ]
  have hPcont : Continuous (fun τ : ℝ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)) :=
    continuous_dirichletPolyW F b c hF
  have hcw_le_sqrt : ∀ τ : ℝ, cw ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    calc cw = Real.sqrt (cw ^ 2) := (Real.sqrt_sq hcw.le).symm
      _ ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg τ])
  have hIntW : IntegrableOn (fun τ : ℝ =>
      ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      (Set.Icc (-T₀) T₀) :=
    ((hPcont.norm.pow 2).div (Real.continuous_sqrt.comp (by fun_prop))
      (fun τ => (Real.sqrt_pos.mpr (hden_pos τ)).ne')).integrableOn_Icc
  have hIntQ : IntegrableOn (fun τ : ℝ =>
      cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2)
      (Set.Icc (-T₀) T₀) :=
    (continuous_const.mul (hPcont.norm.pow 2)).integrableOn_Icc
  have hstep1 : (∫ τ in Set.Icc (-T₀) T₀,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hIntW hIntQ measurableSet_Icc (fun τ _ => ?_)
    calc ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)
        ≤ ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / cw :=
          div_le_div_of_nonneg_left (by positivity) hcw (hcw_le_sqrt τ)
      _ = cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := div_eq_inv_mul _ _
  have hbsm := band_second_moment_width F b (c := c) hA0 hAT hF
  have hplanch := widthA_plancherel F b (c := c) hA0 hF
  have hRe_le_K : ∀ m n : ℕ,
      (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|))
        ≤ ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)) := by
    intro m n
    have hre : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * starRingEnd ℂ (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(A * |Real.log m - Real.log n|)) := by positivity
    calc (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|))
        = (b m * starRingEnd ℂ (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  have hper_m : ∀ m ∈ F,
      (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c
          + ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
    intro m hm
    have he1 : (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ∑ n ∈ F, ((if m = n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)
            + (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : m = n
      · rw [if_pos h, if_neg (by simp [h]), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    rw [he1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq F m (fun n => ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(A * |Real.log m - Real.log n|))), if_pos hm,
      sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, ← pow_two]
  have hKsplit : (∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
          + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
    rw [Finset.sum_congr rfl hper_m, Finset.sum_add_distrib]
  have hfinal_planch : (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
          + 4 * C / A * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
    calc (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)))
        ≤ ∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)) :=
          Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hRe_le_K m n))
      _ = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
            + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
                * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := hKsplit
      _ ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / A * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
          add_le_add le_rfl hoff
  have hpref0 : (0 : ℝ) ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw) :=
    div_nonneg (by positivity) (by positivity)
  refine ⟨C, hC0, ?_⟩
  calc (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := hstep1
    _ ≤ cw⁻¹ * (2 * T₀ ^ 2 * ∫ τ : ℝ,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbsm (inv_nonneg.mpr hcw.le)
    _ = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / A
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)))) := by rw [hplanch]
    _ = 2 * Real.pi * T₀ ^ 2 / (A * cw)
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) := by
        rw [show (2 : ℝ) * Real.pi * T₀ ^ 2 / (A * cw)
              = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / A)) from by field_simp]
        ring
    _ ≤ 2 * Real.pi * T₀ ^ 2 / (A * cw)
          * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / A * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)) :=
        mul_le_mul_of_nonneg_left hfinal_planch hpref0

/-! ## A-3 — the Plancherelized tail (`tail_lorentz_core`, `tail_lorentz_grade`)

**The one new analytic stone.**  `tail_band_sum` (HeadGrade) closes the `crossKer` tail by the
CRUDE leg sups: `∫_{tail} ‖P₋‖‖P₊‖‖K‖ ≤ Mm·Mp·2(X+h)^{cw}` — the window mass SQUARED, i.e.
`min(L,1/σ)²`, and the σ-page must spend one `min` on an `L` to convert.  Here the tail is
Plancherelized instead, at the SAME free width `A` the head uses:

* branch-2 (`hatKernel_branch2`) gives `‖K τ‖ ≤ Bamp/(cw²+τ²)`, `Bamp = 2(X+h)^{cw+1}/h`;
* on the tail `|τ| > T₀ ≥ A` one has `A² < τ²`, hence `A²+τ² < 2τ² ≤ 2(cw²+τ²)`, so the
  branch-2 Lorentzian is dominated by the WIDTH-`A` Lorentzian: `1/(cw²+τ²) ≤ 2/(A²+τ²)`;
* the tail integral is therefore majorized by a FULL-LINE width-`A` Lorentzian-weighted
  cross-integral, which `mixed_weight_cs` (JointHead) splits into the geometric mean of the
  two legs' width-`A` second moments — the very integrals `widthA_plancherel` evaluates.

Exit: `tail ≤ 2·Bamp·√(∫‖P₋‖²/(A²+τ²))·√(∫‖P₊‖²/(A²+τ²))`.  The mass enters under a SQUARE
ROOT — `min¹`, not `min²` — and the amplitude `Bamp·(π/A)·(1/A) ≍ (X+h)^{cw}·T₀/A²` is
`√L`-SUPPRESSED at `A ≍ T₀ ≍ √L`. -/

/-- **A-3 core — the Plancherelized tail** (`tail_lorentz_core`).  For continuous legs
`Pm, Pp` with uniform sups, a kernel `K` that is `L¹` and obeys the branch-2 Lorentzian bound
`‖K τ‖ ≤ Bamp/(cw²+τ²)`, and a width `0 < A ≤ T₀`:

  `∫_{|τ|>T₀} ‖Pm‖‖Pp‖‖K‖ ≤ 2·Bamp·√(∫_ℝ ‖Pm‖²/(A²+τ²))·√(∫_ℝ ‖Pp‖²/(A²+τ²))`.

The Lorentzian domination `1/(cw²+τ²) ≤ 2/(A²+τ²)` holds on the tail (`A < |τ|`), the tail
integral is extended to the full line (nonneg integrand), and `mixed_weight_cs` splits it.
Weight-agnostic in `cw` — exactly as the head grades keep `cw` free of the legs' lines. -/
theorem tail_lorentz_core {Pm Pp K : ℝ → ℂ} {Mm Mp cw A T₀ Bamp : ℝ}
    (hPm : Continuous Pm) (hPp : Continuous Pp)
    (hMm : ∀ τ, ‖Pm τ‖ ≤ Mm) (hMp : ∀ τ, ‖Pp τ‖ ≤ Mp)
    (hA0 : 0 < A) (hAT : A ≤ T₀) (hB0 : 0 ≤ Bamp)
    (hKint : Integrable K) (hKb : ∀ τ, ‖K τ‖ ≤ Bamp / (cw ^ 2 + τ ^ 2)) :
    (∫ τ in {τ : ℝ | T₀ < |τ|}, ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖)
      ≤ 2 * Bamp * (Real.sqrt (∫ τ : ℝ, ‖Pm τ‖ ^ 2 / (A ^ 2 + τ ^ 2))
          * Real.sqrt (∫ τ : ℝ, ‖Pp τ‖ ^ 2 / (A ^ 2 + τ ^ 2))) := by
  have hMm0 : (0 : ℝ) ≤ Mm := le_trans (norm_nonneg _) (hMm 0)
  have hMp0 : (0 : ℝ) ≤ Mp := le_trans (norm_nonneg _) (hMp 0)
  have hd : ∀ τ : ℝ, (0 : ℝ) < A ^ 2 + τ ^ 2 := fun τ => by positivity
  have hWcont : Continuous (fun τ : ℝ => 1 / (A ^ 2 + τ ^ 2)) :=
    continuous_const.div (by fun_prop) (fun τ => (hd τ).ne')
  have hWnn : ∀ τ : ℝ, (0 : ℝ) ≤ 1 / (A ^ 2 + τ ^ 2) := fun τ => by positivity
  have hS : MeasurableSet {τ : ℝ | T₀ < |τ|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  -- integrability of the tail integrand (dominated by `Mm·Mp·‖K‖`)
  have hΦmeas : AEStronglyMeasurable (fun τ : ℝ => ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖) volume :=
    ((hPm.norm.mul hPp.norm).aestronglyMeasurable).mul hKint.norm.aestronglyMeasurable
  have hΦint : Integrable (fun τ : ℝ => ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖) := by
    refine (hKint.norm.const_mul (Mm * Mp)).mono' hΦmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hMm τ) (hMp τ) (norm_nonneg _) hMm0)
      (norm_nonneg _)
  -- integrability of the width-`A` Lorentzian majorant
  have hGint : Integrable (fun τ : ℝ => ‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2)) := by
    have hmeas : AEStronglyMeasurable
        (fun τ : ℝ => ‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2)) volume :=
      ((hPm.norm.mul hPp.norm).div (by fun_prop) (fun τ => (hd τ).ne')).aestronglyMeasurable
    refine ((Salt.SW.integrable_inv_c_sq_add_sq hA0).const_mul (Mm * Mp)).mono' hmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hMm τ) (hMp τ) (norm_nonneg _) hMm0)
      (by positivity)
  -- STEP 1: the tail domination `1/(cw²+τ²) ≤ 2/(A²+τ²)` (valid since `A < |τ|`)
  have hdom : ∀ τ ∈ {τ : ℝ | T₀ < |τ|},
      ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖
        ≤ 2 * Bamp * (‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2)) := by
    intro τ hτ
    have hτA : A < |τ| := lt_of_le_of_lt hAT hτ
    have hA2 : A ^ 2 < τ ^ 2 := by
      have h1 : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      nlinarith [abs_nonneg τ]
    have hcw2 : (0 : ℝ) < cw ^ 2 + τ ^ 2 := by nlinarith [sq_nonneg cw, pow_pos hA0 2]
    have hKle : ‖K τ‖ ≤ 2 * Bamp / (A ^ 2 + τ ^ 2) := by
      refine (hKb τ).trans ?_
      rw [div_le_div_iff₀ hcw2 (hd τ)]
      nlinarith [sq_nonneg cw]
    calc ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖
        ≤ ‖Pm τ‖ * ‖Pp τ‖ * (2 * Bamp / (A ^ 2 + τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hKle (by positivity)
      _ = 2 * Bamp * (‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2)) := by ring
  -- STEP 2: the `L²` sockets for `mixed_weight_cs`
  have hsq : ∀ (Q : ℝ → ℂ) (MQ : ℝ), (∀ τ, ‖Q τ‖ ≤ MQ) → Continuous Q →
      Integrable (fun τ : ℝ => ‖Q τ‖ ^ 2 * (1 / (A ^ 2 + τ ^ 2))) := by
    intro Q MQ hQ hQc
    have hMQ0 : (0 : ℝ) ≤ MQ := le_trans (norm_nonneg _) (hQ 0)
    have hmeas : AEStronglyMeasurable
        (fun τ : ℝ => ‖Q τ‖ ^ 2 * (1 / (A ^ 2 + τ ^ 2))) volume :=
      ((hQc.norm.pow 2).mul hWcont).aestronglyMeasurable
    refine ((Salt.SW.integrable_inv_c_sq_add_sq hA0).const_mul (MQ ^ 2)).mono' hmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity), one_div]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hQ τ) 2)
      (by positivity)
  have hmem : ∀ (Q : ℝ → ℂ) (MQ : ℝ), (∀ τ, ‖Q τ‖ ≤ MQ) → Continuous Q →
      MemLp (fun τ : ℝ => ‖Q τ‖ * Real.sqrt (1 / (A ^ 2 + τ ^ 2))) 2 volume := by
    intro Q MQ hQ hQc
    have hucont : Continuous (fun τ : ℝ => ‖Q τ‖ * Real.sqrt (1 / (A ^ 2 + τ ^ 2))) :=
      hQc.norm.mul (Real.continuous_sqrt.comp hWcont)
    rw [memLp_two_iff_integrable_sq hucont.aestronglyMeasurable]
    refine (hsq Q MQ hQ hQc).congr (Filter.Eventually.of_forall (fun τ => ?_))
    simp only [mul_pow, Real.sq_sqrt (hWnn τ)]
  -- STEP 3: assemble
  have hcs := mixed_weight_cs (f := fun τ : ℝ => ‖Pm τ‖) (g := fun τ : ℝ => ‖Pp τ‖)
    (w := fun τ : ℝ => 1 / (A ^ 2 + τ ^ 2)) hWnn (fun τ => norm_nonneg _)
    (fun τ => norm_nonneg _) (hmem Pm Mm hMm hPm) (hmem Pp Mp hMp hPp)
  simp only [mul_one_div] at hcs
  calc (∫ τ in {τ : ℝ | T₀ < |τ|}, ‖Pm τ‖ * ‖Pp τ‖ * ‖K τ‖)
      ≤ ∫ τ in {τ : ℝ | T₀ < |τ|},
          2 * Bamp * (‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2)) :=
        setIntegral_mono_on hΦint.integrableOn
          ((hGint.const_mul (2 * Bamp)).integrableOn) hS hdom
    _ = 2 * Bamp * ∫ τ in {τ : ℝ | T₀ < |τ|},
          ‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2) := integral_const_mul _ _
    _ ≤ 2 * Bamp * ∫ τ : ℝ, ‖Pm τ‖ * ‖Pp τ‖ / (A ^ 2 + τ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hGint
            (Filter.Eventually.of_forall (fun τ => by positivity)))
          (by positivity)
    _ ≤ 2 * Bamp * (Real.sqrt (∫ τ : ℝ, ‖Pm τ‖ ^ 2 / (A ^ 2 + τ ^ 2))
          * Real.sqrt (∫ τ : ℝ, ‖Pp τ‖ ^ 2 / (A ^ 2 + τ ^ 2))) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)

/-- **A-3 — the Plancherelized `crossKer` tail** (`tail_lorentz_grade`).  The `tail_band_sum`
region at the free width `A ≤ T₀ = 2(X+h)/h`, with the window legs kept under the square
root instead of being spent as sups:

  `∫_{|t−t₀|>T₀} ‖P₋‖‖P₊‖‖K‖
      ≤ (4(X+h)^{cw+1}/h)·√(∫_ℝ‖P₋‖²/(A²+τ²))·√(∫_ℝ‖P₊‖²/(A²+τ²))`,  `cw = c₀−α−β`.

The change of variables `t ↦ t−t₀`, then `tail_lorentz_core` at `Bamp = 2(X+h)^{cw+1}/h`
(the `hatKernel_branch2` amplitude).  UNCONDITIONAL in `1 ≤ X`, `0 < h`, `0 < cw`, `0 < A ≤ T₀`. -/
theorem tail_lorentz_grade {g : ℕ → ℂ} {X h y c₀ t₀ α β A : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hA0 : 0 < A)
    (hAT : A ≤ 2 * (X + h) / h) :
    (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ 4 * (X + h) ^ (c₀ - α - β + 1) / h
          * (Real.sqrt (∫ τ : ℝ,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
            * Real.sqrt (∫ τ : ℝ,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))) := by
  set cw := c₀ - α - β with hcwdef
  set T₀ := 2 * (X + h) / h with hT₀def
  have hXh : (0 : ℝ) < X + h := by linarith
  have hPmc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hPpc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hbm : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) := fun τ =>
    norm_windowSum_le_mass g X y (c₀ - β)
      (by rw [show (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
  have hbp : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) := fun τ =>
    norm_windowSum_le_mass g X y (c₀ + β)
      (by rw [show (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
  have hKb : ∀ τ : ℝ, ‖hatKernel X h cw τ‖
      ≤ (2 * (X + h) ^ (cw + 1) / h) / (cw ^ 2 + τ ^ 2) := fun τ => by
    rw [div_div]; exact hatKernel_branch2 hX hh hc τ
  have hB0 : (0 : ℝ) ≤ 2 * (X + h) ^ (cw + 1) / h :=
    div_nonneg (by positivity) hh.le
  -- the change of variables `t ↦ t − t₀`
  have hmp : MeasurePreserving (fun t : ℝ => t - t₀) volume volume :=
    measurePreserving_sub_right volume t₀
  have hme : MeasurableEmbedding (fun t : ℝ => t - t₀) :=
    (Homeomorph.subRight t₀).measurableEmbedding
  have hcov : (∫ t in {t : ℝ | T₀ < |t - t₀|},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h cw (t - t₀)‖)
      = ∫ τ in {τ : ℝ | T₀ < |τ|},
          ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h cw τ‖ := by
    rw [show {t : ℝ | T₀ < |t - t₀|}
          = (fun t : ℝ => t - t₀) ⁻¹' {τ : ℝ | T₀ < |τ|} from rfl]
    exact hmp.setIntegral_preimage_emb hme (fun τ =>
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h cw τ‖) {τ : ℝ | T₀ < |τ|}
  rw [hcov]
  refine le_trans (tail_lorentz_core (Pm := fun τ : ℝ =>
      windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ)))
    (Pp := fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ)))
    (K := fun τ : ℝ => hatKernel X h cw τ) (T₀ := T₀)
    hPmc hPpc hbm hbp hA0 hAT hB0 (integrable_hatKernel hX hh hc) hKb) (le_of_eq (by ring))

/-! ## A-4 — the τ-split composition at the free width (`crossKer_grade_width`)

`head_split_ledger` splits `crossKer` at the branch crossover `T₀ = 2(X+h)/h`.  Both halves
are now graded against the SAME full-line width-`A` Lorentzian second moments
`B∓ = ∫_ℝ ‖P∓‖²/(A²+τ²)` — the integrals `widthA_plancherel` evaluates exactly:

* the head, via `head_sharp_socket` (branch-1 + band CS) and then `band_weight_le_lorentz`,
  which is `band_second_moment_width`'s domination in weight form: the branch-1 band moment
  is at most `(2T₀²/cw)·B`;
* the tail, via `tail_lorentz_grade` (A-3), whose amplitude `4(X+h)^{cw+1}/h` is exactly
  `(X+h)^{cw}·2T₀`.

Exit: `crossKer ≤ (X+h)^{cw}·(4T₀²/cw + 2T₀)·√(B₋)·√(B₊)` — the mass under ONE square root
(the `min¹` the σ-page needs), and `B∓ ≍ (π/A)·(4C/A)·mass` makes the whole amplitude
`(X+h)^{cw}·T₀²/A²` — ABSOLUTE at `A ≍ T₀`. -/

/-- The branch-1 band second moment against the full-line width-`A` Lorentzian moment
(`band_weight_le_lorentz`).  For a bounded continuous `P`, `0 < cw`, `0 < A ≤ T₀`:
`∫_{|τ|≤T₀} ‖P‖²/√(cw²+τ²) ≤ (2T₀²/cw)·∫_ℝ ‖P‖²/(A²+τ²)`.  The two steps of
`band_second_moment_width` in weight form (`1/√(cw²+τ²) ≤ 1/cw` on the band, then
`A²+τ² ≤ 2T₀²`), stated for a general leg so the `windowSum` legs need no Dirichlet fold. -/
theorem band_weight_le_lorentz {P : ℝ → ℂ} {M cw A T₀ : ℝ}
    (hP : Continuous P) (hM : ∀ τ, ‖P τ‖ ≤ M) (hcw : 0 < cw) (hA0 : 0 < A) (hAT : A ≤ T₀) :
    (∫ τ in Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ 2 * T₀ ^ 2 / cw * ∫ τ : ℝ, ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hd : ∀ τ : ℝ, (0 : ℝ) < A ^ 2 + τ ^ 2 := fun τ => by positivity
  have hsq : ∀ τ : ℝ, (0 : ℝ) < Real.sqrt (cw ^ 2 + τ ^ 2) :=
    fun τ => Real.sqrt_pos.mpr (by positivity)
  have hcw_le : ∀ τ : ℝ, cw ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    calc cw = Real.sqrt (cw ^ 2) := (Real.sqrt_sq hcw.le).symm
      _ ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg τ])
  have hLint : Integrable (fun τ : ℝ => ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) volume :=
      ((hP.norm.pow 2).div (by fun_prop) (fun τ => (hd τ).ne')).aestronglyMeasurable
    refine ((Salt.SW.integrable_inv_c_sq_add_sq hA0).const_mul (M ^ 2)).mono' hmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM τ) 2) (by positivity)
  have hbandInt : IntegrableOn (fun τ : ℝ => ‖P τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      (Set.Icc (-T₀) T₀) :=
    ((hP.norm.pow 2).div (Real.continuous_sqrt.comp (by fun_prop))
      (fun τ => (hsq τ).ne')).integrableOn_Icc
  have hpt : ∀ τ ∈ Set.Icc (-T₀) T₀,
      ‖P τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)
        ≤ 2 * T₀ ^ 2 / cw * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by
    intro τ hτ
    rw [Set.mem_Icc] at hτ
    have hτ2 : τ ^ 2 ≤ T₀ ^ 2 := by nlinarith [hτ.1, hτ.2]
    have hA2 : A ^ 2 ≤ T₀ ^ 2 := by nlinarith
    have hratio : (1 : ℝ) ≤ 2 * T₀ ^ 2 / (A ^ 2 + τ ^ 2) := by
      rw [le_div_iff₀ (hd τ)]; linarith
    calc ‖P τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)
        ≤ ‖P τ‖ ^ 2 / cw := div_le_div_of_nonneg_left (by positivity) hcw (hcw_le τ)
      _ = ‖P τ‖ ^ 2 / cw * 1 := (mul_one _).symm
      _ ≤ ‖P τ‖ ^ 2 / cw * (2 * T₀ ^ 2 / (A ^ 2 + τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * T₀ ^ 2 / cw * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) := by ring
  calc (∫ τ in Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ ∫ τ in Set.Icc (-T₀) T₀, 2 * T₀ ^ 2 / cw * (‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2)) :=
        setIntegral_mono_on hbandInt ((hLint.const_mul (2 * T₀ ^ 2 / cw)).integrableOn)
          measurableSet_Icc hpt
    _ = 2 * T₀ ^ 2 / cw * ∫ τ in Set.Icc (-T₀) T₀, ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2) :=
        integral_const_mul _ _
    _ ≤ 2 * T₀ ^ 2 / cw * ∫ τ : ℝ, ‖P τ‖ ^ 2 / (A ^ 2 + τ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hLint (Filter.Eventually.of_forall (fun τ => by positivity)))
          (by positivity)

/-- **A-4 — the `crossKer` grade at the free Lorentzian width** (`crossKer_grade_width`).
The τ-split composition with BOTH halves referred to the same full-line width-`A` moments:

  `crossKer g X h y c₀ t₀ α β
      ≤ (X+h)^{cw}·(4T₀²/cw + 2T₀)·√(∫‖P₋‖²/(A²+τ²))·√(∫‖P₊‖²/(A²+τ²))`,

`cw = c₀−α−β`, `T₀ = 2(X+h)/h`, `P∓ = windowSum(c₀+iτ∓β)`.  UNCONDITIONAL in `1 ≤ X`,
`0 < h`, `0 < cw`, `0 < A ≤ T₀`.  The window mass now sits under ONE square root — the
`min¹` that the σ-page's `min(L,1/σ)²` budget can afford without spending an `L`. -/
theorem crossKer_grade_width {g : ℕ → ℂ} {X h y c₀ t₀ α β A : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hA0 : 0 < A)
    (hAT : A ≤ 2 * (X + h) / h) :
    crossKer g X h y c₀ t₀ α β
      ≤ (X + h) ^ (c₀ - α - β)
          * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h))
          * (Real.sqrt (∫ τ : ℝ,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
            * Real.sqrt (∫ τ : ℝ,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))) := by
  have hXh : (0 : ℝ) < X + h := by linarith
  have hPmc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hPpc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hbm : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) := fun τ =>
    norm_windowSum_le_mass g X y (c₀ - β)
      (by rw [show (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
  have hbp : ∀ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) := fun τ =>
    norm_windowSum_le_mass g X y (c₀ + β)
      (by rw [show (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
  rw [head_split_ledger hX hh hc]
  have hhead := head_sharp_socket (g := g) (y := y) (t₀ := t₀) hX hh hc
  have htail := tail_lorentz_grade (g := g) (y := y) (t₀ := t₀) (A := A) hX hh hc hA0 hAT
  have hAm := band_weight_le_lorentz (A := A) (T₀ := 2 * (X + h) / h) hPmc hbm hc hA0 hAT
  have hAp := band_weight_le_lorentz (A := A) (T₀ := 2 * (X + h) / h) hPpc hbp hc hA0 hAT
  set Am : ℝ := ∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2
        / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2) with hAmdef
  set Ap : ℝ := ∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2
        / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2) with hApdef
  set Bm : ℝ := ∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2) with hBmdef
  set Bp : ℝ := ∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2) with hBpdef
  set k : ℝ := 2 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) with hkdef
  have hk0 : (0 : ℝ) ≤ k := by rw [hkdef]; positivity
  have hSnn : (0 : ℝ) ≤ Real.sqrt Bm * Real.sqrt Bp := by positivity
  -- the geometric mean of the two band moments against the two width-`A` moments
  have hgeo : Real.sqrt Am * Real.sqrt Ap ≤ k * (Real.sqrt Bm * Real.sqrt Bp) := by
    calc Real.sqrt Am * Real.sqrt Ap
        ≤ Real.sqrt (k * Bm) * Real.sqrt (k * Bp) :=
          mul_le_mul (Real.sqrt_le_sqrt hAm) (Real.sqrt_le_sqrt hAp)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt k * Real.sqrt k) * (Real.sqrt Bm * Real.sqrt Bp) := by
          rw [Real.sqrt_mul hk0 Bm, Real.sqrt_mul hk0 Bp]; ring
      _ = k * (Real.sqrt Bm * Real.sqrt Bp) := by rw [Real.mul_self_sqrt hk0]
  have hpre0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β) * 2 :=
    mul_nonneg (Real.rpow_nonneg hXh.le _) (by norm_num)
  have hhead2 : (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ (X + h) ^ (c₀ - α - β) * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β))
          * (Real.sqrt Bm * Real.sqrt Bp) := by
    refine hhead.trans ?_
    calc (X + h) ^ (c₀ - α - β) * 2 * (Real.sqrt Am * Real.sqrt Ap)
        ≤ (X + h) ^ (c₀ - α - β) * 2 * (k * (Real.sqrt Bm * Real.sqrt Bp)) :=
          mul_le_mul_of_nonneg_left hgeo hpre0
      _ = (X + h) ^ (c₀ - α - β) * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β))
          * (Real.sqrt Bm * Real.sqrt Bp) := by rw [hkdef]; ring
  have hpow : (X + h) ^ (c₀ - α - β + 1) = (X + h) ^ (c₀ - α - β) * (X + h) := by
    rw [Real.rpow_add hXh, Real.rpow_one]
  have htail2 : (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ (X + h) ^ (c₀ - α - β) * (2 * (2 * (X + h) / h))
          * (Real.sqrt Bm * Real.sqrt Bp) := by
    refine htail.trans (le_of_eq ?_)
    rw [hpow]; field_simp; ring
  calc (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
          ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
        + ∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
          ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ (X + h) ^ (c₀ - α - β) * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β))
            * (Real.sqrt Bm * Real.sqrt Bp)
          + (X + h) ^ (c₀ - α - β) * (2 * (2 * (X + h) / h))
            * (Real.sqrt Bm * Real.sqrt Bp) := add_le_add hhead2 htail2
    _ = (X + h) ^ (c₀ - α - β)
          * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h))
          * (Real.sqrt Bm * Real.sqrt Bp) := by ring

/-! ## A-5a — the FULL-LINE width-`A` moment, graded (`line_moment_grade_width`)

`widthA_plancherel` evaluates `∫_ℝ ‖P(c+iτ)‖²/(A²+τ²)` EXACTLY as `(π/A)·(bilinear sum)`;
the bilinear sum collapses to `diagonal + off-diagonal` and both are graded:

* the off-diagonal by `offdiag_widthA_final` (`4C/(A−c+1)`) resp. `offdiag_widthA_final_low`
  (`4C/A`, with the window excess `Q^{1−c}`) — pure instantiation at the free width;
* the DIAGONAL by `diag_le_mass_width`: under the y-gate `2A⁸ ≤ n` and `c ≥ 3/4` every window
  term obeys `‖b_n‖/n^c ≤ 2√n/n^{3/4} = 2/n^{1/4} ≤ 2/A²`, so
  `∑ ‖b_n‖²/n^{2c} ≤ (2/A²)·∑ ‖b_n‖/n^c` — the diagonal is `1/A²`-SMALL, not `O(1)`.
  This is what makes the closed grade absolute: the head amplitude `4πT₀²/(A·cw)` multiplies
  `(2/A² + 4C/A)`, i.e. `T₀²/A²` times an absolute constant. -/

/-- The bilinear collapse of the Plancherel sum: real parts to norms, then the diagonal
`m = n` split off (its exponential factor is `1`).  The shared core of the width-`A` grades,
parameterized by whatever bound `Off` the off-diagonal ladder supplies. -/
private lemma planch_bilinear_le {F : Finset ℕ} {b : ℕ → ℂ} {c A Off : ℝ}
    (hoff : (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) ≤ Off) :
    (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(A * |Real.log m - Real.log n|)))
      ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c) + Off := by
  have hRe_le_K : ∀ m n : ℕ,
      (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|))
        ≤ ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)) := by
    intro m n
    have hre : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * starRingEnd ℂ (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(A * |Real.log m - Real.log n|)) := by positivity
    calc (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|))
        = (b m * starRingEnd ℂ (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(A * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(A * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  have hper_m : ∀ m ∈ F,
      (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c
          + ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
    intro m hm
    have he1 : (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
        = ∑ n ∈ F, ((if m = n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)
            + (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : m = n
      · rw [if_pos h, if_neg (by simp [h]), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    rw [he1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq F m (fun n => ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(A * |Real.log m - Real.log n|))), if_pos hm,
      sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, ← pow_two]
  calc (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)))
      ≤ ∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(A * |Real.log m - Real.log n|)) :=
        Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hRe_le_K m n))
    _ = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
          + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(A * |Real.log m - Real.log n|)) else 0) := by
        rw [Finset.sum_congr rfl hper_m, Finset.sum_add_distrib]
    _ ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c) + Off := add_le_add le_rfl hoff

/-- **The `1/A²`-small window diagonal** (`diag_le_mass_width`).  Under the y-gate
`2A⁸ ≤ n` on the window, `1 ≤ A` and a line `c ≥ 3/4`, every `Λ`-bounded coefficient obeys
`‖b_n‖/n^c ≤ 2√n/n^{3/4} = 2/n^{1/4} ≤ 2/A²`, so the diagonal is `2/A²` times the mass:
`∑_{n∈F} ‖b_n‖²/(n·n)^c ≤ (2/A²)·∑_{n∈F} ‖b_n‖/n^c`. -/
private lemma diag_le_mass_width {F : Finset ℕ} {b : ℕ → ℂ} {c A : ℝ}
    (hc34 : 3 / 4 ≤ c) (hA1 : 1 ≤ A)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) :
    (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
      ≤ 2 / A ^ 2 * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  have hA0 : (0 : ℝ) < A := by linarith
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- the term is the square of `‖b n‖/n^c`
  have hsq : ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c = (‖b n‖ / (n : ℝ) ^ c) ^ 2 := by
    rw [div_pow, show ((n * n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) from by push_cast; ring,
      Real.mul_rpow hn0.le hn0.le, ← pow_two]
  -- the uniform per-term bound `‖b n‖/n^c ≤ 2/A²`
  have hlog : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have h1 : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 := Real.log_sqrt hn0.le
    have h3 : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
    rw [h2] at h1
    rw [← h3]
    linarith
  have hA2n : A ^ 2 ≤ (n : ℝ) ^ (c - 1 / 2 : ℝ) := by
    have h8 : (A : ℝ) ^ 2 = ((A : ℝ) ^ 8) ^ (1 / 4 : ℝ) := by
      rw [show (A : ℝ) ^ 8 = ((A : ℝ) ^ 2) ^ (4 : ℕ) from by ring,
        ← Real.rpow_natCast ((A : ℝ) ^ 2) 4, ← Real.rpow_mul (by positivity)]
      norm_num
    have hgate : (A : ℝ) ^ 8 ≤ (n : ℝ) := by
      have := hygate n hn
      nlinarith [pow_nonneg hA0.le 8]
    have h2 : ((A : ℝ) ^ 8) ^ (1 / 4 : ℝ) ≤ ((n : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hgate (by norm_num)
    have h3 : ((n : ℝ)) ^ (1 / 4 : ℝ) ≤ ((n : ℝ)) ^ (c - 1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [h8]; linarith
  have hterm : ‖b n‖ / (n : ℝ) ^ c ≤ 2 / A ^ 2 := by
    have hsplit : (n : ℝ) ^ c = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (c - 1 / 2 : ℝ) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hbn : ‖b n‖ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) :=
      le_trans (hb n) (le_trans ArithmeticFunction.vonMangoldt_le_log hlog)
    have hp1 : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
    have hp2 : (0 : ℝ) < (n : ℝ) ^ (c - 1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
    rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hA2n hp1.le]
  have hnn : (0 : ℝ) ≤ ‖b n‖ / (n : ℝ) ^ c := by positivity
  rw [hsq, pow_two]
  exact mul_le_mul_of_nonneg_right hterm hnn

/-- **A-5a (high leg) — the graded full-line width-`A` moment** (`line_moment_grade_width`).
For `3/4 ≤ c` with `1 ≤ c ≤ A`, `4 ≤ A`, `Λ`-bounded coefficients and the y-gate `2A⁸ ≤ n`:

  `∫_ℝ ‖P(c+iτ)‖²/(A²+τ²) ≤ (π/A)·(2/A² + 4C/(A−c+1))·∑_{n∈F} ‖b_n‖/n^c`,

`C` the absolute constant of `shortInterval_vonMangoldt_le`. -/
theorem line_moment_grade_width {F : Finset ℕ} {b : ℕ → ℂ} {c A : ℝ}
    (hc : 1 ≤ c) (hA4 : 4 ≤ A) (hcA : c ≤ A)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∫ τ : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 4 * Cb / (A - c + 1))
            * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
  have hA0 : (0 : ℝ) < A := by linarith
  obtain ⟨C, hC0, hoff⟩ := offdiag_widthA_final hc hcA hA4 hF hb hygate
  refine ⟨C, hC0, ?_⟩
  rw [widthA_plancherel F b (c := c) hA0 hF]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (planch_bilinear_le hoff).trans ?_
  have hdiag := diag_le_mass_width (c := c) (A := A) (by linarith) (by linarith) hF hb hygate
  rw [add_mul]
  exact add_le_add hdiag le_rfl

/-- **A-5a (low leg) — the graded full-line width-`A` moment at a sub-unit line**
(`line_moment_grade_low_width`).  For `3/4 ≤ c ≤ 1`, `4 ≤ A`, the y-gate `2A⁸ ≤ n` and the
window `1 ≤ n ≤ Q`:

  `∫_ℝ ‖P(c+iτ)‖²/(A²+τ²) ≤ (π/A)·(2/A² + 4C/A)·(Q^{1−c}·∑_{n∈F} ‖b_n‖/n^c)`.

The window excess `Q^{1−c} ≥ 1` (`1 ≤ Q`, `c ≤ 1`) absorbs the diagonal too. -/
theorem line_moment_grade_low_width {F : Finset ℕ} {b : ℕ → ℂ} {c A Q : ℝ}
    (hc34 : 3 / 4 ≤ c) (hc1 : c ≤ 1) (hA4 : 4 ≤ A) (hQ1 : 1 ≤ Q)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) (hQ : ∀ n ∈ F, (n : ℝ) ≤ Q) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∫ τ : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 4 * Cb / A)
            * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcA : c ≤ A := by linarith
  obtain ⟨C, hC0, hoff⟩ := offdiag_widthA_final_low hc0 hc1 hcA hA4 hF hb hygate hQ
  refine ⟨C, hC0, ?_⟩
  rw [widthA_plancherel F b (c := c) hA0 hF]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (planch_bilinear_le hoff).trans ?_
  have hdiag := diag_le_mass_width (c := c) (A := A) hc34 (by linarith) hF hb hygate
  have hmass0 : (0 : ℝ) ≤ ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hQexc : (1 : ℝ) ≤ Q ^ (1 - c) := Real.one_le_rpow hQ1 (by linarith)
  have hdiag' : (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
      ≤ 2 / A ^ 2 * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
    refine hdiag.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc (∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)
        = 1 * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := (one_mul _).symm
      _ ≤ Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c :=
          mul_le_mul_of_nonneg_right hQexc hmass0
  rw [add_mul]
  exact add_le_add hdiag' le_rfl

/-! ## A-5 — the per-`(α,β)` `1/σ` bound at an ABSOLUTE constant

`crossKer_sharp_sigma_bound` (RHSGrade §2) pays `min(L,1/σ)² ≤ L·(1/σ)` because the crude
face carries the window mass SQUARED.  The width-decoupled face carries it under a square
root, so the geometric mean `√(S₋·S₊)` consumes exactly ONE `min`, and `min ≤ 1/σ` closes
with NO leftover `L`.  That is the whole win: the σ-page's second `L` never appears.

The `X^β` bookkeeping: the low leg's window excess `(X/y)^{1−(c₀−β)} = (X/y)^{β−1/L}` (and
`1` in the `β < 1/L` sub-range, where the low line is still `≥ 1`) is uniformly `≤ X^β`, and
`√(X^β·S₋·S₊) ≤ 9(log 4+4)·X^β·min(L,1/σ)` by `window_bridge` (dropping `y^{−2β} ≤ 1` and
`e ≤ 9`); the surviving `X^β` is cancelled by `amp_beta_cancel_widthA`. -/

/-- The geometric-mean step, on OPAQUE reals (so no `ring` ever meets a window sum):
from `u·v ≤ w²` and a common nonneg factor `k`, `√(k·u)·√(k·v) ≤ k·w`. -/
private lemma sqrt_mul_sqrt_le {k u v w : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u) (_hv : 0 ≤ v)
    (hw : 0 ≤ w) (huv : u * v ≤ w ^ 2) :
    Real.sqrt (k * u) * Real.sqrt (k * v) ≤ k * w := by
  have h2 : (k * u) * (k * v) ≤ (k * w) ^ 2 := by
    calc (k * u) * (k * v) = k ^ 2 * (u * v) := by ring
      _ ≤ k ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_left huv (sq_nonneg _)
      _ = (k * w) ^ 2 := by ring
  calc Real.sqrt (k * u) * Real.sqrt (k * v) = Real.sqrt ((k * u) * (k * v)) :=
        (Real.sqrt_mul (mul_nonneg hk hu) _).symm
    _ ≤ Real.sqrt ((k * w) ^ 2) := Real.sqrt_le_sqrt h2
    _ = k * w := Real.sqrt_sq (mul_nonneg hk hw)

/-- The closing regrouping, on OPAQUE reals: the amplitude `P` meets the `X^β` cancellation
and the single `min` is spent on `1/σ`. -/
private lemma width_final_algebra {P Amp Kf Lg Xb XX mn sg : ℝ}
    (hP : 0 ≤ P) (hAmp : 0 ≤ Amp) (hKf : 0 ≤ Kf) (hLg : 0 ≤ Lg) (hmn : 0 ≤ mn)
    (hXb : 0 ≤ Xb) (hcancel : P * Xb ≤ XX) (hms : mn ≤ sg) :
    P * Amp * (Kf * (Lg * Xb * mn)) ≤ Amp * Kf * Lg * XX * sg := by
  have hXX0 : (0 : ℝ) ≤ XX := le_trans (mul_nonneg hP hXb) hcancel
  calc P * Amp * (Kf * (Lg * Xb * mn)) = (Amp * Kf * Lg) * ((P * Xb) * mn) := by ring
    _ ≤ (Amp * Kf * Lg) * (XX * sg) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcancel hms hmn hXX0)
          (by positivity)
    _ = Amp * Kf * Lg * XX * sg := by ring

/-- The `X^β` cancellation at the width face: `(X+h)^{c₀−α−β}·X^β ≤ (X+h)^{c₀}·(X+h)^{−α}`.
Local re-derivation of `RHSGrade`'s private `amp_beta_cancel_sharp`. -/
private lemma amp_beta_cancel_widthA {X h c₀ α β : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    (hβ0 : 0 ≤ β) :
    (X + h) ^ (c₀ - α - β) * X ^ β ≤ (X + h) ^ c₀ * (X + h) ^ (-α) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hsplit : (X + h) ^ (c₀ - α - β)
      = (X + h) ^ c₀ * (X + h) ^ (-α) * (X + h) ^ (-β) := by
    rw [← Real.rpow_add hXh0, ← Real.rpow_add hXh0]
    congr 1
  have hXβ : X ^ β ≤ (X + h) ^ β := Real.rpow_le_rpow hX0.le (by linarith) hβ0
  have hneg0 : (0 : ℝ) < (X + h) ^ (-β) := Real.rpow_pos_of_pos hXh0 _
  have hcancel : (X + h) ^ (-β) * X ^ β ≤ 1 := by
    have hkey : (X + h) ^ (-β) * (X + h) ^ β = 1 := by
      rw [← Real.rpow_add hXh0]; simp
    calc (X + h) ^ (-β) * X ^ β ≤ (X + h) ^ (-β) * (X + h) ^ β :=
          mul_le_mul_of_nonneg_left hXβ hneg0.le
      _ = 1 := hkey
  have hbase0 : (0 : ℝ) ≤ (X + h) ^ c₀ * (X + h) ^ (-α) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _)
  calc (X + h) ^ (c₀ - α - β) * X ^ β
      = ((X + h) ^ c₀ * (X + h) ^ (-α)) * ((X + h) ^ (-β) * X ^ β) := by rw [hsplit]; ring
    _ ≤ ((X + h) ^ c₀ * (X + h) ^ (-α)) * 1 := mul_le_mul_of_nonneg_left hcancel hbase0
    _ = (X + h) ^ c₀ * (X + h) ^ (-α) := by ring

/-- **A-5 — the width-decoupled per-`(α,β)` `1/σ` bound** (`crossKer_width_sigma_bound`).
At the pinned home (`c₀ = 1+1/L`, `L = log X`, `σ = β+1/L`), for any width `4 ≤ A ≤ T₀`
whose y-gate `2A⁸ ≤ n` holds on the window:

  `crossKer α β ≤ Kα·(1/σ)`,
  `Kα = (4T₀²/(c₀−α−β) + 2T₀)·(π/A)(2/A² + 8C/A)·9(log 4+4)·(X+h)^{c₀}·(X+h)^{−α}`.

**No `L`.**  The bracket `(4T₀²/cw + 2T₀)·(π/A)(2/A²+8C/A)` is `Θ(T₀²/A²)` — an ABSOLUTE
constant at `A ≍ T₀`, where `crossKer_sharp_sigma_bound` carried `L·(4·arsinh(2T)+…)`. -/
theorem crossKer_width_sigma_bound (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ A : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hσ : σ = β + 1 / L)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 4)
    (hA4 : 4 ≤ A) (hAT : A ≤ 2 * (X + h) / h)
    (hygate : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, 2 * A ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      crossKer g X h y c₀ t₀ α β
        ≤ ((4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h))
            * (Real.pi / A * (2 / A ^ 2 + 8 * Cb / A))
            * (9 * (Real.log 4 + 4))
            * ((X + h) ^ c₀ * (X + h) ^ (-α))) * (1 / σ) := by
  have hX : (1 : ℝ) ≤ X := le_trans hy hyX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hLinv4 : 1 / L ≤ 1 / 3 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hc : (0 : ℝ) < c₀ - α - β := by rw [hc₀]; linarith
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  have hβ4 : β ≤ 1 / 4 := by linarith
  -- the numeric facts, hoisted (linarith/nlinarith run in a SMALL context)
  have hβ2 : β ≤ 1 / 2 := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog9 : (0 : ℝ) ≤ 9 * (Real.log 4 + 4) := by linarith
  have hmin0 : (0 : ℝ) ≤ min L (1 / σ) := le_min hL0.le (by positivity)
  have hyb : y ^ (-(2 * β)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hyb0 : (0 : ℝ) ≤ y ^ (-(2 * β)) := Real.rpow_nonneg hy0.le _
  have hfac : 9 * Real.exp 1 * y ^ (-(2 * β)) ≤ 81 := by
    have h1 : 9 * Real.exp 1 * y ^ (-(2 * β)) ≤ 9 * Real.exp 1 * 1 :=
      mul_le_mul_of_nonneg_left hyb (by positivity)
    nlinarith [Real.exp_one_lt_d9]
  -- the window data
  have hF : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, 1 ≤ n := by
    intro n hn; rw [Finset.mem_Ioo] at hn; omega
  have hb : ∀ n, ‖lambdaLin (restrictAbove y g) n‖ ≤ ArithmeticFunction.vonMangoldt n :=
    fun n => lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) n
  have hQ : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (n : ℝ) ≤ X / y := by
    intro n hn
    rw [Finset.mem_Ioo] at hn
    exact le_of_lt (Nat.lt_ceil.mp hn.2)
  have hQ1 : (1 : ℝ) ≤ X / y := (one_le_div hy0).mpr hyX
  have hXy_le : X / y ≤ X := div_le_self hX0.le hy
  set Sm : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hSmdef
  set Sp : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hSpdef
  have hSm0 : (0 : ℝ) ≤ Sm := Finset.sum_nonneg (fun n _ => by positivity)
  have hSp0 : (0 : ℝ) ≤ Sp := Finset.sum_nonneg (fun n _ => by positivity)
  have hXβ0 : (0 : ℝ) ≤ X ^ β := Real.rpow_nonneg hX0.le _
  have hXβ1 : (1 : ℝ) ≤ X ^ β := Real.one_le_rpow hX hβ0
  -- the two legs, folded to the Dirichlet form the width-`A` grades speak
  have hfoldM : (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      = ∫ τ : ℝ, ‖∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ - β : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
        / (A ^ 2 + τ ^ 2) := by
    have hwin : ∀ τ : ℝ, windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))
        = ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ - β : ℝ) : ℂ) + (τ : ℂ) * I) := by
      intro τ
      unfold windowSum
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ)) = (((c₀ - β : ℝ) : ℂ) + (τ : ℂ) * I) from by
        push_cast; ring]
    simp_rw [hwin]
  have hfoldP : (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      = ∫ τ : ℝ, ‖∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ + β : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
        / (A ^ 2 + τ ^ 2) := by
    have hwin : ∀ τ : ℝ, windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))
        = ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ + β : ℝ) : ℂ) + (τ : ℂ) * I) := by
      intro τ
      unfold windowSum
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ)) = (((c₀ + β : ℝ) : ℂ) + (τ : ℂ) * I) from by
        push_cast; ring]
    simp_rw [hwin]
  -- the LOW leg, uniformly across the `β ≷ 1/L` sub-ranges
  have hBmkey : ∃ Cm : ℝ, 0 ≤ Cm ∧
      (∫ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 8 * Cm / A) * (X ^ β * Sm)) := by
    rw [hfoldM]
    rcases le_or_gt (c₀ - β) 1 with hlow | hhigh
    · obtain ⟨Cm, hCm0, hgr⟩ := line_moment_grade_low_width
        (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
        (c := c₀ - β) (A := A) (Q := X / y)
        (by rw [hc₀]; linarith) hlow hA4 hQ1 hF hb hygate hQ
      refine ⟨Cm, hCm0, hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
      have hexp : (1 : ℝ) - (c₀ - β) = β - 1 / L := by rw [hc₀]; ring
      have hβL : 1 / L ≤ β := by rw [hc₀] at hlow; linarith
      have hexc : (X / y) ^ (1 - (c₀ - β)) ≤ X ^ β := by
        rw [hexp]
        calc (X / y) ^ (β - 1 / L) ≤ X ^ (β - 1 / L) :=
              Real.rpow_le_rpow (by positivity) hXy_le (by linarith)
          _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      have hcoef : 2 / A ^ 2 + 4 * Cm / A ≤ 2 / A ^ 2 + 8 * Cm / A := by
        have h48 : 4 * Cm / A ≤ 8 * Cm / A := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hA0.le)
        exact add_le_add le_rfl h48
      exact mul_le_mul hcoef (mul_le_mul_of_nonneg_right hexc hSm0)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) hSm0) (by positivity)
    · obtain ⟨Cm, hCm0, hgr⟩ := line_moment_grade_width
        (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
        (c := c₀ - β) (A := A) hhigh.le hA4 (by rw [hc₀]; linarith) hF hb hygate
      refine ⟨Cm, hCm0, hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
      have hden : A / 2 ≤ A - (c₀ - β) + 1 := by rw [hc₀]; linarith
      have hcoef : 4 * Cm / (A - (c₀ - β) + 1) ≤ 8 * Cm / A := by
        rw [div_le_div_iff₀ (by linarith) hA0]
        nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ 8 * Cm)]
      refine mul_le_mul (by linarith) ?_ hSm0 (by positivity)
      calc Sm = 1 * Sm := (one_mul _).symm
        _ ≤ X ^ β * Sm := mul_le_mul_of_nonneg_right hXβ1 hSm0
  -- the HIGH leg
  have hBpkey : ∃ Cp : ℝ, 0 ≤ Cp ∧
      (∫ τ : ℝ, ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 8 * Cp / A) * Sp) := by
    rw [hfoldP]
    obtain ⟨Cp, hCp0, hgr⟩ := line_moment_grade_width
      (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
      (c := c₀ + β) (A := A) (by rw [hc₀]; linarith) hA4 (by rw [hc₀]; linarith) hF hb hygate
    refine ⟨Cp, hCp0, hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
    have hden : A / 2 ≤ A - (c₀ + β) + 1 := by rw [hc₀]; linarith
    have hcoef : 4 * Cp / (A - (c₀ + β) + 1) ≤ 8 * Cp / A := by
      rw [div_le_div_iff₀ (by linarith) hA0]
      nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ 8 * Cp)]
    exact mul_le_mul_of_nonneg_right (by linarith) hSp0
  obtain ⟨Cm, hCm0, hBm⟩ := hBmkey
  obtain ⟨Cp, hCp0, hBp⟩ := hBpkey
  set C : ℝ := max Cm Cp with hCdef
  have hC0 : (0 : ℝ) ≤ C := le_trans hCm0 (le_max_left _ _)
  have hKfac0 : (0 : ℝ) ≤ Real.pi / A * (2 / A ^ 2 + 8 * C / A) := by positivity
  have hmono : ∀ D : ℝ, D ≤ C → 2 / A ^ 2 + 8 * D / A ≤ 2 / A ^ 2 + 8 * C / A := by
    intro D hD
    have hmul : 8 * D / A ≤ 8 * C / A := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) (inv_nonneg.mpr hA0.le)
    exact add_le_add le_rfl hmul
  have hBm' : (∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * (2 / A ^ 2 + 8 * C / A) * (X ^ β * Sm) :=
    hBm.trans (le_of_le_of_eq
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hmono Cm (le_max_left _ _)) (mul_nonneg hXβ0 hSm0))
        (by positivity))
      (mul_assoc _ _ _).symm)
  have hBp' : (∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * (2 / A ^ 2 + 8 * C / A) * Sp :=
    hBp.trans (le_of_le_of_eq
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hmono Cp (le_max_right _ _)) hSp0)
        (by positivity))
      (mul_assoc _ _ _).symm)
  -- the window-mass product: ONE `min`, no `L`
  have hW0 : (0 : ℝ) ≤ 9 * (Real.log 4 + 4) * X ^ β * min L (1 / σ) :=
    mul_nonneg (mul_nonneg hlog9 hXβ0) hmin0
  have hwin := window_bridge g hg hL hL3 hy hyX hc₀ hβ0 hβ2 hσ
  have hstep : X ^ β * Sm * Sp ≤ (9 * (Real.log 4 + 4) * X ^ β * min L (1 / σ)) ^ 2 := by
    calc X ^ β * Sm * Sp
        = X ^ β * (Sm * Sp) := mul_assoc _ _ _
      _ ≤ X ^ β * (9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 * (X ^ β * y ^ (-(2 * β)))
            * min L (1 / σ) ^ 2) := mul_le_mul_of_nonneg_left hwin hXβ0
      _ = X ^ β * ((9 * Real.exp 1 * y ^ (-(2 * β)))
            * ((Real.log 4 + 4) ^ 2 * X ^ β * min L (1 / σ) ^ 2)) := by ring
      _ ≤ X ^ β * (81 * ((Real.log 4 + 4) ^ 2 * X ^ β * min L (1 / σ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hfac (by positivity)) hXβ0
      _ = (9 * (Real.log 4 + 4) * X ^ β * min L (1 / σ)) ^ 2 := by ring
  -- the geometric mean: the `min¹` exit
  have hgeo : Real.sqrt (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      * Real.sqrt (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      ≤ Real.pi / A * (2 / A ^ 2 + 8 * C / A)
          * (9 * (Real.log 4 + 4) * X ^ β * min L (1 / σ)) := by
    refine le_trans (mul_le_mul (Real.sqrt_le_sqrt hBm') (Real.sqrt_le_sqrt hBp')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
    exact sqrt_mul_sqrt_le hKfac0 (mul_nonneg hXβ0 hSm0) hSp0 hW0 hstep
  -- assemble against the A-4 exit
  have hAmp0 : (0 : ℝ) ≤ 4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h) := by
    positivity
  have hpre0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β)
      * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h)) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) hAmp0
  refine ⟨C, hC0, ?_⟩
  refine (crossKer_grade_width (g := g) (y := y) (t₀ := t₀) (A := A) hX hh hc hA0 hAT).trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left hgeo hpre0) ?_
  exact width_final_algebra (Real.rpow_nonneg hXh0.le _) hAmp0 hKfac0 hlog9 hmin0 hXβ0
    (amp_beta_cancel_widthA hX hh hβ0) (min_le_right _ _)

/-! ## A-6a — the width pin: the y-gate holds BY CONSTRUCTION (`width_pin_gates`)

The one price of the free width is the y-gate `2A⁸ ≤ n` on the window.  GRADE-SCOPE's
choice `A := (y/2)^{1/8}` makes it an IDENTITY-plus-`ε`: `2A⁸ = y`, and every window member
satisfies `n > y` by definition of `Finset.Ioo ⌊y⌋₊ _`.  So the gate costs NO new hypothesis
downstream — no re-pin, only the (already available) window floor.  The other two gates
(`4 ≤ A`, `A ≤ T₀`) are the elementary `y ≥ 2·4⁸` and `y ≤ 2T₀⁸`; at the pin `y = L⁴`,
`T₀ = 2(X+h)/h = 2√L + 2` these read `L ≥ 19.1…` and `L⁴ ≤ 2(2√L+2)⁸`, both slack. -/

/-- **A-6a — the width pin gates** (`width_pin_gates`).  At `A := (y/2)^{1/8}`:
`A⁸ = y/2`, `4 ≤ A` (from `y ≥ 2·4⁸ = 131072`), `A ≤ T₀` (from `y ≤ 2T₀⁸`), and the y-gate
`2A⁸ = y ≤ n` on the whole window — BY CONSTRUCTION. -/
theorem width_pin_gates {X y T₀ A : ℝ} (hy : 131072 ≤ y) (hT₀ : 0 < T₀)
    (hyT : y ≤ 2 * T₀ ^ 8) (hA : A = (y / 2) ^ (1 / 8 : ℝ)) :
    A ^ 8 = y / 2 ∧ 4 ≤ A ∧ A ≤ T₀ ∧
      ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, 2 * A ^ 8 ≤ (n : ℝ) := by
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; exact Real.rpow_nonneg hy2.le _
  have hA8 : A ^ 8 = y / 2 := by
    rw [hA, ← Real.rpow_natCast ((y / 2) ^ (1 / 8 : ℝ)) 8, ← Real.rpow_mul hy2.le]
    norm_num
  have h48 : ((4 : ℝ)) ^ 8 = 65536 := by norm_num
  refine ⟨hA8, ?_, ?_, ?_⟩
  · refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hA0 ?_
    rw [hA8, h48]; linarith
  · refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hT₀.le ?_
    rw [hA8]; linarith
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    have hyn : y < (n : ℝ) := (Nat.floor_lt (by linarith)).mp hn.1
    rw [hA8]; linarith

/-- **A-6b — the width-decoupled `1/σ` bound AT THE PIN** (`crossKer_width_sigma_pin`).
`crossKer_width_sigma_bound` at `A := (y/2)^{1/8}`, whose three gates `width_pin_gates`
discharges from the window floor alone:

  `crossKer α β ≤ Kα·(1/σ)`,
  `Kα = (4T₀²/(c₀−α−β) + 2T₀)·(π/A)(2/A² + 8C/A)·9(log 4+4)·(X+h)^{c₀}·(X+h)^{−α}`,
  `A = (y/2)^{1/8}`, `T₀ = 2(X+h)/h`.

At the pin (`y = L⁴`, `h = X/√L`) the bracket is `Θ(L)·Θ(C/L) = Θ(C)` — an ABSOLUTE
constant, where `crossKer_sharp_sigma_bound` carried `Θ(L·log L)`.  **No `L` survives.** -/
theorem crossKer_width_sigma_pin (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 131072 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hσ : σ = β + 1 / L)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 4)
    (hyT : y ≤ 2 * (2 * (X + h) / h) ^ 8) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      crossKer g X h y c₀ t₀ α β
        ≤ ((4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h))
            * (Real.pi / (y / 2) ^ (1 / 8 : ℝ)
              * (2 / ((y / 2) ^ (1 / 8 : ℝ)) ^ 2 + 8 * Cb / (y / 2) ^ (1 / 8 : ℝ)))
            * (9 * (Real.log 4 + 4))
            * ((X + h) ^ c₀ * (X + h) ^ (-α))) * (1 / σ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hT₀0 : (0 : ℝ) < 2 * (X + h) / h := div_pos (by linarith) hh
  obtain ⟨-, hA4, hAT, hygate⟩ := width_pin_gates (X := X) hy hT₀0 hyT rfl
  exact crossKer_width_sigma_bound g hg hL hL3 (by linarith) hyX hc₀ hh hσ hα0 hβ0 hαβ
    hA4 hAT hygate

end Salt.MR
