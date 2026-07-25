/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.WidthGrade
import Salt.MR.RHSGrade

/-!
# The ABSOLUTE-constant grade (`GradeConst`)

`WidthGrade.crossKer_width_sigma_bound` closes the `crossKer` page at a bracket that carries
**no `L`** — the whole win of the width-decoupled Plancherel route.  Three residuals stood
between that and the `hgrade` socket of `RHSGrade.hRHS_discharged` at an ABSOLUTE `C₁`:

1. **`Cb` uniformity.**  `crossKer_width_sigma_bound` exhibits its short-interval constant
   per `(α, β)` (and per scale `k`), because `HeadGrade.hband_discharge` opens
   `shortInterval_vonMangoldt_le`'s existential inside.  The consumers
   (`bridge_adapter` ∘ `joint_sigma_integral`, then the `α`-integral) need ONE constant
   fixed before every quantifier.  §1 re-runs the A-arm ladder with the short-interval
   datum as a PARAMETER (`hCbound`), so the constant can be obtained once, outermost.
2. **The pin arithmetic.**  §2 collapses the bracket
   `(4T₀²/cw + 2T₀)·(π/A)(2/A² + 8Cb/A)·9(log 4+4)` at the pin (`h = X/√L`, `y = L⁴`,
   `A = (y/2)^{1/8}`, `cw ≥ 3/4`) to an explicit absolute numeral times `(1 + Cb)`.
3. **A-6 proper.**  §3 re-runs `RHSGrade`'s §4/§5 assembly against the width face:
   `beta_integral_pin_const` → `rhs_grade_at_scale_const` → `hRHS_discharged_const`,
   whose conclusion is `hRHS_discharged`'s byte-for-byte with `C₁` EXHIBITED absolute.

Nothing in `HeadGrade`/`WidthGrade`/`RHSGrade` is touched: the handful of `private` lemmas
those files keep (`sum_ne_eq_two_lt`, `planch_bilinear_le`, `diag_le_mass_width`,
`sqrt_mul_sqrt_le`, `width_final_algebra`, `amp_beta_cancel_widthA`, `pin_basic`,
`continuous_rpow_neg`, the two integrability pages, `four_log_le_self`) are re-derived here
verbatim-private.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the `Cb`-parametrized width ladder

Every step of `WidthGrade`'s A-5 that touches the short-interval grain is repeated with the
constant carried as an explicit parameter.  The one genuinely new statement is
`crossKer_width_sigma_bound_uniform`: `∃ Cb, ∀ (α, β)` in place of `∀ (α, β), ∃ Cb`. -/

/-- The short-interval Chebyshev datum, as a hypothesis: `shortInterval_vonMangoldt_le`'s
conclusion at a NAMED constant.  Parametrizing on this is what lets the constant be fixed
outside every quantifier downstream. -/
def ShortIntervalDatum (Cb : ℝ) : Prop :=
  ∀ u H : ℝ, (65536 : ℝ) ≤ u → u ≤ H * Real.sqrt (Real.sqrt (Real.sqrt u)) → H ≤ u →
    ∑ m ∈ Finset.Ioc ⌊u⌋₊ ⌊u + H⌋₊, ArithmeticFunction.vonMangoldt m ≤ Cb * H

/-- The datum is inhabited (at `Cb = 250`) — `shortInterval_vonMangoldt_le` repackaged. -/
theorem exists_shortIntervalDatum : ∃ Cb : ℝ, 0 ≤ Cb ∧ ShortIntervalDatum Cb :=
  shortInterval_vonMangoldt_le

/-- For a symmetric kernel `T`, the full `m ≠ n` off-diagonal is twice its strict lower part.
Verbatim re-derivation of `HeadGrade`'s private `sum_ne_eq_two_lt`. -/
private lemma sum_ne_eq_two_ltC {F : Finset ℕ} {T : ℕ → ℕ → ℝ}
    (hsymm : ∀ m n, T m n = T n m) :
    ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then T m n else 0)
      = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by
  have hsplit : ∀ m n : ℕ, (if m ≠ n then T m n else 0)
      = (if m < n then T m n else 0) + (if n < m then T m n else 0) := by
    intro m n
    rcases lt_trichotomy m n with h | h | h
    · rw [if_pos (ne_of_lt h), if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_neg (by simp [h]), add_zero]
    · rw [if_pos (ne_of_gt h), if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have hlow : ∑ m ∈ F, ∑ n ∈ F, (if n < m then T m n else 0)
      = ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => by rw [hsymm n m]))
  calc ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then T m n else 0)
      = ∑ m ∈ F, ∑ n ∈ F, ((if m < n then T m n else 0) + (if n < m then T m n else 0)) :=
        Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hsplit m n))
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0))
          + ∑ m ∈ F, ∑ n ∈ F, (if n < m then T m n else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_add_distrib])
    _ = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by rw [hlow]; ring

/-- **The `hband` discharge at a NAMED short-interval constant** — `HeadGrade`'s
`hband_discharge` with `shortInterval_vonMangoldt_le`'s existential lifted to a parameter.
The proof is that file's verbatim, minus the `obtain`. -/
theorem hband_discharge_param {F : Finset ℕ} {b : ℕ → ℂ} {a Cb : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (ha4 : 4 ≤ a)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * a ^ 8 ≤ (n : ℝ)) :
    ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hexp_le2 : Real.exp (1 / a) ≤ 2 := by
    have h14 : (1 : ℝ) / a ≤ 1 / 2 := by
      rw [div_le_div_iff₀ ha0 (by norm_num)]; linarith
    have he12 : Real.exp (1 / 2 : ℝ) < 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [hsq, Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
    calc Real.exp (1 / a) ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr h14
      _ ≤ 2 := le_of_lt he12
  intro n hn k
  have hn1 : 1 ≤ n := hF n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnY : 2 * a ^ 8 ≤ (n : ℝ) := hygate n hn
  set Rk : ℝ := (n : ℝ) * Real.exp (-((k : ℝ) / a)) with hRkdef
  set Lk : ℝ := (n : ℝ) * Real.exp (-(((k : ℝ) + 1) / a)) with hLkdef
  have hLk0 : (0 : ℝ) < Lk := by rw [hLkdef]; exact mul_pos hn0 (Real.exp_pos _)
  have hRk0 : (0 : ℝ) < Rk := by rw [hRkdef]; exact mul_pos hn0 (Real.exp_pos _)
  have hRL : Rk = Lk * Real.exp (1 / a) := by
    rw [hLkdef, hRkdef, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hLkRk2 : Lk = Rk * Real.exp (-(1 / a)) := by
    rw [hLkdef, hRkdef, mul_assoc, ← Real.exp_add]; congr 2; ring
  set Fib := (F.filter (· < n)).filter
      (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k) with hFibdef
  have hmem : ∀ m ∈ Fib, Lk < (m : ℝ) ∧ (m : ℝ) ≤ Rk := by
    intro m hm
    rw [hFibdef, Finset.mem_filter, Finset.mem_filter] at hm
    obtain ⟨⟨hmF, hmn⟩, hk⟩ := hm
    have hm1 : 1 ≤ m := hF m hmF
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hloglt : Real.log (m : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log hm0 (by exact_mod_cast hmn)
    have hx0 : (0 : ℝ) ≤ a * (Real.log (n : ℝ) - Real.log (m : ℝ)) :=
      mul_nonneg ha0.le (by linarith)
    obtain ⟨hkle, hklt⟩ := (Nat.floor_eq_iff hx0).mp hk
    refine ⟨?_, ?_⟩
    · have hlt2 : Real.log (n : ℝ) - Real.log (m : ℝ) < ((k : ℝ) + 1) / a := by
        rw [lt_div_iff₀ ha0, mul_comm]; linarith [hklt]
      have hlogm_gt : Real.log (n : ℝ) - ((k : ℝ) + 1) / a < Real.log (m : ℝ) := by linarith
      rw [hLkdef]
      calc (n : ℝ) * Real.exp (-(((k : ℝ) + 1) / a))
          = Real.exp (Real.log (n : ℝ) - ((k : ℝ) + 1) / a) := by
            rw [show Real.log (n : ℝ) - ((k : ℝ) + 1) / a
                  = Real.log (n : ℝ) + (-(((k : ℝ) + 1) / a)) from by ring,
              Real.exp_add, Real.exp_log hn0]
        _ < Real.exp (Real.log (m : ℝ)) := Real.exp_lt_exp.mpr hlogm_gt
        _ = (m : ℝ) := Real.exp_log hm0
    · have hge2 : (k : ℝ) / a ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
        rw [div_le_iff₀ ha0, mul_comm]; linarith [hkle]
      have hlogm_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - (k : ℝ) / a := by linarith
      rw [hRkdef]
      calc (m : ℝ) = Real.exp (Real.log (m : ℝ)) := (Real.exp_log hm0).symm
        _ ≤ Real.exp (Real.log (n : ℝ) - (k : ℝ) / a) := Real.exp_le_exp.mpr hlogm_le
        _ = (n : ℝ) * Real.exp (-((k : ℝ) / a)) := by
            rw [show Real.log (n : ℝ) - (k : ℝ) / a
                  = Real.log (n : ℝ) + (-((k : ℝ) / a)) from by ring,
              Real.exp_add, Real.exp_log hn0]
  have hsub : Fib ⊆ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊ := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := hmem m hm
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hLk0.le).mpr hlo, Nat.le_floor hhi⟩
  have hfib_le : (∑ m ∈ Fib, ‖b m‖)
      ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m := by
    calc (∑ m ∈ Fib, ‖b m‖) ≤ ∑ m ∈ Fib, ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum (fun m _ => hb m)
      _ ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hRHS0 : (0 : ℝ) ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) :=
    mul_nonneg (div_nonneg (mul_nonneg hCb0 hn0.le) ha0.le) (Real.exp_nonneg _)
  have h1me : 1 - Real.exp (-(1 / a)) ≤ 1 / a := by linarith [Real.add_one_le_exp (-(1 / a))]
  have hHk_bound : Rk - Lk ≤ (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by
    rw [hLkRk2]
    have hfac : Rk - Rk * Real.exp (-(1 / a)) = Rk * (1 - Real.exp (-(1 / a))) := by ring
    rw [hfac]
    calc Rk * (1 - Real.exp (-(1 / a))) ≤ Rk * (1 / a) :=
          mul_le_mul_of_nonneg_left h1me hRk0.le
      _ = (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by rw [hRkdef]; ring
  rcases Finset.eq_empty_or_nonempty Fib with hE | ⟨m₀, hm₀⟩
  · rw [hE, Finset.sum_empty]; exact hRHS0
  · have hm₀' := hm₀
    rw [hFibdef, Finset.mem_filter, Finset.mem_filter] at hm₀'
    obtain ⟨⟨hm₀F, -⟩, -⟩ := hm₀'
    have hRkY : 2 * a ^ 8 ≤ Rk := le_trans (hygate m₀ hm₀F) (hmem m₀ hm₀).2
    have ha8_65536 : (65536 : ℝ) ≤ a ^ 8 := by
      calc (65536 : ℝ) = 4 ^ 8 := by norm_num
        _ ≤ a ^ 8 := by gcongr
    have hLk_ge_a8 : a ^ 8 ≤ Lk := by
      have hLkRk : Lk = Rk / Real.exp (1 / a) := by
        rw [hRL, mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]
      rw [hLkRk, le_div_iff₀ (Real.exp_pos _)]
      linarith [hRkY, mul_le_mul_of_nonneg_left hexp_le2 (pow_nonneg ha0.le 8)]
    have hLk_65536 : (65536 : ℝ) ≤ Lk := le_trans ha8_65536 hLk_ge_a8
    have hHa : Rk - Lk ≤ Lk := by
      have h2 : Lk * Real.exp (1 / a) ≤ Lk * 2 := mul_le_mul_of_nonneg_left hexp_le2 hLk0.le
      rw [hRL]; linarith [h2]
    have hHk_ge : Lk / a ≤ Rk - Lk := by
      have hEexp : 1 / a + 1 ≤ Real.exp (1 / a) := Real.add_one_le_exp (1 / a)
      have hkey : Lk / a ≤ Lk * (Real.exp (1 / a) - 1) := by
        rw [div_eq_mul_inv, ← one_div]
        exact mul_le_mul_of_nonneg_left (by linarith [hEexp]) hLk0.le
      calc Lk / a ≤ Lk * (Real.exp (1 / a) - 1) := hkey
        _ = Rk - Lk := by rw [hRL]; ring
    have hs8 : Real.sqrt (Real.sqrt (Real.sqrt Lk)) ^ 8 = Lk := by
      set s := Real.sqrt (Real.sqrt (Real.sqrt Lk)) with hs
      have h2 : s ^ 2 = Real.sqrt (Real.sqrt Lk) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have h4 : s ^ 4 = Real.sqrt Lk := by
        have hpow : s ^ 4 = (s ^ 2) ^ 2 := by ring
        rw [hpow, h2, Real.sq_sqrt (Real.sqrt_nonneg _)]
      have hpow8 : s ^ 8 = (s ^ 4) ^ 2 := by ring
      rw [hpow8, h4, Real.sq_sqrt hLk0.le]
    have hsa : a ≤ Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
      le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (Real.sqrt_nonneg _)
        (by rw [hs8]; exact hLk_ge_a8)
    have hHr : Lk ≤ (Rk - Lk) * Real.sqrt (Real.sqrt (Real.sqrt Lk)) := by
      calc Lk = Lk / a * a := by field_simp
        _ ≤ Lk / a * Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
            mul_le_mul_of_nonneg_left hsa (div_nonneg hLk0.le ha0.le)
        _ ≤ (Rk - Lk) * Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
            mul_le_mul_of_nonneg_right hHk_ge (Real.sqrt_nonneg _)
    have hshort := hCbound Lk (Rk - Lk) hLk_65536 hHr hHa
    have hfloor : ⌊Lk + (Rk - Lk)⌋₊ = ⌊Rk⌋₊ := by congr 1; ring
    rw [hfloor] at hshort
    calc (∑ m ∈ Fib, ‖b m‖)
        ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m := hfib_le
      _ ≤ Cb * (Rk - Lk) := hshort
      _ ≤ Cb * ((n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :=
          mul_le_mul_of_nonneg_left hHk_bound hCb0
      _ = Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by ring

/-- `offdiag_widthA_final` at a named constant: the symmetrization of
`offdiag_widthA_sharp` against a supplied `hband`. -/
private lemma offdiag_finalC {F : Finset ℕ} {b : ℕ → ℂ} {c a Cb : ℝ}
    (hc : 1 ≤ c) (hca : c ≤ a) (hF : ∀ n ∈ F, 1 ≤ n) (hCb0 : 0 ≤ Cb)
    (hband : ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :
    (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      ≤ 4 * Cb / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  have hsharp := offdiag_widthA_sharp hc hca hF hCb0 hband
  have hsymm : ∀ m n : ℕ,
      ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c * Real.exp (-(a * |Real.log m - Real.log n|))
        = ‖b n‖ * ‖b m‖ / ((n * m : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log n - Real.log m|)) := by
    intro m n
    rw [mul_comm (‖b m‖) (‖b n‖), Nat.mul_comm m n, abs_sub_comm (Real.log m) (Real.log n)]
  calc (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0) := sum_ne_eq_two_ltC hsymm
    _ ≤ 2 * (2 * Cb / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left hsharp (by norm_num)
    _ = 4 * Cb / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by ring

/-- `offdiag_widthA_final_low` at a named constant. -/
private lemma offdiag_finalC_low {F : Finset ℕ} {b : ℕ → ℂ} {c a Q Cb : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hca : c ≤ a) (hF : ∀ n ∈ F, 1 ≤ n) (hCb0 : 0 ≤ Cb)
    (hQ : ∀ n ∈ F, (n : ℝ) ≤ Q)
    (hband : ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :
    (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      ≤ 4 * Cb / a * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
  have hsharp := offdiag_widthA_sharp_low hc0 hc1 hca hF hCb0 hQ hband
  have hsymm : ∀ m n : ℕ,
      ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c * Real.exp (-(a * |Real.log m - Real.log n|))
        = ‖b n‖ * ‖b m‖ / ((n * m : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log n - Real.log m|)) := by
    intro m n
    rw [mul_comm (‖b m‖) (‖b n‖), Nat.mul_comm m n, abs_sub_comm (Real.log m) (Real.log n)]
  calc (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0) := sum_ne_eq_two_ltC hsymm
    _ ≤ 2 * (2 * Cb / a * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)) :=
        mul_le_mul_of_nonneg_left hsharp (by norm_num)
    _ = 4 * Cb / a * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by ring

/-- The bilinear collapse of the Plancherel sum.  Verbatim re-derivation of `WidthGrade`'s
private `planch_bilinear_le`. -/
private lemma planch_bilinear_leC {F : Finset ℕ} {b : ℕ → ℂ} {c A Off : ℝ}
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

/-- The `1/A²`-small window diagonal.  Verbatim re-derivation of `WidthGrade`'s private
`diag_le_mass_width`. -/
private lemma diag_le_mass_widthC {F : Finset ℕ} {b : ℕ → ℂ} {c A : ℝ}
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
  have hsq : ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c = (‖b n‖ / (n : ℝ) ^ c) ^ 2 := by
    rw [div_pow, show ((n * n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) from by push_cast; ring,
      Real.mul_rpow hn0.le hn0.le, ← pow_two]
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

/-- `line_moment_grade_width` at a named constant. -/
private lemma line_moment_widthC {F : Finset ℕ} {b : ℕ → ℂ} {c A Cb : ℝ}
    (hCb0 : 0 ≤ Cb) (hc : 1 ≤ c) (hA4 : 4 ≤ A) (hcA : c ≤ A)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ))
    (hband : ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊A * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / A * Real.exp (-((k : ℝ) / A))) :
    (∫ τ : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2))
      ≤ Real.pi / A * ((2 / A ^ 2 + 4 * Cb / (A - c + 1))
          * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hoff := offdiag_finalC hc hcA hF hCb0 hband
  rw [widthA_plancherel F b (c := c) hA0 hF]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (planch_bilinear_leC hoff).trans ?_
  have hdiag := diag_le_mass_widthC (c := c) (A := A) (by linarith) (by linarith) hF hb hygate
  rw [add_mul]
  exact add_le_add hdiag le_rfl

/-- `line_moment_grade_low_width` at a named constant. -/
private lemma line_moment_low_widthC {F : Finset ℕ} {b : ℕ → ℂ} {c A Q Cb : ℝ}
    (hCb0 : 0 ≤ Cb) (hc34 : 3 / 4 ≤ c) (hc1 : c ≤ 1) (hA4 : 4 ≤ A) (hQ1 : 1 ≤ Q)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * A ^ 8 ≤ (n : ℝ)) (hQ : ∀ n ∈ F, (n : ℝ) ≤ Q)
    (hband : ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊A * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / A * Real.exp (-((k : ℝ) / A))) :
    (∫ τ : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (A ^ 2 + τ ^ 2))
      ≤ Real.pi / A * ((2 / A ^ 2 + 4 * Cb / A)
          * (Q ^ (1 - c) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c)) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hcA : c ≤ A := by linarith
  have hoff := offdiag_finalC_low hc0 hc1 hcA hF hCb0 hQ hband
  rw [widthA_plancherel F b (c := c) hA0 hF]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (planch_bilinear_leC hoff).trans ?_
  have hdiag := diag_le_mass_widthC (c := c) (A := A) hc34 (by linarith) hF hb hygate
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

/-- The geometric-mean step on OPAQUE reals.  Re-derivation of `WidthGrade`'s private
`sqrt_mul_sqrt_le`. -/
private lemma sqrt_mul_sqrt_leC {k u v w : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u) (_hv : 0 ≤ v)
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

/-- The closing regrouping on OPAQUE reals.  Re-derivation of `WidthGrade`'s private
`width_final_algebra`. -/
private lemma width_final_algebraC {P Amp Kf Lg Xb XX mn sg : ℝ}
    (hP : 0 ≤ P) (hAmp : 0 ≤ Amp) (hKf : 0 ≤ Kf) (hLg : 0 ≤ Lg) (hmn : 0 ≤ mn)
    (hXb : 0 ≤ Xb) (hcancel : P * Xb ≤ XX) (hms : mn ≤ sg) :
    P * Amp * (Kf * (Lg * Xb * mn)) ≤ Amp * Kf * Lg * XX * sg := by
  have hXX0 : (0 : ℝ) ≤ XX := le_trans (mul_nonneg hP hXb) hcancel
  calc P * Amp * (Kf * (Lg * Xb * mn)) = (Amp * Kf * Lg) * ((P * Xb) * mn) := by ring
    _ ≤ (Amp * Kf * Lg) * (XX * sg) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcancel hms hmn hXX0)
          (by positivity)
    _ = Amp * Kf * Lg * XX * sg := by ring

/-- The `X^β` cancellation at the width face.  Re-derivation of `WidthGrade`'s private
`amp_beta_cancel_widthA`. -/
private lemma amp_beta_cancel_widthAC {X h c₀ α β : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
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

set_option maxHeartbeats 800000 in
-- The A-5 body composes six window-sum estimates in one context; elaborating the folded
-- Dirichlet rewrites plus the geometric-mean `calc` exceeds the default budget by ~10%.
/-- **R-1 core — the width-decoupled `1/σ` bound at a NAMED constant**
(`crossKer_width_sigma_bound_param`).  `WidthGrade.crossKer_width_sigma_bound` with the
short-interval constant supplied from outside, so the SAME `Cb` serves every `(α, β)`. -/
theorem crossKer_width_sigma_bound_param (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ A Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hσ : σ = β + 1 / L)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 4)
    (hA4 : 4 ≤ A) (hAT : A ≤ 2 * (X + h) / h)
    (hygate : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, 2 * A ^ 8 ≤ (n : ℝ)) :
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
  -- THE UNIFORM BAND DATUM: one `Cb`, independent of the line `c`
  have hband := hband_discharge_param (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊)
    (b := lambdaLin (restrictAbove y g)) (a := A) hCb0 hCbound hA4 hF hb hygate
  set Sm : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hSmdef
  set Sp : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hSpdef
  have hSm0 : (0 : ℝ) ≤ Sm := Finset.sum_nonneg (fun n _ => by positivity)
  have hSp0 : (0 : ℝ) ≤ Sp := Finset.sum_nonneg (fun n _ => by positivity)
  have hXβ0 : (0 : ℝ) ≤ X ^ β := Real.rpow_nonneg hX0.le _
  have hXβ1 : (1 : ℝ) ≤ X ^ β := Real.one_le_rpow hX hβ0
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
  have hBm : (∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * (2 / A ^ 2 + 8 * Cb / A) * (X ^ β * Sm) := by
    rw [hfoldM]
    have hkey : (∫ τ : ℝ, ‖∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ - β : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
          / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 8 * Cb / A) * (X ^ β * Sm)) := by
      rcases le_or_gt (c₀ - β) 1 with hlow | hhigh
      · have hgr := line_moment_low_widthC
          (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
          (c := c₀ - β) (A := A) (Q := X / y) hCb0
          (by rw [hc₀]; linarith) hlow hA4 hQ1 hF hb hygate hQ hband
        refine hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have hexp : (1 : ℝ) - (c₀ - β) = β - 1 / L := by rw [hc₀]; ring
        have hexc : (X / y) ^ (1 - (c₀ - β)) ≤ X ^ β := by
          rw [hexp]
          have hβL : 1 / L ≤ β := by rw [hc₀] at hlow; linarith
          calc (X / y) ^ (β - 1 / L) ≤ X ^ (β - 1 / L) :=
                Real.rpow_le_rpow (by positivity) hXy_le (by linarith)
            _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
        have hcoef : 2 / A ^ 2 + 4 * Cb / A ≤ 2 / A ^ 2 + 8 * Cb / A := by
          have h48 : 4 * Cb / A ≤ 8 * Cb / A := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hA0.le)
          exact add_le_add le_rfl h48
        exact mul_le_mul hcoef (mul_le_mul_of_nonneg_right hexc hSm0)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) hSm0) (by positivity)
      · have hgr := line_moment_widthC
          (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
          (c := c₀ - β) (A := A) hCb0 hhigh.le hA4 (by rw [hc₀]; linarith) hF hb hygate hband
        refine hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have hden : A / 2 ≤ A - (c₀ - β) + 1 := by rw [hc₀]; linarith
        have hcoef : 4 * Cb / (A - (c₀ - β) + 1) ≤ 8 * Cb / A := by
          rw [div_le_div_iff₀ (by linarith) hA0]
          nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ 8 * Cb)]
        refine mul_le_mul (by linarith) ?_ hSm0 (by positivity)
        calc Sm = 1 * Sm := (one_mul _).symm
          _ ≤ X ^ β * Sm := mul_le_mul_of_nonneg_right hXβ1 hSm0
    exact hkey.trans (le_of_eq (mul_assoc _ _ _).symm)
  -- the HIGH leg
  have hBp : (∫ τ : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * (2 / A ^ 2 + 8 * Cb / A) * Sp := by
    rw [hfoldP]
    have hgr := line_moment_widthC
      (F := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (b := lambdaLin (restrictAbove y g))
      (c := c₀ + β) (A := A) hCb0 (by rw [hc₀]; linarith) hA4 (by rw [hc₀]; linarith)
      hF hb hygate hband
    have hkey : (∫ τ : ℝ, ‖∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          lambdaLin (restrictAbove y g) n / (n : ℂ) ^ (((c₀ + β : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
          / (A ^ 2 + τ ^ 2))
        ≤ Real.pi / A * ((2 / A ^ 2 + 8 * Cb / A) * Sp) := by
      refine hgr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hden : A / 2 ≤ A - (c₀ + β) + 1 := by rw [hc₀]; linarith
      have hcoef : 4 * Cb / (A - (c₀ + β) + 1) ≤ 8 * Cb / A := by
        rw [div_le_div_iff₀ (by linarith) hA0]
        nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : (0 : ℝ) ≤ 8 * Cb)]
      exact mul_le_mul_of_nonneg_right (by linarith) hSp0
    exact hkey.trans (le_of_eq (mul_assoc _ _ _).symm)
  have hKfac0 : (0 : ℝ) ≤ Real.pi / A * (2 / A ^ 2 + 8 * Cb / A) := by positivity
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
  have hgeo : Real.sqrt (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      * Real.sqrt (∫ τ : ℝ,
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2 / (A ^ 2 + τ ^ 2))
      ≤ Real.pi / A * (2 / A ^ 2 + 8 * Cb / A)
          * (9 * (Real.log 4 + 4) * X ^ β * min L (1 / σ)) := by
    refine le_trans (mul_le_mul (Real.sqrt_le_sqrt hBm) (Real.sqrt_le_sqrt hBp)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
    exact sqrt_mul_sqrt_leC hKfac0 (mul_nonneg hXβ0 hSm0) hSp0 hW0 hstep
  have hAmp0 : (0 : ℝ) ≤ 4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h) := by
    positivity
  have hpre0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β)
      * (4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h)) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) hAmp0
  refine (crossKer_grade_width (g := g) (y := y) (t₀ := t₀) (A := A) hX hh hc hA0 hAT).trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left hgeo hpre0) ?_
  exact width_final_algebraC (Real.rpow_nonneg hXh0.le _) hAmp0 hKfac0 hlog9 hmin0 hXβ0
    (amp_beta_cancel_widthAC hX hh hβ0) (min_le_right _ _)

/-- **R-1 — the `β`-UNIFORM width bound** (`crossKer_width_sigma_bound_uniform`).  One `Cb`,
fixed before the `(α, β)` quantifiers: the shape `bridge_adapter` needs. -/
theorem crossKer_width_sigma_bound_uniform (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ A : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h)
    (hA4 : 4 ≤ A) (hAT : A ≤ 2 * (X + h) / h)
    (hygate : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, 2 * A ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ α β σ : ℝ, 0 ≤ α → 0 ≤ β → α + β ≤ 1 / 4 → σ = β + 1 / L →
      crossKer g X h y c₀ t₀ α β
        ≤ ((4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h))
            * (Real.pi / A * (2 / A ^ 2 + 8 * Cb / A))
            * (9 * (Real.log 4 + 4))
            * ((X + h) ^ c₀ * (X + h) ^ (-α))) * (1 / σ) := by
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  exact ⟨Cb, hCb0, fun α β σ hα0 hβ0 hαβ hσ =>
    crossKer_width_sigma_bound_param g hg hCb0 hCbound hL hL3 hy hyX hc₀ hh hσ
      hα0 hβ0 hαβ hA4 hAT hygate⟩

/-! ## §2 — the pin arithmetic: the bracket at an ABSOLUTE numeral

Two moves turn `crossKer_width_sigma_bound_param`'s exit into a `β`-free amplitude with an
absolute constant:

* **`β` out of the bracket** — the width face's `cw = c₀−α−β` is `≥ 3/4` on the pin's
  `α + β ≤ 1/4` (with `c₀ = 1+1/L ≥ 1`), so `4T₀²/cw ≤ (16/3)·T₀²` uniformly;
* **the numeral** — at `h = X/√L`, `y = L⁴`, `A = (y/2)^{1/8}` and `L ≥ 64`:
  `T₀ = 2(√L+1) ≤ (9/4)√L`, `A ≥ √L/2`, so
  `(16/3 T₀² + 2T₀) ≤ 28L`, `(π/A)(2/A² + 8Cb/A) ≤ 128(1+Cb)/L`, `9(log 4+4) ≤ 49`.
  The `L`'s cancel: the bracket is `≤ 28·128·49·(1+Cb) = 175616·(1+Cb)` — **absolute**.

Sharpness is irrelevant here (the honest page is `≈ 638·Cb`); what matters is that the
numeral carries no `L`. -/

/-- The pin's `β`-free BRACKET: `crossKer_width_sigma_bound`'s amplitude with `cw` replaced
by its floor `3/4` and the width at the pin `A = (y/2)^{1/8}`. -/
def widthKampBr (Cb X h y : ℝ) : ℝ :=
  (4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h))
    * (Real.pi / (y / 2) ^ (1 / 8 : ℝ)
      * (2 / ((y / 2) ^ (1 / 8 : ℝ)) ^ 2 + 8 * Cb / (y / 2) ^ (1 / 8 : ℝ)))
    * (9 * (Real.log 4 + 4))

/-- The pin's `α`-free kernel amplitude at the WIDTH face — the width-route replacement for
`RHSGrade.rhsKamp`.  Note the absence of the `L` factor `rhsKamp` carries: that missing `L`
is the whole content of the width-decoupled route. -/
def widthKamp (Cb X h y c₀ : ℝ) : ℝ := widthKampBr Cb X h y * (X + h) ^ c₀

/-- Regrouping on OPAQUE reals (so no `ring` ever meets a window sum or an integral). -/
private lemma pin_regroup {a b Kf Lg P Q S : ℝ} (hab : a ≤ b) (hKf : 0 ≤ Kf) (hLg : 0 ≤ Lg)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS : 0 ≤ S) :
    a * Kf * Lg * (P * Q) * S ≤ b * Kf * Lg * P * Q * S := by
  have hlhs : a * Kf * Lg * (P * Q) * S = a * (Kf * Lg * (P * Q) * S) := by ring
  have hrhs : b * Kf * Lg * P * Q * S = b * (Kf * Lg * (P * Q) * S) := by ring
  rw [hlhs, hrhs]
  exact mul_le_mul_of_nonneg_right hab (by positivity)

/-- **R-2a — the pin's elementary width gates.**  At `h = X/√L` and `y = L⁴` with `L ≥ 64`:
`h > 0`, `T₀ = 2(√L+1)`, `y ≥ 131072`, and `y ≤ 2T₀⁸`. -/
theorem pin_width_gates {X h y L : ℝ} (hL64 : 64 ≤ L) (hX0 : 0 < X)
    (hh : h = X / Real.sqrt L) (hy : y = L ^ 4) :
    0 < h ∧ 2 * (X + h) / h = 2 * (Real.sqrt L + 1) ∧ (131072 : ℝ) ≤ y
      ∧ y ≤ 2 * (2 * (X + h) / h) ^ 8 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hT : 2 * (X + h) / h = 2 * (Real.sqrt L + 1) := by
    rw [hh]; field_simp
  refine ⟨hh0, hT, ?_, ?_⟩
  · rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  · rw [hT, hy]
    have hpow : (2 * Real.sqrt L) ^ 8 ≤ (2 * (Real.sqrt L + 1)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 8
    have hval : (2 * Real.sqrt L) ^ 8 = 256 * L ^ 4 := by
      have h2 : (Real.sqrt L) ^ 8 = L ^ 4 := by
        have h4 : (Real.sqrt L) ^ 8 = ((Real.sqrt L) * (Real.sqrt L)) ^ 4 := by ring
        rw [h4, hsq]
      rw [mul_pow, h2]; norm_num
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 2 * (Real.sqrt L + 1)) 8]

/-- **R-2 — the pin bracket at an ABSOLUTE numeral** (`width_pin_bracket_le`).  With
`h = X/√L`, `y = L⁴` and `L ≥ 64`:

  `(4T₀²/(3/4) + 2T₀)·(π/A)(2/A² + 8Cb/A)·9(log 4+4) ≤ 175616·(1 + Cb)`,

`T₀ = 2(X+h)/h`, `A = (y/2)^{1/8}`.  **No `L` survives**: the bracket's `T₀² ≍ L` is exactly
cancelled by the width's `A² ≍ L`, which is the width pin's entire purpose. -/
theorem width_pin_bracket_le {Cb X h y L : ℝ} (hCb0 : 0 ≤ Cb) (hL64 : 64 ≤ L) (hX0 : 0 < X)
    (hh : h = X / Real.sqrt L) (hy : y = L ^ 4) :
    widthKampBr Cb X h y ≤ 175616 * (1 + Cb) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  obtain ⟨hh0, hT, -, -⟩ := pin_width_gates hL64 hX0 hh hy
  set A : ℝ := (y / 2) ^ (1 / 8 : ℝ) with hAdef
  have hy0 : (0 : ℝ) < y / 2 := by rw [hy]; positivity
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; exact Real.rpow_nonneg hy0.le _
  have hA8 : A ^ 8 = y / 2 := by
    rw [hAdef, ← Real.rpow_natCast ((y / 2) ^ (1 / 8 : ℝ)) 8, ← Real.rpow_mul hy0.le]
    norm_num
  -- the width floor `A ≥ √L/2`
  have hAlow : Real.sqrt L / 2 ≤ A := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hA0 ?_
    rw [hA8, hy]
    have h2 : (Real.sqrt L / 2) ^ 8 = L ^ 4 / 256 := by
      have h4 : (Real.sqrt L) ^ 8 = L ^ 4 := by
        have h4' : (Real.sqrt L) ^ 8 = ((Real.sqrt L) * (Real.sqrt L)) ^ 4 := by ring
        rw [h4', hsq]
      rw [div_pow, h4]; norm_num
    rw [h2]; nlinarith [pow_nonneg hL0.le 4]
  have hA4 : (4 : ℝ) ≤ A := by linarith
  have hApos : (0 : ℝ) < A := by linarith
  have hA2 : L / 4 ≤ A ^ 2 := by nlinarith
  have hA3 : L ≤ A * A ^ 2 := by nlinarith
  -- factor 1: the `T₀` bracket
  have hLs : 8 * Real.sqrt L ≤ L := by
    have hprod : (0 : ℝ) ≤ (Real.sqrt L - 8) * Real.sqrt L :=
      mul_nonneg (by linarith) hs0.le
    nlinarith [hsq]
  have hF1 : 4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h) ≤ 28 * L := by
    rw [hT]
    have hkey : 4 * (2 * (Real.sqrt L + 1)) ^ 2 / (3 / 4) + 2 * (2 * (Real.sqrt L + 1))
        = 64 / 3 * (Real.sqrt L + 1) ^ 2 + 4 * (Real.sqrt L + 1) := by ring
    have hexp : (Real.sqrt L + 1) ^ 2 = L + 2 * Real.sqrt L + 1 := by
      have hsq' : (Real.sqrt L + 1) ^ 2
          = Real.sqrt L * Real.sqrt L + 2 * Real.sqrt L + 1 := by ring
      rw [hsq', hsq]
    rw [hkey, hexp]
    linarith
  have hF1nn : (0 : ℝ) ≤ 4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h) := by
    rw [hT]; positivity
  -- factor 2: the width face
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hF2 : Real.pi / A * (2 / A ^ 2 + 8 * Cb / A) ≤ 128 * (1 + Cb) / L := by
    have hsplit : Real.pi / A * (2 / A ^ 2 + 8 * Cb / A)
        = 2 * Real.pi / (A * A ^ 2) + 8 * Real.pi * Cb / A ^ 2 := by
      field_simp
    rw [hsplit]
    have h1 : 2 * Real.pi / (A * A ^ 2) ≤ 8 / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]
      nlinarith [hA3, hL0]
    have h2 : 8 * Real.pi * Cb / A ^ 2 ≤ 128 * Cb / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]
      nlinarith [mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ 128 * Cb),
        mul_nonneg hCb0 hL0.le, hpi4]
    have h3 : 8 / L + 128 * Cb / L = (8 + 128 * Cb) / L := by ring
    have h4 : (8 + 128 * Cb) / L ≤ 128 * (1 + Cb) / L := by
      rw [div_le_div_iff₀ hL0 hL0]; nlinarith
    linarith
  have hF2nn : (0 : ℝ) ≤ Real.pi / A * (2 / A ^ 2 + 8 * Cb / A) := by positivity
  -- factor 3: the window-bridge constant
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) from by norm_num, Real.log_pow]; push_cast; ring
    rw [h2]; linarith [Real.log_two_lt_d9]
  have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hF3 : 9 * (Real.log 4 + 4) ≤ 49 := by linarith
  have hF3nn : (0 : ℝ) ≤ 9 * (Real.log 4 + 4) := by linarith
  -- the product: the two `L`'s cancel
  unfold widthKampBr
  calc (4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h))
        * (Real.pi / A * (2 / A ^ 2 + 8 * Cb / A)) * (9 * (Real.log 4 + 4))
      ≤ (28 * L) * (128 * (1 + Cb) / L) * 49 := by
        refine mul_le_mul (mul_le_mul hF1 hF2 hF2nn (by positivity)) hF3 hF3nn (by positivity)
    _ = 175616 * (1 + Cb) := by field_simp; ring

/-- **R-2b — `crossKer` at the WIDTH PIN, `β`-free** (`crossKer_width_pin_const`).  The
`bridge_adapter` shape: `crossKer α β ≤ (Kamp·(X+h)^{−α})·(1/σ)` with `Kamp` free of both
`β` and `σ`, and its short-interval constant fixed OUTSIDE the `(α,β)` quantifiers. -/
theorem crossKer_width_pin_const (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 131072 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hσ : σ = β + 1 / L)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 4)
    (hyT : y ≤ 2 * (2 * (X + h) / h) ^ 8) :
    crossKer g X h y c₀ t₀ α β
      ≤ widthKamp Cb X h y c₀ * (X + h) ^ (-α) * (1 / σ) := by
  have hX : (1 : ℝ) ≤ X := le_trans (by linarith) hyX
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  have hT₀0 : (0 : ℝ) < 2 * (X + h) / h := div_pos (by linarith) hh
  obtain ⟨-, hA4, hAT, hygate⟩ := width_pin_gates (X := X) hy hT₀0 hyT rfl
  have hbd := crossKer_width_sigma_bound_param g hg (t₀ := t₀) hCb0 hCbound hL hL3
    (by linarith) hyX hc₀ hh hσ hα0 hβ0 hαβ hA4 hAT hygate
  refine hbd.trans ?_
  have hcw : (3 : ℝ) / 4 ≤ c₀ - α - β := by rw [hc₀]; linarith
  have hcw0 : (0 : ℝ) < c₀ - α - β := by linarith
  have hbr : 4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β) + 2 * (2 * (X + h) / h)
      ≤ 4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h) := by
    have hd : 4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β)
        ≤ 4 * (2 * (X + h) / h) ^ 2 / (3 / 4) := by
      rw [div_le_div_iff₀ hcw0 (by norm_num)]
      nlinarith [sq_nonneg (2 * (X + h) / h)]
    linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hstep := pin_regroup (a := 4 * (2 * (X + h) / h) ^ 2 / (c₀ - α - β)
      + 2 * (2 * (X + h) / h))
    (b := 4 * (2 * (X + h) / h) ^ 2 / (3 / 4) + 2 * (2 * (X + h) / h))
    (Kf := Real.pi / (y / 2) ^ (1 / 8 : ℝ)
      * (2 / ((y / 2) ^ (1 / 8 : ℝ)) ^ 2 + 8 * Cb / (y / 2) ^ (1 / 8 : ℝ)))
    (Lg := 9 * (Real.log 4 + 4)) (P := (X + h) ^ c₀) (Q := (X + h) ^ (-α))
    (S := 1 / σ) hbr (by positivity) (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)])
    (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _) (by positivity)
  exact hstep

/-! ## §3 — A-6 proper: the grade at scale, and the `hRHS` exit at an ABSOLUTE `C₁`

`RHSGrade`'s §4/§5 assembly, re-run against the width face.  Everything upstream of the
amplitude is unchanged (`joint_cs_factoring`, `joint_supF_pin`, `bridge_adapter`,
`joint_sigma_integral`, `alpha_rpow_integral_le`); only `rhsKamp` — which carried the extra
`L` — is replaced by `widthKamp`, which does not.  The exit `hRHS_discharged_const` has
`hRHS_discharged`'s conclusion byte-for-byte, with `C₁` EXHIBITED (no longer a socket). -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `RHSGrade`'s private `four_log_le_self`. -/
private lemma four_log_le_selfC {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- The pin's elementary arithmetic at the `e^{64}` gate: everything `beta_integral_pin_const`
and `rhs_grade_at_scale_const` need about `(k, L, y, η)`. -/
private lemma pin_basic64 {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ 0 < Real.log y ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L ≤ η ∧ L ^ 4 ≤ k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hy131072 : (131072 : ℝ) ≤ y := by
    rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  refine ⟨hk0, hL64, hy131072, hlogy0, by rw [hη]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_le_div_iff₀ hL0 (by linarith)]
    linarith [four_log_le_selfC hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfC hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-- Interval-integrability of the σ-integrand `Fbound σ/σ`.  Re-derivation of `RHSGrade`'s
private `rhs_sigma_div_integrable`. -/
private lemma rhs_sigma_div_integrableC {M L b : ℝ} (hL0 : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable (fun σ : ℝ => rhsFbound M L σ / σ) volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id
    (fun σ hσ => (hpos σ hσ).ne')
  · exact continuousOn_const.mul
      (continuousOn_const.div continuousOn_id (fun σ hσ => (hpos σ hσ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL0).ne'))

/-- Interval-integrability of `bridge_adapter`'s translated integrand.  Re-derivation of
`RHSGrade`'s private `rhs_shift_integrable`. -/
private lemma rhs_shift_integrableC {M L η Kα : ℝ} (hL0 : 0 < L) (hη0 : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => Kα * (rhsFbound M L (β + 1 / L) / (β + 1 / L))) volume 0 η := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ β ∈ Set.uIcc (0 : ℝ) η, (0 : ℝ) < β + 1 / L := by
    intro β hβ
    rw [Set.uIcc_of_le hη0, Set.mem_Icc] at hβ
    linarith [hβ.1]
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul ?_ ?_) ?_
    (fun β hβ => (hpos β hβ).ne'))
  · exact continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) (fun β hβ => (hpos β hβ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      (fun β hβ => (mul_pos (hpos β hβ) hL0).ne'))
  · fun_prop

/-- Continuity of `α ↦ a^{−α}`.  Re-derivation of `RHSGrade`'s private
`continuous_rpow_neg`. -/
private lemma continuous_rpow_negC {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative on the pin's data. -/
private lemma widthKamp_nonneg {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-- **A-6a — the per-`α` β-integral at the WIDTH face** (`beta_integral_pin_const`).
`RHSGrade.beta_integral_pin` with `crossKer_width_pin_const` in place of
`crossKer_sharp_sigma_bound`: the amplitude loses its `L`, everything else is unchanged. -/
theorem beta_integral_pin_const (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀' M k L c₀ y η h α : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hyk : y ≤ k) (hM0 : 0 ≤ M)
    (hα0 : 0 ≤ α) (hαη : α ≤ η)
    (hIβ : IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L)
        * crossKer g k h y c₀ t₀' α β) volume 0 η) :
    (∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L) * crossKer g k h y c₀ t₀' α β)
      ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L := by
  obtain ⟨hk0, hL64, hy131072, _hlogy0, hη0, hη8, hLη, -⟩ := pin_basic64 hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  obtain ⟨hh0, -, -, hyT⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hK0 : (0 : ℝ) ≤ widthKamp Cb k h y c₀ * (k + h) ^ (-α) :=
    mul_nonneg (widthKamp_nonneg hCb0 hk0 hh0 hy0) (Real.rpow_nonneg hkh0.le _)
  have hcross : ∀ β ∈ Icc (0 : ℝ) η,
      crossKer g k h y c₀ t₀' α β
        ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * (1 / (β + 1 / L)) := by
    intro β hβ
    exact crossKer_width_pin_const g hg hCb0 hCbound hL (by linarith) hy131072 hyk hc₀ hh0
      rfl hα0 hβ.1 (by linarith [hβ.2]) hyT
  have hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ rhsFbound M L (β + 1 / L) := by
    intro β hβ
    exact rhsFbound_nonneg M L (by linarith [hβ.1])
  have hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ rhsFbound M L σ := by
    intro σ hσ
    exact rhsFbound_nonneg M L (lt_of_lt_of_le hLinv0 hσ.1)
  have hIσ := rhs_sigma_div_integrableC (M := M) (L := L) (b := 2 * η) hL0 (by linarith)
  have hBA := bridge_adapter (g := g) (X := k) (h := h) (y := y) (c₀ := c₀) (t₀ := t₀')
    (L := L) (η := η) (Kα := widthKamp Cb k h y c₀ * (k + h) ^ (-α)) (α := α)
    (supF := fun _ β => rhsFbound M L (β + 1 / L)) (Fbound := rhsFbound M L)
    hL0 hLη hK0 hsup0 hcross (fun β _ => le_rfl) hFnn hIβ
    (rhs_shift_integrableC hL0 hη0.le) hIσ
  refine le_trans hBA ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hlogk3 : (3 : ℝ) ≤ Real.log k := by rw [← hL]; linarith
  rw [hL]
  exact joint_sigma_integral (Fbound := rhsFbound M (Real.log k))
    (c := 1 / (2 * Real.exp 1)) (X := k) (b := 2 * η) (M := M) (CSF := rhsCSF)
    (by positivity)
    (by
      rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring,
        div_lt_one (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9])
    hlogk3 hM0 rhsCSF_pos.le (by rw [← hL]; linarith) (by rw [← hL]; exact hIσ)
    (fun σ _ => le_rfl)

/-- **THE ASSEMBLED GRADE AT THE WIDTH FACE.**  `RHSGrade.rhsAgrade` with `widthKamp` in
place of `rhsKamp`: `Agrade = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·Kamp`, and `Kamp` carries no
`L`.  At the pin this is `≍ C·k` — see `rhsAgradeConst_le`. -/
def rhsAgradeConst (Cb X h y c₀ : ℝ) : ℝ :=
  (1 / Real.pi) * rhsCSF
    * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
    * widthKamp Cb X h y c₀

/-- **A-6 — THE GRADE AT SCALE `k`, ABSOLUTE** (`rhs_grade_at_scale_const`).
`RHSGrade.rhs_grade_at_scale` re-run against the width face:

  `‖prop21RHS g' t₀' k h c₀ y η‖ ≤ Agrade_const·e^{−(1/(2e))·M}`,
  `Agrade_const = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·widthKamp`.

The four integrability sockets are carried, exactly as upstream; the `M`-shape is free. -/
theorem rhs_grade_at_scale_const (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀' M k L c₀ y η h : ℝ} (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hyk : y ≤ k) (hM0 : 0 ≤ M)
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hIβ : ∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L)
        * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β) volume 0 η)
    (hIβ' : ∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
        (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand
          (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y α β t‖) volume 0 η)
    (hIα : IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
        * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β) volume 0 η)
    (hIα' : IntervalIntegrable (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
        ∫ t, jointIntegrand (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y α β t‖)
        volume 0 η) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ rhsAgradeConst Cb k h y c₀ * Real.exp (-(1 / (2 * Real.exp 1)) * M) := by
  obtain ⟨hk0, hL64, hy131072, _hlogy0, hη0, hη8, _hLη, -⟩ := pin_basic64 hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLne : L ≠ 0 := ne_of_gt hL0
  obtain ⟨hh0, -, -, -⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk3 : Real.exp 3 ≤ k := by
    have h3 : Real.exp 3 ≤ Real.exp 64 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hKamp0 : (0 : ℝ) ≤ widthKamp Cb k h y c₀ := widthKamp_nonneg hCb0 hk0 hh0 hy0
  have hG0 : (0 : ℝ) ≤ rhsSigmaG M L := by
    unfold rhsSigmaG
    have hE : (0 : ℝ) ≤ Real.exp (1 / (2 * Real.exp 1) * 48)
        / (1 - 2 * (1 / (2 * Real.exp 1))) := by
      have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
        rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
        have h1 : 1 / Real.exp 1 < 1 := by
          rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
        linarith
      positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  have hJ1 := joint_cs_factoring (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
    (t₀ := t₀') (X := k) (h := h) (c₀ := c₀) (y := y) (η := η)
    (supF := fun _ β => rhsFbound M L (β + 1 / L))
    hk1 hh0 hη0.le (by rw [hc₀]; linarith)
    (fun _ _ β hβ => rhsFbound_nonneg M L (by linarith [hβ.1]))
    (fun α hα β hβ t => joint_supF_pin hg hk3 hL hy hη hc₀ hMt hα.1 hβ.1 hα.2 hβ.2 t)
    hIβ hIβ' hIα hIα'
  refine hJ1.trans ?_
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L :=
    fun α hα => beta_integral_pin_const _ hgtw hCb0 hCbound hk hL hy hη hc₀ hh hyk hM0
      hα.1 hα.2 (hIβ α hα)
  have hKcont : Continuous
      (fun α : ℝ => (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L) :=
    ((continuous_rpow_negC hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L
      = (widthKamp Cb k h y c₀ * rhsSigmaG M L) * ((k + h) ^ (-α)) := fun α => by ring
  have hpull : (∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L)
      = (widthKamp Cb k h y c₀ * rhsSigmaG M L) * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith) hη0.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFbound M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β
      ≤ (1 / Real.pi) * ((widthKamp Cb k h y c₀ * rhsSigmaG M L) * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ ∫ α in (0 : ℝ)..η, (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaG M L := hmono
      _ = (widthKamp Cb k h y c₀ * rhsSigmaG M L) * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (widthKamp Cb k h y c₀ * rhsSigmaG M L) * (1 / L) :=
          mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  refine hstep.trans (le_of_eq ?_)
  have hexpeq : Real.exp (-(1 / (2 * Real.exp 1) * M))
      = Real.exp (-(1 / (2 * Real.exp 1)) * M) := by rw [neg_mul]
  have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold rhsAgradeConst rhsSigmaG
  rw [← hexpeq]
  field_simp

/-! ### The absolute grade socket -/

/-- The EXHIBITED absolute constant of the `hRHS` socket:
`C₁ = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·1580544·(1+Cb)`, `Cb` the short-interval Chebyshev
constant (`= 250`).  Absolute: no `k`, no `X`, no `L`. -/
def gradeAbsConst (Cb : ℝ) : ℝ :=
  (1 / Real.pi) * rhsCSF
    * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
    * (1580544 * (1 + Cb))

lemma gradeAbsConst_nonneg {Cb : ℝ} (hCb0 : 0 ≤ Cb) : 0 ≤ gradeAbsConst Cb := by
  have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
    rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
    have h1 : 1 / Real.exp 1 < 1 := by
      rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
    linarith
  unfold gradeAbsConst
  have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
  positivity

/-- The pin's scale factor: `(k+h)^{c₀} ≤ 9·k` at `h = k/√L`, `c₀ = 1+1/L`, `L = log k ≥ 64`.
(`k+h ≤ (9/8)k` and `(k+h)^{1/L} ≤ e² ≤ 8`.) -/
private lemma pin_rpow_scale {k h L c₀ : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hh : h = k / Real.sqrt L) (hc₀ : c₀ = 1 + 1 / L) :
    (k + h) ^ c₀ ≤ 9 * k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt hL64
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hk1 : (1 : ℝ) ≤ k := by linarith
  -- `k + h ≤ (9/8)·k`
  have hhk : h ≤ k / 8 := by
    rw [hh, div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
  have hkh98 : k + h ≤ 9 / 8 * k := by linarith
  -- `(k+h)^{1/L} ≤ 8`
  have hlogkh : Real.log (k + h) ≤ 2 * L := by
    have hsq : k + h ≤ k * k := by nlinarith
    have h1 : Real.log (k + h) ≤ Real.log (k * k) := Real.log_le_log hkh0 hsq
    rw [Real.log_mul hk0.ne' hk0.ne', ← hL] at h1
    linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hfrac : (k + h) ^ (1 / L : ℝ) ≤ 8 := by
    rw [Real.rpow_def_of_pos hkh0]
    have hexp : Real.log (k + h) * (1 / L) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hL0]; linarith
    calc Real.exp (Real.log (k + h) * (1 / L)) ≤ Real.exp 2 := Real.exp_le_exp.mpr hexp
      _ ≤ 8 := he2
  have hsplit : (k + h) ^ c₀ = (k + h) * (k + h) ^ (1 / L : ℝ) := by
    rw [hc₀, Real.rpow_add hkh0, Real.rpow_one]
  rw [hsplit]
  calc (k + h) * (k + h) ^ (1 / L : ℝ) ≤ (9 / 8 * k) * 8 :=
        mul_le_mul hkh98 hfrac (Real.rpow_nonneg hkh0.le _) (by linarith)
    _ = 9 * k := by ring

/-- **THE GRADE SOCKET, DISCHARGED ABSOLUTELY** (`rhsAgradeConst_le`).  At the corpus pin
(`h = k/√L`, `y = L⁴`, `c₀ = 1+1/L`, `L = log k ≥ 64`):

  `rhsAgradeConst Cb k h y c₀ ≤ gradeAbsConst Cb · k`,

`gradeAbsConst Cb` free of `k`.  This is `hRHS_discharged`'s `hgrade` hypothesis with the
`C₁` EXHIBITED — where `RHSGrade.rhsAgrade` needed `C₁ ≳ L·log L`. -/
theorem rhsAgradeConst_le {Cb k L y h c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hk : Real.exp 64 ≤ k)
    (hL : L = Real.log k) (hy : y = L ^ 4) (hh : h = k / Real.sqrt L) (hc₀ : c₀ = 1 + 1 / L) :
    rhsAgradeConst Cb k h y c₀ ≤ gradeAbsConst Cb * k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  obtain ⟨hh0, -, -, -⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hbr := width_pin_bracket_le hCb0 hL64 hk0 hh hy
  have hbr0 : (0 : ℝ) ≤ widthKampBr Cb k h y := by
    have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
    have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    unfold widthKampBr
    positivity
  have hsc := pin_rpow_scale hk hL hh hc₀
  have hsc0 : (0 : ℝ) ≤ (k + h) ^ c₀ := Real.rpow_nonneg hkh0.le _
  have hkey : widthKamp Cb k h y c₀ ≤ 1580544 * (1 + Cb) * k := by
    unfold widthKamp
    calc widthKampBr Cb k h y * (k + h) ^ c₀
        ≤ (175616 * (1 + Cb)) * (9 * k) := mul_le_mul hbr hsc hsc0 (by positivity)
      _ = 1580544 * (1 + Cb) * k := by ring
  have hfront0 : (0 : ℝ) ≤ (1 / Real.pi) * rhsCSF
      * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1)))) := by
    have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
      rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
      have h1 : 1 / Real.exp 1 < 1 := by
        rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
      linarith
    have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
    positivity
  unfold rhsAgradeConst gradeAbsConst
  calc (1 / Real.pi) * rhsCSF
        * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
        * widthKamp Cb k h y c₀
      ≤ (1 / Real.pi) * rhsCSF
        * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
        * (1580544 * (1 + Cb) * k) := mul_le_mul_of_nonneg_left hkey hfront0
    _ = (1 / Real.pi) * rhsCSF
        * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
        * (1580544 * (1 + Cb)) * k := by ring

/-- **THE EXIT (`hRHS_discharged_const`).**  `RHSGrade.hRHS_discharged`'s conclusion
byte-for-byte, with the grade socket DISCHARGED: `C₁` is exhibited once, before every
quantifier, and is absolute (`gradeAbsConst` at the short-interval constant).

Only the four integrability sockets and the row's minimality `hmin` remain carried — the
`Agrade ≍ C·k·L·log L` frontier of `RHSGrade` §5 is gone. -/
theorem hRHS_discharged_const :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (t₀ t₁ X : ℝ) (k : ℕ), Real.exp 64 ≤ (k : ℝ) → ⌊X⌋₊ ≤ k →
      (∀ v : ℝ, pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
      JointIntegrableAt (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
          (k : ℝ) (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
          (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
        ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  refine ⟨gradeAbsConst Cb, gradeAbsConst_nonneg hCb0, ?_⟩
  intro g hg t₀ t₁ X k hk64 hXk hmin hInt
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  set L : ℝ := Real.log (k : ℝ) with hLdef
  obtain ⟨hk0, hL64, -, -, -, -, -, hyk⟩ :=
    pin_basic64 (k := (k : ℝ)) (L := L) (y := L ^ 4)
      (η := 1 / Real.log (L ^ 4)) hk64 hLdef rfl rfl
  have hM0 : (0 : ℝ) ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X :=
    pretDistSq_nonneg _ _ _
      (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
      (fun n => le_of_eq (costwist_norm t₁ n))
  have hMt := center_dist_floor hg (z := (k : ℝ))
    (by rw [Nat.floor_natCast]; exact hXk) hmin
  have hgrade := rhs_grade_at_scale_const g hg (t₀' := t₀ + t₁) (Cb := Cb)
    hCb0 hCbound hk64 hLdef rfl rfl rfl rfl hyk hM0 hMt hIβ hIβ' hIα hIα'
  refine hgrade.trans ?_
  exact mul_le_mul_of_nonneg_right
    (rhsAgradeConst_le hCb0 hk64 hLdef rfl rfl rfl) (Real.exp_nonneg _)

/-- **THE CAPSTONE AT AN ABSOLUTE CONSTANT** (`center_halasz_of_grade_const`).
`CenterSupply.center_halasz_supply` ∘ `hRHS_discharged_const`: `RHSGrade`'s
`center_halasz_of_grade` with the grade socket GONE and `C₁` quantified outermost.

  `‖∑_{n≤k} seamCoeff (ellLin g) 1 t₀ n · e^{−it₁ log n}‖
     ≤ (C₁·e^{−(1/(2e))·𝔻²(f, p^{it₁}; X)} + 4·(log X)^{−1/2+1/1000})·k`,  `C₁` ABSOLUTE.

The residual carried hypotheses are exactly two: the row's minimality `hmin` (the ⟦TWO-M⟧
semantics) and the four integrability sockets.  This composition also certifies that
`hRHS_discharged_const`'s conclusion is `center_halasz_supply`'s `hRHS` binder byte-for-byte.
**LIVE GUARD** (inherited): `c = 1/(2e)` is the BALL arm's halved constant. -/
theorem center_halasz_of_grade_const :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ t₀ t₁ : ℝ,
      ∃ X₀ : ℝ, 0 < X₀ ∧
        ∀ (X : ℝ) (N : ℕ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
          (∀ v : ℝ, pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
              ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
          (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            JointIntegrableAt (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
              (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              (k : ℝ) (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
              (1 / Real.log (Real.log (k : ℝ) ^ 4))
              ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
        ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
            ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨C₁, hC₁0, hexit⟩ := hRHS_discharged_const
  refine ⟨C₁, hC₁0, fun g hg t₀ t₁ => ?_⟩
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply hg t₀ t₁
  refine ⟨max X₁ (Real.exp 64 + 1), lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N hXlb hXN hN2 hmin hInt
  refine hsupply X N C₁ (le_trans (le_max_left _ _) hXlb) hXN hN2 hC₁0 ?_
  intro k hkfl hkN
  have hXexp : Real.exp 64 + 1 ≤ X := le_trans (le_max_right _ _) hXlb
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk64 : Real.exp 64 ≤ (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  exact hexit g hg t₀ t₁ X k hk64 hkfl hmin (hInt k hkfl hkN)

end Salt.MR
