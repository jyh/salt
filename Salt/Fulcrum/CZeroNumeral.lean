/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Fulcrum.Basic

/-!
# The zero-free-region constant `c₀` as a kernel-checked NUMERAL (`fulcrum`)

`Salt.SW.zero_free_region_all` delivers the S5-facing zero-free region at an
EXISTENTIALLY-packaged constant `∃ c₀ > 0, …`; its two arms refine at the explicit
literals `1/50456` (`zero_free_region_primitive`, `χ² ≠ 1`) and `1/126848`
(`zero_free_region_real`, `χ² = 1`, complex zero), and the combined witness is
`min = 1/126848`. But the numeral is unrecoverable through the `∃`: `obtain` yields
an opaque `c₀` with no lower bound, so the fulcrum calibration `2 ≤ C·c₀`
(equivalently `C ≥ 2/c₀`) can never be discharged at a fixed `C`.

This module re-derives the region with the numeral PINNED (fulcrum-pass1.md R6:
"restate `zero_free_region_all` with the explicit numeral"). The two arms are
re-run verbatim — their proof bodies already carry the literals `1/126848` /
`1/50456`, never the bound variable — as numeral-explicit lemmas, then combined
into `zero_free_region_all_numeral`, the region at the citable value

  **`c₀ = 1/126848`**  (so `2/c₀ = 253696`).

`fulcrum_zero_real_numeral` instantiates `fulcrum_zero_real` at that numeral: the
calibration `hC` becomes the honest arithmetic threshold `253696 ≤ C`, i.e. the
`2/c₀` arm of `C⋆ = max C⁽¹⁾ (2/c₀) = max C⁽¹⁾ 253696` (`c_star_second_arm`).

Nothing here is a new estimate: the analytic content is exactly the landed
`zero_free_region_primitive` / `zero_free_region_real`; only the packaging changes
from `∃` to a definite numeral.
-/

open Complex DirichletCharacter

namespace Salt.Fulcrum

open Salt.SW

set_option maxHeartbeats 800000 in
-- Verbatim re-run of `Salt.SW.zero_free_region_real`'s body (the two-case 3-4-1 Davenport
-- chain with three heavy `LFunction` rewrites); it needs the same budget as the original.
/-- **Real-character complex-zero arm at the explicit numeral `1/126848`.** The body
of `Salt.SW.zero_free_region_real` (which `refine`s at `1/126848`), re-run with the
numeral in the conclusion instead of behind an `∃`. -/
lemma zfr_real_numeral :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 = 1 → χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.im ≠ 0 →
        ρ.re ≤ 1 - 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  intro q hNe χ hχ hsq hχ1 ρ hzero _hre hγ0
  -- basics (mirror S3d)
  have hcond : χ.conductor = q := hχ
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1
    have hqne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set Lval : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLdef
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * (|ρ.im| + 2) := by
    nlinarith [abs_nonneg ρ.im, hqR2,
      mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
  have hexp4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp4
  have hL1 : (1 : ℝ) ≤ Lval := le_trans h4 (Real.log_le_log (by norm_num) hQ4)
  have hLpos : (0 : ℝ) < Lval := by linarith
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hzero
  rcases le_or_gt ρ.re (3 / 4) with hβle | hβgt
  · -- trivial branch: `Re ρ ≤ 3/4 ≤ 1 − c₀/L`
    have hc0 : (1 / 126848 : ℝ) / Lval ≤ 1 / 126848 := by
      rw [div_le_iff₀ hLpos]; nlinarith [hL1]
    linarith [hc0, hβle]
  · -- the 3-4-1 machinery
    set dd : ℝ := 1 / 15856 with hdddef
    have hddpos : (0 : ℝ) < dd := by norm_num
    have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
    set σ : ℝ := 1 + dd / Lval with hσdef
    have hddL : dd / Lval ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
    have hθpos : 0 < dd / Lval := div_pos hddpos hLpos
    have hσ1 : 1 < σ := by rw [hσdef]; linarith
    have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
    -- the 3-4-1 positivity with the third character rewritten to `χ₀`
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    rw [hsq] at h341
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C,
        neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ2C] at h341
    -- opaque names for the three log-derivative real parts (keeps the arithmetic light)
    set T0 : ℝ := (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)).re
      with hT0def
    set T1 : ℝ := (-logDeriv (LFunction χ) s1).re with hT1def
    set T2 : ℝ := (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) s2).re with hT2def
    -- A₀ : the χ₀ pole bound at real `σ`
    have hA0 : T0 ≤ 1 / (σ - 1) + 1 := by
      have h := neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2.le
      rwa [← hT0def] at h
    -- A₂ : the χ₀ bound at complex `s₂`, with the pole real part evaluated
    have hpole_eval : (1 / (s2 - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) := by
      have hre2 : (s2 - 1).re = σ - 1 := by
        rw [hs2def]
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have him2 : (s2 - 1).im = 2 * ρ.im := by
        rw [hs2def]
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [one_div, Complex.inv_re, Complex.normSq_apply, hre2, him2]
      ring
    have hA2 : T2 ≤ (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2)
        + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ) := by
      have h := neg_re_logDeriv_trivChar_complex_le q hσ1 hσ2.le (γ := ρ.im)
      rw [← hs2def, hpole_eval] at h
      rwa [← hT2def] at h
    clear_value T0 T1 T2
    -- the growth collapses
    have hB1 : 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
        * (1 + Real.log (q : ℝ)))) ≤ 720 * Lval := by
      have := log_four_M0_le (f := q) (q := q) (t := ρ.im) (γ := ρ.im) hq2 le_rfl hq2
        (by linarith [abs_nonneg ρ.im])
      rw [← hLdef] at this; linarith [this]
    have hlogq : Real.log (q : ℝ) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by linarith)
      nlinarith [abs_nonneg ρ.im, hqR2,
        mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
    have hlogγ : Real.log (|ρ.im| + 2) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg ρ.im, hqR2]
    -- the growth-to-pole conversion `3964·L = (1/4)/(σ−1)`
    have hθL : σ - 1 = dd / Lval := by rw [hσdef]; ring
    have hσ1' : (0 : ℝ) < σ - 1 := by linarith
    have hLB : Lval * (σ - 1) = dd := by
      rw [hθL]; field_simp
    have hLdd' : 3964 * Lval = 1 / 4 * (1 / (σ - 1)) := by
      rw [mul_one_div, eq_div_iff (ne_of_gt hσ1')]
      calc 3964 * Lval * (σ - 1) = 3964 * (Lval * (σ - 1)) := by ring
        _ = 3964 * dd := by rw [hLB]
        _ = 1 / 4 := by rw [hdddef]; norm_num
    rcases le_or_gt (σ - 1) |ρ.im| with hcase | hcase
    · -- Case (i): `|γ| ≥ σ−1`; keep one zero; the pole is `≤ (1/4)/(σ−1)`
      have hA1 : T1 ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
          * (1 + Real.log (q : ℝ)))) - 1 / (σ - ρ.re) := by
        have h := neg_reLogDeriv_le_keep χ hχ hq2 hzero (by linarith : 1 / 2 < ρ.re)
          hβ1 hσ1 hσ2
        rw [← hs1def] at h
        rwa [← hT1def] at h
      have hγsq : (σ - 1) * (σ - 1) ≤ ρ.im * ρ.im := by
        have h1 := mul_self_le_mul_self hσ1'.le hcase
        rwa [abs_mul_abs_self] at h1
      have hpole : (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) ≤ 1 / 4 * (1 / (σ - 1)) := by
        have hden : (0 : ℝ) < (σ - 1) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hσ1' 2, sq_nonneg ρ.im]
        rw [mul_one_div, div_le_div_iff₀ hden hσ1']
        nlinarith [hγsq]
      have hA2' : T2 ≤ 1 / 4 * (1 / (σ - 1)) + 1080 * Real.log (|ρ.im| + 2)
          + Real.log (q : ℝ) := by
        linarith [hA2, hpole]
      have hstep : 4 * (1 / (σ - ρ.re))
          ≤ 3 * (1 / (σ - 1)) + 1 / 4 * (1 / (σ - 1))
            + (3 + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
              + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
                  * (1 + Real.log (q : ℝ)))))) := by
        linarith [h341, hA0, hA1, hA2']
      have hcollapse : (3 : ℝ) + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
          + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
              * (1 + Real.log (q : ℝ))))) ≤ 3964 * Lval := by
        linarith [hB1, hlogq, hlogγ, hL1]
      have hchain : 4 * (1 / (σ - ρ.re)) ≤ 7 / 2 * (1 / (σ - 1)) := by
        linarith [hstep, hcollapse, hLdd']
      have hchain' : 4 / (dd / Lval + (1 - ρ.re)) ≤ (7 / 2) / (dd / Lval) := by
        rw [mul_one_div, mul_one_div] at hchain
        have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
        rw [e1, hθL] at hchain
        exact hchain
      have hext := zero_free_extraction2 hθpos (by norm_num : (0:ℝ) < 7 / 2) hβ1 hchain'
      rw [hdddef] at hext
      have hh : (1 / 126848 : ℝ) / Lval ≤ (4 - 7 / 2) / (7 / 2) * (1 / 15856 / Lval) := by
        have heq : (4 - 7 / 2 : ℝ) / (7 / 2) * (1 / 15856 / Lval) = 1 / 110992 / Lval := by
          ring
        rw [heq, div_le_div_iff_of_pos_right hLpos]
        norm_num
      linarith [hext, hh]
    · -- Case (ii): `|γ| < σ−1 ≤ δ`; keep the conjugate pair; the pole is `≤ 1/(σ−1)`
      have hγ4 : |ρ.im| ≤ 1 / 4 := by
        have hddq : σ - 1 ≤ dd := by rw [hθL]; exact hddL
        rw [hdddef] at hddq
        linarith [hcase]
      have hρc0 : LFunction χ ((starRingEnd ℂ) ρ) = 0 := LFunction_conj_zero hχ1 hsq hzero
      have hA1 : T1 ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
          * (1 + Real.log (q : ℝ)))) - 1 / (σ - ρ.re)
            - (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
        have h := neg_reLogDeriv_le_keep_two χ hχ hq2 hzero hρc0 (le_of_lt hβgt) hβ1
          hγ0 hγ4 hσ1 hσ2
        rw [← hs1def] at h
        rwa [← hT1def] at h
      have hηpos : (0 : ℝ) < σ - ρ.re := by linarith
      have hγsq : ρ.im * ρ.im ≤ (σ - 1) * (σ - 1) := by
        have h1 : |ρ.im| * |ρ.im| ≤ (σ - 1) * (σ - 1) :=
          mul_self_le_mul_self (abs_nonneg ρ.im) hcase.le
        rwa [abs_mul_abs_self] at h1
      have hθη : σ - 1 ≤ σ - ρ.re := by linarith
      have hconj_ge : 1 / (5 * (σ - ρ.re))
          ≤ (σ - ρ.re) / ((σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2) := by
        have hden : (0 : ℝ) < (σ - ρ.re) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hηpos 2, sq_nonneg ρ.im]
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 5 * (σ - ρ.re)) hden]
        nlinarith [hγsq, mul_self_le_mul_self hσ1'.le hθη]
      have hbridge : (1 : ℝ) / 5 * (1 / (σ - ρ.re)) = 1 / (5 * (σ - ρ.re)) := by
        rw [div_mul_div_comm, one_mul]
      have hpole : (σ - 1) / ((σ - 1) ^ 2 + 4 * ρ.im ^ 2) ≤ 1 / (σ - 1) := by
        have hden : (0 : ℝ) < (σ - 1) ^ 2 + 4 * ρ.im ^ 2 := by
          nlinarith [pow_pos hσ1' 2, sq_nonneg ρ.im]
        rw [div_le_div_iff₀ hden hσ1']
        nlinarith [sq_nonneg ρ.im]
      have hA2' : T2 ≤ 1 / (σ - 1) + 1080 * Real.log (|ρ.im| + 2)
          + Real.log (q : ℝ) := by
        linarith [hA2, hpole]
      have hstep : 24 / 5 * (1 / (σ - ρ.re))
          ≤ 4 * (1 / (σ - 1))
            + (3 + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
              + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
                  * (1 + Real.log (q : ℝ)))))) := by
        linarith [h341, hA0, hA1, hA2', hconj_ge, hbridge]
      have hcollapse : (3 : ℝ) + 1080 * Real.log (|ρ.im| + 2) + Real.log (q : ℝ)
          + 4 * (120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ)
              * (1 + Real.log (q : ℝ))))) ≤ 3964 * Lval := by
        linarith [hB1, hlogq, hlogγ, hL1]
      have hchain : 24 / 5 * (1 / (σ - ρ.re)) ≤ 17 / 4 * (1 / (σ - 1)) := by
        linarith [hstep, hcollapse, hLdd']
      have hchain' : (24 / 5) / (dd / Lval + (1 - ρ.re)) ≤ (17 / 4) / (dd / Lval) := by
        rw [mul_one_div, mul_one_div] at hchain
        have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
        rw [e1, hθL] at hchain
        exact hchain
      have hext := zero_free_extraction2 hθpos (by norm_num : (0:ℝ) < 17 / 4) hβ1 hchain'
      rw [hdddef] at hext
      have hh : (1 / 126848 : ℝ) / Lval
          ≤ (24 / 5 - 17 / 4) / (17 / 4) * (1 / 15856 / Lval) := by
        have heq : (24 / 5 - 17 / 4 : ℝ) / (17 / 4) * (1 / 15856 / Lval)
            = 11 / 1347760 / Lval := by
          ring
        rw [heq, div_le_div_iff_of_pos_right hLpos]
        norm_num
      linarith [hext, hh]

/-- **Primitive complex-character arm at the explicit numeral `1/50456`.** The body of
`Salt.SW.zero_free_region_primitive` (which `refine`s at `1/50456`), re-run with the
numeral in the conclusion instead of behind an `∃`. -/
lemma zfr_primitive_numeral :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ^ 2 ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        ρ.re ≤ 1 - 1 / 50456 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  intro q hNe χ hχ hsq ρ hzero _hre
  -- basics
  have hχ1 : χ ≠ 1 := fun h => hsq (by rw [h, one_pow])
  have hcond : χ.conductor = q := hχ
  have hq2 : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1
    have hqne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set Lval : ℝ := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLdef
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) * (|ρ.im| + 2) := by
    nlinarith [abs_nonneg ρ.im, hqR2, mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
  have hexp4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp4
  have hL1 : (1 : ℝ) ≤ Lval := le_trans h4 (Real.log_le_log (by norm_num) hQ4)
  have hLpos : (0 : ℝ) < Lval := by linarith
  have hLne : Lval ≠ 0 := ne_of_gt hLpos
  have hβ1 : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hzero
  rcases le_or_gt ρ.re (1 / 2) with hβle | hβgt
  · -- trivial branch: `Re ρ ≤ 1/2 ≤ 1 − c₀/L`
    have hc0 : (1 / 50456 : ℝ) / Lval ≤ 1 / 50456 := by
      rw [div_le_iff₀ hLpos]; nlinarith [hL1]
    linarith [hc0, hβle]
  · -- the 3-4-1 machinery
    set dd : ℝ := 1 / 7208 with hdddef
    have hddpos : (0 : ℝ) < dd := by norm_num
    have hddlt1 : dd < 1 := by rw [hdddef]; norm_num
    set σ : ℝ := 1 + dd / Lval with hσdef
    have hddL : dd / Lval ≤ dd := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, hddpos]
    have hσ1 : 1 < σ := by
      rw [hσdef]
      have hpos : 0 < dd / Lval := div_pos hddpos hLpos
      linarith
    have hσ2 : σ < 2 := by rw [hσdef]; linarith [hddL, hddlt1]
    -- the 3-4-1 positivity and the LSeries → LFunction bridge
    have h341 := three_four_one_logDeriv χ hσ1 ρ.im
    set s1 : ℂ := (σ : ℂ) + (ρ.im : ℂ) * I with hs1def
    set s2 : ℂ := (σ : ℂ) + 2 * (ρ.im : ℂ) * I with hs2def
    have hσ0C : (1 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
    have hσ1C : (1 : ℝ) < s1.re := by rw [hs1def]; simpa using hσ1
    have hσ2C : (1 : ℝ) < s2.re := by rw [hs2def]; simpa using hσ1
    rw [neg_logDeriv_LSeries_eq (1 : DirichletCharacter ℂ q) hσ0C,
        neg_logDeriv_LSeries_eq χ hσ1C, neg_logDeriv_LSeries_eq (χ ^ 2) hσ2C] at h341
    -- A₀ : the χ₀ pole bound
    have hA0 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 :=
      neg_logDeriv_LFunction_trivChar_le q hσ1 hσ2.le
    -- A₁ : the retained-zero bound for χ
    have hA1 : (-logDeriv (LFunction χ) s1).re
        ≤ 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
          - 1 / (σ - ρ.re) := by
      have h := neg_reLogDeriv_le_keep χ hχ hq2 hzero hβgt hβ1 hσ1 hσ2
      rw [← hs1def] at h; exact h
    -- A₂ : the dropped-zeros bound for χ², via the primitive-inducing character + EulerBridge
    have hf2q : (χ ^ 2).conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level (χ ^ 2))
    have hf22 : 2 ≤ (χ ^ 2).conductor := by
      have hc1 : (χ ^ 2).conductor ≠ 1 := fun h => hsq (eq_one_iff_conductor_eq_one.mpr h)
      have hc0' : (χ ^ 2).conductor ≠ 0 := (χ ^ 2).conductor_ne_zero
      omega
    have hprim : ((χ ^ 2).primitiveCharacter).IsPrimitive := primitiveCharacter_isPrimitive (χ ^ 2)
    have hχ2'ne1 : (χ ^ 2).primitiveCharacter ≠ 1 := ne_one_of_isPrimitive _ hprim hf22
    have hL1s2 : LFunction (χ ^ 2).primitiveCharacter s2 ≠ 0 :=
      LFunction_ne_zero_of_one_le_re (χ ^ 2).primitiveCharacter (Or.inl hχ2'ne1) hσ2C.le
    have hsc2 : ‖s2 - (2 + ((2 * ρ.im : ℝ) : ℂ) * I)‖ ≤ 23 / 20 := by
      have he : s2 - (2 + ((2 * ρ.im : ℝ) : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
        rw [hs2def]; push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
      linarith
    have hdrop := neg_reLogDeriv_le_drop (χ ^ 2).primitiveCharacter hprim hf22 (2 * ρ.im) hsc2 hσ2C
    have hbr := norm_logDeriv_LFunction_sub_primitive_le (χ ^ 2) hσ2C.le hL1s2 (Or.inl hsq)
    have hA2 : (-logDeriv (LFunction (χ ^ 2)) s2).re
        ≤ (-logDeriv (LFunction (χ ^ 2).primitiveCharacter) s2).re + Real.log (q : ℝ) := by
      have habs := (Complex.abs_re_le_norm _).trans hbr
      rw [Complex.sub_re] at habs
      rw [Complex.neg_re, Complex.neg_re]
      linarith [abs_le.mp habs |>.1]
    have hA2full : (-logDeriv (LFunction (χ ^ 2)) s2).re
        ≤ 120 * Real.log (4 * (5 * (4 + |2 * ρ.im|) * Real.sqrt ((χ ^ 2).conductor : ℝ)
            * (1 + Real.log ((χ ^ 2).conductor : ℝ)))) + Real.log (q : ℝ) := by
      linarith [hA2, hdrop]
    -- the growth terms are `O(L)`
    have hB1 : 120 * Real.log (4 * (5 * (4 + |ρ.im|) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
        ≤ 720 * Lval := by
      have := log_four_M0_le (f := q) (q := q) (t := ρ.im) (γ := ρ.im) hq2 le_rfl hq2
        (by linarith [abs_nonneg ρ.im])
      rw [← hLdef] at this; linarith [this]
    have hB2 : 120 * Real.log (4 * (5 * (4 + |2 * ρ.im|) * Real.sqrt ((χ ^ 2).conductor : ℝ)
          * (1 + Real.log ((χ ^ 2).conductor : ℝ)))) ≤ 720 * Lval := by
      have := log_four_M0_le (f := (χ ^ 2).conductor) (q := q) (t := 2 * ρ.im) (γ := ρ.im)
        hf22 hf2q hq2 (by rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num])
      rw [← hLdef] at this; linarith [this]
    have hlogq : Real.log (q : ℝ) ≤ Lval := by
      rw [hLdef]
      apply Real.log_le_log (by linarith)
      nlinarith [abs_nonneg ρ.im, hqR2,
        mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by linarith) (abs_nonneg ρ.im)]
    -- assemble the 3-4-1 chain
    have hrel1 : (4 : ℝ) / (σ - ρ.re) = 4 * (1 / (σ - ρ.re)) := by ring
    have hrel2 : (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
    have hchain : 4 / (σ - ρ.re) ≤ 3 / (σ - 1) + 3604 * Lval := by
      rw [hrel1, hrel2]
      linarith [h341, hA0, hA1, hA2full, hB1, hB2, hlogq, hL1]
    -- the numeric extraction
    have hCdd : (3604 : ℝ) * dd = 1 / 2 := by rw [hdddef]; norm_num
    have hchain' : 4 / (dd / Lval + (1 - ρ.re)) ≤ 3 / (dd / Lval) + 3604 * Lval := by
      have e1 : σ - ρ.re = dd / Lval + (1 - ρ.re) := by rw [hσdef]; ring
      have e2 : σ - 1 = dd / Lval := by rw [hσdef]; ring
      rw [e1, e2] at hchain; exact hchain
    have hfinal := zero_free_extraction hLpos hddpos hCdd hβ1 hchain'
    have heq : (1 / 50456 : ℝ) / Lval = dd / (7 * Lval) := by rw [hdddef]; field_simp; ring
    rw [heq]; linarith [hfinal]

/-- **The combined zero-free region at the explicit numeral `c₀ = 1/126848`.** The
numeral form of `Salt.SW.zero_free_region_all`: every zero of `L(·,χ)` with
`Re ρ ≥ 1/2` that is not a real zero of a real character obeys
`Re ρ ≤ 1 − (1/126848)/log(q(|Im ρ|+2))`. Combines `zfr_real_numeral` (the `χ²=1`,
`Im ρ ≠ 0` arm, exactly `1/126848`) with `zfr_primitive_numeral` (the `χ²≠1` arm at
`1/50456`, weakened to the smaller `1/126848`). This is precisely the `hZFR`
hypothesis of `fulcrum_zero_real`, now available at a definite numeral. -/
theorem zero_free_region_all_numeral :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
  intro q hNe χ hχ hχ1 ρ hzero hre hor
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hLpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos
    nlinarith [abs_nonneg ρ.im, hq1]
  by_cases hsq : χ ^ 2 = 1
  · have hγ : ρ.im ≠ 0 := by
      rcases hor with h | h
      · exact absurd hsq h
      · exact h
    exact zfr_real_numeral q χ hχ hsq hχ1 hzero hre hγ
  · have hb := zfr_primitive_numeral q χ hχ hsq hzero hre
    have hmono : (1 : ℝ) / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ 1 / 50456 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
      rw [div_le_div_iff_of_pos_right hLpos]
      norm_num
    linarith [hb, hmono]

/-- **The `2/c₀` arm of `C⋆` at the extracted numeral.** With `c₀ = 1/126848`,
`2/c₀ = 253696`, so `C⋆ = max C⁽¹⁾ (2/c₀) = max C⁽¹⁾ 253696`. -/
lemma c_star_second_arm : (2 : ℝ) / (1 / 126848) = 253696 := by norm_num

/-- **Fulcrum calibration at the numeral.** The abstract threshold `2 ≤ C·c₀` of
`fulcrum_zero_real` becomes the honest arithmetic bound `253696 ≤ C` at
`c₀ = 1/126848`. -/
lemma fulcrum_calibration_numeral (C : ℝ) :
    (2 : ℝ) ≤ C * (1 / 126848) ↔ 253696 ≤ C := by
  constructor <;> intro h <;> nlinarith [h]

/-- **Reality from the region at the explicit numeral.** `fulcrum_zero_real`
instantiated at `c₀ = 1/126848` and `zero_free_region_all_numeral`: a fulcrum witness
whose fixed constant clears the `2/c₀` arm `C ≥ 253696` (with `q ≥ 3`) has its zero
`ρ` REAL with `1/2 ≤ Re ρ < 1`. The calibration `hC` is now a bare numeral threshold,
no residual `hcal`. -/
theorem fulcrum_zero_real_numeral (C : ℝ) (hC : 253696 ≤ C)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hq3 : 3 ≤ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hzero : LFunction χ ρ = 0)
    (hball : ‖(1 : ℂ) - ρ‖ * (C * Real.log q) ≤ 1) :
    ρ.im = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
  have hCc₀ : (2 : ℝ) ≤ C * (1 / 126848) := by
    rw [show (2 : ℝ) = 253696 * (1 / 126848) by norm_num]
    exact mul_le_mul_of_nonneg_right hC (by norm_num)
  exact fulcrum_zero_real C (1 / 126848) (by norm_num) (by norm_num) hCc₀
    zero_free_region_all_numeral hq3 hprim hne hzero hball

end Salt.Fulcrum
